module TaPL.Chapter11

import Data.Vect
import Decidable.Equality

Name : Type
Name = String

data Info : Type
data Ty : Type
data Context : Type
data TypeStatement : Type
data (|-) : (0 _ : Context) -> TypeStatement -> Type
data TypeDerivation : Type

infix 10 |-
infix 11 <:>

data Binding : Type where
  VarBind  : (ty : Ty) -> Binding

data Context : Type where
  Lin  : Context
  (:<) : Context -> (Name, Binding) -> Context

data InContext : Nat -> Ty -> Context -> Type where
  Here  : InContext 0 ty (ctx :< (n, VarBind ty))
  There : InContext n ty ctx -> InContext (S n) ty (ctx :< b)

Uninhabited (InContext 0     _ Lin) where uninhabited _ impossible
Uninhabited (InContext (S _) _ Lin) where uninhabited _ impossible

total
thereInjective : InContext (S n) ty (ctx :< b) -> InContext n ty ctx
thereInjective (There x) = x

total
inContext : (ctx : Context) -> (i : Nat) -> Dec (ty : Ty ** InContext i ty ctx)
inContext [<] 0                     = No (\inCtxt => uninhabited (snd inCtxt))
inContext [<] (S k)                 = No (\inCtxt => uninhabited (snd inCtxt))
inContext (x :< (y, (VarBind t))) 0 = Yes (t ** Here)
inContext (x :< y) (S k)            = case inContext x k of
  Yes   found => Yes (case found of { (ty ** there) => (ty ** There there) })
  No notFound => No (\(ty ** there) => notFound (ty ** thereInjective there))

total
indexToName : (ctx : Context) -> (i : Nat) -> (inCtx : InContext i ty ctx) -> Name
indexToName (ctx :< (n, VarBind ty))  0     Here      = n
indexToName (ctx :< b)                (S n) (There x) = indexToName ctx n x

public export
addBinding : Name -> Ty -> Context -> Context
addBinding n ty ctx = ctx :< (n, VarBind ty)


data Infer : Type -> Type where
  Pure : a -> Infer a
  Bind : Infer a -> (a -> Infer b) -> Infer b
  Error : {a : Type} -> Info -> List TypeDerivation -> String -> Infer a

namespace InferMonad

  (>>=) : Infer a -> (a -> Infer b) -> Infer b
  (>>=) = Bind

  pure : a -> Infer a
  pure = Pure

Functor Infer where
  map f m = Bind m (\a => Pure (f a))

Applicative Infer where
  pure    x = Pure x
  ef <*> ex = Bind ef (\f => (Bind ex (\x => Pure (f x))))

Monad Infer where
  join m  = Bind m id
  m >>= k = Bind m k

DecEq Ty where
  decEq _ _ = ?decEqTy
  -- decEq Bool Bool = Yes Refl
  -- decEq Bool (Arr x y) = No uninhabited
  -- decEq (Arr x y) Bool = No uninhabited
  -- decEq (Arr x y) (Arr z w) = case (decEq x z, decEq y w) of
  --   ((Yes xIsZ)   , (Yes yIsW)   ) => Yes $ rewrite xIsZ in rewrite yIsW in Refl
  --   ((Yes xIsZ)   , (No contraYW)) => No (\assumeArrYW => contraYW (snd (funInjective assumeArrYW)))
  --   ((No contraXZ), (Yes yIsW)   ) => No (\assumeArrXZ => contraXZ (fst (funInjective assumeArrXZ)))
  --   ((No contraXZ), (No contraYW)) => No (\assumeArrXZ => contraXZ (fst (funInjective assumeArrXZ)))

namespace ForEach

  public export
  data ForEach : Vect n a -> (p : a -> Type) -> Type where
    Nil  : ForEach [] p
    (::) : {xs : Vect n a} -> (p x) -> ForEach xs p -> ForEach (x :: xs) p

namespace NotInt

  public export
  data NotIn : String -> Vect n String -> Type where
    Nil  : NotIn n []
    (::) : (0 c : Not (n = f)) -> NotIn n fs -> NotIn n (f :: fs)

-- If the f and fs are the same, there should be only one way to create the list that proofs for every
-- element the f is not in the fs vector. If we compare such two values, the only possible difference
-- are the proofs that that f is not the head of the vector. We could have many computationaly different
-- functions to create an impossbile Void value, but we say, if we got one, that the difference is their
-- implementation is not relevant.
-- At the same time we don't use such a proof at runtime, because the 0 quantity on the Cons cell, meaning
-- that the runtime representation of such field, will be the Erased value, which is much easier to find
-- if that is the same or not, as it should be the same, we are on the safe side.
DecEq (NotIn f fs) where
  decEq n1 n2 = Yes (believe_me (Refl {x=n1}))

namespace Index

  public export
  data Index : a -> Nat -> Vect n a -> Type where
    Here  : Index x 0 (x :: xs)
    There : Index x n xs -> Index x (S n) (y :: xs)

namespace Record

  public export
  data UniqueFields : Vect n String -> Type where
    Nil  : UniqueFields []
    (::) : NotIn f fs -> UniqueFields fs -> UniqueFields (f :: fs)

  public export
  record Record (a : Type) where
    constructor MkRecord
    size   : Nat
    fields : Vect size String
    values : Vect size a
    uniqueFields : UniqueFields fields

  public export
  data InRecord : String -> a -> Vect n String -> Vect n a -> Type where
    Here  : InRecord f x (f :: fs) (x :: xs)
    There : InRecord f x fs xs -> InRecord f x (g :: fs) (y :: xs)

namespace Variant

  public export
  data UniqueTags : (n : Nat) -> Vect n String -> Type where
    Nil  : UniqueTags 0 []
    (::) : NotIn f fs -> UniqueTags n fs -> UniqueTags (S n) (f :: fs)

  export
  notInInjective : (Variant.(::) ni1 ut1 = ni2 :: ut2) -> (ni1 = ni2, ut1 = ut2)
  notInInjective Refl = (Refl, Refl)

  public export
  record Variant (a : Type) where
    constructor MkVariant
    size        : Nat
    tags        : Vect size String
    info        : Vect size a
    uniqueTags  : UniqueTags size tags
    nonEmpty    : NonZero size

DecEq (UniqueTags n xs) where
  decEq [] [] = Yes Refl
  decEq (x :: y) (z :: w) = case (decEq x z, decEq y w) of
    ((Yes x_is_z)   , (Yes y_is_w)   ) => Yes (cong2 (::) x_is_z y_is_w)
    ((Yes x_is_z)   , (No y_is_not_w)) => No (\assume_xy_is_zw => y_is_not_w (snd (notInInjective assume_xy_is_zw)))
    ((No x_is_not_z), (Yes y_is_w)   ) => No (\assume_xy_is_zw => x_is_not_z (fst (notInInjective assume_xy_is_zw)))
    ((No x_is_not_z), (No y_is_not_w)) => No (\assume_xy_is_zw => y_is_not_w (snd (notInInjective assume_xy_is_zw)))

DecEq (NonZero n) where
  decEq SIsNonZero SIsNonZero = Yes Refl

namespace FieldIndex

  total
  fieldIndexGo : (n : Nat) -> (tag : String) -> (tags : Vect n String) -> (infos : Vect n a) -> Maybe (i : Nat ** (Index tag i tags, ((x : a ** Index x i infos))))
  fieldIndexGo 0       tag []        [] = Nothing
  fieldIndexGo (S len) tag (x :: xs) (y :: ys) = case decEq x tag of
    Yes Refl        => Just (0 ** (Here, (y ** Here)))
    No x_is_not_tag => do
      (i ** (tagThere, (a ** infoThere))) <- fieldIndexGo len tag xs ys
      Just ((S i) ** (There tagThere, (a ** There infoThere)))

  total export
  fieldIndex : (tag : String) -> (v : Variant a) -> Maybe (i : Nat ** (Index tag i v.tags, (x : a ** Index x i v.info)))
  fieldIndex tag v = fieldIndexGo v.size tag v.tags v.info


namespace Term

  public export
  data Tm : Type where
    True  : (fi : Info)                                           -> Tm
    False : (fi : Info)                                           -> Tm
    If    : (fi : Info) -> (p,t,e : Tm)                           -> Tm
    Var   : (fi : Info) -> (i : Nat)                              -> Tm 
    Abs   : (fi : Info) -> (var : Name) -> (ty : Ty) -> (t : Tm)  -> Tm
    App   : (fi : Info) -> (t1, t2 : Tm)                          -> Tm
    Unit  : (fi : Info)                                           -> Tm

    Seq   : (fi : Info) -> (t1, t2 : Tm)                          -> Tm
    As    : (fi : Info) -> (t : Tm) -> (ty : Ty)                  -> Tm
    Let   : (fi : Info) -> (n : Name) -> (t : Tm) -> (b : Tm)     -> Tm
    
    Pair  : (fi : Info) -> (p1,p2 : Tm)                           -> Tm
    First  : (fi : Info) -> (t : Tm)                              -> Tm
    Second : (fi : Info) -> (t : Tm)                              -> Tm

    Tuple : (fi : Info) -> (n : Nat) -> (ti : Vect n Tm)          -> Tm
    Proj  : (fi : Info) -> (t : Tm) -> (n : Nat) -> (i : Fin n)   -> Tm

    Record : (fi : Info) -> (Record.Record Tm)                    -> Tm
    ProjField : (fi : Info) -> (field : String) -> (t : Tm)       -> Tm

    Variant : (fi : Info) -> (tag : String) -> (t : Tm) -> (ty : Ty) -> Tm
    Case : (fi : Info) -> (t : Tm) -> (tags : Variant (Name, Tm)) -> Tm -- TODO: Rename alts

namespace Value

  public export
  data Value : Tm -> Type where
    Abs   : Value (Abs fi var ty t)
    True  : Value (True fi)
    False : Value (False fi)
    Unit  : Value (Unit fi)
    Pair  : Value v1 -> Value v2 -> Value (Pair fi v1 v2)
    Tuple : {n : Nat} -> {tms : Vect n Tm} -> ForEach tms Value -> Value (Tuple fi n tms)
    Record : (r : Record Tm) -> ForEach r.values Value -> Value (Record fi r)

public export
data Ty : Type where
  Bool : Ty
  Arr  : Ty -> Ty -> Ty
  Base : String -> Ty
  Unit : Ty
  Product : Ty -> Ty -> Ty
  Tuple : (n : Nat) -> Vect n Ty -> Ty
  Record : (r : Record Ty) -> Ty
  Variant : (v : Variant Ty) -> Ty

data TypeStatement : Type where
  (<:>) : (0 t1 : Tm) -> (t2 : Ty) -> TypeStatement

data Derivation : Context -> Tm -> Ty -> Type where
  MkDerivation : (t : Tm) -> (ty : Ty) -> (deriv : (ctx |- t <:> ty)) -> Derivation ctx t ty

namespace DerivList

  public export
  data Derivations : Context -> Vect n Tm -> Vect n Ty -> Type where
    Nil  : Derivations ctx [] []
    (::) : Derivation ctx t ty -> Derivations ctx ts tys -> Derivations ctx (t :: ts) (ty :: tys)

namespace VariantDerivations

  ||| Witness that every Tm term in the alternatives has the same Ty type.
  public export
  data VariantDerivations : (n : Nat) -> Context -> Vect n (Name, Tm) -> Vect n Ty -> Ty -> Type where
    Nil  : VariantDerivations 0 ctx [] [] ty
    (::) : {var : Name} -> {tty : Ty}
           -> Derivation (ctx :< (var, VarBind tty)) t ty
           -> VariantDerivations n ctx ts ttys ty
           -> VariantDerivations (S n) ctx ((var, t) :: ts) (tty :: ttys) ty

namespace InVariant

  public export
  data InVariant : String -> Name -> Tm -> Vect n String -> Vect n (Name,Tm) -> Type where
    Here  : InVariant tag x tm (tag :: tags) ((x,tm) :: alts)
    There : InVariant tag x tm tags alts -> InVariant tag x tm (tah :: tags) ((y,tn) :: alts)

data (|-) : (0 _ : Context) -> TypeStatement -> Type where

  TVar : Info ->
      InContext x ty gamma  ->
    --------------------------
     gamma |- Var fi x <:> ty
  
  TAbs : Info -> -- Introduction rule for Arr
     (gamma :< (x,VarBind ty1)) |- tm2 <:> ty2  ->
  ------------------------------------------------ 
   gamma |- Abs fi1 x ty1 tm2 <:> Arr ty1 ty2

  TApp : Info -> -- Elimination rule for Arr
    (gamma |- tm1 <:> Arr ty11 ty12) -> (gamma |- tm2 <:> ty11) ->
    -------------------------------------------------------------- 
                    gamma |- App fi tm1 tm2 <:> ty12

  TTrue : Info ->
    -------------------------
    gamma |- True fi <:> Bool

  TFalse : Info ->
    --------------------------
    gamma |- False fi <:> Bool

  TIf : Info ->
    (gamma |- tmp <:> Bool) -> (gamma |- tmt <:> ty) -> (gamma |- tme <:> ty) ->
    ----------------------------------------------------------------------------
                     gamma |- (If fi tmp tmt tme <:> ty)

  TUnit : Info ->
    -------------------------
    gamma |- Unit fi <:> Unit

  TSeq : Info ->
    (gamma |- t1 <:> Unit) -> (gamma |- t2 <:> ty2) ->
    --------------------------------------------------
            gamma |- Seq fi t1 t2 <:> ty2

  TAscribe : Info ->
        (gamma |- t1 <:> ty1)  ->
    -----------------------------
    gamma |- As fi t1 ty1 <:> ty1

  TLet : Info ->
    (gamma |- (t1 <:> ty1)) -> ((gamma :< (x,VarBind ty1)) |- t2 <:> ty2) ->
    ------------------------------------------------------------------------
                       gamma |- Let fi x t1 t2 <:> ty2

  TPair : Info ->
    (gamma |- (t1 <:> ty1)) -> (gamma |- (t2 <:> ty2)) ->
    -----------------------------------------------------
          gamma |- Pair fi t1 t2 <:> Product ty1 ty2

  TProj1 : Info ->
    (gamma |- (t1 <:> Product ty1 ty2)) ->
    --------------------------------------
          gamma |- First fi t1 <:> ty1

  TProj2 : Info ->
    (gamma |- (t1 <:> Product ty1 ty2)) ->
    --------------------------------------
         gamma |- Second fi t1 <:> ty2

  TTuple : Info ->
          Derivations gamma ts tys      ->
    --------------------------------------
    gamma |- Tuple fi n ts <:> Tuple n tys

  TProj : Info ->
          gamma |- t <:> Tuple n tys    ->
    --------------------------------------
    gamma |- Proj fi t n i <:> index i tys

  TRcd : Info ->
                  {fields : Vect n String} -> {u : UniqueFields fields}           ->
                               Derivations gamma ts tys                           ->
    --------------------------------------------------------------------------------
    gamma |- Record fi (MkRecord n fields ts u) <:> Record (MkRecord n fields tys u)

  TRProj : Info ->
    gamma |- t <:> Record (MkRecord n fields tys u) -> InRecord field ty fields tys ->
    ----------------------------------------------------------------------------------
                           gamma |- ProjField fi field t <:> ty

  TVariant : Info ->
                                            {n : Nat} -> {nz : NonZero n}                                       ->
                                            {j : Nat} -> {ty : Ty}                                              ->
                  {tags : Vect n String} -> {tys : Vect n Ty} ->  {u : UniqueTags n tags} -> {tj : Tm}          -> 
                            Index tag j tags -> Index ty j tys -> (gamma |- tj <:> ty)                          ->
    --------------------------------------------------------------------------------------------------------------
      gamma |- Variant fi tag tj (Variant (MkVariant n tags tys u nz)) <:> (Variant (MkVariant n tags tys u nz))

  TCase : Info ->
                                  {n : Nat} -> {nz : NonZero n}                           ->
        {tags : Vect n String} -> {u : UniqueTags n tags} -> {alts : Vect n (Name, Tm)}   ->
                                 {ty : Ty} -> {tys : Vect n Ty}                           ->
                      (gamma |- t0 <:> (Variant (MkVariant n tags tys u nz)))             ->
                                (VariantDerivations n gamma alts tys ty)                  ->
    ----------------------------------------------------------------------------------------
                       gamma |- Case fi t0 (MkVariant n tags alts u nz) <:> ty

funInjective : (Arr x y = Arr z w) -> (x = z, y = w)
funInjective Refl = (Refl, Refl)

Uninhabited (Bool = Arr _ _) where uninhabited _ impossible
Uninhabited (Arr _ _ = Bool) where uninhabited _ impossible

data TypeDerivation : Type where
  MkTypeDerivation : (0 ctx : Context) -> (0 t : Tm) -> (0 ty : Ty) -> (deriv : (ctx |- t <:> ty)) -> TypeDerivation

mkTD : (ctx |- t <:> ty) -> TypeDerivation
mkTD deriv = MkTypeDerivation ctx t ty deriv

mutual

  inferType : (ctx : Context) -> (t : Tm) -> Infer (ty : Ty ** (ctx |- t <:> ty))
  inferType ctx (True fi) = pure (Bool ** TTrue fi)
  inferType ctx (False fi) = pure (Bool ** TFalse fi)
  inferType ctx (If fi p t e) = do
    (Bool ** pDeriv) <- inferType ctx p
      | (_ ** wrongDeriv) => Error fi [mkTD wrongDeriv] "guard of conditional is not a Bool"
    (tty ** thenDeriv) <- inferType ctx t
    (ety ** elseDeriv) <- inferType ctx e
    let Yes Refl = decEq tty ety
        | No _ => Error fi [mkTD thenDeriv, mkTD elseDeriv] "arms of conditional have different types"
    pure (tty ** TIf fi pDeriv thenDeriv elseDeriv)
  inferType ctx (Var fi i) = do
    let Yes (ty ** inCtx) = inContext ctx i
        | No _ => Error fi [] "Variable not found \{show i}"
    pure (ty ** (TVar fi inCtx))
  inferType ctx (Abs fi var ty t) = do
    (ty2 ** tDeriv) <- inferType (addBinding var ty ctx) t
    pure (Arr ty ty2 ** TAbs fi tDeriv)
  inferType ctx (App fi t1 t2) = do
    (ty1 ** t1Deriv) <- inferType ctx t1
    (ty2 ** t2Deriv) <- inferType ctx t2
    case ty1 of
      Arr aty1 aty2 => case decEq ty2 aty1 of
        Yes Refl
          => pure (aty2 ** TApp fi t1Deriv t2Deriv)
        No _
          => Error fi [mkTD t2Deriv] "parameter type mismatch"
      _ => Error fi [mkTD t1Deriv] "arrow type expected"
  inferType ctx (Unit fi) = pure (Unit ** TUnit fi)
  inferType ctx (Seq fi t1 t2) = do
    (Unit ** t1Deriv) <- inferType ctx t1
      | (_ ** wrongDeriv) => Error fi [mkTD wrongDeriv] "First arm of sequence doesn't have Unit type"
    (ty2 ** t2Deriv) <- inferType ctx t2
    pure (ty2 ** TSeq fi t1Deriv t2Deriv)
  inferType ctx (As fi t ty) = do
    (ty1 ** tDeriv) <- inferType ctx t
    let Yes Refl = decEq ty ty1
        | No _ => Error fi [mkTD tDeriv] "Found type is different than ascribed type"
    pure (ty ** TAscribe fi tDeriv)
  inferType ctx (Let fi n t b) = do
    (ty1 ** tDeriv) <- inferType ctx t
    (ty2 ** bDeriv) <- inferType (addBinding n ty1 ctx) b
    pure $ (ty2 ** TLet fi tDeriv bDeriv)
  inferType ctx (Pair fi t1 t2) = do
    (ty1 ** t1Deriv) <- inferType ctx t1
    (ty2 ** t2Deriv) <- inferType ctx t2
    pure $ (Product ty1 ty2 ** TPair fi t1Deriv t2Deriv)
  inferType ctx (First fi t) = do
    (Product ty1 ty2 ** tDeriv) <- inferType ctx t
      | (_ ** wrongDeriv) => Error fi [mkTD wrongDeriv] "Found type is different than product"
    pure (ty1 ** TProj1 fi tDeriv)
  inferType ctx (Second fi t) = do
    (Product ty1 ty2 ** tDeriv) <- inferType ctx t
      | (_ ** wrongDeriv) => Error fi [mkTD wrongDeriv] "Found type is different than product"
    pure (ty2 ** TProj2 fi tDeriv)
  inferType ctx (Tuple fi n tms) = do
    (tys ** tty) <- inferTypes ctx tms
    pure (Tuple n tys ** TTuple fi tty)
  inferType ctx (Proj fi t n idx) = do
    (Tuple m tys ** tDeriv) <- inferType ctx t
      | (_ ** wrongDeriv) => Error fi [mkTD wrongDeriv] "Found type is different than tuple"
    let Yes Refl = decEq n m
        | No _ => Error fi [mkTD tDeriv] "Tuple have different arity than expected"
    pure (index idx tys ** (TProj fi tDeriv))
  inferType ctx (Variant fi tag tj ty) = do
    let (Variant (MkVariant n tags tys u nz)) = ty
        | _ => Error fi [] "Should have been type of Variant." -- TODO: Got ty
    (tyj1 ** tDeriv) <- inferType ctx tj
    let Just (j ** (idx1, (tyj2 ** idx2))) = fieldIndex tag (MkVariant n tags tys u nz)
        | Nothing => Error fi [] "\{tag} is not found in the Variant." -- TODO: Describe variants more
    let Yes Refl = decEq tyj2 tyj1
        | No _ => Error fi [mkTD tDeriv] "Found type in variant was different than expected." -- TODO: Got ty
    pure ((Variant (MkVariant n tags tys u nz)) ** TVariant fi idx1 idx2 tDeriv)
  inferType ctx (Case fi t0 (MkVariant n tags alts u nz)) = do
    (Variant (MkVariant n_t0 tags_t0 tys_t0 u_t0 nz_t0) ** t0Deriv) <- inferType ctx t0
    let Yes Refl = decEq n n_t0
        | No _ => Error fi [mkTD t0Deriv] "Record had different arity" -- TODO: Expected, got
    let Yes Refl = decEq nz nz_t0
        | No _ => Error fi [mkTD t0Deriv] "Internal error: Different non-zeros in Record type inference."
    let Yes Refl = decEq tags tags_t0
        | No _ => Error fi [mkTD t0Deriv] "Tags were different" -- TODO: Expected got
    let Yes Refl = decEq u u_t0
        | No _ => Error fi [mkTD t0Deriv] "Internal error: Different unique-tag derivations in Record type inference."
    (ty ** vDerivs) <- inferVariantTypes fi n_t0 nz_t0 ctx alts tys_t0
    pure (ty ** TCase fi t0Deriv vDerivs)

  inferTypes : (ctx : Context) -> (tms : Vect n Tm) -> Infer (tys : Vect n Ty ** Derivations ctx tms tys)
  inferTypes ctx [] = pure ([] ** [])
  inferTypes ctx (t :: ts) = do
    (ty  ** tDeriv) <- inferType  ctx t
    (tys ** fields) <- inferTypes ctx ts
    pure (ty :: tys ** (MkDerivation t ty tDeriv) :: fields)

  -- Check if all the alternatives has the same type in their branches.
  inferVariantTypes
    :  (fi : Info) -> (n : Nat) -> (nz : NonZero n) -> (ctx : Context) -> (alts : Vect n (Name, Tm)) -> (tys : Vect n Ty)
    -> Infer (ty : Ty ** VariantDerivations n ctx alts tys ty)
  inferVariantTypes fi (S 0) SIsNonZero ctx ((var,tm) :: []) (t :: []) = do
    (tmty ** tmDeriv) <- inferType (ctx :< (var,VarBind t)) tm
    pure (tmty ** [MkDerivation tm tmty tmDeriv])
  inferVariantTypes fi (S (S n)) SIsNonZero ctx ((var,tm) :: (a :: as)) (t :: (ty :: tys)) = do
    (tyh ** hDeriv) <- inferType (ctx :< (var,VarBind t)) tm
    (tyt ** variantDerivs) <- inferVariantTypes fi (S n) SIsNonZero ctx (a :: as) (ty :: tys)
    let Yes Refl = decEq tyh tyt
        | No _ => Error fi [mkTD hDeriv] "Different type found for alternative." -- TODO
    pure (tyt ** (MkDerivation tm tyt hDeriv :: variantDerivs))

-- Substituition assumes unique names, no need for alpha conversions.
-- TODO: Check if this right.
total
substituition : (Name, Tm) -> Tm -> Tm
-- substituition (n, tm1) (Var var) = case decEq n var of
--   (Yes prf)   => tm1
--   (No contra) => (Var var)
-- substituition s (Abs var ty t) = Abs var ty (substituition s t)
-- substituition s (App t1 t2) = App (substituition s t1) (substituition s t2)
-- substituition s True = True
-- substituition s False = False

data Evaluation : Tm -> Tm -> Type where

  EApp1 :
                Evaluation t1 t1'          ->
    -----------------------------------------
    Evaluation (App fi t1 t2) (App fi t1' t2)
  
  EApp2 :
                      Value v1            ->
                  Evaluation t t'        ->
    ---------------------------------------            
    Evaluation (App fi v1 t) (App fi v1 t')

  EAppAbs :
                                Value v                           ->
    ---------------------------------------------------------------
    Evaluation (App fi1 (Abs fi2 x ty t) v) (substituition (x,v) t)
  
  ESeq :
                Evaluation t1 t1'          ->
    -----------------------------------------
    Evaluation (Seq fi t1 t2) (Seq fi t1' t2)

  ESeqNext :
    -------------------------------------
    Evaluation (Seq fi1 (Unit fi2) t2) t2

  EAscribeV :
             Value v       ->
    -------------------------
    Evaluation (As fi v ty) v 

  EAscribe :
               Evaluation t t'         ->
    -------------------------------------
    Evaluation (As fi t ty) (As fi t' ty)

  ELetV :
                          Value v                    ->
    ---------------------------------------------------
    Evaluation (Let fi x v t2) (substituition (x,v) t2)
  
  ELet :
                  Evaluation t t'            ->
    -------------------------------------------
    Evaluation (Let fi x t t2) (Let fi c t' t2)

  EPairBeta1 :
             Value v1 -> Value v2           ->
    ------------------------------------------
    Evaluation (First fi1 (Pair fi2 v1 v2)) v1
  
  EPairBeta2 :
              Value v1 -> Value v2           ->
    -------------------------------------------
    Evaluation (Second fi1 (Pair fi2 v1 v2)) v2

  EProj1 :
               Evaluation t t'         ->
    -------------------------------------
    Evaluation (First fi t) (First fi t')

  EProj2 :
                Evaluation t t'          ->
    ---------------------------------------
    Evaluation (Second fi t) (Second fi t')

  EPair1 :
                 Evaluation t1 t1'           ->
    -------------------------------------------
    Evaluation (Pair fi t1 t2) (Pair fi t1' t2)

  EPair2 :
                      Value v1               ->
                 Evaluation t2 t2'           ->
    -------------------------------------------
    Evaluation (Pair fi t1 t2) (Pair fi t1 t2')

  EProjTuple :
                   Value (Tuple fi2 n tms)                 ->
    ---------------------------------------------------------
    Evaluation (Proj fi1 (Tuple fi2 n tms) n j) (index j tms)

  EProj :
                  Evaluation t t'            ->
    -------------------------------------------
    Evaluation (Proj fi t n i) (Proj fi t' n i)

  ETuple :
                  {n,m : Nat} -> {vs : Vect n Tm} -> {t : Tm} -> {ts : Vect m Tm}                  ->
                                ForEach vs Value -> Evaluation t t'                                ->
    -------------------------------------------------------------------------------------------------
      Evaluation
        (Tuple fi (n + (1 + m)) (vs ++ (t :: ts)))
        (Tuple fi (n + (1 + m)) (vs ++ (t' :: ts)))

  EProjRec :
    {r : Record Tm} -> {inr : InRecord field v r.fields r.values}  ->
                        (vs : ForEach r.values Value)              ->
    -----------------------------------------------------------------                        
             Evaluation (ProjField fi1 field (Record fi2 r)) v

  EProjField :
                        Evaluation t t'                    ->
    ---------------------------------------------------------
    Evaluation (ProjField fi field t) (ProjField fi field t')

  ERcd :
                 {n,m : Nat}                                                           ->
                 {lvs : Vect n String} -> {f : String} -> {lts : Vect m String}        ->
                 {vs  : Vect n   Tm  } -> {t :   Tm  } -> {ts  : Vect m   Tm  }        ->
                         {u : UniqueFields (lvs ++ (f :: lts))}                        ->
                           ForEach vs Value -> Evaluation t t'                         ->
    -------------------------------------------------------------------------------------
        Evaluation
          (Record fi (MkRecord (n + (1 + m)) (lvs ++ (f :: lts)) (vs ++ (t  :: ts)) u))
          (Record fi (MkRecord (n + (1 + m)) (lvs ++ (f :: lts)) (vs ++ (t' :: ts)) u))

  ECase :
                   Evaluation t0 t0'             ->
    -----------------------------------------------
    Evaluation (Case fi t0 tags) (Case fi t0' tags)

  EVariant :
                        Evaluation t t'                  ->
    -------------------------------------------------------
    Evaluation (Variant fi tag t ty) (Variant fi tag t' ty)

  ECaseVariant :
                            {n : Nat} -> {nz : NonZero n}                           ->
    {tags : Vect n String} -> {alts : Vect n (Name, Tm)} -> {u : UniqueTags n tags} ->
                             ForEach alts (Value . snd)                             ->
                             InVariant tag x vj tags alts                           ->
    ----------------------------------------------------------------------------------
            Evaluation
              (Case fi1 (Variant fi2 tag t ty) (MkVariant n tags alts u nz))
              (substituition (x,vj) tj)
