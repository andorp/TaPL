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

getBinding : Info -> (ctx : Context) -> (i : Nat) -> (inCtx : InContext i ty ctx) -> Binding
getBinding fi (ctx :< (n, VarBind ty)) 0     Here      = VarBind ty
getBinding fi (ctx :< b)               (S n) (There x) = getBinding fi ctx n x

DecEq Ty where
  decEq _ _ = ?h1
  -- decEq Bool Bool = Yes Refl
  -- decEq Bool (Arr x y) = No uninhabited
  -- decEq (Arr x y) Bool = No uninhabited
  -- decEq (Arr x y) (Arr z w) = case (decEq x z, decEq y w) of
  --   ((Yes xIsZ)   , (Yes yIsW)   ) => Yes $ rewrite xIsZ in rewrite yIsW in Refl
  --   ((Yes xIsZ)   , (No contraYW)) => No (\assumeArrYW => contraYW (snd (funInjective assumeArrYW)))
  --   ((No contraXZ), (Yes yIsW)   ) => No (\assumeArrXZ => contraXZ (fst (funInjective assumeArrXZ)))
  --   ((No contraXZ), (No contraYW)) => No (\assumeArrXZ => contraXZ (fst (funInjective assumeArrXZ)))

data ForEach : Vect n a -> (p : a -> Type) -> Type where
  Nil  : ForEach [] p
  (::) : {xs : Vect n a} -> (p x) -> ForEach xs p -> ForEach (x :: xs) p

namespace Record

  namespace NotInt
  
    public export
    data NotIn : String -> Vect n String -> Type where
      Nil  : NotIn n []
      (::) : Not (n = f) -> NotIn n fs -> NotIn n (f :: fs)

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
    0 uniqueFields : UniqueFields fields

  public export
  data InRecord : String -> a -> Vect n String -> Vect n a -> Type where
    Here  : InRecord f x (f :: fs) (x :: xs)
    There : InRecord f x fs xs -> InRecord f x (g :: fs) (y :: xs)

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

namespace Value

  public export
  data Value : Tm -> Type where
    Abs   : Value (Abs fi var ty t)
    True  : Value (True fi)
    False : Value (False fi)
    Unit  : Value (Unit fi)
    Pair  : Value v1 -> Value v2 -> Value (Pair fi v1 v2)
    Tuple : {n : Nat} -> {tms : Vect n Tm} -> ForEach tms Value -> Value (Tuple fi n tms)
    Record : {n : Nat} -> (r : Record Tm) -> ForEach r.values Value -> Value (Record fi r) 

public export
data Ty : Type where
  Bool : Ty
  Arr  : Ty -> Ty -> Ty
  Base : String -> Ty
  Unit : Ty
  Product : Ty -> Ty -> Ty
  Tuple : (n : Nat) -> Vect n Ty -> Ty
  Record : (r : Record Ty) -> Ty

data TypeStatement : Type where
  (<:>) : (0 t1 : Tm) -> (t2 : Ty) -> TypeStatement

namespace DerivList

  public export
  data Derivation : Context -> Tm -> Ty -> Type where
    MkDerivation : (t : Tm) -> (ty : Ty) -> (deriv : (ctx |- t <:> ty)) -> Derivation ctx t ty

  public export
  data Derivations : Context -> Vect n Tm -> Vect n Ty -> Type where
    Nil  : Derivations ctx [] []
    (::) : Derivation ctx t ty -> Derivations ctx ts tys -> Derivations ctx (t :: ts) (ty :: tys)

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

funInjective : (Arr x y = Arr z w) -> (x = z, y = w)
funInjective Refl = (Refl, Refl)

Uninhabited (Bool = Arr _ _) where uninhabited _ impossible
Uninhabited (Arr _ _ = Bool) where uninhabited _ impossible

data TypeDerivation : Type where
  MkTypeDerivation : (0 ctx : Context) -> (0 t : Tm) -> (0 ty : Ty) -> (deriv : (ctx |- t <:> ty)) -> TypeDerivation

mkTD : (ctx |- t <:> ty) -> TypeDerivation
mkTD deriv = MkTypeDerivation ctx t ty deriv

mutual

  deriveType : (ctx : Context) -> (t : Tm) -> Infer (ty : Ty ** (ctx |- t <:> ty))
  deriveType ctx (True fi) = pure (Bool ** TTrue fi)
  deriveType ctx (False fi) = pure (Bool ** TFalse fi)
  deriveType ctx (If fi p t e) = do
    (Bool ** pDeriv) <- deriveType ctx p
      | (_ ** wrongDeriv) => Error fi [mkTD wrongDeriv] "guard of conditional is not a Bool"
    (tty ** thenDeriv) <- deriveType ctx t
    (ety ** elseDeriv) <- deriveType ctx e
    let Yes tty_is_ety = decEq tty ety
        | No _ => Error fi [mkTD thenDeriv, mkTD elseDeriv] "arms of conditional have different types"
    pure (tty ** TIf fi pDeriv thenDeriv (rewrite tty_is_ety in elseDeriv))
  deriveType ctx (Var fi i) = do
    let Yes (ty ** inCtx) = inContext ctx i
        | No _ => Error fi [] "Variable not found \{show i}"
    pure (ty ** (TVar fi inCtx))
  deriveType ctx (Abs fi var ty t) = do
    (ty2 ** tDeriv) <- deriveType (addBinding var ty ctx) t
    pure (Arr ty ty2 ** TAbs fi tDeriv)
  deriveType ctx (App fi t1 t2) = do
    (ty1 ** t1Deriv) <- deriveType ctx t1
    (ty2 ** t2Deriv) <- deriveType ctx t2
    case ty1 of
      Arr aty1 aty2 => case decEq ty2 aty1 of
        Yes t2_is_aty2
          => pure (aty2 ** TApp fi t1Deriv (rewrite (sym t2_is_aty2) in t2Deriv))
        No _
          => Error fi [mkTD t2Deriv] "parameter type mismatch"
      _ => Error fi [mkTD t1Deriv] "arrow type expected"
  deriveType ctx (Unit fi) = pure (Unit ** TUnit fi)
  deriveType ctx (Seq fi t1 t2) = do
    (Unit ** t1Deriv) <- deriveType ctx t1
      | (_ ** wrongDeriv) => Error fi [mkTD wrongDeriv] "First arm of sequence doesn't have Unit type"
    (ty2 ** t2Deriv) <- deriveType ctx t2
    pure (ty2 ** TSeq fi t1Deriv t2Deriv)
  deriveType ctx (As fi t ty) = do
    (ty1 ** tDeriv) <- deriveType ctx t
    case decEq ty ty1 of
      Yes ty_is_ty1 => pure (ty ** TAscribe fi (rewrite ty_is_ty1 in tDeriv))
      No  _         => Error fi [mkTD tDeriv] "Found type is different than ascribed type"
  deriveType ctx (Let fi n t b) = do
    (ty1 ** tDeriv) <- deriveType ctx t
    (ty2 ** bDeriv) <- deriveType (addBinding n ty1 ctx) b
    pure $ (ty2 ** TLet fi tDeriv bDeriv)
  deriveType ctx (Pair fi t1 t2) = do
    (ty1 ** t1Deriv) <- deriveType ctx t1
    (ty2 ** t2Deriv) <- deriveType ctx t2
    pure $ (Product ty1 ty2 ** TPair fi t1Deriv t2Deriv)
  deriveType ctx (First fi t) = do
    (Product ty1 ty2 ** tDeriv) <- deriveType ctx t
      | (_ ** wrongDeriv) => Error fi [mkTD wrongDeriv] "Found type is different than product"
    pure (ty1 ** TProj1 fi tDeriv)
  deriveType ctx (Second fi t) = do
    (Product ty1 ty2 ** tDeriv) <- deriveType ctx t
      | (_ ** wrongDeriv) => Error fi [mkTD wrongDeriv] "Found type is different than product"
    pure (ty2 ** TProj2 fi tDeriv)
  deriveType ctx (Tuple fi n tms) = do
    (tys ** tty) <- deriveTypes ctx tms
    pure (Tuple n tys ** TTuple fi tty)
  deriveType ctx (Proj fi t n idx) = do
    (Tuple m tys ** tDeriv) <- deriveType ctx t
      | (_ ** wrongDeriv) => Error fi [mkTD wrongDeriv] "Found type is different than tuple"
    let Yes n_is_m = decEq n m
        | No _ => Error fi [mkTD tDeriv] "Tuple have different arity than expected"
    pure (index (rewrite (sym n_is_m) in idx) tys ** (TProj fi (rewrite n_is_m in tDeriv)))

  deriveTypes : (ctx : Context) -> (tms : Vect n Tm) -> Infer (tys : Vect n Ty ** Derivations ctx tms tys)
  deriveTypes ctx [] = pure ([] ** [])
  deriveTypes ctx (t :: ts) = do
    (ty  ** tDeriv) <- deriveType  ctx t
    (tys ** fields) <- deriveTypes ctx ts
    pure (ty :: tys ** (MkDerivation t ty tDeriv) :: fields)

-- typeOf : (ctx : Context) -> (t : Tm) -> Infer Ty

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
                 {vs  : Vect n Tm    } -> {t : Tm    } -> {ts  : Vect m Tm}            ->
                         {u : UniqueFields (lvs ++ (f :: lts))}                        ->
                           ForEach vs Value -> Evaluation t t'                         ->
    -------------------------------------------------------------------------------------
        Evaluation
          (Record fi (MkRecord (n + (1 + m)) (lvs ++ (f :: lts)) (vs ++ (t :: ts)) u))
          (Record fi (MkRecord (n + (1 + m)) (lvs ++ (f :: lts)) (vs ++ (t' :: ts)) u))
