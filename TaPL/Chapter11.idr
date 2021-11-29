module TaPL.Chapter11

import Decidable.Equality

Name : Type
Name = String

data Ty : Type
data Info  : Type

data Binding : Type where
  NameBind : Binding
  VarBind  : (ty : Ty) -> Binding

data Context : Type where
  Lin  : Context
  (:<) : Context -> (Name, Binding) -> Context

data InContext : Nat -> Context -> Type where
  Here  : InContext 0 (ctx :< b)
  There : InContext n ctx -> InContext (S n) (ctx :< b)

Uninhabited (InContext 0     Lin) where uninhabited _ impossible
Uninhabited (InContext (S _) Lin) where uninhabited _ impossible

total
thereInjective : InContext (S n) (ctx :< b) -> InContext n ctx
thereInjective (There x) = x

total
inContext : (ctx : Context) -> (i : Nat) -> Dec (InContext i ctx)
inContext [<]       0     = No uninhabited
inContext [<]       (S k) = No uninhabited
inContext (x :< y)  0     = Yes Here
inContext (x :< y)  (S k) = case inContext x k of
  (Yes found) => Yes $ There found
  (No contra) => No (\assumeFound => contra (thereInjective assumeFound))

indexToName : (ctx : Context) -> (i : Nat) -> {auto inCtx : InContext i ctx} -> Name
indexToName (ctx :< b) 0      {inCtx = Here}      = fst b
indexToName (ctx :< b) (S n)  {inCtx = (There y)} = indexToName ctx n

addBinding : Name -> Ty -> Context -> Context
addBinding n ty ctx = ctx :< (n, VarBind ty)

data Infer : Type -> Type where
  Pure : a -> Infer a
  Bind : Infer a -> (a -> Infer b) -> Infer b

  Error : {a : Type} -> Info -> String -> Infer a
  GetTypeFromContext : Info -> (ctx : Context) -> (i : Nat) -> (InContext i ctx) => Infer Ty
  GetInContext : (ctx : Context) -> (i : Nat) -> Infer (InContext i ctx)
  AddBinding : Name -> Ty -> Context -> Infer Context

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

getBinding : Info -> (ctx : Context) -> (i : Nat) -> {auto inCtx : InContext i ctx} -> Binding
getBinding fi (ctx :< b) 0     {inCtx = Here}      = snd b
getBinding fi (ctx :< b) (S n) {inCtx = (There x)} = getBinding fi ctx n


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

namespace Value

  public export
  data Value : Tm -> Type where
    Abs   : Value (Abs fi var ty t)
    True  : Value (True fi)
    False : Value (False fi)
    Unit  : Value (Unit fi)
    Pair  : Value v1 -> Value v2 -> Value (Pair fi v1 v2)

public export
data Ty : Type where
  Bool : Ty
  Arr  : Ty -> Ty -> Ty
  Base : String -> Ty
  Unit : Ty
  Product : Ty -> Ty -> Ty

namespace Context

  public export
  data InGamma : Name -> Ty -> Context -> Type where
    Here  : InGamma n ty (g :< (n,VarBind ty))
    There : (Not (n = m)) -> InGamma n ty g -> InGamma n ty (g :< (m,VarBind tz))

infix 11 <:>

data TypeStatement : Type where
  (<:>) : (t1 : Tm) -> (t2 : Ty) -> TypeStatement

infix 10 |-

data (|-) : Context -> TypeStatement -> Type where

  TVar :
      InContext x gamma ->
    -----------------------
     gamma |- Var fi x <:> ty
  
  TAbs :
     (gamma :< (x,VarBind ty1)) |- tm2 <:> ty2  ->
  ---------------------------------------- - Introduction rule for Arr
   gamma |- Abs fi1 x ty1 tm2 <:> Arr ty1 ty2

  TApp :
    (gamma |- tm1 <:> Arr ty11 ty12) -> (gamma |- tm2 <:> ty11) ->
    -------------------------------------------------------------- - Elimination rule for Arr
                    gamma |- App fi tm1 tm2 <:> ty12

  TTrue :
    ----------------------
    gamma |- True fi <:> Bool

  TFalse :
    -----------------------
    gamma |- False fi <:> Bool

  TIf :
    (gamma |- tmp <:> Bool) -> (gamma |- tmt <:> ty) -> (gamma |- tme <:> ty) ->
    ----------------------------------------------------------------------------
                     gamma |- (If fi tmp tmt tme <:> ty)

  TUnit :
    -------------------------
    gamma |- Unit fi <:> Unit

  TSeq :
    (gamma |- t1 <:> Unit) -> (gamma |- t2 <:> ty2) ->
    --------------------------------------------------
            gamma |- Seq fi t1 t2 <:> ty2

  TAscribe :
        (gamma |- t1 <:> ty1)  ->
    -----------------------------
    gamma |- As fi t1 ty1 <:> ty1

  TLet :
    (gamma |- (t1 <:> ty1)) -> ((gamma :< (x,VarBind ty1)) |- t2 <:> ty2) ->
    ------------------------------------------------------------------------
                       gamma |- Let fi x t1 t2 <:> ty2

  TPair :
    (gamma |- (t1 <:> ty1)) -> (gamma |- (t2 <:> ty2)) ->
    -----------------------------------------------------
          gamma |- Pair fi t1 t2 <:> Product ty1 ty2

  TProj1 :
    (gamma |- (t1 <:> Product ty1 ty2)) ->
    --------------------------------------
          gamma |- First fi t1 <:> ty1

  TProj2 :
    (gamma |- (t1 <:> Product ty1 ty2)) ->
    --------------------------------------
         gamma |- Second fi t1 <:> ty1


funInjective : (Arr x y = Arr z w) -> (x = z, y = w)
funInjective Refl = (Refl, Refl)

Uninhabited (Bool = Arr _ _) where uninhabited _ impossible
Uninhabited (Arr _ _ = Bool) where uninhabited _ impossible

getTypeFromContext : Info -> (ctx : Context) -> (i : Nat) -> (InContext i ctx) => Infer Ty
getTypeFromContext fi ctx i = do
  let VarBind ty = getBinding fi ctx i
      | _ => Error fi "Wrong kind of binding for variable \{indexToName ctx i}"
  pure ty

-- covering -- ???
typeOf : (ctx : Context) -> (t : Tm) -> Infer Ty
typeOf ctx (True fi)  = pure Bool
typeOf ctx (False fi) = pure Bool
typeOf ctx (If fi p t e) = do
  Bool <- typeOf ctx p
    | _ => Error fi "guard of conditional is not a Bool"
  tty <- typeOf ctx t
  ety <- typeOf ctx e
  let Yes _ = decEq tty ety
      | No _ => Error fi "arms of conditional have different types"
  pure tty
typeOf ctx (Var fi i) = do
  inCtx <- GetInContext ctx i
  GetTypeFromContext fi ctx i
typeOf ctx (Abs fi var ty t) = do
  ctx' <- AddBinding var ty ctx
  ty2 <- typeOf ctx' t
  pure $ Arr ty ty2
typeOf ctx (App fi t1 t2) = do
  ty1 <- typeOf ctx t1
  ty2 <- typeOf ctx t2
  case ty1 of
    Arr aty1 aty2 => case decEq ty2 aty1 of
      Yes _ => pure aty2
      No  _ => Error fi "parameter type mismatch"
    _ => Error fi "arrow type expected"
typeOf ctx (Unit fi) = pure Unit
typeOf ctx (Seq fi t1 t2) = do
  Unit <- typeOf ctx t1
    | _ => Error fi "First arm of sequence doesn't have Unit type"
  typeOf ctx t2
typeOf ctx (As fi t1 ty) = do
  ty1 <- typeOf ctx t1
  case decEq ty1 ty of
    Yes _ => pure ty
    No _ => Error fi "Found type is different than ascribed type"
typeOf ctx (Let fi x t b) = do
  ty1 <- typeOf ctx t
  ctx' <- AddBinding x ty1 ctx
  typeOf ctx b
typeOf ctx (Pair fi t1 t2) = do
  ty1 <- typeOf ctx t1
  ty2 <- typeOf ctx t2
  pure $ Product ty1 ty2
typeOf ctx (First fi t) = do
  Product ty1 ty2 <- typeOf ctx t
    | _ => Error fi "Found type is different than product"
  pure ty1
typeOf ctx (Second fi t) = do
  Product ty1 ty2 <- typeOf ctx t
    | _ => Error fi "Found type is different than product"
  pure ty2

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

  EProf1 :
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
