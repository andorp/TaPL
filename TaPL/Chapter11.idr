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

namespace Value

  public export
  data Value : Tm -> Type where
    Abs   : Value (Abs fi var ty t)
    True  : Value (True fi)
    False : Value (False fi)
    Unit  : Value (Unit fi)

public export
data Ty : Type where
  Bool : Ty
  Arr  : Ty -> Ty -> Ty
  Base : String -> Ty
  Unit : Ty

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

funInjective : (Arr x y = Arr z w) -> (x = z, y = w)
funInjective Refl = (Refl, Refl)

Uninhabited (Bool = Arr _ _) where uninhabited _ impossible
Uninhabited (Arr _ _ = Bool) where uninhabited _ impossible

getTypeFromContext : Info -> (ctx : Context) -> (i : Nat) -> (InContext i ctx) => Infer Ty
getTypeFromContext fi ctx i = do
  let VarBind ty = getBinding fi ctx i
      | _ => Error fi "Wrong kind of binding for variable \{indexToName ctx i}"
  pure ty

typeOf : (ctx : Context) -> (t : Tm) -> Infer Ty
typeOf ctx (True fi)  = pure Bool
typeOf ctx (False fi) = pure Bool
typeOf ctx (Unit fi) = pure Unit
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

-- typeOf : (ctx : Context) -> (t : Tm) -> Infer Ty

-- Continuation from Chapter10

