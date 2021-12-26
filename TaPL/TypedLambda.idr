module TaPL.TypedLambda

import Data.List
import Decidable.Equality

Name : Type
Name = String

data Ty   : Type

data Info : Type where
  EmptyInfo : Info

data Binding : Type where
  NameBind : Binding
  VarBind  : (ty : Ty) -> Binding

data Context : Type where
  Lin  : Context
  (:<) : Context -> (Name, Binding) -> Context

data InContext : Nat -> Context -> Type where
  Here  : InContext 0 (ctx :< b)
  There : InContext n ctx -> InContext (S n) (ctx :< b)

Uninhabited (InContext _ Lin) where uninhabited _ impossible

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

data Ty : Type where
  Arr  : Ty -> Ty -> Ty

getTypeFromContext : Info -> (ctx : Context) -> (i : Nat) -> (InContext i ctx) => Infer Ty
getTypeFromContext fi ctx i = do
  let VarBind ty = getBinding fi ctx i
      | _ => Error fi "Wrong kind of binding for variable \{indexToName ctx i}"
  pure ty

funInjective : (Arr x y = Arr z w) -> (x = z, y = w)
funInjective Refl = (Refl, Refl)

Uninhabited (Bool = Arr _ _) where uninhabited _ impossible
Uninhabited (Arr _ _ = Bool) where uninhabited _ impossible

DecEq Ty where
  decEq (Arr x y) (Arr z w) = case (decEq x z, decEq y w) of
    ((Yes xIsZ)   , (Yes yIsW)   ) => Yes $ rewrite xIsZ in rewrite yIsW in Refl
    ((Yes xIsZ)   , (No contraYW)) => No (\assumeArrYW => contraYW (snd (funInjective assumeArrYW)))
    ((No contraXZ), (Yes yIsW)   ) => No (\assumeArrXZ => contraXZ (fst (funInjective assumeArrXZ)))
    ((No contraXZ), (No contraYW)) => No (\assumeArrXZ => contraXZ (fst (funInjective assumeArrXZ)))

data Tm : Type where
  Var   : (fi : Info) -> (i : Nat)                              -> Tm 
  Abs   : (fi : Info) -> (var : Name) -> (ty : Ty) -> (t : Tm)  -> Tm
  App   : (fi : Info) -> (t1, t2 : Tm)                          -> Tm

namespace Value

  public export
  data Value : Tm -> Type where
    Abs   : Value (Abs fi var ty t)

  export Uninhabited (Value (Var _ _))      where uninhabited x impossible
  export Uninhabited (Value (App _ _ _))    where uninhabited x impossible

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
                               {ty11 : Ty}                      ->
    (gamma |- tm1 <:> Arr ty11 ty12) -> (gamma |- tm2 <:> ty11) ->
    -------------------------------------------------------------- - Elimination rule for Arr
                    gamma |- App fi tm1 tm2 <:> ty12

typeOf : (ctx : Context) -> (t : Tm) -> Infer (ty : Ty ** ctx |- t <:> ty)
typeOf ctx (Var fi i) = do
  let Yes inCtx = inContext ctx i
    | No _ => Error fi ""
  ty <- getTypeFromContext fi ctx i
  pure (ty ** TVar inCtx)
typeOf ctx (Abs fi var ty t) = do
  (ty2 ** ty2Deriv) <- typeOf (addBinding var ty ctx) t
  pure (Arr ty ty2 ** TAbs ty2Deriv)
typeOf ctx (App fi t1 t2) = do
  (ty1 ** ty1Deriv) <- typeOf ctx t1
  (ty2 ** ty2Deriv) <- typeOf ctx t2
  case ty1 of
    Arr aty1 aty2 => case decEq ty2 aty1 of
      Yes Refl => pure (aty2 ** TApp ty1Deriv ty2Deriv)
      No  _ => Error fi "parameter type mismatch"
    _ => Error fi "arrow type expected"

data Substitution : Type where
  Subst : (x : Name) -> (s : Tm) -> Substitution

substitution : Substitution -> Tm -> Tm
substitution (Subst var s) t = subst [] t
  where
    subst : List Name -> Tm -> Tm
    subst xs (Var fi i) = case inBounds i xs of
      Yes found => case index i xs == var of
        False => Var fi i
        True  => s
      No notFound => Var fi i -- This shouldn't happen. Improve subst later on.
    subst xs (Abs fi y ty t)  = Abs fi y ty (subst (y :: xs) t)
    subst xs (App fi t1 t2)   = App fi (subst xs t1) (subst xs t2)

-- Operational semantics
namespace Evaluation

  -- data Value : Term -> Type where
  --   Lam : Value (Lam x t)

  data Evaluation : Tm -> Tm -> Type where

    EApp1
      :             Not (Value t1)           -> 
                   Evaluation t1 t1'         ->
      -----------------------------------------
      Evaluation (App fi t1 t2) (App fi t1' t2)

    EApp2
      :               Value v1               ->
                   Not (Value t2)            ->
                   Evaluation t2 t2'         ->
      -----------------------------------------
      Evaluation (App fi v1 t2) (App fi v1 t2')

    EAppAbs :
                  Value t2          ->
      --------------------------------
      Evaluation
        (App fi2 (Abs fi1 x ty t1) t2)
        (substitution (Subst x t2) t1)

  public export total
  CanonicalFormTy : (t : Tm) -> (ty : Ty) -> Type
  CanonicalFormTy t (Arr ty1 ty2) = (fi : Info ** (var : Name ** (t2 : Tm ** t = Abs fi var ty1 t2)))

  public export total
  cannonicalFormArr
    :  (t : Tm) -> (gamma |- (t <:> Arr ty1 ty2)) -> (v : Value t)
    -> (fi : Info ** (var : Name ** (t2 : Tm ** t = Abs fi var ty1 t2)))
  cannonicalFormArr (Abs fi var ty1 t) (TAbs y) Abs = (fi ** (var ** (t ** Refl)))

  public export total
  cannonicalForms : (t : Tm) -> (ty : Ty) -> (gamma |- (t <:> ty)) -> (v : Value t) -> CanonicalFormTy t ty
  cannonicalForms t (Arr y z) td v = cannonicalFormArr t td v

  data Progress : Tm -> Type where
    PrgVal  : (fi : Info) -> (Value t) -> Progress t
    PrgEval : (fi : Info) -> (Not (Value t)) -> (t' : Tm) -> (Evaluation t t') -> Progress t

  progressPure : (t : Tm) -> (ty : Ty) -> ([<] |- (t <:> ty)) -> Progress t
  progressPure (Var fi x1) ty (TVar x) = absurd (uninhabited x)
  progressPure (Abs fi1 x1 ty1 tm2) (Arr ty1 ty2) (TAbs x) = PrgVal fi1 Abs
  progressPure (App fi1 t1 t2) ty (TApp {ty11 = ty11} t2ty t1ty) = case progressPure t1 (Arr ty11 ty) t2ty of
    (PrgVal  _ t1Value) => case progressPure t2 ty11 t1ty of
      (PrgVal  _ t2Value) => case cannonicalForms t1 (Arr ty11 ty) t2ty t1Value of
        (MkDPair fi (MkDPair var (MkDPair t Refl))) => PrgEval fi1 uninhabited (substitution (Subst var t2) t) (EAppAbs t2Value)
      (PrgEval _ t2NotValue t2' t2Infer)            => PrgEval fi1 uninhabited (App fi1 t1 t2') (EApp2 t1Value t2NotValue t2Infer)
    (PrgEval _ t1NotValue t1' t1Infer)              => PrgEval fi1 uninhabited (App fi1 t1' t2) (EApp1 t1NotValue t1Infer)

  namespace EvalMonad

    public export
    data Eval : Type -> Type where
      Pure : (x : t) -> Eval t
      Bind : (Eval a) -> (a -> Eval b) -> Eval b
      OnProgress : {t : Tm} -> (p : Progress t) -> Eval ()

    record EvalImpl (m : Type -> Type) where
      constructor MkEvalImpl
      -- monad         : Type -> Type
      -- monadInstance : Monad monad
      onValue       : (fi : Info) -> {t : Tm} -> Value t -> m ()
      onStep        : (fi : Info) -> {t,t' : Tm} -> Evaluation t t' -> m ()

    export
    evalInterpreter : (Monad m) => (EvalImpl m) -> Eval a -> m a
    evalInterpreter i (Pure x)    = pure x
    evalInterpreter i (Bind m k)  = evalInterpreter i m >>= (evalInterpreter i . k)
    evalInterpreter i (OnProgress (PrgVal fi x)) = i.onValue fi x
    evalInterpreter i (OnProgress (PrgEval fi f t' x)) = i.onStep fi x

    export
    Functor Eval where
      map f m = Bind m (Pure . f)
    
    export
    Applicative Eval where
      pure x    = Pure x
      ef <*> ex = Bind ef (\f => Bind ex (\x => Pure (f x)))

    export
    Monad Eval where
      join m  = Bind m id
      m >>= k = Bind m k

    export
    pure : a -> Eval a
    pure = Pure

    export
    (>>=) : (Eval a) -> (a -> Eval b) -> Eval b
    (>>=) = Bind

  progress : (t : Tm) -> (ty : Ty) -> ([<] |- (t <:> ty)) -> Eval (Progress t)
  progress (Var fi x1) ty (TVar x) = do
    pure (absurd (uninhabited x))
  progress (Abs fi1 x1 ty1 tm2) (Arr ty1 ty2) (TAbs x) = do
    let p = PrgVal fi1 Abs
    OnProgress p
    pure p
  progress (App fi1 t1 t2) ty (TApp {ty11 = ty11} t2ty t1ty) = do
    progress1 <- progress t1 (Arr ty11 ty) t2ty
    case progress1 of
      (PrgVal  _ t1Value) => do
        progress2 <- progress t2 ty11 t1ty
        case progress2 of
          (PrgVal  _ t2Value) => case cannonicalForms t1 (Arr ty11 ty) t2ty t1Value of
            (MkDPair fi (MkDPair var (MkDPair t Refl))) => do
              let p = PrgEval fi1 uninhabited (substitution (Subst var t2) t) (EAppAbs t2Value) 
              OnProgress p
              pure p
          (PrgEval _ t2NotValue t2' t2Infer) => do
            let p = PrgEval fi1 uninhabited (App fi1 t1 t2') (EApp2 t1Value t2NotValue t2Infer)
            OnProgress p
            pure p
      (PrgEval _ t1NotValue t1' t1Infer) => do
        let p = PrgEval fi1 uninhabited (App fi1 t1' t2) (EApp1 t1NotValue t1Infer) 
        OnProgress p
        pure p

  progressResult : (tm : Tm ** Progress tm) -> Tm
  progressResult (MkDPair tm (PrgVal fi x)) = tm
  progressResult (MkDPair tm (PrgEval fi f t' x)) = t'

  evaluation : (t : Tm) -> (ty : Ty ** ([<] |- t <:> ty)) -> Eval Tm
  evaluation t (ty ** tDeriv) = do
    p <- progress t ty tDeriv
    pure $ progressResult (t ** p)
