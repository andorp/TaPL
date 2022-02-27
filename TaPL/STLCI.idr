module TaPL.STLCI

import Data.DPair
import Data.Vect
import Data.SnocList
import Decidable.Equality

%default total

data Name : Type where
  MkName : String -> Name

data Info : Type where
  EmptyInfo : Info

namespace Ty

  public export
  data Ty : Type where
    Unit : Ty
    Arr  : Ty -> Ty -> Ty

  export Uninhabited (Unit = Arr t1 t2) where uninhabited _ impossible
  export Uninhabited (Arr t1 t2 = Unit) where uninhabited _ impossible

  funInjective : (Arr x y = Arr z w) -> (x = z, y = w)
  funInjective Refl = (Refl, Refl)

  public export
  DecEq Ty where
    decEq Unit Unit = Yes Refl
    decEq Unit (Arr x y) = No uninhabited
    decEq (Arr x y) Unit = No uninhabited
    decEq (Arr x y) (Arr z w) = case decEq x z of
      (Yes Refl) => case decEq y w of
        (Yes Refl) => Yes Refl
        (No yIsNotW) => No (\assumeArrOk => yIsNotW (snd (funInjective assumeArrOk)))
      (No xIsNotZ) => No (\assumeArrOk => xIsNotZ (fst (funInjective assumeArrOk)))

namespace Named

  public export
  data Tm : Type where
    Unit  : (fi : Info)                                               -> Tm
    Var   : (fi : Info) -> (i : Nat) -> (v : Name)                    -> Tm
    Abs   : (fi : Info) -> (var : Name) -> (ty : Ty) -> (t : Tm)      -> Tm
    App   : (fi : Info) -> (t1, t2 : Tm)                              -> Tm

data Context : a -> Type where
  Lin  : Context a
  (:<) : Context a -> a -> Context a

data In : Context a -> a -> Type where
  Z : In (ctx :< a) a
  S : In ctx a -> In (ctx :< b) a

public export
data InAsNat : In ctx a -> Nat -> Type where
  ZI : InAsNat Z Z
  SI : (0 _ : InAsNat i n) -> InAsNat (S i) (S n)

namespace WellTyped

  public export
  data Tm : Context Ty -> Ty -> Type where

    Unit : (fi : Info) ->
      {ctx : Context Ty} ->
      ---------------------
           Tm ctx Unit

    Var : (fi : Info) ->
      {ctx : Context Ty} ->
            {ty : Ty}     -> 
        (k : In ctx ty)  ->
      ---------------------
            Tm ctx ty

    Abs : (fi : Info) -> 
          {ctx : Context Ty}     ->
              {ty2 : Ty}         ->
      (var : Name) -> (ty1 : Ty) ->
      (t : Tm (ctx :< ty1) ty2) ->
      -----------------------------
          Tm ctx (Arr ty1 ty2)

    App : (fi : Info) ->
                      {ctx : Context Ty}               ->
                      {ty1, ty2 : Ty}                 ->
      (t1 : Tm ctx (Arr ty1 ty2)) -> (t2 : Tm ctx ty1) ->
      ---------------------------------------------------
                          Tm ctx ty2

namespace Value

  public export
  data Value : Tm ctx ty -> Type where
    Unit : Value (Unit fi)
    Abs  : Value (Abs fi var ty t)

  export Uninhabited (Value (App fi t1 t2)) where uninhabited _ impossible

namespace ForgetType 

  public export
  data Forget : Tm ctx ty -> Tm -> Type where
    Unit : Forget (Unit fi) (Unit fi)
    Var  : (InAsNat k i) -> Forget (Var fi k) (Var fi i v)
    Abs  : (Forget tt t) -> Forget (Abs fi v ty tt) (Abs fi v ty t)
    App  : (Forget tt1 t1) -> (Forget tt2 t2) -> Forget (App fi tt1 tt2) (App fi t1 t2)

public export
data TypeInferenceError : Type where
  DerivInfo       : (deriv : (Tm ctx ty))             -> TypeInferenceError
  TypeMissmatch   : (expected, found : Ty)            -> TypeInferenceError
  ArityMissmatch  : (expected, found : Nat)           -> TypeInferenceError
  TagMissmatch    : (expected, found : Vect n String) -> TypeInferenceError
  Message         : String                            -> TypeInferenceError
  NotFound        : (ctx : Context Ty) -> (i : Nat)   -> TypeInferenceError
  FoundType       : (ty : Ty)                         -> TypeInferenceError
  InternalError   : String                            -> TypeInferenceError

data Infer : Type -> Type where
  Pure : a -> Infer a
  Bind : Infer a -> (a -> Infer b) -> Infer b
  Error : {0 a : Type} -> Info -> List TypeInferenceError -> Infer a

record InferImpl (m : Type -> Type) where
  constructor MkInferImpl
  error : {0 a : Type} -> Info -> List TypeInferenceError -> m a

partial
runInfer : (Monad m) => InferImpl m -> Infer a -> m a
runInfer i (Pure x)          = pure x
runInfer i (Bind m k)        = runInfer i m >>= (runInfer i . k)
runInfer i (Error fi errors) = i.error fi errors

namespace InferMonad

  export
  (>>=) : Infer a -> (a -> Infer b) -> Infer b
  (>>=) = Bind

  export
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

inContext : (ctx : Context Ty) -> (i : Nat) -> Dec (DPair Ty (\ty => (DPair (In ctx ty) (\j => InAsNat j i))))
inContext ctx i = ?ic

||| Proof that the WellTyped term has a corresponding Term
data InferedTy : (y : Ty) -> Tm -> Tm ctx y -> Type where
  Infered : {0 ty : Ty} -> {0 t : Tm} -> {0 tt : Tm ctx ty} -> (0 f : Forget tt t) -> InferedTy ty t tt

partial
inferType : (ctx : Context Ty) -> (t : Tm) -> Infer (ty : Ty ** (tt : Tm ctx ty ** InferedTy ty t tt))
inferType ctx (Unit fi) = pure (Unit ** Unit fi ** Infered Unit)
inferType ctx (Var fi i v) = do
  let Yes (ty ** (inCtx ** inAsNat)) = inContext ctx i
      | No _ => Error fi [NotFound ctx i]
  pure (ty ** (Var fi inCtx ** Infered (Var inAsNat)))
inferType ctx (Abs fi var ty t) = do
  (ty2 ** tt ** (Infered fgt)) <- inferType (ctx :< ty) t
  pure (Arr ty ty2 ** (Abs fi var ty tt ** Infered (Abs fgt)))
inferType ctx (App fi t1 t2) = do
  (ty1 ** tt1 ** (Infered fgt1)) <- inferType ctx t1
  (ty2 ** tt2 ** (Infered fgt2)) <- inferType ctx t2
  case ty1 of
    (Arr aty1 aty2) => case decEq ty2 aty1 of
      (Yes Refl)
        => pure (aty2 ** App fi tt1 tt2 ** (Infered (App fgt1 fgt2)))
      (No _)
        => Error fi
            [ DerivInfo tt1
            , DerivInfo tt2
            , TypeMissmatch aty1 ty2
            , Message "parameter type missmatch"
            ]
    _ => Error fi
          [ DerivInfo tt1
          , DerivInfo tt2
          , FoundType ty1
          , Message "function type is expected"
          ]

namespace Substituition

  extend
    :  {gamma, delta : Context Ty}
    -> ({a : Ty} -> In gamma a -> In delta a)
    -> {a,b : Ty} -> In (gamma :< b) a -> In (delta :< b) a
  extend f Z = Z
  extend f (S x) = S (f x)

  rename
    :  {gamma, delta : Context Ty}
    -> ({a : Ty} -> In gamma a -> In delta a)
    -> Tm gamma a -> Tm delta a
  rename f (Unit fi) = Unit fi
  rename f (Var fi k) = Var fi (f k)
  rename f (Abs fi var ty1 t) = Abs fi var ty1 (rename (extend f) t)
  rename f (App fi t1 t2) = App fi (rename f t1) (rename f t2)

  record Variable (gamma : Context Ty) (a : Ty) where
    constructor MkVariable
    info  : Info
    idx   : In gamma a

  extendSubst
    :  {gamma, delta : Context Ty}
    -> ({a : Ty} -> Variable gamma a -> Tm delta a)
    -> {a,b : Ty}
    -> Variable (gamma :< b) a
    -> Tm (delta :< b) a
  extendSubst f (MkVariable i Z) = Var i Z
  extendSubst f (MkVariable i (S x)) = rename S (f (MkVariable i x))

  subst
    :  {gamma, delta : Context Ty}
    -> ({a : Ty} -> Variable gamma a -> Tm delta a)
    -> Tm gamma a -> Tm delta a
  subst f (Unit fi) = Unit fi
  subst f (Var fi k) = f (MkVariable fi k)
  subst f (Abs fi var ty1 t) = Abs fi var ty1 (subst (extendSubst f) t)
  subst f (App fi t1 t2) = App fi (subst f t1) (subst f t2)

  singleVariable
    :  {gamma : Context Ty}
    -> {a,b : Ty}
    -> Tm gamma b
    -> Variable (gamma :< b) a
    -> Tm gamma a
  singleVariable s (MkVariable i Z)     = s
  singleVariable s (MkVariable i (S x)) = Var i x

  export
  substituition
    :  {gamma : Context Ty}
    -> {a,b : Ty}
    -> Tm gamma b
    -> Tm (gamma :< b) a
    -> Tm gamma a
  substituition s t = subst (singleVariable s) t

data Evaluation : (Tm ctx ty) -> (Tm ctx ty) -> Type where

  EApp1 :
    Not (Value t1) ->
    Evaluation t1 t1' ->
    Evaluation (App fi t1 t2) (App fi t1' t2)
  
  EApp2 :
    Value v1 ->
    Not (Value t) ->
    Evaluation t t' ->
    Evaluation (App fi v1 t) (App fi v1 t')
  
  EAppAbs :
    Value v ->
    Evaluation (App fi (Abs fi2 x ty t) v) (substituition v t)

data Progress : Tm ctx ty -> Type where
  Value  : (fi : Info) -> (t : Tm ctx ty) -> (tValue : Value t) -> Progress t
  RtmErr : (fi : Info) -> (msg : String) -> (trace : SnocList Info) -> Progress t
  Step  :  (fi : Info)
        -> (tNotValue : Not (Value t))
        -> (t' : Tm ctx ty)
        -> (tEval : Evaluation t t')
        -> Progress t

covering
smallStep : (t : Tm [<] y) -> Progress t
smallStep (Var _ Z)     impossible
smallStep (Var _ (S x)) impossible
smallStep (Unit fi) = Value fi (Unit fi) Unit
smallStep (Abs fi var ty1 t) = Value fi (Abs fi var ty1 t) Abs
smallStep (App fi t1 t2) = case smallStep t1 of
  (Value x (Abs fi1 var aty t) Abs) => case smallStep t2 of
    (Value y t2 t2Value)
      => Step fi uninhabited (substituition t2 t) (EAppAbs t2Value)
    (RtmErr fi0 msg trace)
      => RtmErr fi msg (trace :< fi0)
    (Step _ tNotValue t' tEval)
      => Step fi uninhabited
          (App fi (Abs fi1 var aty t) t')
          (EApp2 Abs tNotValue tEval)
  (RtmErr t msg trace) => RtmErr fi msg (trace :< t)
  (Step _ t1NotValue t1' t1Eval)
    => Step fi
        uninhabited
        (App fi t1' t2)
        (EApp1 t1NotValue t1Eval)

public export
data RuntimeError : Type where
  MkRuntimeError : (fi : Info) -> (msg : String) -> (trace : SnocList Info) -> RuntimeError

covering
evaluate : Tm [<] y -> Either (t : (Tm [<] y) ** Value t) RuntimeError
evaluate t = case smallStep t of
  (Value fi t tValue)
    => Left (t ** tValue)
  (RtmErr fi msg trace)
    => Right (MkRuntimeError fi msg trace)
  (Step fi tNotValue t' tEval)
    => evaluate t'
