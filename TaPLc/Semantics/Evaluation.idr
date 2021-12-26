module TaPLc.Semantics.Evaluation

import Data.Vect
import Data.SnocList
import Decidable.Equality
import Data.Nat

import TaPLc.Data.Vect
import TaPLc.IR.Term
import TaPLc.IR.Name
import TaPLc.IR.Type
import TaPLc.IR.Record
import TaPLc.IR.Variant
import TaPLc.IR.Context
import TaPLc.IR.Info
import TaPLc.Typing.Rules
import TaPLc.Semantics.CannonicalForm
import TaPLc.Semantics.Rules
import TaPLc.Semantics.Substituition


data Progress : Tm -> Type where
  Value  : (fi : Info) -> (0 t : Tm) -> (tValue : Value t) -> Progress t
  Step   : (fi : Info) -> (0 tNotValue : Not (Value t)) -> (t' : Tm) -> (0 tEval : Evaluation t t') -> Progress t
  RtmErr : (fi : Info) -> (msg : String) -> (trace : SnocList Info) -> Progress t

namespace EvalMonad

  public export
  data Eval : Type -> Type where
    Pure : (x : t) -> Eval t
    Bind : (Eval a) -> (a -> Eval b) -> Eval b
    OnProgress : {t : Tm} -> (p : Progress t) -> Eval Unit

  record EvalImpl (m : Type -> Type) where
    constructor MkEvalImpl
    -- monad         : Type -> Type
    -- monadInstance : Monad monad
    onValue        : (fi : Info) -> {0 t : Tm} -> Value t -> m Unit
    onStep         : (fi : Info) -> {0 t,t' : Tm} -> (0 e : Evaluation t t') -> m Unit
    onRuntimeError : (fi : Info) -> (msg : String) -> (trace : SnocList Info) -> m Unit

  export
  evalInterpreter : (Monad m) => (EvalImpl m) -> Eval a -> m a
  evalInterpreter i (Pure x)    = pure x
  evalInterpreter i (Bind m k)  = evalInterpreter i m >>= (evalInterpreter i . k)
  evalInterpreter i (OnProgress (Value fi t x)) = i.onValue fi x
  evalInterpreter i (OnProgress (Step  fi f t' x)) = i.onStep fi x
  evalInterpreter i (OnProgress (RtmErr fi msg trace)) = i.onRuntimeError fi msg trace
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

namespace TupleValues

  public export
  data Descriptor : (Vect (S n) Tm) -> Type where
    Values : ForEach xs Value -> Descriptor xs
    HasNonValue : (i : Fin (S n)) -> (valuePrefix : ForEach (Vect.take i xs) Value) -> Descriptor xs

  export
  descriptor : (xs : Vect (S n) Tm) -> Descriptor xs
  descriptor (x :: []) = case isValue x of
    Yes xIsValue   => Values [xIsValue]
    No xIsNotValue => HasNonValue FZ []
  descriptor (x :: (y :: ys)) = case isValue x of
    Yes xIsValue => case descriptor (y :: ys) of
      (HasNonValue i zs) => HasNonValue (FS i) (xIsValue :: zs)
      Values es          => Values (xIsValue :: es)
    No xIsNotValue => HasNonValue FZ []

mutual

  total
  evaluation : (t : Tm) -> (ty : Ty) -> ([<] |- (t <:> ty)) -> Eval (Progress t)
  evaluation t ty deriv = do
    p <- evalp t ty deriv
    OnProgress p
    pure p

  total
  evalp : (t : Tm) -> (ty : Ty) -> ([<] |- (t <:> ty)) -> Eval (Progress t)
  evalp (Var fi x1) ty (TVar fi x) = absurd (uninhabited x)
  evalp (Abs fi1 x1 ty1 tm2) (Arr ty1 ty2) (TAbs fi x) = pure (Value fi1 _ Abs)
  evalp (App fi1 t1 t2) ty (TApp {ty11 = ty11} fi1 t2Deriv t1Deriv) = do
    progress1 <- evaluation t1 (Arr ty11 ty) t2Deriv
    case progress1 of
      (Value  _ _ t1Value) => do
        progress2 <- evaluation t2 ty11 t1Deriv
        case progress2 of
          (Value  _ _ t2Value) => case cannonicalForms t1 t1Value (Arr ty11 ty) t2Deriv of
            (fi ** var ** t ** Refl) =>
              pure $ Step fi1 uninhabited (substituition (var, t2) t) (EAppAbs t2Value) 
          (Step  _ t2NotValue t2' t2Eval) =>
            pure $ Step fi1 uninhabited (App fi1 t1 t2') (EApp2 t1Value t2NotValue t2Eval)
          (RtmErr t m ts) =>
            pure $ RtmErr fi1 m (ts :< t)
      (Step  _ t1NotValue t1' t1Eval) =>
        pure $ Step fi1 uninhabited (App fi1 t1' t2) (EApp1 t1NotValue t1Eval)
      (RtmErr t m ts) =>
        pure $ RtmErr fi1 m (ts :< t)
  evalp (True fi) Bool (TTrue fi) = pure (Value fi _ True)
  evalp (False fi) Bool (TFalse fi) = pure (Value fi _ False)
  evalp (If fi tp tt te) ty (TIf fi tpDeriv ttDeriv teDeriv) =
    pure $ case !(evaluation tp Bool tpDeriv) of
      (Value _ _ True)              => Step fi uninhabited tt EIfTrue
      (Value _ _ False)             => Step fi uninhabited te EIfFalse
      (Step _ tpNotValue t' tpEval) => Step fi uninhabited (If fi t' tt te) (EIf tpNotValue tpEval)
      (RtmErr t m ts)               => RtmErr fi m (ts :< t)
  evalp (Unit fi) Unit (TUnit fi) = pure (Value fi _ Unit)
  evalp (Seq fi t1 t2) ty (TSeq fi t1Deriv t2Deriv) =
    pure $ case !(evaluation t1 Unit t1Deriv) of
      (Value _ _ Unit)               => Step fi uninhabited t2 ESeqNext
      (Step _ t1NotValue t1' t1Eval) => Step fi uninhabited (Seq fi t1' t2) (ESeq t1NotValue t1Eval)
      (RtmErr t m ts)                => RtmErr fi m (ts :< t)
  evalp (Let fi x1 t1 t2) ty (TLet fi t1Deriv t2Deriv) =
    pure $ case !(evaluation t1 _ t1Deriv) of
      (Value _ t1 t1Value)           => Step fi uninhabited (substituition (x1,t1) t2) (ELetV t1Value)
      (Step _ t1NotValue t1' t1Eval) => Step fi uninhabited (Let fi x1 t1' t2) (ELet t1NotValue t1Eval)
      (RtmErr t m ts)                => RtmErr fi m (ts :< t)
  evalp (Tuple fi 0 []) (Tuple 0 []) (TTuple fi x) = 
    pure $ RtmErr fi "Internal error; Empty tuple is not supported."  [<]
  evalp (Tuple fi (S k) ts) (Tuple (S k) tys) (TTuple fi tyDerivations) = do
    case TupleValues.descriptor ts of
      Values es =>
        pure $ Value fi (Tuple fi (S k) ts) (Tuple es)
      HasNonValue idx valuePrefix => do
        -- Reason for assert_total:
        -- - The index function is total for Data.Vect
        -- - The ts and tys are structurally smaller than the original Tuple parameter.
        p <- assert_total $ evaluation (index idx ts) (index idx tys) (index idx tyDerivations)
        case p of
          (Value _ (index idx ts) tValue) => do
            -- When evaluate an intermediate step, which we determined to to be a value, it should
            -- produce Step, and never Value constructor. If for some reason Value constructor
            -- is happened we have an issue somewhere in the evaluator.
            pure $ RtmErr fi "Internal error: tuple ith element resulted in Value instead of Evaluation Step." [<]
          (Step  _ tNotValue t' tEval) => do
            pure $ Step fi
                    (\case
                       (Tuple assumeTupleValues) => tNotValue (index idx assumeTupleValues))
                    (Tuple fi (S k) (Vect.replaceAt idx t' ts))
                    (ETuple idx valuePrefix tNotValue tEval)
          (RtmErr t msg ts) => pure $ RtmErr fi msg (ts :< t)
  evalp (Proj fi t n i) _ (TProj fi {tys} tpDeriv) = do
    p <- evaluation t (Tuple n tys) tpDeriv
    pure $ case p of
      (Value _ (Tuple fi m tms) (Tuple vs)) => case decEq m n of
        (Yes Refl)  => Step fi uninhabited (Vect.index i tms) (EProjTuple (Tuple vs))
        (No contra) => RtmErr fi "Projection of tuple of wrong arity. Expected \{show n}, but got \{show n}" [<] -- Why, how?
      (Step  _ tNotValue t' tEval)  => Step fi uninhabited (Proj fi t' n i) (EProj tNotValue tEval)
      (RtmErr t msg ts)             => RtmErr fi msg (ts :< t)
  evalp (Record fi (MkRecord n fields ts u)) (Record (MkRecord n fields tys u)) (TRcd fi x) = do
    ?progress_rhs_13
  evalp (ProjField fi field t) ty (TRProj fi x y) = do
    ?progress_rhs_14
  evalp (Variant fi tag tj (Variant (MkVariant n tags tys u nz))) (Variant (MkVariant n tags tys u nz)) (TVariant fi x y z) = do
    ?progress_rhs_15
  evalp (Case fi t0 (MkVariant n tags alts u nz)) ty (TCase fi x y) = do
    ?progress_rhs_16
  evalp (Fix fi t1) ty (TFix fi t1Deriv) = do
    pure $ case !(evaluation t1 (Arr ty ty) t1Deriv) of
      (Value _ (Abs fia va tya tma) Abs) => Step fi uninhabited (substituition (va, Fix fi (Abs fia va tya tma)) tma) EFixBeta
      (Step  _ t1NotVaue t2 t1Eval)      => Step fi uninhabited (Fix fi t2) (EFix t1NotVaue t1Eval)
      (RtmErr t m ts)                    => RtmErr fi m (ts :< t)
  evalp (Nil fi ty) (List ty) (TNil fi) = pure (Value fi _ Nil)
  evalp (Cons fi ty t1 t2) (List ty) (TCons fi t1Deriv t2Deriv) = do
    p1 <- evaluation t1 ty t1Deriv
    case p1 of
      (Value _ t1 t1Value) => do
        pure $ case !(evaluation t2 (List ty) t2Deriv) of
          (Value _ t2 t2Value) =>
            Value fi (Cons fi ty t1 t2) (Cons t1Value t2Value)
          (Step _ t2NotValue t2' t2Eval) =>
            Step fi
              (\case
                (Cons hValue tValue) => t2NotValue tValue)
              (Cons fi ty t1 t2')
              (ECons2 t1Value t2NotValue t2Eval)
          (RtmErr t m ts) =>
            RtmErr fi m (ts :< t)
      (Step _ t1NotValue t1' t1Eval) => 
        pure $ Step fi
                (\case
                  (Cons hValue tlValue) => t1NotValue hValue)
                (Cons fi ty t1' t2)
                (ECons1 t1NotValue t1Eval)
      (RtmErr t m ts) =>
        pure $ RtmErr fi m (ts :< t)
  evalp (IsNil fi ty t) Bool (TIsNil fi tDeriv) = do
    pure $ case !(evaluation t (List ty) tDeriv) of
      (Value _ (Nil _ _) Nil)                         => Step fi uninhabited (True fi) EIsNilNil
      (Value _ (Cons _ _ _ _) (Cons hdValue tlValue)) => Step fi uninhabited (False fi) (EIsNilCons hdValue tlValue)
      (Step _ tNotValue t' tEval)                     => Step fi uninhabited (IsNil fi ty t') (EIsNil tNotValue tEval)
      (RtmErr t msg ts)                               => RtmErr fi msg (ts :< t)
  evalp (Head fi _ t) ty (THead fi tDeriv) = do
    pure $ case !(evaluation t _ tDeriv) of
      (Value _ (Nil fi ty) Nil)                           => RtmErr fi "Head of empty list." [<]
      (Value _ (Cons fi ty hd tl) (Cons hdValue tlValue)) => Step fi uninhabited hd (EHeadCons hdValue tlValue)
      (Step _ tNotValue t' tEval)                         => Step fi uninhabited (Head fi ty t') (EHead tNotValue tEval)
      (RtmErr t m ts)                                     => RtmErr fi m (ts :< t)
  evalp (Tail fi ty t) (List ty) (TTail fi tDeriv) = do
    pure $ case !(evaluation t (List ty) tDeriv) of
      (Value _ (Nil fi ty) Nil)                    => RtmErr fi "Tail of empty list." [<]
      (Value _ (Cons fi2 ty hd tl) (Cons hdv tlv)) => Step fi uninhabited tl (ETailCons hdv tlv)
      (Step _ tNotValue t' tEval)                  => Step fi uninhabited (Tail fi ty t') (ETail tNotValue tEval)
      (RtmErr t msg ts)                            => RtmErr fi msg (ts :< t)
