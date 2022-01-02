module TaPLc.Semantics.Evaluation

import public TaPLc.Semantics.Substituition
import public TaPLc.IR.Name
import public TaPLc.IR.Variant

import Data.Vect
import Data.SnocList
import Decidable.Equality
import Data.Nat

import TaPLc.Data.Vect
import TaPLc.IR.Term
import TaPLc.IR.Type
import TaPLc.IR.Record
import TaPLc.IR.Context
import TaPLc.IR.Info
import TaPLc.Typing.Rules
import TaPLc.Semantics.CannonicalForm
import TaPLc.Semantics.Rules
import TaPLc.Semantics.ShowRules
import TaPLc.IR.FFI
import TaPLc.Typing.Substituition
import TaPLc.Typing.Lemmas

public export
data RuntimeError : Type where
  MkRuntimeError : (fi : Info) -> (msg : String) -> (trace : SnocList Info) -> RuntimeError

export
data Progress : Tm -> Type where
  Value  : (fi : Info) -> (t : Tm) -> (tValue : Value t) -> Progress t
  RtmErr : (fi : Info) -> (msg : String) -> (trace : SnocList Info) -> Progress t
  -- TODO: Add tDeriv and use type-safety.
  Step  :  (fi : Info)
        -> (tNotValue : Not (Value t))
        -> (t' : Tm)
        -> (tEval : Evaluation t t')
        -> (ty' : Ty)
        -> (t'Deriv : [<] |- t' <:> ty')
        -> Progress t
  StepX :  (fi : Info)
        -> (tNotValue : Not (Value t))
        -> (t' : Tm)
        -> {tye : Ty}
        -> (tDeriv  : [<] |- t  <:> tye)
        -> (t'Deriv : [<] |- t' <:> tye)
        -> (tEval : Evaluation t t')
        -> Progress t


export
Show (Progress t) where
  showPrec d (Value fi t tValue) = showCon d "Value" $ showArg fi ++ showArg tValue
  showPrec d (Step fi tNotValue t' tEval ty' t'Deriv) = showCon d "Step" $ showArg fi ++ showArg tEval
  showPrec d (StepX fi tNotValue t' tDeriv t'Deriv tEval) = showCon d "StepX" $ showArg fi ++ showArg tEval
  showPrec d (RtmErr fi msg trace) = showCon d "RtmErr" $ showArg fi ++ showArg msg ++ showArg trace

namespace EvalMonad

  public export
  data Eval : Type -> Type where
    Pure : (x : t) -> Eval t
    Bind : (Eval a) -> (a -> Eval b) -> Eval b
    OnProgress : {t : Tm} -> (p : Progress t) -> Eval Unit
    FFICall : (fi : Info) -> {n : Nat} -> (c : FFICall n) -> (args : Vect n Tm) -> (0 fe : ForEach args Value) -> Eval (Either String (FFIVal (ffiCallRetType c)))
    ConvertFFIVal : (fi : Info) -> (t : Tm) -> (vt : Value t) -> (0 ft : FFI t) -> (b : BaseType) -> Eval (Either String (v : (FFIVal b) ** FFIConv t v))

  export
  pure : a -> Eval a
  pure = Pure

  export
  (>>=) : (Eval a) -> (a -> Eval b) -> Eval b
  (>>=) = Bind

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

public export
record EvalImpl (m : Type -> Type) where
  constructor MkEvalImpl
  -- monad         : Type -> Type
  -- monadInstance : Monad monad
  onValue        : (fi : Info) -> {0 t : Tm} -> Value t -> m Unit
  onStep         : (fi : Info) -> {0 t : Tm} -> (t' : Tm) -> (e : Evaluation t t') -> m Unit
  onRuntimeError : (fi : Info) -> (msg : String) -> (trace : SnocList Info) -> m Unit
  ffiCall        : (fi : Info) -> {n : Nat} -> (c : FFICall n) -> (args : Vect n Tm) -> m (Either String (FFIVal (ffiCallRetType c)))
  convertFFIVal  : (fi : Info) -> (t : Tm) -> (vt : Value t) -> (0 ft : FFI t) -> (b : BaseType) -> m (Either String (v : (FFIVal b) ** FFIConv t v))

export covering
runEval : (Monad m) => EvalImpl m -> Eval a -> m a
runEval i (Pure x)                            = pure x
runEval i (Bind m k)                          = runEval i m >>= (runEval i . k)
runEval i (OnProgress (Value fi t x))         = i.onValue fi x
runEval i (OnProgress (Step  fi f t' e ty' t'd))      = i.onStep fi t' e
runEval i (OnProgress (StepX fi f t' td t'd e)) = i.onStep fi t' e
runEval i (OnProgress (RtmErr fi msg trace))  = i.onRuntimeError fi msg trace
runEval i (FFICall fi c args fe)              = i.ffiCall fi c args
runEval i (ConvertFFIVal fi t vt ft b)        = i.convertFFIVal fi t vt ft b


namespace ValuePrefix

  ||| Value preffix descriptor of a Tm sotring vector.
  |||
  ||| For tuples and records we need to know if the terms in these structrues are
  ||| already evaluated to Values or just there is a possible preffix of values,
  ||| as the evaluation as a process for evaluating parameters one-by-one, from left to right.
  public export
  data Descriptor : (Vect n Tm) -> Type where
    ||| Every element in the term vector is actually a value.
    Values      : ForEach xs Value -> Descriptor xs
    ||| There is at least one element in term vector which is not a value, and its index is 'i'.
    HasNonValue : (i : Fin n) -> (valuePrefix : ForEach (Vect.Take.take i xs) Value) -> Descriptor xs

  export
  descriptor : (xs : Vect n Tm) -> Descriptor xs
  descriptor []        = Values []
  descriptor (x :: xs) = case isValue x of
    Yes xIsValue => case descriptor xs of
      (HasNonValue i zs) => HasNonValue (FS i) (xIsValue :: zs)
      Values es          => Values (xIsValue :: es)
    No xIsNotValue => HasNonValue FZ []

mutual

  export total
  smallStep : (t : Tm) -> (ty : Ty) -> ([<] |- (t <:> ty)) -> Eval (Progress t)
  smallStep t ty deriv = do
    p <- step t ty deriv
    OnProgress p
    pure p

  total
  step : (t : Tm) -> (ty : Ty) -> ([<] |- (t <:> ty)) -> Eval (Progress t)
  
  step (Var fi x1) ty (TVar fi x) = absurd (uninhabited x)
  
  step (Abs fi1 x1 ty1 tm2) (Arr ty1 ty2) (TAbs fi x) = pure (Value fi1 _ Abs)
  
  step (App fi1 t1 t2) ty (TApp {ty11 = ty11} fi1 t2Deriv t1Deriv) = do
    progress1 <- smallStep t1 (Arr ty11 ty) t2Deriv
    case progress1 of
      (Value  _ _ t1Value) => do
        progress2 <- smallStep t2 ty11 t1Deriv
        case progress2 of
          (Value  _ _ t2Value) => case cannonicalForms t1 t1Value (Arr ty11 ty) t2Deriv of
            (fi ** var ** t ** Refl) =>
              pure $ Step fi1
                      uninhabited
                      (substituition (var, t2) t)
                      (EAppAbs t2Value)
                      ty
                      (Lemmas.application t t2 var ty t1Deriv t2Deriv)
          (Step  _ t2NotValue t2' t2Eval t2'ty t2'Deriv) => do
            let Yes Refl = decEq ty11 t2'ty
                | No _ => pure $ RtmErr fi1 "Type error" [<]
            pure $ Step fi1
                    uninhabited
                    (App fi1 t1 t2')
                    (EApp2 t1Value t2NotValue t2Eval)
                    ty
                    (TApp {ty11=ty11} fi1 t2Deriv t2'Deriv)
          (StepX fi tNotValue t' tDeriv t'Deriv tEval) => ?sx1
          (RtmErr t m ts) =>
            pure $ RtmErr fi1 m (ts :< t)
      (Step  _ t1NotValue t1' t1Eval ty1' t1'Deriv) => do
        let Yes Refl = decEq ty1' (Arr ty11 ty)
            | No _ => pure $ RtmErr fi1 "Type error" [<]
        pure $ Step fi1
                uninhabited
                (App fi1 t1' t2)
                (EApp1 t1NotValue t1Eval)
                ty
                (TApp {ty11=ty11} fi1 t1'Deriv t1Deriv)
      (StepX fi tNotValue t' tDeriv t'Deriv tEval) => ?sx2
      (RtmErr t m ts) =>
        pure $ RtmErr fi1 m (ts :< t)
  
  step (True fi) Bool (TTrue fi) = pure (Value fi _ True)
  
  step (False fi) Bool (TFalse fi) = pure (Value fi _ False)
  
  step (If fi tp tt te) ty (TIf fi tpDeriv ttDeriv teDeriv) =
    case !(smallStep tp Bool tpDeriv) of
      (Value _ _ True) =>
        pure $ Step fi
                uninhabited
                tt
                EIfTrue
                ty
                ttDeriv
      (Value _ _ False) =>
        pure $ Step fi uninhabited
                te
                EIfFalse
                ty
                teDeriv
      (Step _ tpNotValue t' tpEval Bool t'Deriv) =>
        pure $ Step fi
                uninhabited
                (If fi t' tt te)
                (EIf tpNotValue tpEval)
                ty
                (TIf fi t'Deriv ttDeriv teDeriv)
      (Step _ tpNotValue t' tpEval other t'Deriv) =>
        pure $ RtmErr fi "Type error; if predicate didn't evaluate to bool" [<]
      (StepX fi1 tNotValue t' tDeriv t'Deriv tEval) => 
        pure $ StepX fi1
                uninhabited
                (If fi t' tt te)
                (TIf fi tpDeriv ttDeriv teDeriv)
                ?tDeriv
                (EIf tNotValue tEval)
      (RtmErr t m ts) =>
        pure $ RtmErr fi m (ts :< t)

  step (Unit fi) Unit (TUnit fi) = pure (Value fi _ Unit)

  step (Seq fi t1 t2) ty (TSeq fi t1Deriv t2Deriv) =
    pure $ case !(smallStep t1 Unit t1Deriv) of
      (Value _ _ Unit) =>
        Step fi
          uninhabited
          t2
          ESeqNext
          ty
          t2Deriv
      (Step _ t1NotValue t1' t1Eval Unit t1'Deriv) =>
        Step fi
          uninhabited
          (Seq fi t1' t2)
          (ESeq t1NotValue t1Eval)
          ty
          (TSeq fi t1'Deriv t2Deriv)
      (Step _ t1NotValue t1' t1Eval ty1 t1'Deriv) =>
        RtmErr fi "Type error; Seq first element didn't have the type Unit, found \{show ty1}" [<]
      (StepX fi tNotValue t' tDeriv t'Deriv tEval) => ?sx4
      (RtmErr t m ts) => RtmErr fi m (ts :< t)

  step (Let fi x1 t1 t2) ty (TLet fi {ty1} t1Deriv t2Deriv) = do
    p <- smallStep t1 _ t1Deriv
    case p of
      (Value _ t1 t1Value) =>
        pure $ Step fi
                uninhabited
                (substituition (x1,t1) t2)
                (ELetV t1Value)
                ty
                (Substituition.keepsType t1 t2 x1 ty1 ty t1Deriv t2Deriv)
      (Step _ t1NotValue t1' t1Eval ty1' t1'Deriv) => do
        let Yes Refl = decEq ty1 ty1'
              | No _ => pure $ RtmErr fi "Type error; different type in let expressions. Expected \{show ty}, got \{show ty1}" [<]
        pure $ Step fi
                uninhabited
                (Let fi x1 t1' t2)
                (ELet t1NotValue t1Eval)
                ty
                (TLet fi t1'Deriv t2Deriv)
      (StepX fi tNotValue t' tDeriv t'Deriv tEval) => ?sx5
      (RtmErr t m ts) =>
        pure $ RtmErr fi m (ts :< t)

  step (Tuple fi n ts) (Tuple n tys) (TTuple fi tyDerivations) =
    case ValuePrefix.descriptor ts of
      Values vs =>
        pure $ Value fi (Tuple fi n ts) (Tuple vs)
      HasNonValue idx valuePrefix => do
        -- Reason for assert_total:
        -- - The index function is total for Data.Vect
        -- - The ts and tys are structurally smaller than the original Tuple parameter.
        p <- assert_total $ smallStep (index idx ts) (index idx tys) (index idx tyDerivations)
        case p of
          (Value _ (index idx ts) tValue) => do
            -- When smallStep an intermediate step, which we determined to be a value, it should
            -- produce Step, and never Value constructor. If for some reason Value constructor
            -- is happened we have an issue somewhere in the evaluator.
            -- TODO: Use a different error, with stack-trace
            pure $ RtmErr fi "Internal error: tuple \{show idx} element resulted in Value instead of Evaluation Step." [<]
          (Step  _ tNotValue t' tEval ty' t'Deriv) => do
            let Yes Refl = decEq ty' (index idx tys)
                | No _ => pure $ RtmErr fi "Type error" [<]
            pure $ Step fi
                    (\case
                        (Tuple assumeTupleValues) => tNotValue (index idx assumeTupleValues))
                    (Tuple fi n (Vect.replaceAt idx t' ts))
                    (ETuple idx valuePrefix tNotValue tEval)
                    (Tuple n tys)
                    (TTuple fi (replaceDerivations idx t' t'Deriv tyDerivations))
          (StepX fi tNotValue t' tDeriv t'Deriv tEval) => ?sx6
          (RtmErr t msg ts) => 
            pure $ RtmErr fi msg (ts :< t)

  step (Proj fi t n i) (index i tys) (TProj fi {tys} tpDeriv) = do
    p <- smallStep t (Tuple n tys) tpDeriv
    case p of
      (Value _ (Tuple fi m tms) (Tuple vs)) => case decEq m n of
        (Yes Refl)  =>
          pure $ Step fi
                  uninhabited
                  (Vect.index i tms)
                  (EProjTuple (Tuple vs))
                  (index i tys)
                  (Lemmas.tupleProj i (Tuple vs) tpDeriv)
        (No contra) => 
          pure $ RtmErr fi "Projection of tuple of wrong arity. Expected \{show n}, but got \{show m}" [<] -- Why, how?
      (Step  _ tNotValue t' tEval ty' t'Deriv) => do
        let Yes Refl = decEq ty' (Tuple n tys)
            | No _ => pure $ RtmErr fi "Type error; Expected \{show (Tuple n tys)}, got \{show ty'}" [<]
        pure $ Step fi
                uninhabited
                (Proj fi t' n i)
                (EProj tNotValue tEval)
                (index i tys)
                (TProj fi t'Deriv)
      (StepX fi tNotValue t' tDeriv t'Deriv tEval) => ?sx7
      (RtmErr t msg ts) =>
        pure $ RtmErr fi msg (ts :< t)

  step (Record fi (MkRecord n fields ts u)) (Record (MkRecord n fields tys u)) (TRcd fi fieldDerivations) =
    case ValuePrefix.descriptor ts of
      (Values vs)
        => pure $ Value fi (Record fi (MkRecord n fields ts u)) (Record vs)
      (HasNonValue idx valuePrefix) => do
        -- Reason for assert_total:
        -- - The index function is total for Data.Vect
        -- - The ts and tys are structurally smaller than the original Tuple parameter.
        p <- assert_total $ smallStep (index idx ts) (index idx tys) (index idx fieldDerivations)
        case p of
          (Value _ (index idx ts) tValue) => do
            -- When smallStep an intermediate step, which we determined to be a value, it should
            -- produce Step, and never Value constructor. If for some reason Value constructor
            -- is happened we have an issue somewhere in the evaluator.
            -- TODO: Use a different error, with stack trace included
            pure $ RtmErr fi "Internal error: record \{show idx} element resulted in Value instead of Evaluation Step." [<]
          (Step _ tNotValue t' tEval ty1 t'Deriv) => do
            let Yes Refl = decEq ty1 (index idx tys)
                | No _ => pure $ RtmErr fi "Type error; Expected \{show (Tuple n tys)}, got \{show ty1}" [<]
            pure $ Step fi
                    (\case
                      (Record vs) => tNotValue (index idx vs))
                    (Record fi (MkRecord n fields (Vect.replaceAt idx t' ts) u))
                    (ERcd idx valuePrefix tNotValue tEval)
                    (Record (MkRecord n fields tys u))
                    (TRcd fi (Lemmas.replaceDerivations idx t' t'Deriv fieldDerivations))
          (StepX fi tNotValue t' tDeriv t'Deriv tEval) => ?sx8
          (RtmErr t msg ts) =>
            pure $ RtmErr fi msg (ts :< t)

  step (ProjField fi field t) (index idx tys) (TRProj fi {n} {tys} {fields} {u} {idx} fieldInRecord tDeriv) = do
    p <- smallStep t (Record (MkRecord n fields tys u)) tDeriv
    case p of
      (Value _ (Record fi (MkRecord n1 fields1 tms1 u1)) (Record vs)) => do
        let Yes Refl = decEq n n1
            | No _ => pure $ RtmErr fi
                        """
                        Internal error: smallStep of record value resulted in different sized records.
                        Expected \{show n}, but got \{show n1}.
                        """
                        [<]
        let Yes Refl = decEq fields fields1
            | No _ => pure $ RtmErr fi
                        """
                        Internal error: smallStep of record value resulted in different fields in records.
                        Expected \{show fields}, but got \{show fields1}.
                        """
                        [<]
        let Yes Refl = decEq u1 u
            | No _ => pure $ RtmErr fi "Internal error; found different unique names." [<]
        pure $ Step fi
          uninhabited
          (Vect.index idx tms1)
          (EProjRec {inr=fieldInRecord} vs)
          (index idx tys)
          (Lemmas.recordFieldType tms1 tys fields1 u fi idx (Record vs) tDeriv)
      (Step _ tNotValue t' tEval ty1 t'Deriv) => do
        let Yes Refl = decEq ty1 (Record (MkRecord n fields tys u))
            | No _ => pure $ RtmErr fi "Type error; Expected \{show (index idx tys)}, got \{show ty1}" [<]
        pure $ Step fi
          uninhabited
          (ProjField fi field t')
          (EProjField tNotValue tEval)
          (index idx tys)
          (TRProj fi fieldInRecord t'Deriv)
      (StepX fi tNotValue t' tDeriv t'Deriv tEval) => ?sx9
      (RtmErr t msg ts) =>
        pure $ RtmErr fi msg (ts :< t)

  step (Variant fi tag tj (Variant (MkVariant n tags tys u nz)))
        (Variant (MkVariant n tags tys u nz))
        (TVariant fi tagIndex nameIndex tjDeriv) = do
    p <- smallStep tj _ tjDeriv
    case p of
      (Value _ tj tValue) =>
        pure (Value fi _ (Variant tValue))
      (Step _ tNotValue t' tEval ty1 t'Deriv) => do
        let Yes Refl = decEq (index tagIndex tys) ty1
            | No _ => pure $ RtmErr fi "Type error; Expected type for \{tag} differs. Expected; \{show (index tagIndex tys)}, got \{show ty1}" [<]
        pure $ Step fi
          (\case (Variant assumeValue) => tNotValue assumeValue)
          (Variant fi tag t' (Variant (MkVariant n tags tys u nz)))
          (EVariant tNotValue tEval)
          (Variant (MkVariant n tags tys u nz))
          (TVariant fi tagIndex nameIndex t'Deriv)
      (StepX fi tNotValue t' tDeriv t'Deriv tEval) => ?sx10
      (RtmErr t msg ts) =>
        pure $ RtmErr fi msg (ts :< t)

  step (Case fi t0 (MkVariant n tags alts u nz)) ty (TCase fi {tys} t0Deriv variantDerivs) = do
    p <- smallStep t0 _ t0Deriv
    case p of
      (Value _ (Variant fi tag t ty) (Variant tValue)) => do
        let Yes (idx ** inTags) = inNames tag tags
            | No _ => pure $ RtmErr fi "Internal error; \{tag} is not found in \{show tags}" [<]
        pure $ Step fi
                uninhabited
                (substituition (fst (index idx alts),t) (snd (index idx alts)))
                (ECaseVariant idx inTags)
                ty
                (Lemmas.caseEval idx t0Deriv)
      (Step _ tNotValue t' tEval ty1 t'Deriv) => do
        let Yes Refl = decEq ty1 (Variant (MkVariant n tags tys u nz))
            | No _ => pure $ RtmErr fi "Type error; Expected \{show (Variant (MkVariant n tags tys u nz))}, but got \{show ty1}" [<]
        pure $ Step fi
                uninhabited
                (Case fi t' (MkVariant n tags alts u nz))
                (ECase tNotValue tEval)
                ty
                (TCase fi t'Deriv variantDerivs)
      (StepX fi tNotValue t' tDeriv t'Deriv tEval) => ?sx11
      (RtmErr t msg ts) =>
        pure $ RtmErr fi msg (ts :< t)

  step (Fix fi t1) ty (TFix fi t1Deriv) = do
    case !(smallStep t1 (Arr ty ty) t1Deriv) of
      (Value _ (Abs fia va tya tma) Abs) =>
        pure $ Step fi
          uninhabited
          (substituition (va, Fix fi (Abs fia va tya tma)) tma)
          EFixBeta
          ty
          (Lemmas.fixEval t1Deriv)
      (Step  _ t1NotVaue t2 t1Eval ty1 t1Deriv) => do
        let Yes Refl = decEq ty1 (Arr ty ty)
            | No _ => pure $ RtmErr fi "Type error; Expected \{show (Arr ty ty)}, but got \{show ty1}" [<]
        pure $ Step fi
          uninhabited
          (Fix fi t2)
          (EFix t1NotVaue t1Eval)
          ty
          (TFix fi t1Deriv)
      (StepX fi tNotValue t' tDeriv t'Deriv tEval) => ?sx12
      (RtmErr t m ts) =>
        pure $ RtmErr fi m (ts :< t)

  step (Nil fi ty) (List ty) (TNil fi) = pure (Value fi _ Nil)

  step (Cons fi ty t1 t2) (List ty) (TCons fi t1Deriv t2Deriv) = do
    p1 <- smallStep t1 ty t1Deriv
    case p1 of
      (Value _ t1 t1Value) => do
        case !(smallStep t2 (List ty) t2Deriv) of
          (Value _ t2 t2Value) =>
            pure $ Value fi (Cons fi ty t1 t2) (Cons t1Value t2Value)
          (Step _ t2NotValue t2' t2Eval ty2 t2'Deriv) => do
            let Yes Refl = decEq (List ty) ty2
                | No _ => pure $ RtmErr fi "Type error" [<]
            pure $ Step fi
                    (\case
                      (Cons hValue tValue) => t2NotValue tValue)
                    (Cons fi ty t1 t2')
                    (ECons2 t1Value t2NotValue t2Eval)
                    (List ty)
                    (TCons fi t1Deriv t2'Deriv)
          (StepX fi tNotValue t' tDeriv t'Deriv tEval) => ?sx19
          (RtmErr t m ts) =>
            pure $ RtmErr fi m (ts :< t)
      (Step _ t1NotValue t1' t1Eval ty1' t1'Deriv) => do
        let Yes Refl = decEq ty1' ty
            | No _ => pure $ RtmErr fi "Type error" [<]
        pure $ Step fi
                (\case
                  (Cons hValue tlValue) => t1NotValue hValue)
                (Cons fi ty t1' t2)
                (ECons1 t1NotValue t1Eval)
                (List ty)
                (TCons fi t1'Deriv t2Deriv)
      (StepX fi tNotValue t' tDeriv t'Deriv tEval) => ?sx13
      (RtmErr t m ts) =>
        pure $ RtmErr fi m (ts :< t)

  step (IsNil fi ty t) Bool (TIsNil fi tDeriv) = do
    case !(smallStep t (List ty) tDeriv) of
      (Value _ (Nil _ _) Nil) =>
        pure $ Step fi
                uninhabited
                (True fi)
                EIsNilNil
                Bool
                (TTrue fi)
      (Value _ (Cons _ _ _ _) (Cons hdValue tlValue)) =>
        pure $ Step fi
                uninhabited
                (False fi)
                (EIsNilCons hdValue tlValue)
                Bool
                (TFalse fi)
      (Step _ tNotValue t' tEval ty1 t'Deriv) => do
        let Yes Refl = decEq ty1 (List ty)
            | No _ => pure $ RtmErr fi "Type error" [<]
        pure $ Step fi
                uninhabited
                (IsNil fi ty t')
                (EIsNil tNotValue tEval)
                Bool
                (TIsNil fi t'Deriv)
      (StepX fi tNotValue t' tDeriv t'Deriv tEval) => ?sx14
      (RtmErr t msg ts) =>
        pure $ RtmErr fi msg (ts :< t)

  step (Head fi _ t) ty (THead fi tDeriv) =
    case !(smallStep t _ tDeriv) of
      (Value _ (Nil fi ty) Nil) => 
        pure $ RtmErr fi "Head of empty list." [<]
      (Value _ (Cons fi ty1 hd tl) (Cons hdValue tlValue)) => do
        let Yes Refl = decEq ty1 ty
            | No _ => pure $ RtmErr fi "Type error" [<]
        pure $ Step fi
                uninhabited
                hd
                (EHeadCons hdValue tlValue)
                ty
                (Lemmas.headEval tDeriv)
      (Step _ tNotValue t' tEval ty1 t'Deriv) => do
        let Yes Refl = decEq ty1 (List ty)
            | No _ => pure $ RtmErr fi "Type error" [<]
        pure $ Step fi
                uninhabited
                (Head fi ty t')
                (EHead tNotValue tEval)
                ty
                (THead fi t'Deriv)
      (StepX fi tNotValue t' tDeriv t'Deriv tEval) => ?sx15
      (RtmErr t m ts) => 
        pure $ RtmErr fi m (ts :< t)

  step (Tail fi ty t) (List ty) (TTail fi tDeriv) =
    case !(smallStep t (List ty) tDeriv) of
      (Value _ (Nil fi ty) Nil) =>
        pure $ RtmErr fi "Tail of empty list." [<]
      (Value _ (Cons fi2 ty1 hd tl) (Cons hdv tlv)) =>
        pure $ Step fi
                uninhabited
                tl
                (ETailCons hdv tlv)
                (List ty)
                (Lemmas.tailType tDeriv)
      (Step _ tNotValue t' tEval ty1 t'Deriv) => do
        let Yes Refl = decEq ty1 (List ty)
            | No _ => pure $ RtmErr fi "Type error" [<]
        pure $ Step fi
                uninhabited
                (Tail fi ty t')
                (ETail tNotValue tEval)
                (List ty)
                (TTail fi t'Deriv)
      (StepX fi tNotValue t' tDeriv t'Deriv tEval) => ?sx16
      (RtmErr t msg ts) =>
        pure $ RtmErr fi msg (ts :< t)

  step (LitNat fi l) LitNat (TLitNat fi) =
    pure $ Value fi (LitNat fi l) LitNat

  step (FFI fi (MkFFICall f n pms ret) args) (Base ret) (TFFICall fi argsDeriv) =
    case ValuePrefix.descriptor args of
      (Values vs) => do
        Right (MkFFIVal ret so) <- FFICall fi (MkFFICall f n pms ret) args vs
          | Left msg => pure $ RtmErr fi "FFICall: \{msg}" [<]
        pure $ Step fi
                uninhabited
                (FFIVal fi (MkFFIVal ret so))
                EFFICall
                (Base ret)
                (TFFIVal fi)
      (HasNonValue idx valuePrefix) => do
        -- Reason for assert_total:
        -- - The index function is total for Data.Vect
        -- - The args are structurally smaller than the original FFI parameter.
        p <- assert_total $ smallStep (index idx args) _ (index idx argsDeriv)
        case p of
          (Value _ (index idx ts) tValue) => do
            -- When smallStep an intermediate step, which we determined to be a value, it should
            -- produce Step, and never Value constructor. If for some reason Value constructor
            -- is happened we have an issue somewhere in the evaluator.
            -- TODO: Use a different error, with stack trace included
            pure $ RtmErr fi "Internal error: ffi call \{show idx} element resulted in Value instead of Evaluation Step." [<]
          (Step _ tNotValue t' tEval ty1 t'Deriv) => do
            let Yes Refl = decEq (index idx (map Base pms)) ty1
                | No _ => pure $ RtmErr fi "Type error" [<]
            pure $ Step fi
                    uninhabited
                    (FFI fi (MkFFICall f n pms ret) (Vect.replaceAt idx t' args))
                    (EFFICallArg idx valuePrefix tNotValue tEval)
                    (Base ret)
                    (TFFICall fi (Lemmas.replaceDerivations idx t' t'Deriv argsDeriv))
          (StepX fi tNotValue t' tDeriv t'Deriv tEval) => ?sx17
          (RtmErr t msg ts) =>
            pure $ RtmErr fi msg (ts :< t)

  step (FFIVal fi (MkFFIVal baseType sn)) (Base baseType) (TFFIVal fi) = 
    pure $ Value fi (FFIVal fi (MkFFIVal baseType sn)) FFIVal

  step (ConvertFFI fi baseType t) (Base baseType) (TConvertFFI fi {ty} ffiRet tDeriv) = do
    p <- smallStep t _ tDeriv
    case p of
      (Value _ t tValue) => do
        let Yes ffiVal = isFFIValue t
            | No _ => pure $ RtmErr fi "" [<]
        Right (MkFFIVal _ so ** ffiConv) <- ConvertFFIVal fi t tValue ffiVal baseType
          | Left msg => pure $ RtmErr fi "FFI value: \{msg}" [<]
        pure $ Step fi
                uninhabited
                (FFIVal fi (MkFFIVal baseType so))
                (EConvertVal tValue ffiVal ffiConv)
                (Base baseType)
                (TFFIVal fi)
      (Step _ tNotValue t' tEval ty1 t'Deriv) => do
        let Yes Refl = decEq ty ty1
            | No _ => pure $ RtmErr fi "Type error" [<]
        pure $ Step fi
                uninhabited
                (ConvertFFI fi baseType t')
                (EConvert tNotValue tEval)
                (Base baseType)
                (TConvertFFI fi {ty=ty} ffiRet t'Deriv)
      (StepX fi tNotValue t' tDeriv t'Deriv tEval) => ?sx18
      (RtmErr t msg ts) =>
        pure $ RtmErr fi msg (ts :< t)

export
evaluate : (t : Tm) -> (ty : Ty) -> ([<] |- t <:> ty) -> Eval (Either (t' : Tm ** Value t') RuntimeError)
evaluate t ty tDeriv = do
  p <- smallStep t ty tDeriv
  case p of
    (Value fi t tValue) => pure (Left (t ** tValue))
    (RtmErr fi msg trace) => pure (Right (MkRuntimeError fi msg trace))
    (Step fi tNotValue t' tEval ty' t'Deriv) => evaluate t' ty' t'Deriv
    (StepX fi tNotValue t' tDeriv t'Deriv tEval) => evaluate t' _ t'Deriv
