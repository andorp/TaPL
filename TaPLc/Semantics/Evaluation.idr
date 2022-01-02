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
data Progress : Tm -> Ty -> Type where
  Value  : (fi : Info) -> (t : Tm) -> (tValue : Value t) -> (tDeriv : [<] |- t <:> ty) -> Progress t ty
  RtmErr : (fi : Info) -> (msg : String) -> (trace : SnocList Info) -> Progress t ty
  -- TODO: Add tDeriv and use type-safety.
  Step  :  (fi : Info)
        -> (tNotValue : Not (Value t))
        -> (t' : Tm)
        -> (tEval : Evaluation t t')
        -> (ty' : Ty)
        -> (t'Deriv : [<] |- t' <:> ty')
        -> Progress t ty'

export
Show (Progress t ty) where
  showPrec d (Value fi t tValue tDeriv) = showCon d "Value" $ showArg fi ++ showArg tValue
  showPrec d (Step fi tNotValue t' tEval ty' t'Deriv) = showCon d "Step" $ showArg fi ++ showArg tEval
  showPrec d (RtmErr fi msg trace) = showCon d "RtmErr" $ showArg fi ++ showArg msg ++ showArg trace

namespace EvalMonad

  public export
  data Eval : Type -> Type where
    Pure : (x : t) -> Eval t
    Bind : (Eval a) -> (a -> Eval b) -> Eval b
    OnProgress : {t : Tm} -> (p : Progress t ty) -> Eval Unit
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
runEval i (OnProgress (Value fi t x y))         = i.onValue fi x
runEval i (OnProgress (Step  fi f t' e ty' t'd))      = i.onStep fi t' e
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
  smallStep : (t : Tm) -> (ty : Ty) -> (tDeriv : [<] |- (t <:> ty)) -> Eval (Progress t ty)
  smallStep t ty deriv = do
    p <- step t ty deriv
    OnProgress p
    pure p

  total
  step : (t : Tm) -> (ty : Ty) -> (tDeriv : [<] |- (t <:> ty)) -> Eval (Progress t ty)

  -- Because of the empty context, a free variable can not refer to anything.  
  step (Var _ _) _ (TVar _ Here)      impossible
  step (Var _ _) _ (TVar _ (There x)) impossible
  
  step (Abs fi1 x1 ty1 tm2) (Arr ty1 ty2) (TAbs fi x) = pure (Value fi1 _ Abs (TAbs fi x))
  
  step (App fi1 t1 t2) ty (TApp {ty11 = ty11} fi1 t2Deriv t1Deriv) =
    case !(smallStep t1 (Arr ty11 ty) t2Deriv) of
      (Value  _ _ t1Value _) =>
        pure $ case !(smallStep t2 ty11 t1Deriv) of
          -- TODO: Use a different approach for cannonical forms, as deriv arguments
          -- should have 0 quantity.
          (Value  _ _ t2Value _) => case cannonicalForms t1 t1Value (Arr ty11 ty) t2Deriv of
            (fi ** var ** t ** Refl) =>
              Step fi1
                uninhabited
                (substituition (var, t2) t)
                (EAppAbs t2Value)
                ty
                (Lemmas.application t t2 var ty t1Deriv t2Deriv)
          (Step  _ t2NotValue t2' t2Eval ty11 t2'Deriv) =>
            Step fi1
              uninhabited
              (App fi1 t1 t2')
              (EApp2 t1Value t2NotValue t2Eval)
              ty
              (TApp {ty11=ty11} fi1 t2Deriv t2'Deriv)
          (RtmErr t m ts) =>
            RtmErr fi1 m (ts :< t)
      (Step  _ t1NotValue t1' t1Eval (Arr ty11 ty) t1'Deriv) =>
        pure $ Step fi1
                uninhabited
                (App fi1 t1' t2)
                (EApp1 t1NotValue t1Eval)
                ty
                (TApp {ty11=ty11} fi1 ?t1'Deriv t1Deriv)
      (RtmErr t m ts) =>
        pure $ RtmErr fi1 m (ts :< t)
  
  step (True fi) Bool (TTrue fi) = pure (Value fi _ True (TTrue fi))
  
  step (False fi) Bool (TFalse fi) = pure (Value fi _ False (TFalse fi))
  
  step (If fi tp tt te) ty (TIf fi tpDeriv ttDeriv teDeriv) =
    pure $ case !(smallStep tp Bool tpDeriv) of
      (Value _ _ True _) =>
        Step fi uninhabited tt EIfTrue ty ttDeriv
      (Value _ _ False _) =>
        Step fi uninhabited te EIfFalse ty teDeriv
      (Step _ tpNotValue t' tpEval Bool t'Deriv) =>
        Step fi uninhabited (If fi t' tt te) (EIf tpNotValue tpEval) ty
             (TIf fi t'Deriv ttDeriv teDeriv)
      (RtmErr t m ts) =>
        RtmErr fi m (ts :< t)

  step (Unit fi) Unit (TUnit fi) = pure (Value fi _ Unit (TUnit fi))

  step (Seq fi t1 t2) ty (TSeq fi t1Deriv t2Deriv) =
    pure $ case !(smallStep t1 Unit t1Deriv) of
      (Value _ _ Unit _) =>
        Step fi uninhabited t2 ESeqNext ty t2Deriv
      (Step _ t1NotValue t1' t1Eval Unit t1'Deriv) =>
        Step fi uninhabited (Seq fi t1' t2) (ESeq t1NotValue t1Eval) ty (TSeq fi t1'Deriv t2Deriv)
      (RtmErr t m ts) => RtmErr fi m (ts :< t)

  step (Let fi x1 t1 t2) ty (TLet fi {ty1} t1Deriv t2Deriv) =
    pure $ case !(smallStep t1 _ t1Deriv) of
      (Value _ t1 t1Value _) =>
        Step fi uninhabited (substituition (x1,t1) t2) (ELetV t1Value) ty
             (Substituition.keepsType t1 t2 x1 ty1 ty t1Deriv t2Deriv)
      (Step _ t1NotValue t1' t1Eval ty1 t1'Deriv) =>
        Step fi uninhabited (Let fi x1 t1' t2) (ELet t1NotValue t1Eval) ty
             (TLet fi t1'Deriv t2Deriv)
      (RtmErr t m ts) =>
        RtmErr fi m (ts :< t)

  step (Tuple fi n ts) (Tuple n tys) (TTuple fi tyDerivations) =
    case ValuePrefix.descriptor ts of
      Values vs =>
        pure $ Value fi (Tuple fi n ts) (Tuple vs) (TTuple fi tyDerivations)
      HasNonValue idx valuePrefix => do
        -- Reason for assert_total:
        -- - The index function is total for Data.Vect
        -- - The ts and tys are structurally smaller than the original Tuple parameter.
        pure $ case !(assert_total $ smallStep (index idx ts) (index idx tys) (index idx tyDerivations)) of
          (Value _ (index idx ts) tValue _) => do
            -- When smallStep an intermediate step, which we determined to be a value, it should
            -- produce Step, and never Value constructor. If for some reason Value constructor
            -- is happened we have an issue somewhere in the evaluator.
            -- TODO: Use a different error, with stack-trace
            RtmErr fi "Internal error: tuple \{show idx} element resulted in Value instead of Evaluation Step." [<]
          (Step  _ tNotValue t' tEval (index idx tys) t'Deriv) => do
            Step fi
              (\case
                  (Tuple assumeTupleValues) => tNotValue (index idx assumeTupleValues))
              (Tuple fi n (Vect.replaceAt idx t' ts))
              (ETuple idx valuePrefix tNotValue tEval)
              (Tuple n tys)
              (TTuple fi (replaceDerivations idx t' t'Deriv tyDerivations))
          (RtmErr t msg ts) => 
            RtmErr fi msg (ts :< t)

  step (Proj fi t n i) (index i tys) (TProj fi {tys} tpDeriv) =
    pure $ case !(smallStep t (Tuple n tys) tpDeriv) of
      (Value _ (Tuple fi n tms) (Tuple vs) (TTuple fi y)) => 
        Step fi uninhabited (Vect.index i tms) (EProjTuple (Tuple vs)) (index i tys)
             (Lemmas.tupleProj i (Tuple vs) tpDeriv)
      (Step  _ tNotValue t' tEval (Tuple n tys) t'Deriv) => do
        Step fi uninhabited (Proj fi t' n i) (EProj tNotValue tEval) (index i tys) (TProj fi t'Deriv)
      (RtmErr t msg ts) =>
        RtmErr fi msg (ts :< t)

  step (Record fi (MkRecord n fields ts u)) (Record (MkRecord n fields tys u)) (TRcd fi fieldDerivations) =
    case ValuePrefix.descriptor ts of
      (Values vs)
        => pure $ Value fi (Record fi (MkRecord n fields ts u)) (Record vs) (TRcd fi fieldDerivations)
      (HasNonValue idx valuePrefix) => do
        -- Reason for assert_total:
        -- - The index function is total for Data.Vect
        -- - The ts and tys are structurally smaller than the original Tuple parameter.
        pure $ case !(assert_total $ smallStep (index idx ts) (index idx tys) (index idx fieldDerivations)) of
          (Value _ (index idx ts) tValue _) => do
            -- When smallStep an intermediate step, which we determined to be a value, it should
            -- produce Step, and never Value constructor. If for some reason Value constructor
            -- is happened we have an issue somewhere in the evaluator.
            -- TODO: Use a different error, with stack trace included
            RtmErr fi "Internal error: record \{show idx} element resulted in Value instead of Evaluation Step." [<]
          (Step _ tNotValue t' tEval (index idx tys) t'Deriv) => do
            Step fi
              (\case
                (Record vs) => tNotValue (index idx vs))
              (Record fi (MkRecord n fields (Vect.replaceAt idx t' ts) u))
              (ERcd idx valuePrefix tNotValue tEval)
              (Record (MkRecord n fields tys u))
              (TRcd fi (Lemmas.replaceDerivations idx t' t'Deriv fieldDerivations))
          (RtmErr t msg ts) =>
            RtmErr fi msg (ts :< t)

  step (ProjField fi field t)
       (index idx tys)
       (TRProj fi {n} {tys} {fields} {u} {idx} fieldInRecord tDeriv) = do
    pure $ case !(smallStep t (Record (MkRecord n fields tys u)) tDeriv) of
      (Value _ (Record fi (MkRecord n fields tms u)) (Record vs) (TRcd fi y)) =>
        Step fi
          uninhabited
          (Vect.index idx tms)
          (EProjRec {inr=fieldInRecord} vs)
          (index idx tys)
          (Lemmas.recordFieldType tms tys fields u fi idx (Record vs) tDeriv)
      (Step _ tNotValue t' tEval (Record (MkRecord n fields tys u)) t'Deriv) =>
        Step fi
          uninhabited
          (ProjField fi field t')
          (EProjField tNotValue tEval)
          (index idx tys)
          (TRProj fi fieldInRecord t'Deriv)
      (RtmErr t msg ts) =>
        RtmErr fi msg (ts :< t)

  step (Variant fi tag tj (Variant (MkVariant n tags tys u nz)))
       (Variant (MkVariant n tags tys u nz))
       (TVariant fi tagIndex nameIndex tjDeriv) =
    pure $ case !(smallStep tj _ tjDeriv) of
      (Value _ tj tValue _) =>
        (Value fi _ (Variant tValue) (TVariant fi tagIndex nameIndex tjDeriv))
      (Step _ tNotValue t' tEval (index tagIndex tys) t'Deriv) => do
        Step fi
          (\case (Variant assumeValue) => tNotValue assumeValue)
          (Variant fi tag t' (Variant (MkVariant n tags tys u nz)))
          (EVariant tNotValue tEval)
          (Variant (MkVariant n tags tys u nz))
          (TVariant fi tagIndex nameIndex t'Deriv)
      (RtmErr t msg ts) =>
        RtmErr fi msg (ts :< t)

  step (Case fi t0 (MkVariant n tags alts u nz)) ty (TCase fi {alts} {ty} {tys} t0Deriv variantDerivs) =
    pure $ case !(smallStep t0 _ t0Deriv) of
      (Value _ (Variant fi tag t (Variant (MkVariant n tags tys u nz)))
               (Variant tValue) (TVariant fi idx inTags z)) => do
        Step fi
          uninhabited
          (substituition (fst (index idx alts),t) (snd (index idx alts)))
          (ECaseVariant idx inTags)
          ty
          (Lemmas.caseEval ty idx alts t0Deriv)
      (Step _ tNotValue t' tEval (Variant (MkVariant n tags tys u nz)) t'Deriv) => do
        Step fi
          uninhabited
          (Case fi t' (MkVariant n tags alts u nz))
          (ECase tNotValue tEval)
          ty
          (TCase fi t'Deriv variantDerivs)
      (RtmErr t msg ts) =>
        RtmErr fi msg (ts :< t)

  step (Fix fi t1) ty (TFix fi t1Deriv) = do
    pure $ case !(smallStep t1 (Arr ty ty) t1Deriv) of
      (Value _ (Abs fia va tya tma) Abs _) =>
        Step fi
          uninhabited
          (substituition (va, Fix fi (Abs fia va tya tma)) tma)
          EFixBeta
          ty
          (Lemmas.fixEval t1Deriv)
      (Step  _ t1NotVaue t2 t1Eval (Arr ty ty) t1Deriv) => do
        Step fi
          uninhabited
          (Fix fi t2)
          (EFix t1NotVaue t1Eval)
          ty
          (TFix fi t1Deriv)
      (RtmErr t m ts) =>
        RtmErr fi m (ts :< t)

  step (Nil fi ty) (List ty) (TNil fi) = pure (Value fi _ Nil (TNil fi)) 

  step (Cons fi ty t1 t2) (List ty) (TCons fi t1Deriv t2Deriv) =
    case !(smallStep t1 ty t1Deriv) of
      (Value _ t1 t1Value _) =>
        pure $ case !(smallStep t2 (List ty) t2Deriv) of
          (Value _ t2 t2Value _) =>
            Value fi (Cons fi ty t1 t2) (Cons t1Value t2Value) (TCons fi t1Deriv t2Deriv)
          (Step _ t2NotValue t2' t2Eval (List ty) t2'Deriv) => do
            Step fi
              (\case
                (Cons hValue tValue) => t2NotValue tValue)
              (Cons fi ty t1 t2')
              (ECons2 t1Value t2NotValue t2Eval)
              (List ty)
              (TCons fi t1Deriv t2'Deriv)
          (RtmErr t m ts) =>
            RtmErr fi m (ts :< t)
      (Step _ t1NotValue t1' t1Eval ty t1'Deriv) => do
        pure $ Step fi
                (\case
                  (Cons hValue tlValue) => t1NotValue hValue)
                (Cons fi ty t1' t2)
                (ECons1 t1NotValue t1Eval)
                (List ty)
                (TCons fi t1'Deriv t2Deriv)
      (RtmErr t m ts) =>
        pure $ RtmErr fi m (ts :< t)

  step (IsNil fi ty t) Bool (TIsNil fi tDeriv) =
    pure $ case !(smallStep t (List ty) tDeriv) of
      (Value _ (Nil _ _) Nil _) =>
        Step fi uninhabited (True fi) EIsNilNil Bool (TTrue fi)
      (Value _ (Cons _ _ _ _) (Cons hdValue tlValue) _) =>
        Step fi uninhabited (False fi) (EIsNilCons hdValue tlValue) Bool (TFalse fi)
      (Step _ tNotValue t' tEval (List ty) t'Deriv) => do
        Step fi uninhabited (IsNil fi ty t') (EIsNil tNotValue tEval) Bool (TIsNil fi t'Deriv)
      (RtmErr t msg ts) =>
        RtmErr fi msg (ts :< t)

  step (Head fi _ t) ty (THead fi tDeriv) =
    pure $ case !(smallStep t _ tDeriv) of
      (Value _ (Nil fi ty) Nil _) => 
        RtmErr fi "Head of empty list." [<]
      (Value _ (Cons fi ty hd tl) (Cons hdValue tlValue) (TCons fi y z)) =>
        Step fi uninhabited hd (EHeadCons hdValue tlValue) ty (Lemmas.headEval tDeriv)
      (Step _ tNotValue t' tEval (List ty) t'Deriv) => do
        Step fi uninhabited (Head fi ty t') (EHead tNotValue tEval) ty (THead fi t'Deriv)
      (RtmErr t m ts) => 
        RtmErr fi m (ts :< t)

  step (Tail fi ty t) (List ty) (TTail fi tDeriv) =
    pure $ case !(smallStep t (List ty) tDeriv) of
      (Value _ (Nil fi ty) Nil _) =>
        RtmErr fi "Tail of empty list." [<]
      (Value _ (Cons fi2 ty1 hd tl) (Cons hdv tlv) _) =>
        Step fi uninhabited tl (ETailCons hdv tlv) (List ty) (Lemmas.tailType tDeriv)
      (Step _ tNotValue t' tEval (List ty) t'Deriv) => do
        Step fi uninhabited (Tail fi ty t') (ETail tNotValue tEval) (List ty) (TTail fi t'Deriv)
      (RtmErr t msg ts) =>
        RtmErr fi msg (ts :< t)

  step (LitNat fi l) LitNat (TLitNat fi) =
    pure $ Value fi (LitNat fi l) LitNat (TLitNat fi)

  step (FFI fi (MkFFICall f n pms ret) args) (Base ret) (TFFICall fi argsDeriv) = do
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
        pure $ case !(assert_total $ smallStep (index idx args) _ (index idx argsDeriv)) of
          (Value _ (index idx ts) tValue _) => do
            -- When smallStep an intermediate step, which we determined to be a value, it should
            -- produce Step, and never Value constructor. If for some reason Value constructor
            -- is happened we have an issue somewhere in the evaluator.
            -- TODO: Use a different error, with stack trace included
            RtmErr fi "Internal error: ffi call \{show idx} element resulted in Value instead of Evaluation Step." [<]
          (Step _ tNotValue t' tEval _ t'Deriv) => do
            Step fi
              uninhabited
              (FFI fi (MkFFICall f n pms ret) (Vect.replaceAt idx t' args))
              (EFFICallArg idx valuePrefix tNotValue tEval)
              (Base ret)
              (TFFICall fi (Lemmas.replaceDerivations idx t' t'Deriv argsDeriv))
          (RtmErr t msg ts) =>
            RtmErr fi msg (ts :< t)

  step (FFIVal fi (MkFFIVal baseType sn)) (Base baseType) (TFFIVal fi) = 
    pure $ Value fi (FFIVal fi (MkFFIVal baseType sn)) FFIVal (TFFIVal fi)

  step (ConvertFFI fi baseType t) (Base baseType) (TConvertFFI fi {ty} ffiRet tDeriv) = do
    case !(smallStep t _ tDeriv) of
      (Value _ t tValue ffiVal) => do
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
      (Step _ tNotValue t' tEval ty t'Deriv) => do
        pure $ Step fi
                uninhabited
                (ConvertFFI fi baseType t')
                (EConvert tNotValue tEval)
                (Base baseType)
                (TConvertFFI fi {ty=ty} ffiRet t'Deriv)
      (RtmErr t msg ts) =>
        pure $ RtmErr fi msg (ts :< t)

export
evaluate : (t : Tm) -> (ty : Ty) -> ([<] |- t <:> ty) -> Eval (Either (t' : Tm ** Value t') RuntimeError)
evaluate t ty tDeriv =
  case !(smallStep t ty tDeriv) of
    (Value fi t tValue tDeriv) =>
      pure (Left (t ** tValue))
    (RtmErr fi msg trace) =>
      pure (Right (MkRuntimeError fi msg trace))
    (Step fi tNotValue t' tEval ty' t'Deriv) =>
      evaluate t' ty' t'Deriv
