module TaPLc.Semantics.WTRules

import Data.List
import Data.Vect
import Data.Vect.Quantifiers

import TaPLc.IR.WellTypedTerm
import TaPLc.IR.Type
import TaPLc.IR.Info
import TaPLc.IR.Name
import TaPLc.IR.Record
import TaPLc.IR.Variant
import TaPLc.IR.UniqueNames
import TaPLc.Data.Vect
import TaPLc.Semantics.WTSubstituition
import TaPLc.IR.FFI
import TaPLc.Data.Vect.Quantifiers


namespace Value

  public export
  data AllValue : (tys : Vect n Ty) -> All (Tm ctx) tys -> Type where
    Nil  : AllValue [] []
    (::) : Value t -> AllValue tys ts -> AllValue (ty :: tys) (t :: ts)

data Evaluation : (Tm ctx ty) -> (Tm ctx ty) -> Type where

  EApp1 :
    Not (Value t1) ->
    Evaluation t1 t1' ->
    Evaluation (App fi t1 t2) (App fi t1' t2)
  
  EApp2 :
    Value v1 ->
    Not (Value t2) ->
    Evaluation t t' ->
    Evaluation (App fi v1 t) (App fi v1 t')
  
  EAppAbs :
    Value v ->
    Evaluation (App fi (Abs fi2 x ty t) v) (substituition v t)

  ESeq :
    Not (Value t1) ->
    Evaluation t1 t1' ->
    Evaluation (Seq fi t1 t2) (Seq fi t1' t2)
  
  ESeqNext :
    Evaluation (Seq fi1 (Unit fi2) t2) t2
  
  ELetV :
    Value v ->
    Evaluation (Let fi x v t) (substituition v t)
  
  ELet :
    Not (Value t1) ->
    Evaluation t t' ->
    Evaluation (Let fi x t t2) (Let fi x t' t2)

  EProjTuple :
    AllValue tys tms ->
    Evaluation (Proj fi1 n j (Tuple fi2 n tys tms)) (index j tms)

  EProj :
    Not (Value t) ->
    Evaluation t t' ->
    Evaluation (Proj fi n j t) (Proj fi n j t')
  
  ETuple :
    AllValue (Vect.Take.take i tys) (take i tms) ->
    Not (Value (index i tms)) ->
    Evaluation (index i tms) t' ->
    Evaluation (Tuple fi n tys tms) (Tuple fi n tys tms)
  
  EProjRec :
    AllValue tys.values tms ->
    Evaluation
      (ProjField fi1 field idx (Record fi2 tys tms))
      (index (finIdx tys idx) tms)

  EProjField :
    Not (Value t) ->
    Evaluation t t' ->
    Evaluation (ProjField fi f i t) (ProjField fi f i t')

  ERcd :
    AllValue (Vect.Take.take i tys.values) (take i tms) ->
    Evaluation
      (Record fi tys tms) (Record fi tys (replaceAt i t' tms))

  ECase :
    Not (Value t) ->
    Evaluation t t' ->
    Evaluation (Case fi v t alts) (Case fi v t' alts)

  EVariant :
    Not (Value t) ->
    Evaluation t t' ->
    Evaluation (Variant fi tag v r t) (Variant fi tag v r t')

  ECaseVariant :
    Value t ->
    Evaluation
      (Case fi1 v (Variant fi tag v r s) alts)
      (substituition s (Quantifiers.index {n=v.size} {xs=v.info} (finIdx v r) alts))

  EFix :
    Not (Value t) ->
    Evaluation t t' ->
    Evaluation (Fix fi t) (Fix fi t')
  
  EFixBeta :
    Evaluation
      (Fix fi1 (Abs fi2 v ty tm))
      (substituition (Fix fi (Abs fi2 v ty tm)) tm)
  
  ECons1 :
    Not (Value t1) ->
    Evaluation t1 t1' ->
    Evaluation (Cons fi ty t1 t2) (Cons fi ty t1' t2)
  
  ECons2 :
    Value t1 ->
    Not (Value t2) ->
    Evaluation t2 t2' ->
    Evaluation (Cons fi ty t1 t2) (Cons fi ty t1 t2')
  
  EIsNilNil :
    Evaluation (IsNil fi1 ty (Nil fi2 ty)) (True fi1)

  EIsNilCons :
    Value t1 ->
    Value t2 ->
    Evaluation (IsNil fi1 ty (Cons fi2 ty t1 t2)) (False fi1)
  
  EIsNil :
    Not (Value t) ->
    Evaluation t t' ->
    Evaluation (IsNil fi ty t) (IsNil fi ty t')
  
  EHeadCons :
    Value t1 ->
    Value t2 ->
    Evaluation (Head fi1 ty (Cons fi2 ty t1 t2)) t1
  
  EHead :
    Not (Value t) ->
    Evaluation t t' ->
    Evaluation (Head fi ty t) (Head fi ty t')
  
  ETailCons :
    Value t1 ->
    Value t2 ->
    Evaluation (Tail fi1 ty (Cons fi2 ty t1 t2)) t2
  
  ETail :
    Not (Value t) ->
    Evaluation t t' ->
    Evaluation (Tail fi ty t) (Tail fi ty t')
  
  EIfTrue :
    Evaluation (If fi1 (True fi2) t2 t3) t2
  
  EIfFalse :
    Evaluation (If fi1 (False fi2) t2 t3) t3
  
  EIf :
    Not (Value t1) ->
    Evaluation t1 t1' ->
    Evaluation (If fi t1 t2 t3) (If fi t1' t2 t3)
  
  EFFICallArg :
    (idx : Fin f.argsSize) ->
    {t' : Tm ctx (index idx (map Base f.argsTy))} ->
    AllValue (Vect.Take.take idx (map Base f.argsTy)) (take idx args) ->
    Not (Value (Quantifiers.index {xs=map Base f.argsTy} idx args)) ->
    Evaluation (Quantifiers.index {xs=map Base f.argsTy} idx args) t' ->
    Evaluation
      (FFI fi f args)
      (FFI fi f (Quantifiers.replaceAt {xs=map Base f.argsTy} idx t' args))

  EFFICall :
    Evaluation
      (FFI fi f args)
      (FFIVal fi (MkFFIVal f.retTy sn))

  EConvert :
    Not (Value t) ->
    Evaluation t t' ->
    Evaluation
      (ConvertFFI fi ffi baseType t)
      (ConvertFFI fi ffi baseType t')

  EConvertVal :
    Value t ->
    Evaluation
      (ConvertFFI fi baseType ffi t)
      (FFIVal fi (MkFFIVal baseType so))
