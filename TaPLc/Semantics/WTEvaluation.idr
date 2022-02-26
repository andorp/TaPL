module TaPLc.Semantics.WTEvaluation

import TaPLc.IR.WellTypedTerm
import public TaPLc.Semantics.WTSubstituition
import public TaPLc.IR.Name
import public TaPLc.IR.Variant

import Data.Vect
import Data.SnocList
import Decidable.Equality
import Data.Nat

import TaPLc.Data.Vect
import TaPLc.IR.WellTypedTerm
import TaPLc.IR.Type
import TaPLc.IR.Record
import TaPLc.IR.Context
import TaPLc.IR.Info
import TaPLc.Typing.Rules
import TaPLc.Semantics.CannonicalForm
import TaPLc.Semantics.Rules
import TaPLc.Semantics.ShowRules
import TaPLc.IR.FFI
import TaPLc.Typing.Lemmas

public export
data RuntimeError : Type where
  MkRuntimeError : (fi : Info) -> (msg : String) -> (trace : SnocList Info) -> RuntimeError

export
Show RuntimeError where
  showPrec d (MkRuntimeError fi msg trace) = showCon d "MkRuntimeError" $ showArg fi ++ showArg msg ++ showArg trace

export
data Progress : Tm ctx ty -> Type where
  Value  : (fi : Info) -> (t : Tm ctx ty) -> (tValue : Value t) -> Progress t
  RtmErr : (fi : Info) -> (msg : String) -> (trace : SnocList Info) -> Progress t
  Step  :  (fi : Info)
        -> (tNotValue : Not (Value t))
        -> (t' : Tm ctx ty)
--        -> (tEval : Evaluation t t')
        -> Progress t

smallStep : {ty : Ty} -> (t : Tm [<] ty) -> Builtin.Unit -- () -- Progress t
smallStep t = ?st1
