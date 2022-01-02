module TaPLc.Semantics.SimpleInterp

import Data.Vect
import TaPLc.IR.Info
import TaPLc.IR.FFI
import TaPLc.IR.Term
import TaPLc.Semantics.Evaluation
import TaPLc.Semantics.Rules
import TaPLc.Semantics.ShowRules
import Control.Monad.State
import TaPLc.IR.Record

Counter : Type
Counter = Nat

export
data SimpleInterp : Type -> Type where
  MkSimpleInterp : StateT Counter IO a -> SimpleInterp a

export
runSimpleInterp : SimpleInterp a -> IO a
runSimpleInterp (MkSimpleInterp m) = evalStateT 0 m

export
Functor SimpleInterp where
  map f (MkSimpleInterp m) = MkSimpleInterp (map f m)

export
Applicative SimpleInterp where
  pure x = MkSimpleInterp (pure x)
  (MkSimpleInterp f) <*> (MkSimpleInterp x) = MkSimpleInterp (f <*> x)

export
Monad SimpleInterp where
  join (MkSimpleInterp m) = MkSimpleInterp $ do
    (MkSimpleInterp n) <- m
    n
  (MkSimpleInterp m) >>= k = MkSimpleInterp $ do
    x <- m
    let (MkSimpleInterp l) = k x
    l

onValue : (fi : Info) -> {0 t : Tm} -> Value t -> SimpleInterp Unit
onValue fi v = MkSimpleInterp $ liftIO $ printLn $ ("OnValue", fi,v)

onStep : (fi : Info) -> {0 t : Tm} -> (t' : Tm) -> (e : Evaluation t t') -> SimpleInterp Unit
onStep fi t' e = MkSimpleInterp $ liftIO $ printLn $ ("OnStep",fi,e,t')

onRuntimeError : (fi : Info) -> (msg : String) -> (trace : SnocList Info) -> SimpleInterp Unit
onRuntimeError fi msg trace = MkSimpleInterp $ liftIO $ printLn ("OnRtmErr", fi,msg)

ffiCall : (fi : Info) -> {n : Nat} -> (c : FFICall n) -> (args : Vect n Tm) -> SimpleInterp (Either String (FFIVal (ffiCallRetType c)))
ffiCall fi (MkFFICall funName n argTys retTy) args = pure $ Left "Unknown function: \{funName}"

convertFFIVal : (fi : Info) -> (t : Tm) -> (vt : Value t) -> (0 ft : FFI t) -> (b : BaseType) -> SimpleInterp (Either String (v : (FFIVal b) ** FFIConv t v))
convertFFIVal fi t vt ft b = pure $ Left "Unknown BaseType: \{b}"

export
evalImpl : EvalImpl SimpleInterp
evalImpl = MkEvalImpl
  { onValue        = onValue
  , onStep         = onStep
  , onRuntimeError = onRuntimeError
  , ffiCall        = ffiCall
  , convertFFIVal  = convertFFIVal
  }
