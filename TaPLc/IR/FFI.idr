module TaPLc.IR.FFI

import Data.Vect


public export
BaseType : Type
BaseType = String

public export
data FFICall : Nat -> Type where
  MkFFICall : (funName : String) -> (n : Nat) -> (argTys : Vect n BaseType) -> (retTy : BaseType) -> FFICall n

export
Show (FFICall n) where
  showPrec d (MkFFICall f n arg ret) = showCon d "MkFFICall" $ showArg f ++ showArg n ++ showArg arg ++ showArg ret

public export
ffiCallRetType : FFICall n -> BaseType
ffiCallRetType (MkFFICall funName _ argTys retTy) = retTy

public export
data FFIVal : BaseType -> Type where
  MkFFIVal : (baseType : BaseType) -> (serialNo : Nat) -> FFIVal baseType

export
Show (FFIVal b) where
  showPrec d (MkFFIVal b s) = showCon d "MkFFIVal" $ showArg b ++ showArg s
