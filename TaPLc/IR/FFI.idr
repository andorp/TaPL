module TaPLc.IR.FFI

import Data.Vect


public export
BaseType : Type
BaseType = String

public export
data FFICall : Nat -> Type where
  MkFFICall : (funName : String) -> (n : Nat) -> (argTys : Vect n BaseType) -> (retTy : BaseType) -> FFICall n

public export
ffiCallRetType : FFICall n -> BaseType
ffiCallRetType (MkFFICall funName _ argTys retTy) = retTy

public export
data FFIVal : BaseType -> Type where
  MkFFIVal : (baseType : BaseType) -> (serialNo : Nat) -> FFIVal baseType
