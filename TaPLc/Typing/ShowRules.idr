module TaPLc.Typing.ShowRules

import Data.Vect

import TaPLc.IR.Type
import TaPLc.IR.Record
import TaPLc.IR.Variant
import TaPLc.IR.Name
import TaPLc.IR.FFI
import TaPLc.IR.Term
import TaPLc.IR.Info
import TaPLc.IR.Context
import TaPLc.Typing.Rules

export
Show (gamma |- (t <:> ty)) where
  showPrec d (TVar fi x)            = showCon d "TVar" $ showArg fi ++ showArg "TODO"
  showPrec d (TAbs fi x)            = showCon d "TAbs" $ showArg fi ++ showArg x
  showPrec d (TApp fi x y)          = showCon d "TApp" $ showArg fi ++ showArg x ++ showArg y
  showPrec d (TTrue fi)             = showCon d "TTrue" $ showArg fi
  showPrec d (TFalse fi)            = showCon d "TFalse" $ showArg fi
  showPrec d (TIf fi x y z)         = showCon d "TIf" $ showArg fi ++ showArg x ++ showArg y ++ showArg z
  showPrec d (TUnit fi)             = showCon d "TUnit" $ showArg fi
  showPrec d (TSeq fi x y)          = showCon d "TSeq" $ showArg fi ++ showArg x ++ showArg y
  showPrec d (TLet fi x y)          = showCon d "TLet" $ showArg fi ++ showArg x ++ showArg y
  showPrec d (TTuple fi x)          = showCon d "TTuple" $ showArg fi ++ showArg "TODO"
  showPrec d (TProj fi x)           = showCon d "TProj" $ showArg fi ++ showArg x
  showPrec d (TRcd fi x)            = showCon d "TRcd" $ showArg fi ++ showArg "TODO"
  showPrec d (TRProj fi x y)        = showCon d "TRProj" $ showArg fi ++ showArg "TODO" ++ showArg y
  showPrec d (TVariant fi idx x y)  = showCon d "TVariant" $ showArg fi ++ showArg idx ++ showArg "TODO" ++ showArg y
  showPrec d (TCase fi x y)         = showCon d "TCase" $ showArg fi ++ showArg x ++ showArg "TODO"
  showPrec d (TFix fi x)            = showCon d "TFix" $ showArg fi ++ showArg x
  showPrec d (TNil fi)              = showCon d "TNil" $ showArg fi
  showPrec d (TCons fi x y)         = showCon d "TCons" $ showArg fi ++ showArg x ++ showArg y
  showPrec d (TIsNil fi x)          = showCon d "TIsNil" $ showArg fi ++ showArg x
  showPrec d (THead fi x)           = showCon d "THead" $ showArg fi ++ showArg x
  showPrec d (TTail fi x)           = showCon d "TTail" $ showArg fi ++ showArg x
  showPrec d (TLitNat fi)           = showCon d "TLitNat" $ showArg fi
  showPrec d (TFFICall fi x)        = showCon d "TFFICall" $ showArg fi ++ showArg "TODO"
  showPrec d (TFFIVal fi)           = showCon d "TFFIVal" $ showArg fi
  showPrec d (TConvertFFI fi x y)   = showCon d "TConvertFFI" $ showArg fi ++ showArg "TODO" ++ showArg y
