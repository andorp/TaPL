module TaPLc.Semantics.ShowRules

import Data.Vect
import TaPLc.IR.Term
import TaPLc.Semantics.Substituition
import TaPLc.IR.Name
import TaPLc.IR.Record
import TaPLc.IR.Variant
import TaPLc.IR.FFI
import TaPLc.Semantics.Rules

export
Show (Evaluation t t') where
  show (EApp1 f x) = "EApp1"
  show (EApp2 x f y) = "EApp2"
  show (EAppAbs x) = "EAppAbs"
  show (ESeq f x) = "ESeq"
  show ESeqNext = "ESeqNext"
  show (ELetV x) = "ELetV"
  show (ELet f x) = "ELet"
  show (EProjTuple x) = "EProjTuple"
  show (EProj f x) = "EProj"
  show (ETuple idx x f y) = "ETuple"
  show (EProjRec vs) = "EProjRec"
  show (EProjField f x) = "EProjField"
  show (ERcd idx x f y) = "ERcd"
  show (ECase f x) = "ECase"
  show (EVariant f x) = "EVariant"
  show (ECaseVariant idx x) = "ECaseVariant"
  show (EFix f x) = "EFix"
  show EFixBeta = "EFixBet"
  show (ECons1 f x) = "ECons1"
  show (ECons2 x f y) = "ECons2"
  show EIsNilNil = "EIsNilNil"
  show (EIsNilCons x y) = "EIsNilCons"
  show (EIsNil f x) = "EIsNil"
  show (EHeadCons x y) = "EHeadCons"
  show (EHead f x) = "EHead"
  show (ETailCons x y) = "ETailCons"
  show (ETail f x) = "ETail"
  show EIfTrue = "EIfTrue"
  show EIfFalse = "EIfFalse"
  show (EIf f x) = "EIf"
  show (EFFICallArg idx x f y) = "EFFICallArg"
  show EFFICall = "EFFICall"
  show (EConvert f x) = "EConvert"
  show (EConvertVal x y z) = "EConvertVal"
