module TaPLc.IR.Term

import Data.Vect

import TaPLc.IR.Type
import TaPLc.IR.Record
import TaPLc.IR.Variant
import TaPLc.IR.Name
import TaPLc.IR.Info
import TaPLc.Data.Vect
import TaPLc.IR.FFI

%default total


public export
data Tm : Type where
  True  : (fi : Info)                                               -> Tm
  False : (fi : Info)                                               -> Tm
  If    : (fi : Info) -> (p,t,e : Tm)                               -> Tm
  Var   : (fi : Info) -> (i : Nat) -> (v : Name)                    -> Tm 
  Abs   : (fi : Info) -> (var : Name) -> (ty : Ty) -> (t : Tm)      -> Tm
  App   : (fi : Info) -> (t1, t2 : Tm)                              -> Tm
  Unit  : (fi : Info)                                               -> Tm

  Seq   : (fi : Info) -> (t1, t2 : Tm)                              -> Tm
  Let   : (fi : Info) -> (n : Name) -> (t : Tm) -> (b : Tm)         -> Tm
  
  -- TODO: Add Tuple datatype, similar to records
  Tuple : (fi : Info) -> (n : Nat) -> (ti : Vect n Tm)              -> Tm
  Proj  : (fi : Info) -> (t : Tm) -> (n : Nat) -> (i : Fin n)       -> Tm

  Record : (fi : Info) -> (Record.Record Tm)                        -> Tm
  ProjField : (fi : Info) -> (field : String) -> (t : Tm)           -> Tm

  Variant : (fi : Info) -> (tag : String) -> (t : Tm) -> (ty : Ty)  -> Tm
  Case : (fi : Info) -> (t : Tm) -> (alts : Variant (Name, Tm))     -> Tm

  Fix : (fi : Info) -> (t : Tm)                                     -> Tm

  Nil : (fi : Info) -> (ty : Ty)                                    -> Tm
  Cons : (fi : Info) -> (ty : Ty) -> (h,t : Tm)                     -> Tm
  IsNil : (fi : Info) -> (ty : Ty) -> (t : Tm)                      -> Tm
  Head : (fi : Info) -> (ty : Ty) -> (t : Tm)                       -> Tm
  Tail : (fi : Info) -> (ty : Ty) -> (t : Tm)                       -> Tm

  LitNat     : (fi : Info) -> (literal : Nat)                       -> Tm
  ConvertFFI : (fi : Info) -> (baseType : BaseType) -> Tm           -> Tm
  FFI        : (fi : Info) -> FFICall n -> (args : Vect n Tm)       -> Tm
  FFIVal     : (fi : Info) -> FFIVal baseType                       -> Tm

-- Reasons for assert_total, Tm parameters are structurally smaller than their containing constructor.
export
Show Tm where
  showPrec d (True fi) = showCon d "True" $ showArg fi
  showPrec d (False fi) = showCon d "False" $ showArg fi
  showPrec d (If fi p t e) = showCon d "If" $ showArg fi ++ assert_total (showArg p ++ showArg t ++ showArg e)
  showPrec d (Var fi i x) = showCon d "Var" $ showArg fi ++ showArg i
  showPrec d (Abs fi var ty t) = showCon d "Abs" $ showArg fi ++ showArg var ++ showArg ty ++ assert_total (showArg t)
  showPrec d (App fi t1 t2) = showCon d "App" $ showArg fi ++ assert_total (showArg t1 ++ showArg t2)
  showPrec d (Unit fi) = showCon d "Unit" $ showArg fi
  showPrec d (Seq fi t1 t2) = showCon d "Seq" $ showArg fi ++ assert_total (showArg t1 ++ showArg t2)
  showPrec d (Let fi n t b) = showCon d "Let" $ showArg fi ++ showArg n ++ assert_total (showArg t ++ showArg b)
  showPrec d (Tuple fi n ti) = showCon d "Tuple" $ showArg fi ++ showArg n ++ assert_total (showArg ti)
  showPrec d (Proj fi t n i) = showCon d "Proj" $ showArg fi ++ assert_total (showArg t ++ showArg n ++ showArg i)
  showPrec d (Record fi x) = showCon d "Record" $ showArg fi ++ assert_total (showArg x)
  showPrec d (ProjField fi field t) = showCon d "ProjField" $ showArg fi ++ showArg field ++ assert_total (showArg t)
  showPrec d (Variant fi tag t ty) = showCon d "Variant" $ showArg fi ++ showArg tag ++ assert_total (showArg t ++ showArg ty)
  showPrec d (Case fi t alts) = showCon d "Case" $ showArg fi ++ assert_total (showArg t ++ showArg alts)
  showPrec d (Fix fi t) = showCon d "Fix" $ showArg fi ++ assert_total (showArg t)
  showPrec d (Nil fi ty) = showCon d "Nil" $ showArg fi ++ showArg ty
  showPrec d (Cons fi ty h t) = showCon d "Cons" $ showArg fi ++ showArg ty ++ assert_total (showArg h ++ showArg t)
  showPrec d (IsNil fi ty t) = showCon d "IsNil" $ showArg fi ++ showArg ty ++ assert_total (showArg t)
  showPrec d (Head fi ty t) = showCon d "Head" $ showArg fi ++ showArg ty ++ assert_total (showArg t)
  showPrec d (Tail fi ty t) = showCon d "Tail" $ showArg fi ++ showArg ty ++ assert_total (showArg t)
  showPrec d (LitNat fi literal) = showCon d "LitNat" $ showArg fi ++ showArg literal
  showPrec d (ConvertFFI fi baseType x) = showCon d "ConvertFFI" $ showArg fi ++ showArg baseType ++ assert_total (showArg x)
  showPrec d (FFI fi x args) = showCon d "FFI" $ showArg fi ++ showArg x ++ assert_total (showArg args)
  showPrec d (FFIVal fi x) = showCon d "FFIVal" $ showArg fi ++ showArg x

namespace FFIValue

  public export
  data FFI : Tm -> Type where
    True   : FFI (True fi)
    False  : FFI (False fi)
    LitNat : FFI (LitNat fi lit)
    FFIVal : FFI (FFIVal fi val)

  export Uninhabited (FFI (If _ _ _ _))       where uninhabited _ impossible
  export Uninhabited (FFI (Var _ _ _))        where uninhabited _ impossible 
  export Uninhabited (FFI (Abs _ _ _ _))      where uninhabited _ impossible
  export Uninhabited (FFI (App _ _ _))        where uninhabited _ impossible
  export Uninhabited (FFI (Unit _))           where uninhabited _ impossible
  export Uninhabited (FFI (Seq _ _ _))        where uninhabited _ impossible
  export Uninhabited (FFI (Let _ _ _ _))      where uninhabited _ impossible
  export Uninhabited (FFI (Tuple _ a b))      where uninhabited _ impossible
  export Uninhabited (FFI (Proj _ _ a b))     where uninhabited _ impossible
  export Uninhabited (FFI (Record _ _))       where uninhabited _ impossible
  export Uninhabited (FFI (ProjField _ _ _))  where uninhabited _ impossible
  export Uninhabited (FFI (Variant _ _ _ _))  where uninhabited _ impossible
  export Uninhabited (FFI (Case _ _ _))       where uninhabited _ impossible
  export Uninhabited (FFI (Fix _ _))          where uninhabited _ impossible
  export Uninhabited (FFI (Nil _ _))          where uninhabited _ impossible
  export Uninhabited (FFI (Cons _ _ _ _))     where uninhabited _ impossible
  export Uninhabited (FFI (IsNil _ _ _))      where uninhabited _ impossible
  export Uninhabited (FFI (Head _ _ _))       where uninhabited _ impossible
  export Uninhabited (FFI (Tail _ _ _))       where uninhabited _ impossible
  export Uninhabited (FFI (ConvertFFI _ _ _)) where uninhabited _ impossible
  export Uninhabited (FFI (FFI _ a b))        where uninhabited _ impossible

  export
  isFFIValue : (t : Tm) -> Dec (FFI t)
  isFFIValue (True fi) = Yes True
  isFFIValue (False fi) = Yes False
  isFFIValue (If fi p t e) = No uninhabited
  isFFIValue (Var fi i x) = No uninhabited
  isFFIValue (Abs fi var ty t) = No uninhabited
  isFFIValue (App fi t1 t2) = No uninhabited
  isFFIValue (Unit fi) = No uninhabited
  isFFIValue (Seq fi t1 t2) = No uninhabited
  isFFIValue (Let fi n t b) = No uninhabited
  isFFIValue (Tuple fi n ti) = No uninhabited
  isFFIValue (Proj fi t n i) = No uninhabited
  isFFIValue (Record fi x) = No uninhabited
  isFFIValue (ProjField fi field t) = No uninhabited
  isFFIValue (Variant fi tag t ty) = No uninhabited
  isFFIValue (Case fi t alts) = No uninhabited
  isFFIValue (Fix fi t) = No uninhabited
  isFFIValue (Nil fi ty) = No uninhabited
  isFFIValue (Cons fi ty h t) = No uninhabited
  isFFIValue (IsNil fi ty t) = No uninhabited
  isFFIValue (Head fi ty t) = No uninhabited
  isFFIValue (Tail fi ty t) = No uninhabited
  isFFIValue (LitNat fi literal) = Yes LitNat
  isFFIValue (ConvertFFI fi baseType x) = No uninhabited
  isFFIValue (FFI fi x args) = No uninhabited
  isFFIValue (FFIVal fi x) = Yes FFIVal

namespace BoolValue
  public export
  data Bool : Tm -> Type where
    True  : Bool (True fi)
    False : Bool (False fi)

namespace Value

  public export
  data Value : Tm -> Type where
    Abs     : Value (Abs fi var ty t)
    True    : Bool (True fi) => Value (True fi)
    False   : Bool (False fi) => Value (False fi)
    Unit    : Value (Unit fi)
    Nil     : Value (Nil fi ty)
    Cons    : (Value h) -> (Value t)   -> Value (Cons fi ty h t)
    Tuple   : (vs : ForEach tms Value) -> Value (Tuple fi n tms)
    Record  : ForEach vs Value         -> Value (Record fi (MkRecord n fs vs u))
    Variant : Value t                  -> Value (Variant fi tag t ty)
    LitNat  : Value (LitNat fi lit)
    FFIVal  : Value (FFIVal fi val)

-- TODO: Make t 0 and port all the necessary parameters
export
Show (Value t) where
  show Abs = "Abs"
  show True = "True"
  show False = "False"
  show Unit = "Unit"
  show Nil = "Nil"
  show (Cons x y) = "Cons"
  show (Tuple vs) = "Tuple"
  show (Record x) = "Record"
  show (Variant x) = "Variant"
  show LitNat = "LitNat"
  show FFIVal = "FFIVal"

export Uninhabited (Value (If _ _ _ _))       where uninhabited _ impossible
export Uninhabited (Value (Var _ _ _))        where uninhabited _ impossible
export Uninhabited (Value (App _ _ _))        where uninhabited _ impossible
export Uninhabited (Value (Seq _ _ _))        where uninhabited _ impossible
export Uninhabited (Value (Let _ _ _ _))      where uninhabited _ impossible
export Uninhabited (Value (Proj _ _ n i))     where uninhabited _ impossible
export Uninhabited (Value (ProjField _ _ _))  where uninhabited _ impossible
export Uninhabited (Value (Case _ _ _))       where uninhabited _ impossible
export Uninhabited (Value (Fix _ _))          where uninhabited _ impossible
export Uninhabited (Value (IsNil _ _ _))      where uninhabited _ impossible
export Uninhabited (Value (Head _ _ _))       where uninhabited _ impossible
export Uninhabited (Value (Tail _ _ _))       where uninhabited _ impossible
export Uninhabited (Value (FFI _ c a))        where uninhabited _ impossible
export Uninhabited (Value (ConvertFFI _ _ _)) where uninhabited _ impossible

mutual

  ||| A term must be a value or not.
  |||
  ||| Being able to state that a Tm is a Value or not closes out the third
  ||| option where we can't decide on this property. The existence of such
  ||| property is used in the evaluation of a term which builds on it.
  ||| During the evaluation, which can be represented as a tree structure
  ||| the leafs must be end in leaf nodes.
  public export total
  isValue : (t : Tm) -> Dec (Value t)
  isValue (True fi)         = Yes True
  isValue (False fi)        = Yes False
  isValue (If fi p t e)     = No uninhabited
  isValue (Var fi i x)      = No uninhabited
  isValue (Abs fi var ty t) = Yes Abs
  isValue (App fi t1 t2)    = No uninhabited
  isValue (Unit fi)         = Yes Unit
  isValue (Seq fi t1 t2)    = No uninhabited
  isValue (Let fi n t b)    = No uninhabited
  isValue (Tuple fi n tms)  = case forEachIsValue tms of
    (Yes tmsAreValues)   => Yes (Tuple tmsAreValues)
    (No tmsAreNotValues) => No (\case (Tuple tmsValues) => tmsAreNotValues tmsValues)
  isValue (Proj fi t n i)   = No uninhabited
  isValue (Record fi (MkRecord n fields values u)) = case forEachIsValue values of
      (Yes fieldsAreValues)   => Yes (Record fieldsAreValues)
      (No fieldsAreNotValues) => No (\case (Record fieldsAsValues) => fieldsAreNotValues fieldsAsValues)
  isValue (ProjField fi field t)  = No uninhabited
  isValue (Variant fi tag t ty)   = case isValue t of
    (Yes tIsValue)    => Yes (Variant tIsValue)
    (No tIsNotValue)  => No (\case (Variant tValue) => tIsNotValue tValue)
  isValue (Case fi t alts)  = No uninhabited
  isValue (Fix fi t)        = No uninhabited
  isValue (Nil fi ty)       = Yes Nil
  isValue (Cons fi ty h t)  = case isValue h of
    (Yes hIsValue) => case isValue t of
      (Yes tIsNotValue) => Yes (Cons hIsValue tIsNotValue)
      (No tIsNotValue) => No (\case
        (Cons assumeHValue assumeTValue) => tIsNotValue assumeTValue)
    (No hIsNotValue) => No (\case
      (Cons assumeHValue assumeTValue) => hIsNotValue assumeHValue)
  isValue (IsNil fi ty t)   = No uninhabited
  isValue (Head fi ty t)    = No uninhabited
  isValue (Tail fi ty t)    = No uninhabited
  isValue (LitNat fi l)     = Yes LitNat
  isValue (FFI fi op args)  = No uninhabited
  isValue (FFIVal fi val)   = Yes FFIVal
  isValue (ConvertFFI _ _ _) = No uninhabited

  public export total
  forEachIsValue : (xs : Vect n Tm) -> Dec (ForEach xs Value)
  forEachIsValue [] = Yes []
  forEachIsValue (x :: xs) = case isValue x of
    (Yes xIsValue) => case forEachIsValue xs of
      (Yes xsAreValues) => Yes (xIsValue :: xsAreValues)
      (No xsAreNotValues) => No (\case
        (xValue :: xsValues) => xsAreNotValues xsValues)
    (No xIsNotValue) => No (\case
      (xValue :: xsValues) => xIsNotValue xValue)
