module TaPLc.IR.Term

import Data.Vect

import TaPLc.IR.Type
import TaPLc.IR.Record
import TaPLc.IR.Variant
import TaPLc.IR.Name
import TaPLc.IR.Info
import TaPLc.Data.Vect

%default total

public export
data Tm : Type where
  True  : (fi : Info)                                               -> Tm
  False : (fi : Info)                                               -> Tm
  If    : (fi : Info) -> (p,t,e : Tm)                               -> Tm
  Var   : (fi : Info) -> (i : Nat)                                  -> Tm 
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

namespace Value

  public export
  data Value : Tm -> Type where
    Abs     : Value (Abs fi var ty t)
    True    : Value (True fi)
    False   : Value (False fi)
    Unit    : Value (Unit fi)
    Nil     : Value (Nil fi ty)
    Cons    : (Value h) -> (Value t) -> Value (Cons fi ty h t)
    Tuple   : {n : Nat} -> {0 tms : Vect n Tm} -> (vs : ForEach tms Value) -> Value (Tuple fi n tms) -- TODO: Remove fields?
    Record  : ForEach vs Value -> Value (Record fi (MkRecord n fs vs u))
    Variant : Value t          -> Value (Variant fi tag t ty)

export Uninhabited (Value (If _ _ _ _))       where uninhabited _ impossible
export Uninhabited (Value (Var _ _))          where uninhabited _ impossible
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
  isValue (Var fi i)        = No uninhabited
  isValue (Abs fi var ty t) = Yes Abs
  isValue (App fi t1 t2)    = No uninhabited
  isValue (Unit fi)         = Yes Unit
  isValue (Seq fi t1 t2)    = No uninhabited
  isValue (Let fi n t b)    = No uninhabited
  isValue (Tuple fi n tms)  = case forEachIsValue tms of
    (Yes tmsAreValues)   => Yes (Tuple tmsAreValues)
    (No tmsAreNotValues) => No (\case (Tuple tmsValues) => tmsAreNotValues tmsValues)
  isValue (Proj fi t n i)   = No uninhabited
  isValue (Record fi (MkRecord n fields values u)) = case (assert_total (forEachIsValue values)) of
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
