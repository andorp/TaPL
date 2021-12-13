module TaPLc.IR.Term

import Data.Vect

import TaPLc.IR.Type
import TaPLc.IR.Record
import TaPLc.IR.Variant
import TaPLc.IR.Name
import TaPLc.IR.Info
import TaPLc.Data.Vect

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
  As    : (fi : Info) -> (t : Tm) -> (ty : Ty)                      -> Tm
  Let   : (fi : Info) -> (n : Name) -> (t : Tm) -> (b : Tm)         -> Tm
  
  Pair  : (fi : Info) -> (p1,p2 : Tm)                               -> Tm
  First  : (fi : Info) -> (t : Tm)                                  -> Tm
  Second : (fi : Info) -> (t : Tm)                                  -> Tm

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
    Cons    : Value (Cons fi ty h t)
    Pair    : Value v1 -> Value v2                                -> Value (Pair fi v1 v2)
    Tuple   : {n : Nat} -> {tms : Vect n Tm} -> ForEach tms Value -> Value (Tuple fi n tms)
    Record  : (r : Record Tm) -> ForEach r.values Value           -> Value (Record fi r)
