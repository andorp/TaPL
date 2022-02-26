module TaPLc.IR.WellTypedTerm

import TaPLc.IR.Record
import TaPLc.IR.Variant
import TaPLc.IR.Name
import TaPLc.IR.Info
import TaPLc.IR.Type
import TaPLc.Data.Vect
import TaPLc.IR.FFI
import Data.Vect
import Data.Vect.Quantifiers


public export
data Context : a -> Type where
  Lin  : Context a
  (:<) : Context a -> a -> Context a

public export
data In : Context a -> a -> Type where
  Here  : In (ctx :< a) a
  There : In ctx a -> In (ctx :< b) a

Functor Context where
  map f Lin = Lin
  map f (cx :< x) = map f cx :< f x

namespace Record

  public export
  data RecordField : String -> Vect n String -> Type where
    Here  : RecordField f (f :: fs)
    There : RecordField f fs -> RecordField f (g :: fs)

  public export
  asFin : {n : Nat} -> {f : String} -> {fs : Vect n String} -> RecordField f fs -> Fin n
  asFin Here      = FZ
  asFin (There x) = FS (asFin x)

  public export
  lookup : {f : String} -> (r : Record a) -> RecordField f r.fields -> a
  lookup r f = Vect.index (asFin f) r.values

  public export
  finIdx : {f : String} -> (r : Record a) -> RecordField f r.fields -> Fin r.size
  finIdx r g = asFin g

namespace Variant

  public export
  data VariantTag : String -> Vect n String -> Type where
    Here  : VariantTag t (t :: ts)
    There : VariantTag t ts -> VariantTag t (z :: ts)

  public export
  asFin : {n : Nat} -> {t : String} -> {ts : Vect n String} -> VariantTag t ts -> Fin n
  asFin Here = FZ
  asFin (There x) = FS (asFin x)

  public export
  lookup : {t : String} -> (v : Variant a) -> VariantTag t v.tags -> a
  lookup v g = Vect.index (asFin g) v.info

  public export
  finIdx : {t : String} -> (v : Variant a) -> VariantTag t v.tags -> Fin v.size
  finIdx v g = asFin g

namespace FFI

  public export
  data FFI : BaseType -> Ty -> Type where
    Bool : FFI "Builtin.Bool" Bool
    Nat  : FFI "Builtin.Nat"  LitNat
    Base : {tyName : BaseType} -> FFI tyName (Base tyName)

  export Uninhabited (FFI _ (Arr _ _))    where uninhabited _ impossible
  export Uninhabited (FFI _ Unit     )    where uninhabited _ impossible
  export Uninhabited (FFI _ (Tuple n x))  where uninhabited _ impossible
  export Uninhabited (FFI _ (Record _))   where uninhabited _ impossible
  export Uninhabited (FFI _ (Variant _))  where uninhabited _ impossible
  export Uninhabited (FFI _ (List _))     where uninhabited _ impossible

public export
data Tm : Context Ty -> Ty -> Type where

  True : (fi : Info) ->
    {ctx : Context Ty} ->
    ---------------------
         Tm ctx Bool
  
  False : (fi : Info) -> 
    {ctx : Context Ty} ->
    ---------------------
         Tm ctx Bool

  If : (fi : Info) ->
                       {ctx : Context Ty}                   ->
    (p : Tm ctx Bool) -> (t : Tm ctx ty) -> (e : Tm ctx ty) ->
    ----------------------------------------------------------
                          Tm ctx ty

  Var : (fi : Info) ->
     {ctx : Context Ty} ->
          {ty : Ty}     -> 
       (k : In ctx ty)  ->
     ---------------------
           Tm ctx ty

  Abs : (fi : Info) -> 
        {ctx : Context Ty}     ->
            {ty2 : Ty}         ->
    (var : Name) -> (ty1 : Ty) ->
     (t : Tm (ctx :< ty1) ty2) ->
    -----------------------------
        Tm ctx (Arr ty1 ty2)

  App : (fi : Info) ->
                    {ctx : Context Ty}               ->
                     {ty1, ty2 : Ty}                 ->
    (t1 : Tm ctx (Arr ty1 ty2)) -> (t2 : Tm ctx ty1) ->
    ---------------------------------------------------
                        Tm ctx ty2

  Unit : (fi : Info) -> 
    {ctx : Context Ty} ->
    ---------------------
         Tm ctx Unit

  Seq : (fi : Info) ->
                {ctx : Context Ty}         ->
    (t1 : Tm ctx Unit) -> (t2 : Tm ctx ty) ->
    -----------------------------------------
                    Tm ctx ty

  Let : (fi : Info) ->
                      {ctx : Context Ty}                        ->
                        {ty1, ty2 : Ty}                         ->
    (n : Name) -> (t : Tm ctx ty1) -> (b : Tm (ctx :< ty1) ty2) ->
    --------------------------------------------------------------
                          Tm ctx ty2
  
  -- TODO: Add Tuple datatype, similar to records
  Tuple : (fi : Info) ->
    {ctx : Context Ty}  -> 
         (n : Nat)      ->
     (tys : Vect n Ty)  ->
      All (Tm ctx) tys  ->
    ----------------------
     Tm ctx (Tuple n tys)

  Proj : (fi : Info) ->
         {ctx : Context Ty}    ->
      (n : Nat) -> (i : Fin n) ->
          {tys : Vect n Ty}    ->
    (t : Tm ctx (Tuple n tys)) ->
    -----------------------------
         Tm ctx (index i tys)

  Record : (fi : Info) ->
      {ctx : Context Ty}   ->
    (r : Record.Record Ty) ->
    All (Tm ctx) r.values  ->
    -------------------------
      Tm ctx (Type.Record r)

  ProjField : (fi : Info) ->
           {ctx : Context Ty}        ->
            {r : Record Ty}          ->
             (field : String)        ->
    (f : RecordField field r.fields) ->
       (t : Tm ctx (Type.Record r))  ->
    -----------------------------------
            Tm ctx (lookup r f)

  Variant : (fi : Info) ->
          {ctx : Context Ty}    ->
            (tag : String)      ->
           (v : Variant Ty)     ->
    (f : VariantTag tag v.tags) ->
          Tm ctx (lookup v f)   ->
    ------------------------------
        Tm ctx (Type.Variant v)

  Case : (fi : Info) ->
             {ctx : Context Ty}           ->
                 {ty : Ty}                ->
              (v : Variant Ty)            ->
           (s : Tm ctx (Variant v))       ->
    (All (\t => Tm (ctx :< t) ty) v.info) ->
    ----------------------------------------
                    Tm ctx ty

  Fix : (fi : Info) ->
    {ctx : Context Ty} ->
    Tm ctx (Arr ty ty) ->
    ---------------------
    Tm ctx ty

  Nil : (fi : Info) ->
    {ctx : Context Ty} ->
         (ty : Ty)     ->
    ---------------------
       Tm ctx (List ty)

  Cons : (fi : Info) ->
           {ctx : Context Ty}     ->
               (ty : Ty)          ->
    Tm ctx ty -> Tm ctx (List ty) ->
    --------------------------------
            Tm ctx (List ty)
  
  IsNil : (fi : Info) ->
    {ctx : Context Ty} ->
         (ty : Ty)     ->
      Tm ctx (List ty) ->
    ---------------------
         Tm ctx Bool

  Head : (fi : Info) ->
    {ctx : Context Ty} ->
         (ty : Ty)     ->
      Tm ctx (List ty) ->
    ---------------------
          Tm ctx ty

  Tail : (fi : Info) ->
    {ctx : Context Ty} ->
          (ty : Ty)    ->
      Tm ctx (List ty) ->
    ---------------------
       Tm ctx (List ty)

  LitNat : (fi : Info) ->
    {ctx : Context Ty} ->
      (literal : Nat)  ->
    ---------------------
        Tm ctx LitNat

  ConvertFFI : (fi : Info) ->
      {ctx : Context Ty}  ->
           {ty : Ty}      ->
    (baseType : BaseType) ->
       (FFI baseType ty)  ->
           Tm ctx ty      ->
    ------------------------
     Tm ctx (Base baseType)

  FFI : (fi : Info) ->
              (f : FFICall2)         ->
    All (Tm ctx) (map Base f.argsTy) ->
    -----------------------------------
          Tm ctx (Base f.retTy)

  FFIVal : (fi : Info) ->
     {ctx : Context Ty} ->
      FFIVal baseType   ->
    ----------------------
    Tm ctx (Base baseType)

namespace Value

  public export
  data Value : Tm ctx ty -> Type where
    Abs     : Value (Abs fi var ty t)
    True    : Value (True fi)
    False   : Value (False fi)
    Unit    : Value (Unit fi)
    Nil     : Value (Nil fi ty)
    Cons    : (Value h) -> (Value t)   -> Value (Cons fi ty h t)
    Tuple   : {- (vs : App Value ) -> -} Value (Tuple fi n tys tms)
    Record  : {- ForEach vs Value -> -} Value (Record fi r tms)
    Variant : Value t                  -> Value (Variant fi tag v fld t)
    LitNat  : Value (LitNat fi lit)
    FFIVal  : Value (FFIVal fi val)
