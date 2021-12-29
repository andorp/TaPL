module TaPLc.IR.Type

import Data.Vect
import Decidable.Equality

import TaPLc.IR.Record
import TaPLc.IR.Variant
import TaPLc.IR.FFI -- (FFIType)

%default total

public export
data Ty : Type where
  Bool    : Ty
  Arr     : Ty -> Ty                -> Ty
  Unit    : Ty
  Tuple   : (n : Nat) -> Vect n Ty  -> Ty
  Record  : (r : Record Ty)         -> Ty
  Variant : (v : Variant Ty)        -> Ty
  List    : Ty                      -> Ty
  LitNat  : Ty
  Base    : BaseType                -> Ty

export
funInjective : (Type.Arr x y = Type.Arr z w) -> (x = z, y = w)
funInjective Refl = (Refl, Refl)

export
tupleInjective : (Type.Tuple n xs = Type.Tuple m ys) -> (n = m, xs = ys)
tupleInjective Refl = (Refl, Refl)

export
recordInjective : (Type.Record x = Type.Record y) -> (x = y)
recordInjective Refl = Refl

export
variantInjective : (Type.Variant x = Type.Variant y) -> (x = y)
variantInjective Refl = Refl

export
listInjective : (Type.List x = Type.List y) -> (x = y)
listInjective Refl = Refl

export
baseInjective : (Type.Base x = Type.Base y) -> (x = y)
baseInjective Refl = Refl

export Uninhabited (Type.Bool = Type.Arr _ _)         where uninhabited _ impossible
export Uninhabited (Type.Bool = Type.Unit)            where uninhabited _ impossible
export Uninhabited (Type.Bool = Type.Tuple n v)       where uninhabited _ impossible
export Uninhabited (Type.Bool = Type.Record _)        where uninhabited _ impossible
export Uninhabited (Type.Bool = Type.Variant _)       where uninhabited _ impossible
export Uninhabited (Type.Bool = Type.List _)          where uninhabited _ impossible
export Uninhabited (Type.Bool = Type.LitNat)          where uninhabited _ impossible
export Uninhabited (Type.Bool = Type.Base _)          where uninhabited _ impossible

export Uninhabited (Type.Arr _ _ = Type.Bool)         where uninhabited _ impossible
export Uninhabited (Type.Arr _ _ = Type.Unit)         where uninhabited _ impossible
export Uninhabited (Type.Arr _ _ = Type.Tuple n v)    where uninhabited _ impossible
export Uninhabited (Type.Arr _ _ = Type.Record _)     where uninhabited _ impossible
export Uninhabited (Type.Arr _ _ = Type.Variant _)    where uninhabited _ impossible
export Uninhabited (Type.Arr _ _ = Type.List _)       where uninhabited _ impossible
export Uninhabited (Type.Arr _ _ = Type.LitNat)       where uninhabited _ impossible
export Uninhabited (Type.Arr _ _ = Type.Base _)       where uninhabited _ impossible

export Uninhabited (Type.Unit = Type.Bool)            where uninhabited _ impossible
export Uninhabited (Type.Unit = Type.Arr _ _)         where uninhabited _ impossible
export Uninhabited (Type.Unit = Type.Tuple n v)       where uninhabited _ impossible
export Uninhabited (Type.Unit = Type.Record _)        where uninhabited _ impossible
export Uninhabited (Type.Unit = Type.Variant _)       where uninhabited _ impossible
export Uninhabited (Type.Unit = Type.List _)          where uninhabited _ impossible
export Uninhabited (Type.Unit = Type.LitNat)          where uninhabited _ impossible
export Uninhabited (Type.Unit = Type.Base _)          where uninhabited _ impossible

export Uninhabited (Type.Tuple n v = Bool)            where uninhabited _ impossible
export Uninhabited (Type.Tuple n v = Arr _ _)         where uninhabited _ impossible
export Uninhabited (Type.Tuple n v = Unit)            where uninhabited _ impossible
export Uninhabited (Type.Tuple n v = Record _)        where uninhabited _ impossible
export Uninhabited (Type.Tuple n v = Variant _)       where uninhabited _ impossible
export Uninhabited (Type.Tuple n v = List _)          where uninhabited _ impossible
export Uninhabited (Type.Tuple n v = Type.LitNat)     where uninhabited _ impossible
export Uninhabited (Type.Tuple n v = Type.Base _)     where uninhabited _ impossible

export Uninhabited (Type.Record _ = Bool)             where uninhabited _ impossible
export Uninhabited (Type.Record _ = Arr _ _)          where uninhabited _ impossible
export Uninhabited (Type.Record _ = Unit)             where uninhabited _ impossible
export Uninhabited (Type.Record _ = Tuple n v)        where uninhabited _ impossible
export Uninhabited (Type.Record _ = Variant _)        where uninhabited _ impossible
export Uninhabited (Type.Record _ = List _)           where uninhabited _ impossible
export Uninhabited (Type.Record _ = Type.LitNat)      where uninhabited _ impossible
export Uninhabited (Type.Record _ = Type.Base _)      where uninhabited _ impossible

export Uninhabited (Type.Variant _ = Type.Bool)       where uninhabited _ impossible
export Uninhabited (Type.Variant _ = Type.Arr _ _)    where uninhabited _ impossible
export Uninhabited (Type.Variant _ = Type.Unit)       where uninhabited _ impossible
export Uninhabited (Type.Variant _ = Type.Tuple n v)  where uninhabited _ impossible
export Uninhabited (Type.Variant _ = Type.Record _)   where uninhabited _ impossible
export Uninhabited (Type.Variant _ = Type.List _)     where uninhabited _ impossible
export Uninhabited (Type.Variant _ = Type.LitNat)     where uninhabited _ impossible
export Uninhabited (Type.Variant _ = Type.Base _)     where uninhabited _ impossible

export Uninhabited (Type.List _ = Type.Bool)          where uninhabited _ impossible
export Uninhabited (Type.List _ = Type.Arr _ _)       where uninhabited _ impossible
export Uninhabited (Type.List _ = Type.Unit)          where uninhabited _ impossible
export Uninhabited (Type.List _ = Type.Tuple n v)     where uninhabited _ impossible
export Uninhabited (Type.List _ = Type.Record _)      where uninhabited _ impossible
export Uninhabited (Type.List _ = Type.Variant _)     where uninhabited _ impossible
export Uninhabited (Type.List _ = Type.LitNat)        where uninhabited _ impossible
export Uninhabited (Type.List _ = Type.Base _)        where uninhabited _ impossible

export Uninhabited (Type.LitNat = Type.Bool)          where uninhabited _ impossible
export Uninhabited (Type.LitNat = Type.Arr _ _)       where uninhabited _ impossible
export Uninhabited (Type.LitNat = Type.Unit)          where uninhabited _ impossible
export Uninhabited (Type.LitNat = Type.Tuple n v)     where uninhabited _ impossible
export Uninhabited (Type.LitNat = Type.Record _)      where uninhabited _ impossible
export Uninhabited (Type.LitNat = Type.Variant _)     where uninhabited _ impossible
export Uninhabited (Type.LitNat = Type.List _)        where uninhabited _ impossible
export Uninhabited (Type.LitNat = Type.Base _)        where uninhabited _ impossible

export Uninhabited (Type.Base _ = Type.Bool)          where uninhabited _ impossible
export Uninhabited (Type.Base _ = Type.Arr _ _)       where uninhabited _ impossible
export Uninhabited (Type.Base _ = Type.Unit)          where uninhabited _ impossible
export Uninhabited (Type.Base _ = Type.Tuple n v)     where uninhabited _ impossible
export Uninhabited (Type.Base _ = Type.Record _)      where uninhabited _ impossible
export Uninhabited (Type.Base _ = Type.Variant _)     where uninhabited _ impossible
export Uninhabited (Type.Base _ = Type.List _)        where uninhabited _ impossible
export Uninhabited (Type.Base _ = Type.LitNat)        where uninhabited _ impossible

public export
DecEq Ty where
  decEq Bool Bool = Yes Refl
  decEq Bool (Arr x y)      = No uninhabited
  decEq Bool Unit           = No uninhabited
  decEq Bool (Tuple n xs)   = No uninhabited
  decEq Bool (Record r)     = No uninhabited
  decEq Bool (Variant v)    = No uninhabited
  decEq Bool (List x)       = No uninhabited
  decEq Bool LitNat         = No uninhabited
  decEq Bool (Base y)       = No uninhabited

  decEq (Arr _ _) Bool      = No uninhabited
  decEq (Arr x y) (Arr z w) = case decEq x z of
    (Yes Refl) => case decEq y w of
      (Yes Refl      ) => Yes Refl 
      (No  y_is_not_w) => No (\assumeArrOk => (y_is_not_w (snd (funInjective assumeArrOk))))
    (No x_is_not_z) => No (\assumeArrOk => (x_is_not_z (fst (funInjective assumeArrOk))))
  decEq (Arr _ _) Unit          = No uninhabited
  decEq (Arr _ _) (Tuple n xs)  = No uninhabited
  decEq (Arr _ _) (Record _)    = No uninhabited
  decEq (Arr _ _) (Variant _)   = No uninhabited
  decEq (Arr _ _) (List _)      = No uninhabited
  decEq (Arr _ _) LitNat        = No uninhabited
  decEq (Arr _ _) (Base _)      = No uninhabited

  decEq Unit Bool           = No uninhabited
  decEq Unit (Arr x y)      = No uninhabited
  decEq Unit Unit           = Yes Refl
  decEq Unit (Tuple n xs)   = No uninhabited
  decEq Unit (Record r)     = No uninhabited
  decEq Unit (Variant v)    = No uninhabited
  decEq Unit (List x)       = No uninhabited
  decEq Unit LitNat         = No uninhabited
  decEq Unit (Base y)       = No uninhabited

  decEq (Tuple n xs) Bool          = No uninhabited
  decEq (Tuple n xs) (Arr x y)     = No uninhabited
  decEq (Tuple n xs) Unit          = No uninhabited
  decEq (Tuple n xs) (Tuple k ys) = case decEq n k of
    (Yes Refl) => case assert_total (decEq xs ys) of
      (Yes Refl)         => Yes Refl
      (No  xs_is_not_ys) => No (\assumeTupleOK => xs_is_not_ys (snd (tupleInjective assumeTupleOK)))
    (No n_is_not_k)      => No (\assumeTupleOK => n_is_not_k (fst (tupleInjective assumeTupleOK)))
  decEq (Tuple n xs) (Record r)   = No uninhabited
  decEq (Tuple n xs) (Variant v)  = No uninhabited
  decEq (Tuple n xs) (List x)     = No uninhabited
  decEq (Tuple n xs) LitNat       = No uninhabited
  decEq (Tuple n xs) (Base y)     = No uninhabited

  decEq (Record r) Bool           = No uninhabited
  decEq (Record r) (Arr x y)      = No uninhabited
  decEq (Record r) Unit           = No uninhabited
  decEq (Record r) (Tuple n xs)   = No uninhabited
  decEq (Record r) (Record x) = case assert_total (decEq r x) of
    (Yes Refl      ) => Yes Refl
    (No  r_is_not_x) => No (\assumeRecordOK => r_is_not_x (recordInjective assumeRecordOK))
  decEq (Record r) (Variant v)    = No uninhabited
  decEq (Record r) (List x)       = No uninhabited
  decEq (Record r) LitNat         = No uninhabited
  decEq (Record r) (Base y)       = No uninhabited

  decEq (Variant v) Bool          = No uninhabited
  decEq (Variant v) (Arr x y)     = No uninhabited
  decEq (Variant v) Unit          = No uninhabited
  decEq (Variant v) (Tuple n xs)  = No uninhabited
  decEq (Variant v) (Record r)    = No uninhabited
  decEq (Variant v) (Variant x) = case assert_total (decEq v x) of
    (Yes Refl      ) => Yes Refl
    (No  v_is_not_x) => No (\assumeVariantOk => v_is_not_x (variantInjective assumeVariantOk))
  decEq (Variant v) (List x)      = No uninhabited
  decEq (Variant v) LitNat        = No uninhabited
  decEq (Variant v) (Base y)      = No uninhabited

  decEq (List x) Bool           = No uninhabited
  decEq (List x) (Arr y z)      = No uninhabited
  decEq (List x) Unit           = No uninhabited
  decEq (List x) (Tuple n xs)   = No uninhabited
  decEq (List x) (Record r)     = No uninhabited
  decEq (List x) (Variant v)    = No uninhabited
  decEq (List x) (List y) = case decEq x y of
    (Yes Refl      ) => Yes Refl
    (No  x_is_not_y) => No (\assumeListOk => x_is_not_y (listInjective assumeListOk))
  decEq (List x) LitNat         = No uninhabited
  decEq (List x) (Base y)       = No uninhabited

  decEq LitNat Bool         = No uninhabited
  decEq LitNat (Arr _ _)    = No uninhabited
  decEq LitNat Unit         = No uninhabited
  decEq LitNat (Tuple n v)  = No uninhabited
  decEq LitNat (Record _)   = No uninhabited
  decEq LitNat (Variant _)  = No uninhabited
  decEq LitNat (List _)     = No uninhabited
  decEq LitNat LitNat       = Yes Refl
  decEq LitNat (Base _)     = No uninhabited

  decEq (Base _) Bool         = No uninhabited
  decEq (Base _) (Arr _ _)    = No uninhabited
  decEq (Base _) Unit         = No uninhabited
  decEq (Base _) (Tuple n v)  = No uninhabited
  decEq (Base _) (Record _)   = No uninhabited
  decEq (Base _) (Variant _)  = No uninhabited
  decEq (Base _) (List _)     = No uninhabited
  decEq (Base _) LitNat       = No uninhabited
  decEq (Base x) (Base y) = case decEq x y of
    Yes Refl => Yes Refl
    No xIsNotY => No (\assumeBaseOK => xIsNotY (baseInjective assumeBaseOK))
  