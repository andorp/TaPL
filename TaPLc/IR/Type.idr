module TaPLc.IR.Type

import Data.Vect
import Decidable.Equality

import TaPLc.IR.Record
import TaPLc.IR.Variant


public export
data Ty : Type where
  Bool    : Ty
  Arr     : Ty -> Ty                -> Ty
  Base    : String                  -> Ty
  Unit    : Ty
  Product : Ty -> Ty                -> Ty
  Tuple   : (n : Nat) -> Vect n Ty  -> Ty
  Record  : (r : Record Ty)         -> Ty
  Variant : (v : Variant Ty)        -> Ty
  List    : Ty                      -> Ty

export
funInjective : (Type.Arr x y = Type.Arr z w) -> (x = z, y = w)
funInjective Refl = (Refl, Refl)

export
baseInjective : (Type.Base x = Type.Base y) -> x = y
baseInjective Refl = Refl

export
productInjective : (Type.Product x y = Type.Product z w) -> (x = z, y = w)
productInjective Refl = (Refl, Refl)

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

export Uninhabited (Type.Bool = Type.Arr _ _)           where uninhabited _ impossible
export Uninhabited (Type.Bool = Type.Base _)            where uninhabited _ impossible
export Uninhabited (Type.Bool = Type.Unit)              where uninhabited _ impossible
export Uninhabited (Type.Bool = Type.Product _ _)       where uninhabited _ impossible
export Uninhabited (Type.Bool = Type.Tuple n v)         where uninhabited _ impossible
export Uninhabited (Type.Bool = Type.Record _)          where uninhabited _ impossible
export Uninhabited (Type.Bool = Type.Variant _)         where uninhabited _ impossible
export Uninhabited (Type.Bool = Type.List _)            where uninhabited _ impossible

export Uninhabited (Type.Arr _ _ = Type.Bool)           where uninhabited _ impossible
export Uninhabited (Type.Arr _ _ = Type.Base _)         where uninhabited _ impossible
export Uninhabited (Type.Arr _ _ = Type.Unit)           where uninhabited _ impossible
export Uninhabited (Type.Arr _ _ = Type.Product _ _)    where uninhabited _ impossible
export Uninhabited (Type.Arr _ _ = Type.Tuple n v)      where uninhabited _ impossible
export Uninhabited (Type.Arr _ _ = Type.Record _)       where uninhabited _ impossible
export Uninhabited (Type.Arr _ _ = Type.Variant _)      where uninhabited _ impossible
export Uninhabited (Type.Arr _ _ = Type.List _)         where uninhabited _ impossible

export Uninhabited (Type.Base _ = Type.Bool)            where uninhabited _ impossible
export Uninhabited (Type.Base _ = Type.Arr _ _)         where uninhabited _ impossible
export Uninhabited (Type.Base _ = Type.Unit)            where uninhabited _ impossible
export Uninhabited (Type.Base _ = Type.Product _ _)     where uninhabited _ impossible
export Uninhabited (Type.Base _ = Type.Tuple n v)       where uninhabited _ impossible
export Uninhabited (Type.Base _ = Type.Record _)        where uninhabited _ impossible
export Uninhabited (Type.Base _ = Type.Variant _)       where uninhabited _ impossible
export Uninhabited (Type.Base _ = Type.List _)          where uninhabited _ impossible

export Uninhabited (Type.Unit = Type.Bool)              where uninhabited _ impossible
export Uninhabited (Type.Unit = Type.Arr _ _)           where uninhabited _ impossible
export Uninhabited (Type.Unit = Type.Base _)            where uninhabited _ impossible
export Uninhabited (Type.Unit = Type.Product _ _)       where uninhabited _ impossible
export Uninhabited (Type.Unit = Type.Tuple n v)         where uninhabited _ impossible
export Uninhabited (Type.Unit = Type.Record _)          where uninhabited _ impossible
export Uninhabited (Type.Unit = Type.Variant _)         where uninhabited _ impossible
export Uninhabited (Type.Unit = Type.List _)            where uninhabited _ impossible

export Uninhabited (Type.Product _ _ = Bool)          where uninhabited _ impossible
export Uninhabited (Type.Product _ _ = Arr _ _)       where uninhabited _ impossible
export Uninhabited (Type.Product _ _ = Base _)        where uninhabited _ impossible
export Uninhabited (Type.Product _ _ = Unit)          where uninhabited _ impossible
export Uninhabited (Type.Product _ _ = Tuple n v)     where uninhabited _ impossible
export Uninhabited (Type.Product _ _ = Record _)      where uninhabited _ impossible
export Uninhabited (Type.Product _ _ = Variant _)     where uninhabited _ impossible
export Uninhabited (Type.Product _ _ = List _)        where uninhabited _ impossible

export Uninhabited (Type.Tuple n v = Bool)            where uninhabited _ impossible
export Uninhabited (Type.Tuple n v = Arr _ _)         where uninhabited _ impossible
export Uninhabited (Type.Tuple n v = Base _)          where uninhabited _ impossible
export Uninhabited (Type.Tuple n v = Unit)            where uninhabited _ impossible
export Uninhabited (Type.Tuple n v = Product _ _)     where uninhabited _ impossible
export Uninhabited (Type.Tuple n v = Record _)        where uninhabited _ impossible
export Uninhabited (Type.Tuple n v = Variant _)       where uninhabited _ impossible
export Uninhabited (Type.Tuple n v = List _)          where uninhabited _ impossible

export Uninhabited (Type.Record _ = Bool)             where uninhabited _ impossible
export Uninhabited (Type.Record _ = Arr _ _)          where uninhabited _ impossible
export Uninhabited (Type.Record _ = Base _)           where uninhabited _ impossible
export Uninhabited (Type.Record _ = Unit)             where uninhabited _ impossible
export Uninhabited (Type.Record _ = Product _ _)      where uninhabited _ impossible
export Uninhabited (Type.Record _ = Tuple n v)        where uninhabited _ impossible
export Uninhabited (Type.Record _ = Variant _)        where uninhabited _ impossible
export Uninhabited (Type.Record _ = List _)           where uninhabited _ impossible

export Uninhabited (Type.Variant _ = Type.Bool)         where uninhabited _ impossible
export Uninhabited (Type.Variant _ = Type.Arr _ _)      where uninhabited _ impossible
export Uninhabited (Type.Variant _ = Type.Base _)       where uninhabited _ impossible
export Uninhabited (Type.Variant _ = Type.Unit)         where uninhabited _ impossible
export Uninhabited (Type.Variant _ = Type.Product _ _)  where uninhabited _ impossible
export Uninhabited (Type.Variant _ = Type.Tuple n v)    where uninhabited _ impossible
export Uninhabited (Type.Variant _ = Type.Record _)     where uninhabited _ impossible
export Uninhabited (Type.Variant _ = Type.List _)       where uninhabited _ impossible

export Uninhabited (Type.List _ = Type.Bool)            where uninhabited _ impossible
export Uninhabited (Type.List _ = Type.Arr _ _)         where uninhabited _ impossible
export Uninhabited (Type.List _ = Type.Base _)          where uninhabited _ impossible
export Uninhabited (Type.List _ = Type.Unit)            where uninhabited _ impossible
export Uninhabited (Type.List _ = Type.Product _ _)     where uninhabited _ impossible
export Uninhabited (Type.List _ = Type.Tuple n v)       where uninhabited _ impossible
export Uninhabited (Type.List _ = Type.Record _)        where uninhabited _ impossible
export Uninhabited (Type.List _ = Type.Variant _)       where uninhabited _ impossible

public export
DecEq Ty where
  decEq Bool Bool = Yes Refl
  decEq Bool (Arr x y)      = No uninhabited
  decEq Bool (Base x)       = No uninhabited
  decEq Bool Unit           = No uninhabited
  decEq Bool (Product x y)  = No uninhabited
  decEq Bool (Tuple n xs)   = No uninhabited
  decEq Bool (Record r)     = No uninhabited
  decEq Bool (Variant v)    = No uninhabited
  decEq Bool (List x)       = No uninhabited

  decEq (Arr x y) Bool      = No uninhabited
  decEq (Arr x y) (Arr z w) = case decEq x z of
    (Yes Refl) => case decEq y w of
      (Yes Refl      ) => Yes Refl 
      (No  y_is_not_w) => No (\assumeArrOk => (y_is_not_w (snd (funInjective assumeArrOk))))
    (No x_is_not_z) => No (\assumeArrOk => (x_is_not_z (fst (funInjective assumeArrOk))))
  decEq (Arr x y) (Base z)      = No uninhabited
  decEq (Arr x y) Unit          = No uninhabited
  decEq (Arr x y) (Product z w) = No uninhabited
  decEq (Arr x y) (Tuple n xs)  = No uninhabited
  decEq (Arr x y) (Record r)    = No uninhabited
  decEq (Arr x y) (Variant v)   = No uninhabited
  decEq (Arr x y) (List z)      = No uninhabited

  decEq (Base x) Bool       = No uninhabited
  decEq (Base x) (Arr y z)  = No uninhabited
  decEq (Base x) (Base y) = case decEq x y of
    (Yes Refl       ) => Yes Refl
    (No  x_is_not_y ) => No (\assumeBaseOk => x_is_not_y (baseInjective assumeBaseOk))
  decEq (Base x) Unit           = No uninhabited
  decEq (Base x) (Product y z)  = No uninhabited
  decEq (Base x) (Tuple n xs)   = No uninhabited
  decEq (Base x) (Record r)     = No uninhabited
  decEq (Base x) (Variant v)    = No uninhabited
  decEq (Base x) (List y)       = No uninhabited

  decEq Unit Bool           = No uninhabited
  decEq Unit (Arr x y)      = No uninhabited
  decEq Unit (Base x)       = No uninhabited
  decEq Unit Unit           = Yes Refl
  decEq Unit (Product x y)  = No uninhabited
  decEq Unit (Tuple n xs)   = No uninhabited
  decEq Unit (Record r)     = No uninhabited
  decEq Unit (Variant v)    = No uninhabited
  decEq Unit (List x)       = No uninhabited

  decEq (Product x y) Bool      = No uninhabited
  decEq (Product x y) (Arr z w) = No uninhabited
  decEq (Product x y) (Base z)  = No uninhabited
  decEq (Product x y) Unit      = No uninhabited
  decEq (Product x y) (Product z w) = case decEq x z of
    (Yes Refl) => case decEq y w of
      (Yes Refl      ) => Yes Refl
      (No  y_is_not_w) => No (\assumeProductOK => y_is_not_w (snd (productInjective assumeProductOK)))
    (No x_is_not_z) => No (\assumeProductOK => x_is_not_z (fst (productInjective assumeProductOK)))
  decEq (Product x y) (Tuple n xs)  = No uninhabited
  decEq (Product x y) (Record r)    = No uninhabited
  decEq (Product x y) (Variant v)   = No uninhabited
  decEq (Product x y) (List z)      = No uninhabited

  decEq (Tuple n xs) Bool          = No uninhabited
  decEq (Tuple n xs) (Arr x y)     = No uninhabited
  decEq (Tuple n xs) (Base x)      = No uninhabited
  decEq (Tuple n xs) Unit          = No uninhabited
  decEq (Tuple n xs) (Product x y) = No uninhabited
  decEq (Tuple n xs) (Tuple k ys) = case decEq n k of
    (Yes Refl) => case decEq xs ys of
      (Yes Refl)         => Yes Refl
      (No  xs_is_not_ys) => No (\assumeTupleOK => xs_is_not_ys (snd (tupleInjective assumeTupleOK)))
    (No n_is_not_k)      => No (\assumeTupleOK => n_is_not_k (fst (tupleInjective assumeTupleOK)))
  decEq (Tuple n xs) (Record r)   = No uninhabited
  decEq (Tuple n xs) (Variant v)  = No uninhabited
  decEq (Tuple n xs) (List x)     = No uninhabited

  decEq (Record r) Bool           = No uninhabited
  decEq (Record r) (Arr x y)      = No uninhabited
  decEq (Record r) (Base x)       = No uninhabited
  decEq (Record r) Unit           = No uninhabited
  decEq (Record r) (Product x y)  = No uninhabited
  decEq (Record r) (Tuple n xs)   = No uninhabited
  decEq (Record r) (Record x) = case decEq r x of
    (Yes Refl      ) => Yes Refl
    (No  r_is_not_x) => No (\assumeRecordOK => r_is_not_x (recordInjective assumeRecordOK))
  decEq (Record r) (Variant v)    = No uninhabited
  decEq (Record r) (List x)       = No uninhabited

  decEq (Variant v) Bool          = No uninhabited
  decEq (Variant v) (Arr x y)     = No uninhabited
  decEq (Variant v) (Base x)      = No uninhabited
  decEq (Variant v) Unit          = No uninhabited
  decEq (Variant v) (Product x y) = No uninhabited
  decEq (Variant v) (Tuple n xs)  = No uninhabited
  decEq (Variant v) (Record r)    = No uninhabited
  decEq (Variant v) (Variant x) = case decEq v x of
    (Yes Refl      ) => Yes Refl
    (No  v_is_not_x) => No (\assumeVariantOk => v_is_not_x (variantInjective assumeVariantOk))
  decEq (Variant v) (List x)      = No uninhabited

  decEq (List x) Bool           = No uninhabited
  decEq (List x) (Arr y z)      = No uninhabited
  decEq (List x) (Base y)       = No uninhabited
  decEq (List x) Unit           = No uninhabited
  decEq (List x) (Product y z)  = No uninhabited
  decEq (List x) (Tuple n xs)   = No uninhabited
  decEq (List x) (Record r)     = No uninhabited
  decEq (List x) (Variant v)    = No uninhabited
  decEq (List x) (List y) = case decEq x y of
    (Yes Refl      ) => Yes Refl
    (No  x_is_not_y) => No (\assumeListOk => x_is_not_y (listInjective assumeListOk))
