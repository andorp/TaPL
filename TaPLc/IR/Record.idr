module TaPLc.IR.Record

import Data.Vect
import Decidable.Equality

import public TaPLc.IR.UniqueNames

%default total

public export
record Record (a : Type) where
  constructor MkRecord
  size          : Nat
  fields        : Vect size String
  values        : Vect size a
  uniqueFields  : UniqueNames size fields

export
Functor Record where
  map f r = record { values $= map f } r

export
recordInjective
  :  {r,s : Record a} -> (r = s)
  -> (r.size = s.size, r.fields ~=~ s.fields, r.values ~=~ s.values, r.uniqueFields ~=~ s.uniqueFields)
recordInjective Refl = (Refl, Refl, Refl, Refl)

export
DecEq a => DecEq (Record a) where
  decEq (MkRecord s1 f1 v1 u1) (MkRecord s2 f2 v2 u2) = case decEq s1 s2 of
    (Yes Refl) => case decEq f1 f2 of
      (Yes Refl) => case decEq v1 v2 of
        (Yes Refl) => case decEq u1 u2 of
          (Yes Refl)        => Yes Refl
          (No u1_is_not_u2) => No (\assumeRecordOK => u1_is_not_u2 ((snd . snd . snd) (recordInjective assumeRecordOK)))
        (No v1_is_not_v2) => No (\assumeRecordOK => v1_is_not_v2 ((fst . snd . snd) (recordInjective assumeRecordOK)))
      (No f1_is_not_f2) => No (\assumeRecordOK => f1_is_not_f2 ((fst . snd) (recordInjective assumeRecordOK)))
    (No s1_is_not_s2) => No (\assumeRecordOK => s1_is_not_s2 (fst (recordInjective assumeRecordOK)))
