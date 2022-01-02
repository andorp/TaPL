module TaPLc.IR.Variant

import Data.Vect
import Decidable.Equality

import TaPLc.IR.UniqueNames
import TaPLc.Data.NonZero

%default total

public export
record Variant (a : Type) where
  constructor MkVariant
  size        : Nat
  tags        : Vect size String
  info        : Vect size a
  uniqueTags  : UniqueNames size tags
  nonEmpty    : NonZero size

export
Show a => Show (Variant a) where
  showPrec d (MkVariant s t i _ _) = showCon d "MkVariant" $ showArg s ++ showArg t ++ showArg i

export
Functor Variant where
  map f v = record { info $= map f } v

export
variantInjective
  :  {v,w : Variant a} -> (v = w)
  -> (v.size = w.size, v.tags ~=~ w.tags, v.info ~=~ w.info, v.uniqueTags ~=~ w.uniqueTags, v.nonEmpty ~=~ w.nonEmpty)
variantInjective Refl = (Refl, Refl, Refl, Refl, Refl)

export
DecEq a => DecEq (Variant a) where
  decEq (MkVariant s1 t1 i1 u1 n1) (MkVariant s2 t2 i2 u2 n2) = case decEq s1 s2 of
    (Yes Refl) => case decEq t1 t2 of
      (Yes Refl) => case decEq i1 i2 of
        (Yes Refl) => case decEq u1 u2 of
          (Yes Refl) => case decEq n1 n2 of
            (Yes Refl) => Yes Refl
            (No n1_is_not_n2) => No (\assumeVariantOK => n1_is_not_n2 ((snd . snd . snd . snd) (variantInjective assumeVariantOK)))
          (No u1_is_not_u2) => No (\assumeVariantOK => u1_is_not_u2 ((fst . snd . snd . snd) (variantInjective assumeVariantOK)))
        (No i1_is_not_i2) => No (\assumeVariantOK => i1_is_not_i2 ((fst . snd . snd) (variantInjective assumeVariantOK)))
      (No t1_is_not_t2) => No (\assumeVariantOK => t1_is_not_t2 ((fst . snd) (variantInjective assumeVariantOK)))
    (No s1_is_not_s2) => No (\assumeVariantOK => s1_is_not_s2 (fst (variantInjective assumeVariantOK)))
