module TaPLc.Data.NonZero

import Data.Nat
import Decidable.Equality

export
DecEq (NonZero n) where
  decEq SIsNonZero SIsNonZero = Yes Refl