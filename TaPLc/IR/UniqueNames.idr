module TaPLc.IR.UniqueNames

import Data.Vect
import Decidable.Equality

namespace NotInt

  public export
  data NotIn : String -> Vect n String -> Type where
    Nil  : NotIn n []
    (::) : (0 c : Not (n = f)) -> NotIn n fs -> NotIn n (f :: fs)

  -- If the f and fs are the same, there should be only one way to create the list that proofs for every
  -- element the f is not in the fs vector. If we compare such two values, the only possible difference
  -- are the proofs that that f is not the head of the vector. We could have many computationaly different
  -- functions to create an impossbile Void value, but we say, if we got one, that the difference is their
  -- implementation is not relevant.
  -- At the same time we don't use such a proof at runtime, because the 0 quantity on the Cons cell, meaning
  -- that the runtime representation of such field, will be the Erased value, which is much easier to find
  -- if that is the same or not, as it should be the same, we are on the safe side.
  export
  DecEq (NotIn f fs) where
    decEq n1 n2 = Yes (believe_me (Refl {x=n1}))

public export
data UniqueNames : (n : Nat) -> Vect n String -> Type where
  Nil  : UniqueNames 0 []
  (::) : NotIn f fs -> UniqueNames n fs -> UniqueNames (S n) (f :: fs)

export
notInInjective : (UniqueNames.(::) ni1 ut1 = UniqueNames.(::) ni2 ut2) -> (ni1 = ni2, ut1 = ut2)
notInInjective Refl = (Refl, Refl)

export
DecEq (UniqueNames n xs) where
  decEq [] [] = Yes Refl
  decEq (x :: y) (z :: w) = case decEq x z of
    (Yes Refl) => case decEq y w of
      (Yes Refl) => Yes Refl
      (No y_is_not_w) => No (\assumeUniqueNames => y_is_not_w (snd (notInInjective assumeUniqueNames)))
    (No x_is_not_z) => No (\assumeUniqueNames => x_is_not_z (fst (notInInjective assumeUniqueNames)))