module TaPLc.Data.Vect

import Decidable.Equality
import Data.Vect

%default total

namespace ForEach

  public export
  data ForEach : Vect n a -> (p : a -> Type) -> Type where
    Nil  : ForEach [] p
    (::) : {xs : Vect n a} -> (p x) -> ForEach xs p -> ForEach (x :: xs) p

  public export
  index : {n : Nat} -> {xs : Vect n a} -> (i : Fin n) -> ForEach xs p -> p (Vect.index i xs)
  index FZ     (x :: xs) = x
  index (FS i) (x :: xs) = index i xs

namespace Take

  ||| Take the elements of a vector, before the given index.
  public export
  take : (i : Fin m) -> Vect m a -> Vect (finToNat i) a
  take FZ     (x :: xs) = []
  take (FS f) (x :: xs) = (x :: take f xs)

  namespace TakeExamples

    0 example1 : take FZ [0,1,2,3,4] === []
    example1 = Refl

    0 example2 : take (FS FZ) [1,2] === [1]
    example2 = Refl

namespace InNames

  public export
  data InNames : (i : Fin n) -> String -> Vect n String -> Type where
    Here  : InNames FZ f (f :: fs)
    There : InNames i f fs -> InNames (FS i) f (g :: fs)

  export Uninhabited (InNames _ f []) where uninhabited _ impossible

  public export
  inNames
    :  (field : String)
    -> (fs : Vect n String)
    -> Dec (DPair (Fin n) $ \i => InNames i field fs)
  inNames field [] = No (\assumeInRecord => uninhabited (snd assumeInRecord))
  inNames field (f :: fs) = case decEq f field of
    (Yes Refl) => Yes (FZ ** Here)
    (No field_is_not_f) => case inNames field fs of
        (Yes (i ** there)) => Yes ((FS i) ** There there)
        (No notThere) => No (\assumeThere => case assumeThere of
          (FZ     ** Here)          => field_is_not_f Refl
          ((FS i) ** (There there)) => notThere (i ** there))
