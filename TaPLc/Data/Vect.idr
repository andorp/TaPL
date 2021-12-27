module TaPLc.Data.Vect

import Decidable.Equality
import Data.Vect

%default total

namespace Index

  public export
  data Index : a -> Nat -> Vect n a -> Type where
    Here  : Index x 0 (x :: xs)
    There : Index x n xs -> Index x (S n) (y :: xs)

  export Uninhabited (Index a n []) where uninhabited _ impossible

  export
  index : (DecEq a) => (x : a) -> (xs : Vect n a) -> Dec (i : Nat ** Index x i xs)
  index x [] = No (\case (MkDPair assumeI assumeIndex) => (uninhabited assumeIndex))
  index x (y :: xs) = case decEq x y of
    (Yes Refl) => Yes (MkDPair 0 Here)
    (No xIsNotY) => case index x xs of
      (Yes (MkDPair i there)) => Yes (MkDPair (S i) (There there))
      (No xIsNotInXS) => No (\case
        (MkDPair 0 Here) => xIsNotY Refl
        (MkDPair (S k) (There there)) => xIsNotInXS (MkDPair k there))

namespace ForEach

  public export
  data ForEach : Vect n a -> (p : a -> Type) -> Type where
    Nil  : ForEach [] p
    (::) : {xs : Vect n a} -> (p x) -> ForEach xs p -> ForEach (x :: xs) p

  public export
  index : {n : Nat} -> {xs : Vect n a} -> (i : Fin n) -> ForEach xs p -> p (Vect.index i xs)
  index FZ     (x :: xs) = x
  index (FS i) (x :: xs) = index i xs

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
