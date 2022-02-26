module TaPLc.Data.Vect.Quantifiers

import Data.Vect
import Data.Vect.Quantifiers
import TaPLc.Data.Vect

public export
take : {n : Nat} -> {xs : Vect n a} -> (i : Fin n) -> All p xs -> All p (Vect.Take.take i xs)
take = ?xtake

public export
index : {n : Nat} -> {xs : Vect n a} -> (i : Fin n) -> All p xs -> p (Vect.index i xs)
index FZ     (x :: y) = x
index (FS z) (x :: y) = index z y

public export
replaceAt : {n : Nat} -> {xs : Vect n a} -> (i : Fin n) -> p (Vect.index i xs) -> All p xs -> All p xs
replaceAt FZ     z (x :: y) = z :: y
replaceAt (FS w) z (x :: y) = x :: replaceAt w z y

export
replaceAtIndex
  :  {n : Nat} -> {xs : Vect n a} -> (i : Fin n) -> (y : p (Vect.index i xs)) -> (ys : All p xs)
  -> index i (replaceAt i y ys) === y
replaceAtIndex FZ     y (x :: z) = Refl
replaceAtIndex (FS w) y (x :: z) = replaceAtIndex w y z
