module TaPLc.Data.Vect

import Data.Vect

namespace Index

  public export
  data Index : a -> Nat -> Vect n a -> Type where
    Here  : Index x 0 (x :: xs)
    There : Index x n xs -> Index x (S n) (y :: xs)

  export Uninhabited (Index a n []) where uninhabited _ impossible

namespace ForEach

  public export
  data ForEach : Vect n a -> (p : a -> Type) -> Type where
    Nil  : ForEach [] p
    (::) : {xs : Vect n a} -> (p x) -> ForEach xs p -> ForEach (x :: xs) p
