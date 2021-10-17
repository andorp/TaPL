module TaPL.Chapter5

import Data.Nat -- (maximum)
import Data.SortedSet
import Control.WellFounded

Variable : Type
Variable = String

data Term : Type where
  Var : (v : Variable) -> Term
  Lam : (v : Variable) -> (t : Term) -> Term
  App : (t1 : Term) -> (t2 : Term) -> Term

total
size : Term -> Nat
size (Var v)   = 1
size (Lam v t) = 1 + size t
size (App t1 t2) = 1 + size t1 + size t2

total
depth : Term -> Nat
depth (Var v)   = 1
depth (Lam v t) = 1 + depth t
depth (App t1 t2)  = 1 + maximum (depth t1) (depth t2)

namespace Induction

  namespace Structural

    export
    structural
      :  {P : Term -> Type}
      -> ((v : Variable) -> P (Var v))
      -> ((v : Variable) -> (t : Term) -> (pt : P t) -> P (Lam v t))
      -> ((t1,t2 : Term) -> (pt1 : P t1) -> (pt2 : P t2) -> P (App t1 t2))
      -> (t : Term)
      -> P t
    structural var lam app (Var v)     = var v
    structural var lam app (Lam v  t)  = lam v t   (structural var lam app t)
    structural var lam app (App t1 t2) = app t1 t2 (structural var lam app t1) (structural var lam app t2)

  namespace Size

    export
    size :  {p : Term -> Type}
        -> (step : (x : Term) -> ((y : Term) -> (LT (size y) (size x)) -> p y) -> p x) -> (s : Term) -> p s
    size = sizeInd
      where
        Sized Term where size = Chapter5.size

  namespace Depth

    export 
    depth :  {p : Term -> Type}
          -> (step : (x : Term) -> ((y : Term) -> (LT (depth y) (depth x)) -> p y) -> p x) -> (s : Term) -> p s
    depth = sizeInd
      where
        Sized Term where size = Chapter5.depth

total
freeVars : Term -> SortedSet String
freeVars (Var x)    = singleton x
freeVars (Lam x t)  = delete x (freeVars t)
freeVars (App s t)  = union (freeVars s) (freeVars t)

-- Exercise 5.3.3
namespace SortedSet

  export
  size : SortedSet Variable -> Nat
  size s = length (SortedSet.toList s)

  public export
  data DeepLTE : Nat -> Nat -> Type where
    SingletonSet : (a : Variable)
                -> DeepLTE (SortedSet.size (singleton a)) 1
    DeleteSize   : (a : Variable) -> (as : SortedSet Variable)
                -> DeepLTE (SortedSet.size (delete a as)) (SortedSet.size as)
    UnionSize    : (a, b : SortedSet Variable)
                -> DeepLTE (SortedSet.size (union a b)) (SortedSet.size a + SortedSet.size b)
    LTESuccRight : DeepLTE m n -> DeepLTE m (S n)
    Transitive   : {k : Nat} -> DeepLTE m k -> DeepLTE k n -> DeepLTE m n
    Monotonicity : {a,b,c,d : Nat} -> DeepLTE a b -> DeepLTE c d -> DeepLTE (a + c) (b + d)

  export
  freeVars_LTE_Size : (t : Term) -> DeepLTE (size (freeVars t)) (size t)
  freeVars_LTE_Size (Var v)
    = SingletonSet v
  freeVars_LTE_Size (Lam v t)
    = Transitive
        (DeleteSize v (freeVars t))
        (LTESuccRight (freeVars_LTE_Size t))
  freeVars_LTE_Size (App t1 t2)
    = Transitive
        (UnionSize (freeVars t1) (freeVars t2))
        (LTESuccRight
          (Monotonicity
            (freeVars_LTE_Size t1)
            ((freeVars_LTE_Size t2))))

  export
  lteProperty : {m,n : Nat} -> DeepLTE m n -> Bool
  lteProperty (SingletonSet a)    = m <= n
  lteProperty (DeleteSize a as)   = m <= n
  lteProperty (UnionSize a b)     = m <= n
  lteProperty (LTESuccRight x)    = m <= n && lteProperty x
  lteProperty (Transitive x y)    = m <= n && lteProperty x && lteProperty y
  lteProperty (Monotonicity x y)  = m <= n && lteProperty x && lteProperty y

  export
  lteProof : DeepLTE m n -> LTE m n
  lteProof (SingletonSet a) = ?lteProof_rhs_1
  lteProof (DeleteSize a as) = ?lteProof_rhs_2
  lteProof (UnionSize a b) = ?lteProof_rhs_3
  lteProof (LTESuccRight x) = ?lteProof_rhs_4
  lteProof (Transitive x y) = ?lteProof_rhs_5
  lteProof (Monotonicity x y) = ?lteProof_rhs_6

  isItOk : (t : Term) -> Bool
  isItOk t = lteProperty (freeVars_LTE_Size t)



data Substitution : Type where
  Subst : (x : Variable) -> (s : Term) -> Substitution

substitution : Substitution -> Term -> Term
substitution (Subst x s) (Var v) with (x == v)
  _ | True  = s
  _ | False = Var v
substitution (Subst x s) (Lam y t) with (x == y)
  _ | False with (contains y (freeVars s))
    _ | False = Lam y (substitution (Subst x s) t)
    _ | True  = Lam y t
  _ | True  = Lam y t
substitution (Subst x s) (App t1 t2)
  = App (substitution (Subst x s) t1) (substitution (Subst x s) t2)

-- Operational semantics
namespace Evaluation

  data Value : Term -> Type where
    Lam : Value (Lam x t)

  data Evaluation : Term -> Term -> Type where

    EApp1 :
              Not (Value t1)    -> 
              Evaluation t1 t1' ->
      -----------------------------------
      Evaluation (App t1 t2) (App t1' t2)

    EApp2 :
                   Value v1     ->
              Evaluation t2 t2' ->
      -----------------------------------
      Evaluation (App v1 t2) (App v1 t2')

    EAppAbs :
      -------------------------------------------------------------
      Evaluation (App (Lam x t1) t2) (substitution (Subst x t2) t1)

