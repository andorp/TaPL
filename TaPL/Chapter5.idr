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

    -- If, for each natural number n,
    --   given P (i) for all i < n
    --   we can show P (n),
    --   then P (n) holds for all n. 
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

  ||| The sketch of the LTE proof for the |Fv(t)| <= size(t)
  |||
  ||| With these pieces we can sketch the proof. This is the deep embedding of the proof.
  ||| The 'freeVarsLTESizeProof' functions creates the actual proof object, which has
  ||| two possible interpretations; one can be used to give the actual proof in terms
  ||| of the properties if the SortedSet (which still needs to be proven), and a function
  ||| that creates the Bool value, actually calling the functions, when we evaluate the
  ||| property.
  public export
  data FreeVarsLTESizeProof : Nat -> Nat -> Type where

    ||| The singleton sets have the size less then equal to one.
    SingletonSet
      :              (a : Variable)            ->
      -------------------------------------------
      FreeVarsLTESizeProof (size (singleton a)) 1
    
    ||| The delete operation could remove one element from the set,
    ||| leading to the assumption of the new set has less than or
    ||| equal number of elements compared to the original set.
    DeleteSize
      :                (a : Variable)                  ->
                  (as : SortedSet Variable)            ->
      ---------------------------------------------------
      FreeVarsLTESizeProof (size (delete a as)) (size as)
    
    ||| The size of the union of two sets should be less than equal
    ||| to the addition of the size of the each sets.
    UnionSize
      :          (a, b : SortedSet Variable)                 ->
      ---------------------------------------------------------
      FreeVarsLTESizeProof (size (union a b)) (size a + size b)
    
    ||| The trivial assumption of when m <= n then m <= (S n)
    LTESuccRight
      :   FreeVarsLTESizeProof m n    ->
      ----------------------------------
          FreeVarsLTESizeProof m (S n)
    
    ||| The tranisitivity property of the less than equal;
    ||| if m <= k and k <= n then m <= n
    Transitive
      :                       {k : Nat}                       ->
        FreeVarsLTESizeProof m k -> FreeVarsLTESizeProof k n  ->
      ----------------------------------------------------------
                  FreeVarsLTESizeProof m n

    ||| The monotonicity property of the less than equal operation;
    ||| if a <= b and c <= d then (a + c) <= (b + d)
    Monotonicity
      :                     {a,b,c,d : Nat} ->
        FreeVarsLTESizeProof a b -> FreeVarsLTESizeProof c d  ->
      ----------------------------------------------------------
                FreeVarsLTESizeProof (a + c) (b + d)

  ||| The sketch of the proof that |Fv(t)| <= size(t). It uses the
  ||| deeply embedded proof steps to create the spine/sketch of the
  ||| proof which can be used in different contexts.
  total
  export
  freeVarsLTESizeProof : (t : Term) -> FreeVarsLTESizeProof (size (freeVars t)) (size t)
  freeVarsLTESizeProof (Var v)
    = SingletonSet v
  freeVarsLTESizeProof (Lam v t)
    = Transitive
        (DeleteSize v (freeVars t))
        (LTESuccRight (freeVarsLTESizeProof t))
  freeVarsLTESizeProof (App t1 t2)
    = Transitive
        (UnionSize (freeVars t1) (freeVars t2))
        (LTESuccRight
          (Monotonicity
            (freeVarsLTESizeProof t1)
            ((freeVarsLTESizeProof t2))))

  ||| Check if the given proof object has a True evaluation in the
  ||| interpretation (vaguely speaking) in the value universe.
  ||| This function is expected to always return to True,
  ||| if it returns False some property is broken, we need further
  ||| investigation.
  |||
  ||| This function can be used in a property based testing framework to
  ||| actually check if the desired property holds.
  total
  export
  lteProperty : {m,n : Nat} -> FreeVarsLTESizeProof m n -> Bool
  lteProperty (SingletonSet a)    = m <= n
  lteProperty (DeleteSize a as)   = m <= n
  lteProperty (UnionSize a b)     = m <= n
  lteProperty (LTESuccRight x)    = m <= n && lteProperty x
  lteProperty (Transitive x y)    = m <= n && lteProperty x && lteProperty y
  lteProperty (Monotonicity x y)  = m <= n && lteProperty x && lteProperty y

  ||| The constructive proof for the defunctionalized FreeVarsLTESizeProof.
  ||| If we can create an LTE value from the FreeVarsLTESizeProof we are
  ||| sure that all the properties hold.
  |||
  ||| Even if we don't have the actual proofs yet, we know what to proof and
  ||| how it fits to the spine of the proof. The things around the LTE constructive
  ||| proofs are given, but the ones around SortedSet are not (yet).
  total
  export
  lteProof : {m,n : Nat} -> FreeVarsLTESizeProof m n -> LTE m n
  lteProof (SingletonSet a)   = ?lteProof_rhs_1
  lteProof (DeleteSize a as)  = ?lteProof_rhs_2
  lteProof (UnionSize a b)    = ?lteProof_rhs_3
  lteProof (LTESuccRight x)   = lteSuccRight (lteProof x)
  lteProof (Transitive x y)   = transitive {ty=Nat} {rel=LTE} (lteProof x) (lteProof y)
  lteProof (Monotonicity x y) = ?lteProof_rhs_6

  -- Example how to use the lteProperty
  -- In a QuickCheck like framework we could generate random Terms and the testing
  -- framework could use the computed Bool to assess if the expected property
  -- holds around proofs, if not, two things could be; the first that the freeVars
  -- implementation has some bugs, or the SortedSet has some bugs.
  isItOk : (t : Term) -> Bool
  isItOk t = lteProperty (freeVarsLTESizeProof t)


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

    EApp1
      :        Not (Value t1)          -> 
               Evaluation t1 t1'       ->
      -----------------------------------
      Evaluation (App t1 t2) (App t1' t2)

    EApp2
      :             Value v1           ->
               Evaluation t2 t2'       ->
      -----------------------------------
      Evaluation (App v1 t2) (App v1 t2')

    EAppAbs :
      -------------------------------------------------------------
      Evaluation (App (Lam x t1) t2) (substitution (Subst x t2) t1)

