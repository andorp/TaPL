module TaPL.Chapter7Dep

import Data.Fin

-- Based on http://adam.chlipala.net/cpdt/html/DeBruijn.html

data Exp : Nat -> Type where
  Var : {n : Nat} -> Fin n -> Exp n
  App : {n : Nat} -> (t1, t2 : Exp n) -> Exp n
  Abs : {n : Nat} -> Exp (S n) -> Exp n

-- pred : Nat -> Nat
-- pred Z     = Z
-- pred (S n) = n

{-
The classic implementation of substitution in de Bruijn terms requires
an auxiliary operation, lifting, which increments the indices of
all free variables in an expression. We need to lift whenever we
"go under a binder." It is useful to write an auxiliary function liftVar
that lifts a variable; that is, liftVar x y will return y + 1 if y >= x,
and it will return y otherwise. This simple description uses numbers
rather than our dependent fin family, so the actual specification is
more involved. 
-}

freeVarInc : {n : Nat} -> Fin n -> (Fin (pred n) -> Fin n) -> Fin (S n)
freeVarInc FZ     fx = FZ
freeVarInc (FS y) fx = FS (fx y)

liftVar : {n : Nat} -> (x : Fin n) -> Fin (pred n) -> Fin n
liftVar FZ     y = FS y
liftVar (FS x) y = freeVarInc y (liftVar x)

lift : {n : Nat} -> (e : Exp n) -> Fin (S n) -> Exp (S n)
lift (Var f')     f = Var (liftVar f f')
lift (App e1 e2)  f = App (lift e1 f) (lift e2 f)
lift (Abs e1)     f = Abs (lift e1 (FS f))

nzf : (n : Nat) -> (f : Fin n) -> S (pred n) = n
nzf (S _) FZ      = Refl
nzf (S _) (FS _)  = Refl

castExpr : {n1,n2 : Nat} -> (n1 = n2) -> Exp n1 -> Exp n2
castExpr prf e = rewrite (sym prf) in e

substVarSub
  : {n : Nat} -> Fin n -> Fin (pred n) -> (Fin (pred n) -> Maybe (Fin (pred (pred n)))) -> Maybe (Fin (pred n))
substVarSub FZ x fx     = Just x
substVarSub (FS y) x fx with (fx y)
  substVarSub (FS y) x fx | Nothing  = Nothing
  substVarSub (FS y) x fx | (Just z) = Just y

substVar : {n : Nat} -> (x : Fin n) -> Fin n -> Maybe (Fin (pred n))
substVar FZ     FZ     = Nothing
substVar FZ     (FS x) = Just x
substVar (FS x) y      = substVarSub y x (substVar x)

subst : {n : Nat} -> (e : Exp n) -> Fin n -> Exp (pred n) -> Exp (pred n)
subst (Var f') f v with (substVar f f')
  subst (Var f') f v | Nothing    = v
  subst (Var f') f v | (Just f'') = Var f''
subst (App e1 e2)  f v = App (subst e1 f v) (subst e2 f v)
subst {n} (Abs e1) f v
  = Abs
  $ castExpr (sym (nzf n f))
  $ subst e1 (FS f)
  $ castExpr (nzf n f)
  $ lift v FZ

-- Actually I don't fully understand what happens here, but I trust Adam Chipala's formalisation in Coq
