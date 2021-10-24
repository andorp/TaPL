module TaPL.Chapter7

import Data.Either
import Data.Fuel

Name : Type
Name = String

namespace Ordinary

  public export
  data Term : Type where
    Var : Name -> Term
    Abs : Name -> Term -> Term
    App : Term -> Term -> Term

namespace Nameless

  public export
  data Term : Type where
    Var : (x,n : Int)                          -> Term
    Abs : (var : name) -> (t : Nameless.Term)  -> Term
    App : (t1, t2 : Nameless.Term)             -> Term

interface FreshName m where
  freshName : Name -> m Name

data Binding : Type where
  NameBindings : Binding

public export
Context :  Type
Context = List (Name, Binding)

printTerm : (Monad m, FreshName m) => Context -> Nameless.Term -> m String

export
total
termShift : (d : Int) -> Nameless.Term -> Nameless.Term
termShift d = walk 0
  where
    walk : (c : Int) -> (t : Nameless.Term) -> Nameless.Term
    walk c (Var x n)    = if x >= c then Var (x + d) (n + d) else Var x (n + d)
    walk c (Abs var t)  = Abs var (walk (1 + c) t)
    walk c (App t1 t2)  = App (walk c t1) (walk c t2)

export
total
termSubst : (j : Int) -> (s : Nameless.Term) -> Nameless.Term -> Nameless.Term
termSubst j s = walk 0
  where
    walk : (c : Int) -> (t : Nameless.Term) -> Nameless.Term
    walk c (Var x n)   = if x == j + c then termShift c s else Var x n
    walk c (Abs var t) = Abs var (walk (1 + c) t)
    walk c (App t1 t2) = App (walk c t1) (walk c t2)

export
total
termSubstTop : (s,t : Nameless.Term) -> Nameless.Term
termSubstTop s t = termShift (-1) (termSubst 0 (termShift 1 s) t)

data IsVal : Nameless.Term -> Type where
  Abs : IsVal (Abs _ _)

Uninhabited (IsVal (Var _ _)) where uninhabited _ impossible
Uninhabited (IsVal (App _ _)) where uninhabited _ impossible

total
isVal : (t : Nameless.Term) -> Either (IsVal t) (Not (IsVal t))
isVal (Var x n)   = Right uninhabited
isVal (Abs var t) = Left Abs
isVal (App t1 t2) = Right uninhabited

total
isValue : Context -> Nameless.Term -> Bool
isValue ctx t = isLeft (isVal t)

-- Single step evaluator
total
export
eval1 : Context -> Nameless.Term -> Maybe Nameless.Term
eval1 ctx (App (Abs var t12) v2@(Abs x t)) = 
  Just (termSubstTop v2 t12)
eval1 ctx (App v1@(Abs var t) t2) = do
  t2' <- eval1 ctx t2
  Just (App v1 t2')
eval1 ctx (App t1 t2) = do
  t1' <- eval1 ctx t1
  Just (App t1' t2)
eval1 _ _ = Nothing

total
eval : Fuel -> Context -> Nameless.Term -> Maybe Nameless.Term
eval Dry ctx t = Nothing
eval (More fuel) ctx t = do
  t' <- eval1 ctx t
  eval fuel ctx t'
