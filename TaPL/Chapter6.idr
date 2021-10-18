module TaPL.Chapter6

import Data.Vect
import Data.Nat

Name : Type
Name = String

namespace Ordinary

  public export
  data Term : Type where
    Var : Name -> Term
    Lam : Name -> Term -> Term
    App : Term -> Term -> Term

namespace Nameless

  public export
  Context : Nat -> Type
  Context n = Vect n Name

  public export
  data Term : Context _ -> Type where
    Var : {g : Nat} -> {gamma : Context g} -> Fin g -> Term gamma
    Lam : {g : Nat} -> {gamma : Context g} -> {var : Name} -> (t : Term (var :: gamma)) -> Term gamma
    App : {g : Nat} -> {gamma : Context g} -> (t1, t2 : Term gamma) -> Term gamma

restoreNames : Nameless.Term _ -> Ordinary.Term
restoreNames (Var {g} {gamma} k)       = Var (index k gamma)
restoreNames (Lam {g} {gamma} {var} t) = Lam var (restoreNames t)
restoreNames (App {g} {gamma} t1 t2)   = App (restoreNames t1) (restoreNames t2)

removeNames : (gamma : Context g) -> Ordinary.Term -> Either String (Nameless.Term gamma)
removeNames gamma (Var x) = ?removeNames_rhs_1
removeNames gamma (Lam x y) = ?removeNames_rhs_2
removeNames gamma (App x y) = ?removeNames_rhs_3

