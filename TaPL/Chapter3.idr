module TaPL.Chapter3

import Data.Nat -- (maximum)
import Control.WellFounded

-- Terms by inference rules
data T : Type where
  True       : T
  False      : T
  Zero       : T
  Succ       : (t : T) -> T
  Pred       : (t : T) -> T
  IsZero     : (t : T) -> T
  IfThenElse : (p,t,e : T) -> T

namespace Values

  public export
  data Bool : T -> Type where
    True  : Bool True
    False : Bool False
    
  public export
  data Numeric : T -> Type where
    Zero : Numeric Zero
    Succ : (_ : Numeric n) -> Numeric (Succ n)

  public export
  data Value : T -> Type where
    BoolValue : {t : T} -> (b : Bool t)    -> Value t
    NumValue  : {t : T} -> (n : Numeric t) -> Value t

-- 3.3 Induction on Terms

-- Morally list as set.
total
consts : T -> List T
consts True = [True]
consts False = [False]
consts Zero = [Zero]
consts (Succ t) = consts t
consts (Pred t) = consts t
consts (IsZero t) = consts t
consts (IfThenElse p t e) = concat [consts p, consts t, consts e]

total
t_size : T -> Nat
t_size True = 1
t_size False = 1
t_size Zero = 1
t_size (Succ t) = 1 + t_size t
t_size (Pred t) = 1 + t_size t
t_size (IsZero t) = 1 + t_size t
t_size (IfThenElse p t e) = 1 + t_size p + t_size t + t_size e

total
t_depth : T -> Nat
t_depth True = 1
t_depth False = 1
t_depth Zero = 1
t_depth (Succ t) = 1 + t_depth t
t_depth (Pred t) = 1 + t_depth t
t_depth (IsZero t) = 1 + t_depth t
t_depth (IfThenElse p t e) = 1 + maximum (maximum (t_depth p) (t_depth t)) (t_depth e)

[TSized] Sized T where
  size = t_size

total
sizeInduction : {p : T -> Type} -> (step : (x : T) -> ((y : T) -> (LT (t_size y) (t_size x)) -> p y) -> p x) -> (s : T) -> p s
sizeInduction = sizeInd @{TSized}

[TDepth] Sized T where
  size = t_depth

total
depthInduction : {p : T -> Type} -> (step : (x : T) -> ((y : T) -> (LT (t_depth y) (t_depth x)) -> p y) -> p x) -> (s : T) -> p s
depthInduction = sizeInd @{TDepth}

total
structuralInduction
  :  {P : T -> Type}
  -> (P True)
  -> (P False)
  -> (P Zero)
  -> ((t : T) -> P t -> P (Succ t))
  -> ((t : T) -> P t -> P (Pred t))
  -> ((t : T) -> P t -> P (IsZero t))
  -> ((p,t,e : T) -> (pp : P p) -> (pt : P t) -> (pe : P e) -> P (IfThenElse p t e))
  -> (s : T)
  -> P s
structuralInduction t f z ps pp zp ifep True  = t
structuralInduction t f z ps pp zp ifep False = f
structuralInduction t f z ps pp zp ifep Zero  = z
structuralInduction t f z ps pp zp ifep (Succ x)   = ps x (structuralInduction t f z ps pp zp ifep x)
structuralInduction t f z ps pp zp ifep (Pred x)   = pp x (structuralInduction t f z ps pp zp ifep x)
structuralInduction t f z ps pp zp ifep (IsZero x) = zp x (structuralInduction t f z ps pp zp ifep x)
structuralInduction t f z ps pp zp ifep (IfThenElse px tx ex)
  = ifep px tx ex
         (structuralInduction t f z ps pp zp ifep px)
         (structuralInduction t f z ps pp zp ifep tx)
         (structuralInduction t f z ps pp zp ifep ex)

namespace Relations

  public export
  data IsNumerical : T -> Type where
    Zero : IsNumerical Zero
    Succ : {x : T} -> (n : IsNumerical x) -> IsNumerical (Succ x)

  public export
  isNumerical : (t : T) -> Maybe (IsNumerical t)
  isNumerical Zero = Just Zero
  isNumerical (Succ x) = do
    px <- isNumerical x
    Just (Succ px)
  isNumerical _ = Nothing

  public export
  data IsVal : T -> Type where
    True      : IsVal True
    False     : IsVal False
    Numerical : {1 x : T} -> (0 _ : IsNumerical x) -> IsVal x

  public export
  isVal : (t : T) -> Maybe (IsVal t)
  isVal True = Just True
  isVal False = Just False
  isVal a = do
    n <- isNumerical a
    Just (Numerical n)

public export
data Evaluation : T -> T -> Type where

  EIfTrue  : Evaluation (IfThenElse True  t2 t3) t2
  EIfFalse : Evaluation (IfThenElse False t2 t3) t3
  EIf :  Evaluation t1 t1'
      -> Evaluation (IfThenElse t1 t2 t3) (IfThenElse t1' t2 t3)

  ESucc : Evaluation t1 t1' -> Evaluation (Succ t1) (Succ t1')
  
  EPredZero :                         Evaluation (Pred Zero)      Zero
  EPredSucc : (n : IsNumerical nv) -> Evaluation (Pred (Succ nv)) nv
  EPred     : Evaluation t1 t1'    -> Evaluation (Pred t1)        (Pred t1')
  
  EIsZeroZero :                         Evaluation (IsZero Zero)      True
  EIsZeroSucc : (n : IsNumerical nv) -> Evaluation (IsZero (Succ nv)) False
  EIsZero     : Evaluation t1 t1'    -> Evaluation (IsZero t1)        (IsZero t1')

namespace Exercise_3_5_3

  s : T
  s = IfThenElse True False False

  t : T
  t = IfThenElse s True True

  u : T
  u = IfThenElse False True True

  derivation1 : Evaluation (Exercise_3_5_3.s) False
  derivation1 = EIfTrue

  derivation : Evaluation
                  (IfThenElse Exercise_3_5_3.t False False)
                  (IfThenElse Exercise_3_5_3.u False False)
  derivation = EIf (EIf (EIfTrue))

namespace Exercise_3_5_4

  isNumericalDoNotReduce : {t, t' : T} -> IsNumerical t -> Not (Evaluation t t')
  isNumericalDoNotReduce Zero             e   impossible
  isNumericalDoNotReduce (Succ x) (ESucc y) = isNumericalDoNotReduce x y

  determinacy : (t,t',t'' : T) -> Evaluation t t' -> Evaluation t t'' -> t' = t''
  determinacy (IfThenElse True t' t3)   t'                      t'                      EIfTrue         EIfTrue         = Refl
  determinacy (IfThenElse True t' t3)   t'                      (IfThenElse t1' t' t3)  EIfTrue         (EIf x)         impossible
  determinacy (IfThenElse False t2 t')  t'                      t'                      EIfFalse        EIfFalse        = Refl
  determinacy (IfThenElse False t2 t')  t'                      (IfThenElse t1' t2 t')  EIfFalse        (EIf x)         impossible
  determinacy (IfThenElse True t2 t3)   (IfThenElse t1' t2 t3)  t2                      (EIf x)         EIfTrue         impossible
  determinacy (IfThenElse False t2 t3)  (IfThenElse t1' t2 t3)  t3                      (EIf x)         EIfFalse        impossible
  determinacy (IfThenElse t1 t2 t3)     (IfThenElse qqq t2 t3)  (IfThenElse t1' t2 t3)  (EIf x)         (EIf y)         = rewrite (determinacy t1 qqq t1' x y) in Refl
  determinacy (Succ t1)                 (Succ qqq)              (Succ t1')              (ESucc x)       (ESucc y)       = rewrite (determinacy t1 qqq t1' x y) in Refl
  determinacy (Pred Zero)               Zero                    Zero                    EPredZero       EPredZero       = Refl
  determinacy (Pred Zero)               Zero                    (Pred t1')              EPredZero       (EPred x)       impossible
  determinacy (Pred (Succ t'))          t'                      t'                      (EPredSucc x)   (EPredSucc y)   = Refl
  determinacy (Pred (Succ t'))          t'                      (Pred t1')              (EPredSucc x)   (EPred y)       = the (t' = Pred t1')
                                                                                                                        $ void (isNumericalDoNotReduce (Succ x) y)
  determinacy (Pred Zero)               (Pred t1')              Zero                    (EPred x)       EPredZero       impossible
  determinacy (Pred (Succ t''))         (Pred t1')              t''                     (EPred x)       (EPredSucc y)   = the (Pred t1' = t'')
                                                                                                                        $ void (isNumericalDoNotReduce (Succ y) x)
  determinacy (Pred t1)                 (Pred qqq)              (Pred t1')              (EPred x)       (EPred y)       = rewrite (determinacy t1 qqq t1' x y) in Refl
  determinacy (IsZero Zero)             True                    True                    EIsZeroZero     EIsZeroZero     = Refl
  determinacy (IsZero Zero)             True                    (IsZero t1')            EIsZeroZero     (EIsZero x)     impossible
  determinacy (IsZero (Succ nv))        False                   False                   (EIsZeroSucc x) (EIsZeroSucc y) = Refl
  determinacy (IsZero (Succ nv))        False                   (IsZero t1')            (EIsZeroSucc x) (EIsZero y)     = the (False = IsZero t1')
                                                                                                                        $ void (isNumericalDoNotReduce (Succ x) y)
  determinacy (IsZero Zero)             (IsZero t1')            True                    (EIsZero x)     EIsZeroZero     impossible
  determinacy (IsZero (Succ nv))        (IsZero t1')            False                   (EIsZero x)     (EIsZeroSucc y) = the (IsZero t1' = False)
                                                                                                                        $ void (isNumericalDoNotReduce (Succ y) x) ()
  determinacy (IsZero t1)               (IsZero qqq)            (IsZero t1')            (EIsZero x)     (EIsZero y)     = rewrite (determinacy t1 qqq t1' x y) in Refl

total
public export
eval : T                   -> Maybe T
eval True                   = Just True
eval False                  = Just False
eval Zero                   = Just Zero
eval (Succ t)               = map Succ (eval t)
eval (Pred Zero)            = Just Zero
eval (Pred (Succ nv)) with (isNumerical nv)
  _ | Just n                = Just nv
  _ | Nothing = map Pred (assert_total {- !!! -} (eval (Succ nv)))
eval (Pred t) = map Pred (eval t)
eval (IsZero Zero)          = Just True
eval (IsZero (Succ nv)) with (isNumerical nv)
  _ | Just n  = Just False
  _ | Nothing = map IsZero (assert_total {- !!! -} (eval (Succ nv)))
eval (IsZero t)             = map IsZero (eval t)
eval (IfThenElse True t e)  = Just t
eval (IfThenElse False t e) = Just e
eval (IfThenElse p t e)     = map (\x => IfThenElse x t e) (eval p)
eval _                      = Nothing
