module TaPL.Chapter8

namespace Term

  public export
  data Tm : Type where
    True       : Tm
    False      : Tm
    Zero       : Tm
    Succ       : (t : Tm) -> Tm
    Pred       : (t : Tm) -> Tm
    IsZero     : (t : Tm) -> Tm
    IfThenElse : (p,t,e : Tm) -> Tm

namespace Value

  public export
  data NValue : Tm -> Type where
    Zero  : NValue Zero
    Succ  : NValue t -> NValue (Succ t)

  public export
  data Value : Tm -> Type where
    True  : Value True
    False : Value False
    NVal  : NValue t -> Value t  

data Ty : Type where
  Bool : Ty
  Nat  : Ty

data HasType : Tm -> Ty -> Type where

  TTrue :
    --------------------
    True `HasType` Bool
  
  TFalse :
    --------------------
    False `HasType` Bool

  TIf :
    {ty : Ty} -> (tm1 `HasType` Bool) -> (tm2 `HasType` ty) -> (tm3 `HasType` ty) ->
    --------------------------------------------------------------------------------
                    (IfThenElse tm1 tm2 tm3) `HasType` ty

  TZero :
    ------------------
    Zero `HasType` Nat
  
  TSucc :
         tm `HasType` Nat    ->
    ---------------------------
      (Succ tm) `HasType` Nat
  
  TPred :
         tm `HasType` Nat    ->
    ---------------------------
      (Pred tm) `HasType` Nat

  TIsZero :
            tm `HasType` Nat    ->
      ----------------------------
       (IsZero tm) `HasType` Bool

namespace Exercise_8_2_2

  exercise_8_2_2_1 : True `HasType` r -> r = Bool
  exercise_8_2_2_1 TTrue = Refl

  exercise_8_2_2_2 : False `HasType` r -> r = Bool
  exercise_8_2_2_2 TFalse = Refl

  exercise_8_2_2_3 : IfThenElse t1 t2 t3 `HasType` r -> (t1 `HasType` Bool, t2 `HasType` r, t3 `HasType` r)
  exercise_8_2_2_3 (TIf x y z) = (x, y, z)

  exercise_8_2_2_4 : Zero `HasType` r -> r = Nat
  exercise_8_2_2_4 TZero = Refl

  exercise_8_2_2_5 : (Succ t1) `HasType` r -> (r = Nat, t1 `HasType` Nat)
  exercise_8_2_2_5 (TSucc x) = (Refl, x)

  exercise_8_2_2_6 : (Pred t1) `HasType` r -> (r = Nat, t1 `HasType` Nat)
  exercise_8_2_2_6 (TPred x) = (Refl, x)

  exercise_8_2_2_7 : (IsZero t1) `HasType` r -> (r = Bool, t1 `HasType` Nat)
  exercise_8_2_2_7 (TIsZero x) = (Refl, x)

  exercise_8_2_2_dp : (tm : Tm) -> (DPair Ty $ \ty => ())

  public export
  0 exercise_8_2_2_Ty : (tm : Tm) -> (ty : Ty) -> (tm `HasType` ty) -> Type
  exercise_8_2_2_Ty True                      Bool  TTrue       = Chapter8.Bool === Bool
  exercise_8_2_2_Ty False                     Bool  TFalse      = Chapter8.Bool === Bool
  exercise_8_2_2_Ty (IfThenElse tm1 tm2 tm3)  ty    (TIf x y z) = (tm1 `HasType` Bool, tm2 `HasType` ty, tm3 `HasType` ty)
  exercise_8_2_2_Ty Zero                      Nat   TZero       = Chapter8.Nat === Nat
  exercise_8_2_2_Ty (Succ tm)                 Nat   (TSucc x)   = (Chapter8.Nat === Nat, tm `HasType` Nat)
  exercise_8_2_2_Ty (Pred tm)                 Nat   (TPred x)   = (Chapter8.Nat === Nat, tm `HasType` Nat)
  exercise_8_2_2_Ty (IsZero tm)               Bool  (TIsZero x) = (Chapter8.Bool === Bool, tm `HasType` Nat)

  public export
  0 exercise_8_2_2 : (ty : Ty) -> (tm : Tm) -> (hasTy : (tm `HasType` ty)) -> exercise_8_2_2_Ty tm ty hasTy
  exercise_8_2_2 Bool True                      TTrue       = Refl
  exercise_8_2_2 Bool False                     TFalse      = Refl
  exercise_8_2_2 ty   (IfThenElse tm1 tm2 tm3)  (TIf x y z) = (x, y, z)
  exercise_8_2_2 Nat  Zero                      TZero       = Refl
  exercise_8_2_2 Nat  (Succ tm)                 (TSucc x)   = (Refl, x)
  exercise_8_2_2 Nat  (Pred tm)                 (TPred x)   = (Refl, x)
  exercise_8_2_2 Bool (IsZero tm)               (TIsZero x) = (Refl, x)

namespace Exercise_8_2_3

  subTerms : Tm -> List Tm
  subTerms True               = []
  subTerms False              = []
  subTerms Zero               = []
  subTerms (Succ t)           = [t]
  subTerms (Pred t)           = [t]
  subTerms (IsZero t)         = [t]
  subTerms (IfThenElse p t e) = [p,t,e]

  data WellTypedSubTerms : List Tm -> Type where
    Nil  : WellTypedSubTerms []
    (::) : {tm : Tm} -> {ty : Ty} -> (tm `HasType` ty) -> WellTypedSubTerms tms -> WellTypedSubTerms (tm :: tms)

  wellTypedSubTerms : (tm : Tm) -> (tm `HasType` ty) -> WellTypedSubTerms (subTerms tm)
  wellTypedSubTerms True                TTrue       = []
  wellTypedSubTerms False               TFalse      = []
  wellTypedSubTerms Zero                TZero       = []
  wellTypedSubTerms (Succ t)            (TSucc x)   = [x]
  wellTypedSubTerms (Pred t)            (TPred x)   = [x]
  wellTypedSubTerms (IsZero t)          (TIsZero x) = [x]
  wellTypedSubTerms (IfThenElse p t e)  (TIf x y z) = [x,y,z]

namespace Exercise_8_3_1

  total public export 0
  CanonicalFormTy : Ty -> Tm -> Type
  CanonicalFormTy Bool t = Either (t = True) (t = False)
  CanonicalFormTy Nat  t = Either (t = Zero) (r : Tm ** (t = Succ r))

  total 0
  cannonicalFormsBool : (tm : Tm) -> (v : Value tm) -> (tm `HasType` Bool) -> CanonicalFormTy Bool tm
  cannonicalFormsBool True                True            TTrue   = Left Refl
  cannonicalFormsBool False               False           TFalse  = Right Refl
  cannonicalFormsBool True                (NVal Zero)     _           impossible
  cannonicalFormsBool True                (NVal (Succ y)) _           impossible
  cannonicalFormsBool False               (NVal Zero)     _           impossible
  cannonicalFormsBool False               (NVal (Succ y)) _           impossible
  cannonicalFormsBool Zero                (NVal Zero)     TTrue       impossible
  cannonicalFormsBool Zero                (NVal Zero)     TFalse      impossible
  cannonicalFormsBool Zero                (NVal Zero)     (TIf x y z) impossible
  cannonicalFormsBool Zero                (NVal Zero)     TZero       impossible
  cannonicalFormsBool Zero                (NVal Zero)     (TSucc x)   impossible
  cannonicalFormsBool Zero                (NVal Zero)     (TPred x)   impossible
  cannonicalFormsBool Zero                (NVal Zero)     (TIsZero x) impossible
  cannonicalFormsBool (Succ _)            (NVal (Succ _)) TTrue       impossible
  cannonicalFormsBool (Succ _)            (NVal (Succ _)) TFalse      impossible
  cannonicalFormsBool (Succ _)            (NVal (Succ _)) (TIf x z w) impossible
  cannonicalFormsBool (Succ _)            (NVal (Succ _)) TZero       impossible
  cannonicalFormsBool (Succ _)            (NVal (Succ _)) (TSucc x)   impossible
  cannonicalFormsBool (Succ _)            (NVal (Succ _)) (TPred x)   impossible
  cannonicalFormsBool (Succ _)            (NVal (Succ _)) (TIsZero x) impossible
  cannonicalFormsBool (Pred _)            (NVal _)        TTrue       impossible
  cannonicalFormsBool (Pred _)            (NVal _)        TFalse      impossible
  cannonicalFormsBool (Pred _)            (NVal _)        (TIf x z w) impossible
  cannonicalFormsBool (Pred _)            (NVal _)        TZero       impossible
  cannonicalFormsBool (Pred _)            (NVal _)        (TSucc x)   impossible
  cannonicalFormsBool (Pred _)            (NVal _)        (TPred x)   impossible
  cannonicalFormsBool (Pred _)            (NVal _)        (TIsZero x) impossible
  cannonicalFormsBool (IsZero _)          (NVal Zero)     _           impossible
  cannonicalFormsBool (IsZero _)          (NVal (Succ y)) _           impossible
  cannonicalFormsBool (IfThenElse _ _ _)  (NVal Zero)     _           impossible
  cannonicalFormsBool (IfThenElse _ _ _)  (NVal (Succ y)) _           impossible

  total 0
  cannonicalFormsNValNat : (tm : Tm) -> (v : NValue tm) -> (tm `HasType` Nat) -> CanonicalFormTy Nat tm
  cannonicalFormsNValNat Zero     Zero     x         = Left Refl
  cannonicalFormsNValNat (Succ t) (Succ y) (TSucc x) = Right (t ** Refl)

  total 0
  cannonicalFormsNat : (tm : Tm) -> (v : Value tm) -> (tm `HasType` Nat) -> CanonicalFormTy Nat tm
  cannonicalFormsNat tm (NVal y) x = cannonicalFormsNValNat tm y x

  total 0
  cannonicalForms : (tm : Tm) -> (ty : Ty) -> (v : Value tm) -> (tm `HasType` ty) -> CanonicalFormTy ty tm
  cannonicalForms tm Bool v x = cannonicalFormsBool tm v x
  cannonicalForms tm Nat  v x = cannonicalFormsNat  tm v x
