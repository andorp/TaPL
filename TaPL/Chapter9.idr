module TaPL.Chapter9

import Decidable.Equality

mutual

  public export
  Name : Type
  Name = String

  public export
  data Tm : Type where
    Var : (var : Name) -> Tm
    Abs : (var : Name) -> (ty : Ty) -> (t : Tm) -> Tm
    App : (tm1, tm2 : Tm) -> Tm

    True  : Tm
    False : Tm
    IfThenElse : (p,t,e : Tm) -> Tm

  public export
  data Ty : Type where
    Bool : Ty
    Fun  : Ty -> Ty -> Ty  

Uninhabited (Bool = Fun t1 t2) where uninhabited _ impossible
Uninhabited (Fun t1 t2 = Bool) where uninhabited _ impossible

funInjective : Fun t1 t2 = Fun r1 r2 -> (t1 = r1, t2 = r2)
funInjective Refl = (Refl, Refl)

DecEq Ty where
  decEq Bool Bool = Yes Refl
  decEq Bool (Fun x y) = No uninhabited
  decEq (Fun x y) Bool = No uninhabited
  decEq (Fun x y) (Fun z w) = case (decEq x z, decEq y w) of
    ((Yes xz), (Yes yw))      => rewrite xz in rewrite yw in Yes Refl
    ((Yes prf), (No contra))  => No (\funXyFunZw => contra (snd (funInjective funXyFunZw)))
    ((No contra), (Yes prf))  => No (\funXyFunZw => contra (fst (funInjective funXyFunZw)))
    ((No contra), (No _))     => No (\funXyFunZw => contra (fst (funInjective funXyFunZw)))


-- Substituition assumes unique names, no need for alpha conversions.
-- TODO: Check if this right.
total
substituition : (Name, Tm) -> Tm -> Tm
substituition (n, tm1) (Var var) = case decEq n var of
  (Yes prf)   => tm1
  (No contra) => (Var var)
substituition s (Abs var ty t) = Abs var ty (substituition s t)
substituition s (App t1 t2) = App (substituition s t1) (substituition s t2)
substituition s True = True
substituition s False = False
substituition s (IfThenElse p t e) = IfThenElse (substituition s p) (substituition s t) (substituition s e)

namespace Value

  public export
  data Val : Tm -> Type where
    Abs   : Val (Abs var ty t)
    True  : Val True
    False : Val False
    IfThenElse : (pv : Val p) -> (pt : Val t) -> (pe : Val e) -> Val (IfThenElse p t e)

namespace Context

  -- [< , , , ] -- Snoc list
  public export
  data Gamma : Type where
    Lin  : Gamma
    (:<) : (g : Gamma) -> (y : (Name, Ty)) -> Gamma

  public export
  data InGamma : (Name, Ty) -> Gamma -> Type where
    Here  :                    InGamma x (gamma :< x)
    There : InGamma x gamma -> InGamma x (gamma :< y)

  public export
  data Wellformed : Gamma -> Type where
    -- TODO

  public export
  Uninhabited (InGamma _ [<]) where
    uninhabited _ impossible

  public export
  inGamma : (x : (Name, Ty)) -> (g : Gamma) -> Dec (InGamma x g)
  inGamma x1 [<] = No uninhabited
  inGamma x1 (g1 :< y1) = case decEq x1 y1 of
    (Yes x_is_y)    => Yes (rewrite (sym x_is_y) in Here)
    (No x_is_not_y) => case inGamma x1 g1 of
      (Yes x_is_in_gamma)    => Yes $ There x_is_in_gamma
      (No x_is_not_in_gamma) => No $ \case
        Here      => x_is_not_y Refl
        (There x) => x_is_not_in_gamma x

data Evaluation : Tm -> Tm -> Type where

  EApp1 :
            Evaluation t1 t1'        ->
    -----------------------------------
    Evaluation (App t1 t2) (App t1' t2)
  
  EApp2 :
                 (Val v1)          ->
              Evaluation t t'      ->
    ---------------------------------            
    Evaluation (App v1 t) (App v1 t')

  EAppAbs :
                          (Val v1)                       ->
    -------------------------------------------------------
    Evaluation (App (Abs x ty t) v) (substituition (x,v) t)

infix 11 <:>

data TypeStatement : Type where
  (<:>) : (t1 : Tm) -> (t2 : Ty) -> TypeStatement

infix 10 |-

data (|-) : Gamma -> TypeStatement -> Type where

  TVar :
    InGamma (x,ty) gamma ->
    -----------------------
    gamma |- Var x <:> ty
  
  TAbs :
     (gamma :< (x,ty1)) |- tm2 <:> ty2  ->
  ----------------------------------------
   gamma |- Abs x ty1 tm2 <:> Fun ty1 ty2

  TApp :
    (gamma |- tm1 <:> Fun ty11 ty12) -> (gamma |- tm2 <:> ty11) ->
    --------------------------------------------------------------
                    gamma |- App tm1 tm2 <:> ty12

  TTrue :
    ----------------------
    gamma |- True <:> Bool

  TFalse :
    -----------------------
    gamma |- False <:> Bool

  TIf :
    (gamma |- tmp <:> Bool) -> (gamma |- tmt <:> ty) -> (gamma |- tme <:> ty) ->
    ----------------------------------------------------------------------------
                     gamma |- (IfThenElse tmp tmt tme <:> ty)

namespace Exercise_9_3_1

  public export 0
  InversionTy : (gamma : Gamma) -> (tty : TypeStatement) -> (gamma |- tty) -> Type
  InversionTy gamma (Var x                  <:> ty)          (TVar _)          = InGamma (x,ty) gamma
  InversionTy gamma (Abs x ty1 tm2          <:> Fun ty1 ty2) (TAbs _)          = (gamma :< (x,ty1)) |- tm2 <:> ty2
  InversionTy gamma (App tm1 tm2            <:> ty12)        (TApp {ty11} _ _) = (gamma |- tm1 <:> Fun ty11 ty12, gamma |- tm2 <:> ty11)
  InversionTy gamma (True                   <:> Bool)        TTrue             = DPair Ty $ \r => ((True <:> Bool) = (True <:> r))
  InversionTy gamma (False                  <:> Bool)        TFalse            = DPair Ty $ \r => ((False <:> Bool) = (False <:> r))
  InversionTy gamma (IfThenElse tmp tmt tme <:> ty)          (TIf _ _ _)       = (gamma |- tmp <:> Bool, gamma |- tmt <:> ty, gamma |- tme <:> ty)

  public export 0
  inversion : (gamma : Gamma) -> (tty : TypeStatement) -> (typing : gamma |- tty) -> InversionTy gamma tty typing
  inversion gamma (Var _            <:> _)        (TVar inGamma)  = inGamma
  inversion gamma (Abs _ _ _        <:> Fun _ _)  (TAbs tp)       = tp
  inversion gamma (App _ _          <:> _)        (TApp x y)      = (x, y)
  inversion gamma (True             <:> Bool)     TTrue           = MkDPair Bool Refl
  inversion gamma (False            <:> Bool)     TFalse          = MkDPair Bool Refl
  inversion gamma (IfThenElse _ _ _ <:> _)        (TIf x y z)     = (x, y, z)

namespace Exercise_9_3_2

  uniquenessOfTypes : (gamma : Gamma) -> (t : Tm) -> (ty1, ty2 : Ty) -> (gamma |- (t <:> ty1)) -> (gamma |- (t <:> ty2)) -> ty1 = ty2
  uniquenessOfTypes (gamma :< (x, ty1)) (Var x) ty1 ty2 (TVar Here)      (TVar typ2) = ?uniquenessOfTypes_rhs_10
  uniquenessOfTypes (gamma :< (y, r))   (Var x) ty1 ty2 (TVar (There z)) (TVar typ2) = ?uniquenessOfTypes_rhs_11
  uniquenessOfTypes [<] (Var x) ty1 ty2 _ _ = case (inGamma (x, ty1) [<]) of
    (Yes prf) => ?h2_1
    (No contra) => ?h2_2
  uniquenessOfTypes gamma (Abs x ty1 tm2) (Fun ty1 rty1) (Fun ty1 rty2) (TAbs typ1) (TAbs typ2) = ?uniquenessOfTypes_rhs_9
  uniquenessOfTypes gamma (App tm1 tm2) ty1 ty2 (TApp x y) typing2 = ?uniquenessOfTypes_rhs_4
  uniquenessOfTypes gamma True Bool ty2 TTrue typing2 = ?uniquenessOfTypes_rhs_5
  uniquenessOfTypes gamma False Bool ty2 TFalse typing2 = ?uniquenessOfTypes_rhs_6
  uniquenessOfTypes gamma (IfThenElse tmp tmt tme) ty1 ty2 (TIf x y z) typing2 = ?uniquenessOfTypes_rhs_7

