module TaPL.Chapter9

import Decidable.Equality
import Data.SnocList

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

  public export
  data GE : Name -> Ty -> Type where
    MkGE : (n : Name) -> (t : Ty) -> GE n t

  -- [< , , , ] -- Snoc list
  public export
  data Gamma : Type where
    Lin  : Gamma 
    (:<) : (g : Gamma) -> (Name, Ty) -> Gamma

  public export
  data InGamma : Name -> Ty -> Gamma -> Type where
    Here  : InGamma n ty (g :< (n,ty))
    There : (Not (n = m)) -> InGamma n ty g -> InGamma n ty (g :< (m,tz))

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
    (InGamma x ty gamma) ->
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


-- namespace Exercise_9_3_1

--   public export 0
--   InversionTy : (gamma : Gamma ns) -> (tty : TypeStatement) -> (gamma |- tty) -> Type
--   -- InversionTy gamma (Var x <:> (tyFrom g)) (TVar g) = InGamma x gamma
--   -- InversionTy gamma (Abs xx ty1 tm2 <:> Fun ty1 ty2) (TAbs x) = (gamma :< MkGE xx ty1) |- tm2 <:> ty2
--   -- InversionTy gamma (App tm1 tm2 <:> ty12) (TApp {ty11} x y) = (gamma |- tm1 <:> Fun ty11 ty12, gamma |- tm2 <:> ty11)
--   -- InversionTy gamma (True <:> Bool) TTrue = DPair Ty $ \r => ((True <:> Bool) = (True <:> r))
--   -- InversionTy gamma (False <:> Bool) TFalse = DPair Ty $ \r => ((False <:> Bool) = (False <:> r))
--   -- InversionTy gamma (IfThenElse tmp tmt tme <:> ty) (TIf x y z) = (gamma |- tmp <:> Bool, gamma |- tmt <:> ty, gamma |- tme <:> ty)
  
--   InversionTy gamma (Var x                  <:> (tyFrom g))  (TVar _)          = InGamma x gamma
--   InversionTy gamma (Abs x ty1 tm2          <:> Fun ty1 ty2) (TAbs _)          = (gamma :< MkGE x ty1) |- tm2 <:> ty2
--   InversionTy gamma (App tm1 tm2            <:> ty12)        (TApp {ty11} _ _) = (gamma |- tm1 <:> Fun ty11 ty12, gamma |- tm2 <:> ty11)
--   InversionTy gamma (True                   <:> Bool)        TTrue             = DPair Ty $ \r => ((True <:> Bool) = (True <:> r))
--   InversionTy gamma (False                  <:> Bool)        TFalse            = DPair Ty $ \r => ((False <:> Bool) = (False <:> r))
--   InversionTy gamma (IfThenElse tmp tmt tme <:> ty)          (TIf _ _ _)       = (gamma |- tmp <:> Bool, gamma |- tmt <:> ty, gamma |- tme <:> ty)

--   public export 0
--   inversion : (gamma : Gamma ns) -> (tty : TypeStatement) -> (typing : gamma |- tty) -> InversionTy gamma tty typing
--   inversion gamma (Var _            <:> _)        (TVar inGamma)  = inGamma
--   inversion gamma (Abs _ _ _        <:> Fun _ _)  (TAbs tp)       = tp
--   inversion gamma (App _ _          <:> _)        (TApp x y)      = (x, y)
--   inversion gamma (True             <:> Bool)     TTrue           = MkDPair Bool Refl
--   inversion gamma (False            <:> Bool)     TFalse          = MkDPair Bool Refl
--   inversion gamma (IfThenElse _ _ _ <:> _)        (TIf x y z)     = (x, y, z)


namespace Exercise_9_3_2

  0
  lemmaVar : (g : Gamma) -> (z : InGamma x ty1 g) -> (w : InGamma x ty2 g) -> ty1 = ty2
  lemmaVar (g :< (_,ty2)) Here Here = Refl
  lemmaVar (g :< (_,ty1)) Here (There f y) = absurd (f Refl)
  lemmaVar (g :< (m,ty2)) (There f y) Here = absurd (f Refl)
  lemmaVar (g :< (m,tz))  (There f y) (There f1 z) = lemmaVar g y z

  0
  uniquenessOfType : (g : Gamma) -> (typ1 : (g |- (tm <:> ty1))) -> (typ2 : (g |- (tm <:> ty2))) -> ty1 = ty2
  uniquenessOfType g (TVar z)                 (TVar y)    = lemmaVar g z y
  uniquenessOfType g (TAbs {x=x} {ty1=ty1} z) (TAbs y)    = rewrite (uniquenessOfType (g :< (x, ty1)) z y) in Refl
  uniquenessOfType g (TApp x y)               (TApp z w)  = snd (funInjective (uniquenessOfType g x z))
  uniquenessOfType g TTrue                    TTrue       = Refl
  uniquenessOfType g TFalse                   TFalse      = Refl
  uniquenessOfType g (TIf x y z)              (TIf w v s) = (uniquenessOfType g y v)
