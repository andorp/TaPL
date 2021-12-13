module TaPLc.TypeInference.TypingRules

import Data.Vect

import TaPLc.IR.Term
import TaPLc.IR.Type
import TaPLc.IR.Context
import TaPLc.IR.Info
import TaPLc.IR.Name
import TaPLc.IR.UniqueNames
import TaPLc.IR.Record
import TaPLc.IR.Variant
import TaPLc.Data.Vect


infix 10 |-
infix 11 <:>

public export
data TypeStatement : Type where
  (<:>) : (0 t1 : Tm) -> (t2 : Ty) -> TypeStatement

public export
data (|-) : (0 _ : Context) -> TypeStatement -> Type

public export
data Derivation : Context -> Tm -> Ty -> Type where
  MkDerivation : (t : Tm) -> (ty : Ty) -> (deriv : (ctx |- t <:> ty)) -> Derivation ctx t ty

namespace VariantDerivations

  ||| Witness that every Tm term in the alternatives has the same Ty type.
  public export
  data VariantDerivations : (n : Nat) -> Context -> Vect n (Name, Tm) -> Vect n Ty -> Ty -> Type where
    Nil  : VariantDerivations 0 ctx [] [] ty
    (::) : {var : Name} -> {tty : Ty}
           -> Derivation (ctx :< (var, VarBind tty)) t ty
           -> VariantDerivations n ctx ts ttys ty
           -> VariantDerivations (S n) ctx ((var, t) :: ts) (tty :: ttys) ty

namespace Derivations

  ||| Type derivation for record fields
  public export
    data Derivations : Context -> Vect n Tm -> Vect n Ty -> Type where
      Nil  : Derivations ctx [] []
      (::) : Derivation ctx t ty -> Derivations ctx ts tys -> Derivations ctx (t :: ts) (ty :: tys)

public export
data (|-) : (0 _ : Context) -> TypeStatement -> Type where

  TVar : (fi : Info) ->
      InContext x ty gamma  ->
    --------------------------
     gamma |- Var fi x <:> ty
  
  TAbs : (fi : Info) -> -- Introduction rule for Arr
     (gamma :< (x,VarBind ty1)) |- tm2 <:> ty2  ->
  ------------------------------------------------ 
   gamma |- Abs fi1 x ty1 tm2 <:> Arr ty1 ty2

  TApp : (fi : Info) -> -- Elimination rule for Arr
    (gamma |- tm1 <:> Arr ty11 ty12) -> (gamma |- tm2 <:> ty11) ->
    -------------------------------------------------------------- 
                    gamma |- App fi tm1 tm2 <:> ty12

  TTrue : (fi : Info) ->
    -------------------------
    gamma |- True fi <:> Bool

  TFalse : (fi : Info) ->
    --------------------------
    gamma |- False fi <:> Bool

  TIf : (fi : Info) ->
    (gamma |- tmp <:> Bool) -> (gamma |- tmt <:> ty) -> (gamma |- tme <:> ty) ->
    ----------------------------------------------------------------------------
                     gamma |- (If fi tmp tmt tme <:> ty)

  TUnit : (fi : Info) ->
    -------------------------
    gamma |- Unit fi <:> Unit

  TSeq : (fi : Info) ->
    (gamma |- t1 <:> Unit) -> (gamma |- t2 <:> ty2) ->
    --------------------------------------------------
            gamma |- Seq fi t1 t2 <:> ty2

  TAscribe : (fi : Info) ->
        (gamma |- t1 <:> ty1)  ->
    -----------------------------
    gamma |- As fi t1 ty1 <:> ty1

  TLet : (fi : Info) ->
    (gamma |- (t1 <:> ty1)) -> ((gamma :< (x,VarBind ty1)) |- t2 <:> ty2) ->
    ------------------------------------------------------------------------
                       gamma |- Let fi x t1 t2 <:> ty2

  TPair : (fi : Info) ->
    (gamma |- (t1 <:> ty1)) -> (gamma |- (t2 <:> ty2)) ->
    -----------------------------------------------------
          gamma |- Pair fi t1 t2 <:> Product ty1 ty2

  TProj1 : (fi : Info) ->
    (gamma |- (t1 <:> Product ty1 ty2)) ->
    --------------------------------------
          gamma |- First fi t1 <:> ty1

  TProj2 : (fi : Info) ->
    (gamma |- (t1 <:> Product ty1 ty2)) ->
    --------------------------------------
         gamma |- Second fi t1 <:> ty2

  TTuple : (fi : Info) ->
           Derivations gamma ts tys     ->
    --------------------------------------
    gamma |- Tuple fi n ts <:> Tuple n tys

  TProj : (fi : Info) ->
             gamma |- t <:> Tuple n tys      ->
    -------------------------------------------
    gamma |- Proj fi t n i <:> Vect.index i tys

  TRcd : (fi : Info) ->
                  {fields : Vect n String} -> {u : UniqueNames n fields}          ->
                                Derivations gamma ts tys                          ->
    --------------------------------------------------------------------------------
    gamma |- Record fi (MkRecord n fields ts u) <:> Record (MkRecord n fields tys u)

  TRProj : (fi : Info) ->
    gamma |- t <:> Record (MkRecord n fields tys u) -> InRecord field ty fields tys ->
    ----------------------------------------------------------------------------------
                          gamma |- ProjField fi field t <:> ty

  TVariant : (fi : Info) ->
                                            {n : Nat} -> {nz : NonZero n}                                       ->
                                            {j : Nat} -> {ty : Ty}                                              ->
                  {tags : Vect n String} -> {tys : Vect n Ty} ->  {u : UniqueNames n tags} -> {tj : Tm}         -> 
                            Index tag j tags -> Index ty j tys -> (gamma |- tj <:> ty)                          ->
    --------------------------------------------------------------------------------------------------------------
      gamma |- Variant fi tag tj (Variant (MkVariant n tags tys u nz)) <:> (Variant (MkVariant n tags tys u nz))

  TCase : (fi : Info) ->
                                  {n : Nat} -> {nz : NonZero n}                           ->
        {tags : Vect n String} -> {u : UniqueNames n tags} -> {alts : Vect n (Name, Tm)}  ->
                                 {ty : Ty} -> {tys : Vect n Ty}                           ->
                      (gamma |- t0 <:> (Variant (MkVariant n tags tys u nz)))             ->
                                (VariantDerivations n gamma alts tys ty)                  ->
    ----------------------------------------------------------------------------------------
                       gamma |- Case fi t0 (MkVariant n tags alts u nz) <:> ty

  TFix : (fi : Info) ->
    (gamma |- t1 <:> (Arr ty ty)) ->
    --------------------------------
        gamma |- Fix fi t1 <:> ty

  TNil : (fi : Info) -> 
    ------------------------------
    gamma |- Nil fi ty <:> List ty
  
  TCons : (fi : Info) ->
    (gamma |- t1 <:> ty) -> (gamma |- t2 <:> List ty) ->
    ----------------------------------------------------
            gamma |- Cons fi ty t1 t2 <:> List ty

  TIsNil : (fi : Info) ->
       (gamma |- t <:> List ty)  ->
    -------------------------------
    gamma |- IsNil fi ty t <:> Bool

  THead : (fi : Info) ->
        (gamma |- t <:> List ty)  ->
    --------------------------------
      gamma |- Head fi ty t <:> ty

  TTail : (fi : Info) ->
          (gamma |- t <:> List ty)   ->
    -----------------------------------
      gamma |- Tail fi ty t <:> List ty
