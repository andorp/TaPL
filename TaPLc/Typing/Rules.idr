module TaPLc.Typing.Rules

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

%default total

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
  index
    :  {n : Nat} -> {gamma : Context} -> {tms : Vect n Tm} -> {tys : Vect n Ty}
    -> (i : Fin n)
    -> Derivations gamma tms tys
    -> (gamma |- (index i tms) <:> index i tys)
  index FZ     ((MkDerivation t ty deriv) :: xs) = deriv
  index (FS i) (x :: xs)                         = index i xs

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
                             {ty11 : Ty}                        ->
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

  TLet : (fi : Info) ->
                                {ty1 : Ty}                                ->
    (gamma |- (t1 <:> ty1)) -> ((gamma :< (x,VarBind ty1)) |- t2 <:> ty2) ->
    ------------------------------------------------------------------------
                       gamma |- Let fi x t1 t2 <:> ty2

  TTuple : (fi : Info) ->
           Derivations gamma ts tys     ->
    --------------------------------------
    gamma |- Tuple fi n ts <:> Tuple n tys

  TProj : (fi : Info) ->
                  {n : Nat} -> {i : Fin n} ->
                 {tys : Vect n Ty}           ->
             gamma |- t <:> Tuple n tys      ->
    -------------------------------------------
    gamma |- Proj fi t n i <:> Vect.index i tys

  TRcd : (fi : Info) ->
                  {fields : Vect n String} -> {u : UniqueNames n fields}          ->
                                Derivations gamma ts tys                          ->
    --------------------------------------------------------------------------------
    gamma |- Record fi (MkRecord n fields ts u) <:> Record (MkRecord n fields tys u)

  TRProj : (fi : Info) ->
                            {n : Nat}                       ->
                         {tys : Vect n Ty}                  -> 
                     {fields : Vect n String}               ->
                    {u : UniqueNames n fields}              ->
                         {idx : Fin n}                      ->
                    InNames idx field fields                ->
         gamma |- t <:> Record (MkRecord n fields tys u)    -> 
    ----------------------------------------------------------
      gamma |- ProjField fi field t <:> (Vect.index idx tys)

  TVariant : (fi : Info) ->
                                                    (idx : Fin n)                                            -> 
                                                  InNames idx tg tgs                                         ->
                                        gamma |- tj <:> Vect.index idx tys                                   ->
    -----------------------------------------------------------------------------------------------------------
      gamma |- Variant fi tg tj (Variant (MkVariant n tgs tys u nz)) <:> (Variant (MkVariant n tgs tys u nz))

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
