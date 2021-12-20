module TaPLc.Semantics.Evaluation

import Data.Vect

import TaPLc.IR.Term
import TaPLc.IR.Type
import TaPLc.IR.Info
import TaPLc.IR.Name
import TaPLc.IR.Record
import TaPLc.IR.Variant
import TaPLc.IR.UniqueNames
import TaPLc.Data.Vect

-- Substituition assumes unique names, no need for alpha conversions.
-- TODO: Check if this right.
total
substituition : (Name, Tm) -> Tm -> Tm
-- substituition (n, tm1) (Var var) = case decEq n var of
--   (Yes prf)   => tm1
--   (No contra) => (Var var)
-- substituition s (Abs var ty t) = Abs var ty (substituition s t)
-- substituition s (App t1 t2) = App (substituition s t1) (substituition s t2)
-- substituition s True = True
-- substituition s False = False

namespace InVariant

  public export
  data InVariant : String -> Name -> Tm -> Vect n String -> Vect n (Name,Tm) -> Type where
    Here  : InVariant tag x tm (tag :: tags) ((x,tm) :: alts)
    There : InVariant tag x tm tags alts -> InVariant tag x tm (tah :: tags) ((y,tn) :: alts)


data Evaluation : Tm -> Tm -> Type where

  EApp1 :
                Evaluation t1 t1'          ->
    -----------------------------------------
    Evaluation (App fi t1 t2) (App fi t1' t2)
  
  EApp2 :
                      Value v1           ->
                  Evaluation t t'        ->
    ---------------------------------------            
    Evaluation (App fi v1 t) (App fi v1 t')

  EAppAbs :
                                Value v                          ->
    ---------------------------------------------------------------
    Evaluation (App fi1 (Abs fi2 x ty t) v) (substituition (x,v) t)
  
  ESeq :
                Evaluation t1 t1'          ->
    -----------------------------------------
    Evaluation (Seq fi t1 t2) (Seq fi t1' t2)

  ESeqNext :
    -------------------------------------
    Evaluation (Seq fi1 (Unit fi2) t2) t2

  EAscribeV :
             Value v       ->
    -------------------------
    Evaluation (As fi v ty) v 

  EAscribe :
               Evaluation t t'         ->
    -------------------------------------
    Evaluation (As fi t ty) (As fi t' ty)

  ELetV :
                          Value v                    ->
    ---------------------------------------------------
    Evaluation (Let fi x v t2) (substituition (x,v) t2)
  
  ELet :
                  Evaluation t t'            ->
    -------------------------------------------
    Evaluation (Let fi x t t2) (Let fi c t' t2)

  EProjTuple :
                   Value (Tuple fi2 n tms)                      ->
    --------------------------------------------------------------
    Evaluation (Proj fi1 (Tuple fi2 n tms) n j) (Vect.index j tms)

  EProj :
                  Evaluation t t'            ->
    -------------------------------------------
    Evaluation (Proj fi t n i) (Proj fi t' n i)

  ETuple :
                  {n,m : Nat} -> {vs : Vect n Tm} -> {t : Tm} -> {ts : Vect m Tm}                  ->
                                ForEach vs Value -> Evaluation t t'                                ->
    -------------------------------------------------------------------------------------------------
      Evaluation
        (Tuple fi (n + (1 + m)) (vs ++ (t :: ts)))
        (Tuple fi (n + (1 + m)) (vs ++ (t' :: ts)))

  EProjRec :
    {r : Record Tm} -> {inr : InRecord field v r.fields r.values}  ->
                        (vs : ForEach r.values Value)              ->
    -----------------------------------------------------------------                        
             Evaluation (ProjField fi1 field (Record fi2 r)) v

  EProjField :
                        Evaluation t t'                    ->
    ---------------------------------------------------------
    Evaluation (ProjField fi field t) (ProjField fi field t')

  ERcd :
                 {n,m : Nat}                                                           ->
                 {lvs : Vect n String} -> {f : String} -> {lts : Vect m String}        ->
                 {vs  : Vect n   Tm  } -> {t :   Tm  } -> {ts  : Vect m   Tm  }        ->
                      {u : UniqueNames (n + (1 + m)) (lvs ++ (f :: lts))}              ->
                           ForEach vs Value -> Evaluation t t'                         ->
    -------------------------------------------------------------------------------------
        Evaluation
          (Record fi (MkRecord (n + (1 + m)) (lvs ++ (f :: lts)) (vs ++ (t  :: ts)) u))
          (Record fi (MkRecord (n + (1 + m)) (lvs ++ (f :: lts)) (vs ++ (t' :: ts)) u))

  ECase :
                   Evaluation t0 t0'             ->
    -----------------------------------------------
    Evaluation (Case fi t0 tags) (Case fi t0' tags)

  EVariant :
                        Evaluation t t'                  ->
    -------------------------------------------------------
    Evaluation (Variant fi tag t ty) (Variant fi tag t' ty)

  ECaseVariant :
                             {n : Nat} -> {nz : NonZero n}                            ->
    {tags : Vect n String} -> {alts : Vect n (Name, Tm)} -> {u : UniqueNames n tags}  ->
                              ForEach alts (Value . snd)                              ->
                              InVariant tag x vj tags alts                            ->
    ------------------------------------------------------------------------------------
              Evaluation
                (Case fi1 (Variant fi2 tag t ty) (MkVariant n tags alts u nz))
                (substituition (x,vj) tj)

  EFix :
             Evaluation t t'       ->
    ---------------------------------
    Evaluation (Fix fi t) (Fix fi t')

  EFixBeta :
    ----------------------------------------------------------------------------------------
    Evaluation (Fix fi1 (Abs fi2 x ty tm)) (substituition (x, Fix fi1 (Abs fi2 x ty tm)) tm)

  ECons1 :
                    Evaluation t1 t1'              ->
    -------------------------------------------------
    Evaluation (Cons fi ty t1 t2) (Cons fi ty t1' t2)

  ECons2 :
                     {v1 : Value t1}               ->
                    Evaluation t2 t2'              ->
    -------------------------------------------------
    Evaluation (Cons fi ty t1 t2) (Cons fi ty t1 t2')

  EIsNilNil :
    ---------------------------------------------------
    Evaluation (IsNil fi1 ty1 (Nil fi2 ty2)) (True fi1)
  
  EIsNilCons :
                {v1 : Value t1} -> {v2 : Value t2}           ->
    -----------------------------------------------------------
    Evaluation (IsNil fi1 ty1 (Cons fi2 ty2 t1 t2)) (False fi1)

  EIsNil :
                    Evaluation t t'              ->
    -----------------------------------------------
      Evaluation (IsNil fi ty t) (IsNil fi ty t')

  EHeadCons :
                    {v1 : Value t1}                ->
    -------------------------------------------------
    Evaluation (Head fi1 ty1 (Cons fi2 ty2 t1 t2)) t1

  EHead :
                 Evaluation t t'           ->
    -----------------------------------------
    Evaluation (Head fi ty t) (Head fi ty t')

  ETailCons :
            {v1 : Value t1} -> {v2 : Value t2}     ->
    -------------------------------------------------
    Evaluation (Tail fi1 ty1 (Cons fi2 ty1 t1 t2)) t2

  ETail :
                  Evaluation t t'          ->
    -----------------------------------------
    Evaluation (Tail fi ty t) (Tail fi ty t')
