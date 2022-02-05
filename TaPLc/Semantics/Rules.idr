module TaPLc.Semantics.Rules

import Data.List
import Data.Vect

import TaPLc.IR.Term
import TaPLc.IR.Type
import TaPLc.IR.Info
import TaPLc.IR.Name
import TaPLc.IR.Record
import TaPLc.IR.Variant
import TaPLc.IR.UniqueNames
import TaPLc.Data.Vect
import TaPLc.Semantics.Substituition
import TaPLc.IR.FFI

namespace FFI
  public export
  data FFIConv : Tm -> FFIVal b -> Type where -- TODO
    True   : FFIConv (True fi)  (MkFFIVal "Builtin.Bool" so) 
    False  : FFIConv (False fi) (MkFFIVal "Builtin.Bool" so)
    FFIVal : FFIConv (FFIVal fi v) v

public export
data Evaluation : (0 _ : Tm) -> (0 _ : Tm) -> Type where

  EApp1 :
                  Not (Value t1)           ->
                Evaluation t1 t1'          ->
    -----------------------------------------
    Evaluation (App fi t1 t2) (App fi t1' t2)
  
  EApp2 :
                      Value v1           ->
                   Not (Value t)         ->
                  Evaluation t t'        ->
    ---------------------------------------            
    Evaluation (App fi v1 t) (App fi v1 t')

  EAppAbs :
                            Value v                          ->
    -----------------------------------------------------------
    Evaluation (App fi1 (Abs fi2 x ty t) v) (substituition v t)


  ESeq :
                  Not (Value t1)           ->
                Evaluation t1 t1'          ->
    -----------------------------------------
    Evaluation (Seq fi t1 t2) (Seq fi t1' t2)

  ESeqNext :
    -------------------------------------
    Evaluation (Seq fi1 (Unit fi2) t2) t2

  ELetV :
                        Value v                  ->
    -----------------------------------------------
    Evaluation (Let fi x v t2) (substituition v t2)

  ELet :
                   Not (Value t)             ->
                  Evaluation t t'            ->
    -------------------------------------------
    Evaluation (Let fi x t t2) (Let fi c t' t2)

  EProjTuple :
                   Value (Tuple fi2 n tms)                      ->
    --------------------------------------------------------------
    Evaluation (Proj fi1 (Tuple fi2 n tms) n j) (Vect.index j tms)

  EProj :
                   Not (Value t)             ->
                  Evaluation t t'            ->
    -------------------------------------------
    Evaluation (Proj fi t n i) (Proj fi t' n i)

  ETuple :
                          {z : Nat} -> {zs : Vect z Tm}               ->
                                (idx : Fin z)                         ->
                    ForEach (Vect.Take.take idx zs) Value             ->
                        Not (Value (Vect.index idx zs))               ->
                      Evaluation (Vect.index idx zs) t'               ->
    --------------------------------------------------------------------
     Evaluation (Tuple fi z zs) (Tuple fi z (Vect.replaceAt idx t' zs))

  EProjRec :
                {r : Record Tm}             ->
              {idx : Fin r.size}            ->
        {inr : InNames idx field r.fields}  ->
          (vs : ForEach r.values Value)     ->
    ------------------------------------------
      Evaluation
        (ProjField fi1 field (Record fi2 r))
        (Vect.index idx r.values)

  EProjField :
                         Not (Value t)                     ->
                        Evaluation t t'                    ->
    ---------------------------------------------------------
    Evaluation (ProjField fi field t) (ProjField fi field t')

  ERcd :
                                 {n : Nat}                           ->
              {names : Vect n String} -> {fields : Vect n Tm}        ->
                        {u : UniqueNames n names}                    ->
                              (idx : Fin n)                          ->
                  ForEach (Vect.Take.take idx fields) Value          ->
                     Not (Value (Vect.index idx fields))             ->
                    Evaluation (Vect.index idx fields) t'            ->
    -------------------------------------------------------------------
     Evaluation
       (Record fi (MkRecord n names fields u))
       (Record fi (MkRecord n names (Vect.replaceAt idx t' fields) u))

  ECase :
                    Not (Value t)              ->
                   Evaluation t t'             ->
    ---------------------------------------------
    Evaluation (Case fi t tgs) (Case fi t' tgs)

  EVariant :
                         Not (Value t)                   ->
                        Evaluation t t'                  ->
    -------------------------------------------------------
    Evaluation (Variant fi tag t ty) (Variant fi tag t' ty)

  ECaseVariant :
                            (idx : Fin n)                            ->
                          InNames idx tg tgs                         ->
    -------------------------------------------------------------------
      Evaluation
        (Case fi1 (Variant fi2 tg vj ty) (MkVariant n tgs alts u nz))
        (substituition vj (Builtin.snd (index idx alts)))

  EFix :
              Not (Value t)        ->
             Evaluation t t'       ->
    ---------------------------------
    Evaluation (Fix fi t) (Fix fi t')

  EFixBeta :
    ------------------------------------------------
    Evaluation
      (Fix fi1 (Abs fi2 x ty tm))
      (substituition (Fix fi1 (Abs fi2 x ty tm)) tm)

  ECons1 :
                     Not (Value t1)                ->
                    Evaluation t1 t1'              ->
    -------------------------------------------------
    Evaluation (Cons fi ty t1 t2) (Cons fi ty t1' t2)

  ECons2 :
                      (Value t1)                   ->
                     Not (Value t2)                ->
                    Evaluation t2 t2'              ->
    -------------------------------------------------
    Evaluation (Cons fi ty t1 t2) (Cons fi ty t1 t2')

  -- Why do we need ty1 and ty2?
  EIsNilNil :
    ---------------------------------------------------
    Evaluation (IsNil fi1 ty1 (Nil fi2 ty2)) (True fi1)
  
  -- Why do we need ty1 and ty2?
  EIsNilCons :
                            (Value t1)                       ->
                            (Value t2)                       ->
    -----------------------------------------------------------
    Evaluation (IsNil fi1 ty1 (Cons fi2 ty2 t1 t2)) (False fi1)

  EIsNil :
                     Not (Value t)               ->
                    Evaluation t t'              ->
    -----------------------------------------------
      Evaluation (IsNil fi ty t) (IsNil fi ty t')

  -- Why do we need ty1 and ty2?
  EHeadCons :
                       (Value t1)                  ->
                       (Value t2)                  ->
    -------------------------------------------------
    Evaluation (Head fi1 ty1 (Cons fi2 ty2 t1 t2)) t1

  EHead :
                  Not (Value t)            ->
                 Evaluation t t'           ->
    -----------------------------------------
    Evaluation (Head fi ty t) (Head fi ty t')

  -- Why do we need ty1 and ty2?
  ETailCons :
                      (Value t1)                   ->
                      (Value t2)                   ->
    -------------------------------------------------
    Evaluation (Tail fi1 ty1 (Cons fi2 ty2 t1 t2)) t2

  ETail :
                   Not (Value t)           ->
                  Evaluation t t'          ->
    -----------------------------------------
    Evaluation (Tail fi ty t) (Tail fi ty t')

  EIfTrue :
    ---------------------------------------
    Evaluation (If fi1 (True fi2) t2 t3) t2
  
  EIfFalse :
    ----------------------------------------
    Evaluation (If fi1 (False fi2) t2 t3) t3
  
  EIf :
                    Not (Value t1)             ->
                  Evaluation t1 t1'            ->
    ---------------------------------------------
    Evaluation (If fi t1 t2 t3) (If fi t1' t2 t3)

  EFFICallArg :
                              (idx : Fin n)                         ->
                ForEach (Vect.Take.take idx args) Value             ->
                    Not (Value (Vect.index idx args))               ->
                   Evaluation (Vect.index idx args) t'              ->
    ------------------------------------------------------------------
    Evaluation (FFI fi c args) (FFI fi c (Vect.replaceAt idx t' args))
  
  EFFICall :
    ------------------------------------------------------------------------------
    Evaluation (FFI fi (MkFFICall f n pms ret) args) (FFIVal fi (MkFFIVal ret so))

  EConvert :
                               Not (Value t)                       ->
                              Evaluation t t'                      ->
    -----------------------------------------------------------------
    Evaluation (ConvertFFI fi baseType t) (ConvertFFI fi baseType t')
  
  EConvertVal :
                                     Value t                              ->
                                      FFI t                               ->
                      FFIConv t (MkFFIVal baseType so)                    ->
    ------------------------------------------------------------------------
    Evaluation (ConvertFFI fi baseType t) (FFIVal fi (MkFFIVal baseType so))
