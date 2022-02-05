module TaPLc.Typing.Lemmas

import Data.Vect
import Data.Fin
import TaPLc.IR.Name
import TaPLc.IR.Info
import TaPLc.IR.Term
import TaPLc.IR.Type
import TaPLc.IR.FFI
import TaPLc.IR.Context
import TaPLc.IR.Record
import TaPLc.IR.Variant
import TaPLc.Typing.Rules
import TaPLc.Semantics.Substituition

%default total

{-
-- Typing lemmas which are needed in the certified evaluator. With these lemmas we make sure,
-- that the term rewriting in the evaluator creates well typed terms, which makes sure
-- that the evaluation process can take another small step, and eventually terminate.
-}

export
tupleProj
  :  {n : Nat}
  -> {tms : Vect n Tm}
  -> {tys : Vect n Ty}
  -> (i : Fin n)
  -> (tpDeriv : [<] |- (Tuple fi n tms <:> Tuple n tys))
  -> ([<] |- index i tms <:> index i tys)
tupleProj FZ      (TTuple fi (d :: ds)) = case d of (MkDerivation t ty deriv) => deriv
tupleProj (FS y)  (TTuple fi (d :: ds)) = tupleProj y (TTuple fi ds)

export
replaceDerivations
  :  {n : Nat}
  -> {tms : Vect n Tm}
  -> {tys : Vect n Ty}
  -> (i : Fin n)
  -> (t : Tm)
  -> ([<] |- t <:> index i tys)
  -> Derivations [<] tms tys
  -> Derivations [<] (replaceAt i t tms) tys
replaceDerivations FZ     t x (d :: ds) = case d of (MkDerivation r ty rderiv) => MkDerivation t ty x :: ds
replaceDerivations (FS w) t x (d :: ds) = d :: (replaceDerivations w t x ds)

export
recordFieldType
  :  {n : Nat}
  -> {tms : Vect n Tm}
  -> {tys : Vect n Ty}
  -> {fields : Vect n String}
  -> {u : UniqueNames n fields}
  -> (i : Fin n)
  -> (tDeriv : [<] |- (Record fi (MkRecord n fields tms u) <:> Record (MkRecord n fields tys u)))
  -> ([<] |- (index i tms <:> index i tys))
recordFieldType FZ     (TRcd fi (d :: ds)) = case d of (MkDerivation t ty deriv) => deriv
recordFieldType (FS z) (TRcd fi {fields = f :: fs} {u = u0 :: us} (d :: ds)) = recordFieldType {fields = fs} {u = us} z (TRcd fi ds)

extend0
  :  (t : Tm)
  -> ( gamma       |- t            <:> ty)
  -> ((gamma :< g) |- shiftPos 1 t <:> ty)
extend0 _ _ = ?exten0x

-- substInAbs0
--   :  (sDeriv : (gamma                       :< (x, VarBind ty1)) |- (shiftPos 1 s <:> tty))
--   -> (tDeriv : (gamma :< (var, VarBind tty) :< (x, VarBind ty1)) |- (tm2 <:> ty2))
--   -> gamma |- Abs fi x ty1 (subst 1 (shiftPos 1 s) tm2) <:> Arr ty1 ty2
-- substInAbs0 sDeriv tDeriv2 = ?extend31

substInAbs1
  :  (s, tm2 : Tm)
  -> (sDeriv : (gamma                       :< (x, VarBind ty1)) |- (shiftPos 1 s <:> tty))
  -> (tDeriv : (gamma :< (var, VarBind tty) :< (x, VarBind ty1)) |- (tm2 <:> ty2))
  -> (gamma :< (var, VarBind tty) :< (x, VarBind ty1)) |- (subst 1 (shiftPos 1 (shiftPos 1 s)) tm2) <:> ty2

-- abstr0
--   :  gamma |- (Abs fi x ty1 (subst 1 (shiftPos 1 s) tm2) <:> Arr ty1 ty2)
--   -> gamma |- (subst 0 s (Abs fi x ty1 tm2) <:> Arr ty1 ty2)
-- abstr0 deriv = rewrite (Substituition.substAbsLemma fi x ty1 0 s tm2) in deriv

--  0 v3 : String
--  0 ty3 : Ty
--  0 gamma : Context
--    tm2 : Tm
--    ty1 : Ty
--    v : String
--    tm2Deriv : ((gamma :< (v3, VarBind ty3)) :< (v, VarBind ty1)) |- (tm2 <:> ty2)
--    fi : Info
--    s : Tm
--    sDeriv : gamma |- (s <:> ty3)
--  0 ty2 : Ty
-- ------------------------------
-- xxx
--   :  gamma |- (subst 1 (shiftPos 1 (shiftPos 1 s)) tm2 <:> ty2)
--   -> ((gamma :< (v3, VarBind ty3)) :< (v, VarBind ty1)) |- (subst 1 (shiftPos 1 (shiftPos 1 s)) tm2 <:> ty2)

  -- TAbs : (fi : Info) -> -- Introduction rule for Arr
  --    (gamma :< (x,VarBind ty1)) |- tm2 <:> ty2  ->
  -- ------------------------------------------------ 
  --    gamma |- Abs fi x ty1 tm2 <:> Arr ty1 ty2

subst0
  :  (s, t : Tm)
  -> (sDeriv : gamma                        |- (s <:> ty3))
  -> (tDeriv : (gamma :< (v3, VarBind ty3)) |- (t <:> ty2))
  -> ((gamma :< (v3, VarBind ty3)) |- (subst 0 (shiftPos 1 s) t) <:> ty2)
subst0 s (Var fi v n) sDeriv (TVar fi x) = ?subst0_rhs_1

subst0 s (Abs fi v ty1 tm2) sDeriv (TAbs fi tm2Deriv) =
  rewrite (substAbsLemma fi v ty1 0 (shiftPos 1 s) tm2)
  in (TAbs fi (substInAbs1 s tm2 (extend0 _ sDeriv) tm2Deriv))

-- subst0 s (Abs fi v ty1 tm2) sDeriv (TAbs fi tm2Deriv) = case subst0 (shiftPos 1 s) tm2 (extend0 _ sDeriv) (?xxx tm2Deriv) of
--   pat => ?helpx

-- ------------------------------
-- xxx
--  :  ((gamma :< (v3, VarBind ty3)) :< (v, VarBind ty1)) |- (tm2 <:> ty2)
--  -> ((gamma :< ?g) :< (?v3, VarBind ty3)) |- (tm2 <:> ?ty2)

subst0 s (App fi tm1 tm2) sDeriv (TApp fi x y) = ?subst0_rhs_3
subst0 s (True fi) sDeriv (TTrue fi) = rewrite (SubstLemma.true0 fi 0 (shiftPos 1 s)) in (TTrue fi)
subst0 s (False fi) sDeriv (TFalse fi) = ?subst0_rhs_5
subst0 s (If fi tmp tmt tme) sDeriv (TIf fi x y z) = ?subst0_rhs_6
subst0 s (Unit fi) sDeriv (TUnit fi) = ?subst0_rhs_7
subst0 s (Seq fi t1 t2) sDeriv (TSeq fi x y) = ?subst0_rhs_8
subst0 s (Let fi v t1 t2) sDeriv (TLet fi x y) = ?subst0_rhs_9
subst0 s (Tuple fi n ts) sDeriv (TTuple fi x) = ?subst0_rhs_10
subst0 s (Proj fi t n i) sDeriv (TProj fi x) = ?subst0_rhs_11
subst0 s (Record fi (MkRecord n fields ts u)) sDeriv (TRcd fi x) = ?subst0_rhs_12
subst0 s (ProjField fi field t) sDeriv (TRProj fi x y) = ?subst0_rhs_13
subst0 s (Variant fi tg tj (Variant (MkVariant n tgs tys u nz))) sDeriv (TVariant fi idx x y) = ?subst0_rhs_14
subst0 s (Case fi t0 (MkVariant n tags alts u nz)) sDeriv (TCase fi x y) = ?subst0_rhs_15
subst0 s (Fix fi t1) sDeriv (TFix fi x) = ?subst0_rhs_16
subst0 s ([] fi ty) sDeriv (TNil fi) = ?subst0_rhs_17
subst0 s (Cons fi ty t1 t2) sDeriv (TCons fi x y) = ?subst0_rhs_18
subst0 s (IsNil fi ty t) sDeriv (TIsNil fi x) = ?subst0_rhs_19
subst0 s (Head fi ty2 t) sDeriv (THead fi x) = ?subst0_rhs_20
subst0 s (Tail fi ty t) sDeriv (TTail fi x) = ?subst0_rhs_21
subst0 s (LitNat fi l) sDeriv (TLitNat fi) = ?subst0_rhs_22
subst0 s (FFI fi (MkFFICall fun n pms ret) args) sDeriv (TFFICall fi x) = ?subst0_rhs_23
subst0 s (FFIVal fi (MkFFIVal baseType sn)) sDeriv (TFFIVal fi) = ?subst0_rhs_24
subst0 s (ConvertFFI fi baseType t) sDeriv (TConvertFFI fi x y) = ?subst0_rhs_25

subst1
  :  (gamma |- (s <:> sty))
  -> ((gamma :< (var, VarBind sty)) |- (t <:> ty))
  -> (gamma |- (shiftNeg (subst 0 (shiftPos 1 s) t)) <:> ty)
subst1 sDeriv tDeriv = ?subst1x

subst2
  :  (sDeriv : ([<]                        |- (s <:> tty)))
  -> (tDeriv : ([<] :< (var, VarBind tty)) |- (t <:> ty))
  -> [<] |- (substituition s t <:> ty)
subst2 sDeriv tDeriv = rewrite (substituitionLemma s t) in (subst1 sDeriv tDeriv)

-- partial -- TODO
export
caseEval
  :  {n : Nat}
  -> {tys : Vect n Ty}
  -> (ty : Ty)
  -> (idx : Fin n)
  -> (alts : Vect n (String, Tm))
  -> (variantDerivs : VariantDerivations n [<] alts tys ty)
  -> (tDeriv : [<] |- (t <:> index idx tys))
  -> ([<] |- (substituition t (snd (index idx alts)) <:> ty))
caseEval ty FZ ((var, t1) :: ts)    ((::) {tty} (MkDerivation t1 ty deriv) y) tDeriv = subst2 tDeriv deriv
caseEval ty (FS z) ((var, t) :: ts) (x :: y)                                  tDeriv = caseEval ty z ts y tDeriv

export
fixEval
  :  (fib : Info)
  -> (tDeriv : [<] |- (Abs fia va tya tma <:> Arr ty ty))
  -> ([<] |- (substituition (Fix fib (Abs fia va tya tma)) tma <:> ty))
fixEval fib tDeriv@(TAbs fi tmaDeriv) = subst2 (TFix fib tDeriv) tmaDeriv

export
application
  :  (t, t2 : Tm)
  -> (var : Name)
  -> (ty : Ty)
  -> (t1Deriv : [<] |- (t2 <:> ty11))
  -> (t2Deriv : [<] |- (Abs fi var ty11 t <:> Arr ty11 ty))
  -> ([<] |- (substituition t2 t <:> ty))
application t t2 var ty t2Deriv (TAbs fi tDeriv) = subst2 t2Deriv tDeriv

||| Substituition doesn't change the type of the term.
export
substituition
  :  (t1, t2 : Tm)
  -> (x1 : Name)
  -> (ty1, ty2 : Ty)
  -> (t1Deriv : [<] |- (t1 <:> ty1))
  -> (t2Deriv : ([<] :< (x1, VarBind ty1)) |- (t2 <:> ty2))
  -> ([<] |- substituition t1 t2 <:> ty2)
substituition _ _ _ _ _ t1Deriv t2Deriv = subst2 t1Deriv t2Deriv

export
headEval
  :  (tDeriv : [<] |- (Cons fi ty hd tl <:> List ty))
  -> ([<] |- (hd <:> ty))
headEval (TCons _ x y) = x

export
tailType
  :  (tDeriv : [<] |- (Cons fi2 ty1 hd tl <:> List ty))
  -> ([<] |- (tl <:> List ty))
tailType (TCons _ x y) = y
