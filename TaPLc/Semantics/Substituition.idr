module TaPLc.Semantics.Substituition

import TaPLc.IR.Context
import TaPLc.IR.Type
import TaPLc.IR.Info
import TaPLc.IR.Term
import TaPLc.IR.Record
import TaPLc.IR.Variant
import TaPLc.IR.FFI
import TaPLc.IR.Name
import TaPLc.Typing.Rules
import Data.Vect

%default total

public export
rename : (Nat -> Nat) -> Tm -> Tm
rename f (True fi) = True fi
rename f (False fi) = False fi
rename f (If fi p t e) = If fi (rename f p) (rename f t) (rename f e)
rename f (Var fi k v) = Var fi (f k) v
rename f (Abs fi v ty t) = Abs fi v ty (rename (extend f) t)
rename f (App fi t1 t2) = App fi (rename f t1) (rename f t2)
rename f (Unit fi) = Unit fi
rename f (Seq fi t1 t2) = Seq fi (rename f t1) (rename f t2)
rename f (Let fi n t b) = Let fi n (rename f t) (rename (extend f) t)
rename f (Tuple fi n ti) = Tuple fi n (assert_total (map (rename f) ti))
rename f (Proj fi t n i) = Proj fi (rename f t) n i
rename f (Record fi x) = Record fi (assert_total (map (rename f) x))
rename f (ProjField fi field t) = ProjField fi field (rename f t)
rename f (Variant fi tag t ty) = Variant fi tag (rename f t) ty
rename f (Case fi t alts) = Case fi (rename f t) (assert_total (map (mapSnd (rename (extend f))) alts))
rename f (Fix fi t) = Fix fi (rename f t)
rename f (Nil fi ty) = Nil fi ty
rename f (Cons fi ty h t) = Cons fi ty (rename f h) (rename f t)
rename f (IsNil fi ty t) = IsNil fi ty (rename f t)
rename f (Head fi ty t) = Head fi ty (rename f t)
rename f (Tail fi ty t) = Tail fi ty (rename f t)
rename f (LitNat fi literal) = LitNat fi literal
rename f (ConvertFFI fi baseType x) = ConvertFFI fi baseType (rename f x)
rename f (FFI fi x args) = FFI fi x (assert_total (map (rename f) args))
rename f (FFIVal fi x) = FFIVal fi x

-- public export
record Variable where
  constructor MkVariable
  name : Name
  info : Info
  idx  : Nat

-- public export
extendSubst : (Variable -> Tm) -> Variable -> Tm
extendSubst f (MkVariable n i 0) = Var i 0 n
extendSubst f (MkVariable n i (S x))
  = rename S 
  $ assert_total -- As x is smaller than (S x) and the recursion will stop at 0
  $ extendSubst f (MkVariable n i x)

-- public export
subst : (Variable -> Tm) -> Tm -> Tm
subst f (True fi) = True fi
subst f (False fi) = False fi
subst f (If fi p t e) = If fi (subst f p) (subst f t) (subst f e)
subst f (Var fi k v) = f (MkVariable v fi k)
subst f (Abs fi var ty t) = Abs fi var ty (subst (extendSubst f) t)
subst f (App fi t1 t2) = App fi (subst f t1) (subst f t2)
subst f (Unit fi) = Unit fi
subst f (Seq fi t1 t2) = ?subst_rhs_8
subst f (Let fi n t b) = ?subst_rhs_9
subst f (Tuple fi n ti) = ?subst_rhs_10
subst f (Proj fi t n i) = ?subst_rhs_11
subst f (Record fi x) = ?subst_rhs_12
subst f (ProjField fi field t) = ?subst_rhs_13
subst f (Variant fi tag t ty) = ?subst_rhs_14
subst f (Case fi t alts) = ?subst_rhs_15
subst f (Fix fi t) = ?subst_rhs_16
subst f (Nil fi ty) = Nil fi ty
subst f (Cons fi ty h t) = ?subst_rhs_18
subst f (IsNil fi ty t) = ?subst_rhs_19
subst f (Head fi ty t) = ?subst_rhs_20
subst f (Tail fi ty t) = ?subst_rhs_21
subst f (LitNat fi literal) = ?subst_rhs_22
subst f (ConvertFFI fi baseType x) = ?subst_rhs_23
subst f (FFI fi x args) = ?subst_rhs_24
subst f (FFIVal fi x) = FFIVal fi x

-- Issue in Idris, if this is defined as local function under substituition, I get a completely
-- different things in the iff Lemma.
singleVar : Tm -> Variable -> Tm
singleVar s (MkVariable n i Z) = s
singleVar s (MkVariable n i (S x)) = Var i x n

export
substituition : Tm -> Tm -> Tm
substituition s t = subst (singleVar s) t
