module TaPLc.Typing.Lemmas

import Data.Vect
import Data.Fin
import TaPLc.IR.Name
import TaPLc.IR.Info
import TaPLc.IR.Term
import TaPLc.IR.Type
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

export
caseEval
  :  {n : Nat}
  -> {nz : NonZero n}
  -> {tags : Vect n String}
  -> {tys : Vect n Ty}
  -> {u : UniqueNames n tags}
  -> (ty : Ty)
  -> (idx : Fin n)
  -> (alts : Vect n (String, Tm))
  -> (t0Deriv : [<] |- (Variant fi tag t (Variant (MkVariant n tags tys u nz)) <:> Variant (MkVariant n tags tys u nz)))
  -> ([<] |- (substituition (fst (index idx alts), t) (snd (index idx alts)) <:> ty))
caseEval = ?ce

export
fixEval
  :  (tDeriv : [<] |- (Abs fia va tya tma <:> Arr ty ty))
  -> ([<] |- (substituition (va, Fix fi (Abs fia va tya tma)) tma <:> ty))

export
application
  :  (t, t2 : Tm)
  -> (var : Name)
  -> (ty : Ty)
  -> (t1Deriv : [<] |- (t2 <:> ty11))
  -> (t2Deriv : [<] |- (Abs fi var ty11 t <:> Arr ty11 ty))
  -> ([<] |- (substituition (var, t2) t <:> ty))
application t t2 var ty t1Deriv t2Deriv = ?application_rhs

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
