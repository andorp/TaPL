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

subst2
  :  (sDeriv : ([<]                        |- (s <:> tty)))
  -> (tDeriv : ([<] :< (var, VarBind tty)) |- (t <:> ty))
  -> [<] |- (substituition s t <:> ty)
subst2 sDeriv tDeriv = ?xsubst2

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
