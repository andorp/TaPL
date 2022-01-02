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

-- export
-- typeOf : (t : Tm) -> Value t -> (ty : Ty ** [<] |- t <:> ty)
-- typeOf = ?ty1

export
tupleProj
  :  {n : Nat}
  -> {tms : Vect n Tm}
  -> {tys : Vect n Ty}
  -> (i : Fin n)
  -> (Value (Tuple fi n tms))
  -> (tpDeriv : [<] |- (Tuple fi n tms <:> Tuple n tys))
  -> ([<] |- index i tms <:> index i tys)
tupleProj = ?tp1

export
replaceDerivations
  :  {n : Nat}
  -> {tms : Vect n Tm}
  -> {tys : Vect n Ty}
  -> (i : Fin n)
  -> (t' : Tm)
  -> ([<] |- t <:> index i tys)
  -> Derivations [<] tms tys
  -> Derivations [<] (replaceAt i t tms) tys
replaceDerivations = ?rd1

export
recordFieldType
  :  {n : Nat}
  -> (tms : Vect n Tm)
  -> (tys : Vect n Ty)
  -> (fields : Vect n String)
  -> (u : UniqueNames n fields)
  -> (fi : Info)
  -> (i : Fin n)
  -> (Value (Record fi (MkRecord n fields tms u)))
  -> (tDeriv : [<] |- (Record fi (MkRecord n fields tms u) <:> Record (MkRecord n fields tys u)))
  -> ([<] |- (index i tms <:> index i tys))
recordFieldType = ?rft 

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
