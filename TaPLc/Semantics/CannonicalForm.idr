{-
Cannonical forms draws a connection between terms that are values of certain type must have certain form.
For example A Boolean value must be True or False. We use this property during the evaluation of a term,
where the evaluation relation is represented as a tree and in the leaves it must refer to values.
-}

module TaPLc.Semantics.CannonicalForm

import Data.Vect

import TaPLc.IR.Term
import TaPLc.IR.Name
import TaPLc.IR.Type
import TaPLc.IR.Info
import TaPLc.IR.UniqueNames
import TaPLc.IR.Record
import TaPLc.IR.Variant
import TaPLc.Data.Vect
import TaPLc.IR.Context
import TaPLc.Typing.Rules
import TaPLc.IR.FFI

%default total

public export
CFBool : Tm -> Type
CFBool t = (Either (fi : Info ** t = True fi) (fi : Info ** t = False fi))

public export
CFArr : Tm -> Ty -> Type
CFArr t ty1 = (fi : Info ** (var : Name ** (t2 : Tm ** t = Abs fi var ty1 t2)))

public export
CFUnit : Tm -> Type
CFUnit t = (fi : Info ** t = Unit fi)

public export
CFTuple : Tm -> Type
CFTuple t = (fi : Info ** (n : Nat ** (tms : Vect n Tm ** t = Tuple fi n tms)))

public export
CFRecord : Tm -> Type
CFRecord t =
  (fi : Info                 **
  (s  : Nat                  **
  (fs : Vect s String        **
  (vs : Vect s Tm            **
  (u : UniqueNames s fs      **
  (t = Term.Record fi (MkRecord s fs vs u)))))))

public export
CFVariant : Tm -> Type
CFVariant t =
  (fi  : Info                     **
  (tag : String                   **
  (s   : Tm                       **
  (ty  : Ty                       **
  (t = Term.Variant fi tag s ty)))))

public export
CFList : Tm -> Type
CFList t = Either
            (fi : Info ** (ty : Ty ** t = Nil fi ty))
            (fi : Info ** (ty : Ty ** (hd : Tm ** (tl : Tm ** (t = Cons fi ty hd tl)))))

public export
CFBase : BaseType -> Tm -> Type
CFBase baseType t = (fi : Info ** (sn : Nat ** t = FFIVal fi (MkFFIVal baseType sn)))

public export
CFLitNat : Tm -> Type
CFLitNat t = (fi : Info ** (l : Nat ** t = LitNat fi l))

public export
CanonicalFormTy : (t : Tm) -> (ty : Ty) -> Type
CanonicalFormTy t Bool          = CFBool    t
CanonicalFormTy t (Arr ty1 ty2) = CFArr t ty1
CanonicalFormTy t Unit          = CFUnit    t
CanonicalFormTy t (Tuple n xs)  = CFTuple   t
CanonicalFormTy t (Record r)    = CFRecord  t
CanonicalFormTy t (Variant v)   = CFVariant t
CanonicalFormTy t (List x)      = CFList    t
CanonicalFormTy t LitNat        = CFLitNat  t
CanonicalFormTy t (Base n)      = CFBase  n t

public export
cannonicalForms : (t : Tm) -> (v : Value t) -> (ty : Ty) -> (gamma |- (t <:> ty)) -> CanonicalFormTy t ty
cannonicalForms (Abs fi1 x1 ty1 tm2) v (Arr ty1 ty2) (TAbs fi x)
  = MkDPair fi1 (MkDPair x1 (MkDPair tm2 Refl))
cannonicalForms (True fi) v Bool (TTrue fi)
  = Left (MkDPair fi Refl)
cannonicalForms (False fi) v Bool (TFalse fi)
  = Right (MkDPair fi Refl)
cannonicalForms (Unit fi) v Unit (TUnit fi)
  = MkDPair fi Refl
cannonicalForms (Tuple fi n ts) v (Tuple n tys) (TTuple fi x)
  = MkDPair fi (MkDPair n (MkDPair ts Refl))
cannonicalForms (Nil fi ty) v (List ty) (TNil fi)
  = Left (MkDPair fi (MkDPair ty Refl))
cannonicalForms (Cons fi ty t1 t2) (Cons hv tv) (List ty) (TCons fi x y)
  = Right (MkDPair fi (MkDPair ty (MkDPair t1 (MkDPair t2 Refl))))
cannonicalForms
  (Record fi (MkRecord n fields ts u)) v (Record (MkRecord n fields tys u)) (TRcd fi x)
  = MkDPair fi (MkDPair n (MkDPair fields (MkDPair ts (MkDPair u Refl))))
cannonicalForms
  (Variant fi tag tj (Variant (MkVariant n tags tys u nz))) v (Variant (MkVariant n tags tys u nz)) (TVariant fi x y z)
  = MkDPair fi (MkDPair tag (MkDPair tj (MkDPair (Variant (MkVariant n tags tys u nz)) Refl)))
cannonicalForms (LitNat fi l) LitNat LitNat _
  = (fi ** l ** Refl)
cannonicalForms (FFIVal fi (MkFFIVal baseType sn)) FFIVal (Base baseType) (TFFIVal fi)
  = (fi ** sn ** Refl)
