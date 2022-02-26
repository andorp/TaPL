module TaPLc.Semantics.WTSubstituition

import TaPLc.IR.Record
import TaPLc.IR.Variant
import TaPLc.IR.Name
import TaPLc.IR.Info
import TaPLc.IR.Type
import TaPLc.Data.Vect
import TaPLc.IR.FFI
import Data.Vect
import Data.Vect.Quantifiers
import TaPLc.IR.WellTypedTerm

extend
  :  {gamma, delta : Context Ty}
  -> ({a : Ty} -> In gamma a -> In delta a)
  -> {a,b : Ty} -> In (gamma :< b) a -> In (delta :< b) a
extend f Here = Here
extend f (There x) = There (f x)

mutual

  rename
    :  {gamma, delta : Context Ty}
    -> ({a : Ty} -> In gamma a -> In delta a)
    -> Tm gamma a -> Tm delta a
  rename f (True fi)                    = True fi
  rename f (False fi)                   = False fi
  rename f (If fi p t e)                = If fi (rename f p) (rename f t) (rename f e)
  rename f (Var fi k)                   = Var fi (f k)
  rename f (Abs fi var ty1 t)           = Abs fi var ty1 (rename (extend f) t)
  rename f (App fi t1 t2)               = App fi (rename f t1) (rename f t2)
  rename f (Unit fi)                    = Unit fi
  rename f (Seq fi t1 t2)               = Seq fi (rename f t1) (rename f t2)
  rename f (Let fi n t b)               = Let fi n (rename f t) (rename (extend f) b)
  rename f (Tuple fi n tys tms)         = Tuple fi n tys (renameAll f tms)
  rename f (Proj fi n i t)              = Proj fi n i (rename f t)
  rename f (Record fi r tms)            = Record fi r (renameAll f tms)
  rename f (ProjField fi field x t)     = ProjField fi field x (rename f t)
  rename f (Variant fi tag v fld x)     = Variant fi tag v fld (rename f x)
  rename f (Case fi v s alts)           = Case fi v (rename f s) (renameAlts f alts)
  rename f (Fix fi x)                   = Fix fi (rename f x)
  rename f (Nil fi ty)                  = Nil fi ty
  rename f (Cons fi ty x y)             = Cons fi ty (rename f x) (rename f y)
  rename f (IsNil fi ty x)              = IsNil fi ty (rename f x)
  rename f (Head fi a x)                = Head fi a (rename f x)
  rename f (Tail fi ty x)               = Tail fi ty (rename f x)
  rename f (LitNat fi literal)          = LitNat fi literal
  rename f (ConvertFFI fi baseType x y) = ConvertFFI fi baseType x (rename f y)
  rename f (FFI fi x args)              = FFI fi x (renameFFIArgs f args)
  rename f (FFIVal fi x)                = FFIVal fi x

  renameAll
    : {gamma, delta : Context Ty}
    -> {n : Nat}
    -> {tys : Vect n Ty}
    -> ({a : Ty} -> In gamma a -> In delta a)
    -> All (Tm gamma) tys
    -> All (Tm delta) tys
  renameAll f [] = []
  renameAll f (y :: ys) = rename f y :: renameAll f ys
  
  renameAlts
    :  {gamma, delta : Context Ty}
    -> {n : Nat}
    -> {tys : Vect n Ty}
    -> ({a : Ty} -> In gamma a -> In delta a)
    -> All (\t => Tm (gamma :< t) a) tys
    -> All (\t => Tm (delta :< t) a) tys
  renameAlts f [] = []
  renameAlts f (y :: ys) = rename (extend f) y :: renameAlts f ys

  renameFFIArgs
    :  {gamma, delta : Context Ty}
    -> {n : Nat}
    -> {tys : Vect n BaseType}
    -> ({a : Ty} -> In gamma a -> In delta a)
    -> All (Tm gamma) (map Base tys)
    -> All (Tm delta) (map Base tys)
  renameFFIArgs {tys = []       } f []        = []
  renameFFIArgs {tys = (x :: xs)} f (y :: ys) = rename f y :: (renameFFIArgs f ys)

record Variable (gamma : Context Ty) (a : Ty) where
  constructor MkVariable
  info  : Info
  idx   : In gamma a

extendSubst
  :  {gamma, delta : Context Ty}
  -> ({a : Ty} -> Variable gamma a -> Tm delta a)
  -> {a,b : Ty}
  -> Variable (gamma :< b) a
  -> Tm (delta :< b) a
extendSubst f (MkVariable i Here) = Var i Here
extendSubst f (MkVariable i (There x)) = rename There (f (MkVariable i x))

mutual

  subst
    :  {gamma, delta : Context Ty}
    -> ({a : Ty} -> Variable gamma a -> Tm delta a)
    -> Tm gamma a -> Tm delta a
  subst f (True fi)                     = True fi
  subst f (False fi)                    = False fi
  subst f (If fi p t e)                 = If fi (subst f p) (subst f t) (subst f e)
  subst f (Var fi k)                    = f (MkVariable fi k)
  subst f (Abs fi var ty1 t)            = Abs fi var ty1 (subst (extendSubst f) t)
  subst f (App fi t1 t2)                = App fi (subst f t1) (subst f t2)
  subst f (Unit fi)                     = Unit fi
  subst f (Seq fi t1 t2)                = Seq fi (subst f t1) (subst f t2)
  subst f (Let fi n t b)                = Let fi n (subst f t) (subst (extendSubst f) b)
  subst f (Tuple fi n tys ts)           = Tuple fi n tys (substAll f ts)
  subst f (Proj fi n i t)               = Proj fi n i (subst f t)
  subst f (Record fi r x)               = Record fi r (substAll f x)
  subst f (ProjField fi field x t)      = ProjField fi field x (subst f t)
  subst f (Variant fi tag v fld t)      = Variant fi tag v fld (subst f t)
  subst f (Case fi v s alts)            = Case fi v (subst f s) (substAlts f alts)
  subst f (Fix fi x)                    = Fix fi (subst f x)
  subst f (Nil fi ty)                   = Nil fi ty
  subst f (Cons fi ty x y)              = Cons fi ty (subst f x) (subst f y)
  subst f (IsNil fi ty x)               = IsNil fi ty (subst f x)
  subst f (Head fi a x)                 = Head fi a (subst f x)
  subst f (Tail fi ty x)                = Tail fi ty (subst f x)
  subst f (LitNat fi literal)           = LitNat fi literal
  subst f (ConvertFFI fi baseType x t)  = ConvertFFI fi baseType x (subst f t)
  subst f (FFI fi ffi ts)               = FFI fi ffi (substFFIArgs f ts)
  subst f (FFIVal fi x)                 = FFIVal fi x

  substAll
    :  {gamma, delta : Context Ty}
    -> {n : Nat}
    -> {tys : Vect n Ty}
    -> ({a : Ty} -> Variable gamma a -> Tm delta a)
    -> All (Tm gamma) tys
    -> All (Tm delta) tys
  substAll f [] = []
  substAll f (y :: ys) = subst f y :: substAll f ys

  substAlts
    :  {gamma, delta : Context Ty}
    -> {n : Nat}
    -> {tys : Vect n Ty}
    -> ({a : Ty} -> Variable gamma a -> Tm delta a)
    -> All (\t => Tm (gamma :< t) a) tys
    -> All (\t => Tm (delta :< t) a) tys
  substAlts f [] = []
  substAlts f (y :: ys) = subst (extendSubst f) y :: substAlts f ys

  substFFIArgs
    :  {gamma, delta : Context Ty}
    -> {n : Nat}
    -> {tys : Vect n BaseType}
    -> ({a : Ty} -> Variable gamma a -> Tm delta a)
    -> All (Tm gamma) (map Base tys)
    -> All (Tm delta) (map Base tys)
  substFFIArgs {tys=[]     } f []        = []
  substFFIArgs {tys=x :: xs} f (y :: ys) = subst f y :: substFFIArgs f ys

singleVariable
  :  {gamma : Context Ty}
  -> {a,b : Ty}
  -> Tm gamma b
  -> Variable (gamma :< b) a
  -> Tm gamma a
singleVariable s (MkVariable i Here)      = s
singleVariable s (MkVariable i (There x)) = Var i x

export
substituition
  :  {gamma : Context Ty}
  -> {a,b : Ty}
  -> Tm gamma b
  -> Tm (gamma :< b) a
  -> Tm gamma a
substituition s t = subst (singleVariable s) t
