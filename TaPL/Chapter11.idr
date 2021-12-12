module TaPL.Chapter11

import Data.Vect
import Decidable.Equality

Name : Type
Name = String

-- Declare types in advance:

data Info : Type
data Context : Type
data TypeStatement : Type
data (|-) : (0 _ : Context) -> TypeStatement -> Type

-- Even in a namespace

namespace TypeInferenceError
  public export
  data TypeInferenceError : Type

namespace Ty
  public export
  data Ty : Type

infix 10 |-
infix 11 <:>

DecEq (NonZero n) where
  decEq SIsNonZero SIsNonZero = Yes Refl

data Binding : Type where
  VarBind  : (ty : Ty) -> Binding

data Context : Type where
  Lin  : Context
  (:<) : Context -> (Name, Binding) -> Context

data InContext : Nat -> Ty -> Context -> Type where
  Here  : InContext 0 ty (ctx :< (n, VarBind ty))
  There : InContext n ty ctx -> InContext (S n) ty (ctx :< b)

Uninhabited (InContext 0     _ Lin) where uninhabited _ impossible
Uninhabited (InContext (S _) _ Lin) where uninhabited _ impossible

total
thereInjective : InContext (S n) ty (ctx :< b) -> InContext n ty ctx
thereInjective (There x) = x

total
inContext : (ctx : Context) -> (i : Nat) -> Dec (ty : Ty ** InContext i ty ctx)
inContext [<] 0                     = No (\inCtxt => uninhabited (snd inCtxt))
inContext [<] (S k)                 = No (\inCtxt => uninhabited (snd inCtxt))
inContext (x :< (y, (VarBind t))) 0 = Yes (t ** Here)
inContext (x :< y) (S k)            = case inContext x k of
  Yes   found => Yes (case found of { (ty ** there) => (ty ** There there) })
  No notFound => No (\(ty ** there) => notFound (ty ** thereInjective there))

total
indexToName : (ctx : Context) -> (i : Nat) -> (inCtx : InContext i ty ctx) -> Name
indexToName (ctx :< (n, VarBind ty))  0     Here      = n
indexToName (ctx :< b)                (S n) (There x) = indexToName ctx n x

public export
addBinding : Name -> Ty -> Context -> Context
addBinding n ty ctx = ctx :< (n, VarBind ty)


data Infer : Type -> Type where
  Pure : a -> Infer a
  Bind : Infer a -> (a -> Infer b) -> Infer b
  Error : {a : Type} -> Info -> List TypeInferenceError -> Infer a

namespace InferMonad

  (>>=) : Infer a -> (a -> Infer b) -> Infer b
  (>>=) = Bind

  pure : a -> Infer a
  pure = Pure

Functor Infer where
  map f m = Bind m (\a => Pure (f a))

Applicative Infer where
  pure    x = Pure x
  ef <*> ex = Bind ef (\f => (Bind ex (\x => Pure (f x))))

Monad Infer where
  join m  = Bind m id
  m >>= k = Bind m k

namespace ForEach

  public export
  data ForEach : Vect n a -> (p : a -> Type) -> Type where
    Nil  : ForEach [] p
    (::) : {xs : Vect n a} -> (p x) -> ForEach xs p -> ForEach (x :: xs) p

namespace NotInt

  public export
  data NotIn : String -> Vect n String -> Type where
    Nil  : NotIn n []
    (::) : (0 c : Not (n = f)) -> NotIn n fs -> NotIn n (f :: fs)

  -- If the f and fs are the same, there should be only one way to create the list that proofs for every
  -- element the f is not in the fs vector. If we compare such two values, the only possible difference
  -- are the proofs that that f is not the head of the vector. We could have many computationaly different
  -- functions to create an impossbile Void value, but we say, if we got one, that the difference is their
  -- implementation is not relevant.
  -- At the same time we don't use such a proof at runtime, because the 0 quantity on the Cons cell, meaning
  -- that the runtime representation of such field, will be the Erased value, which is much easier to find
  -- if that is the same or not, as it should be the same, we are on the safe side.
  export
  DecEq (NotIn f fs) where
    decEq n1 n2 = Yes (believe_me (Refl {x=n1}))

namespace Index

  public export
  data Index : a -> Nat -> Vect n a -> Type where
    Here  : Index x 0 (x :: xs)
    There : Index x n xs -> Index x (S n) (y :: xs)

namespace UniqueFields

  public export
  data UniqueFields : Vect n String -> Type where
    Nil  : UniqueFields []
    (::) : NotIn f fs -> UniqueFields fs -> UniqueFields (f :: fs)

  export
  consInjective : (UniqueFields.(::) x xs = UniqueFields.(::) y ys) -> (x = y, xs = ys)
  consInjective Refl = (Refl, Refl)

  export
  DecEq (UniqueFields fs) where
    decEq [] [] = Yes Refl
    decEq (x :: y) (z :: w) = case decEq x z of
      (Yes Refl) => case decEq y w of
        (Yes Refl) => Yes Refl
        (No y_is_not_w) => No (\assumeUniqueFieldOK => y_is_not_w (snd (consInjective assumeUniqueFieldOK)))
      (No x_is_not_z) => No (\assumeUniqueFieldOK => x_is_not_z (fst (consInjective assumeUniqueFieldOK)))

namespace Record

  public export
  record Record (a : Type) where
    constructor MkRecord
    size          : Nat
    fields        : Vect size String
    values        : Vect size a
    uniqueFields  : UniqueFields fields

  public export
  data InRecord : String -> a -> Vect n String -> Vect n a -> Type where
    Here  : InRecord f x (f :: fs) (x :: xs)
    There : InRecord f x fs xs -> InRecord f x (g :: fs) (y :: xs)

  export
  recordInjective
    :  {r,s : Record a} -> (r = s)
    -> (r.size = s.size, r.fields ~=~ s.fields, r.values ~=~ s.values, r.uniqueFields ~=~ s.uniqueFields)
  recordInjective Refl = (Refl, Refl, Refl, Refl)

  export
  DecEq a => DecEq (Record a) where
    decEq (MkRecord s1 f1 v1 u1) (MkRecord s2 f2 v2 u2) = case decEq s1 s2 of
      (Yes Refl) => case decEq f1 f2 of
        (Yes Refl) => case decEq v1 v2 of
          (Yes Refl) => case decEq u1 u2 of
            (Yes Refl)        => Yes Refl
            (No u1_is_not_u2) => No (\assumeRecordOK => u1_is_not_u2 ((snd . snd . snd) (recordInjective assumeRecordOK)))
          (No v1_is_not_v2) => No (\assumeRecordOK => v1_is_not_v2 ((fst . snd . snd) (recordInjective assumeRecordOK)))
        (No f1_is_not_f2) => No (\assumeRecordOK => f1_is_not_f2 ((fst . snd) (recordInjective assumeRecordOK)))
      (No s1_is_not_s2) => No (\assumeRecordOK => s1_is_not_s2 (fst (recordInjective assumeRecordOK)))

namespace UniqueTags

  public export
  data UniqueTags : (n : Nat) -> Vect n String -> Type where
    Nil  : UniqueTags 0 []
    (::) : NotIn f fs -> UniqueTags n fs -> UniqueTags (S n) (f :: fs)

  export
  notInInjective : (UniqueTags.(::) ni1 ut1 = UniqueTags.(::) ni2 ut2) -> (ni1 = ni2, ut1 = ut2)
  notInInjective Refl = (Refl, Refl)

  export
  DecEq (UniqueTags n xs) where
    decEq [] [] = Yes Refl
    decEq (x :: y) (z :: w) = case decEq x z of
      (Yes Refl) => case decEq y w of
        (Yes Refl) => Yes Refl
        (No y_is_not_w) => No (\assumeUniqueTags => y_is_not_w (snd (notInInjective assumeUniqueTags)))
      (No x_is_not_z) => No (\assumeUniqueTags => x_is_not_z (fst (notInInjective assumeUniqueTags)))

namespace Variant

  public export
  record Variant (a : Type) where
    constructor MkVariant
    size        : Nat
    tags        : Vect size String
    info        : Vect size a
    uniqueTags  : UniqueTags size tags
    nonEmpty    : NonZero size

  export
  variantInjective
    :  {v,w : Variant a} -> (v = w)
    -> (v.size = w.size, v.tags ~=~ w.tags, v.info ~=~ w.info, v.uniqueTags ~=~ w.uniqueTags, v.nonEmpty ~=~ w.nonEmpty)
  variantInjective Refl = (Refl, Refl, Refl, Refl, Refl)

  export
  DecEq a => DecEq (Variant a) where
    decEq (MkVariant s1 t1 i1 u1 n1) (MkVariant s2 t2 i2 u2 n2) = case decEq s1 s2 of
      (Yes Refl) => case decEq t1 t2 of
        (Yes Refl) => case decEq i1 i2 of
          (Yes Refl) => case decEq u1 u2 of
            (Yes Refl) => case decEq n1 n2 of
              (Yes Refl) => Yes Refl
              (No n1_is_not_n2) => No (\assumeVariantOK => n1_is_not_n2 ((snd . snd . snd . snd) (variantInjective assumeVariantOK)))
            (No u1_is_not_u2) => No (\assumeVariantOK => u1_is_not_u2 ((fst . snd . snd . snd) (variantInjective assumeVariantOK)))
          (No i1_is_not_i2) => No (\assumeVariantOK => i1_is_not_i2 ((fst . snd . snd) (variantInjective assumeVariantOK)))
        (No t1_is_not_t2) => No (\assumeVariantOK => t1_is_not_t2 ((fst . snd) (variantInjective assumeVariantOK)))
      (No s1_is_not_s2) => No (\assumeVariantOK => s1_is_not_s2 (fst (variantInjective assumeVariantOK)))

namespace FieldIndex

  total
  fieldIndexGo : (n : Nat) -> (tag : String) -> (tags : Vect n String) -> (infos : Vect n a) -> Maybe (i : Nat ** (Index tag i tags, ((x : a ** Index x i infos))))
  fieldIndexGo 0       tag []        [] = Nothing
  fieldIndexGo (S len) tag (x :: xs) (y :: ys) = case decEq x tag of
    Yes Refl        => Just (0 ** (Here, (y ** Here)))
    No x_is_not_tag => do
      (i ** (tagThere, (a ** infoThere))) <- fieldIndexGo len tag xs ys
      Just ((S i) ** (There tagThere, (a ** There infoThere)))

  total export
  fieldIndex : (tag : String) -> (v : Variant a) -> Maybe (i : Nat ** (Index tag i v.tags, (x : a ** Index x i v.info)))
  fieldIndex tag v = fieldIndexGo v.size tag v.tags v.info

namespace Term

  public export
  data Tm : Type where
    True  : (fi : Info)                                               -> Tm
    False : (fi : Info)                                               -> Tm
    If    : (fi : Info) -> (p,t,e : Tm)                               -> Tm
    Var   : (fi : Info) -> (i : Nat)                                  -> Tm 
    Abs   : (fi : Info) -> (var : Name) -> (ty : Ty) -> (t : Tm)      -> Tm
    App   : (fi : Info) -> (t1, t2 : Tm)                              -> Tm
    Unit  : (fi : Info)                                               -> Tm

    Seq   : (fi : Info) -> (t1, t2 : Tm)                              -> Tm
    As    : (fi : Info) -> (t : Tm) -> (ty : Ty)                      -> Tm
    Let   : (fi : Info) -> (n : Name) -> (t : Tm) -> (b : Tm)         -> Tm
    
    Pair  : (fi : Info) -> (p1,p2 : Tm)                               -> Tm
    First  : (fi : Info) -> (t : Tm)                                  -> Tm
    Second : (fi : Info) -> (t : Tm)                                  -> Tm

    Tuple : (fi : Info) -> (n : Nat) -> (ti : Vect n Tm)              -> Tm
    Proj  : (fi : Info) -> (t : Tm) -> (n : Nat) -> (i : Fin n)       -> Tm

    Record : (fi : Info) -> (Record.Record Tm)                        -> Tm
    ProjField : (fi : Info) -> (field : String) -> (t : Tm)           -> Tm

    Variant : (fi : Info) -> (tag : String) -> (t : Tm) -> (ty : Ty)  -> Tm
    Case : (fi : Info) -> (t : Tm) -> (alts : Variant (Name, Tm))     -> Tm

    Fix : (fi : Info) -> (t : Tm)                                     -> Tm

    Nil : (fi : Info) -> (ty : Ty)                                    -> Tm
    Cons : (fi : Info) -> (ty : Ty) -> (h,t : Tm)                     -> Tm
    IsNil : (fi : Info) -> (ty : Ty) -> (t : Tm)                      -> Tm
    Head : (fi : Info) -> (ty : Ty) -> (t : Tm)                       -> Tm
    Tail : (fi : Info) -> (ty : Ty) -> (t : Tm)                       -> Tm

namespace Value

  public export
  data Value : Tm -> Type where
    Abs     : Value (Abs fi var ty t)
    True    : Value (True fi)
    False   : Value (False fi)
    Unit    : Value (Unit fi)
    Nil     : Value (Nil fi ty)
    Cons    : Value (Cons fi ty h t)
    Pair    : Value v1 -> Value v2                                -> Value (Pair fi v1 v2)
    Tuple   : {n : Nat} -> {tms : Vect n Tm} -> ForEach tms Value -> Value (Tuple fi n tms)
    Record  : (r : Record Tm) -> ForEach r.values Value           -> Value (Record fi r)

namespace Ty

  public export
  data Ty : Type where
    Bool    : Ty
    Arr     : Ty -> Ty                -> Ty
    Base    : String                  -> Ty
    Unit    : Ty
    Product : Ty -> Ty                -> Ty
    Tuple   : (n : Nat) -> Vect n Ty  -> Ty
    Record  : (r : Record Ty)         -> Ty
    Variant : (v : Variant Ty)        -> Ty
    List    : Ty                      -> Ty

  export
  funInjective : (Ty.Arr x y = Ty.Arr z w) -> (x = z, y = w)
  funInjective Refl = (Refl, Refl)

  export
  baseInjective : (Ty.Base x = Ty.Base y) -> x = y
  baseInjective Refl = Refl

  export
  productInjective : (Ty.Product x y = Ty.Product z w) -> (x = z, y = w)
  productInjective Refl = (Refl, Refl)

  export
  tupleInjective : (Ty.Tuple n xs = Ty.Tuple m ys) -> (n = m, xs = ys)
  tupleInjective Refl = (Refl, Refl)

  export
  recordInjective : (Ty.Record x = Ty.Record y) -> (x = y)
  recordInjective Refl = Refl

  export
  variantInjective : (Ty.Variant x = Ty.Variant y) -> (x = y)
  variantInjective Refl = Refl

  export
  listInjective : (Ty.List x = Ty.List y) -> (x = y)
  listInjective Refl = Refl

  export Uninhabited (Ty.Bool = Ty.Arr _ _)           where uninhabited _ impossible
  export Uninhabited (Ty.Bool = Ty.Base _)            where uninhabited _ impossible
  export Uninhabited (Ty.Bool = Ty.Unit)              where uninhabited _ impossible
  export Uninhabited (Ty.Bool = Ty.Product _ _)       where uninhabited _ impossible
  export Uninhabited (Ty.Bool = Ty.Tuple n v)         where uninhabited _ impossible
  export Uninhabited (Ty.Bool = Ty.Record _)          where uninhabited _ impossible
  export Uninhabited (Ty.Bool = Ty.Variant _)         where uninhabited _ impossible
  export Uninhabited (Ty.Bool = Ty.List _)            where uninhabited _ impossible

  export Uninhabited (Ty.Arr _ _ = Ty.Bool)           where uninhabited _ impossible
  export Uninhabited (Ty.Arr _ _ = Ty.Base _)         where uninhabited _ impossible
  export Uninhabited (Ty.Arr _ _ = Ty.Unit)           where uninhabited _ impossible
  export Uninhabited (Ty.Arr _ _ = Ty.Product _ _)    where uninhabited _ impossible
  export Uninhabited (Ty.Arr _ _ = Ty.Tuple n v)      where uninhabited _ impossible
  export Uninhabited (Ty.Arr _ _ = Ty.Record _)       where uninhabited _ impossible
  export Uninhabited (Ty.Arr _ _ = Ty.Variant _)      where uninhabited _ impossible
  export Uninhabited (Ty.Arr _ _ = Ty.List _)         where uninhabited _ impossible

  export Uninhabited (Ty.Base _ = Ty.Bool)            where uninhabited _ impossible
  export Uninhabited (Ty.Base _ = Ty.Arr _ _)         where uninhabited _ impossible
  export Uninhabited (Ty.Base _ = Ty.Unit)            where uninhabited _ impossible
  export Uninhabited (Ty.Base _ = Ty.Product _ _)     where uninhabited _ impossible
  export Uninhabited (Ty.Base _ = Ty.Tuple n v)       where uninhabited _ impossible
  export Uninhabited (Ty.Base _ = Ty.Record _)        where uninhabited _ impossible
  export Uninhabited (Ty.Base _ = Ty.Variant _)       where uninhabited _ impossible
  export Uninhabited (Ty.Base _ = Ty.List _)          where uninhabited _ impossible

  export Uninhabited (Ty.Unit = Ty.Bool)              where uninhabited _ impossible
  export Uninhabited (Ty.Unit = Ty.Arr _ _)           where uninhabited _ impossible
  export Uninhabited (Ty.Unit = Ty.Base _)            where uninhabited _ impossible
  export Uninhabited (Ty.Unit = Ty.Product _ _)       where uninhabited _ impossible
  export Uninhabited (Ty.Unit = Ty.Tuple n v)         where uninhabited _ impossible
  export Uninhabited (Ty.Unit = Ty.Record _)          where uninhabited _ impossible
  export Uninhabited (Ty.Unit = Ty.Variant _)         where uninhabited _ impossible
  export Uninhabited (Ty.Unit = Ty.List _)            where uninhabited _ impossible

  export Uninhabited (Ty.Product _ _ = Bool)          where uninhabited _ impossible
  export Uninhabited (Ty.Product _ _ = Arr _ _)       where uninhabited _ impossible
  export Uninhabited (Ty.Product _ _ = Base _)        where uninhabited _ impossible
  export Uninhabited (Ty.Product _ _ = Unit)          where uninhabited _ impossible
  export Uninhabited (Ty.Product _ _ = Tuple n v)     where uninhabited _ impossible
  export Uninhabited (Ty.Product _ _ = Record _)      where uninhabited _ impossible
  export Uninhabited (Ty.Product _ _ = Variant _)     where uninhabited _ impossible
  export Uninhabited (Ty.Product _ _ = List _)        where uninhabited _ impossible

  export Uninhabited (Ty.Tuple n v = Bool)            where uninhabited _ impossible
  export Uninhabited (Ty.Tuple n v = Arr _ _)         where uninhabited _ impossible
  export Uninhabited (Ty.Tuple n v = Base _)          where uninhabited _ impossible
  export Uninhabited (Ty.Tuple n v = Unit)            where uninhabited _ impossible
  export Uninhabited (Ty.Tuple n v = Product _ _)     where uninhabited _ impossible
  export Uninhabited (Ty.Tuple n v = Record _)        where uninhabited _ impossible
  export Uninhabited (Ty.Tuple n v = Variant _)       where uninhabited _ impossible
  export Uninhabited (Ty.Tuple n v = List _)          where uninhabited _ impossible

  export Uninhabited (Ty.Record _ = Bool)             where uninhabited _ impossible
  export Uninhabited (Ty.Record _ = Arr _ _)          where uninhabited _ impossible
  export Uninhabited (Ty.Record _ = Base _)           where uninhabited _ impossible
  export Uninhabited (Ty.Record _ = Unit)             where uninhabited _ impossible
  export Uninhabited (Ty.Record _ = Product _ _)      where uninhabited _ impossible
  export Uninhabited (Ty.Record _ = Tuple n v)        where uninhabited _ impossible
  export Uninhabited (Ty.Record _ = Variant _)        where uninhabited _ impossible
  export Uninhabited (Ty.Record _ = List _)           where uninhabited _ impossible

  export Uninhabited (Ty.Variant _ = Ty.Bool)         where uninhabited _ impossible
  export Uninhabited (Ty.Variant _ = Ty.Arr _ _)      where uninhabited _ impossible
  export Uninhabited (Ty.Variant _ = Ty.Base _)       where uninhabited _ impossible
  export Uninhabited (Ty.Variant _ = Ty.Unit)         where uninhabited _ impossible
  export Uninhabited (Ty.Variant _ = Ty.Product _ _)  where uninhabited _ impossible
  export Uninhabited (Ty.Variant _ = Ty.Tuple n v)    where uninhabited _ impossible
  export Uninhabited (Ty.Variant _ = Ty.Record _)     where uninhabited _ impossible
  export Uninhabited (Ty.Variant _ = Ty.List _)       where uninhabited _ impossible

  export Uninhabited (Ty.List _ = Ty.Bool)            where uninhabited _ impossible
  export Uninhabited (Ty.List _ = Ty.Arr _ _)         where uninhabited _ impossible
  export Uninhabited (Ty.List _ = Ty.Base _)          where uninhabited _ impossible
  export Uninhabited (Ty.List _ = Ty.Unit)            where uninhabited _ impossible
  export Uninhabited (Ty.List _ = Ty.Product _ _)     where uninhabited _ impossible
  export Uninhabited (Ty.List _ = Ty.Tuple n v)       where uninhabited _ impossible
  export Uninhabited (Ty.List _ = Ty.Record _)        where uninhabited _ impossible
  export Uninhabited (Ty.List _ = Ty.Variant _)       where uninhabited _ impossible

  public export
  DecEq Ty where
    decEq Bool Bool = Yes Refl
    decEq Bool (Arr x y)      = No uninhabited
    decEq Bool (Base x)       = No uninhabited
    decEq Bool Unit           = No uninhabited
    decEq Bool (Product x y)  = No uninhabited
    decEq Bool (Tuple n xs)   = No uninhabited
    decEq Bool (Record r)     = No uninhabited
    decEq Bool (Variant v)    = No uninhabited
    decEq Bool (List x)       = No uninhabited

    decEq (Arr x y) Bool      = No uninhabited
    decEq (Arr x y) (Arr z w) = case decEq x z of
      (Yes Refl) => case decEq y w of
        (Yes Refl      ) => Yes Refl 
        (No  y_is_not_w) => No (\assumeArrOk => (y_is_not_w (snd (funInjective assumeArrOk))))
      (No x_is_not_z) => No (\assumeArrOk => (x_is_not_z (fst (funInjective assumeArrOk))))
    decEq (Arr x y) (Base z)      = No uninhabited
    decEq (Arr x y) Unit          = No uninhabited
    decEq (Arr x y) (Product z w) = No uninhabited
    decEq (Arr x y) (Tuple n xs)  = No uninhabited
    decEq (Arr x y) (Record r)    = No uninhabited
    decEq (Arr x y) (Variant v)   = No uninhabited
    decEq (Arr x y) (List z)      = No uninhabited

    decEq (Base x) Bool       = No uninhabited
    decEq (Base x) (Arr y z)  = No uninhabited
    decEq (Base x) (Base y) = case decEq x y of
      (Yes Refl       ) => Yes Refl
      (No  x_is_not_y ) => No (\assumeBaseOk => x_is_not_y (baseInjective assumeBaseOk))
    decEq (Base x) Unit           = No uninhabited
    decEq (Base x) (Product y z)  = No uninhabited
    decEq (Base x) (Tuple n xs)   = No uninhabited
    decEq (Base x) (Record r)     = No uninhabited
    decEq (Base x) (Variant v)    = No uninhabited
    decEq (Base x) (List y)       = No uninhabited

    decEq Unit Bool           = No uninhabited
    decEq Unit (Arr x y)      = No uninhabited
    decEq Unit (Base x)       = No uninhabited
    decEq Unit Unit           = Yes Refl
    decEq Unit (Product x y)  = No uninhabited
    decEq Unit (Tuple n xs)   = No uninhabited
    decEq Unit (Record r)     = No uninhabited
    decEq Unit (Variant v)    = No uninhabited
    decEq Unit (List x)       = No uninhabited

    decEq (Product x y) Bool      = No uninhabited
    decEq (Product x y) (Arr z w) = No uninhabited
    decEq (Product x y) (Base z)  = No uninhabited
    decEq (Product x y) Unit      = No uninhabited
    decEq (Product x y) (Product z w) = case decEq x z of
      (Yes Refl) => case decEq y w of
        (Yes Refl      ) => Yes Refl
        (No  y_is_not_w) => No (\assumeProductOK => y_is_not_w (snd (productInjective assumeProductOK)))
      (No x_is_not_z) => No (\assumeProductOK => x_is_not_z (fst (productInjective assumeProductOK)))
    decEq (Product x y) (Tuple n xs)  = No uninhabited
    decEq (Product x y) (Record r)    = No uninhabited
    decEq (Product x y) (Variant v)   = No uninhabited
    decEq (Product x y) (List z)      = No uninhabited

    decEq (Tuple n xs) Bool          = No uninhabited
    decEq (Tuple n xs) (Arr x y)     = No uninhabited
    decEq (Tuple n xs) (Base x)      = No uninhabited
    decEq (Tuple n xs) Unit          = No uninhabited
    decEq (Tuple n xs) (Product x y) = No uninhabited
    decEq (Tuple n xs) (Tuple k ys) = case decEq n k of
      (Yes Refl) => case decEq xs ys of
        (Yes Refl)         => Yes Refl
        (No  xs_is_not_ys) => No (\assumeTupleOK => xs_is_not_ys (snd (tupleInjective assumeTupleOK)))
      (No n_is_not_k)      => No (\assumeTupleOK => n_is_not_k (fst (tupleInjective assumeTupleOK)))
    decEq (Tuple n xs) (Record r)   = No uninhabited
    decEq (Tuple n xs) (Variant v)  = No uninhabited
    decEq (Tuple n xs) (List x)     = No uninhabited

    decEq (Record r) Bool           = No uninhabited
    decEq (Record r) (Arr x y)      = No uninhabited
    decEq (Record r) (Base x)       = No uninhabited
    decEq (Record r) Unit           = No uninhabited
    decEq (Record r) (Product x y)  = No uninhabited
    decEq (Record r) (Tuple n xs)   = No uninhabited
    decEq (Record r) (Record x) = case decEq r x of
      (Yes Refl      ) => Yes Refl
      (No  r_is_not_x) => No (\assumeRecordOK => r_is_not_x (recordInjective assumeRecordOK))
    decEq (Record r) (Variant v)    = No uninhabited
    decEq (Record r) (List x)       = No uninhabited

    decEq (Variant v) Bool          = No uninhabited
    decEq (Variant v) (Arr x y)     = No uninhabited
    decEq (Variant v) (Base x)      = No uninhabited
    decEq (Variant v) Unit          = No uninhabited
    decEq (Variant v) (Product x y) = No uninhabited
    decEq (Variant v) (Tuple n xs)  = No uninhabited
    decEq (Variant v) (Record r)    = No uninhabited
    decEq (Variant v) (Variant x) = case decEq v x of
      (Yes Refl      ) => Yes Refl
      (No  v_is_not_x) => No (\assumeVariantOk => v_is_not_x (variantInjective assumeVariantOk))
    decEq (Variant v) (List x)      = No uninhabited

    decEq (List x) Bool           = No uninhabited
    decEq (List x) (Arr y z)      = No uninhabited
    decEq (List x) (Base y)       = No uninhabited
    decEq (List x) Unit           = No uninhabited
    decEq (List x) (Product y z)  = No uninhabited
    decEq (List x) (Tuple n xs)   = No uninhabited
    decEq (List x) (Record r)     = No uninhabited
    decEq (List x) (Variant v)    = No uninhabited
    decEq (List x) (List y) = case decEq x y of
      (Yes Refl      ) => Yes Refl
      (No  x_is_not_y) => No (\assumeListOk => x_is_not_y (listInjective assumeListOk))

data TypeStatement : Type where
  (<:>) : (0 t1 : Tm) -> (t2 : Ty) -> TypeStatement

data Derivation : Context -> Tm -> Ty -> Type where
  MkDerivation : (t : Tm) -> (ty : Ty) -> (deriv : (ctx |- t <:> ty)) -> Derivation ctx t ty

namespace DerivList

  public export
  data Derivations : Context -> Vect n Tm -> Vect n Ty -> Type where
    Nil  : Derivations ctx [] []
    (::) : Derivation ctx t ty -> Derivations ctx ts tys -> Derivations ctx (t :: ts) (ty :: tys)

namespace VariantDerivations

  ||| Witness that every Tm term in the alternatives has the same Ty type.
  public export
  data VariantDerivations : (n : Nat) -> Context -> Vect n (Name, Tm) -> Vect n Ty -> Ty -> Type where
    Nil  : VariantDerivations 0 ctx [] [] ty
    (::) : {var : Name} -> {tty : Ty}
           -> Derivation (ctx :< (var, VarBind tty)) t ty
           -> VariantDerivations n ctx ts ttys ty
           -> VariantDerivations (S n) ctx ((var, t) :: ts) (tty :: ttys) ty

namespace InVariant

  public export
  data InVariant : String -> Name -> Tm -> Vect n String -> Vect n (Name,Tm) -> Type where
    Here  : InVariant tag x tm (tag :: tags) ((x,tm) :: alts)
    There : InVariant tag x tm tags alts -> InVariant tag x tm (tah :: tags) ((y,tn) :: alts)

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

  TAscribe : (fi : Info) ->
        (gamma |- t1 <:> ty1)  ->
    -----------------------------
    gamma |- As fi t1 ty1 <:> ty1

  TLet : (fi : Info) ->
    (gamma |- (t1 <:> ty1)) -> ((gamma :< (x,VarBind ty1)) |- t2 <:> ty2) ->
    ------------------------------------------------------------------------
                       gamma |- Let fi x t1 t2 <:> ty2

  TPair : (fi : Info) ->
    (gamma |- (t1 <:> ty1)) -> (gamma |- (t2 <:> ty2)) ->
    -----------------------------------------------------
          gamma |- Pair fi t1 t2 <:> Product ty1 ty2

  TProj1 : (fi : Info) ->
    (gamma |- (t1 <:> Product ty1 ty2)) ->
    --------------------------------------
          gamma |- First fi t1 <:> ty1

  TProj2 : (fi : Info) ->
    (gamma |- (t1 <:> Product ty1 ty2)) ->
    --------------------------------------
         gamma |- Second fi t1 <:> ty2

  TTuple : (fi : Info) ->
          Derivations gamma ts tys      ->
    --------------------------------------
    gamma |- Tuple fi n ts <:> Tuple n tys

  TProj : (fi : Info) ->
          gamma |- t <:> Tuple n tys    ->
    --------------------------------------
    gamma |- Proj fi t n i <:> index i tys

  TRcd : (fi : Info) ->
                  {fields : Vect n String} -> {u : UniqueFields fields}           ->
                               Derivations gamma ts tys                           ->
    --------------------------------------------------------------------------------
    gamma |- Record fi (MkRecord n fields ts u) <:> Record (MkRecord n fields tys u)

  TRProj : (fi : Info) ->
    gamma |- t <:> Record (MkRecord n fields tys u) -> InRecord field ty fields tys ->
    ----------------------------------------------------------------------------------
                          gamma |- ProjField fi field t <:> ty

  TVariant : (fi : Info) ->
                                            {n : Nat} -> {nz : NonZero n}                                       ->
                                            {j : Nat} -> {ty : Ty}                                              ->
                  {tags : Vect n String} -> {tys : Vect n Ty} ->  {u : UniqueTags n tags} -> {tj : Tm}          -> 
                            Index tag j tags -> Index ty j tys -> (gamma |- tj <:> ty)                          ->
    --------------------------------------------------------------------------------------------------------------
      gamma |- Variant fi tag tj (Variant (MkVariant n tags tys u nz)) <:> (Variant (MkVariant n tags tys u nz))

  TCase : (fi : Info) ->
                                  {n : Nat} -> {nz : NonZero n}                           ->
        {tags : Vect n String} -> {u : UniqueTags n tags} -> {alts : Vect n (Name, Tm)}   ->
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

namespace TypeInferenceError

  public export
  data TypeInferenceError : Type where
    DerivInfo       : (deriv : (ctx |- t <:> ty))       -> TypeInferenceError
    TypeMissmatch   : (expected, found : Ty)            -> TypeInferenceError
    ArityMissmatch  : (expected, found : Nat)           -> TypeInferenceError
    TagMissmatch    : (expected, found : Vect n String) -> TypeInferenceError
    Message         : String                            -> TypeInferenceError
    NotFound        : (ctx : Context) -> (i : Nat)      -> TypeInferenceError
    FoundType       : (ty : Ty)                         -> TypeInferenceError
    InternalError   : String                            -> TypeInferenceError

  export
  derivInfos : VariantDerivations n ctx tms tys ty -> List TypeInferenceError
  derivInfos [] = []
  derivInfos ((MkDerivation t ty deriv) :: vs) = DerivInfo deriv :: derivInfos vs

mutual

  inferType : (ctx : Context) -> (t : Tm) -> Infer (ty : Ty ** (ctx |- t <:> ty))

  inferType ctx (True fi) = pure (Bool ** TTrue fi)

  inferType ctx (False fi) = pure (Bool ** TFalse fi)

  inferType ctx (If fi p t e) = do
    (Bool ** pDeriv) <- inferType ctx p
      | (wt ** wrongDeriv) => Error fi
          [ DerivInfo wrongDeriv
          , TypeMissmatch Bool wt
          , Message "guard of conditional has wrong type"
          ]
    (tty ** thenDeriv) <- inferType ctx t
    (ety ** elseDeriv) <- inferType ctx e
    let Yes Refl = decEq tty ety
        | No _ => Error fi
            [ DerivInfo thenDeriv
            , DerivInfo elseDeriv
            , TypeMissmatch tty ety
            , Message "arms of conditional have different types"
            ]
    pure (tty ** TIf fi pDeriv thenDeriv elseDeriv)

  inferType ctx (Var fi i) = do
    let Yes (ty ** inCtx) = inContext ctx i
        | No _ => Error fi
            [ NotFound ctx i
            , Message "Variable not found"
            ]
    pure (ty ** (TVar fi inCtx))

  inferType ctx (Abs fi var ty t) = do
    (ty2 ** tDeriv) <- inferType (addBinding var ty ctx) t
    pure (Arr ty ty2 ** TAbs fi tDeriv)

  inferType ctx (App fi t1 t2) = do
    (ty1 ** t1Deriv) <- inferType ctx t1
    (ty2 ** t2Deriv) <- inferType ctx t2
    case ty1 of
      Arr aty1 aty2 => case decEq ty2 aty1 of
        Yes Refl
          => pure (aty2 ** TApp fi t1Deriv t2Deriv)
        No _
          => Error fi
              [ DerivInfo t1Deriv
              , DerivInfo t2Deriv
              , TypeMissmatch aty1 ty2
              , Message "parameter type mismatch"
              ]
      _ => Error fi
              [ DerivInfo t1Deriv
              , DerivInfo t2Deriv
              , FoundType ty1
              , Message "function type expected"
              ]

  inferType ctx (Unit fi) = pure (Unit ** TUnit fi)

  inferType ctx (Seq fi t1 t2) = do
    (Unit ** t1Deriv) <- inferType ctx t1
      | (wt ** wrongDeriv) => Error fi
          [ DerivInfo wrongDeriv
          , TypeMissmatch Unit wt
          , Message "First arm of sequence doesn't have Unit type"
          ]
    (ty2 ** t2Deriv) <- inferType ctx t2
    pure (ty2 ** TSeq fi t1Deriv t2Deriv)

  inferType ctx (As fi t ty) = do
    (ty1 ** tDeriv) <- inferType ctx t
    let Yes Refl = decEq ty ty1
        | No _ => Error fi
            [ DerivInfo tDeriv
            , TypeMissmatch ty ty1
            , Message "Found type is different than ascribed type"
            ]
    pure (ty ** TAscribe fi tDeriv)

  inferType ctx (Let fi n t b) = do
    (ty1 ** tDeriv) <- inferType ctx t
    (ty2 ** bDeriv) <- inferType (addBinding n ty1 ctx) b
    pure $ (ty2 ** TLet fi tDeriv bDeriv)

  inferType ctx (Pair fi t1 t2) = do
    (ty1 ** t1Deriv) <- inferType ctx t1
    (ty2 ** t2Deriv) <- inferType ctx t2
    pure $ (Product ty1 ty2 ** TPair fi t1Deriv t2Deriv)

  inferType ctx (First fi t) = do
    (Product ty1 ty2 ** tDeriv) <- inferType ctx t
      | (wt ** wrongDeriv) => Error fi
          [ DerivInfo wrongDeriv
          , FoundType wt
          , Message "Found type is different than product"
          ]
    pure (ty1 ** TProj1 fi tDeriv)

  inferType ctx (Second fi t) = do
    (Product ty1 ty2 ** tDeriv) <- inferType ctx t
      | (wt ** wrongDeriv) => Error fi
          [ DerivInfo wrongDeriv
          , FoundType wt
          , Message "Found type is different than product"
          ]
    pure (ty2 ** TProj2 fi tDeriv)

  inferType ctx (Tuple fi n tms) = do
    (tys ** tty) <- inferTypes ctx tms
    pure (Tuple n tys ** TTuple fi tty)

  inferType ctx (Proj fi t n idx) = do
    (Tuple m tys ** tDeriv) <- inferType ctx t
      | (wt ** wrongDeriv) => Error fi
          [ DerivInfo wrongDeriv
          , FoundType wt
          , Message "Found type is different than tuple"
          ]
    let Yes Refl = decEq n m
        | No _ => Error fi
            [ DerivInfo tDeriv
            , FoundType (Tuple m tys)
            , Message "Tuple have different arity than expected"
            ]
    pure (index idx tys ** (TProj fi tDeriv))

  inferType ctx (Variant fi tag tj ty) = do
    let (Variant (MkVariant n tags tys u nz)) = ty
        | _ => Error fi
          [ FoundType ty
          , Message "Should have been type of Variant"
          ]
    (tyj1 ** tDeriv) <- inferType ctx tj
    let Just (j ** (idx1, (tyj2 ** idx2))) = fieldIndex tag (MkVariant n tags tys u nz)
        | Nothing => Error fi
            [ FoundType tyj1
            , DerivInfo tDeriv
            , Message "\{tag} is not found in the Variant"
            ]
    let Yes Refl = decEq tyj2 tyj1
        | No _ => Error fi
            [ DerivInfo tDeriv
            , TypeMissmatch tyj2 tyj1
            , Message "Found type in variant was different than expected"
            ]
    pure ((Variant (MkVariant n tags tys u nz)) ** TVariant fi idx1 idx2 tDeriv)

  inferType ctx (Case fi t0 (MkVariant n tags alts u nz)) = do
    (Variant (MkVariant n_t0 tags_t0 tys_t0 u_t0 nz_t0) ** t0Deriv) <- inferType ctx t0
    let Yes Refl = decEq n n_t0
        | No _ => Error fi
            [ DerivInfo t0Deriv
            , ArityMissmatch n n_t0
            , Message "Record had different arity"
            ]
    let Yes Refl = decEq nz nz_t0
        | No _ => Error fi
            [ DerivInfo t0Deriv
            , InternalError "Different non-zeros in Record type inference."
            ]
    let Yes Refl = decEq tags tags_t0
        | No _ => Error fi
            [ DerivInfo t0Deriv
            , TagMissmatch tags tags_t0
            , Message "Tags were different"
            ]
    let Yes Refl = decEq u u_t0
        | No _ => Error fi
            [ DerivInfo t0Deriv
            , InternalError "Different unique-tag derivations in Record type inference."
            ]
    (ty ** vDerivs) <- inferVariantTypes fi n_t0 nz_t0 ctx alts tys_t0
    pure (ty ** TCase fi t0Deriv vDerivs)

  inferType ctx (Fix fi t) = do
    (Arr ty1 ty2 ** tDeriv) <- inferType ctx t
      | (wt ** wrongDeriv) => Error fi
          [ DerivInfo wrongDeriv
          , FoundType wt
          , Message "Expected function type"
          ]
    let Yes Refl = decEq ty1 ty2    
        | No _ => Error fi
            [ DerivInfo tDeriv
            , TypeMissmatch ty1 ty2
            , Message "Function domain and codomain should be the same"
            ]
    pure (ty1 ** TFix fi tDeriv)

  inferType ctx (Nil fi ty) = pure (List ty ** TNil fi)

  inferType ctx (Cons fi ty t1 t2) = do
    (ty1 ** t1Deriv) <- inferType ctx t1
    let Yes Refl = decEq ty ty1
        | No _ => Error fi
          [ DerivInfo t1Deriv
          , TypeMissmatch ty ty1
          , TypeMissmatch (List ty) (List ty1)
          , Message "Expected different type of list"
          ]
    (List ty2 ** t2Deriv) <- inferType ctx t2
      | (wt ** wrongDeriv) => Error fi
          [ DerivInfo t1Deriv
          , DerivInfo wrongDeriv
          , FoundType wt
          , Message "Expected a list type"
          ]
    let Yes Refl = decEq ty1 ty2
        | No _ => Error fi
            [ DerivInfo t1Deriv
            , DerivInfo t2Deriv
            , TypeMissmatch ty1 ty2
            , Message "Type of head should be the same as tail"
            ]
    pure (List ty2 ** TCons fi t1Deriv t2Deriv)

  inferType ctx (IsNil fi ty t) = do
    (List tty ** tDeriv) <- inferType ctx t
      | (wt ** wrongDeriv) => Error fi
          [ DerivInfo wrongDeriv
          , FoundType wt
          , Message "Expected a list type."
          ]
    let Yes Refl = decEq ty tty
        | No _ => Error fi
            [ DerivInfo tDeriv
            , TypeMissmatch ty tty
            , TypeMissmatch (List ty) (List tty)
            , Message "Expected a different type of list"
            ]
    pure (Bool ** TIsNil fi tDeriv)

  inferType ctx (Head fi ty t) = do
    (List tty ** tDeriv) <- inferType ctx t
      | (wt ** wrongDeriv) => Error fi
          [ DerivInfo wrongDeriv
          , FoundType wt
          , Message "Expected a list type."
          ]
    let Yes Refl = decEq ty tty
        | No _ => Error fi
            [ DerivInfo tDeriv
            , TypeMissmatch ty tty
            , TypeMissmatch (List ty) (List tty)
            , Message "Expected a different type of list"
            ]
    pure (ty ** THead fi tDeriv)

  inferType ctx (Tail fi ty t) = do
    (List tty ** tDeriv) <- inferType ctx t
      | (wt ** wrongDeriv) => Error fi
          [ DerivInfo wrongDeriv
          , FoundType wt
          , Message "Expected a list type."
          ]
    let Yes Refl = decEq ty tty
        | No _ => Error fi
            [ DerivInfo tDeriv
            , TypeMissmatch ty tty
            , TypeMissmatch (List ty) (List tty)
            , Message "Expected a different type of list"
            ]
    pure (List ty ** TTail fi tDeriv)


  inferTypes : (ctx : Context) -> (tms : Vect n Tm) -> Infer (tys : Vect n Ty ** Derivations ctx tms tys)
  inferTypes ctx [] = pure ([] ** [])
  inferTypes ctx (t :: ts) = do
    (ty  ** tDeriv) <- inferType  ctx t
    (tys ** fields) <- inferTypes ctx ts
    pure (ty :: tys ** (MkDerivation t ty tDeriv) :: fields)

  -- Check if all the alternatives has the same type in their branches.
  inferVariantTypes
    :  (fi : Info) -> (n : Nat) -> (nz : NonZero n) -> (ctx : Context) -> (alts : Vect n (Name, Tm)) -> (tys : Vect n Ty)
    -> Infer (ty : Ty ** VariantDerivations n ctx alts tys ty)
  inferVariantTypes fi (S 0) SIsNonZero ctx ((var,tm) :: []) (t :: []) = do
    (tmty ** tmDeriv) <- inferType (ctx :< (var,VarBind t)) tm
    pure (tmty ** [MkDerivation tm tmty tmDeriv])
  inferVariantTypes fi (S (S n)) SIsNonZero ctx ((var,tm) :: (a :: as)) (t :: (ty :: tys)) = do
    (tyh ** hDeriv) <- inferType (ctx :< (var,VarBind t)) tm
    (tyt ** variantDerivs) <- inferVariantTypes fi (S n) SIsNonZero ctx (a :: as) (ty :: tys)
    let Yes Refl = decEq tyh tyt
        | No _ => Error fi
            ((derivInfos variantDerivs) ++
            [ DerivInfo hDeriv
            , TypeMissmatch tyh tyt
            , Message "Different type found for alternative."
            ])
    pure (tyt ** (MkDerivation tm tyt hDeriv :: variantDerivs))

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

  EPairBeta1 :
             Value v1 -> Value v2           ->
    ------------------------------------------
    Evaluation (First fi1 (Pair fi2 v1 v2)) v1
  
  EPairBeta2 :
              Value v1 -> Value v2           ->
    -------------------------------------------
    Evaluation (Second fi1 (Pair fi2 v1 v2)) v2

  EProj1 :
               Evaluation t t'         ->
    -------------------------------------
    Evaluation (First fi t) (First fi t')

  EProj2 :
                Evaluation t t'          ->
    ---------------------------------------
    Evaluation (Second fi t) (Second fi t')

  EPair1 :
                 Evaluation t1 t1'           ->
    -------------------------------------------
    Evaluation (Pair fi t1 t2) (Pair fi t1' t2)

  EPair2 :
                      Value v1               ->
                 Evaluation t2 t2'           ->
    -------------------------------------------
    Evaluation (Pair fi t1 t2) (Pair fi t1 t2')

  EProjTuple :
                   Value (Tuple fi2 n tms)                 ->
    ---------------------------------------------------------
    Evaluation (Proj fi1 (Tuple fi2 n tms) n j) (index j tms)

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
                         {u : UniqueFields (lvs ++ (f :: lts))}                        ->
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
                            {n : Nat} -> {nz : NonZero n}                           ->
    {tags : Vect n String} -> {alts : Vect n (Name, Tm)} -> {u : UniqueTags n tags} ->
                             ForEach alts (Value . snd)                             ->
                             InVariant tag x vj tags alts                           ->
    ----------------------------------------------------------------------------------
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
