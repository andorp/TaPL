module TaPLc.IR.Context

import TaPLc.IR.Type
import TaPLc.IR.Name

%default total

public export
data Binding : Type where
  VarBind  : (ty : Ty) -> Binding

public export
data Context : Type where
  Lin  : Context
  (:<) : Context -> (Name, Binding) -> Context

public export
data InContext : Nat -> Ty -> Context -> Type where
  Here  : InContext 0 ty (ctx :< (n, VarBind ty))
  There : InContext n ty ctx -> InContext (S n) ty (ctx :< b)

export Uninhabited (InContext _ _ Lin) where uninhabited _ impossible

-- export
-- extend
--   :  {gamma, delta : Context}
--   -> ({n,m : Nat} -> {a : Ty} -> InContext n a gamma -> InContext m a delta)
--   -> ({n,m : Nat} -> {a,b : Ty} -> {v1, v2 : Name}
--       -> InContext n a (gamma :< (v1,VarBind b))
--       -> InContext m a (delta :< (v2,VarBind b)))
-- extend f Here = Here
-- extend f (There x) = There (f x)

total
public export
thereInjective : InContext (S n) ty (ctx :< b) -> InContext n ty ctx
thereInjective (There x) = x

total
public export
inContext : (ctx : Context) -> (i : Nat) -> Dec (ty : Ty ** InContext i ty ctx)
inContext [<] 0                     = No (\inCtxt => uninhabited (snd inCtxt))
inContext [<] (S k)                 = No (\inCtxt => uninhabited (snd inCtxt))
inContext (x :< (y, (VarBind t))) 0 = Yes (t ** Here)
inContext (x :< y) (S k)            = case inContext x k of
  Yes   found => Yes (case found of { (ty ** there) => (ty ** There there) })
  No notFound => No (\(ty ** there) => notFound (ty ** thereInjective there))

total
public export
indexToName : (ctx : Context) -> (i : Nat) -> (inCtx : InContext i ty ctx) -> Name
indexToName (ctx :< (n, VarBind ty))  0     Here      = n
indexToName (ctx :< b)                (S n) (There x) = indexToName ctx n x

total
public export
addBinding : Name -> Ty -> Context -> Context
addBinding n ty ctx = ctx :< (n, VarBind ty)

public export
(++) : Context -> Context -> Context
(++) sy [<] = sy
(++) sy (sx :< x) = (sy ++ sx) :< x

namespace Length

  public export
  data Length : Context -> Nat -> Type where
    Z : Length [<] Z
    S : Length c n -> Length (c :< x) (S n)

namespace InCtxNat

  export
  extend : (Nat -> Nat) -> Nat -> Nat
  extend f Z = Z
  extend f (S x) = S (f x)

namespace InCtxt

  public export
  data InCtxt : Context -> Ty -> Type where
    Here  : InCtxt (ctx :< (n, VarBind ty)) ty
    There : InCtxt ctx ty -> InCtxt (ctx :< b) ty

  export
  length : InCtxt ctx ty -> Nat
  length = ?xl

  export
  extend
    :  {gamma, delta : Context}
    -> ({a : Ty} -> InCtxt gamma a -> InCtxt delta a)
    -> ({a,b : Ty} -> {v1, v2 : Name}
        -> InCtxt (gamma :< (v1,VarBind b)) a
        -> InCtxt (delta :< (v2,VarBind b)) a)
  extend f Here = Here
  extend f (There x) = There (f x)

  export
  asInContext : (ctx : InCtxt gamma a) -> InContext (length ctx) a gamma
  asInContext = ?xasInContext

  export
  asInCtxt : InContext n a gamma -> InCtxt gamma a
  asInCtxt Here = Here
  asInCtxt (There x) = There (asInCtxt x)
  