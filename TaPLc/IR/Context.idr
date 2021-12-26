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
