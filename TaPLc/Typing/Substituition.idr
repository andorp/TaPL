module TaPLc.Typing.Substituition

import TaPLc.IR.Name
import TaPLc.IR.Term
import TaPLc.IR.Type
import TaPLc.IR.Context
import TaPLc.Typing.Rules
import TaPLc.Semantics.Substituition

||| Substituition doesn't change the type of the term.
export
keepsType
  :  (t1, t2 : Tm)
  -> (x1 : Name)
  -> (ty1, ty2 : Ty)
  -> (t1Deriv : [<] |- (t1 <:> ty1))
  -> (t2Deriv : ([<] :< (x1, VarBind ty1)) |- (t2 <:> ty2))
  -> ([<] |- substituition (x1, t1) t2 <:> ty2)
keepsType = ?kt
