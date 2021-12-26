module TaPLc.Semantics.Examples

import Data.Vect
import TaPLc.IR.Info
import TaPLc.IR.Term
import TaPLc.IR.Type
import TaPLc.Semantics.Rules
import TaPLc.Data.Vect


i : Info
i = EmptyInfo

0
isNilEx1
  : Evaluation
      (IsNil i Unit (Cons i Unit (Unit i) (Nil i Unit)))
      (False i)
isNilEx1 = EIsNilCons Unit Nil

0
isNilEx2
  : Evaluation
      (IsNil i Bool (Cons i Bool (IsNil i Unit (Nil i Unit)) (Nil i Bool)))
      (IsNil i Bool (Cons i Bool (True i) (Nil i Bool)))
isNilEx2 = EIsNil ?h1 $ step1
  where
    step1
      : Evaluation
          (Cons i Bool (IsNil i Unit (Nil i Unit)) (Nil i Bool))
          (Cons i Bool (True i) (Nil i Bool))
    step1 = ECons1 (\x => ?step1_rhs_1) EIsNilNil

