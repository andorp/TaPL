module TaPLc.Semantics.Substituition

import Data.List
import Data.Vect

import TaPLc.IR.Term
import TaPLc.IR.Name
import TaPLc.IR.Record
import TaPLc.IR.Variant

-- Substituition assumes unique names, no need for alpha conversions.
-- TODO: Check if this right.
export total
substituition : (Name, Tm) -> Tm -> Tm
substituition (var, s) = subst []
  where
    subst : List Name -> Tm -> Tm
    subst xs (Var fi i) = case inBounds i xs of
      Yes found => case index i xs == var of
        False => Var fi i
        True  => s
      No notFound => Var fi i -- This shouldn't happen. Improve subst later on.
    subst xs (Abs fi y ty t)  = Abs fi y ty (subst (y :: xs) t)
    subst xs (True      fi          ) = True fi
    subst xs (False     fi          ) = False fi
    subst xs (If        fi p t e    ) = If fi (subst xs p) (subst xs t) (subst xs e)
    subst xs (App       fi t1 t2    ) = App fi (subst xs t1) (subst xs t2)
    subst xs (Unit      fi          ) = Unit fi
    subst xs (Seq       fi t1 t2    ) = Seq fi (subst xs t1) (subst xs t2)
    subst xs (Let       fi n t b    ) = Let fi n (subst xs t) (subst xs b)
    subst xs (Tuple     fi n ti     ) = Tuple fi n (assert_total (map (subst xs) ti))
    subst xs (Proj      fi vt n i   ) = Proj fi (subst xs vt) n i
    subst xs (Record    fi rt       ) = Record fi (assert_total (map (subst xs) rt))
    subst xs (ProjField fi field t  ) = ProjField fi field (subst xs t)
    subst xs (Variant   fi tag t ty ) = Variant fi tag (subst xs t) ty
    subst xs (Case      fi t alts   ) = Case fi (subst xs t) (assert_total (map (\(tag, tm) => (tag, subst xs tm)) alts))
    subst xs (Fix       fi t        ) = Fix fi (subst xs t)
    subst xs (Nil       fi ty       ) = Nil fi ty
    subst xs (Cons      fi ty h t   ) = Cons fi ty (subst xs h) (subst xs t)
    subst xs (IsNil     fi ty t     ) = IsNil fi ty (subst xs t)
    subst xs (Head      fi ty t     ) = Head fi ty (subst xs t)
    subst xs (Tail      fi ty t     ) = Tail fi ty (subst xs t)