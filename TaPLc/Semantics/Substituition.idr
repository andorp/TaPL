module TaPLc.Semantics.Substituition

import Data.List
import Data.Vect

import TaPLc.IR.Info
import TaPLc.IR.Term
import TaPLc.IR.Name
import TaPLc.IR.Record
import TaPLc.IR.Variant

import Debug.Trace


-- Substituition assumes unique names, no need for alpha conversions.
-- TODO: Check if this right. Nope, this needs to be fixed.
export total
substituition : (Name, Tm) -> Tm -> Tm
substituition (var, s) = subst []
  where
    subst : List Name -> Tm -> Tm
    subst xs (Var fi i) = case inBounds i xs of
      Yes found => case trace ("substituition: found \{show (i,xs,var)}") (index i xs == var) of
        False => Var fi i
        True  => s
      No notFound => trace "substituition: notFound \{show (xs,var,fi,i)}" $ Var fi i -- This shouldn't happen. Improve subst later on.
    subst xs (Abs fi y ty t)  = Abs fi y ty (subst (y :: xs) t)
    subst xs (True      fi          ) = True fi
    subst xs (False     fi          ) = False fi
    subst xs (If        fi p t e    ) = If fi (subst xs p) (subst xs t) (subst xs e)
    subst xs (App       fi t1 t2    ) = App fi (subst xs t1) (subst xs t2)
    subst xs (Unit      fi          ) = Unit fi
    subst xs (Seq       fi t1 t2    ) = Seq fi (subst xs t1) (subst xs t2)
    subst xs (Let       fi n t b    ) = Let fi n (subst xs t) (subst (n :: xs) b)
    -- Reason for assert_total: map function on Vect is total and ti is structurally smaller then Tuple
    subst xs (Tuple     fi n ti     ) = Tuple fi n (assert_total (map (subst xs) ti))
    subst xs (Proj      fi vt n i   ) = Proj fi (subst xs vt) n i
    -- Reason for assert_total: map function on Vect is total and rt is structurally smaller then Record
    subst xs (Record    fi rt       ) = Record fi (assert_total (map (subst xs) rt))
    subst xs (ProjField fi field t  ) = ProjField fi field (subst xs t)
    subst xs (Variant   fi tag t ty ) = Variant fi tag (subst xs t) ty
    -- Reason for assert_total: map function on Vect is total and alts is structurally smaller then Case
    subst xs (Case      fi t alts   ) = Case fi (subst xs t) (assert_total (map (\(tag, tm) => (tag, subst xs tm)) alts))
    subst xs (Fix       fi t        ) = Fix fi (subst xs t)
    subst xs (Nil       fi ty       ) = Nil fi ty
    subst xs (Cons      fi ty h t   ) = Cons fi ty (subst xs h) (subst xs t)
    subst xs (IsNil     fi ty t     ) = IsNil fi ty (subst xs t)
    subst xs (Head      fi ty t     ) = Head fi ty (subst xs t)
    subst xs (Tail      fi ty t     ) = Tail fi ty (subst xs t)
    subst xs (LitNat    fi l        ) = LitNat fi l
    -- Reason for assert_total: map function on Vect is total and args is structurally smaller then FFI
    subst xs (FFI       fi c args   ) = FFI fi c (assert_total (map (subst xs) args))
    subst xs (FFIVal    fi v        ) = FFIVal fi v
    subst xs (ConvertFFI fi bt t    ) = ConvertFFI fi bt (subst xs t)
