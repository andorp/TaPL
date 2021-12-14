module TaPLc.TypeInference.Inference

import Data.Vect
import Decidable.Equality

import TaPLc.IR.Type
import TaPLc.IR.Term
import TaPLc.IR.Name
import TaPLc.IR.Info
import TaPLc.IR.Context
import TaPLc.IR.Variant
import TaPLc.IR.Record
import TaPLc.IR.UniqueNames
import TaPLc.TypeInference.TypingRules
import TaPLc.Data.Vect
import TaPLc.Data.NonZero

%default total

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

public export
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


namespace VariantFieldIndex

  total
  fieldIndexGo : (n : Nat) -> (tag : String) -> (tags : Vect n String) -> (infos : Vect n a) -> Dec (i : Nat ** (Index tag i tags, (x : a ** Index x i infos)))
  fieldIndexGo 0       tag []        [] = No (\assumeIndex => uninhabited (fst (snd assumeIndex)))
  fieldIndexGo (S len) tag (x :: xs) (y :: ys) = case decEq x tag of
    Yes Refl => Yes (0 ** (Here, (y ** Here)))
    No x_is_not_tag => case fieldIndexGo len tag xs ys of
      (Yes (MkDPair j (z, MkDPair k w))) => Yes (MkDPair (S j) (There z, MkDPair k (There w)))
      (No notThere) => No (\assumeThere => case assumeThere of
        (MkDPair 0 (Here, (MkDPair y Here))) => x_is_not_tag Refl
        (MkDPair (S n) ((There z), (MkDPair k (There w)))) => notThere (MkDPair n (z, MkDPair k w)))

  total export
  fieldIndex : (tag : String) -> (v : Variant a) -> Dec (i : Nat ** (Index tag i v.tags, (x : a ** Index x i v.info)))
  fieldIndex tag v = fieldIndexGo v.size tag v.tags v.info

mutual

  covering
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

  inferType ctx (Record fi (MkRecord n fields tms u)) = do
    (tys ** fieldDerivations) <- inferTypes ctx tms
    pure (Record (MkRecord n fields tys u) ** TRcd fi fieldDerivations)

  inferType ctx (ProjField fi f t) = do
    (rty@(Record (MkRecord n fields tys u)) ** tDeriv) <- inferType ctx t
      | (wt ** wrongDeriv) => Error fi
          [ FoundType wt
          , DerivInfo wrongDeriv
          , Message "Expected record type."
          ]
    let Yes (ty ** inRec) = inRecord f fields tys
        | No _ => Error fi
            [ FoundType rty
            , DerivInfo tDeriv
            , Message "Record doesn't have \{f} field."
            ]
    pure (ty ** TRProj fi tDeriv inRec)

  inferType ctx (Variant fi tag tj ty) = do
    let (Variant (MkVariant n tags tys u nz)) = ty
        | _ => Error fi
          [ FoundType ty
          , Message "Should have been type of Variant"
          ]
    (tyj1 ** tDeriv) <- inferType ctx tj
    let Yes (j ** (idx1, (tyj2 ** idx2))) = fieldIndex tag (MkVariant n tags tys u nz)
        | No _ => Error fi
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
      | (wt ** wrongDeriv) => Error fi
          [ DerivInfo wrongDeriv
          , FoundType wt
          , Message "Expected variant type"
          ]

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
    (ty ** vDerivs) <- inferVariantCaseTypes fi n_t0 nz_t0 ctx alts tys_t0
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

  covering
  inferTypes : (ctx : Context) -> (tms : Vect n Tm) -> Infer (tys : Vect n Ty ** Derivations ctx tms tys)
  inferTypes ctx [] = pure ([] ** [])
  inferTypes ctx (t :: ts) = do
    (ty  ** tDeriv) <- inferType ctx t
    (tys ** fields) <- inferTypes ctx ts
    pure (ty :: tys ** (MkDerivation t ty tDeriv) :: fields)

  -- Check if all the alternatives has the same type in their branches.
  covering
  inferVariantCaseTypes
    :  (fi : Info) -> (n : Nat) -> (nz : NonZero n) -> (ctx : Context) -> (alts : Vect n (Name, Tm)) -> (tys : Vect n Ty)
    -> Infer (ty : Ty ** VariantDerivations n ctx alts tys ty)
  inferVariantCaseTypes fi (S 0) SIsNonZero ctx ((var,tm) :: []) (t :: []) = do
    (tmty ** tmDeriv) <- inferType (ctx :< (var,VarBind t)) tm
    pure (tmty ** [MkDerivation tm tmty tmDeriv])
  inferVariantCaseTypes fi (S (S n)) SIsNonZero ctx ((var,tm) :: (a :: as)) (t :: (ty :: tys)) = do
    (tyh ** hDeriv) <- inferType (ctx :< (var,VarBind t)) tm
    (tyt ** variantDerivs) <- inferVariantCaseTypes fi (S n) SIsNonZero ctx (a :: as) (ty :: tys)
    let Yes Refl = decEq tyh tyt
        | No _ => Error fi
            ((derivInfos variantDerivs) ++
            [ DerivInfo hDeriv
            , TypeMissmatch tyh tyt
            , Message "Different type found for alternative."
            ])
    pure (tyt ** (MkDerivation tm tyt hDeriv :: variantDerivs))
