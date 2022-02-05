module TaPLc.Typing.Inference

import Data.Vect
import Data.List
import Decidable.Equality

import TaPLc.IR.Type
import TaPLc.IR.Term
import TaPLc.IR.Name
import TaPLc.IR.Info
import TaPLc.IR.Context
import TaPLc.IR.Variant
import TaPLc.IR.Record
import TaPLc.IR.UniqueNames
import TaPLc.Typing.Rules
import TaPLc.Data.Vect
import TaPLc.Data.NonZero
import TaPLc.IR.FFI

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
  Error : {0 a : Type} -> Info -> List TypeInferenceError -> Infer a

public export
record InferImpl (m : Type -> Type) where
  constructor MkInferImpl
  error : {0 a : Type} -> Info -> List TypeInferenceError -> m a

export partial
runInfer : (Monad m) => InferImpl m -> Infer a -> m a
runInfer i (Pure x)          = pure x
runInfer i (Bind m k)        = runInfer i m >>= (runInfer i . k)
runInfer i (Error fi errors) = i.error fi errors

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


isFFIType : (t : Ty) -> Dec (bt : BaseType ** FFI bt t)
isFFIType Bool          = Yes (_ ** Bool)
isFFIType (Arr x y)     = No (\(MkDPair a b) => uninhabited b)
isFFIType Unit          = No (\(MkDPair a b) => uninhabited b)
isFFIType (Tuple n xs)  = No (\(MkDPair a b) => uninhabited b)
isFFIType (Record r)    = No (\(MkDPair a b) => uninhabited b)
isFFIType (Variant v)   = No (\(MkDPair a b) => uninhabited b)
isFFIType (List x)      = No (\(MkDPair a b) => uninhabited b)
isFFIType LitNat        = Yes (_ ** Nat)
isFFIType (Base x)      = Yes (_ ** Base)

mutual

  export covering
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

  inferType ctx (Var fi i n) = do
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

  inferType ctx (Let fi n t b) = do
    (ty1 ** tDeriv) <- inferType ctx t
    (ty2 ** bDeriv) <- inferType (addBinding n ty1 ctx) b
    pure $ (ty2 ** TLet fi tDeriv bDeriv)

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
    let Yes (idx ** inRec) = inNames f fields
        | No _ => Error fi
            [ FoundType rty
            , DerivInfo tDeriv
            , Message "Record doesn't have \{f} field."
            ]
    pure (Vect.index idx tys ** TRProj fi inRec tDeriv)

  inferType ctx (Variant fi tag tj ty) = do
    let (Variant (MkVariant n tags tys u nz)) = ty
        | _ => Error fi
          [ FoundType ty
          , Message "Should have been type of Variant"
          ]
    (tyj1 ** tDeriv) <- inferType ctx tj
    let Yes (idx ** inTags) = inNames tag tags
        | No _ => Error fi
            [ FoundType tyj1
            , DerivInfo tDeriv
            , Message "\{tag} is not found in the Variant"
            ]
    let Yes Refl = decEq tyj1 (index idx tys)
        | No _ => Error fi
            [ DerivInfo tDeriv
            , TypeMissmatch (index idx tys) tyj1
            , Message "Found type in variant was different than expected"
            ]
    pure (Variant (MkVariant n tags tys u nz) ** TVariant fi idx inTags tDeriv)

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

  inferType ctx (LitNat fi l) = do
    pure (LitNat ** TLitNat fi)
  
  inferType ctx (FFI fi (MkFFICall funName n pBaseTypes retBasetype) args) = do
    (tys ** tysDeriv) <- inferTypes ctx args
    let Yes Refl = decEq tys (map Base pBaseTypes)
        | No _ => Error fi
            ([ Message "Different type for FFI Call"
             , Message "One or more type differ for parameters"
             ] ++ (concat $
             zipWith3
              (\ty, baseType, (_ ** _ ** (MkDerivation _ _ deriv)) => case decEq ty (Base baseType) of
                Yes _ => []
                No  _ => [ TypeMissmatch (Base baseType) ty
                         , DerivInfo deriv
                         ])
              (toList tys)
              (toList pBaseTypes)
              (toList tysDeriv)
             ))
    let checkedArgsTys : Derivations ctx args (map Base pBaseTypes) = ?help1
    pure (Base retBasetype ** TFFICall fi tysDeriv)
  
  inferType ctx (FFIVal fi (MkFFIVal baseType _)) = do
    pure (Base baseType ** TFFIVal fi)
  
  inferType ctx (ConvertFFI fi baseType t) = do
    (ty ** tDeriv) <- inferType ctx t
    let (Yes (bt ** b)) = isFFIType ty
        | No _ => Error fi
                    [ Message "Expected FFI type, got different."
                    , FoundType ty
                    , DerivInfo tDeriv
                    ]
    let Yes Refl = decEq bt baseType
        | No _ => Error fi
                    [ Message "FFI representational type differs."
                    , TypeMissmatch (Base baseType) (Base bt)
                    , Message "Original FFI conversion"
                    , TypeMissmatch (Base baseType) LitNat
                    ]
    pure (Base baseType ** TConvertFFI fi b tDeriv)

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
