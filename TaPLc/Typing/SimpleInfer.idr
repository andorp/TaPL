module TaPLc.Typing.SimpleInfer

import Data.Vect
import TaPLc.IR.Info
import TaPLc.IR.Type
import TaPLc.Typing.Inference
import Control.Monad.Either


export
data SimpleInfer : Type -> Type where
  MkSimpleInfer : EitherT (List TypeInferenceError) IO a -> SimpleInfer a

export
runSimpleInfer : SimpleInfer a -> IO (Either (List TypeInferenceError) a)
runSimpleInfer (MkSimpleInfer m) = runEitherT m

export
Functor SimpleInfer where
  map f (MkSimpleInfer m) = MkSimpleInfer (map f m)

export
Applicative SimpleInfer where
  pure x = MkSimpleInfer (pure x)
  (MkSimpleInfer f <*> MkSimpleInfer x) = MkSimpleInfer (f <*> x)

export
Monad SimpleInfer where
  join (MkSimpleInfer m) = MkSimpleInfer $ do
    (MkSimpleInfer n) <- m
    n
  (MkSimpleInfer m) >>= k = MkSimpleInfer $ do
    x <- m
    let (MkSimpleInfer n) = k x
    n

Show TypeInferenceError where
  showPrec d (DerivInfo deriv) = showCon d "DerivInfo" "TODO"
  showPrec d (TypeMissmatch expected found) = showCon d "TypeMissmatch" $ showArg expected ++ showArg found
  showPrec d (ArityMissmatch expected found) = showCon d "ArityMissmatch" $ showArg expected ++ showArg found
  showPrec d (TagMissmatch expected found) = showCon d "TagMissmatch" $ showArg expected ++ showArg found
  showPrec d (Message x) = showCon d "Message" $ showArg x
  showPrec d (NotFound ctx i) = showCon d "NotFound" $ showArg "TODO-Ctx" ++ showArg i
  showPrec d (FoundType ty) = showCon d "FoundType" $ showArg ty
  showPrec d (InternalError x) = showCon d "InternalError" $ showArg x

error : {0 a : Type} -> Info -> List TypeInferenceError -> SimpleInfer a 
error fi es = MkSimpleInfer $ do
  liftIO $ printLn fi
  _ <- traverse (liftIO . printLn) es
  throwError es

export 
inferImpl : InferImpl SimpleInfer
inferImpl = MkInferImpl
  { error = error
  }
