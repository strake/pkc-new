{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TemplateHaskell #-}

module TypInfer where

import Control.Applicative
import Control.Category.Unicode
import Control.Monad
import Control.Monad.Classes as M
import Data.CList
import Data.Comp.Param.Multi as CD
import Data.Comp.Param.Multi.Derive
import Data.Comp.Param.Multi.HDitraversable
import Data.Foldable
import Data.Foldable.Unicode
import Data.Function (on)
import Data.Functor.Compose
import Data.Functor.Product
import "graph" Data.Graph as Gr
import Data.Map (Map)
import qualified Data.Map as Map
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MSet
import Data.PrimOp
import Data.Syntax as S
import Data.Typeable
import Util
import Util.Comp.Param.Multi

fresh :: (Enum a) => MonadState a m => m a
fresh = M.state (liftA2 (,) id succ)

newtype UnboundFailure bv = UnboundFailure bv

data MismatchFailure t = MismatchFailure (Term t Type) (Term t Type)

data TPrimOp   a b i where TPrimOp :: PrimOp n -> Compose (CList n) b i -> TPrimOp a b Type
data TNullable a b i where TNullable :: TNullable a b i

$(derive [smartConstructors, makeHDifunctor] [''TPrimOp, ''TNullable])

instance HDitraversable TPrimOp where hdimapM f (TPrimOp op (Compose xs)) = TPrimOp op ∘ Compose <$> traverse f xs

-- subtype relations of pointers: (s * ≤ t *) ⇔ (s * = t *) ⇔ (s = t)

class Infertile m t f where inferAlgM :: AlgM m f (K (Term t Type))
$(derive [liftSum] [''Infertile])

instance (Ord bv,
          MonadExcept (UnboundFailure bv) m,
          MonadReader (Map bv (Term t Type)) m) =>
         Infertile m t (S.Var bv) where
    inferAlgM (S.Var v) = Map.lookup v <$> ask >>= maybe (throw $ UnboundFailure v) (pure ∘ K)
instance (Tuple :<: t, Applicative m) => Infertile m t Tuple where
    inferAlgM (Tuple (Compose (fmap unK -> ts))) = (pure ∘ K) (Term $ (iTuple ∘ Compose) (unTerm <$> ts))
instance (OrdHD t, HDifunctor t, TIntegral :<: t, TPly :<: t, Tuple :<: t, Var TV :<: t, Var () :<: t,
          MonadState (Graph (Term t Type) () ()) m,
          MonadState TV m) =>
         Infertile m t Lit where
    inferAlgM (Lit l) = K <$> inferL l
      where inferL :: Literal -> m (Term t Type)
            inferL (LInteger _) = fresh >>= \ (v :: TV) ->
                                  subsume (Term $ iVar v) (Term $ iTPly (iTIntegral True) (iVar ()) :: Term t Type) >> pure (Term $ iVar v)
            inferL (LTuple ls) = (\ ts -> Term $ (iTuple ∘ Compose) (unTerm <$> ts)) <$> traverse inferL ls
instance (TPtr :<: t, Applicative m) => Infertile m t XPtr where
    inferAlgM (XPtr (K t)) = (pure ∘ K) (Term $ iTPtr (unTerm t))
instance (OrdHD t, HDifunctor t, TPtr :<: t, Var TV :<: t,
          MonadState (Graph (Term t Type) () ()) m,
          MonadState TV m) =>
         Infertile m t XFollow where
    inferAlgM (XFollow (K t)) = fresh >>= \ (v :: TV) -> subsume t (Term $ iTPtr (iVar v)) >> (pure ∘ K) (Term $ iVar v)
instance (OrdHD t, HDifunctor t, TFunc :<: t, Var TV :<: t,
          MonadState (Graph (Term t Type) () ()) m,
          MonadState TV m) =>
         Infertile m t XCall where
    inferAlgM (XCall (K t) (K s)) = fresh >>= \ (v :: TV) -> subsume t (Term $ iTFunc (unTerm s) (iVar v)) >> (pure ∘ K) (Term $ iVar v)
instance (OrdHD t, HDifunctor t, TPrimOp :<: t, Var TV :<: t,
          MonadState (Graph (Term t Type) () ()) m,
          MonadState TV m) =>
         Infertile m t XPrimOp where
    inferAlgM (XPrimOp op (Compose (fmap unK -> ts))) = fresh >>= \ (v :: TV) -> subsume (Term $ (iTPrimOp op ∘ Compose) (unTerm <$> ts)) (Term $ iVar v :: Term t Type) >> (pure ∘ K) (Term $ iVar v)
instance (Applicative m) =>
         Infertile m t (XCast (Term t Type)) where
    inferAlgM (XCast t (K x)) = (pure ∘ K) t
instance (OrdHD t, HDifunctor t,
          MonadState (Graph (Term t Type) () ()) m) =>
         Infertile m t XIf where
    inferAlgM (XIf (K r) (K s) (K t)) = subsume s t >> subsume t s >> {- iCHasNull r -} (pure ∘ K) t
instance (OrdHD t, HDifunctor t,
          MonadState (Graph (Term t Type) () ()) m) =>
         Infertile m t XConj where
    inferAlgM (XConj (K s) (K t)) = subsume s t >> subsume t s >> {- iCHasNull t -} (pure ∘ K) t
instance (OrdHD t, HDifunctor t,
          MonadState (Graph (Term t Type) () ()) m) =>
         Infertile m t XDisj where
    inferAlgM (XDisj (K s) (K t)) = subsume s t >> subsume t s >> {- iCHasNull t -} (pure ∘ K) t
instance (OrdHD t, HDifunctor t, Tuple :<: t,
          MonadState (Graph (Term t Type) () ()) m) =>
         Infertile m t XAssign where
    inferAlgM (XAssign (K s) (K t)) = subsume t s >> (pure ∘ K) (Term $ iTuple (Compose []))
instance (Applicative m) =>
         Infertile m t (XWith1 (Term t Type)) where
    inferAlgM (XWith1 t f) = pure (f (A (K t)))
instance (Applicative m) =>
         Infertile m t XThen where
    inferAlgM (XThen (K _) (K t)) = (pure ∘ K) t
instance (Tuple :<: t,
          MonadState (Graph (Term t Type) () ()) m) =>
         Infertile m t XLoop where
    inferAlgM (XLoop (K r) (K s) (K t)) = {- iCHasNull r -} (pure ∘ K) (Term $ iTuple (Compose []))
instance (OrdHD t, HDifunctor t, Var () :<: t,
          MonadReader (Term t Type) m,
          MonadState (Graph (Term t Type) () ()) m) =>
         Infertile m t XReturn where
    inferAlgM (XReturn (Compose (fmap unK -> m_t))) = maybe (return ()) (\ t -> ask >>= subsume t) m_t >> (pure ∘ K) (Term $ iVar ())

subsume :: (Ord a) => MonadState (Graph a () ()) m => a -> a -> m ()
subsume s t = modify (Gr.insert (MSet.empty, s, (), MSet.fromList [(t, ())]))

newtype TV = TV Int deriving (Eq, Ord, Show, Enum)
