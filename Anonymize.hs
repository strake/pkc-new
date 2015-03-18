{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}

module Anonymize (Anonymizable (..), anonymize) where

import Control.Arrow
import Control.Category.Unicode
import Data.CList
import Data.Comp.Param.Multi as CD
import Data.Comp.Param.Multi.Derive
import Data.Comp.Param.Multi.Desugar
import Data.Comp.Param.Multi.HDitraversable
import Data.Functor.Compose
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Proxy
import Data.Syntax as S
import Data.Typeable
import Util
import Util.Comp.Param.Multi

class Anonymizable v f g where
    anonymizAlg :: Alg f ((->) (Map v (A a)) `Compose` Trm g a)

instance (Anonymizable v f1 g, Anonymizable v f2 g) => Anonymizable v (f1 :+: f2) g where
    anonymizAlg = caseHD anonymizAlg anonymizAlg

instance {-# OVERLAPPABLE #-} (HDitraversable f, f :<: g) => Anonymizable v f g where
    anonymizAlg = Compose ∘ fmap inject ∘ hdimapM getCompose ∘ hdimap (Compose ∘ pure ∘ CD.Var) id

data XWithNom1 bv t a b i where XWithNom1 :: bv -> t -> b RVal -> XWithNom1 bv t a b RVal

$(derive [smartConstructors, makeHDifunctor, makeEqHD] [''XWithNom1])

instance (HDifunctor f, XWithNom1 bv t :<: f) => Desugar (XWithNom bv t) f where
    desugHom' (XWithNom bm x) = Map.foldrWithKey iXWithNom1 x bm

instance (Ord v, XWith1 t :<: g) => Anonymizable v (XWithNom1 v t) g where
    anonymizAlg (XWithNom1 v t (Compose x)) = Compose $ \ m -> In ∘ inj $ XWith1 t (\ a -> x (Map.insert v a m))

instance (Ord v, XWith1 t :<: g) => Anonymizable v (XWithNom v t) g where
    anonymizAlg = compAlg anonymizAlg (desugHom :: Hom (XWithNom v t) (XWithNom1 v t))

instance (Ord v, Var v :<: g) => Anonymizable v (Var v) g where
    anonymizAlg (S.Var v) = Compose (Map.lookup v & maybe (iVar v) (CD.Var ∘ unA))

anonymize :: ∀ v f g . (HDifunctor f, Anonymizable v f g) => Proxy v -> Term f :-> Term g
anonymize Proxy t = Term $ getCompose (cata (anonymizAlg :: Alg f ((->) (Map v (A a)) `Compose` Trm g a)) t) Map.empty
