module Util.Comp.Param.Multi where

import Prelude hiding (foldr, and)

import Control.Applicative
import Control.Arrow
import Control.Category.Unicode
import Control.Monad
import qualified Data.Comp as Sim
import Data.Comp.Param.Multi
import Data.Comp.Param.Multi.HDitraversable
import Data.Foldable
import Data.Functor.Compose
import Util

la1 :: (e :<: f) => (Cxt h1 (f1 :&: p) a1 b1 i1 -> e a b i) -> (p -> q) -> (f1 :&: p) a1 (Cxt h1 (f1 :&: p) a1 b1) i1 -> (f :&: q) a b i
la1 c f (x :&: n) = inj (c (In $ x :&: n)) :&: f n

la2 :: (e :<: f) => (Cxt h1 (f1 :&: p) a1 b1 i1 -> Cxt h2 (f2 :&: p) a2 b2 i2 -> e a b i) -> (p -> p -> q) -> (f1 :&: p) a1 (Cxt h1 (f1 :&: p) a1 b1) i1 -> (f2 :&: p) a2 (Cxt h2 (f2 :&: p) a2 b2) i2 -> (f :&: q) a b i
la2 c f (x :&: m) (y :&: n) = la2_ c (x :&: m) (y :&: n) :&: f m n

la2_ :: (e :<: f) => (Cxt h1 (f1 :&: p) a1 b1 i1 -> Cxt h2 (f2 :&: p) a2 b2 i2 -> e a b i) -> (f1 :&: p) a1 (Cxt h1 (f1 :&: p) a1 b1) i1 -> (f2 :&: p) a2 (Cxt h2 (f2 :&: p) a2 b2) i2 -> f a b i
la2_ c (x :&: m) (y :&: n) = inj (c (In $ x :&: m) (In $ y :&: n))

la3 :: (e :<: f) => (Cxt h1 (f1 :&: p) a1 b1 i1 -> Cxt h2 (f2 :&: p) a2 b2 i2 -> Cxt h3 (f3 :&: p) a3 b3 i3 -> e a b i) -> (p -> p -> p -> q) -> (f1 :&: p) a1 (Cxt h1 (f1 :&: p) a1 b1) i1 -> (f2 :&: p) a2 (Cxt h2 (f2 :&: p) a2 b2) i2 -> (f3 :&: p) a3 (Cxt h3 (f3 :&: p) a3 b3) i3 -> (f :&: q) a b i
la3 c f (x :&: m) (y :&: n) (z :&: o) = inj (c (In $ x :&: m) (In $ y :&: n) (In $ z :&: o)) :&: f m n o

laF1 :: (e :<: f, Functor u, Foldable u) =>
        (Compose u (Cxt h1 (f1 :&: p) a1 b1) i1 -> e a b i) -> (p -> q -> q) -> q ->
        u ((f1 :&: p) a1 (Cxt h1 (f1 :&: p) a1 b1) i1) -> (f :&: q) a b i
laF1 c f z0 xs = inj (c (Compose $ In <$> xs)) :&: foldr f z0 (snd ∘ Sim.projectA ∘ projectA <$> xs)

laF1_ :: (e :<: f, Functor u) => (Compose u (Cxt h1 (f1 :&: p) a1 b1) i1 -> e a b i) -> u ((f1 :&: p) a1 (Cxt h1 (f1 :&: p) a1 b1) i1) -> f a b i
laF1_ c xs = inj (c (Compose $ In <$> xs))

laF2 :: (e :<: f, Functor u, Functor v, Foldable u, Foldable v) =>
        (Compose u (Cxt h1 (f1 :&: p) a1 b1) i1 -> Compose v (Cxt h2 (f2 :&: p) a2 b2) i2 -> e a b i) -> (p -> q -> q) -> q ->
        u ((f1 :&: p) a1 (Cxt h1 (f1 :&: p) a1 b1) i1) -> v ((f2 :&: p) a2 (Cxt h2 (f2 :&: p) a2 b2) i2) -> (f :&: q) a b i
laF2 c f z0 xs ys = inj (c (Compose $ In <$> xs) (Compose $ In <$> ys)) :&: foldr f (foldr f z0 (snd ∘ Sim.projectA ∘ projectA <$> xs)) (snd ∘ Sim.projectA ∘ projectA <$> ys)

class (HDitraversable f, HDitraversable g, Monad m) => DesugarM m f g where
    desugHomM :: HomM m f g
    desugHomM = hdimap id Hole >>> desugHomM'

    desugHomM' :: NatM m (f a (Cxt h g a b)) (Cxt h g a b)
    desugHomM' = desugHomM >=> appCxtM

appCxtM :: (HDitraversable f, Applicative m) => NatM m (Cxt Hole f a (Cxt h f a b)) (Cxt h f a b)
appCxtM (In t) = In <$> hdimapM appCxtM t
appCxtM (Hole x) = pure x
appCxtM (Var v) = pure (Var v)
