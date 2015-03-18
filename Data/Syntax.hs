{-# LANGUAGE TemplateHaskell #-}

module Data.Syntax where

import Control.Applicative
import Control.Category.Unicode
import Control.Monad.Free
import Data.CList
import Data.Comp.Param.Multi
import Data.Comp.Param.Multi.Derive
import Data.Comp.Param.Multi.Equality ()
import Data.Comp.Param.Multi.HDitraversable
import Data.Comp.Param.Multi.Show ()
import Data.Function (on)
import Data.Functor.Compose as Functor
import Data.Map (Map)
import qualified Data.Map as Map
import Data.PrimOp
import Data.Traversable
import Util

data LVal
data RVal

data Type

data Literal = LInteger Integer | LTuple [Literal] deriving (Eq, Show)

data Var       bv   a b i where  Var      :: bv -> Var bv a b i
data Tuple          a b i where  Tuple    :: Compose [] b c -> Tuple a b i
data Lit            a b i where  Lit      :: Literal -> Lit a b i

data XPtr           a b i where XPtr      :: b RVal -> XPtr a b RVal
data XFollow        a b i where XFollow   :: b RVal -> XFollow a b i
data XCall          a b i where XCall     :: b RVal -> b RVal -> XCall a b RVal
data XMember   bm   a b i where XMember   :: Either (Free [] Int) (Free [] bm) -> b i -> XMember bm a b i
data XStruct   bm   a b i where XStruct   :: Compose (Map bm) b RVal -> XStruct bm a b RVal
data XUnion    bm   a b i where XUnion    :: bm -> b RVal -> XUnion bm a b RVal
data XPrimOp        a b i where XPrimOp   :: PrimOp n -> Compose (CList n) b RVal -> XPrimOp a b RVal
data XCast        t a b i where XCast     :: t -> b RVal -> XCast t a b RVal
data XIf            a b i where XIf       :: b i -> b i -> b i -> XIf a b i
data XConj          a b i where XConj     :: b i -> b i -> XConj a b i
data XDisj          a b i where XDisj     :: b i -> b i -> XDisj a b i
data XAssign        a b i where XAssign   :: b LVal -> b RVal -> XAssign a b RVal
data XWithNom  bv t a b i where XWithNom  :: Map bv t -> b RVal -> XWithNom bv t a b RVal
data XWith1       t a b i where XWith1    :: t -> (A a -> b RVal) -> XWith1 t a b RVal
data XThen          a b i where XThen     :: b RVal -> b RVal -> XThen a b RVal
data XLoop          a b i where XLoop     :: b RVal -> b RVal -> b RVal -> XLoop a b RVal; -- Loop p x y in C = for (; p; x) y
data XReturn        a b i where XReturn   :: Compose Maybe b RVal -> XReturn a b RVal

-- ignore kinds for now
data TPtr           a b i where TPtr      :: b Type -> TPtr a b Type
data TFunc          a b i where TFunc     :: b Type -> b Type -> TFunc a b Type
data TIntegral      a b i where TIntegral :: Signedness -> TIntegral a b i
data TStruct   bm   a b i where TStruct   :: Compose (Compose [] ((,) (Maybe bm))) b Type -> TStruct bm a b Type
data TUnion    bm   a b i where TUnion    :: Compose (Compose [] ((,) (Maybe bm))) b Type -> TUnion  bm a b Type
data TPly           a b i where TPly      :: b Type -> b Type -> TPly a b Type

type Signedness = Bool
type Mutability = Bool

$(derive [smartConstructors, makeHDifunctor, makeEqHD]
  [''Var, ''Tuple, ''Lit,
   ''XPtr, ''XFollow, ''XCall, ''XMember, ''XStruct, ''XUnion, ''XCast, ''XIf, ''XConj, ''XDisj, ''XAssign, ''XWithNom, ''XThen, ''XLoop, ''XReturn,
   ''TPtr, ''TFunc, ''TIntegral, ''TStruct, ''TUnion, ''TPly])

$(derive [smartConstructors, makeHDifunctor] [''XPrimOp])

instance HDifunctor (XWith1 t) where hdimap f g (XWith1 t x) = XWith1 t (g ∘ x ∘ \ a -> A (f (unA a)))

instance HDitraversable (Var bv) where hdimapM f (Data.Syntax.Var v) = pure (Data.Syntax.Var v)
instance HDitraversable Tuple where hdimapM f (Tuple (Compose xs)) = Tuple ∘ Compose <$> traverse f xs
instance HDitraversable Lit where hdimapM f (Lit l) = pure (Lit l)

instance HDitraversable XPtr where hdimapM f (XPtr x) = XPtr <$> f x
instance HDitraversable XFollow where hdimapM f (XFollow x) = XFollow <$> f x
instance HDitraversable XCall where hdimapM f (XCall x y) = (liftA2 XCall `on` f) x y
instance HDitraversable (XMember bm) where hdimapM f (XMember sel x) = XMember sel <$> f x
instance HDitraversable (XStruct bm) where hdimapM f (XStruct (Compose mm)) = XStruct ∘ Compose <$> traverse f mm
instance HDitraversable (XUnion bm) where hdimapM f (XUnion v x) = XUnion v <$> f x
instance HDitraversable XPrimOp where hdimapM f (XPrimOp op (Compose xs)) = XPrimOp op ∘ Compose <$> traverse f xs
instance HDitraversable (XCast t) where hdimapM f (XCast t x) = XCast t <$> f x
instance HDitraversable XIf where hdimapM f (XIf p x y) = (liftA3 XIf `onn` f) p x y
instance HDitraversable XConj where hdimapM f (XConj x y) = (liftA2 XConj `on` f) x y
instance HDitraversable XDisj where hdimapM f (XDisj x y) = (liftA2 XDisj `on` f) x y
instance HDitraversable XAssign where hdimapM f (XAssign y x) = liftA2 XAssign (f y) (f x)
instance HDitraversable (XWithNom bv t) where hdimapM f (XWithNom bm x) = XWithNom bm <$> f x
instance HDitraversable XThen where hdimapM f (XThen x y) = (liftA2 XThen `on` f) x y
instance HDitraversable XLoop where hdimapM f (XLoop p x y) = (liftA3 XLoop `onn` f) p x y
instance HDitraversable XReturn where hdimapM f (XReturn (Compose m_x)) = XReturn ∘ Compose <$> traverse f m_x
