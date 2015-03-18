{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Data.Syntax.Pretty () where

import Control.Applicative
import Control.Category.Unicode
import Control.Monad.Free
import Data.CList
import Data.Comp.Param.Multi
import Data.Foldable.Unicode
import qualified Data.Map as Map
import Data.Monoid
import Data.Ord.Unicode
import Data.Pretty
import Data.PrimOp
import Data.PrimOp.Pretty
import Data.Syntax as S
import Data.Traversable
import Text.PrettyPrint.Mainland hiding (Pretty)
import qualified Text.PrettyPrint.Mainland as Mainland
import Util.Comp.Param.Multi
import Util.Pretty
import Util

instance Pretty Lit where prettyAlg (Lit l) = (K ∘ pure) (ppr l)
instance Pretty (Var [Char]) where prettyAlg (S.Var v) = (K ∘ pure) (string v)
instance Pretty Tuple where prettyAlg (Tuple (Compose ts)) = (K ∘ pure ∘ tuple ∘ ($ 0) ∘ traverse unK) ts

instance Pretty TIntegral where
    prettyAlg (TIntegral True)  = (K ∘ pure) "Int"
    prettyAlg (TIntegral False) = (K ∘ pure) "Nat"
instance Pretty (TStruct [Char]) where
    prettyAlg (TStruct (Compose (Compose ms))) = (K ∘ pure ∘ encloseSepEnd "{" "}" "," ∘ fmap (\ (m_v, K t) -> maybe "_" string m_v <+> ":" <+> t 0)) ms
instance Pretty TFunc where prettyAlg (TFunc (K s) (K t)) = atPrec 1 $ s 1 <+> "->" <+/> t 0
instance Pretty TPtr  where prettyAlg (TPtr (K t))        = atPrec 2 $ t 1 <+> "*"
instance Pretty TPly  where prettyAlg (TPly (K s) (K t))  = atPrec 3 $ s 2 <+/> t 3

instance Pretty (XStruct [Char]) where
    prettyAlg (XStruct (Compose mm)) = (K ∘ pure ∘ encloseSepEnd "{" "}" ";" ∘ fmap (\ (v, K x) -> string v <+> "≔" <+> x 0)) (Map.toList mm)
instance Pretty (XWithNom bv t)  where prettyAlg (XWithNom _ (K x))        = atPrec  1 $ "with" <+> parens "error: Pretty XWithNom unimpl" <+> x 0
instance Pretty XLoop            where prettyAlg (XLoop (K q) (K x) (K y)) = atPrec  1 $ "for" <+> q 1 <+> x 1 <+/> y 0
instance Pretty XAssign          where prettyAlg (XAssign (K y) (K x))     = atPrec  1 $ y 1 <+> "≔" <+> x 1
instance Pretty (XCast t)        where prettyAlg (XCast _ (K x))           = atPrec  2 $ x 1 <+> ":" <+> "error: Pretty XCast unimpl"
instance Pretty XIf              where prettyAlg (XIf (K q) (K x) (K y))   = atPrec  3 $ q 3 <+> "?" <+> x 3 <+> "!" <+/> y 2
instance Pretty XDisj            where prettyAlg (XDisj (K x) (K y))       = atPrec  4 $ x 3 <+> "?!" <+/> y 3
instance Pretty XConj            where prettyAlg (XConj (K x) (K y))       = atPrec  5 $ x 4 <+> "&&" <+/> y 4
instance Pretty XPrimOp          where
    prettyAlg (XPrimOp op (Compose (K x :. Nil)))                          = atPrec 11 $ ppr op <+> x 10
    prettyAlg (XPrimOp op (Compose (K x :. K y :. Nil)))                   = let
        (q,l,r) | op ∈ [PrimEq, PrimNEq, PrimGEq, PrimLEq, PrimGÞ, PrimLÞ] = ( 6, False, False)
                | op ∈ [PrimAnd, PrimOr, PrimXor]                          = ( 7, True,  True)
                | op ∈ [PrimShiftL, PrimShiftR, PrimRotL, PrimRotR]        = ( 8, False, True)
                | op ∈ [PrimAdd]                                           = ( 9, True,  True)
                | op ∈ [PrimSub]                                           = ( 9, True,  False)
                | op ∈ [PrimMul]                                           = (10, True,  True)
                | op ∈ [PrimDiv]                                           = (10, True,  False)
                | op ∈ [PrimRem]                                           = (10, False, False)
                                                                          in atPrec  q $ x (l ? q-1 $ q) <+> ppr op <+> y (r ? q-1 $ q)
instance Pretty XFollow          where prettyAlg (XFollow (K x))           = atPrec 11 $ "*" <+> x 10
instance Pretty XCall            where prettyAlg (XCall (K f) (K x))       = atPrec 12 $ f 11 <+> x 12
instance Pretty XReturn          where prettyAlg (XReturn (Compose m_x))   = atPrec 12 $ "return" <> maybe mempty (\ (K x) -> softline <> x 12) m_x
instance Pretty (XMember [Char]) where prettyAlg (XMember sel (K x))       = atPrec 13 $ x 12 <> "." <> (iter tuple ∘ either (fmap ppr) (fmap string)) sel
instance Pretty XThen where
    prettyAlg (XThen (K x) (K y)) = K ∘ pure ∘ parens $ x 0 <> ";" <+/> y 0

atPrec :: Int -> Doc -> K (Int -> Doc) a
atPrec q x = K $ \ p -> (p ≥ q ? parens $ id) x

instance Mainland.Pretty Literal where
    ppr (LInteger n) = ppr n
    ppr (LTuple ls) = tuple (ppr <$> ls)
