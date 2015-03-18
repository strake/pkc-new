{-# LANGUAGE TemplateHaskell #-}

module Data.Pretty where

import Control.Applicative
import Control.Category.Unicode
import Data.Comp.Param.Multi
import Data.Comp.Param.Multi.Derive
import Text.PrettyPrint.Mainland hiding (Pretty)
import qualified Text.PrettyPrint.Mainland as Mainland

class Pretty f where prettyAlg :: f a (K (Int -> Doc)) :-> K (Int -> Doc)
$(derive [liftSum] [''Pretty])
