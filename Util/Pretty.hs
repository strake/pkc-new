module Util.Pretty where

import Control.Applicative
import Data.String
import Text.PrettyPrint.Mainland

encloseSepEnd :: Doc -> Doc -> Doc -> [Doc] -> Doc
encloseSepEnd l r p ds = l <> align (sep ((<> p) <$> ds)) <> r

instance IsString Doc where fromString = string
