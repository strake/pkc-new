module Main where

import Control.Applicative
import Control.Category.Unicode
import Control.Monad.Classes
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Lazy
import Data.Comp.Param.Multi
import Data.Comp.Param.Multi.Show
import Data.Comp.Param.Multi.FreshM
import Data.Pretty
import Data.Syntax.Pretty
import Data.Text.Pos
import Data.Traversable
import System.Console.Terminal.Size
import System.IO
import qualified Text.PrettyPrint.Mainland as Mainland
import Lex
import Parse
import Anonymize
import TypInfer
import Util
import Util.Parse
import Util.Comp.Param.Multi

main = maybe 80 width <$> hSize stdout >>= \ outWidth ->
       getContents >>= runExceptT ∘ evalStateT Parse.top ∘ (\ xs -> LexSt { _lexInput = xs, _lexPos = TextPos (1,0) }) >>=
       either error
       (mapM_ $ \ (v, m_parm, link, mut, t, m_x) ->
        putStr v >> putStr " : " >>
        traverse (putStrLn ∘ Mainland.pretty outWidth ∘ ($ 0) ∘ unK ∘ cata (Data.Comp.Param.Multi.liftA prettyAlg) ∘ \ (Node x) -> Term (In x)) m_x)
