{-# LANGUAGE UndecidableInstances #-}

module Util.Parse.ToLExpr (toLExpr) where

import Control.Applicative
import Control.Category.Unicode
import Data.Comp.Param.Multi
import Data.Comp.Param.Multi.HDitraversable
import Data.Function (on)
import Data.Syntax as S
import Data.Traversable
import Util
import Util.Comp.Param.Multi
import Util.Parse

newtype Roll f i = Roll { unRoll :: ∀ a . f a (Roll f) i }

toLExpr :: (HDitraversable f, HDifunctor g, ToLExpr f g) => Node (f :&: p) (Cxt NoHole (f :&: p)) (K ()) RVal -> Maybe (Node (g :&: p) (Cxt h (g :&: p)) b LVal)
toLExpr (Node x) = (cataM toLExprAlgM & fmap (unK & unA & nodify)) (Term (In x))

cxtualize :: (HDifunctor f) => Roll f :-> Cxt h f a b
cxtualize (Roll x) = In (hdimap id cxtualize x)

nodify :: (HDifunctor f) => Roll f :-> Node f (Cxt h f) b
nodify (Roll x) = Node (hdimap id cxtualize x)

class ToLExpr f g where toLExprAlgM :: AlgM Maybe (f :&: p) (K (A (Roll (g :&: p))))

instance ( Var     bv   :<: g) => ToLExpr ( Var     bv  ) g where toLExprAlgM (S.Var v :&: p) = (Just ∘ K) (A $ Roll (inj (S.Var v) :&: p))
instance (XPtr          :<: g) => ToLExpr (XPtr         ) g where toLExprAlgM _ = Nothing
instance (XFollow       :<: g) => ToLExpr (XFollow      ) g where toLExprAlgM (XFollow (K (A x)) :&: p) = (Just ∘ K) (A $ Roll (inj (XFollow x) :&: p))
instance (XCall         :<: g) => ToLExpr (XCall        ) g where toLExprAlgM _ = Nothing
instance (XMember  bm   :<: g) => ToLExpr (XMember  bm  ) g where toLExprAlgM (XMember sel (K (A x)) :&: p) = (Just ∘ K) (A $ Roll (inj (XMember sel x) :&: p))
instance ( Tuple        :<: g) => ToLExpr ( Tuple       ) g where toLExprAlgM (Tuple (Compose (fmap (unK & unA) & Compose -> xs)) :&: p) = (Just ∘ K) (A $ Roll (inj (Tuple xs) :&: p))
instance (XStruct  bm   :<: g) => ToLExpr (XStruct  bm  ) g where toLExprAlgM _ = Nothing
instance (XUnion   bm   :<: g) => ToLExpr (XUnion   bm  ) g where toLExprAlgM _ = Nothing
instance ( Lit          :<: g) => ToLExpr ( Lit         ) g where toLExprAlgM _ = Nothing
instance (XPrimOp       :<: g) => ToLExpr (XPrimOp      ) g where toLExprAlgM _ = Nothing
instance (XCast       t :<: g) => ToLExpr (XCast       t) g where toLExprAlgM _ = Nothing
instance (XIf           :<: g) => ToLExpr (XIf          ) g where toLExprAlgM (XIf (K (A q)) (K (A x)) (K (A y)) :&: p) = (Just ∘ K) (A $ Roll (inj (XIf q x y) :&: p))
instance (XConj         :<: g) => ToLExpr (XConj        ) g where toLExprAlgM (XConj (K (A x)) (K (A y)) :&: p) = (Just ∘ K) (A $ Roll (inj (XConj x y) :&: p))
instance (XDisj         :<: g) => ToLExpr (XDisj        ) g where toLExprAlgM (XDisj (K (A x)) (K (A y)) :&: p) = (Just ∘ K) (A $ Roll (inj (XDisj x y) :&: p))
instance (XAssign       :<: g) => ToLExpr (XAssign      ) g where toLExprAlgM _ = Nothing
instance (XWithNom bv t :<: g) => ToLExpr (XWithNom bv t) g where toLExprAlgM _ = Nothing
instance (XThen         :<: g) => ToLExpr (XThen        ) g where toLExprAlgM _ = Nothing
instance (XLoop         :<: g) => ToLExpr (XLoop        ) g where toLExprAlgM _ = Nothing
instance (XReturn       :<: g) => ToLExpr (XReturn      ) g where toLExprAlgM _ = Nothing

instance (ToLExpr f e, ToLExpr g e) => ToLExpr (f :+: g) e where toLExprAlgM = distribAnn & caseHD toLExprAlgM toLExprAlgM

distribAnn :: SigFun ((f :+: g) :&: p) (f :&: p :+: g :&: p)
distribAnn (x :&: p) = caseHD (inj ∘ (:&: p)) (inj ∘ (:&: p)) x
