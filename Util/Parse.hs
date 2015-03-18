module Util.Parse where

newtype Node f g b i = Node { unNode :: ∀ a . f a (g a b) i };

liftNode :: (∀ a . f a (g a b) i -> d a (e a c) j) -> Node f g b i -> Node d e c j;
liftNode f (Node x) = Node (f x);

liftNode2 :: (∀ a . φ a (χ a b) i -> ψ a (ω a c) j -> f a (g a d) k) -> Node φ χ b i -> Node ψ ω c j -> Node f g d k;
liftNode2 f (Node x) (Node y) = Node (f x y);
