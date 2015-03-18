{-# LANGUAGE StandaloneDeriving #-}

module Data.PrimOp where

import Data.Peano

data PrimOp :: Peano -> * where {
    PrimNeg :: PrimOp (Succ Zero);
    PrimEq,  PrimNEq,
    PrimGEq, PrimLEq,
    PrimGÞ,  PrimLÞ,
    PrimAnd, PrimOr, PrimXor,
    PrimShiftL, PrimRotL,
    PrimShiftR, PrimRotR,
    PrimAdd, PrimSub, PrimMul, PrimDiv, PrimRem :: PrimOp (Succ (Succ Zero));
}

deriving instance (Eq   (PrimOp n))
deriving instance (Ord  (PrimOp n))
deriving instance (Show (PrimOp n))
