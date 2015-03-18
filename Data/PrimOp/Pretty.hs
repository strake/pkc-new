{-# LANGUAGE OverloadedStrings #-}

module Data.PrimOp.Pretty where

import Data.PrimOp
import Text.PrettyPrint.Mainland
import Util.Pretty

instance Pretty (PrimOp n) where
    ppr PrimNeg = "¬"
    ppr PrimEq  = "="
    ppr PrimNEq = "≠"
    ppr PrimGEq = "≥"
    ppr PrimLEq = "≤"
    ppr PrimGÞ  = ">"
    ppr PrimLÞ  = "<"
    ppr PrimAnd = "∧"
    ppr PrimOr  = "∨"
    ppr PrimXor = "⊻"
    ppr PrimShiftL = "<<"
    ppr PrimShiftR = ">>"
    ppr PrimRotL   = "<<<"
    ppr PrimRotR   = ">>>"
    ppr PrimAdd = "+"
    ppr PrimSub = "-"
    ppr PrimMul = "×"
    ppr PrimDiv = "/"
