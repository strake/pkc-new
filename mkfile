Main: Util/Pretty.hs Data/Token.hs Data/Nat.hs Data/PrimOp.hs Data/PrimOp/Pretty.hs Data/Linkage.hs Data/CList.hs Util/Comp/Param/Multi.hs Util/Parse.hs Data/Text/Pos.hs Data/Syntax.hs Util/Parse/ToLExpr.hs Data/Pretty.hs Data/Syntax/Pretty.hs Lex.hs Parse.hs
	ghc --make -j -XUnicodeSyntax -XLambdaCase -XTypeOperators -XViewPatterns -XNoMonomorphismRestriction -XRankNTypes -XScopedTypeVariables -XGADTs -XMultiParamTypeClasses -XFlexibleContexts -XFlexibleInstances -XPolyKinds -XDataKinds -XConstraintKinds -XDeriveFunctor -XDeriveFoldable -fcontext-stack=48 Main

Parse.hs: Parse.g
	frown -Occompact -l frownScan Parse.g

clean:V:
	find . | 9 grep '(\.(dyn_)?(hi|o)|^(./)?Parse.hs[0-9]*)$' | xargs rm -f
	rm -f Main
