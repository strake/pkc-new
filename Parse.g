module Parse where

import Prelude hiding (foldr)

import Control.Applicative
import Control.Arrow
import Control.Category.Unicode
import Control.Monad.Classes
import Control.Monad.Free
import Data.CList
import Data.Coerce
import qualified Data.Comp as Sim
import Data.Comp.Param.Multi
import Data.Comp.Param.Multi.Ops
import Data.Foldable
import Data.Functor.Identity
import Data.Lens.Monadic.Classes as ML
import Data.Linkage as L
import Data.List as List hiding (foldr)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import Data.PrimOp
import Data.Syntax as S
import Data.Text.Pos
import Data.Token
import Util
import Util.Comp.Param.Multi
import Util.Parse
import Util.Parse.ToLExpr
import Lex

%{

Terminal	= *EOF
		| LParenth as '(' | RParenth as ')'
		| LBracket as '[' | RBracket as ']'
		| LBrace   as '{' | RBrace   as '}'
		| SemiColon as ';' | Comma as ','

		| KeyWord "_"		as "_"

		| KeyWord "with"	as "with"
		| KeyWord "for"		as "for"
		| KeyWord "return"	as "return"

		| KeyWord "@"		as "@"
		| KeyWord "*"		as "*"
		| KeyWord "."		as "."
		| KeyWord ":"		as ":"
		| KeyWord "≔"		as "≔"

		| IntegerLiteral { Integer } as "<integer>"

		| TermName { [Char] }
		| TypeName { [Char] }

		| Symbol "->"

		| Symbol "?!"
		| Symbol "&&"
		| Symbol "="
		| Symbol "≠"
		| Symbol "≥"
		| Symbol "≤"
		| Symbol ">"
		| Symbol "<"
		| Symbol "∧"
		| Symbol "∨"
		| Symbol "⊻"
		| Symbol "⊼"
		| Symbol "⊽"
		| Symbol "<<"
		| Symbol ">>"
		| Symbol "<<<"
		| Symbol ">>>"
		| Symbol "+"
		| Symbol "-"
		| Symbol "×"
		| Symbol "/"

		| Symbol "¬"

		| Symbol "?" | Symbol "!"

		| Symbol "∧="
		| Symbol "∨="
		| Symbol "⊻="
		| Symbol "⊼="
		| Symbol "⊽="
		| Symbol "+="
		| Symbol "-="
		| Symbol "×="
		| Symbol "/="
		| Symbol "<<="
		| Symbol ">>="
		| Symbol "<<<="
		| Symbol ">>>="
		;

right 2 Symbol "?!";
right 3 Symbol "&&";
left  4 Symbol "=";
left  4 Symbol "≠";
left  4 Symbol "≥";
left  4 Symbol "≤";
left  4 Symbol ">";
left  4 Symbol "<";
left  5 Symbol "∧";
left  5 Symbol "∨";
left  5 Symbol "⊻";
left  5 Symbol "⊼";
left  5 Symbol "⊽";
right 6 Symbol "<<";
right 6 Symbol ">>";
right 6 Symbol "<<<";
right 6 Symbol ">>>";
left  7 Symbol "+";
left  7 Symbol "-";
left  8 Symbol "×";
left  8 Symbol "/";

top		{ [([Char], Maybe (Free [] (Maybe [Char], Node (TSignature [Char] [Char] :&: CTR) (Cxt NoHole (TSignature [Char] [Char] :&: CTR)) (K ()) Type)), Linkage, Mutability, Node (TSignature [Char] [Char] :&: CTR) (Cxt NoHole (TSignature [Char] [Char] :&: CTR)) (K ()) Type, Maybe (Node (XSignature [Char] [Char] :&: CTR) (Cxt NoHole (XSignature [Char] [Char] :&: CTR)) (K ()) RVal))] };
top		{ ds }								: sepEndBy topDecl ';' { ds };

topDecl		{ ([Char], Maybe (Free [] (Maybe [Char], Node (TSignature [Char] [Char] :&: CTR) (Cxt NoHole (TSignature [Char] [Char] :&: CTR)) (K ()) Type)), Linkage, Mutability, Node (TSignature [Char] [Char] :&: CTR) (Cxt NoHole (TSignature [Char] [Char] :&: CTR)) (K ()) Type, Maybe (Node (XSignature [Char] [Char] :&: CTR) (Cxt NoHole (XSignature [Char] [Char] :&: CTR)) (K ()) RVal)) };
topDecl		{ (v, Nothing,   L.External, True,  t, Nothing) }		: termName { v }, ":", type { t };
topDecl		{ (v, Nothing,   L.External, True,  t, Just x)  }		: termName { v }, ":", type { t }, "≔", expr { x };
topDecl		{ (v, Just parm, L.External, False, t, Nothing) }		: termName { v }, parm { parm }, ":", type { t };
topDecl		{ (v, Just parm, L.External, False, t, Just x)  }		: termName { v }, parm { parm }, ":", type { t }, "≔", expr { x };

parm		{ Free [] (Maybe [Char], Node (TSignature [Char] [Char] :&: CTR) (Cxt NoHole (TSignature [Char] [Char] :&: CTR)) (K ()) Type) };
parm		{ stlist id Free parm }						: '(', sepBy parm ',' { parm }, ')';
parm		{ Pure (Just v,  t) }						: termName { v }, ":", type { t };
parm		{ Pure (Nothing, t) }						: "_", ":", type { t };

expr		{ Node (XSignature [Char] [Char] :&: CTR) (Cxt NoHole (XSignature [Char] [Char] :&: CTR)) (K ()) RVal };
expr		{ x }								: expr7 { x };

expr0_		{ Node (XSignature [Char] [Char]) (Cxt NoHole (XSignature [Char] [Char] :&: CTR)) (K ()) RVal };
expr0_		{ Node $ stlist (fst ∘ Sim.projectA ∘ projectA) (laF1_ Tuple)
		         (unNode <$> xs) }					: '(', sepBy expr ',' { xs }, ')';
expr0_		{ Node $
		  fst ∘ Sim.projectA ∘ projectA $
		  foldr (la2 XThen (<>))
		  (fromMaybe (inj (Tuple (Compose [])) :&: mempty) (unNode <$> m_x))
		  (unNode <$> x:xs) }						: '(', expr { x }, ';', sepEndBy expr ';' { xs }, opt expr { m_x }, ')';
expr0_		{ Node $ laF1_ XStruct (unNode <$> Map.fromList ms) }		: '{', sepMayEndBy termMember ',' { ms }, '}';
expr0_		{ Node $ inj $ S.Var v }					: termName { v };
expr0_		{ Node $ inj $ Lit (LInteger n) }				: IntegerLiteral { n };

termMember	{ ([Char], Node (XSignature [Char] [Char] :&: CTR) (Cxt NoHole (XSignature [Char] [Char] :&: CTR)) (K ()) RVal) };
termMember	{ (v, x) }							: ".", termName { v }, "≔", expr { x };

expr0		{ Node (XSignature [Char] [Char] :&: CTR) (Cxt NoHole (XSignature [Char] [Char] :&: CTR)) (K ()) RVal };
expr0		{ Node $ x :&: (a :–: b) }					: loc { a }, expr0_ { Node x }, loc { b };

expr1		{ Node (XSignature [Char] [Char] :&: CTR) (Cxt NoHole (XSignature [Char] [Char] :&: CTR)) (K ()) RVal };
expr1		{ x }								: expr0 { x };
expr1		{ Node $ la1 (XMember sel) (const (a :–: b)) x }		: expr1 { Node (x@(_ :&: (a :–: _))) }, ".", selector { sel }, loc { b };

selector	{ Either (Free [] Int) (Free [] [Char]) };
selector	{ Left  kt }							: deepNest "<integer>" '(' ',' ')' { fmap fromIntegral -> kt };
selector	{ Right vt }							: deepNest termName '(' ',' ')' { vt };

expr2a		{ Node (XSignature [Char] [Char] :&: CTR) (Cxt NoHole (XSignature [Char] [Char] :&: CTR)) (K ()) RVal };
expr2a		{ x }								: expr1 { x };
expr2a		{ Node $ la2 XCall (<>) f x }					: expr2a { Node f }, expr1 { Node x };

expr2b		{ Node (XSignature [Char] [Char] :&: CTR) (Cxt NoHole (XSignature [Char] [Char] :&: CTR)) (K ()) RVal };
expr2b		{ Node $
		  laF1 XReturn (<>)
		  (a :–: case unNode <$> m_x of {
		           Just (_ :&: (_ :–: b)) -> b;
		           _ -> b;
		         }) (unNode <$> m_x) }					: loc { a }, "return", loc { b }, opt expr1 { m_x };

expr2		{ Node (XSignature [Char] [Char] :&: CTR) (Cxt NoHole (XSignature [Char] [Char] :&: CTR)) (K ()) RVal };
expr2		{ x }								: expr2a { x };
expr2		{ x }								: expr2b { x };

expr3		{ Node (XSignature [Char] [Char] :&: CTR) (Cxt NoHole (XSignature [Char] [Char] :&: CTR)) (K ()) RVal };
expr3		{ x }								: expr2 { x };
expr3		{ Node $ la1 XFollow (const (a :–: b)) x }			: loc { a }, "*", expr3 { Node (x@(_ :&: (_ :–: b))) };
expr3		{ Node $ laF1 (XPrimOp PrimNeg) (<>) (a :–: b) (pure x) }		: loc { a }, Symbol "¬", expr3 { Node (x@(_ :&: (_ :–: b))) };

expr4		{ Node (XSignature [Char] [Char] :&: CTR) (Cxt NoHole (XSignature [Char] [Char] :&: CTR)) (K ()) RVal };
expr4		{ x }								: expr3 { x };
expr4		{ Node $ la2 XConj (<>) x y }					: expr4 { Node x }, Symbol "&&",  expr4 { Node y };
expr4		{ Node $ la2 XDisj (<>) x y }					: expr4 { Node x }, Symbol "?!",  expr4 { Node y };
expr4		{ Node $ goBinOp "="   x y }					: expr4 { Node x }, Symbol "=",   expr4 { Node y };
expr4		{ Node $ goBinOp "≠"   x y }					: expr4 { Node x }, Symbol "≠",   expr4 { Node y };
expr4		{ Node $ goBinOp "≥"   x y }					: expr4 { Node x }, Symbol "≥",   expr4 { Node y };
expr4		{ Node $ goBinOp "≤"   x y }					: expr4 { Node x }, Symbol "≤",   expr4 { Node y };
expr4		{ Node $ goBinOp ">"   x y }					: expr4 { Node x }, Symbol ">",   expr4 { Node y };
expr4		{ Node $ goBinOp "<"   x y }					: expr4 { Node x }, Symbol "<",   expr4 { Node y };
expr4		{ Node $ goBinOp "∧"   x y }					: expr4 { Node x }, Symbol "∧",   expr4 { Node y };
expr4		{ Node $ goBinOp "∨"   x y }					: expr4 { Node x }, Symbol "∨",   expr4 { Node y };
expr4		{ Node $ goBinOp "⊻"   x y }					: expr4 { Node x }, Symbol "⊻",   expr4 { Node y };
expr4		{ Node $ goBinOp "⊼"   x y }					: expr4 { Node x }, Symbol "⊼",   expr4 { Node y };
expr4		{ Node $ goBinOp "⊽"   x y }					: expr4 { Node x }, Symbol "⊽",   expr4 { Node y };
expr4		{ Node $ goBinOp "<<<" x y }					: expr4 { Node x }, Symbol "<<<", expr4 { Node y };
expr4		{ Node $ goBinOp ">>>" x y }					: expr4 { Node x }, Symbol ">>>", expr4 { Node y };
expr4		{ Node $ goBinOp "<<"  x y }					: expr4 { Node x }, Symbol "<<",  expr4 { Node y };
expr4		{ Node $ goBinOp ">>"  x y }					: expr4 { Node x }, Symbol ">>",  expr4 { Node y };
expr4		{ Node $ goBinOp "+"   x y }					: expr4 { Node x }, Symbol "+",   expr4 { Node y };
expr4		{ Node $ goBinOp "-"   x y }					: expr4 { Node x }, Symbol "-",   expr4 { Node y };
expr4		{ Node $ goBinOp "×"   x y }					: expr4 { Node x }, Symbol "×",   expr4 { Node y };
expr4		{ Node $ goBinOp "/"   x y }					: expr4 { Node x }, Symbol "/",   expr4 { Node y };

expr5		{ Node (XSignature [Char] [Char] :&: CTR) (Cxt NoHole (XSignature [Char] [Char] :&: CTR)) (K ()) RVal };
expr5		{ x }								: expr4 { x };
expr5		{ Node $ la3 XIf (\ m _ n -> m <> n) p x y }			: expr5 { Node p }, Symbol "?", expr5 { Node x }, Symbol "!", expr5 { Node y };

expr6		{ Node (XSignature [Char] [Char] :&: CTR) (Cxt NoHole (XSignature [Char] [Char] :&: CTR)) (K ()) RVal };
expr6		{ x }								: expr5 { x };
expr6		{ Node $ la1 (XCast t) (pure (a :–: b)) x }			: expr6 { Node (x@(_ :&: (a :–: _))) }, ":", type { terminode -> t }, loc { b };

expr7		{ Node (XSignature [Char] [Char] :&: CTR) (Cxt NoHole (XSignature [Char] [Char] :&: CTR)) (K ()) RVal };
expr7		{ x }								: expr6 { x };
expr7		{ Node $
		  laF1 (\ (Compose (Identity x)) -> XWithNom (terminode <$> Map.fromList ds) x) (const2 (a :–: b)) mempty
		  (Identity x) }						: loc { a }, KeyWord "with", '(', sepMayEndBy localDecl ',' { ds }, ')', expr7 { Node (x@(_ :&: (_ :–: b))) };
expr7		{% (\ (Node y') -> Node $ la2 XAssign (<>) y' (goBinOp opv y x)) <$>
		   maybe (throw "unassignable") return
		   (toLExpr (Node y) ::
		      Maybe (Node (XSignature [Char] [Char] :&: CTR)
		             (Cxt NoHole (XSignature [Char] [Char] :&: CTR))
		             (K ()) LVal)) }					: expr5 { Node y }, assignOp { opv }, expr7 { Node x };
expr7		{ Node $ la3 XLoop (\ _ _ (_ :–: b) -> a :–: b) p x y }		: loc { a }, "for", expr1 { Node p }, expr1 { Node x }, expr { Node y };

localDecl	{ ([Char], Node (TSignature [Char] [Char] :&: CTR) (Cxt NoHole (TSignature [Char] [Char] :&: CTR)) (K ()) Type) };
localDecl	{ (v, t) }							: termName { v }, ":", type { t };

atype_		{ Node (TSignature [Char] [Char]) (Cxt NoHole (TSignature [Char] [Char] :&: CTR)) (K ()) Type };
atype_		{ Node $ inj $ S.Var v }					: TypeName { v };
atype_		{ Node $ stlist (fst ∘ Sim.projectA ∘ projectA) (laF1_ Tuple)
		         (unNode <$> ts) }					: '(', sepBy type ',' { ts }, ')';
atype_		{ Node $ laF1_ TStruct (Compose ((id *** unNode) <$> ms)) }	: '{', sepMayEndBy typeMember ',' { ms }, '}';
atype_		{ Node $ inj $ Lit (LInteger n) }				: "<integer>" { n };

atype		{ Node (TSignature [Char] [Char] :&: CTR) (Cxt NoHole (TSignature [Char] [Char] :&: CTR)) (K ()) Type };
atype		{ Node $ x :&: (a :–: b) }					: loc { a }, atype_ { Node x }, loc { b };

ptype		{ Node (TSignature [Char] [Char] :&: CTR) (Cxt NoHole (TSignature [Char] [Char] :&: CTR)) (K ()) Type };
ptype		{ t }								: atype { t };
ptype		{ Node $ la2 TPly (<>) s t }					: ptype { Node s }, atype { Node t };

qtype		{ Node (TSignature [Char] [Char] :&: CTR) (Cxt NoHole (TSignature [Char] [Char] :&: CTR)) (K ()) Type };
qtype		{ t }								: ptype { t };
qtype		{ Node $ la1 TPtr (const (a :–: b)) t }				: qtype { Node (t@(_ :&: (a :–: _))) }, "*", loc { b };

type		{ Node (TSignature [Char] [Char] :&: CTR) (Cxt NoHole (TSignature [Char] [Char] :&: CTR)) (K ()) Type };
type		{ t }								: qtype { t };
type		{ Node $ la2 TFunc (<>) t s }					: type { Node t }, Symbol "->", qtype { Node s };

typeMember	{ (Maybe [Char], Node (TSignature [Char] [Char] :&: CTR) (Cxt NoHole (TSignature [Char] [Char] :&: CTR)) (K ()) Type) };
typeMember	{ (Just v,  t) }						: termName { v }, ":", type { t };
typeMember	{ (Nothing, t) }						: "_", ":", type { t };

assignOp	{ [Char] };
assignOp	{ "" }								: "≔";
assignOp	{ "∧" }								: Symbol "∧=";
assignOp	{ "∨" }								: Symbol "∨=";
assignOp	{ "⊻" }								: Symbol "⊻=";
assignOp	{ "⊼" }								: Symbol "⊼=";
assignOp	{ "⊽" }								: Symbol "⊽=";
assignOp	{ "+" }								: Symbol "+=";
assignOp	{ "-" }								: Symbol "-=";
assignOp	{ "×" }								: Symbol "×=";
assignOp	{ "/" }								: Symbol "/=";
assignOp	{ "<<" }							: Symbol "<<=";
assignOp	{ ">>" }							: Symbol ">>=";
assignOp	{ "<<<" }							: Symbol "<<<=";
assignOp	{ ">>>" }							: Symbol ">>>=";

termName	{ [Char] };
termName	{ v }								: TermName { v };

loc	{ TextPos };
loc	{% ML.gets lexPosOld }	:;

sepEndBy x s { [a] } <- x { a }, s;
sepEndBy x s { [] }		:;
             { xs ++ [x] }	| sepEndBy x s { xs }, x { x }, s;

sepMayEndBy x s { [a] } <- x { a }, s;
sepMayEndBy x s { [] }		:;
                { xs ++ [x] }	| sepEndBy x s { xs }, x { x }, opt s;

deepNest x r s t { Free [] a } <- x { a }, r, s, t;
deepNest x r s t { Pure x }		: x { x };
                 { stlist id Free ts }	| r, sepBy (deepNest x r s t) s { ts }, t;

}%

type TSignature bv bm = Var bv :+: TPtr :+: Tuple :+: TFunc :+: TIntegral :+: Lit :+: TStruct bm :+: TPly
type XSignature bv bm = Var bv :+: XFollow :+: XCall :+: XMember bm :+: Tuple :+: XStruct bm :+: Lit :+: XPrimOp :+: XCast (Term (TSignature bv bm :&: CTR) Type) :+: XIf :+: XConj :+: XDisj :+: XAssign :+: XWithNom bv (Term (TSignature bm bm :&: CTR) Type) :+: XThen :+: XLoop :+: XReturn

frownScan = Lex.scan1M "scan failure"

frown t = ML.gets lexPos >>= \ pos -> throw ("parse failure at " ++ show pos ++ ": got " ++ show t)

goBinOp :: (XPrimOp :<: f, Monoid p) =>
           [Char] ->
           (f :&: p) a (Cxt h (f :&: p) a b) RVal ->
           (f :&: p) a (Cxt h (f :&: p) a b) RVal ->
           (f :&: p) a (Cxt h (f :&: p) a b) RVal
goBinOp ""  _ y = y
goBinOp "=" x y = laF1 (XPrimOp PrimEq)  (<>) mempty (x:.y:.Nil)
goBinOp "≠" x y = laF1 (XPrimOp PrimNEq) (<>) mempty (x:.y:.Nil)
goBinOp "≥" x y = laF1 (XPrimOp PrimGEq) (<>) mempty (x:.y:.Nil)
goBinOp "≤" x y = laF1 (XPrimOp PrimLEq) (<>) mempty (x:.y:.Nil)
goBinOp ">" x y = laF1 (XPrimOp PrimGÞ)  (<>) mempty (x:.y:.Nil)
goBinOp "<" x y = laF1 (XPrimOp PrimLÞ)  (<>) mempty (x:.y:.Nil)
goBinOp "∧" x y = laF1 (XPrimOp PrimAnd) (<>) mempty (x:.y:.Nil)
goBinOp "∨" x y = laF1 (XPrimOp PrimOr)  (<>) mempty (x:.y:.Nil)
goBinOp "⊻" x y = laF1 (XPrimOp PrimXor) (<>) mempty (x:.y:.Nil)
{-
goBinOp "⊼" x y =
  (XPrimOp PrimXor ∘ fmap (TagT mempty))
  [XPrimOp PrimAnd [x, y],
   Literal (LInteger (negate 1))]
goBinOp "⊽" x y =
  (XPrimOp PrimXor ∘ fmap (TagT mempty))
  [XPrimOp PrimOr [x, y],
   Literal (LInteger (negate 1))]
-}
goBinOp "<<" x y = laF1 (XPrimOp PrimShiftL) (<>) mempty (x:.y:.Nil)
goBinOp ">>" x y = laF1 (XPrimOp PrimShiftR) (<>) mempty (x:.y:.Nil)
goBinOp "<<<" x y = laF1 (XPrimOp PrimRotL)  (<>) mempty (x:.y:.Nil)
goBinOp ">>>" x y = laF1 (XPrimOp PrimRotR)  (<>) mempty (x:.y:.Nil)
goBinOp "+" x y = laF1 (XPrimOp PrimAdd) (<>) mempty (x:.y:.Nil)
goBinOp "-" x y = laF1 (XPrimOp PrimSub) (<>) mempty (x:.y:.Nil)
goBinOp "×" x y = laF1 (XPrimOp PrimMul) (<>) mempty (x:.y:.Nil)
goBinOp "/" x y = laF1 (XPrimOp PrimDiv) (<>) mempty (x:.y:.Nil)

type CTR = ConvexTextRange

stlist :: (a -> b) -> ([a] -> b) -> [a] -> b
stlist f g [x] = f x
stlist f g  xs = g xs

const2 x _ _ = x

terminode :: Node f (Cxt NoHole f) (K ()) :-> Term f
terminode (Node x) = Term (In x)
