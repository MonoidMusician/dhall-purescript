module Dhall.Printer where

import Prelude

import Control.Plus (empty)
import Data.Array as Array
import Data.Const (Const(..))
import Data.Const (Const) as C
import Data.Either (Either(..))
import Data.Functor.App (App(..))
import Data.Functor.Mu (Mu(..))
import Data.Functor.Product (Product(..))
import Data.Functor.Variant (SProxy)
import Data.Functor.Variant as VariantF
import Data.Identity (Identity(..))
import Data.List as List
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Monoid.Additive (Additive(..))
import Data.Natural (natToInt)
import Data.Newtype (over2, un, unwrap)
import Data.String as String
import Data.Symbol (class IsSymbol)
import Data.Traversable (class Foldable, maximum, or)
import Data.Tuple (Tuple(..), fst)
import Data.Variant (Variant)
import Data.Variant as Variant
import Dhall.Core (BindingBody(..), Const(..), Expr, ExprLayerF, LetF(..), MergeF(..), Pair(..), S_, TextLitF(..), Var(..), _S)
import Dhall.Map (InsOrdStrMap, unIOSM)
import Dhall.Map as Dhall.Map
import Effect.Console (log)
import Effect.Unsafe (unsafePerformEffect)
import Matryoshka (Algebra, cata)
import Prim.Row (class Cons) as Row
import Type.Row (type (+))
import Unsafe.Coerce (unsafeCoerce)

-- The process of printing an AST goes like so:
-- - convert to n-ary operators (`fromAST`)
-- - use precendence to add parentheses as necessary (`precede`)
-- - convert to structured syntax tree (`structure`)
-- - convert tokens to paddable (colored) text (`tokDisp`)
-- - convert to 2D displayed tokens array `layout`
-- - convert to flat text `printLines`
-- AST -> OpTree -> PrecTree -> TokStruct -> DispStruct -> Array (Array Disp) -> String
printAST :: forall i.
  { ascii :: Boolean
  , line :: Maybe (Additive Int)
  , printImport :: i -> String
  , tabs ::
    { width :: Additive Int
    , soft :: Boolean
    , align :: Boolean
  } } ->
  Expr InsOrdStrMap i ->
  String
printAST { ascii, line, tabs, printImport } = identity
  >>> cata (unwrap >>> fromAST printImport)
  >>> cata precede
  >>> cata structure
  >>> strMap (tokDisp { ascii })
  >>> layout { line, tabs }
  >>> map _.value
  >>> printLines

-- Formatting should start by capturing the general syntactic structure
-- in semantic chunks, so related things are in one node.
-- Decisions should be deferred to as late as possible, so they can apply
-- uniformly. Some decisions will be AST transformations, while some will
-- affect the rendering process.
--
-- It seems there will be an interplay between deciding where to add
-- newlines and how much to indent.
--
-- Tokens should always be guaranteed to render the same in different contexts.

-- Data: Keywords/symbols
-- Structure: Groupings/Operators
-- - Operators always start the line when split, lining up with the opening and
--   closing of the corresponding group, otherwise spacing rules are applied.
-- - Closings may be combined if openings are, i.e. the outer layer doesn't
--   introduce an indent ???
-- - More generally, if there are only closing groupings on the final line
--   of the first operand, a whole series of operators could squeeze onto the
--   same line if it fits (e.g. repeated field access)
-- - Usually it will try to squeeze the most operands onto each line …?

data TokenType
  = TTGrouping -- e.g. ()
  | TTSeparator -- e.g. , : =
  | TTOperator -- e.g. ++ #
  | TTLiteral -- e.g. 0 ""
  | TTKeyword -- e.g. merge λ forall
  | TTImport -- e.g. https://foo.com/file.dhall ? using
  | TTName Boolean -- e.g. Foo List/fold
derive instance eqTokenType :: Eq TokenType
derive instance ordTokenType :: Ord TokenType
data Side = L | R
derive instance eqSide :: Eq Side
derive instance ordSide :: Ord Side

type Struct t = Mu (StructF t)
data StructF t r
  = StrTokens (Array t)
  | StrGroup (Array { before :: Array t, line :: r })

strMap :: forall t d. (t -> d) -> Struct t -> Struct d
strMap f (In (StrTokens ts)) = In (StrTokens (f <$> ts))
strMap f (In (StrGroup gs)) = In $ StrGroup $
  gs <#> \{ before, line } -> { before: f <$> before, line: strMap f line }

strEmpty :: forall t. Struct t -> Boolean
strEmpty (In (StrTokens [])) = true
strEmpty (In (StrTokens _)) = false
strEmpty (In (StrGroup [])) = true
strEmpty (In (StrGroup gs)) = gs # Array.all \g ->
  Array.null g.before && strEmpty g.line

strNorm :: forall t. Struct t -> Struct t
strNorm (In (StrGroup gs)) = In $ StrGroup $
  gs <#> (\g -> g { line = strNorm g.line })
  # Array.filter \g -> not $
    Array.null g.before && strEmpty g.line
strNorm str = str

-- Flatten a struct into a stream of tokens
flatten :: forall t. Struct t -> Array t
flatten (In (StrTokens ts)) = ts
flatten (In (StrGroup gs)) = gs >>= \{ before, line } ->
  before <> flatten line

type Bush v = Mu (BushF v)
type Branching t = Array { label :: Maybe String, value :: Maybe t }
mapBranch :: forall t d.
  (t -> d) ->
  { label :: Maybe String, value :: Maybe t } ->
  { label :: Maybe String, value :: Maybe d }
mapBranch f { label, value } = { label, value: map f value }
data BushF v r = BushF v (Branching r)
derive instance functorBushF :: Functor (BushF v)

type Containers r =
  ( "List" :: Unit
  , "Record" :: Unit
  , "RecordLit" :: Unit
  , "Union" :: Unit
  , "StringInterp" :: Unit
  | r
  )
type Precedence r =
  ( "Paren" :: Unit
  , "ByType" :: Unit
  , "LabelSet" :: Unit
  | r
  )
type Blocks r =
  ( "Let" :: Unit
  , "BoolIf" :: Unit
  | r
  )
type Abstractions r =
  ( "Pi" :: Unit
  , "Lam" :: Unit
  | r
  )
type Operators r =
  ( "BoolAnd" :: Unit
  , "BoolOr" :: Unit
  , "BoolEQ" :: Unit
  , "BoolNE" :: Unit
  , "NaturalPlus" :: Unit
  , "NaturalTimes" :: Unit
  , "TextAppend" :: Unit
  , "ListAppend" :: Unit
  , "Combine" :: Unit
  , "CombineTypes" :: Unit
  , "Prefer" :: Unit
  , "Equivalent" :: Unit
  , "ImportAlt" :: Unit
  , "Annot" :: Unit
  , "App" :: Unit
  , "Field" :: Unit
  , "Hashed" :: Unit
  , "UsingHeaders" :: Unit
  , "Arrow" :: Unit
  | r
  )
type Literals r =
  ( "Keyword" :: String
  , "Builtin" :: String
  , "Name" :: String
  , "At" :: Unit
  , "Number" :: String
  , "Import" :: String
  , "String" :: Unit
  , "StringData" :: String
  | r
  )
type Groupings r =
  ( "Paren" :: Side
  , "Brace" :: Side
  , "Bracket" :: Side
  , "Interp" :: Side
  , "Angle" :: Side
  | r
  )
type Separators r =
  ( "Comma" :: Unit
  , "Alt" :: Unit
  , "Equal" :: Unit
  | r
  )
type Whitespace r =
  ( "Space" :: Unit
  , "Tab" :: Unit
  | r
  )

type Nodes r =
  Precedence + Containers + Blocks + Abstractions + Operators + Literals + r
type Tokens r =
  Abstractions + Operators + Literals + Groupings + Separators + Whitespace + r

type Node = Variant (Nodes + ())
type NodeBush = Bush (Variant (Nodes + ()))
type NodeBushF = BushF (Variant (Nodes + ()))
type Tok = Variant (Tokens + ())
type TokStruct = Struct (Variant (Tokens + ()))
type TokStructF = StructF (Variant (Tokens + ()))
type DispStruct = Struct Disp
type DispStructF = StructF Disp

type Prec = { assoc :: Maybe Boolean, prec :: Int }

fromAST :: forall i. (i -> String) -> Algebra (ExprLayerF InsOrdStrMap i) NodeBush
fromAST renderImport = VariantF.match
  { "Annot": annot
  , "App": app
  , "Assert": \(Identity prop) ->
      annot $ Pair (keyword "assert") prop
  , "Bool": builtin "Bool"
  , "BoolAnd": binop (_S::S_ "BoolAnd")
  , "BoolEQ": binop (_S::S_ "BoolEQ")
  , "BoolIf": foldable (_S::S_ "BoolIf")
  , "BoolLit": \(Const b) ->
      Const unit # builtin if b then "True" else "False"
  , "BoolNE": binop (_S::S_ "BoolNE")
  , "BoolOr": binop (_S::S_ "BoolOr")
  , "Combine": binop (_S::S_ "Combine")
  , "CombineTypes": binop (_S::S_ "CombineTypes")
  , "Const": (Const unit # _) <<< builtin <<< unwrap >>> case _ of
      Type -> "Type"
      Kind -> "Kind"
      Sort -> "Sort"
  , "Double": builtin "Double"
  , "DoubleLit": unwrap >>> showDouble >>> number
  , "DoubleShow": builtin "Double/show"
  , "Embed": unwrap >>> renderImport >>> literal (_S::S_ "Import")
  , "Equivalent": binop (_S::S_ "Equivalent")
  , "Field": \(Tuple s obj) ->
      binop (_S::S_ "Field") $ Pair obj (name s)
  , "Hashed": \(Tuple hash e) ->
      binop (_S::S_ "Hashed") $ Pair e (literal (_S::S_ "StringData") hash)
  , "ImportAlt": binop (_S::S_ "ImportAlt")
  , "Integer": builtin "Integer"
  , "IntegerLit": unwrap >>> showInteger >>> number
  , "IntegerShow": builtin "Integer/show"
  , "IntegerToDouble": builtin "Integer/toDouble"
  , "Lam": \(BindingBody label ty body) ->
      bush (_S::S_ "Lam")
        [ { label: Just label, value: Just ty }
        , { label: Nothing, value: Just body }
        ]
  , "Let": \(LetF label mty val body) ->
      bush (_S::S_ "Let")
        [ { label: Just label, value: mty }
        , { label: Just label, value: Just val }
        , { label: Nothing, value: Just body }
        ]
  , "List": builtin "List"
  , "ListAppend": binop (_S::S_ "ListAppend")
  , "ListBuild": builtin "List/build"
  , "ListFold": builtin "List/fold"
  , "ListHead": builtin "List/head"
  , "ListIndexed": builtin "List/indexed"
  , "ListLast": builtin "List/last"
  , "ListLength": builtin "List/length"
  , "ListLit": \(Product (Tuple mty es)) ->
      annotWith mty $ foldable (_S::S_ "List") es
  , "ListReverse": builtin "List/reverse"
  , "Merge": \(MergeF r u mty) ->
      annotWith mty $ app $ Pair (app $ Pair (keyword "merge") r) u
  , "Natural": builtin "Natural"
  , "NaturalBuild": builtin "Natural/build"
  , "NaturalEven": builtin "Natural/even"
  , "NaturalFold": builtin "Natural/fold"
  , "NaturalIsZero": builtin "Natural/isZero"
  , "NaturalLit": unwrap >>> showNatural >>> number
  , "NaturalOdd": builtin "Natural/odd"
  , "NaturalPlus": binop (_S::S_ "NaturalPlus")
  , "NaturalShow": builtin "Natural/show"
  , "NaturalSubtract": builtin "Natural/subtract"
  , "NaturalTimes": binop (_S::S_ "NaturalTimes")
  , "NaturalToInteger": builtin "Natural/toInteger"
  , "None": builtin "None"
  , "Optional": builtin "Optional"
  , "OptionalBuild": builtin "Optional/build"
  , "OptionalFold": builtin "Optional/fold"
  , "Pi": \(BindingBody label ty body) ->
      if label == "_" then binop (_S::S_ "Arrow") (Pair ty body) else
      bush (_S::S_ "Pi")
        [ { label: Just label, value: Just ty }
        , { label: Nothing, value: Just body }
        ]
  , "Prefer": binop (_S::S_ "Prefer")
  , "Project": \(Product (Tuple (Identity e) fs)) ->
      binop (_S::S_ "Field") $ Pair e $
        case fs of
          Left (App ks) ->
            let
              names = name <<< fst <$> Dhall.Map.unIOSM ks
            in foldable (_S::S_ "LabelSet") names
          Right t -> foldable (_S::S_ "ByType") [ t ]
  , "Record": map Just >>> miosm (_S::S_ "Record")
  , "RecordLit": map Just >>> miosm (_S::S_ "RecordLit")
  , "Some": \(Identity e) -> app $ Pair (keyword "Some") e
  , "Text": builtin "Text"
  , "TextAppend": binop (_S::S_ "TextAppend")
  , "TextLit":
      let
        -- FIXME: escapes
        str s = [ literal (_S::S_ "StringData") s ]
        interp e =
          [ foldable (_S::S_ "StringInterp") [ e ] ]
        rec (TextLit s) = str s
        rec (TextInterp s e t) =
          str s <> interp e <> rec t
      in foldable (_S::S_ "String") <<< rec
  , "TextShow": builtin "Text/show"
  , "ToMap": \(Product (Tuple (Identity e) mty)) ->
      annotWith mty $ app $ Pair (keyword "toMap") e
  , "Union": unwrap >>> miosm (_S::S_ "Union")
  , "UsingHeaders": binop (_S::S_ "UsingHeaders")
  , "Var": unwrap >>> \(V n i) ->
      if i /= 0
        then binop (_S::S_ "At") $ Pair (name n) (number (show i))
        else name n
  } where
    showDouble = show
    showNatural = show <<< natToInt
    showInteger i
      | i < 0 = show i
      | otherwise = "+" <> show i
    annot = binop (_S::S_ "Annot")
    app = binop (_S::S_ "App")
    annotWith Nothing = identity
    annotWith (Just ty) = \e -> annot $ Pair e ty
    bush ::
      forall s r.
        IsSymbol s =>
        Row.Cons s Unit r (Nodes ()) =>
      SProxy s -> Algebra Branching NodeBush
    bush s = In <<< BushF (Variant.inj s unit)
    foldable ::
      forall s r f.
        IsSymbol s =>
        Row.Cons s Unit r (Nodes ()) =>
        Foldable f =>
      SProxy s -> Algebra f NodeBush
    foldable s = bush s <<< map conv <<< Array.fromFoldable where
      conv value = { label: Nothing, value: Just value }
    miosm ::
      forall s r.
        IsSymbol s =>
        Row.Cons s Unit r (Nodes ()) =>
      SProxy s -> InsOrdStrMap (Maybe NodeBush) -> NodeBush
    miosm s = bush s <<< map conv <<< unIOSM where
      conv (Tuple label value) = { label: Just label, value }
    binop ::
      forall s r.
        IsSymbol s =>
        Row.Cons s Unit r (Nodes ()) =>
      SProxy s -> Algebra Pair NodeBush
    binop s = foldable s
    literal ::
      forall s r t.
        IsSymbol s =>
        Row.Cons s t r (Nodes ()) =>
      SProxy s -> t -> NodeBush
    literal s v = In (BushF (Variant.inj s v) [])
    builtin :: String -> C.Const Unit NodeBush -> NodeBush
    builtin = const <<< literal (_S::S_ "Builtin")
    keyword = literal (_S::S_ "Keyword")
    name = literal (_S::S_ "Name")
    number = literal (_S::S_ "Number")

precede :: Algebra NodeBushF NodeBush
precede = In <<< process where
  process (BushF v cs) | Just { assoc, prec } <- precedence v = BushF v $
    let
      tgt = assoc <#> if _ then Array.length cs - 1 else 0
      paren c = In $ BushF (Variant.inj (_S::S_ "Paren") unit)
        [ { label: Nothing, value: Just c } ]
    in join $ cs # Array.mapWithIndex \i -> case _ of
      { label: Nothing, value: Just (c@(In (BushF v' cs'))) }
        -- Collapse it into its parent, if it is the same type of node
        -- on the side of its associativity
        | v == v' && tgt == Just i -> cs'
        -- Or add parentheses
        | Just { prec: prec' } <- precedence v'
        , prec' < prec + (if tgt == Just i then 0 else 1) ->
          pure { label: Nothing, value: Just (paren c) }
      -- Or preserve it as-is
      c -> pure c
  process b = b
  lassoc :: Int -> Unit -> Maybe Prec
  lassoc prec _ = Just { assoc: Just false, prec }
  rassoc :: Int -> Unit -> Maybe Prec
  rassoc prec _ = Just { assoc: Just true, prec }
  precedence :: Variant (Nodes + ()) -> Maybe Prec
  precedence = Variant.default Nothing # Variant.onMatch
    { "Lam": rassoc (-100)
    , "BoolIf": rassoc (-100)
    , "Let": rassoc (-100)
    , "Pi": rassoc (-100)
    , "Arrow": rassoc (-100)
    , "Annot": rassoc (-100)
    , "ImportAlt": lassoc (-13)
    , "BoolOr": lassoc (-12)
    , "NaturalPlus": lassoc (-11)
    , "TextAppend": lassoc (-10)
    , "ListAppend": lassoc (-9)
    , "BoolAnd": lassoc (-8)
    , "Combine": lassoc (-7)
    , "Prefer": lassoc (-6)
    , "CombineTypes": lassoc (-5)
    , "NaturalTimes": lassoc (-4)
    , "BoolEQ": lassoc (-3)
    , "BoolNE": lassoc (-2)
    , "Equivalent": lassoc (-1)
    , "App": lassoc 0
    , "Field": lassoc 1
    , "UsingHeaders": lassoc 100
    , "Hashed": lassoc 100
    }

structure :: Algebra NodeBushF TokStruct
structure (BushF v cs) = (#) v $ Variant.case_
  # Variant.on (_S::S_ "List")
    ( handleContainer (_S::S_ "Bracket") (_S::S_ "Comma") [] )
  # Variant.on (_S::S_ "Record")
    ( handleLabelled (_S::S_ "Brace") (_S::S_ "Comma") (_S::S_ "Annot") [] )
  # Variant.on (_S::S_ "RecordLit")
    ( handleLabelled (_S::S_ "Brace") (_S::S_ "Comma") (_S::S_ "Equal")
      [ Variant.inj (_S::S_ "Equal") unit ]
    )
  # Variant.on  (_S::S_ "Union")
    ( handleLabelled (_S::S_ "Angle") (_S::S_ "Alt") (_S::S_ "Annot") [] )
  # Variant.on (_S::S_ "StringInterp")
    ( handleContainer (_S::S_ "Interp") (_S::S_ "Comma") [] )
  # Variant.on (_S::S_ "Paren")
    ( handleContainer (_S::S_ "Paren") (_S::S_ "Comma") [] )
  # Variant.on (_S::S_ "Let") handleLet
  # Variant.on (_S::S_ "BoolIf") handleIf
  # handleAbstraction (_S::S_ "Pi")
  # handleAbstraction (_S::S_ "Lam")
  # handleOperator (_S::S_ "BoolAnd")
  # handleOperator (_S::S_ "BoolOr")
  # handleOperator (_S::S_ "BoolEQ")
  # handleOperator (_S::S_ "BoolNE")
  # handleOperator (_S::S_ "NaturalPlus")
  # handleOperator (_S::S_ "NaturalTimes")
  # handleOperator (_S::S_ "TextAppend")
  # handleOperator (_S::S_ "ListAppend")
  # handleOperator (_S::S_ "Combine")
  # handleOperator (_S::S_ "CombineTypes")
  # handleOperator (_S::S_ "Prefer")
  # handleOperator (_S::S_ "Equivalent")
  # handleOperator (_S::S_ "ImportAlt")
  # handleOperator (_S::S_ "Annot")
  # handleOperator (_S::S_ "App")
  # handleOperator (_S::S_ "Field")
  # Variant.on (_S::S_ "ByType")
    ( handleContainer (_S::S_ "Paren") (_S::S_ "Comma") [] )
  # handleOperator (_S::S_ "Hashed")
  # handleOperator (_S::S_ "UsingHeaders")
  # handleOperator (_S::S_ "Arrow")
  # handleLiteral (_S::S_ "Keyword")
  # handleLiteral (_S::S_ "Builtin")
  # handleLiteral (_S::S_ "Name")
  # handleOperator (_S::S_ "At")
  # handleLiteral (_S::S_ "Number")
  # handleLiteral (_S::S_ "Import")
  # Variant.on (_S::S_ "String") handleString
  # handleLiteral (_S::S_ "StringData")
  # Variant.on (_S::S_ "LabelSet")
    ( handleContainer (_S::S_ "Brace") (_S::S_ "Comma") [] )
  where
    emptyLine = In $ StrTokens []
    handleContainer ::
      forall s2 s3 r2 r3.
        IsSymbol s2 => Row.Cons s2 Side r2 (Tokens + ()) =>
        IsSymbol s3 => Row.Cons s3 Unit r3 (Tokens + ()) =>
      SProxy s2 -> SProxy s3 ->
      Array Tok -> Unit -> TokStruct
    handleContainer s2 s3 empt _ = buildGroup (Variant.inj s2) (Variant.inj s3 unit) empt $
      cs # Array.mapMaybe \{ label, value } -> value
    handleLabelled ::
      forall s2 s3 s4 r2 r3 r4.
        IsSymbol s2 => Row.Cons s2 Side r2 (Tokens + ()) =>
        IsSymbol s3 => Row.Cons s3 Unit r3 (Tokens + ()) =>
        IsSymbol s4 => Row.Cons s4 Unit r4 (Tokens + ()) =>
      SProxy s2 -> SProxy s3 -> SProxy s4 ->
      Array Tok -> Unit -> TokStruct
    handleLabelled s2 s3 s4 empt _ = buildGroup (Variant.inj s2) (Variant.inj s3 unit) empt $
      cs # Array.mapMaybe \{ label, value } -> label <#> \l ->
        let nm = Variant.inj (_S::S_ "Name") l in
        case value of
          Nothing -> In $ StrTokens [ nm ]
          Just line -> In $ StrGroup
            [ { before: empty
              , line: In $ StrTokens [ nm, Variant.inj s4 unit ]
              }
            , { before: empty, line }
            ]
    -- TODO: absorb inside grouping, if possible
    buildGroup :: (Side -> Tok) -> Tok -> Array Tok -> Array TokStruct -> TokStruct
    buildGroup g _ empt [] = In $ StrTokens $ [ g L ] <> empt <> [ g R ]
    buildGroup g sep _ items = In $ StrGroup $
      (map Just items <> [ Nothing ]) # Array.mapWithIndex \i line ->
        let
          b
            | i == 0
              = g L
            | i == Array.length items
              = g R
            | otherwise
              = sep
        in { before: pure b, line: fromMaybe emptyLine line }
    keyword = Variant.inj (_S::S_ "Keyword")
    handleLet :: Unit -> TokStruct
    handleLet _ = In $ StrGroup (handle (List.fromFoldable cs)) where
      handle List.Nil = []
      handle ({ value: Just body } List.: List.Nil) =
        [ { before: pure (keyword "in"), line: body } ]
      handle ( { label: Just name1, value: mty }
        List.: { label: Just name2, value: Just line }
        List.: r )
        | name1 == name2 =
          [ { before: pure (keyword "let")
            , line: In $ StrGroup $ { before: empty, line: _ } <$>
                [ In (StrTokens (pure (Variant.inj (_S::S_ "Name") name1)))
                , In $ StrGroup $ Array.catMaybes $
                  [ mty <#> { before: pure (Variant.inj (_S::S_ "Annot") unit), line: _ }
                  , Just { before: pure (Variant.inj (_S::S_ "Equal") unit), line }
                  ]
                ]
            }
          ] <> handle r
      handle ( { label: Just name, value: Just line }
        List.: r ) =
        [ { before: pure (keyword "let")
          , line: In $ StrGroup $ Array.catMaybes $
              [ Just { before: pure (Variant.inj (_S::S_ "Name") name), line: emptyLine }
              , Just { before: pure (Variant.inj (_S::S_ "Equal") unit), line }
              ]
          }
        ] <> handle r
      handle (_ List.: r) =
        handle r
    handleIf :: Unit -> TokStruct
    handleIf _ = In $ StrGroup (handle empty (List.fromFoldable (Array.mapMaybe _.value cs))) where
      handle _ List.Nil = []
      handle b (line List.: List.Nil) = [ { before: b, line } ]
      handle b (line1 List.: line2 List.: r) =
        [ { before: b
          , line: In $ StrGroup
            [ { before: pure (keyword "if"), line: line1 } ]
          }
        , { before: pure (keyword "then"), line: line2 }
        ] <> handle (pure (keyword "else")) r
    handleAbstraction ::
      forall s r1 r2 r3.
        IsSymbol s =>
        Row.Cons s Unit r1 r2 =>
        Row.Cons s Unit r3 (Tokens + ()) =>
      SProxy s ->
      (Variant r1 -> TokStruct) ->
      (Variant r2 -> TokStruct)
    handleAbstraction s = Variant.on s \_ -> In $ StrGroup
      let
        handle _ List.Nil = []
        handle b ({ value: Nothing } List.: List.Nil) =
          [ { before: b, line: emptyLine } ]
        handle b ({ value: Just line } List.: List.Nil) =
          [ { before: b, line } ]
        handle b ({ label: Just label, value: Just line } List.: r) =
          [ { before: b
            , line: In $ StrGroup
              [ { before: pure (Variant.inj s unit)
                , line: In $ StrGroup
                  [ { before: pure (Variant.inj (_S::S_ "Paren") L)
                    , line: In $ StrTokens [ Variant.inj (_S::S_ "Name") label ]
                    }
                  , { before: pure (Variant.inj (_S::S_ "Annot") unit)
                    , line
                    }
                  , { before: pure (Variant.inj (_S::S_ "Paren") R), line: emptyLine }
                  ]
                }
              ]
            }
          ] <> handle (pure (Variant.inj (_S::S_ "Arrow") unit)) r
        handle b (_ List.: r) = handle b r
      in handle empty (List.fromFoldable cs)
    handleOperator ::
      forall s r1 r2 r3.
        IsSymbol s =>
        Row.Cons s Unit r1 r2 =>
        Row.Cons s Unit r3 (Tokens + ()) =>
      SProxy s ->
      (Variant r1 -> TokStruct) ->
      (Variant r2 -> TokStruct)
    handleOperator s = Variant.on s \_ -> In $ StrGroup
      let
        handle _ List.Nil = []
        handle b ({ value: Just line } List.: r) =
          [ { before: b, line } ] <> handle (pure (Variant.inj s unit)) r
        handle b ({ value: Nothing } List.: r) = handle b r
      in handle empty (List.fromFoldable cs)
    handleLiteral ::
      forall s t r1 r2 r3.
        IsSymbol s =>
        Row.Cons s t r1 r2 =>
        Row.Cons s t r3 (Tokens + ()) =>
      SProxy s ->
      (Variant r1 -> TokStruct) ->
      (Variant r2 -> TokStruct)
    handleLiteral s = Variant.on s \l ->
      In $ StrTokens [ Variant.inj s l ]
    handleString _ =
      let
        adding :: forall a. Array a -> Array (Array a) -> Array (Array a)
        adding as bs = case Array.uncons as, Array.unsnoc bs of
          Just { head, tail }, Just { init, last } ->
            init <> [ Array.snoc last head ] <> map pure tail
          Nothing, _ -> bs
          _, Nothing -> map pure as
        splitToken t = (#) t
          $ Variant.default (adding (pure (In (StrTokens [t]))))
          # Variant.on (_S::S_ "StringData")
            \s -> adding $
              String.split (String.Pattern "\n") s <#>
                In <<< StrTokens <<< pure <<< Variant.inj (_S::S_ "StringData")
        splitLines (In (StrTokens toks)) =
          Array.foldl (flip splitToken) <@> toks
        splitLines (In (StrGroup as)) = Array.unsnoc >>> case _ of
          Just { init, last } ->
            Array.snoc init (Array.snoc last (In (StrGroup as)))
          Nothing -> pure (pure (In (StrGroup as)))
        lines = Array.foldl (flip splitLines) [] (Array.mapMaybe _.value cs)
        realLines = Array.foldl foldLine emptyLine <<< map strNorm <$> lines
        result = realLines <#> \line -> { before: empty, line }
        sep = { before: empty, line: In (StrTokens [ Variant.inj (_S::S_ "String") unit ]) }
      in In $ StrGroup $ [sep] <> result <> [sep]

spy :: forall a. a -> a
spy = unsafePerformEffect <<< unsafeCoerce ((<$) <*> log)

foldTokens :: Array Tok -> Array Tok
foldTokens toks =
  let
    strdata "" = []
    strdata str = [ Variant.inj (_S::S_ "StringData") str ]
    folder { acc, str } tok
      | Just s <- Variant.prj (_S::S_ "StringData") tok
      = { acc, str: str <> s }
      | otherwise
      = { acc: acc <> (strdata str <> [tok]), str: "" }
    { acc, str } = Array.foldl folder { acc: [], str: "" } toks
  in acc <> strdata str
foldLine :: Struct Tok -> Struct Tok -> Struct Tok
foldLine = case _, _ of
  In (StrTokens as), In (StrTokens bs) -> In (StrTokens (foldTokens (as <> bs)))
  --a, In (StrTokens []) -> a
  --In (StrTokens []), b -> b
  --a, In (StrGroup []) -> a
  --In (StrGroup []), b -> b
  In (StrGroup as), In (StrTokens bs) ->
    case Array.unsnoc as of
      Nothing -> In (StrTokens bs)
      Just { init, last } ->
        In $ StrGroup $
          init <>
          [ last { line = foldLine last.line (In (StrTokens bs)) } ]
  -- TODO: if there is only whitespace, indent by that
  In (StrTokens as), In (StrGroup bs) ->
    case Array.uncons bs of
      Nothing -> In (StrTokens as)
      Just { head, tail } ->
        case head of
          { before: [], line } ->
            In $ StrGroup $
              [ { before: empty, line: foldLine (In (StrTokens as)) line } ] <>
              tail
          -- Move an existing prefix to the former line, with `as`
          { before: pr, line } ->
            In $ StrGroup $ { before: empty, line: _ } <$>
              [ In $ StrTokens $ as <> pr
              , In $ StrGroup $
                  [ { before: empty, line } ] <>
                  tail
              ]
  -- TODO: if there is only whitespace, indent by that
  In (StrGroup as), In (StrGroup bs) ->
    case Array.unsnoc as, Array.uncons bs of
      Nothing, Nothing -> In (StrGroup [])
      Nothing, Just _ -> In (StrGroup bs)
      Just _, Nothing -> In (StrGroup as)
      Just { init, last }, Just { head, tail } ->
        In $ StrGroup $ { before: empty, line: _ } <$>
          [ In (StrGroup init)
          , let mkTok = In <<< StrTokens <<< Array.fromFoldable in
            foldLine (foldLine (mkTok last.before) last.line) (mkTok head.before)
          , foldLine head.line (In (StrGroup tail))
          ]

data Hm = No | Perhaps | Yes
derive instance eqHm :: Eq Hm
derive instance ordHm :: Ord Hm
instance heytingAlgebraHm :: HeytingAlgebra Hm where
  tt = Yes
  ff = No
  conj = case _, _ of
    No, _ -> No
    _, No -> No
    Yes, a -> a
    a, Yes -> a
    Perhaps, Perhaps -> Perhaps
  disj = case _, _ of
    Yes, _ -> Yes
    _, Yes -> Yes
    No, a -> a
    a, No -> a
    Perhaps, Perhaps -> Perhaps
  implies = case _, _ of
    Yes, No -> No
    No, _ -> Yes
    _, Yes -> Yes
    _, _ -> Perhaps
  not Yes = No
  not No = Yes
  not Perhaps = Perhaps

type Padding r =
  ( spaceBefore :: Hm
  , spaceAfter :: Hm
  | r
  )
type TokInfo r =
  ( tokType :: TokenType
  | r
  )
type TokValue v r =
  ( value :: v
  | r
  )
type Disp = Record (Padding + TokInfo + TokValue String + ())

tokDisp ::
  { ascii :: Boolean } ->
  Tok -> Disp
tokDisp { ascii } = Variant.match
  { "Pi": spaceIf ascii TTKeyword "\x2200" "forall"
  , "Lam": nospace TTKeyword "\x03BB" "\\"
  , "BoolAnd": simple space TTOperator "&&"
  , "BoolOr": simple space TTOperator "||"
  , "BoolEQ": simple space TTOperator "=="
  , "BoolNE": simple space TTOperator "!="
  , "NaturalPlus": simple space TTOperator "+"
  , "NaturalTimes": simple space TTOperator "*"
  , "TextAppend": simple space TTOperator "++"
  , "ListAppend": simple space TTOperator "#"
  , "Combine": space TTOperator "\x2227" "/\\"
  , "CombineTypes": space TTOperator "\x2A53" "//\\\\"
  , "Prefer": space TTOperator "\x2AFD" "//"
  , "Equivalent": space TTOperator "\x2261" "==="
  , "ImportAlt": simple space TTImport "?"
  , "Annot": simple space TTSeparator ":"
  , "App": mkSpace Yes No TTOperator "" ""
  , "Field": simple nospace TTOperator "."
  -- Note: the hash value includes the identifying "sha256:" prefix
  , "Hashed": simple space TTImport ""
  , "UsingHeaders": simple space TTImport "using"
  , "Keyword": valued space TTKeyword
  , "Builtin": datum (TTName true)
  , "Name": datum (TTName false)
  , "At": simple nospace TTSeparator "@"
  , "Number": datum TTLiteral
  , "Import": datum TTImport
  , "String": simple nospace TTLiteral "''"
  , "StringData": valued raw TTLiteral
  , "Paren": group "(" ")"
  , "Brace": spread "{" "}"
  , "Bracket": spread "[" "]"
  , "Angle": spread "<" ">"
  , "Interp": (#) unit <<< case _ of
      L -> join (mkSpace No Perhaps TTGrouping) "${"
      R -> join (mkSpace Perhaps No TTGrouping) "}"
  , "Comma": simple spaceAfter TTSeparator ","
  , "Alt": simple space TTSeparator "|"
  , "Equal": simple space TTSeparator "="
  , "Arrow": space TTOperator "\x2192" "->"
  , "Space": simple raw TTSeparator " "
  , "Tab": simple raw TTSeparator "\t"
  } where
    mkSpace bf af tokType uniValue asciiValue (_ :: Unit) =
      { spaceBefore: bf, spaceAfter: af
      , tokType, value: if ascii then asciiValue else uniValue
      }
    spaceIf = join mkSpace <<< if _ then Yes else Perhaps
    simple = compose join
    space = join mkSpace Yes
    nospace = join mkSpace Perhaps
    -- Raw means that there absolutely must not be space added on either side
    -- Appropriate for string literals
    raw = join mkSpace No
    spaceBefore = mkSpace Yes Perhaps
    spaceAfter = mkSpace Perhaps Yes
    valued spacer tokType value = spacer tokType value value unit
    -- I think it is right for "bare words" to not require space
    -- (since everything else does)
    datum = valued nospace
    group l r side = unit # simple nospace TTGrouping
      case side of
        L -> l
        R -> r
    spread l r side = unit #
      simple
        (case side of
          L -> spaceAfter
          R -> spaceBefore
        )
        TTGrouping
        (case side of
          L -> l
          R -> r
        )

type Counting = Additive Int
type Colmn = Counting
type Width = Counting
type Measured m =
  { value :: m
  , length :: Width
  }

type Line = Array Disp
type Lines = Array Line
type MLine = Measured Line
type MLines = Array MLine

printLine' :: forall r m. Monoid m =>
  m ->
  Array (Record (Padding + TokValue m + r)) ->
  m
printLine' spc = _.value <<< Array.foldl folder { value: mempty, space: No } where
  needSpace = case _, _ of
    No, _ -> false
    _, No -> false
    Yes, _ -> true
    _, Yes -> true
    Perhaps, Perhaps -> false
  folder { value, space } { spaceBefore, spaceAfter, value: tok } =
    { value: value <>
        (if needSpace space spaceBefore then spc else mempty) <>
        tok
    , space: spaceAfter
    }

printLine :: Line -> String
printLine = printLine' " "

printLines :: Lines -> String
printLines = Array.foldMap \line -> printLine line <> "\n"

  -- FIXME: measure tabs?
-- Options for laying out a structured display
type LayoutOpts =
  -- The maximum line length, if any
  { line :: Maybe (Additive Int)
  -- Tab options
  , tabs ::
    -- Width of each tab
    { width :: Additive Int
    -- Whether to insert spaces instead of tabs
    , soft :: Boolean
    -- Whether indentation should always be aligned to tab stops
    , align :: Boolean
  } }

-- TODO: handle overflow of a single line
layout :: LayoutOpts -> DispStruct -> MLines
layout opts = layoutFrom mempty where
  -- Measure the length of a line, once it will laid out with appropriate
  -- spacing
  lineLength :: Line -> Additive Int
  lineLength = printLine' (Additive 1) <<< map
    -- FIXME: measure tabs?
    \tok -> tok { value = Additive $ String.length $ tok.value }
  measure :: Line -> MLine
  measure = { value: _, length: _ } <*> lineLength
  -- Nearest tabStop after specified column, if opts.align is set
  tabStop :: Colmn -> Colmn
  tabStop c | not opts.tabs.align = c
  tabStop (Additive col) = Additive $
    let Additive w = opts.tabs.width in
    if col `mod` w == zero
      then col
      else col + (w - (col `mod` w))
  sub' :: Colmn -> Colmn -> Width
  sub' = over2 Additive sub
  tab :: Disp
  tab = { spaceBefore: No, spaceAfter: No, tokType: TTSeparator, value: "\t" }
  spc :: Disp
  spc = { spaceBefore: No, spaceAfter: No, tokType: TTSeparator, value: " " }
  -- Pad a sequence of tokens to a desired width of `goal`, if possible,
  -- using the tab and space preferences set in `opts`.
  padTo :: Width -> MLine -> MLine
  -- If no space is allowed after the last token,
  -- and it is not a space itself, do not bother padding
  padTo _ r@{ value: ts }
    | Just t <- Array.last ts, t /= tab, t /= spc, t.spaceAfter == No = r
  padTo goal { value: ts, length: len } =
    let Additive w = opts.tabs.width in
    let
      extra = max 0 $ un Additive (goal `sub'` len)
      nextStop = tabStop len
      { tabs, spcs } =
        -- use only spaces if `soft` is selected or if the next tab would overrun
        if opts.tabs.soft || extra == zero || nextStop > goal
          then { tabs: zero, spcs: extra }
        -- otherwise we start at the tab stop, and recalculate `extra`
          else
            let
              -- subtract the amount that `nextStop` changed from `len`
              extra' = extra - un Additive (nextStop `sub'` len)
              -- count an extra tab only if `nextStop` changed from `len`
              initial = if extra' == extra then zero else one
            -- divvy the extra up into as many tabs as possible, then spaces
            in { tabs: initial + extra' `div` w, spcs: extra' `mod` w }
      padding = Array.replicate tabs tab <> Array.replicate spcs spc
    in { value: ts <> padding, length: max len goal }
  layoutFrom :: MLine -> DispStruct -> MLines
  layoutFrom pre =
    let
      exceeds ts = case opts.line of
        Nothing -> false
        Just w -> (pre.length <> ts.length) > w
      tryFlatten gs
        | ts <- measure (flatten gs), not exceeds ts
        = Just ts
        | otherwise
        = Nothing
    in case _ of
      In (StrTokens ts) -> [ pre <> measure ts ]
      gs | Just ts <- tryFlatten gs -> [ pre <> ts ]
      In (StrGroup gs) ->
        let
          firstChar (In (StrTokens ts)) = Array.head ts
          firstChar (In (StrGroup gs'')) =
            Array.head gs'' >>= \hd ->
              case Array.head hd.before of
                Nothing -> firstChar hd.line
                Just c -> Just c
          needSpace = case _, _ of
            No, _ -> false
            _, No -> false
            Yes, _ -> true
            _, Yes -> true
            Perhaps, Perhaps -> false
          needsSpace bf ln = or $
            needSpace
            <$> map _.spaceAfter (Array.last bf)
            <*> map _.spaceBefore (firstChar ln)
          gs' = gs # Array.mapWithIndex \i { before, line } ->
            { line
            , padding: padTo pre.length if i == 0 then pre else mempty
            , before:
              { value: before
              , length: lineLength before
            } }
          -- we want to pad each prefix to match the longest one
          -- (taking into account if there needs to be a space on each),
          -- but aligned at the next tab stop (if the option is set)
          goal = tabStop $ append pre.length $
            fromMaybe mempty $ maximum $ gs' <#>
              \r -> r.before.length <>
                (if needsSpace r.before.value r.line then Additive 1 else mempty)
        in gs' >>= \{ before, line, padding } ->
          -- add `before` to `pre` and pad it
          let pre' = (padding <> before) # padTo goal in
          -- and lay out each line
          layoutFrom pre' line
