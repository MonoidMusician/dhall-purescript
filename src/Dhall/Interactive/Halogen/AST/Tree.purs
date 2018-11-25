module Dhall.Interactive.Halogen.AST.Tree where

import Prelude

import Control.Comonad.Env (EnvT(..))
import Data.Array as Array
import Data.Const (Const)
import Data.Exists (Exists, mkExists, runExists)
import Data.Functor.Variant (FProxy, VariantF)
import Data.Functor.Variant as VariantF
import Data.Int as Int
import Data.Lens (ALens', IndexedTraversal', lens')
import Data.Lens as Lens
import Data.Lens as Tuple
import Data.Lens.Indexed (itraversed, unIndex)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Lens.Product as Product
import Data.Maybe (Maybe(..), maybe)
import Data.Monoid (guard)
import Data.Monoid.Disj (Disj(..))
import Data.Natural (Natural, intToNat, natToInt)
import Data.Newtype (over, unwrap)
import Data.Number as Number
import Data.Ord (abs, signum)
import Data.Profunctor.Star (Star(..))
import Data.Symbol (class IsSymbol, SProxy, reflectSymbol)
import Data.Tuple (Tuple(..))
import Dhall.Core (S_, _S)
import Dhall.Core.AST as AST
import Dhall.Core.AST.Noted as Ann
import Dhall.Core.StrMapIsh as IOSM
import Dhall.Interactive.Halogen.AST (SlottedHTML(..))
import Dhall.Interactive.Halogen.Inputs (inline_feather_button_action)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Matryoshka (embed, project)
import Prim.Row as Row
import Unsafe.Coerce (unsafeCoerce)

type Rendering r a = Star (SlottedHTML r) a a
type RenderAnd r a = { df :: a, rndr :: Rendering r a }
type RenderingOptions =
  { interactive :: Boolean
  , editable :: Boolean
  }
{-
type Slot = Array String
type RenderPlus r a =
  -- available slot to insert components at
  { slot :: Slot
  -- pointer to this node in the AST
  , pointer :: AST.ExprI
  -- currently selected expression
  , cursor :: Maybe AST.ExprI
  -- general rendering options
  , opts :: RenderingOptions
  } -> Star (SlottedHTML r) a (Either Action a)
data Action = SelectHere
-}

renderNode :: forall r a.
  String ->
  Array (Tuple String (SlottedHTML r a)) ->
  SlottedHTML r a
renderNode name children = SlottedHTML $ HH.div
  [ HP.class_ $ H.ClassName ("node " <> name) ] $
  Array.cons
    do HH.div [ HP.class_ $ H.ClassName "node-name" ]
        if Array.null children then [ HH.text name ]
        else [ HH.text name, HH.text ":" ]
    do children <#> \(Tuple childname (SlottedHTML child)) ->
        HH.div [ HP.class_ $ H.ClassName "node-child" ]
          [ HH.span_ [ HH.text childname, HH.text ":" ], child ]

data LensedF r i e = LensedF (ALens' i e) (Rendering r e)
type Lensed r i = Exists (LensedF r i)

mkLensed :: forall r i a.
  String ->
  ALens' i a ->
  Rendering r a ->
  Tuple String (Exists (LensedF r i))
mkLensed name focus renderer = Tuple name $ mkExists $ LensedF focus renderer

renderVFNone :: forall r a. Rendering r (VariantF () a)
renderVFNone = Star VariantF.case_

renderVFLensed ::
  forall r f a sym conses conses'.
    IsSymbol sym =>
    Row.Cons sym (FProxy f) conses' conses =>
    Functor f =>
  SProxy sym ->
  Array (Tuple String (Lensed r (f a))) ->
  Rendering r (VariantF conses' a) ->
  Rendering r (VariantF conses a)
renderVFLensed sym renderFA renderRest = Star $
  VariantF.on sym renderCase (unwrap renderRest >>> map unsafeCoerce) where
    renderCase fa = renderNode (reflectSymbol sym) $
      renderFA # (map <<< map) do
        runExists \(LensedF target renderTarget) ->
          unwrap renderTarget (Lens.view (Lens.cloneLens target) fa) <#>
            flip (Lens.set (Lens.cloneLens target)) fa >>> VariantF.inj sym

lensedConst :: forall r a b. String -> Rendering r a -> Array (Tuple String (Exists (LensedF r (Const a b))))
lensedConst name renderer = pure $ Tuple name $ mkExists $ LensedF _Newtype renderer

renderMaybe :: forall r a.
  RenderingOptions -> -- TODO
  RenderAnd r a ->
  Rendering r (Maybe a)
renderMaybe opts { df, rndr: renderA } = Star \as -> SlottedHTML $
  HH.ul [ HP.class_ $ H.ClassName "maybe" ] $ pure $
    case as of
      Nothing -> if not opts.editable then HH.text "(Nothing)" else
        HH.div [ HP.class_ $ H.ClassName "just button" ]
        [ inline_feather_button_action (Just (Just df)) "plus-square" ]
      Just a -> HH.li_ $ join $
        [ guard opts.editable $ pure $ HH.div [ HP.class_ $ H.ClassName "pre button" ]
          [ inline_feather_button_action (Just Nothing) "minus-square" ]
        , pure $ unwrap $ Just <$> unwrap renderA a
        ]

renderIxTraversal :: forall i r s a. Eq i =>
  IndexedTraversal' i s a ->
  { df :: a, rndr :: i -> Rendering r a } ->
  (s -> Array (SlottedHTML r s))
renderIxTraversal foci { df, rndr: renderA } s =
  s # Lens.ifoldMapOf foci \i a ->
    [ unwrap (renderA i) a <#>
      flip (Lens.set (unIndex (Lens.elementsOf foci (eq i)))) s
    ]

renderArray :: forall r a.
  RenderingOptions -> -- TODO
  RenderAnd r a ->
  Rendering r (Array a)
renderArray opts { df, rndr: renderA } = Star \as -> SlottedHTML $
  HH.ol [ HP.class_ $ H.ClassName "array" ] $ map unwrap $
    as # renderIxTraversal itraversed
      { df
      , rndr: \_ -> Star \a ->
          SlottedHTML $ HH.li_ [ unwrap $ unwrap renderA a ]
      }

renderIOSM :: forall r a.
  RenderingOptions -> -- TODO
  RenderAnd r a ->
  Rendering r (IOSM.InsOrdStrMap a)
renderIOSM opts { df, rndr: renderA } = Star \as -> SlottedHTML $
  HH.dl [ HP.class_ $ H.ClassName "strmap" ] $
    IOSM.unIOSM as # Lens.ifoldMapOf itraversed \i (Tuple s a) ->
      let here v = IOSM.mkIOSM $ IOSM.unIOSM as #
            Lens.set (unIndex (Lens.elementsOf itraversed (eq i))) v
      in
      [ HH.dt_
        [ HH.input
          [ HP.type_ HP.InputText
          , HP.value s
          , HE.onValueInput \s' -> Just (here (Tuple s' a))
          ]
        ]
      , HH.dd_ [ unwrap $ unwrap renderA a <#> Tuple s >>> here ]
      ]

renderString :: forall r. RenderingOptions -> Rendering r String
renderString { editable: true } =
  Star \v -> SlottedHTML $ HH.input
    [ HP.type_ HP.InputText
    , HP.value v
    , HE.onValueInput pure
    ]
renderString { editable: false } =
  Star $ SlottedHTML <<< HH.text

renderNatural :: forall r. RenderingOptions -> Rendering r Natural
renderNatural { editable: true } =
  Star \v -> SlottedHTML $ HH.input
    [ HP.type_ HP.InputNumber
    , HP.min zero
    , HP.step (HP.Step one)
    , HP.value (show v)
    , HE.onValueInput (Int.fromString >>> map intToNat)
    ]
renderNatural { editable: false } = Star $ SlottedHTML <<< HH.text <<< show <<< natToInt

renderBoolean :: forall r. RenderingOptions -> Rendering r Boolean
renderBoolean { editable: true } =
  Star \v -> SlottedHTML $
    HH.button [ HE.onClick (pure (pure (not v))) ]
      [ HH.text if v then "True" else "False" ]
renderBoolean { editable: false } = Star $ SlottedHTML <<< HH.text <<<
  if _ then "True" else "False"

renderInt :: forall r. RenderingOptions -> Rendering r Int
renderInt opts@{ editable: true } =
  Star \v -> SlottedHTML $ HH.span_
    [ HH.button [ HE.onClick (pure (pure (negate v))) ]
      [ HH.text if v < 0 then "-" else "+" ]
    , unwrap $ unwrap (renderNatural opts) (intToNat v) <#> natToInt >>> mul (signum v)
    ]
renderInt { editable: false } = Star $ SlottedHTML <<< HH.text <<< show

renderNumber :: forall r. RenderingOptions -> Rendering r Number
renderNumber { editable: true } =
  Star \v -> SlottedHTML $ HH.input
    [ HP.type_ HP.InputNumber
    , HP.step (HP.Step 0.5)
    , HP.value (show (abs v))
    , HE.onValueInput Number.fromString
    ]
renderNumber { editable: false } = Star $ SlottedHTML <<< HH.text <<< show

renderBindingBody :: forall r a.
  RenderingOptions ->
  Rendering r a ->
  Array (Tuple String (Lensed r (AST.BindingBody a)))
renderBindingBody opts renderA =
  let
    _name = lens' \(AST.BindingBody name a0 a1) -> Tuple name \name' -> AST.BindingBody name' a0 a1
    _a0 = lens' \(AST.BindingBody name a0 a1) -> Tuple a0 \a0' -> AST.BindingBody name a0' a1
    _a1 = lens' \(AST.BindingBody name a0 a1) -> Tuple a1 \a1' -> AST.BindingBody name a0 a1'
  in
  [ Tuple "identifier" $ mkExists $ LensedF _name (renderString opts)
  , Tuple "type" $ mkExists $ LensedF _a0 renderA
  , Tuple "body" $ mkExists $ LensedF _a1 renderA
  ]

type RenderChunk cases r a =
  forall conses.
  Rendering r (VariantF conses a) ->
  Rendering r (VariantF (cases IOSM.InsOrdStrMap conses) a)

renderLiterals :: forall r a. RenderingOptions -> RenderChunk AST.Literals r a
renderLiterals opts = identity
  >>> renderVFLensed (_S::S_ "BoolLit") (lensedConst "value" (renderBoolean opts))
  >>> renderVFLensed (_S::S_ "NaturalLit") (lensedConst "value" (renderNatural opts))
  >>> renderVFLensed (_S::S_ "IntegerLit") (lensedConst "value" (renderInt opts))
  >>> renderVFLensed (_S::S_ "DoubleLit") (lensedConst "value" (renderNumber opts))

renderBuiltinTypes :: forall r a. RenderingOptions -> RenderChunk AST.BuiltinTypes r a
renderBuiltinTypes _ = identity
  >>> renderVFLensed (_S::S_ "Bool") named
  >>> renderVFLensed (_S::S_ "Natural") named
  >>> renderVFLensed (_S::S_ "Integer") named
  >>> renderVFLensed (_S::S_ "Double") named
  >>> renderVFLensed (_S::S_ "Text") named
  >>> renderVFLensed (_S::S_ "List") named
  >>> renderVFLensed (_S::S_ "Optional") named
  where named = []

renderBuiltinFuncs :: forall r a. RenderingOptions -> RenderChunk AST.BuiltinFuncs r a
renderBuiltinFuncs _ = identity
  >>> renderVFLensed (_S::S_ "NaturalFold") named
  >>> renderVFLensed (_S::S_ "NaturalBuild") named
  >>> renderVFLensed (_S::S_ "NaturalIsZero") named
  >>> renderVFLensed (_S::S_ "NaturalEven") named
  >>> renderVFLensed (_S::S_ "NaturalOdd") named
  >>> renderVFLensed (_S::S_ "NaturalToInteger") named
  >>> renderVFLensed (_S::S_ "NaturalShow") named
  >>> renderVFLensed (_S::S_ "IntegerShow") named
  >>> renderVFLensed (_S::S_ "IntegerToDouble") named
  >>> renderVFLensed (_S::S_ "DoubleShow") named
  >>> renderVFLensed (_S::S_ "ListBuild") named
  >>> renderVFLensed (_S::S_ "ListFold") named
  >>> renderVFLensed (_S::S_ "ListLength") named
  >>> renderVFLensed (_S::S_ "ListHead") named
  >>> renderVFLensed (_S::S_ "ListLast") named
  >>> renderVFLensed (_S::S_ "ListIndexed") named
  >>> renderVFLensed (_S::S_ "ListReverse") named
  >>> renderVFLensed (_S::S_ "OptionalFold") named
  >>> renderVFLensed (_S::S_ "OptionalBuild") named
  where named = []

renderTerminals :: forall r a. RenderingOptions -> RenderChunk AST.Terminals r a
renderTerminals opts = identity
  >>> renderVFLensed (_S::S_ "Const") renderConst
  >>> renderVFLensed (_S::S_ "Var") renderVar
  where
    renderConst = pure $ mkLensed "constant" _Newtype $ Star \v -> SlottedHTML $
      HH.select
        [ HE.onSelectedIndexChange (Array.(!!) [AST.Type, AST.Kind])
        ]
        [ HH.option [ HP.selected (v == AST.Type) ] [ HH.text "Type" ]
        , HH.option [ HP.selected (v == AST.Kind) ] [ HH.text "Kind" ]
        ]
    renderVar =
      let
        _identifier = lens' \(AST.V identifier ix) -> Tuple identifier \identifier' -> AST.V identifier' ix
        _ix = lens' \(AST.V identifier ix) -> Tuple ix \ix' -> AST.V identifier ix'
      in
      [ mkLensed "identifier" (_Newtype <<< _identifier) (renderString opts)
      , mkLensed "index" (_Newtype <<< _ix) (renderInt opts)
      ]

renderBuiltinBinOps :: forall r a. RenderingOptions -> RenderAnd r a -> RenderChunk AST.BuiltinBinOps r a
renderBuiltinBinOps _ { rndr: renderA } = identity
  >>> renderVFLensed (_S::S_ "BoolAnd") renderBinOp
  >>> renderVFLensed (_S::S_ "BoolOr") renderBinOp
  >>> renderVFLensed (_S::S_ "BoolEQ") renderBinOp
  >>> renderVFLensed (_S::S_ "BoolNE") renderBinOp
  >>> renderVFLensed (_S::S_ "NaturalPlus") renderBinOp
  >>> renderVFLensed (_S::S_ "NaturalTimes") renderBinOp
  >>> renderVFLensed (_S::S_ "TextAppend") renderBinOp
  >>> renderVFLensed (_S::S_ "ListAppend") renderBinOp
  >>> renderVFLensed (_S::S_ "Combine") renderBinOp
  >>> renderVFLensed (_S::S_ "CombineTypes") renderBinOp
  >>> renderVFLensed (_S::S_ "Prefer") renderBinOp
  >>> renderVFLensed (_S::S_ "ImportAlt") renderBinOp
  where
    _l = lens' \(AST.Pair l r) -> Tuple l \l' -> AST.Pair l' r
    _r = lens' \(AST.Pair l r) -> Tuple r \r' -> AST.Pair l r'
    renderBinOp =
      [ mkLensed "L" _l renderA
      , mkLensed "R" _r renderA
      ]

renderBuiltinOps :: forall r a. RenderingOptions -> RenderAnd r a -> RenderChunk AST.BuiltinOps r a
renderBuiltinOps opts { df, rndr: renderA } = renderBuiltinBinOps opts { df, rndr: renderA }
  >>> renderVFLensed (_S::S_ "Field") renderField
  >>> renderVFLensed (_S::S_ "Constructors") [ mkLensed "argument" _Newtype renderA ]
  >>> renderVFLensed (_S::S_ "BoolIf") renderBoolIf
  >>> renderVFLensed (_S::S_ "Merge") renderMerge
  >>> renderVFLensed (_S::S_ "Project") renderProject
  where
    renderField =
      [ mkLensed "expression" Tuple._2 renderA
      , mkLensed "field" Tuple._1 (renderString opts)
      ]
    _0 = lens' \(AST.Triplet a0 a1 a2) -> Tuple a0 \a0' -> AST.Triplet a0' a1 a2
    _1 = lens' \(AST.Triplet a0 a1 a2) -> Tuple a1 \a1' -> AST.Triplet a0 a1' a2
    _2 = lens' \(AST.Triplet a0 a1 a2) -> Tuple a2 \a2' -> AST.Triplet a0 a1 a2'
    renderBoolIf =
      [ mkLensed "if" _0 renderA
      , mkLensed "then" _1 renderA
      , mkLensed "else" _2 renderA
      ]
    m_0 = lens' \(AST.MergeF a0 a1 a2) -> Tuple a0 \a0' -> AST.MergeF a0' a1 a2
    m_1 = lens' \(AST.MergeF a0 a1 a2) -> Tuple a1 \a1' -> AST.MergeF a0 a1' a2
    m_2 = lens' \(AST.MergeF a0 a1 a2) -> Tuple a2 \a2' -> AST.MergeF a0 a1 a2'
    renderMerge =
      [ mkLensed "handlers" m_0 renderA
      , mkLensed "argument" m_1 renderA
      , mkLensed "type" m_2 (renderMaybe opts { df, rndr: renderA })
      ]
    renderProject =
      [ mkLensed "expression" Tuple._2 renderA
      , mkLensed "fields" (Tuple._1 <<< _Newtype)
        (renderIOSM opts { df: unit, rndr: Star $ const $ SlottedHTML $ HH.text $ "<included>" })
      ]

renderBuiltinTypes2 :: forall r a. RenderingOptions -> RenderAnd r a -> RenderChunk AST.BuiltinTypes2 r a
renderBuiltinTypes2 opts { df, rndr: renderA } = identity
  >>> renderVFLensed (_S::S_ "Record")
    [ mkLensed "types" identity (renderIOSM opts { df, rndr: renderA }) ]
  >>> renderVFLensed (_S::S_ "Union")
    [ mkLensed "types" identity (renderIOSM opts { df, rndr: renderA }) ]

renderLiterals2 :: forall r a. RenderingOptions -> RenderAnd r a -> RenderChunk AST.Literals2 r a
renderLiterals2 opts { df, rndr: renderA } = identity
  >>> renderVFLensed (_S::S_ "None") []
  >>> renderVFLensed (_S::S_ "Some") [ mkLensed "argument" _Newtype renderA ]
  >>> renderVFLensed (_S::S_ "RecordLit")
    [ mkLensed "values" identity (renderIOSM opts { df, rndr: renderA }) ]
  >>> renderVFLensed (_S::S_ "UnionLit") renderUnionLit
  >>> renderVFLensed (_S::S_ "OptionalLit") renderOptionalLit
  >>> renderVFLensed (_S::S_ "ListLit") renderListLit
  >>> renderVFLensed (_S::S_ "TextLit") [] -- TODO
  where
    renderUnionLit =
      [ mkLensed "label" (Product._1 <<< Tuple._1) (renderString opts)
      , mkLensed "value" (Product._1 <<< Tuple._2) renderA
      , mkLensed "types" Product._2 (renderIOSM opts { df, rndr: renderA })
      ]
    renderOptionalLit =
      [ mkLensed "type" (Product._1 <<< _Newtype) renderA
      , mkLensed "value" Product._2 (renderMaybe opts { df, rndr: renderA })
      ]
    renderListLit =
      [ mkLensed "type" Product._1 (renderMaybe opts { df, rndr: renderA })
      , mkLensed "values" Product._2 (renderArray opts { df, rndr: renderA })
      ]

renderSyntax :: forall r a. RenderingOptions -> RenderAnd r a -> RenderChunk AST.Syntax r a
renderSyntax opts { df, rndr: renderA } = identity
  >>> renderVFLensed (_S::S_ "App") renderApp
  >>> renderVFLensed (_S::S_ "Annot") renderAnnot
  >>> renderVFLensed (_S::S_ "Lam") (renderBindingBody opts renderA)
  >>> renderVFLensed (_S::S_ "Pi") (renderBindingBody opts renderA)
  >>> renderVFLensed (_S::S_ "Let") renderLet
  where
    _l = lens' \(AST.Pair l r) -> Tuple l \l' -> AST.Pair l' r
    _r = lens' \(AST.Pair l r) -> Tuple r \r' -> AST.Pair l r'
    renderApp =
      [ mkLensed "function" _l renderA
      , mkLensed "argument" _r renderA
      ]
    renderAnnot =
      [ mkLensed "value" _l renderA
      , mkLensed "type" _r renderA
      ]
    _name = lens' \(AST.LetF name a0 a1 a2) -> Tuple name \name' -> AST.LetF name' a0 a1 a2
    _a0 = lens' \(AST.LetF name a0 a1 a2) -> Tuple a0 \a0' -> AST.LetF name a0' a1 a2
    _a1 = lens' \(AST.LetF name a0 a1 a2) -> Tuple a1 \a1' -> AST.LetF name a0 a1' a2
    _a2 = lens' \(AST.LetF name a0 a1 a2) -> Tuple a2 \a2' -> AST.LetF name a0 a1 a2'
    renderLet =
      [ mkLensed "identifier" _name (renderString opts)
      , mkLensed "type" _a0 (renderMaybe opts { df, rndr: renderA })
      , mkLensed "value" _a1 renderA
      , mkLensed "body" _a2 renderA
      ]

renderAllTheThings :: forall r a.
  RenderingOptions ->
  RenderAnd r a ->
  RenderChunk AST.AllTheThings r a
renderAllTheThings opts renderA = identity
  >>> renderLiterals opts
  >>> renderBuiltinTypes opts
  >>> renderBuiltinFuncs opts
  >>> renderTerminals opts
  >>> renderBuiltinOps opts renderA
  >>> renderLiterals2 opts renderA
  >>> renderBuiltinTypes2 opts renderA
  >>> renderSyntax opts renderA

-- TODO: add selection, add editing, add slots and zuruzuru &c.
renderExpr :: forall a. Show a =>
  RenderingOptions ->
  Ann.Expr IOSM.InsOrdStrMap { collapsed :: Disj Boolean } (Maybe a) ->
  SlottedHTML () (Ann.Expr IOSM.InsOrdStrMap { collapsed :: Disj Boolean } (Maybe a))
renderExpr opts enn = map embed $ project enn # \(EnvT (Tuple ann e)) -> SlottedHTML $
  let df = Ann.innote mempty (AST.mkEmbed Nothing) in
  HH.div [ HP.class_ $ H.ClassName "expression" ] $ join $
    [ guard opts.interactive $ pure $
      HH.div [ HP.class_ $ H.ClassName "pre button" ]
        let act = (Just (EnvT (Tuple (ann { collapsed = over Disj not ann.collapsed }) e)))
        in [ inline_feather_button_action act if unwrap ann.collapsed then "eye" else "eye-off" ]
    , guard (not unwrap ann.collapsed) $ pure $ unwrap $
        map (EnvT <<< Tuple ann <<< AST.ERVF) $ unwrap e # unwrap do
          renderAllTheThings opts { df, rndr: Star (renderExpr opts) } $ renderVFNone #
            renderVFLensed (_S::S_ "Embed")
              [ mkLensed "value" _Newtype $ Star $ SlottedHTML <<< HH.text <<< maybe "_" show ]
    ]
