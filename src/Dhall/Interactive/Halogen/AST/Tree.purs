module Dhall.Interactive.Halogen.AST.Tree where

import Prelude

import Control.Comonad (extract)
import Control.Comonad.Cofree ((:<))
import Control.Comonad.Cofree as Cofree
import Control.Comonad.Env (EnvT(..), withEnvT)
import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.Const (Const)
import Data.Exists (Exists, mkExists, runExists)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Variant (FProxy, VariantF)
import Data.Functor.Variant as VariantF
import Data.Int as Int
import Data.Lens (ALens', IndexedTraversal', Lens', _1, _2, lens, lens', (.~), (^.))
import Data.Lens as Lens
import Data.Lens as Tuple
import Data.Lens.Indexed (itraversed, unIndex)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Lens.Product as Product
import Data.Lens.Record (prop)
import Data.List (List(..))
import Data.Maybe (Maybe(..), maybe)
import Data.Monoid (guard)
import Data.Monoid.Disj (Disj)
import Data.Natural (Natural, intToNat, natToInt)
import Data.Newtype (class Newtype, under, unwrap)
import Data.Number as Number
import Data.Ord (abs, signum)
import Data.Profunctor.Star (Star(..))
import Data.Symbol (class IsSymbol, SProxy, reflectSymbol)
import Data.These (These(..))
import Data.Tuple (Tuple(..))
import Dhall.Core (S_, _S)
import Dhall.Core.AST as AST
import Dhall.Core.AST.Noted as Ann
import Dhall.Core.StrMapIsh as IOSM
import Dhall.Interactive.Halogen.AST (SlottedHTML(..))
import Dhall.Interactive.Halogen.Inputs (inline_feather_button_action)
import Effect.Aff (Aff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Matryoshka (embed, project, transCata)
import Prim.Row as Row
import Unsafe.Coerce (unsafeCoerce)

type Rendering r m a = Star (Compose (SlottedHTML r) (These m)) a a
rendering :: forall r m a. (a -> H.ComponentHTML' (These m a) r Aff) -> Rendering r m a
rendering f = Star $ Compose <<< SlottedHTML <<< f
renderingR :: forall r m a. (a -> H.ComponentHTML' a r Aff) -> Rendering r m a
renderingR f = Star $ Compose <<< map That <<< SlottedHTML <<< f
type RenderAnd r m a = { df :: a, rndr :: Rendering r m a }
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

renderNode :: forall r m a.
  String ->
  Array (Tuple String (Compose (SlottedHTML r) (These m) a)) ->
  Compose (SlottedHTML r) (These m) a
renderNode name children = Compose $ SlottedHTML $ HH.div
  [ HP.class_ $ H.ClassName ("node " <> name) ] $
  Array.cons
    do HH.div [ HP.class_ $ H.ClassName "node-name" ]
        if Array.null children then [ HH.text name ]
        else [ HH.text name, HH.text ":" ]
    do children <#> \(Tuple childname (Compose (SlottedHTML child))) ->
        HH.div [ HP.class_ $ H.ClassName "node-child" ]
          [ HH.span_ [ HH.text childname, HH.text ": " ], child ]

data LensedF r m i e = LensedF (ALens' i e) (Rendering r m e)
type Lensed r m i = Exists (LensedF r m i)

mkLensed :: forall r m i a.
  String ->
  ALens' i a ->
  Rendering r m a ->
  Tuple String (Exists (LensedF r m i))
mkLensed name focus renderer = Tuple name $ mkExists $ LensedF focus renderer

renderVFNone :: forall r m a. Rendering r m (VariantF () a)
renderVFNone = Star VariantF.case_

renderVFLensed ::
  forall r m f a sym conses conses'.
    IsSymbol sym =>
    Row.Cons sym (FProxy f) conses' conses =>
    Functor f =>
  SProxy sym ->
  Array (Tuple String (Lensed r m (f a))) ->
  Rendering r m (VariantF conses' a) ->
  Rendering r m (VariantF conses a)
renderVFLensed sym renderFA renderRest = Star $
  VariantF.on sym renderCase (unwrap renderRest >>> map unsafeCoerce) where
    renderCase fa = renderNode (reflectSymbol sym) $
      renderFA # (map <<< map) do
        runExists \(LensedF target renderTarget) ->
          unwrap renderTarget (Lens.view (Lens.cloneLens target) fa) <#>
            flip (Lens.set (Lens.cloneLens target)) fa >>> VariantF.inj sym

lensedConst :: forall r m a b. String -> Rendering r m a -> Array (Tuple String (Exists (LensedF r m (Const a b))))
lensedConst name renderer = pure $ Tuple name $ mkExists $ LensedF _Newtype renderer

renderMaybe :: forall r m a.
  RenderingOptions -> -- TODO
  RenderAnd r m a ->
  Rendering r m (Maybe a)
renderMaybe opts { df, rndr: renderA } = rendering \as ->
  HH.ul [ HP.class_ $ H.ClassName "maybe" ] $ pure $
    case as of
      Nothing -> if not opts.editable then HH.text "(Nothing)" else
        HH.div [ HP.class_ $ H.ClassName "just button" ]
        [ inline_feather_button_action (Just (That (Just df))) "plus-square" ]
      Just a -> HH.li_ $ join $
        [ guard opts.editable $ pure $ HH.div [ HP.class_ $ H.ClassName "pre button" ]
          [ inline_feather_button_action (Just (That Nothing)) "minus-square" ]
        , pure $ unwrap $ unwrap $ Just <$> unwrap renderA a
        ]

renderIxTraversal :: forall i r m s a. Eq i =>
  IndexedTraversal' i s a ->
  { df :: a, rndr :: i -> Rendering r m a } ->
  (s -> Array (Compose (SlottedHTML r) (These m) s))
renderIxTraversal foci { df, rndr: renderA } s =
  s # Lens.ifoldMapOf foci \i a ->
    [ unwrap (renderA i) a <#>
      flip (Lens.set (unIndex (Lens.elementsOf foci (eq i)))) s
    ]

renderArray :: forall r m a.
  RenderingOptions -> -- TODO
  RenderAnd r m a ->
  Rendering r m (Array a)
renderArray opts { df, rndr: renderA } = rendering \as ->
  HH.ol [ HP.class_ $ H.ClassName "array" ] $ map (unwrap <<< unwrap) $
    as # renderIxTraversal itraversed
      { df
      , rndr: \_ -> rendering \a -> HH.li_ [ unwrap $ unwrap $ unwrap renderA a ]
      }

renderIOSM :: forall r m a.
  RenderingOptions -> -- TODO
  RenderAnd r m a ->
  Rendering r m (IOSM.InsOrdStrMap a)
renderIOSM opts { df, rndr: renderA } = rendering \as ->
  HH.dl [ HP.class_ $ H.ClassName "strmap" ] $
    IOSM.unIOSM as # Lens.ifoldMapOf itraversed \i (Tuple s a) ->
      let here v = IOSM.mkIOSM $ IOSM.unIOSM as #
            Lens.set (unIndex (Lens.elementsOf itraversed (eq i))) v
      in
      [ HH.dt_
        [ HH.input
          [ HP.type_ HP.InputText
          , HP.value s
          , HE.onValueInput \s' -> Just (That (here (Tuple s' a)))
          ]
        ]
      , HH.dd_ [ unwrap $ unwrap $ unwrap renderA a <#> Tuple s >>> here ]
      ]

renderString :: forall r m. RenderingOptions -> Rendering r m String
renderString { editable: true } =
  renderingR \v -> HH.input
    [ HP.type_ HP.InputText
    , HP.value v
    , HE.onValueInput pure
    ]
renderString { editable: false } =
  rendering HH.text

renderNatural :: forall r m. RenderingOptions -> Rendering r m Natural
renderNatural { editable: true } = renderingR \v -> HH.input
  [ HP.type_ HP.InputNumber
  , HP.min zero
  , HP.step (HP.Step one)
  , HP.value (show v)
  , HE.onValueInput (Int.fromString >>> map intToNat)
  ]
renderNatural { editable: false } = rendering $ HH.text <<< show <<< natToInt

renderBoolean :: forall r m. RenderingOptions -> Rendering r m Boolean
renderBoolean { editable: true } = renderingR \v ->
  HH.button [ HE.onClick (pure (pure (not v))) ]
    [ HH.text if v then "True" else "False" ]
renderBoolean { editable: false } = rendering $ HH.text <<<
  if _ then "True" else "False"

renderInt :: forall r m. RenderingOptions -> Rendering r m Int
renderInt opts@{ editable: true } = rendering \v -> HH.span_
  [ HH.button [ HE.onClick (pure (pure (That (negate v)))) ]
    [ HH.text if v < 0 then "-" else "+" ]
  , unwrap $ unwrap $ unwrap (renderNatural opts) (intToNat v) <#> natToInt >>> mul (signum v)
  ]
renderInt { editable: false } = rendering $ HH.text <<< show

renderNumber :: forall r m. RenderingOptions -> Rendering r m Number
renderNumber { editable: true } = renderingR \v -> HH.input
  [ HP.type_ HP.InputNumber
  , HP.step (HP.Step 0.5)
  , HP.value (show (abs v))
  , HE.onValueInput Number.fromString
  ]
renderNumber { editable: false } = rendering $ HH.text <<< show

renderBindingBody :: forall r m a.
  RenderingOptions ->
  Rendering r m a ->
  Array (Tuple String (Lensed r m (AST.BindingBody a)))
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

type RenderChunk cases r m a =
  forall conses.
  Rendering r m (VariantF conses a) ->
  Rendering r m (VariantF (cases IOSM.InsOrdStrMap conses) a)

renderLiterals :: forall r m a. RenderingOptions -> RenderChunk AST.Literals r m a
renderLiterals opts = identity
  >>> renderVFLensed (_S::S_ "BoolLit") (lensedConst "value" (renderBoolean opts))
  >>> renderVFLensed (_S::S_ "NaturalLit") (lensedConst "value" (renderNatural opts))
  >>> renderVFLensed (_S::S_ "IntegerLit") (lensedConst "value" (renderInt opts))
  >>> renderVFLensed (_S::S_ "DoubleLit") (lensedConst "value" (renderNumber opts))

renderBuiltinTypes :: forall r m a. RenderingOptions -> RenderChunk AST.BuiltinTypes r m a
renderBuiltinTypes _ = identity
  >>> renderVFLensed (_S::S_ "Bool") named
  >>> renderVFLensed (_S::S_ "Natural") named
  >>> renderVFLensed (_S::S_ "Integer") named
  >>> renderVFLensed (_S::S_ "Double") named
  >>> renderVFLensed (_S::S_ "Text") named
  >>> renderVFLensed (_S::S_ "List") named
  >>> renderVFLensed (_S::S_ "Optional") named
  >>> renderVFLensed (_S::S_ "Const") renderConst
  where
    named = []
    renderConst = pure $ mkLensed "constant" _Newtype $ renderingR \v ->
      HH.select
        [ HE.onSelectedIndexChange (Array.(!!) [AST.Type, AST.Kind])
        ]
        [ HH.option [ HP.selected (v == AST.Type) ] [ HH.text "Type" ]
        , HH.option [ HP.selected (v == AST.Kind) ] [ HH.text "Kind" ]
        ]

renderBuiltinFuncs :: forall r m a. RenderingOptions -> RenderChunk AST.BuiltinFuncs r m a
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

renderBuiltinBinOps :: forall r m a. RenderingOptions -> RenderAnd r m a -> RenderChunk AST.BuiltinBinOps r m a
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

renderBuiltinOps :: forall r m a. RenderingOptions -> RenderAnd r m a -> RenderChunk AST.BuiltinOps r m a
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
        (renderIOSM opts { df: unit, rndr: rendering $ const $ HH.text $ "<included>" })
      ]

renderBuiltinTypes2 :: forall r m a. RenderingOptions -> RenderAnd r m a -> RenderChunk AST.BuiltinTypes2 r m a
renderBuiltinTypes2 opts { df, rndr: renderA } = identity
  >>> renderVFLensed (_S::S_ "Record")
    [ mkLensed "types" identity (renderIOSM opts { df, rndr: renderA }) ]
  >>> renderVFLensed (_S::S_ "Union")
    [ mkLensed "types" identity (renderIOSM opts { df, rndr: renderA }) ]

renderLiterals2 :: forall r m a. RenderingOptions -> RenderAnd r m a -> RenderChunk AST.Literals2 r m a
renderLiterals2 opts { df, rndr: renderA } = identity
  >>> renderVFLensed (_S::S_ "None") []
  >>> renderVFLensed (_S::S_ "Some") [ mkLensed "value" _Newtype renderA ]
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

renderVariable :: forall r m a. RenderingOptions -> RenderAnd r m a -> RenderChunk AST.Variable r m a
renderVariable opts { df, rndr: renderA } = identity
  >>> renderVFLensed (_S::S_ "Var") renderVar
  >>> renderVFLensed (_S::S_ "Lam") (renderBindingBody opts renderA)
  >>> renderVFLensed (_S::S_ "Pi") (renderBindingBody opts renderA)
  >>> renderVFLensed (_S::S_ "Let") renderLet
  where
    renderVar =
      let
        _identifier = lens' \(AST.V identifier ix) -> Tuple identifier \identifier' -> AST.V identifier' ix
        _ix = lens' \(AST.V identifier ix) -> Tuple ix \ix' -> AST.V identifier ix'
      in
      [ mkLensed "identifier" (_Newtype <<< _identifier) (renderString opts)
      , mkLensed "index" (_Newtype <<< _ix) (renderInt opts)
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

renderSyntax :: forall r m a. RenderingOptions -> RenderAnd r m a -> RenderChunk AST.Syntax r m a
renderSyntax opts { df, rndr: renderA } = identity
  >>> renderVFLensed (_S::S_ "App") renderApp
  >>> renderVFLensed (_S::S_ "Annot") renderAnnot
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

renderAllTheThings :: forall r m a.
  RenderingOptions ->
  RenderAnd r m a ->
  RenderChunk AST.AllTheThings r m a
renderAllTheThings opts renderA = identity
  >>> renderLiterals opts
  >>> renderBuiltinTypes opts
  >>> renderBuiltinFuncs opts
  >>> renderVariable opts renderA
  >>> renderBuiltinOps opts renderA
  >>> renderLiterals2 opts renderA
  >>> renderBuiltinTypes2 opts renderA
  >>> renderSyntax opts renderA

type Ann = { collapsed :: Disj Boolean }
type IdxAnn = Tuple Ann AST.ExprI
type AnnExpr = Ann.Expr IOSM.InsOrdStrMap Ann
type IdxAnnExpr = Ann.Expr IOSM.InsOrdStrMap IdxAnn

newtype Customize slots i o = Customize
  (i -> { actions :: Array
    { icon :: String
    , action :: Maybe (Unit -> o)
    }
  , wrap :: (Unit -> SlottedHTML slots o) -> SlottedHTML slots o
  })
derive instance newtypeCustomize :: Newtype (Customize slots i o) _
instance semigroupCustomize :: Semigroup (Customize slots i o) where
  append (Customize c1) (Customize c2) = Customize \i ->
    let c1i = c1 i in let c2i = c2 i in
    { actions: c1i.actions <> c2i.actions
    , wrap: \h -> c1i.wrap (\_ -> c2i.wrap h)
    }
instance monoidCustomize :: Monoid (Customize slots i o) where
  mempty = Customize \_ -> { actions: mempty, wrap: (#) unit }

mkActions :: forall slots i o.
  (i -> Array { icon :: String, action :: Maybe (Unit -> o) }) ->
  Customize slots i o
mkActions actions = Customize \i -> { wrap: (#) unit, actions: actions i }

mkInteractions :: forall slots i o.
  RenderingOptions ->
  (i -> Array { icon :: String, action :: Maybe (Unit -> o) }) ->
  Customize slots i o
mkInteractions opts = if opts.interactive then mkActions else mempty

indexFrom :: forall x. AST.ExprI -> AnnExpr x -> IdxAnnExpr x
indexFrom loc = Ann.notateIndexFrom loc <<< lmap Tuple
unindex :: forall x. IdxAnnExpr x -> AnnExpr x
unindex = transCata (withEnvT \(Tuple ann _) -> ann)

-- TODO: add selection, add editing, add slots and zuruzuru &c.
renderExprWith :: forall slots o a. Show a =>
  RenderingOptions ->
  Customize slots (IdxAnnExpr (Maybe a)) (These o (AnnExpr (Maybe a))) ->
  AnnExpr (Maybe a) ->
  SlottedHTML slots (These o (AnnExpr (Maybe a)))
renderExprWith opts customize = indexFrom Nil >>> go where
  cons ann e = embed (EnvT (Tuple ann (AST.ERVF (map unindex e))))
  go ::
    IdxAnnExpr (Maybe a) ->
    SlottedHTML slots (These o (AnnExpr (Maybe a)))
  go enn = project enn # \(EnvT (Tuple (Tuple ann hereIx) e)) -> SlottedHTML $
    let df = Ann.innote mempty (AST.mkEmbed Nothing) in
    HH.div [ HP.class_ $ H.ClassName "expression" ] $ join
      let custom = unwrap customize enn in
      [ custom.actions <#> \{ action, icon } ->
          HH.div [ HP.class_ $ H.ClassName "pre button" ]
            [ under SlottedHTML (map ((#) unit)) $ inline_feather_button_action action icon ]
      , pure $ unwrap $ custom.wrap \_ -> unwrap $
          map (cons ann) $ unwrap e # unwrap do
            renderAllTheThings opts { df, rndr: Star (map (indexFrom hereIx) {- necessary evil -} <<< Compose <<< go) } $ renderVFNone #
              renderVFLensed (_S::S_ "Embed")
                [ mkLensed "value" _Newtype $ rendering $ HH.text <<< maybe "_" show ]
      ]

renderExprSelectable :: forall slots a. Show a =>
  RenderingOptions ->
  Maybe AST.ExprI ->
  AnnExpr (Maybe a) ->
  SlottedHTML slots (These (Maybe AST.ExprI) (AnnExpr (Maybe a)))
renderExprSelectable opts selectedIx = renderExprWith opts $
  selectable opts selectedIx identity <> collapsible opts

_topAnn :: forall m s a. Lens' (Ann.Expr m s a) s
_topAnn = _Newtype <<< lens extract
  \old ann -> ann :< Cofree.tail old

_collapsed :: Lens' IdxAnn Boolean
_collapsed = _1 <<< prop (_S::S_ "collapsed") <<< _Newtype

_idx :: Lens' IdxAnn AST.ExprI
_idx = _2

collapsible :: forall slots o a.
  RenderingOptions -> Customize slots (IdxAnnExpr a) (These o (AnnExpr a))
collapsible opts =
  if not opts.interactive then mempty else Customize \e ->
  let collapsed = e ^. (_topAnn <<< _collapsed) in
  { actions: pure
    { icon: if collapsed then "eye" else "eye-off"
    , action: pure \_ -> That $ unindex $ (_topAnn <<< _collapsed) not e
    }
  , wrap: if not collapsed then (#) unit else \_ -> SlottedHTML $
      HH.div [ HP.class_ (H.ClassName "collapsed") ] []
  }

selectable :: forall slots o a. Show a =>
  RenderingOptions ->
  Maybe AST.ExprI -> (Maybe AST.ExprI -> o) ->
  Customize slots (IdxAnnExpr a) (These o (AnnExpr a))
selectable opts selectedIx injIx =
  if not opts.interactive then mempty else Customize \e ->
  let
    hereIx = e ^. (_topAnn <<< _idx)
    selected = Just hereIx == selectedIx
  in
  { actions: pure
      { icon: if selected then "crosshair" else "disc"
      , action: if selected
        then pure \_ -> This (injIx Nothing)
        else pure \_ -> Both (injIx (Just hereIx)) $ unindex $ ((_topAnn <<< _collapsed) .~ false) e
      }
  , wrap: if not selected then (#) unit else \inner -> SlottedHTML $
      HH.div [ HP.class_ (H.ClassName "selected") ]
        [ unwrap (inner unit) ]
  }
