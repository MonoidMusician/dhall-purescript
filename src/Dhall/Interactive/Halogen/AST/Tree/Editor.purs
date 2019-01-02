module Dhall.Interactive.Halogen.AST.Tree.Editor where

import Prelude

import Control.Comonad (extract)
import Control.Monad.Writer (WriterT, runWriterT)
import Control.Plus (empty, (<|>))
import Data.Array (any, fold, intercalate)
import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Bifoldable (bifoldMap)
import Data.Either (either)
import Data.Foldable (for_)
import Data.FunctorWithIndex (mapWithIndex)
import Data.HeytingAlgebra (tt)
import Data.Lens (Traversal', _2, (%=), (.=), (.~))
import Data.Lens as L
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.List (List(..), (:))
import Data.List as List
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.Monoid (guard)
import Data.Natural (Natural)
import Data.Newtype (un, unwrap)
import Data.These (These(..))
import Data.TraversableWithIndex (class TraversableWithIndex)
import Data.Tuple (fst)
import Data.Variant as Variant
import Dhall.Context as Dhall.Context
import Dhall.Core (S_, _S)
import Dhall.Core as AST
import Dhall.Core.AST (ExprI, ExprRowVFI(..))
import Dhall.Core.AST.Noted as Ann
import Dhall.Core.AST.Operations.Location (Location)
import Dhall.Core.AST.Operations.Location as Loc
import Dhall.Core.AST.Types.Basics (Three(..))
import Dhall.Core.Imports as Core.Imports
import Dhall.Core.StrMapIsh as IOSM
import Dhall.Core.Zippers (_ix)
import Dhall.Core.Zippers.Recursive (_recurse)
import Dhall.Interactive.Halogen.AST (SlottedHTML(..))
import Dhall.Interactive.Halogen.AST.Tree (AnnExpr, collapsible, mkActions, renderExprWith, selectable)
import Dhall.Interactive.Halogen.Icons as Icons
import Dhall.Interactive.Halogen.Inputs (inline_feather_button_action)
import Dhall.Lib.Timeline (Timeline)
import Dhall.Lib.Timeline as Timeline
import Dhall.Parser as Dhall.Parser
import Dhall.TypeCheck (Errors, L, TypeCheckError, locateE)
import Effect.Aff (Aff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Type.Row (type (+))
import Unsafe.Coerce (unsafeCoerce)
import Validation.These (Erroring(..))

type Ixpr = AnnExpr (Maybe Core.Imports.Import)
type EditState =
  { value :: Timeline Ixpr
  , views :: Array ViewId
  , nextView :: ViewId
  , userInput :: String
  -- , highlights :: Array { variety :: HighlightVariety, pos :: Derivation }
  }
type ViewId = Natural
data GlobalActions = NoGlobalActions Void
data EditActions
  = Set Ixpr -- lowest common denominator: unsatisfactory, but works
  | Undo
  | Redo
  | NewView Location
  | DeleteView
data EditQuery a
  = EditAction (Maybe ViewId) a EditActions
  | Output a -- output Ixpr to parent
  | Check (Ixpr -> a) -- check its current value
  | UserInput a String

type ERROR = Erroring (TypeCheckError (Errors + ( "Not found" :: ExprRowVFI )) (L IOSM.InsOrdStrMap (Maybe Core.Imports.Import)))
type ViewState =
  { parsed :: Maybe Ixpr
  , value :: Ixpr
  , view :: Location
  , selection :: Maybe ExprI
  }
type ViewRender =
  { st :: ViewState
  , window :: ERROR Ixpr
  , editable :: Boolean
  , exists :: Boolean
  , typechecks :: Boolean
  }
data ViewActions
  = Select (Maybe ExprI)
  | Un_Focus Int Location -- pop foci and move down to new location
  | SetSelection Ixpr -- set new Ixpr at selection
  | SetView Ixpr
data ViewQuery a
  = ViewInitialize a Location
  | ViewAction a (Array ViewActions)
  | Raise a EditActions
  | Receive a { parsed :: Maybe Ixpr, value :: Ixpr }

tpi :: Maybe Core.Imports.Import -> AST.Expr IOSM.InsOrdStrMap (Maybe Core.Imports.Import)
tpi _ = pure Nothing

unWriterT :: forall m f a. Functor f => WriterT m f a -> f a
unWriterT = runWriterT >>> map fst

editor :: H.Component HH.HTML EditQuery Ixpr Ixpr Aff
editor = H.component
  { initializer: Nothing
  , finalizer: Nothing
  , receiver: Just <<< EditAction Nothing unit <<< Set
  , initialState: ({ userInput: "Type", nextView: one, views: [zero], value: _ } <<< pure) :: Ixpr -> EditState
  , eval: case _ of
      Output a -> a <$ (H.gets _.value >>= extract >>> H.raise)
      Check a -> H.gets _.value <#> extract >>> a
      UserInput a userInput -> a <$ (prop (_S::S_ "userInput") .= userInput)
      EditAction mviewId a act -> a <$ case act of
        Set value -> prop (_S::S_ "value") %= Timeline.happen value
        Undo -> prop (_S::S_ "value") %= (fromMaybe <*> Timeline.unhappen)
        Redo -> prop (_S::S_ "value") %= (fromMaybe <*> Timeline.rehappen)
        DeleteView -> for_ mviewId \viewId ->
          prop (_S::S_ "views") %= Array.delete viewId
        NewView view -> do
          prop (_S::S_ "nextView") %= add one
          viewId <- H.gets _.nextView
          prop (_S::S_ "views") %= flip Array.snoc viewId
          void $ H.query (_S::S_ "view") viewId $ ViewInitialize unit view
  , render
  } where
    render :: EditState -> H.ComponentHTML EditQuery ( view :: H.Slot ViewQuery EditActions Natural ) Aff
    render { views, value, userInput } =
      let
        renderedViews = views <#> \viewId ->
          HH.slot (_S::S_ "view") viewId viewer
            { parsed, value: extract value }
            (Just <<< EditAction (Just viewId) unit)
        appendView = Just (EditAction Nothing unit (NewView empty))
        parsed = Ann.innote mempty <<< map Just <$> Dhall.Parser.parse userInput
      in HH.div [ HP.class_ (H.ClassName "expr-editor") ]
        [ HH.div_ renderedViews
        , HH.div_
          [ inline_feather_button_action appendView "plus-square" "Add a new view"
          , inline_feather_button_action (Timeline.unhappen value $> EditAction Nothing unit Undo) "corner-up-left" "Undo"
          , inline_feather_button_action (Timeline.rehappen value $> EditAction Nothing unit Redo) "corner-down-right" "Redo"
          ]
        , HH.textarea [ HE.onValueInput (Just <<< UserInput unit), HP.value userInput ]
        , Icons.icon (if isJust parsed then "check" else "x") [ Icons.class_ "feather" ]
        ]

_ixes_Ann :: forall m s a. TraversableWithIndex String m =>
  ExprI -> Traversal' (Ann.Expr m s a) (Ann.Expr m s a)
_ixes_Ann Nil = identity
_ixes_Ann (i : is) = _recurse <<< _Newtype <<< _2 <<< _ix (extract i) <<< _ixes_Ann is

viewer :: H.Component HH.HTML ViewQuery { parsed :: Maybe Ixpr, value :: Ixpr } EditActions Aff
viewer = H.component
  { initializer: Nothing
  , finalizer: Nothing
  , receiver: Just <<< Receive unit
  , initialState: \{ parsed, value } ->
    { parsed, value
    , view: empty
    , selection: pure empty
    } :: ViewState
  , eval: case _ of
      ViewInitialize a view -> a <$ do
        prop (_S::S_ "view") .= view
      Receive a { parsed, value } -> a <$ do
        prop (_S::S_ "parsed") .= parsed
        prop (_S::S_ "value") .= value
      Raise a edit -> a <$ H.raise edit
      ViewAction a acts -> a <$ for_ acts case _ of
        Select loc -> prop (_S::S_ "selection") .= loc
        Un_Focus up down -> do
          prop (_S::S_ "view") %= \view -> down <> List.drop up view
          -- TODO: adapt selection in a smart manner (common prefix)
          when (not List.null down) do prop (_S::S_ "selection") .= Nothing
        SetView patch -> do
          { value: old, view } <- H.get
          case Loc.allWithin view of
            Just loc' | loc <- map pure loc', L.has (_ixes_Ann loc) old ->
              let new = (_ixes_Ann loc .~ patch) old in
              when (new /= old) $ H.raise $ Set new
            _ -> pure unit
        SetSelection patch -> do
          { value: old, view, selection } <- H.get
          case Loc.allWithin view, selection of
            Just loc', Just sel | loc <- sel <> map pure loc', L.has (_ixes_Ann loc) old ->
              let new = (_ixes_Ann loc .~ patch) old in
              when (new /= old) $ H.raise $ Set new
            _, _ -> pure unit
  , render: renderInfo >>> render
  } where
    renderInfo :: ViewState -> ViewRender
    renderInfo st =
      let
        from = { ctx: Dhall.Context.empty, expr: Ann.denote st.value }
        steps = (Variant.expand <$> st.view)
        to = unWriterT $ locateE tpi steps from
        typeof = unWriterT <<< locateE tpi (pure (Variant.inj (_S::S_ "typecheck") {})) =<< to
        window = Ann.innote mempty <<< _.expr <$> to
      in
        { st, window
        , editable: isJust (Loc.allWithin st.view)
        , exists: any tt window
        , typechecks: any tt typeof
        }
    showError :: TypeCheckError (Errors ( "Not found" :: ExprRowVFI )) (L IOSM.InsOrdStrMap (Maybe Core.Imports.Import)) -> String
    showError = unsafeCoerce >>> _.tag >>> _.type
    render :: ViewRender -> HH.ComponentHTML ViewQuery () Aff
    render r = HH.div [ HP.class_ (H.ClassName "expr-viewer") ]
      [ HH.div [ HP.class_ (H.ClassName "header") ]
        [ inline_feather_button_action (Just (Raise unit DeleteView)) "x-square" "Close this view"
        , HH.text " "
        , renderLocation r.st.view <#> \i -> ViewAction unit [Un_Focus i empty]
        ]
      , HH.div [ HP.class_ (H.ClassName "edit-bar") ] $ guard (r.editable && isJust r.st.selection) $
        [ renderLocation (Variant.inj (_S::S_ "within") <<< extract <$> fold r.st.selection) <#> \i -> ViewAction unit []
        , inline_feather_button_action (Just (ViewAction unit [SetSelection (Ann.innote mempty $ pure Nothing)])) "trash-2" "Delete this node"
        , HH.text " "
        , inline_feather_button_action (r.st.parsed <#> ViewAction unit <<< pure <<< SetSelection) "edit-3" "Replace this node with parsed content"
        ]
      , case r.window of
          Success flowers -> un SlottedHTML $
            let
              opts = { interactive: true, editable: r.editable }
              selectHere = mkActions $ unwrap >>> extract >>> extract >>> \i ->
                let here = (Variant.inj (_S::S_ "within") <<< extract <$> i)
                    focus loc = Just \_ -> This $ Un_Focus zero loc
                in
                [ { icon: "at-sign"
                  , action: focus here
                  , tooltip: "Move view here"
                  }
                , { icon: "cpu"
                  , action: focus (Variant.inj (_S::S_ "normalize") {} : here)
                  , tooltip: "View this node, normalized"
                  }
                , { icon: "type"
                  , action: focus (Variant.inj (_S::S_ "typecheck") {} : here)
                  , tooltip: "View the type of this node"
                  }
                ]
            in
            renderExprWith opts
            (selectable opts { interactive = true } r.st.selection Select <> selectHere <> collapsible opts { interactive = false })
            flowers <#> ViewAction unit <<< bifoldMap pure (pure <<< SetView)
          Error errors' _ | errors <- NEA.toArray errors' ->
            HH.ul [ HP.class_ (H.ClassName "errors") ] $ errors <#>
              showError >>> HH.text >>> pure >>> HH.li_
      ]

renderLocation :: forall p. Location -> HH.HTML p Int
renderLocation loc = HH.span [ HP.class_ (H.ClassName "location") ] $
  intercalate [ HH.span [ HP.class_ (H.ClassName "breadcrumb-sep") ] [] ] $
    let len = List.length loc in
    (<|>) (pure $ pure $ inline_feather_button_action (Just len) "home" "Top of expression") $
    List.reverse loc # mapWithIndex \i -> pure <<<
      let act = Just (len - i - 1) in
      Variant.match
        { within: HH.button [ HE.onClick (pure act) ] <<< pure <<< renderERVFI
        , normalize: \_ -> inline_feather_button_action act "cpu" "Normalized"
        , typecheck: \_ -> inline_feather_button_action act "type" "Typechecked"
        }

renderERVFI :: forall p q. ExprRowVFI -> HH.HTML p q
renderERVFI ervfi = HH.span [ HP.class_ (H.ClassName "index") ]
  [ HH.span [ HP.class_ (H.ClassName "type") ] [ HH.text (unsafeCoerce ervfi)."type" ]
  , HH.text " "
  , HH.span [ HP.class_ (H.ClassName "tag") ] [ HH.text (tagERVFI ervfi) ]
  ]

tagERVFI :: ExprRowVFI -> String
tagERVFI = un ERVFI >>> Variant.match
  { "BoolLit": identity absurd
  , "NaturalLit": identity absurd
  , "IntegerLit": identity absurd
  , "DoubleLit": identity absurd
  , "Bool": identity absurd
  , "Natural": identity absurd
  , "Integer": identity absurd
  , "Double": identity absurd
  , "Text": identity absurd
  , "List": identity absurd
  , "Optional": identity absurd
  , "Const": identity absurd
  , "NaturalFold": identity absurd
  , "NaturalBuild": identity absurd
  , "NaturalIsZero": identity absurd
  , "NaturalEven": identity absurd
  , "NaturalOdd": identity absurd
  , "NaturalToInteger": identity absurd
  , "NaturalShow": identity absurd
  , "IntegerShow": identity absurd
  , "IntegerToDouble": identity absurd
  , "DoubleShow": identity absurd
  , "ListBuild": identity absurd
  , "ListFold": identity absurd
  , "ListLength": identity absurd
  , "ListHead": identity absurd
  , "ListLast": identity absurd
  , "ListIndexed": identity absurd
  , "ListReverse": identity absurd
  , "OptionalFold": identity absurd
  , "OptionalBuild": identity absurd
  , "TextLit": \i -> "interp@" <> show i
  , "ListLit":
      either (\(_ :: Unit) -> "type")
      \i -> "value@" <> show i
  , "OptionalLit":
      either (\(_ :: Unit) -> "type")
      \(_ :: Unit) -> "value"
  , "Some": \(_ :: Unit) -> "value"
  , "None": identity absurd
  , "RecordLit": \k -> "values@" <> show k
  , "UnionLit":
      either (\(_ :: Unit) -> "value")
      \k -> "types@" <> show k
  , "Record": \k -> "types@" <> show k
  , "Union": \k -> "types@" <> show k
  , "BoolAnd": binop
  , "BoolOr": binop
  , "BoolEQ": binop
  , "BoolNE": binop
  , "NaturalPlus": binop
  , "NaturalTimes": binop
  , "TextAppend": binop
  , "ListAppend": binop
  , "Combine": binop
  , "CombineTypes": binop
  , "Prefer": binop
  , "ImportAlt": binop
  , "BoolIf": case _ of
      Three1 -> "if"
      Three2 -> "then"
      Three3 -> "else"
  , "Field": \(_ :: Unit) -> "Field expr"
  , "Project": \(_ :: Unit) -> "Project expr"
  , "Merge": case _ of
      Three1 -> "handlers"
      Three2 -> "arg"
      Three3 -> "type"
  , "Constructors": \(_ :: Unit) -> "Constructors arg"
  , "App": if _ then "fn" else "arg"
  , "Annot": if _ then "value" else "type"
  , "Lam": if _ then "type" else "body"
  , "Pi": if _ then "type" else "body"
  , "Let": case _ of
      Three1 -> "type"
      Three2 -> "value"
      Three3 -> "body"
  , "Var": identity absurd
  , "Embed": identity absurd
  } where
    binop = if _ then "R" else "L"
