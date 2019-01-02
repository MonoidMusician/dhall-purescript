module Dhall.Interactive.Halogen.AST.Tree.Editor where

import Prelude

import Control.Comonad (extract)
import Control.Monad.Writer (WriterT, runWriterT)
import Control.Plus (empty)
import Data.Array (any, intercalate)
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
import Data.Natural (Natural)
import Data.Newtype (un)
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
import Dhall.Core.StrMapIsh as IOSM
import Dhall.Core.Zippers (_ix)
import Dhall.Core.Zippers.Recursive (_recurse)
import Dhall.Interactive.Halogen.AST (SlottedHTML(..))
import Dhall.Interactive.Halogen.AST.Tree (AnnExpr, renderExprSelectable)
import Dhall.Interactive.Halogen.Inputs (inline_feather_button_action)
import Dhall.Interactive.Types as Core.Imports
import Dhall.Lib.Timeline (Timeline)
import Dhall.Lib.Timeline as Timeline
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
  -- , highlights :: Array { variety :: HighlightVariety, pos :: Derivation }
  }
type ViewId = Natural
data GlobalActions = NoGlobalActions Void
data EditActions
  = Set Ixpr -- lowest common denominator: unsatisfactory, but works
  | Undo
  | Redo
  | NewView Location
  | DeleteView ViewId
data EditQuery a
  = EditAction EditActions a
  | Output a -- output Ixpr to parent
  | Check (Ixpr -> a) -- check its current value

type ERROR = Erroring (TypeCheckError (Errors + ( "Not found" :: ExprRowVFI )) (L IOSM.InsOrdStrMap (Maybe Core.Imports.Import)))
type ViewState =
  { id :: ViewId
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
  = ViewInitialize
    { id :: ViewId
    , view :: Location
    } a
  | ViewAction (Array ViewActions) a
  | Raise EditActions a
  | Receive Ixpr a

tpi :: Maybe Core.Imports.Import -> AST.Expr IOSM.InsOrdStrMap (Maybe Core.Imports.Import)
tpi _ = pure Nothing

unWriterT :: forall m f a. Functor f => WriterT m f a -> f a
unWriterT = runWriterT >>> map fst

editor :: H.Component HH.HTML EditQuery Ixpr Ixpr Aff
editor = H.component
  { initializer: Nothing
  , finalizer: Nothing
  , receiver: Just <<< flip EditAction unit <<< Set
  , initialState: ({ nextView: zero, views: empty, value: _ } <<< pure) :: Ixpr -> EditState
  , eval: case _ of
      Output a -> a <$ (H.gets _.value >>= extract >>> H.raise)
      Check a -> H.gets _.value <#> extract >>> a
      EditAction act a -> a <$ case act of
        Set value -> prop (_S::S_ "value") %= Timeline.happen value
        Undo -> prop (_S::S_ "value") %= (fromMaybe <*> Timeline.unhappen)
        Redo -> prop (_S::S_ "value") %= (fromMaybe <*> Timeline.rehappen)
        DeleteView viewId -> prop (_S::S_ "views") %= Array.delete viewId
        NewView view -> do
          viewId <- H.gets _.nextView
          prop (_S::S_ "views") %= flip Array.snoc viewId
          void $ H.query (_S::S_ "view") viewId $ ViewInitialize
            { id: viewId, view } unit
  , render
  } where
    render :: EditState -> H.ComponentHTML EditQuery ( view :: H.Slot ViewQuery EditActions Natural ) Aff
    render { views, value } = HH.div_ $ views <#> \viewId ->
      HH.slot (_S::S_ "view") viewId viewer (extract value)
        (Just <<< flip EditAction unit)

_ixes_Ann :: forall m s a. TraversableWithIndex String m =>
  ExprI -> Traversal' (Ann.Expr m s a) (Ann.Expr m s a)
_ixes_Ann Nil = identity
_ixes_Ann (i : is) = _recurse <<< _Newtype <<< _2 <<< _ix (extract i) <<< _ixes_Ann is

viewer :: H.Component HH.HTML ViewQuery Ixpr EditActions Aff
viewer = H.component
  { initializer: Nothing
  , finalizer: Nothing
  , receiver: pure Nothing
  , initialState:
    { id: zero
    , value: _
    , view: empty
    , selection: empty
    } :: Ixpr -> ViewState
  , eval: case _ of
      ViewInitialize { id, view } a -> a <$ do
        prop (_S::S_ "id") .= id
        prop (_S::S_ "view") .= view
      Receive value a -> a <$ do prop (_S::S_ "value") .= value
      Raise edit a -> a <$ H.raise edit
      ViewAction acts a -> a <$ for_ acts case _ of
        Select loc -> prop (_S::S_ "selection") .= loc
        Un_Focus up down -> prop (_S::S_ "view") %= \view ->
          List.drop up view <> down
        SetView new -> do
          { value: old, view } <- H.get
          case Loc.allWithin view of
            Just loc' | loc <- map pure loc', L.has (_ixes_Ann loc) old ->
              H.raise $ Set $ (_ixes_Ann loc .~ new) old
            _ -> pure unit
        SetSelection new -> do
          { value: old, view, selection } <- H.get
          case Loc.allWithin view, selection of
            Just loc', Just sel | loc <- sel <> map pure loc', L.has (_ixes_Ann loc) old ->
              H.raise $ Set $ (_ixes_Ann loc .~ new) old
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
      [ renderLocation r.st.view <#> \i -> ViewAction [Un_Focus i empty] unit
      , case r.window of
          Success flowers -> un SlottedHTML $
            renderExprSelectable
            { interactive: tt, editable: r.editable }
            r.st.selection
            flowers <#> flip ViewAction unit <<< bifoldMap
              (pure <<< Select)
              (pure <<< SetView)
          Error errors' _ | errors <- NEA.toArray errors' ->
            HH.ul [ HP.class_ (H.ClassName "errors") ] $ errors <#>
              showError >>> HH.text >>> pure >>> HH.li_
      ]

renderLocation :: forall p. Location -> HH.HTML p Int
renderLocation loc = HH.div [ HP.class_ (H.ClassName "location") ] $
  intercalate [ HH.span [ HP.class_ (H.ClassName "breadcrumb") ] [] ] $
    List.reverse loc # mapWithIndex \i -> pure <<<
      let act = Just i in
      Variant.match
        { within: HH.button [ HE.onClick (pure act) ] <<< pure <<< renderERVFI
        , normalize: \_ -> inline_feather_button_action act "cpu"
        , typecheck: \_ -> inline_feather_button_action act "type"
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
    binop = if _ then "L" else "R"
