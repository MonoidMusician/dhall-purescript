module Dhall.Interactive.Halogen.AST.Tree.Editor where

import Dhall.Interactive.Halogen.AST.Tree (AnnExpr)
import Prelude (Void, bind, discard, flip, identity, map, pure, unit, void, zero, ($), (<#>), (<$), (<*>), (<<<), (<>), (>>=), (>>>))

import Control.Comonad (extract)
import Control.Plus (empty)
import Data.Array as Array
import Data.Lens (Traversal', _2, (%=), (.=), (.~))
import Data.Lens as L
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.List (List(..), (:))
import Data.List as List
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Natural (Natural, natToInt)
import Data.TraversableWithIndex (class TraversableWithIndex)
import Dhall.Core (S_, _S)
import Dhall.Core.AST (ExprI)
import Dhall.Core.AST.Noted as Ann
import Dhall.Core.AST.Operations.Location (Location)
import Dhall.Core.AST.Operations.Location as Loc
import Dhall.Core.Zippers (_ix)
import Dhall.Core.Zippers.Recursive (_recurse)
import Dhall.Interactive.Types as Core.Imports
import Dhall.Lib.Timeline (Timeline)
import Dhall.Lib.Timeline as Timeline
import Effect.Aff (Aff)
import Halogen as H
import Halogen.HTML as HH

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

type ViewState =
  { id :: ViewId
  , value :: Ixpr
  , view :: Location
  , selection :: Maybe ExprI
  }
type ViewRender =
  { st :: ViewState
  , editable :: Boolean
  , exists :: Boolean
  , typechecks :: Boolean
  }
data ViewActions
  = Select (Maybe ExprI)
  | Un_Focus Natural Location -- pop foci and move down to new location
  | SetSelection Ixpr -- set new Ixpr at selection
data ViewQuery a
  = ViewInitialize
    { id :: ViewId
    , view :: Location
    } a
  | ViewAction ViewActions a
  | Raise EditActions a
  | Receive Ixpr a

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
      ViewAction act a -> a <$ case act of
        Select loc -> prop (_S::S_ "selection") .= loc
        Un_Focus up down -> prop (_S::S_ "view") %= \view ->
          List.drop (natToInt up) view <> down
        SetSelection new -> do
          { value: old, view } <- H.get
          case Loc.allWithin view of
            Just loc' | loc <- map pure loc', L.has (_ixes_Ann loc) old ->
              H.raise $ Set $ (_ixes_Ann loc .~ new) old
            _ -> pure unit
  , render
  } where
    render _ = HH.div_ []
