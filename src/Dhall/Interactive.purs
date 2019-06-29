module Dhall.Interactive where

import Prelude

import Data.Maybe (Maybe(..))
import Dhall.Core (S_, _S)
import Dhall.Core.AST.Noted as Ann
import Dhall.Interactive.Halogen.AST.Tree.Editor (EditQuery, Ixpr, editor)
import Dhall.Interactive.Halogen.Types (DataComponent, InOut(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Halogen as H
import Halogen.Aff as HA
import Halogen.HTML as HH
import Halogen.VDom.Driver (runUI)

parserC :: DataComponent Ixpr Aff
parserC = H.mkComponent
  { initialState: identity
  , eval: H.mkEval $ H.defaultEval
      { handleAction = eval, handleQuery = map pure <<< eval, receive = Just <<< In unit }
  , render
  }
  where
    eval :: _ ~> _
    eval = case _ of
      In a v -> a <$ H.put v
      Out a v -> a <$ H.put v <* H.raise v
    render :: Ixpr -> H.ComponentHTML (InOut Ixpr Unit)
      ( editor :: H.Slot EditQuery Ixpr Unit ) Aff
    render = HH.slot (_S::S_ "editor") unit editor <@> Just <<< Out unit

main :: Effect Unit
main = HA.runHalogenAff do
  body <- HA.awaitBody
  driver3 <- runUI parserC (Ann.innote mempty $ pure Nothing) body
  pure unit
