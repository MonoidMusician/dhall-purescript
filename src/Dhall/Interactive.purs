module Dhall.Interactive where

import Prelude

import Complex.Validation.These as V
import Control.Monad.Writer (runWriterT)
import Data.Array as Array
import Data.Bifunctor (bimap)
import Data.Either (Either(..))
import Data.Lens (review)
import Data.Maybe (Maybe(..), isNothing)
import Data.Newtype (unwrap)
import Data.String (joinWith)
import Data.Tuple (fst)
import Dhall.Context as Dhall.Context
import Dhall.Core ((~))
import Dhall.Core as Core
import Dhall.Core as Dhall.Core
import Dhall.Core.AST as AST
import Dhall.Core.Imports as Core.Imports
import Dhall.Core.StrMapIsh as IOSM
import Dhall.Interactive.Halogen.AST.Tree (renderExpr)
import Dhall.Interactive.Halogen.Types (DataComponent, InOut(..))
import Dhall.Parser (parse)
import Dhall.TypeCheck (typeWithA)
import Dhall.TypeCheck as TypeCheck
import Effect (Effect)
import Effect.Aff (Aff)
import Halogen as H
import Halogen.Aff as HA
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.VDom.Driver (runUI)
import Unsafe.Coerce (unsafeCoerce)

parserC :: DataComponent (Either String (AST.Expr IOSM.InsOrdStrMap Core.Imports.Import)) Aff
parserC = H.component
  { initializer: Nothing
  , finalizer: Nothing
  , receiver: Just <<< In unit
  , initialState: identity
  , eval: case _ of
      In a v -> a <$ H.put v
      Out a v -> a <$ H.put v <* H.raise v
  , render
  }
  where
    render = case _ of
      Left s -> HH.div_
        let
          parsed = parse s
          showError :: TypeCheck.TypeCheckError (TypeCheck.Errors () IOSM.InsOrdStrMap Core.Imports.Import) IOSM.InsOrdStrMap Core.Imports.Import -> String
          showError = unsafeCoerce >>> _.tag >>> _.type
          ctx = Dhall.Context.empty # Dhall.Context.insert "Test/equal" do
            AST.mkPi "a" AST.mkType (AST.mkPi "_" (AST.mkVar (AST.V "a" 0)) (AST.mkPi "_" (AST.mkVar (AST.V "a" 0)) AST.mkBool))
          typechecked = bimap showError fst <<< runWriterT <<< typeWithA (\_ -> AST.mkType) ctx =<< V.note "Parse fail" parsed
          shown = case typechecked of
            V.Error es _ -> (<>) "Errors: " $
              joinWith "; " <<< Array.fromFoldable $
                map (joinWith ", " <<< Array.fromFoldable) es
            V.Success a -> "Success: " <> show a
          normalized :: Maybe (AST.Expr IOSM.InsOrdStrMap Core.Imports.Import)
          normalized = case typechecked of
            V.Success _ ->
              -- Funny thing: the `normalizer` does not obey any laws of normalization
              -- because it inspects its arguments too much, takes them verbatim
              -- and wholly consumes them ... due to a bug in my implementation
              -- this means that it would see unnormalized terms, when let/lambda
              -- bound variables are involved (since the normalization happens
              -- bottom-to-top, and then the let/lambda bindings are renormalized
              -- after substitution). So, to circumvent this, the normalizer is run
              -- only after the regular normalization (and substituion) has happened.
              Dhall.Core.normalizeWith normalizator <<< Dhall.Core.normalize <$> parsed
            _ -> Nothing
          normalizator :: Dhall.Core.Normalizer IOSM.InsOrdStrMap Core.Imports.Import
          normalizator = Dhall.Core.Normalizer normalizer
          normalizer ::
            Dhall.Core.Apps IOSM.InsOrdStrMap Core.Imports.Import ->
            Maybe (Unit -> AST.Expr IOSM.InsOrdStrMap Core.Imports.Import)
          normalizer (testequal~_~x~y)
            | Just (AST.V "Test/equal" 0) <- Core.noapplit AST._Var testequal
            , x' <- review Core.apps x
            , y' <- review Core.apps y
            , Core.judgmentallyEqual x' y' =
              Just \_ -> AST.mkBoolLit (Core.judgmentallyEqual x' y')
          normalizer _ =
              Nothing
        in
        [ HH.div [ HP.class_ $ H.ClassName "code" ]
          [ HH.div_ [ HH.textarea [ HE.onValueInput (Just <<< Out unit <<< Left), HP.value s ] ]
          , HH.div_ [ HH.text (show parsed) ]
          , HH.div_ [ HH.text shown ]
          , HH.div_ [ HH.text "Normalized: ", HH.text (show normalized) ]
          , HH.div_ [ HH.text "abNormalized: ", HH.text (show (Dhall.Core.alphaNormalize <$> normalized)) ]
          ]
        , HH.div_
          [ HH.button
            [ HP.disabled (isNothing parsed)
            , HE.onClick (\_ -> Out unit <<< Right <$> parsed)
            ] [ HH.text "Click here to render and interact with it!" ]
          ]
        ]
      Right expr ->
        HH.div_
        [ HH.div [ HP.class_ $ H.ClassName "code" ]
          [ unwrap <<< map (Out unit <<< Right) <<< renderExpr $ expr ]
        , HH.div_
          [ HH.button [ HE.onClick (pure (pure (Out unit (Left "")))) ] [ HH.text "Click here to enter another expression to parse" ]
          ]
        ]

main :: Effect Unit
main = HA.runHalogenAff do
  body <- HA.awaitBody
  -- driver <- runUI interactive unit body
  driver3 <- runUI parserC (Left "Type") body
  pure unit
