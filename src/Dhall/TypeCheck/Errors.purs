module Dhall.TypeCheck.Errors where

import Prelude

import Control.Plus (empty)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldMap, null)
import Data.FoldableWithIndex (anyWithIndex, foldMapWithIndex)
import Data.Functor.Variant (SProxy, VariantF)
import Data.Functor.Variant as VariantF
import Data.Lens (firstOf, has, lastOf)
import Data.Lens.Indexed (asIndex, itraversed)
import Data.List.Types (NonEmptyList)
import Data.Maybe (Maybe(..))
import Data.Monoid.Endo (Endo(..))
import Data.Natural (Natural)
import Data.String as String
import Data.Symbol (class IsSymbol)
import Data.Tuple (Tuple(..))
import Data.Variant (Variant)
import Data.Variant as Variant
import Dhall.Core.AST (Var(..), Const, Expr, ExprRowVF(..), ExprRowVFI(..), S_, _S, rehydrate)
import Dhall.Core.AST as AST
import Dhall.Core.AST.Operations.Location as Loc
import Dhall.Imports.Retrieve (headerType)
import Dhall.Core.Zippers (_ix)
import Dhall.Map (class MapLike)
import Dhall.Map as Dhall.Map
import Type.Row as R

import Dhall.TypeCheck.Types (BiContext, Errors)

data Reference a
  = Text String
  | Br
  | Reference a
  | List (Array (Reference a))
  | Compare String a String a
  | Href String String
  -- | NodeType String
derive instance functorReference :: Functor Reference

-- The explanation, given as text interspersed with specific places to look at
-- (for the user to read)
explain ::
  forall r m a.
    MapLike String m =>
  BiContext Unit ->
  VariantF (AST.ExprLayerRow m a) Unit ->
  Variant (Errors r) ->
  Array (Reference (Loc.BasedExprDerivation m a))
explain ctx nodeType =
  let errorUnknownError = [ Text "Unexplained error" ]
      within ::
        forall sym v r'.
          IsSymbol sym =>
          R.Cons sym v r' AST.ExprLayerRowI =>
        SProxy sym -> v -> Endo (->) (Loc.BasedExprDerivation m a)
      within sym v = within' (ERVFI (Variant.inj sym v))
      within' :: ExprRowVFI -> Endo (->) (Loc.BasedExprDerivation m a)
      within' ervfi = Endo $ Loc.moveF (_S::S_ "within") ervfi
      typechecked :: Endo (->) (Loc.BasedExprDerivation m a)
      typechecked = Endo $ Loc.stepF (_S::S_ "typecheck")
      normalized :: Endo (->) (Loc.BasedExprDerivation m a)
      normalized = Endo $ Loc.stepF (_S::S_ "normalize")
      expr :: Expr m Void -> Loc.BasedExprDerivation m a
      expr e = Tuple empty $ pure $ absurd <$> e
      referenceExpr :: Expr m Void -> Reference (Loc.BasedExprDerivation m a)
      referenceExpr e = Reference (expr e)
      referenceConst :: AST.Const -> Reference (Loc.BasedExprDerivation m a)
      referenceConst = referenceExpr <<< AST.mkConst
      reference :: Endo (->) (Loc.BasedExprDerivation m a) -> Reference (Loc.BasedExprDerivation m a)
      reference = Reference <<< dereference
      dereference :: Endo (->) (Loc.BasedExprDerivation m a) -> Loc.BasedExprDerivation m a
      dereference (Endo localize) = localize (Tuple empty Nothing)
      compare :: String -> Endo (->) (Loc.BasedExprDerivation m a) -> String -> Endo (->) (Loc.BasedExprDerivation m a) -> Reference (Loc.BasedExprDerivation m a)
      compare s1 l1 s2 l2 = Compare s1 (dereference l1) s2 (dereference l2)
      here = reference mempty

      notAType desc loc =
        [ Text $ "The " <> (if String.null desc then "" else desc <> " ") <> " type "
        , reference loc
        , Text " is required to be a type in some universe, e.g. "
        , referenceExpr AST.mkType
        , Text " but instead had type "
        , reference (typechecked <> loc)
        ]
  in
  Variant.default errorUnknownError #
  Variant.onMatch
  { "`Sort` has no type": \(_ :: Unit) ->
    [ Text "Sort is the top universe of types and therefore it has no type itself" ]
  , "Not a function": \(_ :: Unit) ->
      [ Text $ "The left side of a function application node must be a function "
      , Text $ "(i.e. a term whose type is a Pi type)"
      , Text $ " but instead it had type "
      , reference $ typechecked <> within (_S::S_ "App") false
      ]
  , "Type mismatch": \(_ :: Unit) ->
      [ compare
          "The function takes values in type "
          (  within (_S::S_ "Pi") false
          <> normalized <> typechecked
          <> within (_S::S_ "App") false
          ) " but was instead given a value of type "
          (  normalized
          <> typechecked
          <> within (_S::S_ "App") true
          )
      ]
  , "Invalid predicate": \(_ :: Unit) ->
      [ Text $ "If-then-else expressions take predicates whose type is "
      , referenceExpr AST.mkBool
      , Text $ " but the predicate had this type instead "
      , reference $ typechecked <> within (_S::S_ "BoolIf") AST.Three1
      ]
  , "If branch mismatch": \(_ :: Unit) ->
      [ Text $ "If expressions must have the same type in the `then` branch as the `else` branch, "
      , compare
          " but the former was "
          (typechecked <> within (_S::S_ "BoolIf") AST.Three2)
          " and the latter was "
          (typechecked <> within (_S::S_ "BoolIf") AST.Three3)
      ]
  , "If branch must be term": \side ->
      let focus = within (_S::S_ "BoolIf") if side then AST.Three3 else AST.Three2 in
      [ Text $ "If-then-else expressions must return a term"
      , Text $ " but the expression had type "
      , reference $ typechecked <> focus
      , Text $ " which is not in a type universe, but instead had type "
      , reference $ typechecked <> typechecked <> focus
      ]
  -- TODO: needs work
  , "Invalid list type": \(mc :: Maybe Const) ->
      let
        annot = ERVFI (Variant.inj (_S::S_ "ListLit") (Left unit))
        focus = if has (_ix annot) (ERVF nodeType) then within' annot else
          typechecked <> within (_S::S_ "ListLit") (Right zero)
      in
      [ Text $ "A list should contain elements in the universe "
      , referenceExpr AST.mkType
      , Text $ " but this is not "
      , reference (typechecked <> focus)
      ]
  , "Missing list type": \(_ :: Unit) ->
      [ Text "Empty list literals must be annotated with the type of their elements" ]
  , "Invalid list element": \i ->
      [ Text $ "The list was annotated to have type "
      , reference $ within (_S::S_ "ListLit") (Left unit)
      , Text $ " but the element at index "
      , Text $ show i
      , Text $ " had type "
      , reference $ typechecked <> within (_S::S_ "ListLit") (Right i)
      ]
  -- TODO: needs work
  , "Mismatched list elements": \i ->
      [ Text $ "The list was assumed to have type "
      , reference $ typechecked <> within (_S::S_ "ListLit") (Right zero)
      , Text $ " but the element at index "
      , Text $ show i
      , Text $ " had type "
      , reference $ typechecked <> within (_S::S_ "ListLit") (Right i)
      ]
  , "Cannot append non-list": \(side :: Boolean) ->
      let focus = within (_S::S_ "ListAppend") side in
      [ Text $ "Appending lists requires the operands to be lists"
      , Text $ " but the " <> (if side then "right" else "left") <> " side instead had type "
      , reference $ normalized <> typechecked <> focus
      ]
  , "Cannot interpolate": \(i :: Natural) ->
      let focus = within (_S::S_ "TextLit") i in
      [ Text $ "Expressions interpolated into a text literal must have type "
      , referenceExpr AST.mkText
      , Text $ " but this instead had type "
      , reference $ typechecked <> focus
      ]
  , "List append mismatch": \(_ :: Unit) ->
      let
        elType side =
          within (_S::S_ "App") true <>
          normalized <> typechecked <>
          within (_S::S_ "ListAppend") side
      in
      [ Text $ "Appending lists requires the operands to be lists of equal types"
      , Text $ " but the left side has elements of type "
      , reference $ elType false
      , Text $ " while the right has elements of type "
      , reference $ elType true
      ]
  , "List annotation must be list type": \(_ :: Unit) ->
      [ Text $ "Lists must be annotated with a type that starts with `List`, but this one was annotated with "
      , reference $ within (_S::S_ "ListLit") (Left unit)
      ]
  , "Invalid `Some`": \(mc :: Maybe Const) ->
      let focus = within (_S::S_ "Some") unit in
      [ Text $ "A optional literal must contain a term but Some was given an expression "
      , reference $ focus
      , Text $ " of type "
      , reference $ typechecked <> focus
      ] <> case mc of
        Nothing ->
          [ Text $ " which is not in a type universe, but instead had type "
          , reference $ typechecked <> typechecked <> focus
          ]
        Just c ->
          [ Compare
              " which was in universe "
              (expr (AST.mkConst c))
              " instead of "
              (expr (AST.mkConst AST.Type))
          ]
  , "Duplicate record fields": \(keys :: NonEmptyList String) ->
      [ Text $ "The following names of fields occurred more than once in a Record (type): "
      , List $ Text <$> Array.fromFoldable keys
      ]
  , "Invalid field type": \name ->
      let
        focus = nodeType # VariantF.on (_S::S_ "RecordLit")
          do \_ -> typechecked <> within (_S::S_ "RecordLit") name
          -- NOTE: assume it is a Record type, if it's not a RecordLit
          do \_ -> within (_S::S_ "Record") name
      in
      [ Text $ "Record field types must live in a universe, but "
      , Text $ "`" <> name <> "` "
      , reference $ focus
      , Text $ " instead had type "
      , reference $ typechecked <> focus
      ]
  -- TODO
  , "Inconsistent alternative types": \keys ->
      let
        focus name = within (_S::S_ "Union") (Tuple name unit)
      in
      [ Text $ "Union alternative types must all live in the same universe, but these did not "
      , List $ Text <<< show <$> Array.fromFoldable keys
      ]
  , "Duplicate union alternatives": \(keys :: NonEmptyList String) ->
      [ Text $ "The following names of alternatives occurred more than once in a Union (type): "
      , List $ Text <$> Array.fromFoldable keys
      ]
  , "Invalid alternative type": \name ->
      let
        focus = within (_S::S_ "Union") (Tuple name unit)
      in
      [ Text $ "Union alternative types must live in a universe, but "
      , Text $ "`" <> name <> "` "
      , reference $ focus
      , Text $ " instead had type "
      , reference $ typechecked <> focus
      ]
  -- TODO
  , "Must combine a record": \(Tuple path side) ->
      let
        focus name = within (_S::S_ "Union") (Tuple name unit)
      in
      [
      ]
  , "Must merge a record": \(_ :: Unit) ->
      [ Text $ "Using the `merge` operator requires a record as the first argument, but this had type "
      , reference $ normalized <> typechecked <> within (_S::S_ "Merge") AST.Three1
      ]
  , "Must merge a union": \(_ :: Unit) ->
      [ Text $ "Using the `merge` operator requires a union as the second argument, but this had type "
      , reference $ normalized <> typechecked <> within (_S::S_ "Merge") AST.Three1
      ]
  -- TODO
  , "Missing handler": \names ->
    [ Text $ "Handlers for the `merge` operator "
    , Text $ "`" <> show names <> "` "
    ]
  , "Unused handlers": \names ->
    [ Text $ "Handlers for the `merge` operator "
    , Text $ "`" <> show names <> "` "
    ]
  , "Handler not a function": \name ->
      [ Text $ "Handlers for the `merge` operator "
      , Text $ "`" <> name <> "` "
      ]
  , "Dependent handler function": \name ->
      [ Text $ "Handlers for the `merge` operator "
      , Text $ "`" <> name <> "` "
      ]
  , "Handler input type mismatch": \name ->
      [ Text $ "Handlers for the `merge` operator "
      , Text $ "`" <> name <> "` "
      ]
  , "Handler output type mismatch": \(Tuple fromAnnot name) ->
      let
        assumed = case fromAnnot of
          Nothing -> within (_S::S_ "Merge") AST.Three3
          Just { key, fn } ->
            (if fn then within (_S::S_ "Pi") true else mempty) <>
            within (_S::S_ "Record") key <>
            normalized <> typechecked <> within (_S::S_ "Merge") AST.Three1
      in
      [ Text $ "The handler for the `merge` operator "
      , Text $ "`" <> name <> "` "
      , compare
          " was expected to have type "
          assumed
          " but instead had type "
          (within (_S::S_ "Pi") true <> within (_S::S_ "Record") name <>
          normalized <> typechecked <> within (_S::S_ "Merge") AST.Three1)
      ]
  , "Handler type mismatch": \(Tuple fromAnnot name) ->
      let
        assumed = case fromAnnot of
          Nothing -> within (_S::S_ "Merge") AST.Three3
          Just { key, fn } ->
            (if fn then within (_S::S_ "Pi") true else mempty) <>
            within (_S::S_ "Record") key <>
            normalized <> typechecked <> within (_S::S_ "Merge") AST.Three1
      in
      [ Text $ "The handler for the `merge` operator case "
      , Text $ "`" <> name <> "` "
      , compare
          " was expected to have type "
          assumed
          " but instead had type "
          (within (_S::S_ "Record") name <>
          normalized <> typechecked <> within (_S::S_ "Merge") AST.Three1)
      ]
  , "Cannot project": \(_ :: Unit) ->
      [ Text $ "The projection operation can only be used on records, but the expression had type "
      , reference $ typechecked <> within (_S::S_ "Project") (Left unit)
      ]
  , "Cannot project by expression": \(_ :: Unit) ->
      [ Text $ "The project-by-expression operation can only take a record type, but this was not a record type "
      , reference $ normalized <> within (_S::S_ "Project") (Right unit)
      ]
  , "Projection type mismatch": \key ->
      [ Text $ "The field "
      , Text $ "`" <> key <> "`"
      , compare
          " should match its type in the  "
          (within (_S::S_ "Record") key <> normalized <> within (_S::S_ "Project") (Right unit))
          " but instead had type "
          (within (_S::S_ "Record") key <> normalized <> typechecked <> within (_S::S_ "Project") (Left unit))
      ]
  , "Missing field": \key ->
      let
        focus = nodeType # VariantF.on (_S::S_ "Field")
          do \_ -> within (_S::S_ "Field") unit
          do \_ -> within (_S::S_ "Project") (Left unit)
      in
      [ Text $ "The field "
      , Text $ "`" <> key <> "`"
      , Text $ " was missing from "
      , reference $ within (_S::S_ "Record") key <> normalized <> typechecked <> focus
      ]
  , "Cannot access": \(_ :: Unit) ->
      [ Text $ "The field accessor only works on records and union types, but this instead had type "
      , reference $ normalized <> typechecked <> within (_S::S_ "Field") unit
      ]
  , "toMap takes a record": \(_ :: Unit) ->
      [ Text $ "The `toMap` operation can only take a record, but this instead had type "
      , reference $ normalized <> typechecked <> within (_S::S_ "ToMap") (Left unit)
      ]
  , "Invalid toMap type annotation": \(_ :: Unit) ->
      [ Text $ "The `toMap` operation should have a type annotation that looks like "
      , referenceExpr $ AST.mkApp AST.mkList $ AST.mkRecord $ Dhall.Map.fromFoldable
        [ Tuple "mapKey" AST.mkText
        , Tuple "mapValue" (AST.mkVar (V "_" 0))
        ]
      , Text $ " but instead it was "
      , reference $ normalized <> within (_S::S_ "ToMap") (Right unit)
      ]
  -- TODO
  , "Invalid completion type": \mc ->
      [ Text $ "TODO"
      ]
  -- TODO
  , "Invalid toMap type": \mc ->
      [ Text $ "The `toMap` operation should contain elements in the universe "
      , referenceExpr $ AST.mkType
      , Text $ " but instead the inferred type "
      ] <> case mc of
        Nothing ->
          [ Text $ " was not in a type universe"
          -- , but instead had type "
          -- , reference $ typechecked <> typechecked <> focus
          ]
        Just c ->
          [ Compare
              " which was in universe "
              (expr (AST.mkConst c))
              " instead of "
              (expr (AST.mkConst AST.Type))
          ]
  , "Missing toMap type": \(_ :: Unit) ->
      [ Text $ "The `toMap` operation, when its record is empty, must be annotated with a result type that looks like "
      , referenceExpr $ AST.mkApp AST.mkList $ AST.mkRecord $ Dhall.Map.fromFoldable
        [ Tuple "mapKey" AST.mkText
        , Tuple "mapValue" (AST.mkVar (V "_" 0))
        ]
      ]
  -- TODO
  , "Inconsistent toMap types": \keys ->
      [ Text $ "The `toMap` operation must have fields all of one type "
      , List $ Text <<< show <$> Array.fromFoldable keys
      ]
  , "Invalid input type": \(_ :: Unit) ->
      let
        ty = nodeType # VariantF.on (_S::S_ "Lam")
          do \_ -> within (_S::S_ "Lam") false
          -- NOTE: assume it is a Pi type, if it's not a Lam
          do \_ -> within (_S::S_ "Pi") false
      in
      notAType "input" ty
  , "Invalid output type": \(_ :: Unit) ->
      let
        ty_body = nodeType # VariantF.on (_S::S_ "Lam")
          do \_ -> typechecked <> within (_S::S_ "Lam") true
          -- NOTE: assume it is a Pi type, if it's not a Lam
          do \_ -> (within (_S::S_ "Pi") true)
      in
      notAType "output" ty_body
  , "Unbound variable": \(AST.V name idx) ->
      let
        scope =
          if null ctx then [ Text "The context was empty." ] else
          [ Text $ "The variables in scope, from most local to most global, are: "
          , List $ ctx # foldMapWithIndex \v' _ -> pure $
              referenceExpr $ AST.mkVar v'
          ]
      in (_ <> scope) $
      if not anyWithIndex (\(AST.V name' _) _ -> name == name') ctx
      then
      [ Text $ "There were no variables with name "
      , Text $ show name
      , Text $ " bound in scope. "
      ]
      else
      [ Text $ "The scope does not contain the variable "
      , Text $ show name
      , Text $ " at index "
      , Text $ show idx
      , Text $ ". "
      ]
  , "Annotation mismatch": \(_ :: Unit) ->
      let
        { value, ty } = nodeType # VariantF.on (_S::S_ "Let")
          do \_ ->
              { value: within (_S::S_ "Let") AST.Three2
              , ty: within (_S::S_ "Let") AST.Three1
              }
          -- NOTE: assume it is an Annot node, if not a Let
          do \_ ->
              { value: within (_S::S_ "Annot") false
              , ty: within (_S::S_ "Annot") true
              }
      in
      [ Text $ "The value "
      , reference value
      , compare
          " was annotated to have type "
          ty
          " but instead had type "
          (typechecked <> value)
      ]
  , "Unexpected type": \(Tuple side ty) ->
      ( if side
          then lastOf  (asIndex itraversed) (ERVF nodeType)
          else firstOf (asIndex itraversed) (ERVF nodeType)
      ) # foldMap \focus ->
      [ Text $ "The binary operator was expected to have operands of type "
      , referenceExpr $ rehydrate ty
      , Text $ " but instead its " <> (if side then "right" else "left") <> " operand had type "
      , reference $ typechecked <> within' focus
      ]
  , "Wrong header type": \(_ :: Unit) ->
      [ Compare
          "Headers are expected to have type "
          (expr headerType)
          " but this instead had type "
          (dereference $ typechecked <> within (_S::S_ "UsingHeaders") true)
      ]
  }
