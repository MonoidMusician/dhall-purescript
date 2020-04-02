module Pontifex where

import Prelude

import Control.Alt (class Alt, (<|>))
import Control.Lazy (fix)
import Control.Monad.Free (Free)
import Control.Monad.Free as Free
import Control.Monad.State (StateT(..), modify_)
import Control.Plus (empty)
import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.Const (Const)
import Data.Either (Either(..), either)
import Data.Eq (class Eq1)
import Data.Foldable as F
import Data.FunctorWithIndex (class FunctorWithIndex, mapWithIndex)
import Data.Lens (ALens', Lens', cloneLens, set, view)
import Data.Lens.Record (prop)
import Data.List (List(..), (:))
import Data.List as List
import Data.List.NonEmpty as NEL
import Data.List.Types (NonEmptyList)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Natural (Natural)
import Data.Newtype (over, unwrap)
import Data.Ord (class Ord1)
import Data.Set (Set)
import Data.Set as Set
import Data.String (drop, dropWhile, fromCodePointArray, length, null, take, takeWhile, toLower, toUpper)
import Data.Traversable as TF
import Data.Tuple (Tuple(..), snd)
import Dhall.Core (Pair(..), S_, _S)
import Dhall.Core.AST.Types.Basics (PairI)
import Effect (Effect)
import Effect.Aff (Aff)
import Halogen as H
import Halogen.Aff as HA
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.VDom.DOM.Prop as Prop
import Halogen.VDom.Driver as VD
import Matryoshka (cata)
import Matryoshka.Pattern.CoEnvT (CoEnvT(..))

cls :: forall r i. String -> HH.IProp ( class :: String | r ) i
cls = HP.class_ <<< H.ClassName
spanned :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
spanned = HH.span <<< pure <<< cls
spannedp :: forall w i. String -> HH.HTML w i -> HH.HTML w i
spannedp c = spanned c <<< pure
spannedpt :: forall w i. String -> String -> HH.HTML w i
spannedpt c = spannedp c <<< HH.text
pspanned :: forall w i. String -> Array (HH.HTML w i) -> Array (HH.HTML w i)
pspanned c = pure <<< spanned c
pspannedp :: forall w i. String -> HH.HTML w i -> Array (HH.HTML w i)
pspannedp c = pure <<< spannedp c
pspannedpt :: forall w i. String -> String -> Array (HH.HTML w i)
pspannedpt c = pure <<< spannedpt c
espanned :: forall w i. String -> i -> Array (HH.HTML w i) -> HH.HTML w i
espanned c i = HH.span [ cls c, HE.onClick (pure (pure i)) ]
espannedp :: forall w i. String -> i -> HH.HTML w i -> HH.HTML w i
espannedp c i = espanned c i <<< pure
espannedpt :: forall w i. String -> i -> String -> HH.HTML w i
espannedpt c i = espannedp c i <<< HH.text
epspanned :: forall w i. String -> i -> Array (HH.HTML w i) -> Array (HH.HTML w i)
epspanned c i = pure <<< espanned c i
epspannedp :: forall w i. String -> i -> HH.HTML w i -> Array (HH.HTML w i)
epspannedp c i = pure <<< espannedp c i
epspannedpt :: forall w i. String -> i -> String -> Array (HH.HTML w i)
epspannedpt c i = pure <<< espannedpt c i
silence :: forall w i j. HH.HTML w i -> HH.HTML w j
silence = over HH.HTML $ lmap $ map case _ of
  Prop.Attribute ns s v -> Prop.Attribute ns s v
  Prop.Property s v -> Prop.Property s v
  Prop.Handler s _ -> Prop.Handler s (const Nothing)
  Prop.Ref _ -> Prop.Ref (const Nothing)

sel :: forall i j r. Eq i => (String -> Maybe i -> j -> r) -> String -> i -> j -> Maybe i -> r
sel f s p1 j (Just p2) | p1 == p2 = f (s <> " selected") Nothing j
sel f s p1 j _ = f s (Just p1) j

type Focus o i =
  { value :: i
  , new :: i -> o
  }
ofocus :: forall o u i. (o -> u) -> Focus o i -> Focus u i
ofocus ou { value, new } =
  { value: value
  , new: ou <<< new
  }
ifocus :: forall o i j. (i -> j) -> (j -> i) -> Focus o i -> Focus o j
ifocus ij ji { value, new } =
  { value: ij value
  , new: new <<< ji
  }
from :: forall o. o -> Focus o o
from = { value: _, new: identity }
flow :: forall o i j. Focus o i -> ALens' i j -> Focus o j
flow { value, new } l' = let l = cloneLens l' :: Lens' i j in
  { value: view l value
  , new: \j -> new (set l j value)
  }
divert :: forall e f o i. FunctorWithIndex e f => Eq e => Focus o (f i) -> f (Focus o i)
divert { value, new } = value # mapWithIndex \i v ->
  { value: v
  , new: new <<< \v' -> value # mapWithIndex \j ->
      if i == j then const v' else identity
  }
divertTo :: forall e f o i.
  Applicative f => Alt f =>
  FunctorWithIndex e f => Eq e =>
  i ->
  Focus o (f i) -> f (Focus o i)
divertTo v0 f@{ value, new } =
  let
    snoc :: forall a. f a -> a -> f a
    snoc fa a = fa <|> pure a
  in snoc (divert f)
    { value: v0
    , new: new <<< snoc value
    }
listicle :: forall o i.
  i -> (i -> Boolean) ->
  Focus o (Array i) -> Array (Focus o i)
listicle v0 is0 = divertTo v0 <<< join ifocus (Array.filter (not is0))
strong :: forall o i j.
  Focus o (Tuple i j) -> Tuple (Focus o i) (Focus o j)
strong { value: Tuple i j, new } = Tuple
  { value: i
  , new: new <<< flip Tuple j
  }
  { value: j
  , new: new <<< Tuple i
  }
focal :: forall f i o. Functor f => (i -> f i) -> Focus o i -> f o
focal f { value, new } = new <$> f value

edtString :: forall w. String -> String -> HH.HTML w String
edtString n v = HH.input [ HP.placeholder n, HP.value v, HE.onValueInput Just ]

data Shape a b = Shape (Maybe b) a (List (Tuple b a)) (Maybe b)
derive instance eqShape :: (Eq a, Eq b) => Eq (Shape a b)
derive instance ordShape :: (Ord a, Ord b) => Ord (Shape a b)
derive instance eq1Shape :: (Eq a) => Eq1 (Shape a)
derive instance ord1Shape :: (Ord a) => Ord1 (Shape a)
type Name = Shape String Unit
strName :: Name -> String
strName (Shape pre name parts post) =
  let
    m Nothing = ""
    m (Just (_ :: Unit)) =
      "_"
    l Nil = ""
    l (Tuple (_ :: Unit) part : r) =
      "_" <> part <> l r
  in m pre <> name <> l parts <> m post
rndName :: forall w i. Name -> HH.HTML w i
rndName (Shape pre name parts post) = spanned "name"
  let
    m Nothing = []
    m (Just (_ :: Unit)) =
      [ spanned "placeholder" [ HH.text "_" ] ]
    l Nil = []
    l (Tuple (_ :: Unit) part : r) =
      [ spanned "placeholder" [ HH.text "_" ]
      , spanned "part" [ HH.text part ]
      ] <> l r
  in m pre <> [ spanned "part" [ HH.text name ] ] <> l parts <> m post
type AbsType =
  { lam :: Boolean
  , imp :: Boolean
  }
data Abs e = Abs AbsType Name e e
strAbs :: Abs String -> String
strAbs (Abs ver nam typ bdy) =
  let
    p = if ver.imp then "?" else "!"
    { o, c } = case ver.lam of
      true -> { o: "[", c: "]" }
      false -> { o: "{", c: "}" }
  in o <> p <> strName nam <> " : " <> typ <> c <> " " <> bdy
data App e
  = Opr (Shape { name :: String, indx :: Natural } e)
  | App e e
data SyntaxF e
  = AbsF (Abs e)
  | AppF (App e)
  | Grp e
type PSyntax = Free SyntaxF (Maybe Natural)
type TSyntax = Free SyntaxF Natural

type Simple = Free Pair String
cataSimple :: forall r.
  (Ptr -> String -> r) ->
  (Ptr -> Pair r -> r) ->
  Ptr -> Simple -> r
cataSimple s p = flip $ cata $ flip \ptr -> unwrap >>>
  either (s ptr) (p ptr <<< mapWithIndex ((#) <<< (_ : ptr)))
ptrSimple :: Ptr -> Simple -> Maybe Simple
ptrSimple Nil = pure
ptrSimple (i : is) = ptrSimple is >=>
  Free.resume >>> flip either (const Nothing)
    \(Pair l r) -> Just (if i then r else l)
setSimple :: Ptr -> Simple -> Simple -> Simple
setSimple = List.reverse >>> go where
  go Nil _ r = r
  go (i : is) e r =
    case Free.resume e of
      Left (Pair x y) -> Free.wrap $ Pair
        (if i then x else go is x r)
        (if i then go is y r else y)
      Right _ -> e
subSimple :: Simple -> Map String Simple -> Simple
subSimple x m = x >>= \v ->
  case Map.lookup v m of
    Nothing -> pure v
    Just r -> r
strSimple :: Simple -> String
strSimple = cata go <@> false where
  go :: CoEnvT String Pair (Boolean -> String) -> Boolean -> String
  go (CoEnvT (Left var)) _ = var
  go (CoEnvT (Right (Pair l r))) p =
    (if p then \e -> "(" <> e <> ")" else identity) $
    l false <> "\xA0" <> r true
prsSimple :: String -> Maybe Simple
prsSimple = runParser $ wssw $ fix \prs ->
  let n = map pure (mparens prsName) <|> parens prs
  in nelist ws n <#> NEL.uncons >>> \{ head, tail } ->
      TF.foldl (map map map Free.wrap Pair) head tail
rndSimple :: forall w i. Simple -> HH.HTML w i
rndSimple = compose (spanned "expr") $ cata go <@> false where
  go (CoEnvT (Left var)) _ = pspannedpt "name" var
  go (CoEnvT (Right (Pair l r))) p =
    (if p then \e ->
      pspannedpt "paren left" "(" <>
      e <>
      pspannedpt "paren left" ")"
    else identity) $
    l false <> pspannedpt "app" "\xA0" <> r true

type Context = Array
  { name :: String
  , of :: Simple
  }
type BiContext =
  { terms :: Array
    { ctx :: Context
    , name :: String
    , of :: Simple
    }
  , idems :: Array
    { ctx :: Context
    , name :: String
    , left :: Simple
    , right :: Simple
    }
  }

type Parser = StateT String Maybe
runParser :: forall t. Parser t -> String -> Maybe t
runParser (StateT f) s = case f s of
  Just (Tuple t "") -> Just t
  _ -> Nothing

lit :: String -> Parser Unit
lit s0 = StateT \s ->
  if take (length s0) s /= s0 then Nothing else
    Just (Tuple unit (drop (length s0) s))

ws :: Parser Unit
ws = modify_ $ dropWhile $
  pure >>> fromCodePointArray >>> flip TF.elem
    [ " ", "\n", "\xA0" ]

wssw :: Parser ~> Parser
wssw p = ws *> p <* ws

ne :: Parser ~> Parser
ne p = StateT
  case _ of
    "" -> Nothing
    s -> unwrap p s

try :: forall a. Parser a -> Parser (Maybe a)
try p = map pure p <|> pure empty

list :: forall a. Parser Unit -> Parser a -> Parser (List a)
list s p = try (nelist s p) <#> maybe Nil NEL.toList

nelist :: forall a. Parser Unit -> Parser a -> Parser (NonEmptyList a)
nelist s p = do
  head <- p
  tail <- try (s *> nelist s p) <#> maybe Nil NEL.toList
  pure $ NEL.cons' head tail

parens :: Parser ~> Parser
parens p = lit "(" *> wssw p <* lit ")"

mparens :: Parser ~> Parser
mparens p = p <|> parens p

prsName :: Parser String
prsName = StateT \s ->
  let
    isAlpha c =
      let z = fromCodePointArray [c]
      in z /= toLower z || z /= toUpper z
    name = takeWhile isAlpha s
  in if null name then Nothing else
    Just (Tuple name (drop (length name) s))

type KISS = Free Pair String
type Ptr = List PairI
cataKISS :: forall r.
  (Ptr -> String -> r) ->
  (Ptr -> Pair r -> r) ->
  Ptr -> KISS -> r
cataKISS s p = flip $ cata $ flip \ptr -> unwrap >>>
  either (s ptr) (p ptr <<< mapWithIndex ((#) <<< (_ : ptr)))
ptrKISS :: Ptr -> KISS -> Maybe KISS
ptrKISS Nil = pure
ptrKISS (i : is) = ptrKISS is >=>
  Free.resume >>> flip either (const Nothing)
    \(Pair l r) -> Just (if i then r else l)
setKISS :: Ptr -> KISS -> KISS -> KISS
setKISS = List.reverse >>> go where
  go Nil _ r = r
  go (i : is) e r =
    case Free.resume e of
      Left (Pair x y) -> Free.wrap $ Pair
        (if i then x else go is x r)
        (if i then go is y r else y)
      Right _ -> e
subKISS :: KISS -> Map String KISS -> KISS
subKISS x m = x >>= \v ->
  case Map.lookup v m of
    Nothing -> pure v
    Just r -> r
strKISS :: KISS -> String
strKISS = cata $ unwrap >>> either identity
  \(Pair l r) -> "(" <> l <> "•" <> r <> ")"
prsKISS :: String -> Maybe KISS
prsKISS = runParser $ wssw $ fix \prs ->
  map pure (mparens prsName) <|>
    parens ado
      l <- prs
      _ <- ws *> lit "•" <* ws
      r <- prs
      in Free.wrap (Pair l r)
rndKISS :: forall w. KISS -> Maybe Ptr -> HH.HTML w (Maybe Ptr)
rndKISS = map map map (spanned "expr") $ (#) Nil $ cataKISS
  (sel epspannedpt "name")
    \ptr (Pair l r) ->
      flip (sel (pspanned >>> const) "paren g" ptr) <*>
      ( sel epspannedpt "paren l" ptr "(" <>
        l <> sel epspannedpt "op" ptr "•" <> r <>
        sel epspannedpt "paren r" ptr ")"
      )
edtKISS :: forall w. String -> String -> HH.HTML w String
edtKISS n v = HH.div [ cls "expr edit" ]
  [ HH.textarea
    [ cls "editing"
    , HP.value v
    , HP.placeholder n
    , HE.onValueInput Just
    ]
  , case prsKISS v of
      Nothing -> HH.div [ cls "result error" ] [ HH.text "<!>" ]
      Just p -> HH.div [ cls "result" ] [ silence (rndKISS p Nothing) ]
  ]

fit :: Set String -> KISS -> KISS -> Maybe (Map String KISS)
fit vs = Free.resume >>> case _ of
  Right v ->
    if Set.member v vs
      then Just <<< Map.singleton v
      else Free.resume >>> case _ of
        Right w | w == v -> Just Map.empty
        _ -> Nothing
  Left (Pair l r) -> Free.resume >>> case _ of
    Left (Pair x y) -> do
      a <- fit vs l x
      b <- fit vs r y
      fitTogether a b
    _ -> Nothing

fitTogether :: forall k v. Ord k => Eq v => Map k v -> Map k v -> Maybe (Map k v)
fitTogether m n =
  if TF.and $ Map.intersectionWith eq m n then Just (Map.union m n) else Nothing

appliesToAt ::
  KISS -> Ptr ->
  Set String -> KISS ->
  Maybe
    { ctx :: Map String KISS
    , result :: Map String KISS -> KISS -> KISS
    }
appliesToAt e p cnst =
  case ptrKISS p e of
    Nothing -> const Nothing
    Just x -> \d ->
      fit (Set.fromFoldable d `Set.difference` cnst) d x <#> \ctx ->
        let result ctx' = setKISS p e <<< flip subKISS (ctx <> ctx')
        in { ctx, result }
type Truss =
  { ptr :: Ptr
  , rule ::
    { name :: String
    , ctx :: Map String KISS
    }
  , result :: KISS
  }

type Slots =
  ()
type Data =
  {}
data State
  = Entering
    { axioms :: Array
      { name :: String
      , old :: String
      , new :: String
      , cnst :: Set String
      }
    , expr :: String
    }
  | Bridging
    { axioms :: Array
      { name :: String
      , old :: KISS
      , new :: KISS
      , cnst :: Set String
      }
    , expr :: KISS
    , span :: Array Truss
    , next :: Maybe
      { ptr :: Ptr
      , rule :: String
      , ctx :: Map String (Map String String)
      }
    }
data Action = Set State

slices :: forall a. Array a -> Array (Tuple (Array a) a)
slices = snd <<< Array.foldl adder (Tuple [] []) where
  adder (Tuple as ds) a =
    Tuple (Array.snoc as a) (Array.snoc ds (Tuple as a))

pontifex :: H.Component HH.HTML (Const Void) Unit Void Aff
pontifex = H.mkComponent
  { initialState: const $ Entering
      { axioms:
        [ { name: "assoc"
          , old: "((x•y)•z)"
          , new: "(x•(y•z))"
          , cnst: Set.empty
          }
        , { name: "comm"
          , old: "(a•b)"
          , new: "(b•a)"
          , cnst: Set.empty
          }
        , { name: "idem"
          , old: "(m•m)"
          , new: "m"
          , cnst: Set.empty
          }
        , { name: "idL"
          , old: "(e•m)"
          , new: "m"
          , cnst: Set.singleton "e"
          }
        , { name: "idR"
          , old: "(m•e)"
          , new: "m"
          , cnst: Set.singleton "e"
          }
        , { name: "absorbL"
          , old: "(a•m)"
          , new: "a"
          , cnst: Set.singleton "a"
          }
        ]
      , expr: "a"
      }
  , render, eval: H.mkEval H.defaultEval { handleAction = eval }
  } where
    render :: State -> H.ComponentHTML Action Slots Aff
    render = case _ of
      Entering s ->
        let
          foc = { value: s, new: Entering >>> Set }
          axioms = flow foc $ prop (_S::S_ "axioms")
          bridge = Set <<< Bridging <$> ado
            axs <- Just $ s.axioms # Array.mapMaybe \r -> ado
              name <- if r.name == "" then Nothing else Just r.name
              old <- prsKISS r.old
              new <- prsKISS r.new
              in { name, old, new, cnst: r.cnst }
            expr <- prsKISS s.expr
            in
              { axioms: axs
              , expr
              , span: []
              , next: Nothing
              }
        in HH.div [ cls "entering" ]
          [ HH.ol [ cls "axioms" ] $ map (HH.li_ <<< pure) $
              listicle mempty (eq mempty) axioms <#>
                \ax -> HH.div [ cls "axiom" ] $
                  [ focal (edtString "name") $ flow ax $ prop (_S::S_ "name")
                  , focal (edtKISS "old") $ flow ax $ prop (_S::S_ "old")
                  , HH.text " = "
                  , focal (edtKISS "new") $ flow ax $ prop (_S::S_ "new")
                  ] <>
                    let
                      vs = Array.fromFoldable $
                        maybe mempty Set.fromFoldable (prsKISS ax.value.old) <>
                        maybe mempty Set.fromFoldable (prsKISS ax.value.new)
                    in vs <#> \v ->
                      HH.label [ cls "constants" ]
                        [ HH.input
                          [ HP.type_ HP.InputCheckbox
                          , HP.checked $ not Set.member v ax.value.cnst
                          , HE.onChecked \c -> Just $
                              ax.new $ ax.value
                                { cnst = ax.value.cnst #
                                    if c then Set.delete v else Set.insert v
                                }
                          ]
                        , HH.text " "
                        , HH.text v
                        ]
          , focal (edtKISS "expr") $ flow foc $ prop (_S::S_ "expr")
          , HH.button
            [ maybe (HP.disabled true) (HE.onClick <<< pure <<< pure) bridge ]
            [ HH.text "Start bridging!" ]
          ]
      Bridging s ->
        let foc = { value: s, new: Bridging >>> Set } in
        HH.div [ cls "bridging" ]
          [ HH.div [ cls "entered" ]
            [ HH.ol [ cls "axioms" ] $ map (HH.li_ <<< pure) $
                s.axioms <#> \ax -> silence $ HH.div [ cls "axiom" ]
                  [ HH.text $ ax.name <> ": "
                  , rndKISS ax.old Nothing
                  , HH.text " = "
                  , rndKISS ax.new Nothing
                  , HH.text $ " " <> TF.foldMap ("∀" <> _)
                      ((Set.fromFoldable ax.old <> Set.fromFoldable ax.new)
                      `Set.difference` ax.cnst
                      )
                  ]
            , HH.button
              [ HE.onClick \_ -> pure $ Set $ Entering $
                  { axioms: s.axioms <#> \{ name, old, new, cnst } ->
                      { name, old: strKISS old, new: strKISS new, cnst }
                  , expr: strKISS s.expr
                  }
              ]
              [ HH.text "Revise assumptions" ]
            ]
          , HH.ol [ cls "bridges" ] $ map (HH.li_ <<< pure) $
              let
                exprs =
                  let
                    base = pure <<<
                      { prev: []
                      , expr: s.expr
                      , next: _
                      }
                    adder to (Tuple prev span) next =
                      (:) { prev: Array.snoc prev span
                      , expr: span.result
                      , next
                      } $ to $ Left
                        { ptr: span.ptr
                        , rule: span.rule.name
                        , ctx: span.rule.ctx
                        }
                    r1 = Array.foldl adder base (slices s.span)
                    r2 = r1 (Right s.next)
                  in r2 # Array.fromFoldable # Array.reverse
                rndExpr { prev, expr, next } =
                  let
                    new nextnext =
                      foc.new $ s
                        { span = prev
                        , next = nextnext
                        }
                    ptr =
                      { value: case next of
                          Left r -> Just r.ptr
                          Right (Just r) -> Just r.ptr
                          Right Nothing -> Nothing
                      , new: new <<< map { rule: "", ctx: Map.empty, ptr: _ }
                      }
                    newrule ctx rule = new $ { rule, ctx, ptr: _ } <$> ptr.value
                  in HH.div [ cls "bridge" ] $ [ focal (rndKISS expr) ptr ] <>
                    case next of
                      Left { rule, ctx } ->
                        [ HH.div [ cls "rule" ]
                          [ spannedpt "name" rule
                          , spanned "ctx"
                            [ HH.text "["
                            , HH.text $ TF.intercalate ", " $
                                ctx # mapWithIndex \k v ->
                                  k <> " ≔ " <> strKISS v
                            , HH.text "]"
                            ]
                          ]
                        ]
                      Right Nothing -> []
                      Right (Just { ptr: ptr0, rule, ctx: freectx }) ->
                        let
                          apple = appliesToAt expr ptr0
                          attempt side ax = F.oneOfMap pure $
                            apple ax.cnst (if side then ax.new else ax.old) <#>
                              \{ ctx, result } ->
                                let
                                  c = if side then "⇐" else "⇒"
                                  name' = c <> ax.name
                                  sub =
                                    maybe Map.empty (Map.mapMaybe prsKISS)
                                      (Map.lookup name' freectx)
                                  result' = result sub $
                                    (if side then ax.old else ax.new)
                                in
                                  { name: name', ctx
                                  , result: result'
                                  , freevars: Array.fromFoldable $
                                      Set.fromFoldable (if side then ax.old else ax.new)
                                      `Set.difference`
                                      Set.fromFoldable (if side then ax.new else ax.old)
                                      `Set.difference`
                                      ax.cnst
                                  }
                          applicable = s.axioms >>= \ax ->
                            attempt false ax <|> attempt true ax
                        in case applicable of
                          [] -> [ HH.text "No rules applicable!" ]
                          _ -> applicable <#> \{ result, ctx, freevars, name: name' } -> HH.div_
                            let freectx' = fromMaybe Map.empty $ Map.lookup name' freectx in
                            [ HH.div [ cls "rule" ]
                              [ spannedpt "name" name'
                              , spanned "ctx"
                                [ HH.text "["
                                , HH.text $ TF.intercalate ", " $
                                    ctx # mapWithIndex \k v ->
                                      k <> " ≔ " <> strKISS v
                                , HH.text "]"
                                ]
                              ]
                            , HH.ul [ cls "freevars" ] $
                              freevars <#> \var -> HH.li_
                                let v = fromMaybe "" $ Map.lookup var freectx' in
                                [ spannedpt "name" var
                                , HH.text " = "
                                , edtKISS "" v <#>
                                    \val -> new $ Just
                                      { rule, ptr: ptr0
                                      , ctx: freectx # Map.insert name'
                                        (Map.insert var val freectx')
                                      }
                                ]
                            , HH.div [ cls "result" ] $ pure $
                              rndKISS result Nothing <#> \clicked ->
                                foc.new $ s
                                  { span = Array.snoc prev
                                    { ptr: ptr0
                                    , rule:
                                      { name: name'
                                      , ctx: ctx <>
                                          maybe Map.empty (Map.mapMaybe prsKISS)
                                            (Map.lookup name' freectx)
                                      }
                                    , result
                                    }
                                  , next = clicked <#>
                                    { ptr: _, rule: "", ctx: Map.empty }
                                  }
                            ]
              in exprs <#> rndExpr
          ]

    eval :: Action -> H.HalogenM State Action Slots Void Aff Unit
    eval (Set s) = H.put s

main :: Effect Unit
main = HA.runHalogenAff do
  body <- HA.awaitBody
  driver <- VD.runUI pontifex unit body
  pure unit
