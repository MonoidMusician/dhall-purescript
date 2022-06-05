{-
Welcome to a Spago project!
You can edit this file as you like.

Need help? See the following resources:
- Spago documentation: https://github.com/purescript/spago
- Dhall language tour: https://docs.dhall-lang.org/tutorials/Language-Tour.html

When creating a new Spago project, you can use
`spago init --no-comments` or `spago init -C`
to generate this file without the comments in this block.
-}
{ name = "dhall-purescript"
, dependencies =
  [ "aff"
  , "aff-promise"
  , "argonaut-core"
  , "arraybuffer-types"
  , "arrays"
  , "avar"
  , "bifunctors"
  , "bigints"
  , "console"
  , "const"
  , "contravariant"
  , "control"
  , "datetime"
  , "effect"
  , "either"
  , "enums"
  , "exceptions"
  , "fixed-points"
  , "foldable-traversable"
  , "foreign"
  , "foreign-object"
  , "free"
  , "functors"
  , "identity"
  , "integers"
  , "lazy"
  , "lists"
  , "matryoshka"
  , "maybe"
  , "naturals"
  , "newtype"
  , "node-buffer"
  , "node-child-process"
  , "node-fs"
  , "node-fs-aff"
  , "node-path"
  , "node-process"
  , "node-streams"
  , "nonempty"
  , "nullable"
  , "ordered-collections"
  , "orders"
  , "parallel"
  , "partial"
  , "prelude"
  , "profunctor"
  , "profunctor-lenses"
  , "psci-support"
  , "record"
  , "refs"
  , "strings"
  , "these"
  , "transformers"
  , "tuples"
  , "typelevel-prelude"
  , "unfoldable"
  , "unsafe-coerce"
  , "unsafe-reference"
  , "variant"
  , "yoga-fetch"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs", "test/**/*.purs" ]
}
