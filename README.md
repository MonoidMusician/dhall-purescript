# dhall-purescript
This project is an implementation of [Dhall](https://github.com/dhall-lang/dhall-lang) in PureScript. It covers the standard API for representing, parsing, importing, and verifying Dhall expressions.

It works both in the browser and on node.js. Or at least it should! File an issue if you run into problems.

The current weaknesses are lack of efficiency and some bugs/edge cases in parsing and pretty printing.

## Installation
PS dependencies currently use `bower`, and JS dependencies use `npm`, so installation looks like:
```sh
bower install --save MonoidMusician/dhall-purescript#master
npm install --save @petamoriken/float16@^2.0.0
npm install --save big-integer@^1.6.48
npm install --save nearley@^2.20.1
npm install --save node-fetch@^2.6.1
npm install --save git://github.com/athanclark/sjcl.git#e6ca43fbcc85689f9e6b212cc88b85a53295a459
```

It should also be possible to use `spago` to install it too.

Generate the grammar by calling `nearleyc grammar.ne -o grammar.js` through `npm`:
```
cd bower_components/dhall-purescript
npm run grammar
```

## Why Dhall?
Because Dhall is awesome, relatively simple, and conceptually clean. It has an agreed-upon standard, with lots of tests, is under active development, continually improving.

## Why PureScript?
It is in my experience one of the best (typed!) compile-to-JS languages out there, and it supports all the abstraction I need. (It even has PolyKinds!)

## Dhall Implementation and API
Dhall-Purescript has 100% compliance with the test suite. Nevertheless there are some gaps in the API, particularly in the untested pretty printer, lack of consumer API, and incomplete CLI interface.

It implements the syntax, a parser, and all the judgments of the Dhall standard: import resolution, typechecking, alpha- and beta-normalization, and all the smaller judgments needed to support them. Additionally, there is a small and incomplete API for converting to PureScript types (like the Haskell implementation provides).

### AST type

The main expression type is `Dhall.Core.AST.Types.Expr m a`. It is a newtype of the `Free` monad on top of `VariantF` (an extensible sum functor, although the extensibility is rarely used in this library). The first parameter `m :: Type -> Type` is the functor used for records/unions; it is usually `Data.Map.Map String` (unordered) or `Dhall.Map.InsOrdStrMap` (ordered), see `Dhall.Core.AST.Operations` for functions to change it. The second parameter `a :: Type` represents the leaves (usually used for imports), it can be mapped over using the `Functor` instance (along with `Traversable` and even `Monad`, for substitution).

### Public API

A word of warning: most of the library is implemented in more generality than you should ever want or need. In particular, the algorithms are meant to work with various different types of trees, and some of them are very scary complicated, like `Ospr`. The public API works solely with the simple `Expr m a` tree, however.

- `Dhall.Variables.alphaNormalize` implements alpha-normalization.
- `Dhall.Normalize.normalize` implements beta-normalization. Note that this will **not** sort the tree, so use `Dhall.Core.AST.Operations.unordered` for that.
- `Dhall.Imports.Hash.neutralize` will fully normalize an AST and `Dhall.Imports.Hash.hash` will calculate the sha256 value of it.
- `Dhall.TypeCheck.typeOf` (and friends) implements typechecking, returning results in the error functor `Validation.These.Erroring` (which is bundled with this library), where the error parameter is an extensible variant. `Dhall.TypeCheck.Errors.explain` can be used to render those errors, or just use `Dhall.TypeCheck.oneStopShop`.
- `Dhall.Imports.Resolve.resolveImports` implements import resolution, but it is agnostic to the retrieval mechanism used, some of which can be found in `Dhall.Imports.Retrieve` (for both node and browser). See those files for more docs, and the tests and CLI for example usage.
- `Dhall.Parser.parse` implements parsing, using the external [`nearley.js`](https://nearley.js.org/) library. Sorry, there are no meaningful errors provided.
- `Dhall.Printer.printAST` implements a basic pretty printer.
- `Dhall.API.Conversions` implements conversions to/from PS types.
