# dhall-purescript
This project is an implementation of [Dhall](https://github.com/dhall-lang/dhall-lang) in PureScript. It covers the standard API for representing, parsing, importing, and verifying Dhall expressions. But moreover I also aim to create a structural editor that represents and allows the user to manipulate the AST in the browser, with instant feedback, including interactive(!) errors and suggestions.

It works both in the browser and on node.js. Or at least it should! File an issue if you run into problems.

## Installation
PS dependencies currently use `bower`, and JS dependencies use `npm`, so installation looks like:
```sh
bower install --save MonoidMusician/dhall-purescript#master
npm install --save cbor-js@0.1.0
npm install --save nearley@^2.15.1
npm install --save node-fetch@^2.6.0
npm install --save git://github.com/athanclark/sjcl.git#e6ca43fbcc85689f9e6b212cc88b85a53295a459
```

Generate the grammar by calling `nearleyc grammar.ne -o grammar.js` through `npm`:
```
cd bower_components/dhall-purescript
cat grammar.sh
npm run grammar
```

The browser-based structural editor is running on [GitHub pages](https://monoidmusician.github.io/dhall-purescript/index.html).

## Why Dhall?
Because Dhall is awesome, relatively simple, and conceptually clean. It has an agreed-upon standard, with lots of tests, is under active development, continually improving.

## Why PureScript?
It is in my experience one of the best (typed!) compile-to-JS languages out there, and it supports all the abstraction I need. (It even has PolyKinds!) And it has one of the most well-designed UI libraries out there.

## Dhall Implementation and API
Currently, the project is about 90% up-to-date with the latest version of the standard, plus some upcoming changes, as measured by the dhall-lang test suite. It implements the syntax, a parser, and all the judgments of the Dhall standard: import resolution, typechecking, alpha- and beta-normalization, and all the smaller judgments needed to support them. Additionally, there is a small and incomplete API for converting to PureScript types after the Haskell implementation.

### AST type

The main expression type is `Dhall.Core.AST.Types.Expr m a`. It is a newtype of the `Free` monad on top of `VariantF` (an extensible sum functor, although the extensibility is rarely used in this library). The first parameter `m :: Type -> Type` is the functor used for records/unions; it is usually `Data.Map.Map String` (unordered) or `Dhall.Map.InsOrdStrMap` (ordered), see `Dhall.Core.AST.Operations` for functions to change it. The second parameter `a :: Type` represents the leaves (usually used for imports), it can be mapped over using the `Functor` instance (along with `Traversable` and even `Monad`, for substitution).

### Public API

A word of warning: most of the library is implemented in more generality than you should ever want or need. In particular, the algorithms are meant to work with various different types of trees, and some of them are very scary complicated, like `Ospr`. The public API works solely with the simple `Expr m a` tree, however.

- `Dhall.Variables.alphaNormalize` implements alpha-normalization.
- `Dhall.Normalize.normalize` implements beta-normalization. Note that this will **not** sort the tree, so use `Dhall.Core.AST.Operations.unordered` for that.
- `Dhall.TypeCheck.typeOf` (and friends) implements typechecking, returning results in the error functor `Validation.These.Erroring` (which is bundled with this library), where the error parameter is an extensible variant. `Dhall.TypeCheck.Errors.explain` can be used to render those errors, or just use `Dhall.TypeCheck.oneStopShop`.
- `Dhall.Imports.Resolve.resolveImports` implements import resolution, but it is agnostic to the retrieval mechanism used, some of which can be found in `Dhall.Imports.Retrieve` (for both node and browser). See those files for more docs, and the tests for example usage.
- `Dhall.Parser.parse` implements parsing, using the external [`nearley.js`](https://nearley.js.org/) library. Sorry, there are no meaningful errors provided.
- Sorry, I don’t have pretty printing yet … whoops.
- `Dhall.API.Conversions` implements conversions to/from PS types.
