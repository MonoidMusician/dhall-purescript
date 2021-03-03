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

## So ... AST editor?
I just think that editing _unstructured_ text for a computer to understand is stupid – it means that the software needs to put in extra work to understand what the user is doing, which typically means fewer helpful features, and many more hacks. (Any feature beyond syntax highlighting and automatic imports is usually a hack. Even syntax highlighting is a hack, most of the time.) So my goal is to make the dream of structural editing a reality, and this will be my first proof-of-concept for that. (Of course, this is not a new idea, and there are other projects with this goal too.)

I think this could revolutionize how humans interact with programming languages. The computer and the human will finally be on the same page, so to speak. The editing software will keep up with the user’s input, incrementally typechecking each piece of code, knowing what suggestions will be valid in a certain place, knowing when (and where) variables are used and unused – anything you could imagine.

One of the benefits will be rich semantic edits and diffs – you will interact with the code how it is meant to be changed, with its actual representation at hand, unbroken. For example, one (relatively trivial) operation could be swapping the order of variables in a `let` binding or lambda function (or pi type), which normally takes some copy-paste finesse to pull off, but could be a gestalt command in an AST editor. This only works if the variables are independent, and the second one does not reference the first – but this is easy to check in the AST, so the editor would check that that condition is satisfied before allowing the operation to be done, otherwise it would fail with a nice error message explaining why it could not be done and actually pointing out the cross reference(s). Another common operation is refactoring, and intelligent tools could assist with that, allowing abstraction with minimal effort, automatically managing variable references that need updating, etc. Plus, with Dhall’s normalization, some simple patterns of refactoring will be equivalent to the same normalized expression, resulting in obviously equivalent code.

There also can be cool experiments with how objects are rendered. A couple examples would be: HTML/CSS data (even markdown) could be displayed directly in the browser – no need to wait for code to compile, it would live update; highly structured data could be given it’s own form to input that data with. I’m sure there are more examples, use your imagination!!

## Help
It’s an enormous project, and I’m a busy college student, so if anyone wants to help contribute, I would love it! If you’re interested, contact me and I can suggest things to work on, or look at the open issues. CSS styling advice also welcome ;) (I want to make the AST look pretty!)
