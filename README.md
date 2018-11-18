# dhall-purescript
This project is going to be an implementation of [Dhall](https://github.com/dhall-lang/dhall-lang) in PureScript – that is, the standard API for representing, parsing, importing, and verifying Dhall expressions. But moreover I also aim to create a structural editor that represents and allows the user to manipulate the AST in the browser, with instant feedback, including interactive(!) errors and suggestions.

## Why Dhall?
Because Dhall is awesome, relatively simple, and conceptually clean. It is also under active development, continually improving.

## Why PureScript?
It is in my experience one of the best (typed!) compile-to-JS languages out there, and it supports all the abstraction I need. (Well, okay, I think it could use polykinds ... but that’s only a minor blemish ;)) And it has one of the most well-designed UI libraries out there.

## So ... AST editor?
I just think that editing _text_ for a computer to understand is stupid – it means that the software needs to put in extra work to understand what the user is doing, which typically means fewer helpful features, and many more hacks. (Any feature beyond syntax highlighting and automatic imports is usually a hack. Even syntax highlighting is a hack, most of the time.) So my goal is to make the dream of structural editing a reality, and this will be my first proof-of-concept for that. (Of course, this is nota new idea, and there’s other projects with this goal too.)

I think this could revolutionize how humans interact with programming languages. The computer and the human will finally be on the same page, so to speak. The editing software will keep up with the user’s input, incrementally typechecking each piece of code, knowing what suggestions will be valid in a certain place, knowing when (and where) variables are used and unused – anything you could imagine.

One of the benefits will be rich semantic edits and diffs – you will interact with the code how it is meant to be changed, with its actual representation at hand, unbroken. For example, one (relatively trivial) operation could be swapping the order of variables in a `let` binding or lambda function (or pi type). This only works if the variables are independent, and the second one does not reference the first – but this is easy to check in the AST, so the editor would check that that condition is satisfied before allowing the operation to be done, otherwise it would fail with a nice error message explaining why it could not be done and actually pointing out the cross reference(s). Another common operation is refactoring, and intelligent tools could assist with that, allowing abstraction with minimal effort, automatically managing variable references that need updating, etc. Plus, with Dhall’s normalization, some simple patterns of refactoring will be equivalent to the same normalized expression, resulting in obviously equivalent code.

There also can be cool experiments with how objects are rendered. A couple examples would be: HTML/CSS data (even markdown) could be displayed directly in the browser – no need to wait for code to compile, it would live update; highly structured data could be given it’s own form to input that data with. I‘m sure there are more examples, use your imagination!!

## Help??
It’s an enormous project, and I’m a busy college student, so if anyone wants to help contribute, I would love it! If you’re interested, contact me and I can suggest things to work on, or look at the open issues. There should be some things that are easy to get started on without much PS knowledge. CSS styling advice also welcome ;) (I want to make the AST look pretty!)
