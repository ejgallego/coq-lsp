# `coq-lsp` frequently asked questions

 * [Why do you say so often "client" and "server", what does it mean?](#why-do-you-say-so-often-client-and-server-what-does-it-mean)
 * [How is `coq-lsp` different from VSCoq?](#how-is-coq-lsp-different-from-vscoq)
    + [VsCoq "Legacy"](#vscoq-legacy)
    + [VsCoq 2](#vscoq-2)
 * [Is `coq-lsp` limited to VSCode?](#is-coq-lsp-limited-to-vscode)
 * [What part of the LSP protocol does `coq-lsp` support?](#what-part-of-the-lsp-protocol-does-coq-lsp-support)
 * [What is `coq-lsp` roadmap?](#what-is-coq-lsp-roadmap)
 * [How is `coq-lsp` developed and funded?](#how-is-coq-lsp-developed-and-funded)
 * [Is there more information about `coq-lsp` design?](#is-there-more-information-about-coq-lsp-design)

## Why do you say so often "client" and "server", what does it mean?

In the world of user interfaces for programming languages
(a.k.a. IDEs), "client/server" refer respectively to the editor and
the compiler of language checker which provides feedback to the
editor, that is to say, errors, warnings, syntax highlighting
information, etc...

This way, the editor don't need to know a lot about the language.

Thus, in `coq-lsp` case we have:

- the client is Visual Studio Code plus the `coq-lsp` extension, or
  some other editors such as Emacs or vim,
- the server is an extended Coq binary `coq-lsp`, which takes care of
  running and checking Coq commands, among other tasks.

The client and the server communicate using the [Language Server
Protocol](https://microsoft.github.io/language-server-protocol/)
standard, thus, the `coq-lsp` language server can be used from any
editor supporting this protocol.

## How is `coq-lsp` different from VSCoq?

As of Oct 2024, there are two versions of VsCoq, "VsCoq Legacy" and
"VsCoq 2". They are totally different implementations, sharing
the name and project page.

### VsCoq "Legacy"

[VsCoq Legacy](https://github.com/coq-community/vscoq/tree/vscoq1) or
"VsCoq 1" was developed by C.J.  Bell (and later maintained by a team
of volunteers) and at the time was an impressive achievement. The key
difference between "VsCoq 1" and `coq-lsp` is how the VSCode client
communicates with Coq.

VsCoq 1 communicates with Coq using the `coqidetop` server,
which implements a XML protocol providing basic operations over
documents.

In `coq-lsp` case, VS Code and Coq communicate using the LSP protocol,
plus a set of custom extensions. This is possible thanks to a new
`coq-lsp` language server, which is an extended Coq binary taking
advantage of improved Coq APIs.

The XML protocol design dates back to 10 years ago, and it makes hard
to support some nice features. Moreover, development of VSCoq 1 and
`coqidetop` is not coupled, so it is not easy to add new features.

VSCoq 1 went to significant effort to workaround these deficits
client-side, but that came with its own set of technical and
maintenance challenges.

A key problem when implementing a language server for Coq is the fact
that Coq APIs were not meant for reactive UIs.

For `coq-lsp`, we have done a years-long effort to significantly
improve Coq's base APIs, which has resulted in a much more lightweight
client implementation and a more capable server.

Moreover, `coq-lsp` development is active while VSCoq 1 is mostly in
maintenance mode due to the limitations outlined above. In a sense,
you could think of `coq-lsp` as a full rewrite of VSCoq 1, using the
experience we have accumulated over years of work in related projects
(such as jsCoq), and the experience in state-of-the art UI design and
implementation in other systems (Rust, Lean, Isabelle).

We didn't pick `VSCoq 2` as a project name given than `coq-lsp`
follows the LSP standard and is not specific to Visual Studio code, in
fact, it works great on other editors such as vim or Emacs.

### VsCoq 2

[VsCoq 2](https://github.com/coq-community/vscoq) follows the spirit
of `coq-lsp` and uses an OCaml-based language server to provide an
implementation of the Language Server Protocol for Coq.

The implementation approaches of both servers are very different, and
we are working on a more detailed comparison between the projects. In
particular, there seem to be significant differences in terms of
features, performance, robustness, UI model, and extensibility.

We encourage you to try both and provide feedback!

## Is `coq-lsp` limited to VSCode?

No! See above!

While VSCode is for now the primary client development platform,
we fully intend the `coq-lsp` server to be usable from other editors.

In particular, we have already ported jsCoq to work as a `coq-lsp`
client.

Please get in touch if you would like to contribute support for your
favorite editor!

## What part of the LSP protocol does `coq-lsp` support?

See the [PROTOCOL.md](./doc/PROTOCOL.md) file. `coq-lsp` provides some
minimal extensions to the `coq-lsp` protocol as to adapt to the needs
of interactive proof checking, see [this
issue](https://github.com/microsoft/language-server-protocol/issues/1414)
for more information about proof assistants and LSP.

## What is `coq-lsp` roadmap?

The short-term roadmap is to support the full LSP protocol, and to
focus on core issues related to the needs of Coq users.

We follow a release model based on Semantic Versioning, see our bug
tracker and project tracker for more information.

## How is `coq-lsp` developed and funded?

`coq-lsp` is developed collaboratively, by a [team of
contributors](https://github.com/ejgallego/coq-lsp#team).

The development is coordinated by Emilio J. Gallego Arias, who is also
the technical lead for the project.

`coq-lsp` was supported by Inria Paris from November 2019 to October
2024, with key contributions by Ali Caglayan (volunteer) and Shachar
Itzhaky (Technion Institute of Technology), and many other
contributors.

As of November 2024, the project is run on a volunteer basis.

## Is there more information about `coq-lsp` design?

Yes! There are a couple of presentations related to development
methodology and internals. We will upload the presentations here
shortly. We also hope to publish a paper soon.

Our [contributing guide](../CONTRIBUTING.md) provides some valuable
information about the organization of the source code, etc...

Note that it is not easy to describe an evolving system like this, we
like this quote [from Twitter](https://twitter.com/notypes/status/1610279076320923650):

> Papers sometimes feel like a terrible way to communicate systems
> research; systems continue evolving but papers are static
>
> Our compiler (https://calyxir.org) is three years into development
> but people keep citing the paper and discussing limitations that
> have been addressed
