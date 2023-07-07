# Roadmap

For now the main focus of the project to write clean and maintainable
code, and to provide a smooth user experience.

This includes providing feedback upstream so the Coq API can be
tailored to provide a good interactive experience.

We are actively looking for contributors, please read first [the
contributing guide](../CONTRIBUTING.md).

Here are some project ideas:

## UI design

The [info view panel](../editor/code/views/info/index.tsx) can use many
improvements in the are of UI design and layout. In particular, we'd
like to:

- incorporate search and filters bar
- improve rendering of Goals and Coq terms
- allow users to click links from the view to go to particular source points
- make hypothesis sortable
- support goal diff
- welcome screen

## Workspace management

- Provide a left panel for workspace information
- Auto build of workspace files
- Jump to definition: That's in progress, pending on https://github.com/coq/coq/pull/16261
- Workspace search: be able to search on the whole workspace without loading the files.

## Checking engine

- Allow to skip proofs, configure which ones to skip
- Contextual continuous checking: Check only what is visible, _à la_ Isabelle.
- Python Plugin API

## LTAC Debugging

- "Debug Adapter Protocol" for LTAC

## "Semantic" goal and document printing

- Add support for the `coq-layout-engine` project.
- Port the current pp printer code to React

## LaTeX and Markdown document support

- support `.lv` literate Coq LaTeX documents
- support extended markdown contributions to TOC

### "Computational", Jupyter-style Documents

- support Jupyter-style notebooks

### Responsible elaboration and refinement

Supporting inlays and Lean-style info view.
