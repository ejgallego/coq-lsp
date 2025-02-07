# Welcome to rocq-lsp vendor directory

The `rocq-lsp` developer build does depend on a few packages that don't
have a stable interface. In particular:

- `coq`: we heavily depend on Rocq's API. Policy is to try to be close
  to the `master` branch, as this reduces testing delta.

- `coq-stdlib`: we depend on many files numbers as to be able to test,
  for now the policy is to follow the `master` branch. We don't need
  to follow this policy tho.

- `coq-waterproof`: we depend on Waterproof as we include it in our
  Web Build. For stable versions we do a regular build and install in
  the opam switch (as is done for the stdlib and Rocq). Here, we
  follow the policy indicated by Waterproof upstream.

## Tools

`coq-lsp` makefile includes a couple of targets to help managing the
submodules here, in particular:

- `submodules-init`/`submodules-deinit`: init / deinit all the submodules
- `submodules-update`: update Rocq and Stdlib to their latest versions

## Roadmap

The approach used here doesn't not really scale due once more
developments are added, due to several reasons. We hope that at some
point we can use
[rocq-universe](https://github.com/coq-universe/coq-universe)
as replacement for this manual system.
