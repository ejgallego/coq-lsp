- Tests on document lifetime:

  Checks to do:

  a) check that the errors / messages are properly relayed to the user
  b) check that coq-lsp recovers properly

  + create a .v document, fails when importing the prelude for some weird reason
  + bump a .v document, fails to bump due to having to re-create initial state

  + For .mv / .wpn documents: same as before, we can also fail due to
    bad markdown parsing
