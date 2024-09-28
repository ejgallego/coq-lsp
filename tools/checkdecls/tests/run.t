General tests for checkdecls

Error when not input:

  $ checkdecls
  checkdecls: required argument FILES is missing
  Usage: checkdecls [OPTION]… FILES…
  Try 'checkdecls --help' for more information.
  [124]

Error when file doesn't exists:

  $ checkdecls where_i_am.txt
  checkdecls: FILES… arguments: no 'where_i_am.txt' file
  Usage: checkdecls [OPTION]… FILES…
  Try 'checkdecls --help' for more information.
  [124]

Simple test with one file, succeed

  $ echo Coq.Init.Nat.add > clist
  $ echo Coq.Init.Peano.plus_n_O >> clist
  $ checkdecls clist

Simple test with one file, fail

  $ echo Coq.Init.Peano.not_a_constant >> clist
  $ echo Coq.Init.Nat.not_a_theorem >> clist
  $ checkdecls clist
  Coq.Init.Peano.not_a_constant is missing.
  Coq.Init.Nat.not_a_theorem is missing.
  [1]
