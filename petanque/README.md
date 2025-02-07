_Petanque_ (pronounced "petanque") is a
[gymnasium](https://gymnasium.farama.org/)-like environment for the
Coq Proof Assistant.

_Petanque_ is geared towards use cases where interacting at the
document-level (like Flèche provides) in not enough, usually because
we want to work on purely proof-search level vs the document level
one.

Petanque follows the methodology developed in SerAPI, thus we specify
an OCaml API (`agent.mli`) which is then exposed via some form of RPC.

## Authors

- Guilaume Baudart (Inria)
- Emilio J. Gallego Arias (Inria)
- Marc Lelarge (Inria)
- Laetitia Teodorescu (Inria)

## Acknowledgments

- Andrei Kozyrev
- Alex Sánchez-Stern

## Install instructions

Please see the regular `coq-lsp` install instructions for more details.

In general, you want to install `coq-lsp` first, the `pytanque`, the
Python companion. You have three options to install `coq-lsp`, in
order of easiness:

- use a released version from Opam:

```
$ opam install coq-lsp
```

- install a development version using Opam:

```
$ git clone ... coq-lsp && cd coq-lsp
$ make opam-update-and-reinstall
$ opam install coq-mathcomp-ssreflect # etc...
```

- use a development version directly from the tree (expert-mode)

See the contributing guide for instructions on how to do the last.

## Installing in Google Collab

As of Feb 2025, the following will get you a working `petanque` for Coq 8.20 in Google Colab:

```python
# Copyright 2024 Drengskapur
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# @title {display-mode:"form"}
# @markdown <br/><br/><center><img src="https://cdn.jsdelivr.net/gh/drengskapur/docker-in-colab/assets/docker.svg" height="150"><img src="https://cdn.jsdelivr.net/gh/drengskapur/docker-in-colab/assets/colab.svg" height="150"></center><br/>
# @markdown <center><h1>Docker in Colab</h1></center><center>github.com/drengskapur/docker-in-colab<br/><br/><br/><b>udocker("run hello-world")</b></center><br/>
def udocker_init():
    import os
    if not os.path.exists("/home/user"):
        !pip install udocker > /dev/null
        !udocker --allow-root install > /dev/null
        !useradd -m user > /dev/null
    print(f'Docker-in-Colab 1.1.0\n')
    print(f'Usage:     udocker("--help")')
    print(f'Examples:  https://github.com/indigo-dc/udocker?tab=readme-ov-file#examples')

    def execute(command: str):
        user_prompt = "\033[1;32muser@pc\033[0m"
        print(f"{user_prompt}$ udocker {command}")
        !su - user -c "udocker $command"

    return execute

udocker = udocker_init()
```

Then do:
- `udocker("pull coqorg/coq:8.20.1")`
- `udocker("run coqorg/coq:8.20.1 opam install logs lwt coq-lsp")`
- `udocker("run coqorg/coq:8.20.1 pet-server --help")`

Once we have our own `coq-lsp/8.20` image, we can just do:

- `udocker("pull coqorg/coq-lsp:0.2.2+8.20.1")`
- `udocker("run coqorg/coq:8.20.1 pet-server --help")`

which saves a bit of time.

## Running `petanque` JSON shell

You can use `petanque` in 3 different ways:

- call the API using JSON-RPC directly in `coq-lsp`, over the LSP
  protocol
- use the provided `pet` and `pet-server` JSON-RPC shells, usually
  with a library such as Pytanque
- call the API directly from your OCaml program

See `agent.mli` for an overview of the API. The
`petanque/setWorkspace` method is only available in the `pet` and
`pet-server` shells; when `petanque` is used from LSP, the workspace
needs to be set using LSP in the usual way.

To execute the `pet` JSON-RPC shell do:
```
make
dune exec -- rlwrap %{bin:pet} --http_headers=no
```

`rlwrap` is just a convenience, if your dune version is too old and
don't recognize the `%{bin:pet}` form, you can just do `dune exec -- pet`.

### Petanque options

Petanque can be initalized from the command line by passing the `--root` parameter to it:
```
make
dune exec -- rlwrap %{bin:pet} --root=/absolute/path/to/my/project
```

NOTE: If you use this option, you should not call `Init`!

### A first example:

`pet` speaks JSON-RPC, and is usable interactively (tho not designed for it):
```json
{ method: "petanque/setWorkspace", id: 1, params: { debug: false, root: "file:///home/egallego/research/coq-lsp/examples" } }
 > {"jsonrpc":"2.0","id":1,"result":null}

{ method: "petanque/start", id: 2, params: { uri: "file:///home/egallego/research/coq-lsp/examples/ex0.v", thm: "addnC" } }
 > {"jsonrpc":"2.0","method":"$/logTrace","params":{"message":"[check] resuming [v: 0], from: 0 l: 0"}}
 > ...
 > {"jsonrpc":"2.0","id":2,"result":1}

{ method: "petanque/run", id: 3, params: { "st": 1, "tac": "induction n."} }
 > {"jsonrpc":"2.0","id":3,"result":["Current_state",2]}

{ method: "petanque/goals", id: 4, params: { "st": 2 } }
 > {"jsonrpc":"2.0","id":4,"result":{"goals":[{"info":{"evar":["Ser_Evar",51],"name":null},"hyps":[{"names":["m"],"def":null,"ty":"nat"}],"ty":"0 + m = m + 0"},{"info":{"evar":["Ser_Evar",55],"name":null},"hyps":[{"names":["n","m"],"def":null,"ty":"nat"},{"names":["IHn"],"def":null,"ty":"n + m = m + n"}],"ty":"S n + m = m + S n"}],"stack":[],"bullet":null,"shelf":[],"given_up":[]}}

...
```

Seems to work! (TM) (Famous last words)

## Running `pet-server`

After building Petanque, you can launch a TCP server with:
```
dune exec -- pet-server
```

Default address is 127.0.0.1 and default port is 8765.

```
❯ dune exec -- pet-server --help
PET(1)                            Pet Manual                            PET(1)

NAME
       pet - Petanque Server

SYNOPSIS
       pet [--address=ADDRESS] [--backlog=BACKLOG] [--port=PORT] [OPTION]…

DESCRIPTION
       Launch a petanque server to interact with Coq

USAGE
       See the documentation on the project's webpage for more information

OPTIONS
       -a ADDRESS, --address=ADDRESS (absent=127.0.0.1)
           address to listen to

       -b BACKLOG, --backlog=BACKLOG (absent=10)
           socket backlog

       -p PORT, --port=PORT (absent=8765)
           port to listen to

COMMON OPTIONS
       --help[=FMT] (default=auto)
           Show this help in format FMT. The value FMT must be one of auto,
           pager, groff or plain. With auto, the format is pager or plain
           whenever the TERM env var is dumb or undefined.

       --version
           Show version information.
```
