import * as Protocol from "vscode-languageserver-protocol";
import * as Types from "vscode-languageserver-types";
import * as LS from "./LanguageServer";

function printMessage(params : Protocol.LogMessageParams) {
  console.log(`${params.type} ${params.message}`);
}

function printDiags(params : Protocol.PublishDiagnosticsParams) {
    console.log(`${params.diagnostics.length} diagnostics received`);
    console.log(params.diagnostics);
}

async function start() {
  let languageServer = LS.start();
  languageServer.trace
  languageServer.onNotification(Protocol.LogMessageNotification.type, printMessage);

  let initializeParameters: Partial<Protocol.InitializeParams> = {
    rootPath: "/home/egallego/tmp/serapy/CompCert",
    rootUri: "file:///home/egallego/tmp/serapy/CompCert",
    trace: "verbose",
    // workspaceFolders: null,
  };
  let result = await languageServer.initialize(
    initializeParameters,
    '/home/egallego/tmp/serapy/CompCert',
  );
  return languageServer;
}

var version = 0;
let file = "/home/egallego/tmp/serapy/CompCert/file.v";

async function openDoc(languageServer : LS.LanguageServer, text : string) {
  let textDocument = Types.TextDocumentItem.create(
    file,
    "coq",
    version,
    text,
  );

  await languageServer.sendNotification(
    Protocol.DidOpenTextDocumentNotification.type,
    {
      textDocument,
    },
  );
}

async function updateDoc(languageServer : LS.LanguageServer, text : string) {
  version++;

  let textDocument : Types.VersionedTextDocumentIdentifier = Types.VersionedTextDocumentIdentifier.create(
    file,
    version,
  );

  let contentChanges : Protocol.TextDocumentContentChangeEvent[] = [
    { text }
  ]

  console.log("Updating doc");

  await languageServer.sendNotification(
    Protocol.DidChangeTextDocumentNotification.type,
    {
      textDocument,
      contentChanges,
    },
  );
}

let doc1 = `
(* From https://github.com/ejgallego/coq-lsp/issues/487 *)
(* Requires CompCert so that's hard to to test right now *)

Require Import Coqlib.
Require Import Integers.
Require Import Values Memory.
Require Import Cminor CminorSel.
Require Import SelectOp.
Section CMCONSTR.
Variable ge: genv.
Variable sp: val.
Variable e: env.
Variable m: mem.

Definition unary_constructor_sound (cstr: expr -> expr) (sem: val -> val) : Prop
 := forall le a x,eval_expr ge sp e m le a x ->
  exists v, eval_expr ge sp e m le (cstr a) v /\\ Val.lessdef (sem x) v.

About unary_constructor_sound.

Lemma eval_mulimm_base: forall n, unary_constructor_sound
   (mulimm_base n) (fun x => Val.mul x (Vint n)).
induction n.
econstructor.
unfold mulimm_base.
unfold Int.one_bits.
unfold map.
simpl.
`

let doc2 = `
(* From https://github.com/ejgallego/coq-lsp/issues/487 *)
(* Requires CompCert so that's hard to to test right now *)

Require Import Coqlib.
Require Import Integers.
Require Import Values Memory.
Require Import Cminor CminorSel.
Require Import SelectOp.
Section CMCONSTR.
Variable ge: genv.
Variable sp: val.
Variable e: env.
Variable m: mem.

Definition unary_constructor_sound (cstr: expr -> expr) (sem: val -> val) : Prop
 := forall le a x,eval_expr ge sp e m le a x ->
  exists v, eval_expr ge sp e m le (cstr a) v /\\ Val.lessdef (sem x) v.

About unary_constructor_sound.

Lemma eval_mulimm_base: forall n, unary_constructor_sound
   (mulimm_base n) (fun x => Val.mul x (Vint n)).
induction n.
econstructor.
unfold mulimm_base.
unfold Int.one_bits.
unfold map.

`

start().then((ls) => {
    console.log("Starting");
    ls.onNotification(Protocol.PublishDiagnosticsNotification.type, printDiags);
    openDoc(ls, doc1).then(() => {
        setTimeout(() => {
          updateDoc(ls, doc2).then(() => {
            setTimeout(() => {
              ls.exit();
            }, 5000);
          })
        }, 5000)
    });
});
