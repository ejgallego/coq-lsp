// Edition facilities for Coq files
import {
  TextEditor,
  Position,
  Range,
  Selection,
  TextEditorRevealType,
} from "vscode";

function setSelection(editor: TextEditor, newCursor: Position) {
  editor.selection = new Selection(newCursor, newCursor);

  // Is there not a better way?
  editor.revealRange(
    new Range(newCursor, newCursor),
    TextEditorRevealType.InCenterIfOutsideViewport
  );
}

export function sentenceBack(editor: TextEditor) {
  // Slice from the beginning of the document
  let cursor = editor.selection.active;
  let range = new Range(editor.document.positionAt(0), cursor);
  let text = editor.document.getText(range);

  // what a hack
  let regres = text.match(/\.\s+/g);
  if (regres) {
    let match = regres.at(-2) || "";
    var index = 0;
    if (match == regres.at(-1) || "") {
      let idx = text.lastIndexOf(match);
      index = text.lastIndexOf(match, idx - 1) + match.length;
    } else {
      index = text.lastIndexOf(match) + match.length;
    }
    let newCursor = editor.document.positionAt(index);
    setSelection(editor, newCursor);
  }
}

export function sentenceNext(editor: TextEditor) {
  // Slice to the end of the document
  let cursor = editor.selection.active;
  let lastLine = editor.document.lineCount - 1;
  let lastPos = editor.document.lineAt(lastLine).range.end;
  let range = new Range(cursor, lastPos);
  let text = editor.document.getText(range);

  // get the offset of the first match
  let regres = text.match(/\.\s+/);
  if (regres) {
    regres;
    let match: any = regres[0];
    let index = regres.index + match.length;
    let newCursor = editor.document.positionAt(
      editor.document.offsetAt(cursor) + index
    );
    setSelection(editor, newCursor);
  }
}
