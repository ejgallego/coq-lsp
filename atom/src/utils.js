"use strict";

const { Convert } = require("atom-languageclient");
const dk = require("./dedukti-editor-view");
const fs = require('fs');

class Utils {

  static initialize(dedukti_client){
    this.view = dedukti_client.deduktiEditorView;

    this.getkeymaps();
    this.addViewOpener(dedukti_client);
    this.addKeyBindings();
  }

  static addViewOpener(dedukti_client){ // how the view is handled by Atom

    dedukti_client._disposable.add(atom.workspace.addOpener( (uri) => {
      if(uri === this.view.getURI()){ //We want our opener to be active only for this uri
        return this.view; // We return the view
      }
    }));

    dedukti_client._disposable.add(
      atom.workspace.observeActiveTextEditor(editor => {
        //
        if (typeof editor != "undefined"){
          let scopeName = editor.getGrammar().scopeName;
          if(dedukti_client.getGrammarScopes().includes(scopeName)){
            atom.workspace.open(this.view.getURI()); // if it is not alrealdy opened, we open the view
            this.adaptViewToEditor(dedukti_client); // we just update it.
          }
          else{
            atom.workspace.hide(this.view.getURI()); //if not a .dk file, the view is closed
          }
        }
        else{
          atom.workspace.hide(this.view.getURI()); //if not a .dk file, the view is closed
        }
      })
    );
  }

  static addKeyBindings(){ // add some keybindings

    atom.commands.add("atom-workspace", {
      "dedukti-editor:next": () => this.view.nextFocus() // ALT down
    });
    atom.commands.add("atom-workspace", {
      "dedukti-editor:last": () => this.view.lastFocus() // ALT up
    });

  }

  static addeventbutton() { // add some listener for buttons

    this.view.but2.addEventListener("click", () => {
      this.view.nextFocus();
    });

    this.view.but3.addEventListener("click", () => {
      this.view.lastFocus();
    });

    //TODO ACTIVATE AUTOMATIC UPDATE
  }

  static updateDiagnostics(params) {
    // every variable we need.
    let path = Convert.uriToPath(params.uri);
    let i = 0;
    var mydiagnostics = new Array();
    let text_editors = atom.workspace.getTextEditors(); // we get all active editors in atom

    //we want to get the editor concerned by the diagnostics
    let editor = this.getEditorDiagnosed(text_editors, path);

    if (editor === "") {
      //the editor concerned by the diagnostics is not open.
      return [];
    } else {
      //we destroy previous color markers on this editor
      this.destroyDiagnosticsMarkers(params,editor);
    }

    // Then we put new color markers on this editor
    this.destroyDataView(params);

    for (i = 0; i < params.diagnostics.length; i++) {
      if (params.diagnostics[i].message === "OK") {

        this.processDataView(params,i,path);
        //  Hence in Green

        if(atom.config.get("dedukti-editor.style") === "bar_mode"){ // style manager
          this.colorMarkEditor("Completed_lines", "line-number", editor, params,i);
        } else if(atom.config.get("dedukti-editor.style") === "coloredline_mode"){
          this.colorMarkEditor("Completed_lines_colored_mode", "text", editor, params,i);
        }

      } else {

        this.processDataView(params,i,path);
        // Hence, in Red
        if(atom.config.get("dedukti-editor.style") === "bar_mode"){ // style manager
          this.colorMarkEditor("Failed_line", "line-number", editor, params,i);
        } else if(atom.config.get("dedukti-editor.style") === "coloredline_mode"){
          this.colorMarkEditor("Failed_line", "text", editor, params,i);
        }

        // we want those message to be displayed on the diagnostics panel.
        mydiagnostics.push(params.diagnostics[i]);
      }
    }

    // we return error messages to be displayed on the diagnostics panel.
    return mydiagnostics;
  }

  static getEditorDiagnosed(text_editors, path){

    //we want to get the editor concerned by the diagnostics
    let j= 0;
    let editor = "";
    for (j = 0; j < text_editors.length; j++) {
      let text_editor_path = text_editors[j].getPath();
      if (text_editor_path == path) {
        editor = text_editors[j];
      }
    }
    return editor;

  }

  static destroyDiagnosticsMarkers(params,editor){

    //we destroy previous color markers on this editor
    /*
    (**1) This is a workaround specific to dedukti until modifications are made upstream in the server.
    */
    let z = 0;
    if(params.diagnostics.length != 1 || params.diagnostics[0].message != "Parse error."){ //when a parse error occurs, everything diseapper, we don't want that (**1)
      let marker_color = editor.findMarkers({ persistent: false });
      for (z = 0; z < marker_color.length; z++) {
        marker_color[z].destroy();
      }
    }
  }

  static destroyDataView(params){
    if(params.diagnostics.length != 1 || params.diagnostics[0].message!="Parse error."){  //when a parse error occurs, everything disappears, we don't want that (**1)
      this.view.FocusView = []; // We forget every diagnostic sent before by the server.
    }
  }

  static processDataView(params,i,path){

    if (params.diagnostics[i].goal_info != null) { // We get the hypothesis and the goal if there is something to display
      let j=0;
      // We define the variables we need
      let curentobj = "";
      let hypothesislist = [];
      let goallist = [];

      for(j=0;j<params.diagnostics[i].goal_info.goals.length;j++){ // for each diagnostics, we are looking for the main goal
        if(  params.diagnostics[i].goal_info.focus === params.diagnostics[i].goal_info.goals[j].gid ){
          curentobj      = params.diagnostics[i].goal_info.goals[j].type; //we take from the main goal and his hypothesis and his type
          hypothesislist = params.diagnostics[i].goal_info.goals[j].hyps;
        }
        goallist.push(params.diagnostics[i].goal_info.goals[j].type); //in any case, we add the goal in the goalslist
      }

      this.view.FocusView.push({ // we register within our memory
        path: path,     // the file path
        range: params.diagnostics[i].range,       // the range to attribuate to this view
        goal: curentobj,            // the current goal
        hypothesis: hypothesislist,  // the list of hypothesis
        goals : goallist            // the list of unresolved goals
      });
    }

  }

  static colorMarkEditor(mode, type, editor, params,i){
    var marker = editor.markScreenRange([
      [
        params.diagnostics[i].range.start.line,
        params.diagnostics[i].range.start.character
      ],
      [
        params.diagnostics[i].range.end.line,
        params.diagnostics[i].range.end.character
      ]
    ]);

    marker.setProperties({ persistent: false, invalidate: "never" }); //The color is diseappearing when 'touch'

    let decoration = editor.decorateMarker(marker, {
      type: type,
      class: mode
    });

  }

  static add_editor_event(editor) {
    // add some listener for cursor in an editor

    this.add_cursor_event(editor); // the cursor event which update the view
    this.add_parser_event(editor); // the parser event which update the buffer with unicode symbols.

  }

  static add_cursor_event(editor){

    if(typeof this.currentcursor != "undefined"){ //We check if it is the first time a file is opened
      this.currentcursor.dispose(); //We don't need to listen the last file cursor
    }

    //When the user move the cursor, we update the view
    this.currentcursor = editor.onDidChangeSelectionRange(selection => {
      this.view.updateView(selection, editor);
    });

  }

  static add_parser_event(editor){
    if(typeof this.currentEditorUnicode != "undefined"){ //We check if it is the first time a file is opened
      this.currentEditorUnicode.dispose(); //We don't need to listen the last file cursor
    }

    //When the user changes the text, we check the new changes with our parser.
    this.currentEditorUnicode = editor.onDidStopChanging( (data) => {
      let i = 0;
      let j = 0;
      for(j=0;j<data.changes.length;j++){ // For each change
        for(i=0;i<this.parser.length;i++){ // For each parser traduction
          editor.scanInBufferRange(
            new RegExp(this.parser[i].regex), // get the regex associated with the traduction parser
            [
              [data.changes[j].newRange.start.row, 0],
              [data.changes[j].newRange.end.row +1, data.changes[0].newRange.end.colum]
            ], // scan uniquely next where changes have been made
            (iterator) =>{
              iterator.replace(this.parser[i].unicode);  // replace the regex found by a unicode symbol
            }
          );
        }
      }
    });


    let i =0; // In case it is the first time the file is opened, we check all the content of the file.
    for(i=0;i<this.parser.length;i++){
      editor.scan(
        new RegExp(this.parser[i].regex,'g'), // the g argument is used to make sure the scan will find and replace every occurence of the regex
        (iterator) => {
          iterator.replace(this.parser[i].unicode);
        }
      );
    }

  }

  static adaptViewToEditor(dedukti_client){ // We update the view when we switch from an editor to another one. // NOT HERE OK

    if (this.view.isInitialized()){ // We check it is correctly initialized
      this.add_editor_event(atom.workspace.getActiveTextEditor()); // add cursor event
    }
    else{
      this.view.initialize();
      this.add_editor_event(atom.workspace.getActiveTextEditor()); // add cursor event
      this.addeventbutton(); // add events for the buttons within the view
    }

  }

  static getkeymaps(){
    // We read the parser.json file and put the result in our variable.
    this.parser = require("./config/parser.json")
  }
}


exports.default = Utils;
