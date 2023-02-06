/* Adapted from the wonderful https://github.com/realworldocaml/book/ */
/* License of this code was UNLICENSE, we now put it under the coq-lsp licence */

%{
open Json

let lexing_to_point { Lexing.pos_lnum; pos_bol; pos_cnum; _ } =
  let line = pos_lnum - 1 in
  let character = pos_cnum - pos_bol in
  let offset = pos_cnum - 1 in
  Lang.Point.{ line; character; offset }

let lexing_to_range (start, end_) =
  let start = lexing_to_point start in
  let end_ = lexing_to_point end_ in
  Lang.Range.{start; end_}

let make ~loc v =
  let range = lexing_to_range loc in
  CAst.make ~range v

%}

%token <int> INT
%token <float> FLOAT
/* %token <string> ID */
%token <string * Lexing.position * Lexing.position> STRING
%token TRUE
%token FALSE
%token NULL
%token LEFT_BRACE
%token RIGHT_BRACE
%token LEFT_BRACK
%token RIGHT_BRACK
%token COLON
%token COMMA
%token EOF

%start <Json.value option> prog
%%

prog:
  | v = value { Some v }
  | EOF       { None   } ;

value:
  | LEFT_BRACE; obj = obj_fields; RIGHT_BRACE { make ~loc:$loc @@ Assoc obj  }
  | LEFT_BRACK; vl = list_fields; RIGHT_BRACK { make ~loc:$loc @@ List vl    }
  | s = STRING                                { let k, s, e = s in (make ~loc:(s,e) @@ String k) }
  | i = INT                                   { make ~loc:$loc @@ Int i      }
  | x = FLOAT                                 { make ~loc:$loc @@ Float x    }
  | TRUE                                      { make ~loc:$loc @@ Bool true  }
  | FALSE                                     { make ~loc:$loc @@ Bool false }
  | NULL                                      { make ~loc:$loc @@ Null       } ;

obj_fields:
    obj = separated_list(COMMA, obj_field)    { obj } ;

obj_field:
    k = STRING; COLON; v = value              { let k, s, e = k in (make ~loc:(s,e) k, v) } ;

list_fields:
    vl = separated_list(COMMA, value)         { vl } ;
