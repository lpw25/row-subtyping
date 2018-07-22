
%{

open Ast

let location start_pos end_pos =
  { start_pos; end_pos }

let with_location desc start_pos end_pos =
  let location = location start_pos end_pos in
  { desc; location }

let option_join = function
  | None -> None
  | Some None -> None
  | Some (Some x) -> Some x

%}

/* Keywords */

%token AS
%token END
%token FUN
%token IN
%token LET
%token MATCH
%token REF
%token WITH

/* Identifiers */

%token <string> LIDENT
%token <string> UIDENT

/* Symbols */

%token ARROW
%token BANG
%token BAR
%token COLONEQUALS
%token COMMA
%token EQUALS
%token HASH
%token LPAREN
%token RPAREN
%token SEMI
%token SEMISEMI
%token UNDERSCORE

%start <Ast.phrase> phrase

%on_error_reduce nonempty_list(pattern)

%%

phrase:
  | statement = statement SEMISEMI
      { let desc = Statement { statement } in
        with_location desc $startpos $endpos }
  | HASH directive = LIDENT SEMISEMI
      { let desc = Directive { directive } in
        with_location desc $startpos $endpos }
;

statement:
  | LET pattern = pattern params = loption(parameters) EQUALS def = sequence_expr
      { let desc = Definition { pattern; params; def } in
        with_location desc $startpos $endpos }
  | expr = expr
      { let desc = Expr { expr } in
        with_location desc $startpos $endpos }
;

simple_expr:
  | name = LIDENT
      { let desc = Var{ name; } in
        with_location desc $startpos $endpos }
  | BANG reference = simple_expr
      { let desc = Deref{ reference; } in
        with_location desc $startpos $endpos }
  | LPAREN expr = sequence_expr RPAREN
      { expr }
  | LPAREN RPAREN
      { let desc = Unit in
        with_location desc $startpos $endpos }
  | LPAREN first = expr COMMA rest = separated_nonempty_list(COMMA, expr) RPAREN
      { let exprs = first :: rest in
        let desc = Tuple { exprs } in
        with_location desc $startpos $endpos }
;

expr:
  | expr = simple_expr
      { expr }
  | fn = simple_expr args = nonempty_list(simple_expr)
      { let desc = App{ fn; args } in
        with_location desc $startpos $endpos }
  | constructor = UIDENT arg = simple_expr
      { let desc = Constructor{ constructor; arg } in
        with_location desc $startpos $endpos }
  | MATCH expr = sequence_expr WITH cases = list(case) END
      { let desc = Match{ expr; cases; } in
        with_location desc $startpos $endpos }
  | REF value = simple_expr
      { let desc = Ref{ value; } in
        with_location desc $startpos $endpos }
  | reference = simple_expr COLONEQUALS value = expr
      { let desc = Set{ reference; value; } in
        with_location desc $startpos $endpos }
;

sequence_expr:
  | expr = expr
      { expr }
  | LET pattern = pattern params = loption(parameters) EQUALS def = expr IN body = sequence_expr
      { let desc = Let{ pattern; params; def; body; } in
        with_location desc $startpos $endpos }
  | FUN params = parameters ARROW body = sequence_expr
      { let desc = Abs{ params; body } in
        with_location desc $startpos $endpos }
  | left = expr SEMI right = sequence_expr
      { let desc = Sequence{ left; right; } in
        with_location desc $startpos $endpos }
;

binding:
  | name = LIDENT
      { let location = location $startpos(name) $endpos(name) in
        { name; location } }
;

pattern:
  | UNDERSCORE
      { Any }
  | binding = binding
      { Var binding }
  | LPAREN first = pattern COMMA rest = separated_nonempty_list(COMMA, pattern) RPAREN
      { Tuple (first :: rest) }
  | LPAREN RPAREN
      { Unit }
;

parameters:
  | params = nonempty_list(pattern)
      { params }
;

as_binding:
  | AS UNDERSCORE
      { None }
  | AS binding = binding
      { Some binding }
;

case:
  | BAR constructor = UIDENT arg_pattern = pattern
      as_binding_opt = ioption(as_binding) ARROW body = sequence_expr
        { let location = location $startpos $endpos in
          let as_binding = option_join as_binding_opt in
          Destruct { constructor; arg_pattern; as_binding; body; location } }
  | BAR binding = binding ARROW body = expr
        { let location = location $startpos $endpos in
          let binding = Some binding in
          Default { binding; body; location } }
  | BAR UNDERSCORE ARROW body = expr
        { let location = location $startpos $endpos in
          let binding = None in
          Default { binding; body; location } }
;

