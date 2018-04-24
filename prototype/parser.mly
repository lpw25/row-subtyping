
%{

open Ast

let location start_pos end_pos =
  { start_pos; end_pos }

let mkexpr desc start_pos end_pos =
  let location = location start_pos end_pos in
  { desc; location }

%}

/* Keywords */

%token AS
%token END
%token FUN
%token IN
%token LET
%token MATCH
%token WITH

/* Identifiers */

%token <string> LIDENT
%token <string> UIDENT

/* Symbols */

%token ARROW
%token BAR
%token EQUALS
%token HASH
%token LPAREN
%token RPAREN
%token SEMISEMI
%token UNDERSCORE

%start <Ast.phrase> phrase

%on_error_reduce nonempty_list(binding)

%%

phrase:
  | e = expr SEMISEMI
      { Expr e }
  | HASH dir = LIDENT SEMISEMI
      { Directive dir }
;

simple_expr:
  | name = LIDENT
      { let desc = Var{ name; } in
        mkexpr desc $startpos $endpos }
  | LPAREN expr = expr RPAREN
      { expr }
;

expr:
  | expr = simple_expr
      { expr }
  | LET binding = binding params = loption(parameters) EQUALS def = expr IN body = expr
      { let desc = Let{ binding; params; def; body; } in
        mkexpr desc $startpos $endpos }
  | FUN params = parameters ARROW body = expr
      { let desc = Abs{ params; body } in
        mkexpr desc $startpos $endpos }
  | fn = simple_expr args = nonempty_list(simple_expr)
      { let desc = App{ fn; args } in
        mkexpr desc $startpos $endpos }
  | constructor = UIDENT arg = simple_expr
      { let desc = Constructor{ constructor; arg } in
        mkexpr desc $startpos $endpos }
  | MATCH expr = expr WITH cases = list(case) END
      { let desc = Match{ expr; cases; } in
        mkexpr desc $startpos $endpos }
;

binding:
  | name = LIDENT
      { let location = location $startpos(name) $endpos(name) in
        Named { name; location } }
  | UNDERSCORE
      { Unnamed }
;

parameters:
  | params = nonempty_list(binding)
      { params }
;

as_binding:
  | AS binding = binding
      { binding }
;

case:
  | BAR constructor = UIDENT arg_binding = binding
      as_binding = ioption(as_binding) ARROW body = expr
        { let location = location $startpos $endpos in
          Destruct { constructor; arg_binding; as_binding; body; location } }
  | BAR binding = binding ARROW body = expr
        { let location = location $startpos $endpos in
          Default { binding; body; location } }
;
