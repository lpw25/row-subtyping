
type location =
  { start_pos : Lexing.position;
    end_pos : Lexing.position; }

type 'a with_location =
  { desc : 'a;
    location : location; }

type var = string

type binding =
  { name : var; location : location; }

type pattern =
  | Any
  | Var of binding
  | Tuple of pattern list
  | Unit

type constructor = string

type expr_desc =
  | Var of { name : var }
  | Abs of { params : pattern list; body : expr; }
  | Let of
      { pattern : pattern;
        params : pattern list;
        def : expr;
        body : expr; }
  | App of { fn : expr; args : expr list; }
  | Constructor of { constructor : constructor; arg : expr; }
  | Match of { expr: expr; cases : case list; }
  | Unit
  | Tuple of { exprs : expr list; }
  | Ref of { value: expr; }
  | Deref of { reference: expr; }
  | Set of { reference: expr; value: expr; }
  | Sequence of { left : expr; right: expr; }

and expr = expr_desc with_location

and case =
  | Destruct of
      { constructor : constructor;
        arg_pattern : pattern;
        as_binding : binding option;
        body : expr;
        location : location; }
  | Default of
      { binding : binding option;
        body : expr;
        location : location; }

type statement_desc =
  | Definition of
      { pattern : pattern;
        params : pattern list;
        def : expr; }
  | Expr of
      { expr : expr; }

type statement = statement_desc with_location

type phrase_desc =
  | Statement of
      { statement: statement }
  | Directive of
      { directive : string }

type phrase = phrase_desc with_location

(** Debug printing functions *)

type 'a dump =
  Format.formatter -> 'a -> unit

val dump_var : var dump

val dump_binding : binding dump

val dump_constructor : constructor dump

val dump_expr_desc : expr_desc dump

val dump_expr : expr dump

val dump_case : case dump

val dump_statement : statement dump
