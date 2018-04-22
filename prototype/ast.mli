
type location =
  { start_pos : Lexing.position;
    end_pos : Lexing.position; }

type var = string

type binding =
  | Unnamed
  | Named of { name : string; location : location; }

type constructor = string

type expr_desc =
  | Var of { name : var }
  | Abs of { params : binding list; body : expr; }
  | Let of
      { binding : binding;
        params : binding list;
        def : expr;
        body : expr; }
  | App of { fn : expr; args : expr list; }
  | Constructor of { constructor : constructor; arg : expr; }
  | Match of { expr: expr; cases : case list; }

and expr =
  { desc : expr_desc;
    location : location; }

and case =
  { constructor : constructor;
    arg_binding : binding;
    as_binding : binding option;
    body : expr; }

type phrase =
  | Expr of expr
  | Directive of string

(** Debug printing functions *)

type 'a dump =
  Format.formatter -> 'a -> unit

val dump_var : var dump

val dump_binding : binding dump

val dump_constructor : constructor dump

val dump_expr_desc : expr_desc dump

val dump_expr : expr dump

val dump_case : case dump
