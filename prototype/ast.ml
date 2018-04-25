
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
  | Unit

and expr =
  { desc : expr_desc;
    location : location; }

and case =
  | Destruct of
      { constructor : constructor;
        arg_binding : binding;
        as_binding : binding option;
        body : expr;
        location : location; }
  | Default of
      { binding : binding;
        body : expr;
        location : location; }

type definition =
  { binding : binding;
    params : binding list;
    def : expr;
    location : location; }

type phrase =
  | Definition of definition
  | Directive of string

type 'a dump =
  Format.formatter -> 'a -> unit

let dump_list dump ppf list =
  let pp_sep ppf () = Format.fprintf ppf "@ " in
  Format.pp_print_list ~pp_sep dump ppf list

let dump_option dump ppf option =
  match option with
  | None -> Format.fprintf ppf "None"
  | Some x -> Format.fprintf ppf "Some %a" dump x

let dump_var ppf var =
  Format.fprintf ppf "%s" var

let dump_constructor ppf constructor =
  Format.fprintf ppf "%s" constructor

let dump_binding ppf = function
  | Unnamed ->
      Format.fprintf ppf "Unnamed"
  | Named { name; location } ->
      Format.fprintf ppf "%a" dump_var name

let dump_constructor ppf constructor =
  Format.fprintf ppf "%s" constructor

let rec dump_expr_desc ppf = function
  | Var { name } ->
      Format.fprintf ppf "Var %a" dump_var name
  | Abs { params; body; } ->
      Format.fprintf ppf
        "@[<v 2>Abs@ Params @[<h>%a@]@ @[<v 2>Body@ %a@]@]"
        (dump_list dump_binding) params dump_expr body
  | Let { binding; params; def; body; } ->
      Format.fprintf ppf
        "@[<v 2>Let@ Binding %a@ Params @[<h>%a@]@ \
         @[<v 2>Def@ %a@]@ @[<v 2>Body@ %a@]@]"
        dump_binding binding (dump_list dump_binding) params
        dump_expr def dump_expr body
  | App { fn; args; } ->
      Format.fprintf ppf
        "@[<v 2>App@ @[<v 2>Fn@ %a@]@ @[<v 2>Args %a@]@]"
        dump_expr fn (dump_list dump_expr) args
  | Constructor { constructor; arg; } ->
      Format.fprintf ppf
        "@[<v 2>Constructor %a@ @[<v 2>Arg@ %a@]@]"
        dump_constructor constructor dump_expr arg
  | Match { expr; cases; } ->
      Format.fprintf ppf
        "@[<v 2>Match@ @[<v 2>Expr@ %a@]@ @[<v 2>Cases@ %a@]@]"
        dump_expr expr (dump_list dump_case) cases
  | Unit ->
      Format.fprintf ppf "Unit"

and dump_expr ppf expr =
  dump_expr_desc ppf expr.desc

and dump_case ppf = function
  | Destruct { constructor; arg_binding; as_binding; body } ->
      Format.fprintf ppf
        "@[<v 2>Destruct@ Constructor %a@ Arg_binding %a@ As_binding %a@ @[<v 2>Body@ %a@]@]"
        dump_constructor constructor dump_binding arg_binding
        (dump_option dump_binding) as_binding dump_expr body
  | Default { binding; body } ->
      Format.fprintf ppf
        "@[<v 2>Default@ Binding %a@ @[<v 2>Body@ %a@]@]"
        dump_binding binding dump_expr body

let dump_definition ppf { binding; params; def; } =
  Format.fprintf ppf
    "@[<v 2>Definition@ Binding %a@ Params @[<h>%a@]@ \
     @[<v 2>Def@ %a@]@]"
    dump_binding binding (dump_list dump_binding) params dump_expr def
