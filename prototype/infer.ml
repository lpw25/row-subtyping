
open Ast
open Types

type error =
  | Typing of Type.t * Type.t * Error.t
  | Binding of var

exception Error of location * error

let unify loc t1 t2 =
  match Type.unify t1 t2 with
  | Ok subst -> subst
  | Error err -> raise (Error(loc, Typing(t1, t2, err)))

let lookup loc env v =
  match Env.lookup env v with
  | t -> t
  | exception Not_found -> raise (Error(loc, Binding v))

type 'a binding =
  { name : var; desc : 'a }

type type_binding = Type.t binding

type scheme_binding = Scheme.t binding

type type_bindings = type_binding list

type scheme_bindings = scheme_binding list

let subst_type_bindings subst bindings =
  List.map
    (fun { name; desc } ->
      let desc = Type.subst subst desc in
      { name; desc })
    bindings

let scheme_bindings_of_type_bindings bindings =
  List.map
    (fun { name; desc } ->
      let desc = Scheme.of_type desc in
      { name; desc })
    bindings

let add_scheme_bindings_to_env env bindings =
  List.fold_left
    (fun env { name; desc } -> Env.add name desc env)
    env bindings

let rec is_value (ast : expr) =
  match ast.desc with
  | Var _ -> true
  | Abs _ -> true
  | Let { params; def; body } ->
      let def_value =
        match params with
        | [] -> is_value def
        | _ :: _ -> true
      in
      def_value && is_value body
  | App _ -> false
  | Constructor { arg } -> is_value arg
  | Match { expr; cases } ->
      is_value expr && List.for_all is_value_case cases
  | Unit -> true
  | Tuple { exprs } ->
      List.for_all is_value exprs
  | Ref _ -> false
  | Deref { reference } -> is_value reference
  | Set { reference; value } ->
      is_value reference && is_value value
  | Sequence { right } -> is_value right

and is_value_case = function
  | Destruct { body } -> is_value body
  | Default { body } -> is_value body

let generalize_expr env expr typ =
  if is_value expr then
    Type.generalize env typ
  else
    Scheme.of_type typ

let generalize_bindings env bindings =
  List.map
    (fun { name; desc } ->
      let desc = Type.generalize env desc in
      { name; desc })
    bindings

let generalize_bindings_expr env expr bindings =
  if is_value expr then
    generalize_bindings env bindings
  else
    scheme_bindings_of_type_bindings bindings

let generalize_let env params def bindings =
  match params with
  | [] -> generalize_bindings_expr env def bindings
  | _ :: _ -> generalize_bindings env bindings

let rec infer_pattern = function
  | Any -> Type.fresh_var Kind.type_, []
  | Var { name } ->
      let bound_t = Type.fresh_var Kind.type_ in
      let binding = { name; desc = bound_t } in
      bound_t, [binding]
  | Tuple patterns ->
      let rev_pattern_ts, rev_bindings =
        List.fold_left
          (fun (acc_pattern_ts, acc_bindings) pattern ->
            let pattern_t, pattern_bindings = infer_pattern pattern in
            let pattern_ts = pattern_t :: acc_pattern_ts in
            let bindings = List.rev_append pattern_bindings acc_bindings in
            pattern_ts, bindings)
          ([], []) patterns
      in
      let bindings = List.rev rev_bindings in
      let t =
        match rev_pattern_ts with
        | [] -> assert false
        | last :: rest ->
            List.fold_left
              (fun acc_t pattern_t -> Type.prod pattern_t acc_t)
              last rest
      in
      t, bindings
  | Unit -> Type.unit (), []

let rec infer_expr env (ast : expr) =
  match ast.desc with
  | Var { name } ->
      let scheme = lookup ast.location env name in
      let type_ = Scheme.instantiate scheme in
      Subst.empty, type_
  | Abs { params; body } -> infer_abs env ast.location params body
  | Let { pattern; params; def; body } ->
      let def_subst, def_t = infer_abs env ast.location params def in
      let env = Env.subst def_subst env in
      let match_t, type_bindings = infer_pattern pattern in
      let unify_subst = unify ast.location def_t match_t in
      let env = Env.subst unify_subst env in
      let type_bindings = subst_type_bindings unify_subst type_bindings in
      let scheme_bindings = generalize_let env params def type_bindings in
      let env = add_scheme_bindings_to_env env scheme_bindings in
      let body_subst, body_t = infer_expr env body in
      Subst.compose def_subst body_subst, body_t
  | App { fn; args } ->
      let fn_subst, fn_t = infer_expr env fn in
      let env = Env.subst fn_subst env in
      let result_t = Type.fresh_var Kind.type_ in
      let args_subst, env, args_t =
        List.fold_right
          (fun arg (subst, env, t) ->
            let arg_subst, arg_t = infer_expr env arg in
            let env = Env.subst arg_subst env in
            let t = Type.arrow arg_t (Type.subst arg_subst t) in
            let subst = Subst.compose subst arg_subst in
            subst, env, t)
          args (Subst.empty, env, result_t)
      in
      let fn_t = Type.subst args_subst fn_t in
      let unify_subst = unify ast.location fn_t args_t in
      let t = Type.subst unify_subst result_t in
      let subst =
        Subst.compose fn_subst (Subst.compose args_subst unify_subst)
      in
      subst, t
  | Constructor { constructor; arg } ->
      let arg_subst, arg_t = infer_expr env arg in
      let constructor = Constructor.of_string constructor in
      let constructor_t = Type.constructor constructor arg_t in
      let lower_bound =
        Type.or_ constructor_t
          (Type.bot (Constructor.CSet.cosingleton constructor))
      in
      let upper_bound = Type.top Constructor.CSet.universe in
      let range = Type.fresh_var (Kind.range lower_bound upper_bound) in
      let t = Type.variant range in
      arg_subst, t
  | Match { expr; cases } ->
      let expr_subst, expr_t = infer_expr env expr in
      let env = Env.subst expr_subst env in
      let result_t = Type.fresh_var Kind.type_ in
      let cases_subst, final_t =
        List.fold_left
          (fun (subst, incoming_t) case ->
            let env = Env.subst subst env in
            let result_t = Type.subst subst result_t in
            let case_subst, incoming_t = infer_case env result_t incoming_t case in
            let subst = Subst.compose subst case_subst in
            subst, incoming_t)
          (Subst.empty, expr_t) cases
      in
      let result_t = Type.subst cases_subst result_t in
      let empty_t =
        let lower_bound = Type.bot Constructor.CSet.universe in
        let upper_bound = Type.bot Constructor.CSet.universe in
        let range = Type.fresh_var (Kind.range lower_bound upper_bound) in
        Type.variant range
      in
      let empty_subst = unify ast.location final_t empty_t in
      let result_t = Type.subst empty_subst result_t in
      let subst =
        Subst.compose expr_subst
          (Subst.compose cases_subst empty_subst)
      in
      subst, result_t
  | Unit ->
      Subst.empty, Type.unit ()
  | Tuple { exprs } ->
      let subst, rev_types =
        List.fold_left
          (fun (subst, rev_types) expr ->
            let env = Env.subst subst env in
            let expr_subst, expr_t = infer_expr env expr in
            let subst = Subst.compose subst expr_subst in
            subst, expr_t :: rev_types)
          (Subst.empty, []) exprs
      in
      let result_t =
        match rev_types with
        | [] -> assert false
        | last :: rest ->
            List.fold_left
              (fun right_t left_t ->
                Type.prod left_t right_t)
              last rest
      in
      subst, result_t
  | Ref { value } ->
      let subst, value_t = infer_expr env value in
      let result_t = Type.ref value_t in
      subst, result_t
  | Deref { reference } ->
      let reference_subst, reference_t = infer_expr env reference in
      let result_t = Type.fresh_var Kind.type_ in
      let ref_t = Type.ref result_t in
      let ref_subst = unify ast.location ref_t reference_t in
      let result_t = Type.subst ref_subst result_t in
      let subst = Subst.compose reference_subst ref_subst in
      subst, result_t
  | Set { reference; value } ->
      let reference_subst, reference_t = infer_expr env reference in
      let env = Env.subst reference_subst env in
      let value_subst, value_t = infer_expr env value in
      let ref_t = Type.ref value_t in
      let ref_subst = unify reference.location ref_t reference_t in
      let subst =
        Subst.compose reference_subst
          (Subst.compose value_subst ref_subst)
      in
      subst, Type.unit ()
  | Sequence { left; right } ->
      let left_subst, left_t = infer_expr env left in
      let unit_subst = unify left.location left_t (Type.unit ()) in
      let left_subst = Subst.compose left_subst unit_subst in
      let env = Env.subst left_subst env in
      let right_subst, right_t = infer_expr env right in
      let subst = Subst.compose left_subst right_subst in
      subst, right_t

and infer_case env result_t incoming_t case =
  match case with
  | Destruct { constructor; arg_pattern; as_binding; body; location } ->
      let constructor = Constructor.of_string constructor in
      let arg_t, type_bindings = infer_pattern arg_pattern in
      let constructor_t = Type.constructor constructor arg_t in
      let as_constructor_t =
        Type.fresh_var
          (Kind.row (Constructor.CSet.singleton constructor))
      in
      let other_t =
        Type.fresh_var
          (Kind.row (Constructor.CSet.cosingleton constructor))
      in
      let match_t =
        let lower_bound = Type.bot Constructor.CSet.universe in
        let upper_bound =
          Type.or_ (Type.meet constructor_t as_constructor_t) other_t
        in
        let range = Type.fresh_var (Kind.range lower_bound upper_bound) in
        Type.variant range
      in
      let as_t =
        let lower_bound =
          Type.or_ as_constructor_t
            (Type.bot (Constructor.CSet.cosingleton constructor))
        in
        let upper_bound = Type.top Constructor.CSet.universe in
        let range = Type.fresh_var (Kind.range lower_bound upper_bound) in
        Type.variant range
      in
      let rest_t =
        let lower_bound =
          Type.or_ other_t
            (Type.bot (Constructor.CSet.singleton constructor))
        in
        let upper_bound = Type.top Constructor.CSet.universe in
        let range = Type.fresh_var (Kind.range lower_bound upper_bound) in
        Type.variant range
      in
      let match_subst = unify location match_t incoming_t in
      let type_bindings = subst_type_bindings match_subst type_bindings in
      let as_t = Type.subst match_subst as_t in
      let rest_t = Type.subst match_subst rest_t in
      let result_t = Type.subst match_subst result_t in
      let env = Env.subst match_subst env in
      let scheme_bindings = scheme_bindings_of_type_bindings type_bindings in
      let env = add_scheme_bindings_to_env env scheme_bindings in
      let env =
        match as_binding with
        | None -> env
        | Some { name; location } ->
            let scheme = Scheme.of_type as_t in
            Env.add name scheme env
      in
      let body_subst, body_t = infer_expr env body in
      let rest_t = Type.subst body_subst rest_t in
      let result_t = Type.subst body_subst result_t in
      let result_subst = unify location body_t result_t in
      let rest_t = Type.subst result_subst rest_t in
      let subst =
        Subst.compose match_subst
          (Subst.compose body_subst result_subst)
      in
      subst, rest_t
  | Default { binding; body; location } ->
      let rest_t =
        let lower_bound = Type.bot Constructor.CSet.universe in
        let upper_bound = Type.bot Constructor.CSet.universe in
        let range = Type.fresh_var (Kind.range lower_bound upper_bound) in
        Type.variant range
      in
      let env =
        match binding with
        | None -> env
        | Some { name; location } ->
            let scheme = Scheme.of_type incoming_t in
            Env.add name scheme env
      in
      let body_subst, body_t = infer_expr env body in
      let result_t = Type.subst body_subst result_t in
      let result_subst = unify location body_t result_t in
      let subst = Subst.compose body_subst result_subst in
      subst, rest_t

and infer_abs env loc params body =
  let body_t = Type.fresh_var Kind.type_ in
  let env, t =
    let rec loop env patterns =
      match patterns with
      | [] -> env, body_t
      | pattern :: rest ->
          let param_t, type_bindings = infer_pattern pattern in
          let scheme_bindings =
            scheme_bindings_of_type_bindings type_bindings
          in
          let env = add_scheme_bindings_to_env env scheme_bindings in
          let env, t = loop env rest in
          let t = Type.arrow param_t t in
          env, t
    in
    loop env params
  in
  let subst, s = infer_expr env body in
  let subst = Subst.compose subst (unify loc s body_t) in
  subst, Type.subst subst t

let infer env (x : statement) =
  match x.desc with
  | Definition { pattern; params; def } ->
      let def_subst, def_t = infer_abs env x.location params def in
      let env = Env.subst def_subst env in
      let match_t, type_bindings = infer_pattern pattern in
      let unify_subst = unify x.location def_t match_t in
      let env = Env.subst unify_subst env in
      let type_bindings = subst_type_bindings unify_subst type_bindings in
      let scheme_bindings = generalize_let env params def type_bindings in
      let env = add_scheme_bindings_to_env env scheme_bindings in
      let result =
        List.map (fun {name; desc} -> (Some name, desc)) scheme_bindings
      in
      env, result
  | Expr { expr } ->
      let subst, t = infer_expr env expr in
      let env = Env.subst subst env in
      let scheme = generalize_expr env expr t in
      env, [None, scheme]
