
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

let rec infer_expr env ast =
  match ast.desc with
  | Var { name } ->
      let scheme = lookup ast.location env name in
      let type_ = Scheme.instantiate scheme in
      Subst.empty, type_
  | Abs { params; body } -> infer_abs env ast.location params body
  | Let { binding; params; def; body } ->
      let def_subst, def_t = infer_abs env ast.location params def in
      let env = Env.subst def_subst env in
      let scheme = Type.generalize env def_t in
      let env =
        match binding with
        | Unnamed -> env
        | Named { name; location } -> Env.add name scheme env
      in
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

and infer_case env result_t incoming_t case =
  match case with
  | Destruct { constructor; arg_binding; as_binding; body; location } ->
      let constructor = Constructor.of_string constructor in
      let arg_t = Type.fresh_var Kind.type_ in
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
      let arg_t = Type.subst match_subst arg_t in
      let as_t = Type.subst match_subst as_t in
      let rest_t = Type.subst match_subst rest_t in
      let env = Env.subst match_subst env in
      let env =
        match arg_binding with
        | Unnamed -> env
        | Named { name; location } ->
            let scheme = Scheme.of_type arg_t in
            Env.add name scheme env
      in
      let env =
        match as_binding with
        | None | Some Unnamed -> env
        | Some (Named { name; location }) ->
            let scheme = Scheme.of_type as_t in
            Env.add name scheme env
      in
      let body_subst, body_t = infer_expr env body in
      let rest_t = Type.subst body_subst rest_t in
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
        | Unnamed -> env
        | Named { name; location } ->
            let scheme = Scheme.of_type incoming_t in
            Env.add name scheme env
      in
      let body_subst, body_t = infer_expr env body in
      let result_subst = unify location body_t result_t in
      let subst = Subst.compose body_subst result_subst in
      subst, rest_t

and infer_abs env loc params body =
  let body_t = Type.fresh_var Kind.type_ in
  let env, t =
    let rec loop env bindings =
      match bindings with
      | [] -> env, body_t
      | binding :: rest ->
          let param_t = Type.fresh_var Kind.type_ in
          let env =
            match binding with
            | Unnamed -> env
            | Named { name; location } ->
                let scheme = Scheme.of_type param_t in
                Env.add name scheme env
          in
          let env, t = loop env rest in
          let t = Type.arrow param_t t in
          env, t
    in
    loop env params
  in
  let subst, s = infer_expr env body in
  let subst = Subst.compose subst (unify loc s body_t) in
  subst, Type.subst subst t


let infer env ast =
  let _, type_ = infer_expr env ast in
  type_
