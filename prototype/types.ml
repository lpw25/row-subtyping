module Constructor : sig

  type t

  val of_string : string -> t

  val to_string : t -> string

  module CSet : sig

    type constructor = t

    type t

    val empty : t

    val universe : t

    val singleton : constructor -> t

    val cosingleton : constructor -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val is_empty : t -> bool

    val is_universe : t -> bool

    val is_finite : t -> bool

    type proj_representation =
      | Diff of constructor list
      | Absolute of constructor list

    val proj_representation : t -> t -> proj_representation

    val print_raw : t -> unit

  end

end = struct

  type t = string

  let of_string s = s

  let to_string s = s

  module StringSet = Set.Make(String)

  module CSet = struct

    type constructor = t

    type t =
      | Finite : StringSet.t -> t
      | Cofinite : StringSet.t -> t

    let empty = Finite StringSet.empty

    let universe = Cofinite StringSet.empty

    let singleton x =
      Finite (StringSet.singleton x)

    let cosingleton x =
      Cofinite (StringSet.singleton x)

    let union cs1 cs2 =
      match cs1, cs2 with
      | Finite s1, Finite s2 -> Finite (StringSet.union s1 s2)
      | Finite s1, Cofinite s2 -> Cofinite (StringSet.diff s2 s1)
      | Cofinite s1, Finite s2 -> Cofinite (StringSet.diff s1 s2)
      | Cofinite s1, Cofinite s2 -> Cofinite (StringSet.inter s1 s2)

    let inter cs1 cs2 =
      match cs1, cs2 with
      | Finite s1, Finite s2 -> Finite (StringSet.inter s1 s2)
      | Finite s1, Cofinite s2 -> Finite (StringSet.diff s1 s2)
      | Cofinite s1, Finite s2 -> Finite (StringSet.diff s2 s1)
      | Cofinite s1, Cofinite s2 -> Cofinite (StringSet.union s1 s2)

    let diff cs1 cs2 =
      match cs1, cs2 with
      | Finite s1, Finite s2 -> Finite (StringSet.diff s1 s2)
      | Finite s1, Cofinite s2 -> Finite (StringSet.inter s1 s2)
      | Cofinite s1, Finite s2 -> Cofinite (StringSet.union s1 s2)
      | Cofinite s1, Cofinite s2 -> Finite (StringSet.diff s2 s1)

    let equal cs1 cs2 =
      match cs1, cs2 with
      | Finite s1, Finite s2 -> StringSet.equal s1 s2
      | Finite _, Cofinite _ -> false
      | Cofinite _, Finite _ -> false
      | Cofinite s1, Cofinite s2 -> StringSet.equal s1 s2

    let is_empty cs =
      match cs with
      | Finite s -> StringSet.is_empty s
      | Cofinite _ -> false

    let is_universe cs =
      match cs with
      | Finite _ -> false
      | Cofinite s -> StringSet.is_empty s

    let is_finite cs =
      match cs with
      | Finite _ -> true
      | Cofinite _ -> false

    type proj_representation =
      | Diff of constructor list
      | Absolute of constructor list

    let proj_representation cs1 cs2 =
      match cs2 with
      | Finite s2 -> Absolute (StringSet.elements s2)
      | Cofinite s2 ->
          match cs1 with
          | Finite s1 -> Diff (StringSet.elements (StringSet.inter s1 s2))
          | Cofinite s1 -> Diff (StringSet.elements (StringSet.diff s2 s1))

    let print_raw cs =
      match cs with
      | Finite s ->
          Format.printf "[ ";
          StringSet.iter (fun c -> Format.printf "%s; " c) s;
          Format.printf "]"
      | Cofinite s ->
          Format.printf "[<> ";
          StringSet.iter (fun c -> Format.printf "%s; " c) s;
          Format.printf "]"

  end

end

module Var : sig

  type t

  val fresh : unit -> t

  val to_string : t -> string

  val equal : t -> t -> bool

  module Set : Set.S with type elt = t

  module Map : Map.S with type key = t

end = struct

  type t = int

  let fresh =
    let counter = ref 0 in
    fun () ->
      incr counter;
      !counter

  let to_string = string_of_int

  let equal (x : t) (y : t) =
    x = y

  module Ord = struct
    type t = int
    let compare (x : t) (y : t) = Pervasives.compare x y
  end

  module Set = Set.Make(Ord)

  module Map = Map.Make(Ord)

end

module rec TypeT : sig

  type desc =
    | Var of Var.t
    | Constructor of Constructor.t * t
    | Or of Constructor.CSet.t * t * Constructor.CSet.t * t
    | Proj of Constructor.CSet.t * t * Constructor.CSet.t
    | Row of t
    | Variant of t
    | Arrow of t * t
    | Unit
    | Top of Constructor.CSet.t
    | Bot of Constructor.CSet.t
    | Meet of t * t
    | Join of t * t

  and t =
    { desc : desc;
      kind : KindT.t; }

end = TypeT

and KindT : sig

  type t =
    | Type
    | Row of Constructor.CSet.t
    | Range of TypeT.t * TypeT.t

end = KindT

module Error = struct

  type t = unit

end

module Result = struct

  type 'a t = ('a, Error.t) result

  let return x = Ok x

  let error e = Error e

  let bind m f =
    match m with
    | Ok x -> f x
    | Error _ as err -> err

  let map m f =
    match m with
    | Ok x -> Ok (f x)
    | Error _ as err -> err

  let (>>=) = bind

  let (>>|) = map

end

module rec Type : sig

  include module type of struct include TypeT end

  val var : Var.t -> Kind.t -> t

  val fresh_var : Kind.t -> t

  val constructor : Constructor.t -> t -> t

  val or_ : t -> t -> t

  val proj : t -> Constructor.CSet.t -> t

  val row : t -> t

  val variant : t -> t

  val arrow : t -> t -> t

  val unit : unit -> t

  val top : Constructor.CSet.t -> t

  val bot : Constructor.CSet.t -> t

  val meet : t -> t -> t

  val join : t -> t -> t

  val free_variables : t -> Var.Set.t

  val subst_types : Subst.t -> t -> t

  val subst_ranges : Subst.t -> t -> t

  val subst_row_covariant : Subst.t -> t -> t

  val subst_row_contravariant : Subst.t -> t -> t

  val subst_row_invariant : Subst.t -> t -> t

  val subst : Subst.t -> t -> t

  val subst_vars : Var.t Var.Map.t -> t -> t

  val generalize : Env.t -> t -> Scheme.t

  val unify_types : t -> t -> Subst.t Result.t

  val unify_ranges : t -> t -> Subst.t Result.t

  val unify_row : t -> t -> Subst.t Result.t

  val biunify_row : t -> t -> Subst.t Result.t

  val unify : t -> t -> Subst.t Result.t

  val normalize : desc -> desc

end = struct

  include TypeT

  let var v kind =
    let desc = Var v in
    { desc; kind }

  let fresh_var kind =
    let v = Var.fresh () in
    var v kind

  let constructor c t =
    let desc = Constructor(c, t) in
    let kind = Kind.Row (Constructor.CSet.singleton c) in
    { desc; kind }

  let or_ t1 t2 =
    match t1.kind, t2.kind with
    | (Type | Range _), _ -> assert false
    | _, (Type | Range _) -> assert false
    | Row cs1, Row cs2 ->
        let desc = Or(cs1, t1, cs2, t2) in
        let kind = Kind.Row (Constructor.CSet.union cs1 cs2) in
        { desc; kind }

  let proj t cs1 =
    match t.kind with
    | Type | Range _ -> assert false
    | Row cs2 ->
        let desc = Proj(cs2, t, cs1) in
        let kind = Kind.Row cs1 in
        { desc; kind }

  let row t =
    let desc = Row t in
    let kind = Kind.Range(t, t) in
    { desc; kind }

  let variant t =
    let desc = Variant t in
    let kind = Kind.Type in
    { desc; kind }

  let arrow t1 t2 =
    let desc = Arrow(t1, t2) in
    let kind = Kind.Type in
    { desc; kind }

  let unit () =
    let desc = Unit in
    let kind = Kind.Type in
    { desc; kind }

  let top cs =
    let desc = Top cs in
    let kind = Kind.Row cs in
    { desc; kind }

  let bot cs =
    let desc = Bot cs in
    let kind = Kind.Row cs in
    { desc; kind }

  let meet t1 t2 =
    let desc = Meet(t1, t2) in
    let kind = t1.kind in
    { desc; kind }

  let join t1 t2 =
    let desc = Join(t1, t2) in
    let kind = t1.kind in
    { desc; kind }

  let rec free_variables_desc = function
    | Top _ | Bot _ | Unit ->
        Var.Set.empty
    | Var v ->
        Var.Set.singleton v
    | Constructor(_, t) | Proj(_, t, _) | Row t | Variant t ->
        free_variables t
    | Or(_, t1, _, t2) | Arrow(t1, t2) | Meet(t1, t2) | Join(t1, t2) ->
        Var.Set.union (free_variables t1) (free_variables t2)

  and free_variables t =
    Var.Set.union
      (free_variables_desc t.desc) (Kind.free_variables t.kind)

  let rec subst_types s t =
    let kind = Kind.subst s t.kind in
    let desc = t.desc in
    match desc with
    | Var v -> begin
        match Subst.find_types s v with
        | t -> t
        | exception Not_found -> { kind; desc }
      end
    | Variant t ->
        let desc = Variant (subst_ranges s t) in
        { kind; desc }
    | Arrow(t1, t2) ->
        let desc = Arrow (subst_types s t1, subst_types s t2) in
        { kind; desc }
    | Unit -> { kind; desc }
    | (Constructor _ | Or _ | Proj _ | Row _
       | Top _ | Bot _ | Meet _ | Join _) ->
        assert false

  and subst_ranges s t =
    let kind = Kind.subst s t.kind in
    let desc = t.desc in
    match desc with
    | Var v -> begin
        match Subst.find_ranges s v with
        | t -> t
        | exception Not_found -> { kind; desc }
      end
    | Row t ->
        let desc = Row (subst_row_invariant s t) in
        { kind; desc }
    | (Constructor _ | Or _ | Proj _ | Variant _ | Arrow _
       | Unit | Top _ | Bot _ | Meet _ | Join _) ->
        assert false

  and subst_row_covariant s t =
    let kind = Kind.subst s t.kind in
    let desc = t.desc in
    match t.desc with
    | Var v -> begin
        match Subst.find_row_covariant s v with
        | t -> t
        | exception Not_found -> { kind; desc }
      end
    | Constructor(c, t) ->
        let desc = Constructor(c, subst_types s t) in
        { kind; desc }
    | Or(cs1, t1, cs2, t2) ->
        let desc =
          Or(cs1, subst_row_covariant s t1, cs2, subst_row_covariant s t2)
        in
        { kind; desc }
    | Proj(cs1, t, cs2) ->
        let desc = Proj(cs1, subst_row_covariant s t, cs2) in
        { kind; desc }
    | Top _ -> t
    | Bot _ -> t
    | Join(t1, t2) ->
        let desc = Join(subst_row_covariant s t1, subst_row_covariant s t2) in
        { kind; desc }
    | Row _ -> assert false
    | Variant _ -> assert false
    | Arrow _ -> assert false
    | Unit -> assert false
    | Meet _ -> assert false

  and subst_row_contravariant s t =
    let kind = Kind.subst s t.kind in
    match t.desc with
    | Var v -> begin
        match Subst.find_row_contravariant s v with
        | t -> t
        | exception Not_found -> t
      end
    | Constructor(c, t) ->
        let desc = Constructor(c, subst_types s t) in
        { kind; desc }
    | Or(cs1, t1, cs2, t2) ->
        let desc =
          Or(cs1, subst_row_contravariant s t1,
             cs2, subst_row_contravariant s t2)
        in
        { kind; desc }
    | Proj(cs1, t, cs2) ->
        let desc = Proj(cs1, subst_row_contravariant s t, cs2) in
        { kind; desc }
    | Top _ -> t
    | Bot _ -> t
    | Meet(t1, t2) ->
        let desc =
          Meet(subst_row_contravariant s t1, subst_row_contravariant s t2)
        in
        { kind; desc }
    | Row _ -> assert false
    | Variant _ -> assert false
    | Arrow _ -> assert false
    | Unit -> assert false
    | Join _ -> assert false

  and subst_row_invariant s t =
    let kind = Kind.subst s t.kind in
    match t.desc with
    | Constructor(c, t) ->
        let desc = Constructor(c, subst_types s t) in
        { kind; desc }
    | Or(cs1, t1, cs2, t2) ->
        let desc =
          Or(cs1, subst_row_invariant s t1, cs2, subst_row_invariant s t2)
        in
        { kind; desc }
    | Proj(cs1, t, cs2) ->
        let desc = Proj(cs1, subst_row_invariant s t, cs2) in
        { kind; desc }
    | Top _ -> t
    | Bot _ -> t
    | (Var _ | Row _ | Variant _
       | Unit | Arrow _ | Meet _ | Join _) ->
        assert false

  let subst = subst_types

  let rec subst_vars m t =
    let kind = Kind.subst_vars m t.kind in
    match t.desc with
    | Var v -> begin
        match Var.Map.find v m with
        | v -> var v kind
        | exception Not_found -> t
      end
    | Constructor(c, t) ->
        let desc = Constructor(c, subst_vars m t) in
        { kind; desc }
    | Or(cs1, t1, cs2, t2) ->
        let desc = Or(cs1, subst_vars m t1, cs2, subst_vars m t2) in
        { kind; desc }
    | Proj(cs1, t, cs2) ->
        let desc = Proj(cs1, subst_vars m t, cs2) in
        { kind; desc }
    | Row t ->
        let desc = Row (subst_vars m t) in
        { kind; desc }
    | Variant t ->
        let desc = Variant (subst_vars m t) in
        { kind; desc }
    | Arrow(t1, t2) ->
        let desc = Arrow (subst_vars m t1, subst_vars m t2) in
        { kind; desc }
    | Unit -> t
    | Meet(t1, t2) ->
        let desc = Meet(subst_vars m t1, subst_vars m t2) in
        { kind; desc }
    | Join(t1, t2) ->
        let desc = Join(subst_vars m t1, subst_vars m t2) in
        { kind; desc }
    | Top _ -> t
    | Bot _ -> t

  let generalize env t =
    let vars = free_variables t in
    let env_vars = Env.free_variables env in
    let vars = Var.Set.diff vars env_vars in
    Scheme.create vars t

  let add_or_pair cs1 t1 cs2 t2 pairs =
    let inter = Constructor.CSet.inter cs1 cs2 in
    let empty = Constructor.CSet.is_empty inter in
    if empty then pairs
    else begin
      let desc1 = Proj(cs1, t1, inter) in
      let desc2 = Proj(cs2, t2, inter) in
      let t1 = { desc = desc1; kind = Kind.Row inter } in
      let t2 = { desc = desc2; kind = Kind.Row inter } in
      (t1, t2) :: pairs
    end

  let or_pairs cs1 t1 cs1' t1' cs2 t2 cs2' t2' =
    add_or_pair cs1 t1 cs2 t2
      (add_or_pair cs1 t1 cs2' t2'
         (add_or_pair cs1' t1' cs2 t2
           (add_or_pair cs1' t1' cs2' t2' [])))

  let rec normalize = function
    | Proj(_, t, cs) as desc -> begin
        match t.desc with
        | Proj(cs', t', _) -> normalize (Proj(cs', t', cs))
        | Top _ -> Top cs
        | Bot _ -> Bot cs
        | Constructor _ as desc' -> desc'
        | Or(cs', t', cs'', t'') -> begin
            let left = Constructor.CSet.inter cs' cs in
            let right = Constructor.CSet.inter cs'' cs in
            let left_empty = Constructor.CSet.is_empty left in
            let right_empty = Constructor.CSet.is_empty right in
            match left_empty, right_empty with
            | false, false ->
                let left_t = proj t' left in
                let right_t = proj t'' right in
                normalize (Or(left, left_t, right, right_t))
            | true, false ->
                normalize (Proj(cs'', t'', right))
            | false, true ->
                normalize (Proj(cs', t', left))
            | true, true ->
                assert false
          end
        | Meet(t', t'') ->
            let left_t = proj t' cs in
            let right_t = proj t'' cs in
            normalize (Meet(left_t, right_t))
        | Join(t', t'') ->
            let left_t = proj t' cs in
            let right_t = proj t'' cs in
            normalize (Join(left_t, right_t))
        | Var _ as desc' -> begin
            match t.kind with
            | Type | Range _ -> assert false
            | Row cs' ->
                if Constructor.CSet.equal cs cs' then desc'
                else desc
          end
        | Row _ | Variant _ | Arrow _ | Unit -> assert false
      end
    | Meet(t1, t2) -> begin
        match normalize t1.desc, normalize t2.desc with
        | Top _, desc2 -> desc2
        | desc1, Top _ -> desc1
        | Or(cs1', t1', cs1'', t1''), Or(cs2', t2', cs2'', t2'') -> begin
            let desc1' = normalize t1'.desc in
            let desc1'' = normalize t1''.desc in
            let desc2' = normalize t2'.desc in
            let desc2'' = normalize t2''.desc in
            match desc1', desc1'', desc2', desc2'' with
            | Bot _, _, _, _
            | _, Bot _, _, _
            | _, _, Bot _, _
            | _, _, _, Bot _ ->
                let t1' = { t1' with desc = desc1' } in
                let t1'' = { t1'' with desc = desc1'' } in
                let t2' = { t2' with desc = desc2' } in
                let t2'' = { t2'' with desc = desc2'' } in
                let t1 = { t1 with desc = Or(cs1', t1', cs1'', t1'') } in
                let t2 = { t2 with desc = Or(cs2', t2', cs2'', t2'') } in
                Meet(t1, t2)
            | _, _, _, _ -> begin
              let pairs = or_pairs cs1' t1' cs1'' t1'' cs2' t2' cs2'' t2'' in
              match pairs with
              | [] -> assert false
              | (t1, t2) :: rest ->
                  let t =
                    List.fold_left
                      (fun acc (t1, t2) -> or_ (meet t1 t2) acc)
                      (meet t1 t2) rest
                  in
                  t.desc
              end
          end
        | desc1, desc2 ->
            let t1 = { t1 with desc = desc1 } in
            let t2 = { t2 with desc = desc2 } in
            Meet(t1, t2)
      end
    | Join(t1, t2) -> begin
        match normalize t1.desc, normalize t2.desc with
        | Bot _, desc2 -> desc2
        | desc1, Bot _ -> desc1
        | Or(cs1', t1', cs1'', t1''), Or(cs2', t2', cs2'', t2'') -> begin
            let desc1' = normalize t1'.desc in
            let desc1'' = normalize t1''.desc in
            let desc2' = normalize t2'.desc in
            let desc2'' = normalize t2''.desc in
            match desc1', desc1'', desc2', desc2'' with
            | Bot _, _, _, _
            | _, Bot _, _, _
            | _, _, Bot _, _
            | _, _, _, Bot _ ->
                let t1' = { t1' with desc = desc1' } in
                let t1'' = { t1'' with desc = desc1'' } in
                let t2' = { t2' with desc = desc2' } in
                let t2'' = { t2'' with desc = desc2'' } in
                let t1 = { t1 with desc = Or(cs1', t1', cs1'', t1'') } in
                let t2 = { t2 with desc = Or(cs2', t2', cs2'', t2'') } in
                Join(t1, t2)
            | _, _, _, _ -> begin
              let pairs = or_pairs cs1' t1' cs1'' t1'' cs2' t2' cs2'' t2'' in
              match pairs with
              | [] -> assert false
              | (t1, t2) :: rest ->
                  let t =
                    List.fold_left
                      (fun acc (t1, t2) -> or_ (join t1 t2) acc)
                      (join t1 t2) rest
                  in
                  t.desc
              end
          end
        | desc1, desc2 ->
            let t1 = { t1 with desc = desc1 } in
            let t2 = { t2 with desc = desc2 } in
            Join(t1, t2)
      end
    | Or(cs1, t1, cs2, t2) -> begin
        match normalize t1.desc, normalize t2.desc with
        | Bot _, Bot _ -> Bot (Constructor.CSet.union cs1 cs2)
        | Top _, Top _ -> Top (Constructor.CSet.union cs1 cs2)
        | desc1, desc2 ->
            let t1 = { t1 with desc = desc1 } in
            let t2 = { t2 with desc = desc2 } in
            Or(cs1, t1, cs2, t2)
      end
    | desc -> desc

  let rec unify_types t1 t2 =
    let open Result in
    match t1.desc, t2.desc with
    | Var v1, Var v2 when Var.equal v1 v2 ->
        return Subst.empty
    | Var v1, _ ->
        return (Subst.add_type Subst.empty v1 t2)
    | _, Var v2 ->
        return (Subst.add_type Subst.empty v2 t1)
    | Variant t1, Variant t2 ->
        unify_ranges t1 t2
    | Arrow(t1, t1'), Arrow(t2, t2') ->
        unify_types t1 t2 >>= fun subst ->
        let t1' = subst_types subst t1' in
        let t2' = subst_types subst t2' in
        unify_types t1' t2' >>| fun subst' ->
        Subst.compose subst subst'
    | Unit, Unit -> return Subst.empty
    | (Constructor _ | Or _ | Proj _ | Row _
       | Top _ | Bot _ | Meet _ | Join _), _ ->
        assert false
    | _, (Constructor _ | Or _ | Proj _ | Row _
       | Top _ | Bot _ | Meet _ | Join _) ->
        assert false
    | _, _ -> error ()

  and unify_ranges t1 t2 =
    let open Result in
    match t1.desc, t2.desc with
    | Var v1, Var v2 when Var.equal v1 v2 ->
        return Subst.empty
    | Var v1, Var v2 -> begin
        match t1.kind, t2.kind with
        | (Type | Row _), _ -> assert false
        | _, (Type | Row _) -> assert false
        | Range(t1, t1'), Range(t2, t2') ->
            Type.biunify_row t1 t2' >>= fun subst ->
            let t1' = Type.subst_row_contravariant subst t1' in
            let t2 = Type.subst_row_covariant subst t2 in
            Type.biunify_row t2 t1' >>| fun subst' ->
            let t1 = Type.subst_row_covariant subst' t1 in
            let t2' = Type.subst_row_contravariant subst' t2' in
            let t = fresh_var (Range(join t1 t2, meet t1' t2')) in
            let subst'' =
              Subst.add_range (Subst.add_range Subst.empty v1 t) v2 t
            in
            Subst.compose subst (Subst.compose subst' subst'')
      end
    | Var v1, Row t2' -> begin
        match t1.kind with
        | Type | Row _ -> assert false
        | Range(t1, t1') ->
            Type.biunify_row t1 t2' >>= fun subst ->
            let t1' = Type.subst_row_contravariant subst t1' in
            let t2' = Type.subst_row_invariant subst t2' in
            Type.biunify_row t2' t1' >>| fun subst' ->
            let t2' = Type.subst_row_invariant subst' t2' in
            let subst'' = Subst.add_range Subst.empty v1 t2' in
            Subst.compose subst (Subst.compose subst' subst'')
      end
    | Row t1', Var v2 -> begin
        match t2.kind with
        | Type | Row _ -> assert false
        | Range(t2, t2') ->
            Type.biunify_row t2 t1' >>= fun subst ->
            let t2' = Type.subst_row_contravariant subst t2' in
            let t1' = Type.subst_row_invariant subst t1' in
            Type.biunify_row t1' t2' >>| fun subst' ->
            let t1' = Type.subst_row_invariant subst' t1' in
            let subst'' = Subst.add_range Subst.empty v2 t1' in
            Subst.compose subst (Subst.compose subst' subst'')
      end
    | Row t1, Row t2 ->
        unify_row t1 t2
    | (Constructor _ | Or _ | Proj _ | Variant _ | Arrow _
       | Unit | Top _ | Bot _ | Meet _ | Join _), _ ->
        assert false
    | _, (Constructor _ | Or _ | Proj _ | Variant _ | Arrow _
       | Unit | Top _ | Bot _ | Meet _ | Join _) ->
        assert false

  and unify_row t1 t2 =
    let open Result in
    match normalize t1.desc, normalize t2.desc with
    | Constructor(_, t1), Constructor(_, t2) ->
        unify_types t1 t2
    | Or(cs1, t1, cs1', t1'), Or(cs2, t2, cs2', t2') ->
        let pairs = or_pairs cs1 t1 cs1' t1' cs2 t2 cs2' t2' in
        let rec loop subst pairs =
          match pairs with
          | [] -> return subst
          | (t1, t2) :: rest ->
              let t1 = Type.subst_row_invariant subst t1 in
              let t2 = Type.subst_row_invariant subst t2 in
              unify_row t1 t2 >>= fun subst' ->
              loop (Subst.compose subst subst') rest
        in
        loop Subst.empty pairs
    | Top _, Top _ -> return Subst.empty
    | Bot _, Bot _ -> return Subst.empty
    | (Var _ | Proj _ | Row _ | Variant _
       | Arrow _ | Unit | Meet _ | Join _), _ ->
        assert false
    | _, (Var _ | Proj _ | Row _ | Variant _
          | Arrow _ | Unit | Meet _ | Join _) ->
        assert false
    | _, _ -> error ()

  and biunify_row t1 (* pos *) t2 (* neg *) =
    let open Result in
    match normalize t1.desc, normalize t2.desc with
    | Var v1, Var v2 when Var.equal v1 v2 ->
        return Subst.empty
    | Proj(cs, t, cs'), desc -> begin
        match t.desc with
        | Var _ ->
            let rest = Constructor.CSet.diff cs cs' in
            let v = Var.fresh () in
            let var_t = var v (Kind.Row rest) in
            let or_desc = Or(cs', t2, rest, var_t) in
            let or_t = { desc = or_desc; kind = Kind.Row cs' } in
            biunify_row t or_t
        | _ -> assert false
      end
    | desc, Proj(cs, t, cs') -> begin
        match t.desc with
        | Var _ ->
            let rest = Constructor.CSet.diff cs cs' in
            let v = Var.fresh () in
            let var_t = var v (Kind.Row rest) in
            let or_desc = Or(cs', t1, rest, var_t) in
            let or_t = { desc = or_desc; kind = Kind.Row cs' } in
            biunify_row or_t t
        | _ -> assert false
      end
    | Var v, _ ->
        return (Subst.add_row_contravariant Subst.empty v (meet t2 t1))
    | _, Var v ->
        return (Subst.add_row_covariant Subst.empty v (join t1 t2))
    | Constructor(_, t1), Constructor(_, t2) ->
        unify_types t1 t2
    | Or(cs1, t1, cs1', t1'), Or(cs2, t2, cs2', t2') ->
        let pairs = or_pairs cs1 t1 cs1' t1' cs2 t2 cs2' t2' in
        let rec loop subst pairs =
          match pairs with
          | [] -> return subst
          | (t1, t2) :: rest ->
              let t1 = Type.subst_row_covariant subst t1 in
              let t2 = Type.subst_row_contravariant subst t2 in
              biunify_row t1 t2 >>= fun subst' ->
              loop (Subst.compose subst subst') rest
        in
        loop Subst.empty pairs
    | _, Top _ -> return Subst.empty
    | Bot _, _ -> return Subst.empty
    | Or(cs1, t1, cs1', t1'), Bot _ ->
        biunify_row t1 (bot cs1) >>= fun subst ->
        let t1' = Type.subst_row_covariant subst t1' in
        biunify_row t1' (bot cs1') >>| fun subst' ->
        Subst.compose subst subst'
    | Top _, Or(cs1, t1, cs1', t1') ->
        biunify_row (top cs1) t1 >>= fun subst ->
        let t1' = Type.subst_row_covariant subst t1' in
        biunify_row (top cs1') t1' >>| fun subst' ->
        Subst.compose subst subst'
    | Join(t1, t1'), _ ->
        biunify_row t1 t2 >>= fun subst ->
        let t1' = subst_row_covariant subst t1' in
        let t2 = subst_row_contravariant subst t2 in
        biunify_row t1' t2 >>| fun subst' ->
        Subst.compose subst subst'
    | _, Meet(t2, t2') ->
        biunify_row t1 t2 >>= fun subst ->
        let t1 = subst_row_covariant subst t1 in
        let t2' = subst_row_contravariant subst t2' in
        biunify_row t1 t2' >>| fun subst' ->
        Subst.compose subst subst'
    | (Row _ | Variant _ | Arrow _ | Unit | Meet _), _ ->
        assert false
    | _, (Row _ | Variant _ | Arrow _ | Unit | Join _) ->
        assert false
    | _, _ ->
        error ()

  let unify = unify_types

end

and Kind : sig

  include module type of struct include KindT end

  val type_ : t

  val row : Constructor.CSet.t -> t

  val range : Type.t -> Type.t -> t

  val free_variables : t -> Var.Set.t

  val subst : Subst.t -> t -> t

  val subst_vars : Var.t Var.Map.t -> t -> t

end = struct

  include KindT

  let type_ = Type

  let row cs = Row cs

  let range t1 t2 = Range(t1, t2)

  let free_variables = function
    | Type | Row _ -> Var.Set.empty
    | Range(t1, t2) ->
        Var.Set.union (Type.free_variables t1) (Type.free_variables t2)

  let subst s = function
    | Type -> Type
    | Row _ as kind -> kind
    | Range(t1, t2) ->
        Range(Type.subst_row_covariant s t1,
              Type.subst_row_contravariant s t2)

  let subst_vars m = function
    | Type -> Type
    | Row _ as kind -> kind
    | Range(t1, t2) ->
        Range(Type.subst_vars m t1, Type.subst_vars m t2)

end

and Scheme : sig

  type t

  val create : Var.Set.t -> Type.t -> t

  val of_type : Type.t -> t

  val free_variables : t -> Var.Set.t

  val subst : Subst.t -> t -> t

  val instantiate : t -> Type.t

  val vars : t -> Var.Set.t

  val type_ : t -> Type.t

end = struct

  type t =
    { vars : Var.Set.t;
      type_ : Type.t; }

  let create vars type_ =
    { vars; type_ }

  let vars t = t.vars

  let type_ t = t.type_

  let of_type type_ =
    { vars = Var.Set.empty; type_ }

  let free_variables t =
    let vars = Type.free_variables t.type_ in
    Var.Set.diff vars t.vars

  let subst s t =
    let type_ = Type.subst_types s t.type_ in
    { t with type_ }

  let instantiate t =
    let vars =
      Var.Set.fold
        (fun v acc ->
          Var.Map.add v (Var.fresh ()) acc)
        t.vars Var.Map.empty
    in
    Type.subst_vars vars t.type_

end

and Subst : sig

  type t

  val empty : t

  val compose : t -> t -> t

  val add_type : t -> Var.t -> Type.t -> t

  val add_range : t -> Var.t -> Type.t -> t

  val add_row_covariant : t -> Var.t -> Type.t -> t

  val add_row_contravariant : t -> Var.t -> Type.t -> t

  val find_types : t -> Var.t -> Type.t

  val find_ranges : t -> Var.t -> Type.t

  val find_row_covariant : t -> Var.t -> Type.t

  val find_row_contravariant : t -> Var.t -> Type.t

  val fold : (Var.t -> Type.t -> 'a -> 'a) -> t -> 'a -> 'a

end = struct

  type t =
    { types : Type.t Var.Map.t;
      ranges : Type.t Var.Map.t;
      row_covariant : Type.t Var.Map.t;
      row_contravariant : Type.t Var.Map.t; }

  let empty =
    { types = Var.Map.empty;
      ranges = Var.Map.empty;
      row_covariant = Var.Map.empty;
      row_contravariant = Var.Map.empty; }

  let add_type s v t =
    { s with types = Var.Map.add v t s.types }

  let add_range s v t =
    { s with ranges = Var.Map.add v t s.ranges }

  let add_row_covariant s v t =
    { s with row_covariant = Var.Map.add v t s.row_covariant }

  let add_row_contravariant s v t =
    { s with row_contravariant = Var.Map.add v t s.row_contravariant }

  let find_types s v =
    Var.Map.find v s.types

  let find_ranges s v =
    Var.Map.find v s.ranges

  let find_row_covariant s v =
    Var.Map.find v s.row_covariant

  let find_row_contravariant s v =
    Var.Map.find v s.row_contravariant

  let subst s1 s2 =
    let types = Var.Map.map (Type.subst_types s2) s1.types in
    let ranges = Var.Map.map (Type.subst_ranges s2) s1.ranges in
    let row_covariant =
      Var.Map.map (Type.subst_row_covariant s2) s1.row_covariant
    in
    let row_contravariant =
      Var.Map.map (Type.subst_row_contravariant s2) s1.row_contravariant
    in
    { types; ranges; row_covariant; row_contravariant }

  let compose_map m1 m2 =
    Var.Map.union
      (fun _ t _ -> Some t)
      m1 m2

  let compose s1 s2 =
    let s1 = subst s1 s2 in
    let types = compose_map s1.types s2.types in
    let ranges = compose_map s1.ranges s2.ranges in
    let row_covariant =
      compose_map s1.row_covariant s2.row_covariant
    in
    let row_contravariant =
      compose_map s1.row_contravariant s2.row_contravariant
    in
    { types; ranges; row_covariant; row_contravariant }

  let fold f t acc =
    Var.Map.fold f t.types
      (Var.Map.fold f t.ranges
        (Var.Map.fold f t.row_covariant
          (Var.Map.fold f t.row_contravariant acc)))

end

and Env : sig

  type t

  val empty : t

  val add : string -> Scheme.t -> t -> t

  val lookup : t -> string -> Scheme.t

  val free_variables : t -> Var.Set.t

  val subst : Subst.t -> t -> t

  val fold : (string -> Scheme.t -> 'a -> 'a) -> t -> 'a -> 'a

end = struct

  module StringMap = Map.Make(String)

  type t = Scheme.t StringMap.t

  let empty = StringMap.empty

  let add id scheme t = StringMap.add id scheme t

  let lookup t id = StringMap.find id t

  let free_variables t =
    StringMap.fold
      (fun _ scheme acc ->
        Var.Set.union (Scheme.free_variables scheme) acc)
      t Var.Set.empty

  let subst s t =
    StringMap.map
      (fun _type -> Scheme.subst s _type)
      t

  let fold = StringMap.fold

end

module Printing = struct

  module Uses = struct

    type t =
      { types : Var.Set.t;
        ranges : int Var.Map.t;
        row_covariant : Constructor.CSet.t Var.Map.t;
        row_contravariant : Constructor.CSet.t Var.Map.t; }

    let empty =
      { types = Var.Set.empty;
        ranges = Var.Map.empty;
        row_covariant = Var.Map.empty;
        row_contravariant = Var.Map.empty; }

    let combine u1 u2 =
      { types =
          Var.Set.union u1.types u2.types;
        ranges =
          Var.Map.union (fun _ c1 c2 -> Some (c1 + c2))
            u1.ranges u2.ranges;
        row_covariant =
          Var.Map.union (fun _ cs1 _ -> Some cs1)
            u1.row_covariant u2.row_covariant;
        row_contravariant =
          Var.Map.union (fun _ cs1 _ -> Some cs1)
            u1.row_contravariant u2.row_contravariant; }

    let singleton_type v =
      { empty with types = Var.Set.singleton v }

    let singleton_range v =
      { empty with ranges = Var.Map.singleton v 1 }

    let singleton_row_covariant v cs =
      { empty with row_covariant = Var.Map.singleton v cs }

    let singleton_row_contravariant v cs =
      { empty with row_contravariant = Var.Map.singleton v cs }

    let only_row_covariant s =
      Var.Map.filter
        (fun v _ -> not (Var.Map.mem v s.row_contravariant))
        s.row_covariant

    let only_row_contravariant s =
      Var.Map.filter
        (fun v _ -> not (Var.Map.mem v s.row_covariant))
        s.row_contravariant

    let types s = s.types

    let rows all s =
      if all then begin
        Var.Map.fold (fun v _ acc -> Var.Set.add v acc) s.row_covariant
          (Var.Map.fold (fun v _ acc -> Var.Set.add v acc) s.row_contravariant
             Var.Set.empty)
      end else begin
        Var.Map.fold
          (fun v _ acc ->
            if Var.Map.mem v s.row_covariant then
              Var.Set.add v acc
            else acc)
          s.row_contravariant Var.Set.empty
      end

    let aliased_ranges s =
      Var.Map.fold
        (fun v c acc ->
          if c > 1 then Var.Set.add v acc
          else acc)
        s.ranges Var.Set.empty

  end

  let rec analyse_type_vars_types t =
    let open Type in
    Uses.combine
      (analyse_type_desc_vars_types t.desc)
      (analyse_kind_vars t.kind)

  and analyse_type_vars_ranges t =
    let open Type in
    Uses.combine
      (analyse_type_desc_vars_ranges t.desc)
      (analyse_kind_vars t.kind)

  and analyse_type_vars_row_covariant t =
    let open Type in
    Uses.combine
      (analyse_type_desc_vars_row_covariant t.kind t.desc)
      (analyse_kind_vars t.kind)

  and analyse_type_vars_row_contravariant t =
    let open Type in
    Uses.combine
      (analyse_type_desc_vars_row_contravariant t.kind t.desc)
      (analyse_kind_vars t.kind)

  and analyse_type_vars_row_invariant t =
    let open Type in
    Uses.combine
      (analyse_type_desc_vars_row_invariant t.desc)
      (analyse_kind_vars t.kind)

  and analyse_type_desc_vars_types =
    let open Type in function
    | Var v -> Uses.singleton_type v
    | Variant t -> analyse_type_vars_ranges t
    | Arrow(t1, t2) ->
        Uses.combine
          (analyse_type_vars_types t1)
          (analyse_type_vars_types t2)
    | Unit -> Uses.empty
    | _ -> assert false

  and analyse_type_desc_vars_ranges =
    let open Type in function
    | Var v -> Uses.singleton_range v
    | Row t -> analyse_type_vars_row_invariant t
    | _ -> assert false

  and analyse_type_desc_vars_row_covariant kind =
    let open Type in function
    | Var v ->
        let cs =
          match kind with
          | Row cs -> cs
          | _ -> assert false
        in
        Uses.singleton_row_covariant v cs
    | Constructor(_, t) -> analyse_type_vars_types t
    | Or(_, t1, _, t2) | Join(t1, t2) ->
        Uses.combine
          (analyse_type_vars_row_covariant t1)
          (analyse_type_vars_row_covariant t2)
    | Proj(_, t, _) -> analyse_type_vars_row_covariant t
    | Top _ -> Uses.empty
    | Bot _ -> Uses.empty
    | _ -> assert false

  and analyse_type_desc_vars_row_contravariant kind =
    let open Type in function
    | Var v ->
        let cs =
          match kind with
          | Row cs -> cs
          | _ -> assert false
        in
        Uses.singleton_row_contravariant v cs
    | Constructor(_, t) -> analyse_type_vars_types t
    | Or(_, t1, _, t2) | Meet(t1, t2) ->
        Uses.combine
          (analyse_type_vars_row_contravariant t1)
          (analyse_type_vars_row_contravariant t2)
    | Proj(_, t, _) -> analyse_type_vars_row_contravariant t
    | Top _ -> Uses.empty
    | Bot _ -> Uses.empty
    | _ -> assert false

  and analyse_type_desc_vars_row_invariant =
    let open Type in function
    | Constructor(_, t) -> analyse_type_vars_types t
    | Or(_, t1, _, t2) ->
        Uses.combine
          (analyse_type_vars_row_contravariant t1)
          (analyse_type_vars_row_contravariant t2)
    | Proj(_, t, _) -> analyse_type_vars_row_contravariant t
    | Top _ -> Uses.empty
    | Bot _ -> Uses.empty
    | _ -> assert false

  and analyse_kind_vars =
    let open Kind in function
    | Type -> Uses.empty
    | Row _ -> Uses.empty
    | Range(t1, t2) ->
        Uses.combine
          (analyse_type_vars_row_covariant t1)
          (analyse_type_vars_row_contravariant t2)

  let name offset i =
    let code = 97 + ((i + offset) mod 26) in
    if i < 26 then
      String.make 1 (Char.chr code)
    else
      String.make 1 (Char.chr code) ^ string_of_int(i / 26)

  let name_types i = name 0 i
  let name_rows i = name 17 i

  let names all uses =
    let count, names =
      Var.Set.fold
        (fun v (i, map) ->
          let name = name_types i in
          let i = i + 1 in
          let map = Var.Map.add v ("'" ^ name) map in
          (i, map))
        (Uses.types uses) (0, Var.Map.empty)
    in
    let _, names =
      Var.Set.fold
        (fun v (i, map) ->
          let name = name_types i in
          let i = i + 1 in
          let map = Var.Map.add v ("'" ^ name) map in
          (i, map))
        (Uses.aliased_ranges uses) (count, names)
    in
    let _, names =
      Var.Set.fold
        (fun v (i, map) ->
          let name = name_rows i in
          let i = i + 1 in
          let map = Var.Map.add v ("!" ^ name) map in
          (i, map))
        (Uses.rows all uses) (0, names)
    in
    names

  type context =
    | At_toplevel
    | In_arrow_left
    | In_arrow_right
    | In_constructor
    | In_or
    | In_meet
    | In_join
    | In_row
    | In_proj

  let normal raw desc =
    if not raw then Type.normalize desc else desc

  let needs_parens raw desc ctx =
    let open Type in
    match desc, ctx with
    | Var _, _ -> false
    | Constructor _, In_proj -> false
    | Constructor _, _ -> false
    | Or(_, t1, _, t2), (In_meet | In_join | In_proj) -> begin
        match normal raw t1.desc, normal raw t2.desc with
        | Bot _, _ | _, Bot _ -> raw
        | _ -> true
      end
    | Or _, _ -> false
    | Proj _, _ -> false
    | Row _, _ -> false
    | Variant _, _ -> false
    | Arrow _, (In_arrow_right | At_toplevel) -> false
    | Arrow _, _ -> true
    | Unit, _ -> false
    | Top _, In_proj -> false
    | Top _, _ -> false
    | Bot _, In_proj -> false
    | Bot _, _ -> false
    | Meet _, (In_join | In_proj) -> true
    | Meet _, _ -> false
    | Join _, (In_meet | In_proj) -> true
    | Join _, _ -> false

  let printf = Format.printf

  let rec print_type_desc ctx raw aliased names desc =
    let open Type in
    let desc = normal raw desc in
    let needs_parens = needs_parens raw desc ctx in
    if needs_parens then printf "(";
    let aliased =
      match desc with
      | Var v -> print_var aliased names v
      | Constructor(c, t) ->
          printf "%s of " (Constructor.to_string c);
          print_type In_constructor raw aliased names t
      | Or(cs1, t1, cs2, t2) -> begin
          match normal raw t1.desc, normal raw t2.desc with
          | Bot _, _ when not raw-> print_type ctx raw aliased names t2
          | _, Bot _ when not raw -> print_type ctx raw aliased names t1
          | _ ->
              let left, right =
                if Constructor.CSet.is_finite cs2
                   && not (Constructor.CSet.is_finite cs1) then
                  t2, t1
                else t1, t2
              in
              let aliased = print_type In_or raw aliased names left in
              printf " | ";
              print_type In_or raw aliased names right
        end
      | Proj(cs1, t, cs2) -> begin
          let aliased = print_type In_proj raw aliased names t in
          match Constructor.CSet.proj_representation cs1 cs2 with
          | Absolute cs ->
              printf "/[ ";
              List.iter (fun c -> printf "%s " (Constructor.to_string c)) cs;
              printf "]";
              aliased
          | Diff cs ->
              printf "\\[ ";
              List.iter (fun c -> printf "%s " (Constructor.to_string c)) cs;
              printf "]";
              aliased
        end
      | Row _ -> assert false
      | Variant t -> begin
          match t.desc with
          | Var v ->
              if raw then begin
                let aliased = print_kind raw aliased names t.kind in
                printf " as <%s>" (Var.to_string v);
                aliased
              end else begin
                if Var.Set.mem v aliased then print_var aliased names v
                else begin
                  match Var.Map.find v names with
                  | s ->
                      let aliased = Var.Set.add v aliased in
                      let aliased = print_kind raw aliased names t.kind in
                      printf " as %s" s;
                      aliased
                  | exception Not_found ->
                      print_kind raw aliased names t.kind
                end
              end
          | Row t ->
              printf "[";
              let aliased = print_type In_row raw aliased names t in
              printf "]";
              aliased
          | _ -> assert false
        end
      | Arrow(t1, t2) ->
          let aliased = print_type In_arrow_left raw aliased names t1 in
          printf " -> ";
          print_type In_arrow_right raw aliased names t2
      | Unit ->
          printf "unit";
          aliased
      | Top cs ->
          printf "top";
          if raw then
            Constructor.CSet.print_raw cs;
          aliased
      | Bot cs ->
          printf "bot";
          if raw then
            Constructor.CSet.print_raw cs;
          aliased
      | Meet(t1, t2) ->
          let aliased = print_type In_meet raw aliased names t1 in
          printf " /\\ ";
          print_type In_meet raw aliased names t2
      | Join(t1, t2) ->
          let aliased = print_type In_join raw aliased names t1 in
          printf " \\/ ";
          print_type In_join raw aliased names t2
    in
    if needs_parens then printf ")";
    aliased

    and print_type (ctx : context) raw aliased names t =
      let open Type in
      print_type_desc ctx raw aliased names t.desc

    and print_kind raw aliased names =
      let open Kind in function
      | Type | Row _ -> assert false
      | Range(t1, t2) ->
          match normal raw t1.desc, normal raw t2.desc with
          | Bot _, Top _ ->
              printf "[+ bot - top]";
              aliased
          | Bot _, _ ->
              printf "[- ";
              let aliased = print_type In_row raw aliased names t2 in
              printf "]";
              aliased
          | _, Top _ ->
              printf "[+ ";
              let aliased = print_type In_row raw aliased names t1 in
              printf "]";
              aliased
          | _, _ ->
              printf "[+ ";
              let aliased = print_type In_row raw aliased names t1 in
              printf " - ";
              let aliased = print_type In_row raw aliased names t2 in
              printf "]";
              aliased

    and print_var aliased names v =
      match Var.Map.find v names with
      | name ->
          printf "%s" name;
          aliased
      | exception Not_found ->
          printf "<%s>" (Var.to_string v);
          aliased

  let print_raw t =
    ignore (print_type At_toplevel true Var.Set.empty Var.Map.empty t)

  let print_raw_scheme s =
    Var.Set.iter
      (fun v -> printf "<%s>" (Var.to_string v))
      (Scheme.vars s);
    printf " . ";
    print_raw (Scheme.type_ s)

  let print_raw_env e =
    printf "{@[<v 2>@ ";
    Env.fold
      (fun name s () ->
        printf "%s: " name;
        print_raw_scheme s;
        printf "@ ")
      e ();
    printf "@]}"

  let print_raw_subst subst =
    printf "[@[<v 2>@ ";
    Subst.fold
      (fun v t () ->
        printf "<%s> / " (Var.to_string v);
        print_raw t;
        printf "@ ")
      subst ();
    printf "@]]"

  let print t =
    let uses = analyse_type_vars_types t in
    let subst =
      Var.Map.fold
        (fun v cs acc -> Subst.add_row_covariant acc v (Type.bot cs))
        (Uses.only_row_covariant uses) Subst.empty
    in
    let subst =
      Var.Map.fold
        (fun v cs acc -> Subst.add_row_contravariant acc v (Type.top cs))
        (Uses.only_row_contravariant uses) subst
    in
    let t = Type.subst_types subst t in
    let names = names false uses in
    ignore (print_type At_toplevel false Var.Set.empty names t)

  let print_unification_error t1 t2 _ =
    let uses =
      Uses.combine
        (analyse_type_vars_types t1)
        (analyse_type_vars_types t2)
    in
    let names = names true uses in
    printf "@[<v 2>Error: incompatible types:@ ";
    let aliased = print_type At_toplevel false Var.Set.empty names t1 in
    printf "@;<1 -2>and:@ ";
    ignore (print_type At_toplevel false aliased names t2);
    printf "@]"

end
