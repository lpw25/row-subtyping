
module Constructor : sig

  type t

  val of_string : string -> t

  val to_string : t -> string

  module CSet : sig

    type constructor = t

    type t

    val empty : t

    val singleton : constructor -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val is_empty : t -> bool

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

    let singleton x =
      Finite (StringSet.singleton x)

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

    let is_empty cs =
      match cs with
      | Finite s -> StringSet.is_empty s
      | Cofinite _ -> false

  end

end

module Ident : sig

  type t

  val fresh : string -> t

  module Set : Set.S with type elt = t

  module Map : Map.S with type key = t

end = struct

  type t =
    { name : string; stamp : int }

  let fresh =
    let counter = ref 0 in
    fun name ->
      incr counter;
      { name; stamp = !counter }

  module Ord = struct
    type nonrec t = t
    let compare (x : t) (y : t) =
      Pervasives.compare x.stamp y.stamp
  end

  module Set = Set.Make(Ord)

  module Map = Map.Make(Ord)

end

module Var : sig

  type t

  val fresh : unit -> t

  module Set : Set.S with type elt = t

  module Map : Map.S with type key = t

end = struct

  type t = int

  let fresh =
    let counter = ref 0 in
    fun () ->
      incr counter;
      !counter

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

module Subst = struct

  type t =
    { types : TypeT.desc Var.Map.t;
      ranges : TypeT.desc Var.Map.t;
      row_covariant : TypeT.desc Var.Map.t;
      row_contravariant : TypeT.desc Var.Map.t; }

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

  let compose_map m1 m2 =
    Var.Map.union
      (fun _ t _ -> Some t)
      m1 m2

  let compose s1 s2 =
    let types = compose_map s1.types s2.types in
    let ranges = compose_map s1.ranges s2.ranges in
    let row_covariant =
      compose_map s1.row_covariant s2.row_covariant
    in
    let row_contravariant =
      compose_map s1.row_contravariant s2.row_contravariant
    in
    { types; ranges; row_covariant; row_contravariant }

end

module rec Type : sig

  include module type of struct include TypeT end

  val var : Var.t -> Kind.t -> t

  val constructor : Constructor.t -> t -> t

  val or_ : t -> t -> t

  val proj : t -> Constructor.CSet.t -> t

  val row : t -> t

  val variant : t -> t

  val arrow : t -> t -> t

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

end = struct

  include TypeT

  let var v kind =
    let desc = Var v in
    { desc; kind }

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
    | Top _ | Bot _ ->
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

  let rec subst_types_desc s = function
    | Var v as desc -> begin
        match Subst.find_types s v with
        | t -> t
        | exception Not_found -> desc
      end
    | Variant t ->
        Variant (subst_ranges s t)
    | Arrow(t1, t2) ->
        Arrow (subst_types s t1, subst_types s t2)
    | (Constructor _ | Or _ | Proj _ | Row _
       | Top _ | Bot _ | Meet _ | Join _) ->
        assert false

  and subst_ranges_desc s = function
    | Var v as desc -> begin
        match Subst.find_ranges s v with
        | t -> t
        | exception Not_found -> desc
      end
    | Row t ->
        Row (subst_row_invariant s t)
    | (Constructor _ | Or _ | Proj _ | Variant _ | Arrow _
       | Top _ | Bot _ | Meet _ | Join _) ->
        assert false

  and subst_row_covariant_desc s = function
    | Var v as desc -> begin
        match Subst.find_row_covariant s v with
        | t -> t
        | exception Not_found -> desc
      end
    | Constructor(c, t) ->
        Constructor(c, subst_types s t)
    | Or(cs1, t1, cs2, t2) ->
        Or(cs1, subst_row_covariant s t1, cs2, subst_row_covariant s t2)
    | Proj(cs1, t, cs2) ->
        Proj(cs1, subst_row_covariant s t, cs2)
    | Bot _ as desc -> desc
    | Join(t1, t2) ->
        Join(subst_row_covariant s t1, subst_row_covariant s t2)
    | Row _ | Variant _ | Arrow _ | Meet _ | Top _ ->
        assert false

  and subst_row_contravariant_desc s = function
    | Var v as desc -> begin
        match Subst.find_row_contravariant s v with
        | t -> t
        | exception Not_found -> desc
      end
    | Constructor(c, t) ->
        Constructor(c, subst_types s t)
    | Or(cs1, t1, cs2, t2) ->
        Or(cs1, subst_row_covariant s t1, cs2, subst_row_covariant s t2)
    | Proj(cs1, t, cs2) ->
        Proj(cs1, subst_row_covariant s t, cs2)
    | Top _ as desc -> desc
    | Meet(t1, t2) ->
        Meet(subst_row_covariant s t1, subst_row_covariant s t2)
    | Row _ | Variant _ | Arrow _ | Join _ | Bot _ ->
        assert false

  and subst_row_invariant_desc s = function
    | Constructor(c, t) ->
        Constructor(c, subst_types s t)
    | Or(cs1, t1, cs2, t2) ->
        Or(cs1, subst_row_invariant s t1, cs2, subst_row_invariant s t2)
    | Proj(cs1, t, cs2) ->
        Proj(cs1, subst_row_invariant s t, cs2)
    | Top _ as desc -> desc
    | Bot _ as desc -> desc
    | (Var _ | Row _ | Variant _
       | Arrow _ | Meet _ | Join _) ->
        assert false

  and subst_types s t =
    let kind = Kind.subst s t.kind in
    let desc = subst_types_desc s t.desc in
    { kind; desc }

  and subst_ranges s t =
    let kind = Kind.subst s t.kind in
    let desc = subst_ranges_desc s t.desc in
    { kind; desc }

  and subst_row_covariant s t =
    let kind = Kind.subst s t.kind in
    let desc = subst_row_covariant_desc s t.desc in
    { kind; desc }

  and subst_row_contravariant s t =
    let kind = Kind.subst s t.kind in
    let desc = subst_row_contravariant_desc s t.desc in
    { kind; desc }

  and subst_row_invariant s t =
    let kind = Kind.subst s t.kind in
    let desc = subst_row_invariant_desc s t.desc in
    { kind; desc }

  let subst = subst_types

  let rec subst_vars_desc m = function
    | Var v as desc -> begin
        match Var.Map.find v m with
        | v -> Var v
        | exception Not_found -> desc
      end
    | Constructor(c, t) ->
        Constructor(c, subst_vars m t)
    | Or(cs1, t1, cs2, t2) ->
        Or(cs1, subst_vars m t1, cs2, subst_vars m t2)
    | Proj(cs1, t, cs2) ->
        Proj(cs1, subst_vars m t, cs2)
    | Row t ->
        Row (subst_vars m t)
    | Variant t ->
        Variant (subst_vars m t)
    | Arrow(t1, t2) ->
        Arrow (subst_vars m t1, subst_vars m t2)
    | Meet(t1, t2) ->
        Meet(subst_vars m t1, subst_vars m t2)
    | Join(t1, t2) ->
        Join(subst_vars m t1, subst_vars m t2)
    | Top _ as desc -> desc
    | Bot _ as desc -> desc

  and subst_vars m t =
    let kind = Kind.subst_vars m t.kind in
    let desc = subst_vars_desc m t.desc in
    { kind; desc }

  let generalize env t =
    let vars = free_variables t in
    let env_vars = Env.free_variables env in
    let vars = Var.Set.diff vars env_vars in
    Scheme.create vars t

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
            let right_empty = Constructor.CSet.is_empty left in
            match left_empty, right_empty with
            | false, false ->
                let left_t = proj t' left in
                let right_t = proj t'' right in
                Or(left, left_t, right, right_t)
            | true, false ->
                normalize (Proj(cs'', t'', right))
            | false, true ->
                normalize (Proj(cs', t', left))
            | true, true -> assert false
          end
        | Meet(t', t'') ->
            let left_t = proj t' cs in
            let right_t = proj t'' cs in
            Meet(left_t, right_t)
        | Join(t', t'') ->
            let left_t = proj t' cs in
            let right_t = proj t'' cs in
            Join(left_t, right_t)
        | Var _ -> desc
        | Row _ | Variant _ | Arrow _ -> assert false
      end
    | desc -> desc

  let unify_or unify cs1 t1 cs1' t1' cs2 t2 cs2' t2' =
    let open Result in
    let left_left = Constructor.CSet.inter cs1 cs2 in
    let left_right = Constructor.CSet.inter cs1 cs2' in
    let right_left = Constructor.CSet.inter cs1 cs2 in
    let right_right = Constructor.CSet.inter cs1 cs2' in
    let left_left_empty = Constructor.CSet.is_empty left_left in
    let left_right_empty = Constructor.CSet.is_empty left_right in
    let right_left_empty = Constructor.CSet.is_empty right_left in
    let right_right_empty = Constructor.CSet.is_empty right_right in
    let left_left_result =
      if left_left_empty then return Subst.empty
      else begin
        let desc1 = Proj(cs1, t1, left_left) in
        let desc2 = Proj(cs2, t2, left_left) in
        let t1 = { desc = desc1; kind = Kind.Row left_left } in
        let t2 = { desc = desc2; kind = Kind.Row left_left } in
        unify t1 desc1 t2 desc2
      end
    in
    left_left_result >>= fun left_left_subst ->
    let left_right_result =
      if left_right_empty then return Subst.empty
      else begin
        let desc1 = Proj(cs1, t1, left_right) in
        let desc2 = Proj(cs2', t2', left_right) in
        let t1 = { desc = desc1; kind = Kind.Row left_right } in
        let t2 = { desc = desc2; kind = Kind.Row left_right } in
        unify t1 desc1 t2 desc2
      end
    in
    left_right_result >>= fun left_right_subst ->
    let right_left_result =
      if right_left_empty then return Subst.empty
      else begin
        let desc1 = Proj(cs1', t1', right_left) in
        let desc2 = Proj(cs2, t2, right_left) in
        let t1 = { desc = desc1; kind = Kind.Row right_left } in
        let t2 = { desc = desc2; kind = Kind.Row right_left } in
        unify t1 desc1 t2 desc2
      end
    in
    right_left_result >>= fun right_left_subst ->
    let right_right_result =
      if right_right_empty then return Subst.empty
      else begin
        let desc1 = Proj(cs1', t1', right_right) in
        let desc2 = Proj(cs2', t2', right_right) in
        let t1 = { desc = desc1; kind = Kind.Row right_right } in
        let t2 = { desc = desc2; kind = Kind.Row right_right } in
        unify t1 desc1 t2 desc2
      end
    in
    right_right_result >>| fun right_right_subst ->
    Subst.compose left_left_subst
       (Subst.compose left_right_subst
         (Subst.compose right_left_subst right_right_subst))

  let rec unify_types_desc desc1 desc2 =
    let open Result in
    match desc1, desc2 with
    | Var v, desc | desc, Var v ->
        return (Subst.add_type Subst.empty v desc)
    | Variant t1, Variant t2 ->
        unify_ranges t1 t2
    | Arrow(t1, t1'), Arrow(t2, t2') ->
        unify_types t1 t2 >>= fun subst ->
        let t1' = subst_types subst t1' in
        let t2' = subst_types subst t2' in
        unify_types t1' t2' >>| fun subst' ->
        Subst.compose subst subst'
    | (Constructor _ | Or _ | Proj _ | Row _
       | Top _ | Bot _ | Meet _ | Join _), _ ->
        assert false
    | _, (Constructor _ | Or _ | Proj _ | Row _
       | Top _ | Bot _ | Meet _ | Join _) ->
        assert false
    | _, _ -> error ()

  and unify_ranges_desc desc1 desc2 =
    let open Result in
    match desc1, desc2 with
    | Var v, desc | desc, Var v ->
        return (Subst.add_range Subst.empty v desc)
    | Row t1, Row t2 ->
        unify_row t1 t2
    | (Constructor _ | Or _ | Proj _ | Variant _ | Arrow _
       | Top _ | Bot _ | Meet _ | Join _), _ ->
        assert false
    | _, (Constructor _ | Or _ | Proj _ | Variant _ | Arrow _
       | Top _ | Bot _ | Meet _ | Join _) ->
        assert false

  and unify_row_desc t1 desc1 t2 desc2 =
    let open Result in
    match normalize desc1, normalize desc2 with
    | Constructor(_, t1), Constructor(_, t2) ->
        unify_types t1 t2
    | Or(cs1, t1, cs1', t1'), Or(cs2, t2, cs2', t2') ->
        unify_or unify_row_desc cs1 t1 cs1' t1' cs2 t2 cs2' t2'
    | Top _, Top _ -> return Subst.empty
    | Bot _, Bot _ -> return Subst.empty
    | (Var _ | Proj _ | Row _ | Variant _
       | Arrow _ | Meet _ | Join _), _ ->
        assert false
    | _, (Var _ | Proj _ | Row _ | Variant _
          | Arrow _ | Meet _ | Join _) ->
        assert false
    | _, _ -> error ()

  and biunify_row_desc t1 desc1 (* pos *) t2 desc2 (* neg *) =
    let open Result in
    match normalize desc1, normalize desc2 with
    | Proj(cs, t, cs'), desc -> begin
        match t.desc with
        | Var _ as desc' ->
            let rest = Constructor.CSet.diff cs cs' in
            let v = Var.fresh () in
            let var_t = var v (Kind.Row rest) in
            let or_desc = Or(cs', t2, rest, var_t) in
            let or_t = { desc = or_desc; kind = Kind.Row cs' } in
            biunify_row_desc t desc' or_t or_desc
        | _ -> assert false
      end
    | desc, Proj(cs, t, cs') -> begin
        match t.desc with
        | Var _ as desc' ->
            let rest = Constructor.CSet.diff cs cs' in
            let v = Var.fresh () in
            let var_t = var v (Kind.Row rest) in
            let or_desc = Or(cs', t1, rest, var_t) in
            let or_t = { desc = or_desc; kind = Kind.Row cs' } in
            biunify_row_desc or_t or_desc t desc'
        | _ -> assert false
      end
    | Var v, desc ->
        return (Subst.add_row_contravariant Subst.empty v (Meet(t2, t1)))
    | desc, Var v ->
        return (Subst.add_row_covariant Subst.empty v (Meet(t1, t2)))
    | Constructor(_, t1), Constructor(_, t2) ->
        unify_types t1 t2
    | Or(cs1, t1, cs1', t1'), Or(cs2, t2, cs2', t2') ->
        unify_or biunify_row_desc cs1 t1 cs1' t1' cs2 t2 cs2' t2'
    | _, Top _ -> return Subst.empty
    | Bot _, _ -> return Subst.empty
    | Join(t1, t1'), desc2 ->
        biunify_row_desc t1 t1.desc t2 desc2 >>= fun subst ->
        let t1' = subst_row_covariant subst t1' in
        let desc2 = subst_row_contravariant_desc subst desc2 in
        biunify_row_desc t1' t1'.desc t2 desc2 >>| fun subst' ->
        Subst.compose subst subst'
    | desc1, Meet(t2, t2') ->
        biunify_row_desc t1 desc1 t2 t2.desc >>= fun subst ->
        let desc1 = subst_row_covariant_desc subst desc1 in
        let t2' = subst_row_contravariant subst t2' in
        biunify_row_desc t1 desc1 t2' t2'.desc >>| fun subst' ->
        Subst.compose subst subst'
    | (Row _ | Variant _ | Arrow _ | Meet _), _ ->
        assert false
    | _, (Row _ | Variant _ | Arrow _ | Join _) ->
        assert false
    | _, _ -> error ()

  and unify_types t1 t2 =
    let open Result in
    Kind.unify t1.kind t2.kind >>= fun kind_subst ->
    let desc1 = subst_types_desc kind_subst t1.desc in
    let desc2 = subst_types_desc kind_subst t2.desc in
    unify_types_desc desc1 desc2 >>| fun desc_subst ->
    Subst.compose kind_subst desc_subst

  and unify_ranges t1 t2 =
    let open Result in
    Kind.unify t1.kind t2.kind >>= fun kind_subst ->
    let desc1 = subst_ranges_desc kind_subst t1.desc in
    let desc2 = subst_ranges_desc kind_subst t2.desc in
    unify_ranges_desc desc1 desc2 >>| fun desc_subst ->
    Subst.compose kind_subst desc_subst

  and unify_row t1 t2 =
    let open Result in
    Kind.unify t1.kind t2.kind >>= fun kind_subst ->
    let t1 = subst_row_invariant kind_subst t1 in
    let t2 = subst_row_invariant kind_subst t2 in
    unify_row_desc t1 t1.desc t2 t2.desc >>| fun desc_subst ->
    Subst.compose kind_subst desc_subst

  and biunify_row t1 t2 =
    let open Result in
    Kind.unify t1.kind t2.kind >>= fun kind_subst ->
    let t1 = subst_row_covariant kind_subst t1 in
    let t2 = subst_row_contravariant kind_subst t2 in
    biunify_row_desc t1 t1.desc t2 t2.desc >>| fun desc_subst ->
    Subst.compose kind_subst desc_subst

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

  val unify : t -> t -> Subst.t Result.t

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
        Range(Type.subst_row_covariant s t1, Type.subst_row_contravariant s t2)

  let subst_vars m = function
    | Type -> Type
    | Row _ as kind -> kind
    | Range(t1, t2) ->
        Range(Type.subst_vars m t1, Type.subst_vars m t2)

  let unify t1 t2 =
    let open Result in
    match t1, t2 with
    | Type, Type -> return Subst.empty
    | Row _, Row _ -> return Subst.empty
    | Range(t1, t1'), Range(t2, t2') ->
        Type.biunify_row t1 t2' >>= fun subst ->
        let t1' = Type.subst_row_contravariant subst t1' in
        let t2 = Type.subst_row_covariant subst t2 in
        Type.biunify_row t2 t1' >>| fun subst' ->
        Subst.compose subst subst'
    | _, _ -> error ()

end

and Scheme : sig

  type t

  val create : Var.Set.t -> Type.t -> t

  val of_type : Type.t -> t

  val free_variables : t -> Var.Set.t

  val subst : Subst.t -> t -> t

  val instantiate : t -> Type.t

end = struct

  type t =
    { vars : Var.Set.t;
      type_ : Type.t; }

  let create vars type_ =
    { vars; type_ }

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


and Env : sig

  type t

  val add : Ident.t -> Scheme.t -> t -> t

  val lookup : t -> Ident.t -> Scheme.t

  val free_variables : t -> Var.Set.t

  val subst : Subst.t -> t -> t

end = struct

  type t = Scheme.t Ident.Map.t

  let add id scheme t = Ident.Map.add id scheme t

  let lookup t id = Ident.Map.find id t

  let free_variables t =
    Ident.Map.fold
      (fun _ scheme acc ->
        Var.Set.union (Scheme.free_variables scheme) acc)
      t Var.Set.empty

  let subst s t =
    Ident.Map.map
      (fun _type -> Scheme.subst s _type)
      t

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

    let rows s =
      Var.Map.fold
        (fun v _ acc ->
          if Var.Map.mem v s.row_covariant then
            Var.Set.add v acc
          else acc)
        s.row_contravariant Var.Set.empty

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

  let names uses =
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
        (Uses.rows uses) (0, names)
    in
    names

  let printf = Format.printf

  let rec print_type_desc aliased names =
    let open Type in function
    | Var v -> printf "%s" (Var.Map.find v names); aliased
    | Constructor(c, t) ->
        printf "%s" (Constructor.to_string c);
        print_type aliased names t
    | Or(_, t1, _, t2) -> begin
        match t1.desc with
        | Bot _ -> print_type aliased names t2
        | _ ->
            let aliased = print_type aliased names t1 in
            match t2.desc with
            | Bot _ -> aliased
            | _ ->
                printf " | ";
                print_type aliased names t2
      end
    | Proj _ -> assert false
    | Row _ -> assert false
    | Variant t -> begin
        match t.desc with
        | Var v ->
            if Var.Set.mem v aliased then begin
              printf "%s" (Var.Map.find v names);
              aliased
            end else begin
              match Var.Map.find v names with
              | s ->
                  let aliased = Var.Set.add v aliased in
                  let aliased = print_kind aliased names t.kind in
                  printf "as %s" s;
                  aliased
              | exception Not_found ->
                  print_kind aliased names t.kind
            end
        | Row t ->
            printf "[";
            let aliased = print_type aliased names t in
            printf "]";
            aliased
        | _ -> assert false
      end
    | Arrow(t1, t2) ->
        let aliased = print_type aliased names t1 in
        printf " -> ";
        print_type aliased names t2
    | Top _ ->
        printf "top";
        aliased
    | Bot _ ->
        printf "bot";
        aliased
    | Meet(t1, t2) ->
        printf "(";
        let aliased = print_type aliased names t1 in
        printf " & ";
        let aliased = print_type aliased names t2 in
        printf ")";
        aliased
    | Join(t1, t2) ->
        let aliased = print_type aliased names t1 in
        printf " | ";
        print_type aliased names t2

    and print_type aliased names t =
      let open Type in
      print_type_desc aliased names t.desc

    and print_kind aliased names =
      let open Kind in function
      | Type | Row _ -> assert false
      | Range(t1, t2) ->
          match t1.desc, t2.desc with
          | Bot _, Top _ ->
              printf "[+bot -top]";
              aliased
          | Bot _, _ ->
              printf "[-";
              let aliased = print_type aliased names t2 in
              printf "]";
              aliased
          | _, Top _ ->
              printf "[+";
              let aliased = print_type aliased names t1 in
              printf "]";
              aliased
          | _, _ ->
              printf "[+";
              let aliased = print_type aliased names t1 in
              printf " -";
              let aliased = print_type aliased names t2 in
              printf "]";
              aliased

  let print t =
    let uses = analyse_type_vars_types t in
    let subst =
      Var.Map.fold
        (fun v cs acc -> Subst.add_row_covariant acc v (Type.Bot cs))
        (Uses.only_row_covariant uses) Subst.empty
    in
    let subst =
      Var.Map.fold
        (fun v cs acc -> Subst.add_row_contravariant acc v (Type.Top cs))
        (Uses.only_row_contravariant uses) subst
    in
    let t = Type.subst_types subst t in
    let names = names uses in
    ignore (print_type Var.Set.empty names t)

end
