(************************************************
 *          Row Subtyping - Definitions         *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import  List LibLN Cofinite.
Implicit Types x : var.
Implicit Types X : var.

(* *************************************************************** *)
(** ** Description of types *)

(** Representation of pre-types *)

Inductive typ : Type :=
  | typ_bvar : nat -> typ
  | typ_fvar : var -> typ
  | typ_constructor : nat -> typ -> typ
  | typ_or : cset -> typ -> cset -> typ -> typ
  | typ_proj : cset -> typ -> cset -> typ
  | typ_variant : typ -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_ref   : typ -> typ
  | typ_unit : typ
  | typ_prod : typ -> typ -> typ
  | typ_top : cset -> typ
  | typ_bot : cset -> typ
  | typ_meet : typ -> typ -> typ
  | typ_join : typ -> typ -> typ.

Definition typ_fvars Xs :=
  List.map typ_fvar Xs.

(* Kinds *)

Inductive knd : Type :=
  | knd_type : knd
  | knd_row : cset -> knd
  | knd_range : knd.

(* Range kinds *)

Inductive rng : Type :=
  | rng_type : rng
  | rng_row : cset -> rng
  | rng_range : typ -> typ -> rng.

Notation rng_range_all :=
  (rng_range (typ_top CSet.universe)
             (typ_bot CSet.universe)).

Notation rng_range_below T :=
  (rng_range T (typ_bot CSet.universe)).

Notation rng_range_above T :=
  (rng_range (typ_top CSet.universe) T).

(** Type schemes. *)

Inductive sch : Type := Sch { 
  sch_ranges : list rng ; 
  sch_body  : typ }.

Definition sch_empty T := Sch nil T.

Fixpoint sch_arity (M : sch) : nat :=
  List.length (sch_ranges M).

(** Opening a type. *)

Fixpoint typ_open (T : typ) (Us : list typ) : typ :=
  match T with
  | typ_bvar i => List.nth i Us (typ_bvar i)
  | typ_fvar x => typ_fvar x 
  | typ_constructor c T => typ_constructor c (typ_open T Us)
  | typ_or cs1 T1 cs2 T2 =>
    typ_or cs1 (typ_open T1 Us) cs2 (typ_open T2 Us)
  | typ_proj cs1 T cs2 => typ_proj cs1 (typ_open T Us) cs2
  | typ_variant T => typ_variant (typ_open T Us)
  | typ_arrow T1 T2 =>
    typ_arrow (typ_open T1 Us) (typ_open T2 Us)
  | typ_ref T => typ_ref (typ_open T Us)
  | typ_unit => typ_unit
  | typ_prod T1 T2 =>
    typ_prod (typ_open T1 Us) (typ_open T2 Us)
  | typ_top cs => typ_top cs
  | typ_bot cs => typ_bot cs
  | typ_meet T1 T2 =>
    typ_meet (typ_open T1 Us) (typ_open T2 Us)
  | typ_join T1 T2 =>
    typ_join (typ_open T1 Us) (typ_open T2 Us)
  end.

Definition typ_open_vars T Xs := typ_open T (typ_fvars Xs).

(** Opening a range. *)

Definition rng_open (R : rng) (Us : list typ) : rng :=
  match R with
  | rng_type => rng_type
  | rng_row cs => rng_row cs
  | rng_range T1 T2 =>
    rng_range (typ_open T1 Us) (typ_open T2 Us)
  end.

Definition rng_open_vars R Xs := rng_open R (typ_fvars Xs).

Definition rng_open_list Rs Us :=
  List.map (fun R => rng_open R Us) Rs.

Definition rng_open_vars_list Rs Xs :=
  rng_open_list Rs (typ_fvars Xs).

(** Instanciation of a type scheme *)

Definition instance (M : sch) (Us : list typ) : typ :=
  typ_open (sch_body M) Us.

Definition instance_vars M Xs :=
  instance M (typ_fvars Xs).

(** Well-formed types *)

Inductive type : typ -> Prop :=
  | type_fvar : forall X, 
      type (typ_fvar X)
  | type_constructor : forall c T,
      type T ->
      type (typ_constructor c T)
  | type_or : forall cs1 T1 cs2 T2,
      type T1 ->
      type T2 ->
      type (typ_or cs1 T1 cs2 T2)
  | type_proj : forall T cs1 cs2,
      type T ->
      type (typ_proj cs1 T cs2)
  | type_variant : forall T,
      type T ->
      type (typ_variant T)
  | type_arrow : forall T1 T2,
      type T1 -> 
      type T2 -> 
      type (typ_arrow T1 T2)
  | type_ref : forall T,
      type T ->
      type (typ_ref T)
  | type_unit :
      type typ_unit
  | type_prod : forall T1 T2,
      type T1 -> 
      type T2 -> 
      type (typ_prod T1 T2)
  | type_top : forall cs,
      type (typ_top cs)
  | type_bot : forall cs,
      type (typ_bot cs)
  | type_meet : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_meet T1 T2)
  | type_join : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_join T1 T2).

Inductive types : list typ -> Prop :=
  | types_nil : types nil
  | types_cons : forall T Ts,
      type T ->
      types Ts ->
      types (T :: Ts).

(** Well-formed kinds *)

Inductive kind : knd -> Prop :=
  | kind_type : kind knd_type
  | kind_row : forall cs,
      CSet.Nonempty cs -> kind (knd_row cs)
  | kind_range : kind knd_range.

Inductive kinds : list knd -> Prop :=
  | kinds_nil : kinds nil
  | kinds_cons : forall K Ks,
      kind K ->
      kinds Ks ->
      kinds (K :: Ks).

(** Well-formed ranges *)

Inductive range : rng -> Prop :=
  | range_type : range rng_type
  | range_row : forall cs,
      CSet.Nonempty cs -> range (rng_row cs)
  | range_range : forall T1 T2,
      type T1 ->
      type T2 ->
      range (rng_range T1 T2).

Inductive ranges : list rng -> Prop :=
  | ranges_nil : ranges nil
  | ranges_cons : forall R Rs,
      range R ->
      ranges Rs ->
      ranges (R :: Rs).

(** Well-formed schemes *)

Inductive ranges_and_type : list rng -> typ -> Prop :=
  | ranges_and_type_c : forall Rs T,
      ranges Rs ->
      type T ->
      ranges_and_type Rs T.

Inductive scheme : sch -> Prop :=
  | scheme_c : forall L M,
      (forall Xs,
          fresh L (sch_arity M) Xs ->
          ranges_and_type
            (rng_open_vars_list (sch_ranges M) Xs)
            (typ_open_vars (sch_body M) Xs)) ->
      scheme M.

Inductive schemes : list sch -> Prop :=
  | schemes_nil : schemes nil
  | schemes_cons : forall M Ms,
      scheme M ->
      schemes Ms ->
      schemes (M :: Ms).

(* ************************************************************** *)
(** ** Description of terms *)

Definition loc := var.

(** Representation of pre-terms *)

Inductive trm : Type :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_abs : trm -> trm
  | trm_let : trm -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_constructor : nat -> trm -> trm
  | trm_match : trm -> nat -> trm -> trm -> trm
  | trm_destruct : trm -> nat -> trm -> trm
  | trm_absurd : trm -> trm
  | trm_fix : trm -> trm
  | trm_unit : trm
  | trm_prod : trm -> trm -> trm
  | trm_fst : trm -> trm
  | trm_snd : trm -> trm
  | trm_loc : loc -> trm
  | trm_ref : trm -> trm
  | trm_get : trm -> trm
  | trm_set : trm -> trm -> trm.

Fixpoint var_open (k : nat) (us : list trm) (i : nat) (t : trm) : trm :=
  match k with
  | 0 => List.nth i us t
  | S k =>
    match i with
    | 0 => t
    | S i => var_open k us i t
    end
  end.

Fixpoint trm_open_rec (k : nat) (us : list trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i  => var_open k us i (trm_bvar i)
  | trm_fvar x => trm_fvar x 
  | trm_abs t1 => trm_abs (trm_open_rec (S k) us t1) 
  | trm_let t1 t2 =>
      trm_let (trm_open_rec k us t1) (trm_open_rec (S k) us t2) 
  | trm_app t1 t2 =>
      trm_app (trm_open_rec k us t1) (trm_open_rec k us t2)
  | trm_constructor c t =>
      trm_constructor c (trm_open_rec k us t)
  | trm_match t1 c t2 t3 =>
      trm_match (trm_open_rec k us t1) c
                (trm_open_rec (S k) us t2)
                (trm_open_rec (S k) us t3)
  | trm_destruct t1 c t2 =>
      trm_destruct (trm_open_rec k us t1) c
                   (trm_open_rec (S k) us t2)
  | trm_absurd t1 => trm_absurd (trm_open_rec k us t1)
  | trm_fix t1 => trm_fix (trm_open_rec (S (S k)) us t1)
  | trm_unit => trm_unit
  | trm_prod t1 t2 =>
      trm_prod (trm_open_rec k us t1) (trm_open_rec k us t2)
  | trm_fst t1 => trm_fst (trm_open_rec k us t1)
  | trm_snd t1 => trm_snd (trm_open_rec k us t1)
  | trm_loc l => trm_loc l
  | trm_ref t1 => trm_ref (trm_open_rec k us t1)
  | trm_get t1 => trm_get (trm_open_rec k us t1)
  | trm_set t1 t2 => trm_set (trm_open_rec k us t1) (trm_open_rec k us t2)
  end.

Definition trm_open t us := trm_open_rec 0 us t.
Definition trm_fvars := List.map trm_fvar.

Notation "{ k ~> us } t" := (trm_open_rec k us t)
  (at level 67) : trm_scope.

Notation "t ^^* us" := (trm_open t us) (at level 67) : trm_scope.
Notation "t ^^ u" := (trm_open t (u::nil)) (at level 67) : trm_scope.
Notation "t ^* xs" :=
  (trm_open t (trm_fvars xs)) (at level 67) : trm_scope.
Notation "t ^ x" := (trm_open t ((trm_fvar x)::nil)) : trm_scope.

Bind Scope trm_scope with trm.
Open Scope trm_scope.

(** Locally closed term *)

Inductive term : trm -> Prop :=
  | term_var : forall x, 
      term (trm_fvar x)
  | term_abs : forall L t1,
      (forall x, x \notin L -> term (t1 ^ x)) -> 
      term (trm_abs t1)
  | term_let : forall L t1 t2,
      term t1 -> 
      (forall x, x \notin L -> term (t2 ^ x)) -> 
      term (trm_let t1 t2)
  | term_app : forall t1 t2,
      term t1 -> 
      term t2 -> 
      term (trm_app t1 t2)
  | term_constructor : forall c t,
      term t ->
      term (trm_constructor c t)
  | term_match : forall L t1 c t2 t3,
      term t1 ->
      (forall x, x \notin L -> term (t2 ^ x)) ->
      (forall x, x \notin L -> term (t3 ^ x)) ->
      term (trm_match t1 c t2 t3)
  | term_destruct : forall L t1 c t2,
      term t1 ->
      (forall x, x \notin L -> term (t2 ^ x)) ->
      term (trm_destruct t1 c t2)
  | term_absurd : forall t,
      term t ->
      term (trm_absurd t)
  | term_fix : forall L t,
      (forall x y,
          x \notin L -> y \notin (L \u \{x}) ->
          term (t ^* (x::y::nil))) ->
      term (trm_fix t)
  | term_unit :
      term trm_unit
  | term_prod : forall t1 t2,
      term t1 -> 
      term t2 -> 
      term (trm_prod t1 t2)
  | term_fst : forall t,
      term t ->
      term (trm_fst t)
  | term_snd : forall t,
      term t ->
      term (trm_snd t)
  | term_loc : forall l,
      term (trm_loc l)
  | term_ref : forall t,
      term t ->
      term (trm_ref t)
  | term_get : forall t,
      term t ->
      term (trm_get t)
  | term_set : forall t1 t2,
      term t1 ->
      term t2 ->
      term (trm_set t1 t2).

Inductive terms : list trm -> Prop :=
  | terms_nil : terms nil
  | terms_cons : forall T Ts,
      term T ->
      terms Ts ->
      terms (T :: Ts).

(** Definition of the body of an abstraction *)

Definition term_body t :=
  exists L, forall x, x \notin L -> term (t ^ x).

Definition term_body2 t :=
  exists L, forall x y,
  x \notin L -> y \notin (L \u \{x}) -> term (t ^* (x::y::nil)).

(* ****************************************************** *)
(** ** Description of range environments *)

(** Pre-environment is an associative list of bindings. *)

Definition tenv := LibEnv.env rng.

Definition bind_sch_ranges (Xs : list var) (M : sch) : tenv :=
  Xs ~* (rng_open_vars_list (sch_ranges M) Xs).

Notation "Xs ~: M" := (bind_sch_ranges Xs M)
  (at level 23, left associativity) : env_scope.

(** Environment is a pre-environment with unique bindings *)

Inductive type_environment : tenv -> Prop :=
  | type_environment_empty :
      type_environment empty
  | type_environment_push : forall E X R,
      type_environment E ->
      range R ->
      X # E ->
      type_environment (E & X ~ R).

(* ****************************************************** *)
(** ** Description of typing environments *)

(** Pre-environment is an associative list of bindings. *)

Definition env := LibEnv.env sch.

(** Environment is a pre-environment with unique bindings *)

Inductive environment : env -> Prop :=
  | environment_empty :
      environment empty
  | environment_push : forall E x M,
      environment E ->
      scheme M ->
      x # E ->
      environment (E & x ~ M).

(** ************************************************** *)
(** ** Judgements *)
(* The parameters of judgements are either "inputs",
   "subjects" or "outputs". The subject of a judgement
   is the parameter whose "validity" is being checked
   by the judgement (e.g. [valid_range] checks that a
   [range] is valid). Not all judgements have a subject,
   some of them are instead checking a relationship
   between parameters. The inputs of a judgement are
   assumed to be valid by the judgement and that validity
   is not re-checked by the judgement. The outputs of
   a judgement have their validity ensured by the judgement
   (assuming that the inputs are valid).
*)

(** ************************************************** *)
(** Kinding *)

Definition rng_knd R :=
  match R with
  | rng_type => knd_type
  | rng_row cs => knd_row cs
  | rng_range _ _ => knd_range
  end.

Definition rngs_knds Rs :=
  List.map rng_knd Rs.

(* inputs: tenv
   subject: typ
   outputs: knd *)
Inductive kinding : tenv -> typ -> knd -> Prop :=
  | kinding_var : forall E X R K,
      binds X R E ->
      K = rng_knd R ->
      kinding E (typ_fvar X) K
  | kinding_constructor : forall E c T cs,
      kinding E T knd_type ->
      cs = CSet.singleton c ->
      kinding E (typ_constructor c T) (knd_row cs)
  | kinding_or : forall E T1 T2 cs1 cs2 cs12,
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      kinding E (typ_or cs1 T1 cs2 T2) (knd_row cs12)
  | kinding_proj : forall E T cs1 cs2,
      kinding E T (knd_row cs1) ->
      CSet.Subset cs2 cs1 ->
      CSet.Nonempty cs2 ->
      kinding E (typ_proj cs1 T cs2) (knd_row cs2)
  | kinding_variant : forall E T,
      kinding E T knd_range ->
      kinding E (typ_variant T) knd_type
  | kinding_arrow : forall E T1 T2,
      kinding E T1 knd_type -> 
      kinding E T2 knd_type -> 
      kinding E (typ_arrow T1 T2) knd_type
  | kinding_ref : forall E T,
      kinding E T knd_type ->
      kinding E (typ_ref T) knd_type
  | kinding_unit : forall E,
      kinding E typ_unit knd_type
  | kinding_prod : forall E T1 T2,
      kinding E T1 knd_type -> 
      kinding E T2 knd_type -> 
      kinding E (typ_prod T1 T2) knd_type
  | kinding_top : forall E cs,
      CSet.Nonempty cs ->
      kinding E (typ_top cs) (knd_row cs)
  | kinding_bot : forall E cs,
      CSet.Nonempty cs ->
      kinding E (typ_bot cs) (knd_row cs)
  | kinding_meet : forall E T1 T2 cs,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      kinding E (typ_meet T1 T2) (knd_row cs)
  | kinding_join : forall E T1 T2 cs,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      kinding E (typ_join T1 T2) (knd_row cs).

(* inputs: tenv
   subject: list typ
   outputs: list knd *)
Inductive kindings : tenv -> list typ -> list knd -> Prop :=
  | kindings_nil : forall E,
      kindings E nil nil
  | kindings_cons : forall E T Ts K Ks,
      kinding E T K ->
      kindings E Ts Ks ->
      kindings E (T :: Ts) (K :: Ks).

(** ************************************************** *)
(** ** Equality *)

(** Core of the equality relation on types *)

(* inputs: tenv
   subjects: typ(1), typ(2)
   outputs: knd *)
Inductive type_equal_core
  : tenv -> typ -> typ -> knd -> Prop :=
  | type_equal_core_or_commutative :
      forall E T1 T2 cs1 cs2 cs12,
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_core E
        (typ_or cs1 T1 cs2 T2) (typ_or cs2 T2 cs1 T1)
        (knd_row cs12)
  | type_equal_core_or_associative :
      forall E T1 T2 T3 cs1 cs2 cs3 cs12 cs23 cs123,
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs2) ->
      kinding E T3 (knd_row cs3) ->
      CSet.Disjoint cs1 cs2 ->
      CSet.Disjoint cs1 cs3 ->
      CSet.Disjoint cs2 cs3 ->
      cs12 = CSet.union cs1 cs2 ->
      cs23 = CSet.union cs2 cs3 ->
      cs123 = CSet.union cs1 cs23 ->
      type_equal_core E
        (typ_or cs1 T1 cs23 (typ_or cs2 T2 cs3 T3))
        (typ_or cs12 (typ_or cs1 T1 cs2 T2) cs3 T3)
        (knd_row cs123)
  | type_equal_core_or_bot : forall E cs1 cs2 cs12,
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_core E
        (typ_or cs1 (typ_bot cs1) cs2 (typ_bot cs2))
        (typ_bot cs12) (knd_row cs12)
  | type_equal_core_or_top : forall E cs1 cs2 cs12,
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_core E
        (typ_or cs1 (typ_top cs1) cs2 (typ_top cs2))
        (typ_top cs12) (knd_row cs12)
  | type_equal_core_or_meet_distribution :
      forall E T1 T2 T3 T4 cs1 cs2 cs12,
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs2) ->
      kinding E T3 (knd_row cs1) ->
      kinding E T4 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_core E
        (typ_or cs1 (typ_meet T1 T3) cs2 (typ_meet T2 T4))
        (typ_meet (typ_or cs1 T1 cs2 T2)
                  (typ_or cs1 T3 cs2 T4))
        (knd_row cs12)
  | type_equal_core_or_join_distribution :
      forall E T1 T2 T3 T4 cs1 cs2 cs12,
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs2) ->
      kinding E T3 (knd_row cs1) ->
      kinding E T4 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_core E
        (typ_or cs1 (typ_join T1 T3) cs2 (typ_join T2 T4))
        (typ_join (typ_or cs1 T1 cs2 T2)
                  (typ_or cs1 T3 cs2 T4))
        (knd_row cs12)
  | type_equal_core_or_proj :
      forall E T cs1 cs2 cs3 cs23,
      kinding E T (knd_row cs1) ->
      CSet.Nonempty cs2 ->
      CSet.Nonempty cs3 ->
      CSet.Subset cs2 cs1 ->
      CSet.Subset cs3 cs1 ->
      CSet.Disjoint cs2 cs3 ->
      cs23 = CSet.union cs2 cs3 ->
      type_equal_core E
        (typ_or cs2 (typ_proj cs1 T cs2)
                cs3 (typ_proj cs1 T cs3))
        (typ_proj cs1 T cs23) (knd_row cs23)
  | type_equal_core_proj_id : forall E T cs1,
      kinding E T (knd_row cs1) ->
      type_equal_core E
        (typ_proj cs1 T cs1) T (knd_row cs1)
  | type_equal_core_proj_compose : forall E T cs1 cs2 cs3,
      kinding E T (knd_row cs1) ->
      CSet.Subset cs2 cs1 ->
      CSet.Subset cs3 cs2 ->
      CSet.Nonempty cs3 ->
      type_equal_core E
        (typ_proj cs2 (typ_proj cs1 T cs2) cs3)
        (typ_proj cs1 T cs3) (knd_row cs3)
  | type_equal_core_proj_or_l :
      forall E T1 T2 cs1 cs2 cs3 cs12,
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs2) ->
      CSet.Subset cs3 cs1 ->
      CSet.Nonempty cs3 ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_core E
        (typ_proj cs12 (typ_or cs1 T1 cs2 T2) cs3)
        (typ_proj cs1 T1 cs3) (knd_row cs3)
  | type_equal_core_proj_or_r :
      forall E T1 T2 cs1 cs2 cs3 cs12,
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs2) ->
      CSet.Subset cs3 cs2 ->
      CSet.Nonempty cs3 ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_core E
        (typ_proj cs12 (typ_or cs1 T1 cs2 T2) cs3)
        (typ_proj cs2 T2 cs3) (knd_row cs3)
  | type_equal_core_proj_or_both :
      forall E T1 T2 cs1 cs2 cs3 cs4 cs12 cs34,
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs2) ->
      CSet.Subset cs3 cs1 ->
      CSet.Subset cs4 cs2 ->
      CSet.Nonempty cs3 ->
      CSet.Nonempty cs4 ->
      CSet.Disjoint cs1 cs2 ->
      CSet.Disjoint cs3 cs4 ->
      cs12 = CSet.union cs1 cs2 ->
      cs34 = CSet.union cs3 cs4 ->
      type_equal_core E
        (typ_proj cs12 (typ_or cs1 T1 cs2 T2) cs34)
        (typ_or cs3 (typ_proj cs1 T1 cs3)
                cs4 (typ_proj cs2 T2 cs4))
        (knd_row cs34)
  | type_equal_core_proj_meet : forall E T1 T2 cs1 cs2,
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs1) ->
      CSet.Subset cs2 cs1 ->
      CSet.Nonempty cs2 ->
      type_equal_core E
        (typ_proj cs1 (typ_meet T1 T2) cs2)
        (typ_meet (typ_proj cs1 T1 cs2)
                  (typ_proj cs1 T2 cs2))
        (knd_row cs2)
  | type_equal_core_proj_join : forall E T1 T2 cs1 cs2,
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs1) ->
      CSet.Subset cs2 cs1 ->
      CSet.Nonempty cs2 ->
      type_equal_core E
        (typ_proj cs1 (typ_join T1 T2) cs2)
        (typ_join (typ_proj cs1 T1 cs2)
                  (typ_proj cs1 T2 cs2))
        (knd_row cs2)
  | type_equal_core_meet_commutative : forall E T1 T2 cs1,
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs1) ->
      type_equal_core E (typ_meet T1 T2) (typ_meet T2 T1)
        (knd_row cs1)
  | type_equal_core_meet_associative : forall E T1 T2 T3 cs1,
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs1) ->
      kinding E T3 (knd_row cs1) ->
      type_equal_core E
        (typ_meet T1 (typ_meet T2 T3))
        (typ_meet (typ_meet T1 T2) T3)
        (knd_row cs1)
  | type_equal_core_meet_identity : forall E T1 cs1,
      kinding E T1 (knd_row cs1) ->
      type_equal_core E (typ_meet T1 (typ_top cs1)) T1
        (knd_row cs1)
  | type_equal_core_meet_absorption : forall E T1 T2 cs1,
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs1) ->
      type_equal_core E (typ_meet T1 (typ_join T1 T2)) T1
        (knd_row cs1)
  | type_equal_core_meet_distribution :
      forall E T1 T2 T3 cs1,
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs1) ->
      kinding E T3 (knd_row cs1) ->
      type_equal_core E
        (typ_meet T1 (typ_join T2 T3))
        (typ_join (typ_meet T1 T2) (typ_meet T1 T3))
        (knd_row cs1)
  | type_equal_core_join_commutative : forall E T1 T2 cs1,
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs1) ->
      type_equal_core E (typ_join T1 T2) (typ_join T2 T1)
        (knd_row cs1)
  | type_equal_core_join_associative : forall E T1 T2 T3 cs1,
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs1) ->
      kinding E T3 (knd_row cs1) ->
      type_equal_core E
        (typ_join T1 (typ_join T2 T3))
        (typ_join (typ_join T1 T2) T3)
        (knd_row cs1)
  | type_equal_core_join_identity : forall E T1 cs1,
      kinding E T1 (knd_row cs1) ->
      type_equal_core E (typ_join T1 (typ_bot cs1)) T1
        (knd_row cs1)
  | type_equal_core_join_absorption : forall E T1 T2 cs1,
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs1) ->
      type_equal_core E (typ_join T1 (typ_meet T1 T2)) T1
        (knd_row cs1)
  | type_equal_core_join_distribution :
      forall E T1 T2 T3 cs1,
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs1) ->
      kinding E T3 (knd_row cs1) ->
      type_equal_core E
        (typ_join T1 (typ_meet T2 T3))
        (typ_meet (typ_join T1 T2) (typ_join T1 T3))
        (knd_row cs1).

(* Symetric closure of type_equal_core *)

(* inputs: tenv
   subjects: typ(1), typ(2)
   outputs: knd *)
Inductive type_equal_symm
  : tenv -> typ -> typ -> knd -> Prop :=
  | type_equal_symm_l : forall E T1 T2 K,
      type_equal_core E T1 T2 K ->
      type_equal_symm E T1 T2 K
  | type_equal_symm_r : forall E T1 T2 K,
      type_equal_core E T1 T2 K ->
      type_equal_symm E T2 T1 K.

(* Congruence closure of type_equal_symm *)

(* inputs: tenv
   subjects: typ(1), typ(2)
   outputs: knd *)
Inductive type_equal_cong
  : tenv -> typ -> typ -> knd -> Prop :=
  | type_equal_cong_constructor : forall E c T1 T1' cs,
      type_equal_cong E T1 T1' knd_type ->
      cs = CSet.singleton c ->
      type_equal_cong E
        (typ_constructor c T1) (typ_constructor c T1')
        (knd_row cs)
  | type_equal_cong_or_l : forall E T1 T1' T2 cs1 cs2 cs12,
      type_equal_cong E T1 T1' (knd_row cs1) ->
      kinding E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_cong E
        (typ_or cs1 T1 cs2 T2) (typ_or cs1 T1' cs2 T2)
        (knd_row cs12)
  | type_equal_cong_or_r : forall E T1 T2 T2' cs1 cs2 cs12,
      type_equal_cong E T2 T2' (knd_row cs2) ->
      kinding E T1 (knd_row cs1) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_cong E (typ_or cs1 T1 cs2 T2)
        (typ_or cs1 T1 cs2 T2') (knd_row cs12)
  | type_equal_cong_proj : forall E T1 T1' cs1 cs2,
      type_equal_cong E T1 T1' (knd_row cs1) ->
      CSet.Subset cs2 cs1 ->
      CSet.Nonempty cs2 ->
      type_equal_cong E (typ_proj cs1 T1 cs2)
        (typ_proj cs1 T1' cs2) (knd_row cs2)
  | type_equal_cong_variant : forall E T1 T1',
      type_equal_cong E T1 T1' knd_range ->
      type_equal_cong E (typ_variant T1)
        (typ_variant T1') knd_type
  | type_equal_cong_arrow_l : forall E T1 T1' T2,
      type_equal_cong E T1 T1' knd_type ->
      kinding E T2 knd_type ->
      type_equal_cong E (typ_arrow T1 T2)
        (typ_arrow T1' T2) knd_type
  | type_equal_cong_arrow_r : forall E T1 T2 T2',
      kinding E T1 knd_type ->
      type_equal_cong E T2 T2' knd_type ->
      type_equal_cong E (typ_arrow T1 T2)
        (typ_arrow T1 T2') knd_type
  | type_equal_cong_prod_l : forall E T1 T1' T2,
      type_equal_cong E T1 T1' knd_type ->
      kinding E T2 knd_type ->
      type_equal_cong E (typ_prod T1 T2)
        (typ_prod T1' T2) knd_type
  | type_equal_cong_prod_r : forall E T1 T2 T2',
      type_equal_cong E T2 T2' knd_type ->
      kinding E T1 knd_type ->
      type_equal_cong E (typ_prod T1 T2)
        (typ_prod T1 T2') knd_type
  | type_equal_cong_ref : forall E T1 T1',
      type_equal_cong E T1 T1' knd_type ->
      type_equal_cong E (typ_ref T1) (typ_ref T1') knd_type
  | type_equal_cong_meet_l : forall E T1 T1' T2 cs1,
      type_equal_cong E T1 T1' (knd_row cs1) ->
      kinding E T2 (knd_row cs1) ->
      type_equal_cong E (typ_meet T1 T2)
        (typ_meet T1' T2) (knd_row cs1)
  | type_equal_cong_meet_r : forall E T1 T2 T2' cs1,
      type_equal_cong E T2 T2' (knd_row cs1) -> 
      kinding E T1 (knd_row cs1) ->
      type_equal_cong E (typ_meet T1 T2)
        (typ_meet T1 T2') (knd_row cs1)
  | type_equal_cong_join_l : forall E T1 T1' T2 cs1,
      type_equal_cong E T1 T1' (knd_row cs1) ->
      kinding E T2 (knd_row cs1) ->
      type_equal_cong E (typ_join T1 T2)
        (typ_join T1' T2) (knd_row cs1)
  | type_equal_cong_join_r : forall E T1 T2 T2' cs1,
      type_equal_cong E T2 T2' (knd_row cs1) ->
      kinding E T1 (knd_row cs1) ->
      type_equal_cong E (typ_join T1 T2)
        (typ_join T1 T2') (knd_row cs1)
  | type_equal_cong_symm : forall E T1 T1' K,
      type_equal_symm E T1 T1' K ->
      type_equal_cong E T1 T1' K.

(* Reflexive transitive closure of type_equal_cong *)

(* inputs: tenv
   subject: typ(1), typ(2)
   outputs: knd *)
Inductive type_equal : tenv -> typ -> typ -> knd -> Prop :=
  | type_equal_refl : forall E T K,
      kinding E T K ->
      type_equal E T T K
  | type_equal_step : forall E T1 T2 T3 K,
      type_equal_cong E T1 T2 K ->
      type_equal E T2 T3 K ->
      type_equal E T1 T3 K.

(* Subtyping *)

(* inputs: tenv
   subject: typ(1), typ(2)
   outputs: cset *)
Inductive subtype : tenv -> typ -> typ -> cset -> Prop :=
  | subtype_c : forall E T1 T2 cs,
      type_equal E T1 (typ_meet T1 T2) (knd_row cs) ->
      subtype E T1 T2 cs.

(** ************************************************** *)
(* Validity of ranges, schemes and kinding environments *)

(* Validity of ranges *)

(* inputs: tenv
   subject: rng
   outputs: *)
Inductive valid_range : tenv -> rng -> Prop :=
  | valid_range_type : forall E,
      valid_range E rng_type
  | valid_range_row : forall E cs,
      CSet.Nonempty cs ->
      valid_range E (rng_row cs)
  | valid_range_range : forall E T1 T2,
      subtype E T2 T1 CSet.universe ->
      valid_range E (rng_range T1 T2).

(* inputs: tenv
   subject: list rng
   outputs: *)
Inductive valid_ranges : tenv -> list rng -> Prop :=
  | valid_ranges_nil : forall E,
      valid_ranges E nil
  | valid_ranges_cons : forall E R Rs,
      valid_range E R ->
      valid_ranges E Rs ->
      valid_ranges E (R :: Rs).

(* Validity of type schemes *)

(* inputs: tenv
   subjects: list rng, typ
   outputs: *)
Inductive valid_ranges_and_type
  : tenv -> list rng -> typ -> Prop :=
  | valid_ranges_and_type_c : forall E Rs T,
      valid_ranges E Rs ->
      kinding E T knd_type ->
      valid_ranges_and_type E Rs T.

(* inputs: tenv
   subject: sch
   outputs: *)
Inductive valid_scheme : tenv -> sch -> Prop :=
  | valid_scheme_c : forall L E M,
      (forall Xs,
          fresh L (sch_arity M) Xs ->
          valid_ranges_and_type (E & Xs ~: M)
            (rng_open_vars_list (sch_ranges M) Xs)
            (typ_open_vars (sch_body M) Xs)) ->
      valid_scheme E M.

(* inputs: tenv
   subject: list sch
   outputs: *)
Inductive valid_schemes : tenv -> list sch -> Prop :=
  | valid_schemes_nil : forall E,
      valid_schemes E nil
  | valid_schemes_cons : forall E M Ms,
      valid_scheme E M ->
      valid_schemes E Ms ->
      valid_schemes E (M :: Ms).

(* Validity of kinding environments *)

(* inputs: tenv(1)
   subject: tenv(2)
   outputs: *)
Inductive valid_tenv_aux : tenv -> tenv -> Prop :=
  | valid_tenv_aux_empty : forall E,
      valid_tenv_aux E empty
  | valid_tenv_aux_push : forall E1 E2 X R,
      valid_tenv_aux E1 E2 ->
      valid_range E1 R ->
      X # E2 ->
      valid_tenv_aux E1 (E2 & X ~ R).

(* inputs:
   subject: tenv
   outputs: *)
Inductive valid_tenv : tenv -> Prop :=
  | valid_tenv_c : forall E,
      valid_tenv_aux E E ->
      valid_tenv E.

(** ************************************************** *)
(** Ranging *)

(* inputs: tenv
   subject: typ
   outputs: rng *)
Inductive ranging : tenv -> typ -> rng -> Prop :=
  | ranging_kinding_type : forall E T,
      kinding E T knd_type ->
      ranging E T rng_type
  | ranging_kinding_row : forall E T cs,
      kinding E T (knd_row cs) ->
      ranging E T (rng_row cs)
  | ranging_var : forall E X R ,
      binds X R E ->
      ranging E (typ_fvar X) R
  | ranging_range_subsumption : forall E T T1 T2 T1' T2',
      ranging E T (rng_range T1 T2) ->
      subtype E T1 T1' CSet.universe ->
      subtype E T2' T2 CSet.universe ->
      ranging E T (rng_range T1' T2').

(* inputs: tenv
   subject: list typ
   outputs: list rng *)
Inductive rangings : tenv -> list typ -> list rng -> Prop :=
  | rangings_nil : forall E,
      rangings E nil nil
  | rangings_cons : forall E T Ts R Rs,
      ranging E T R ->
      rangings E Ts Rs ->
      rangings E (T :: Ts) (R :: Rs).

(** Validity of instances *)

(* inputs: tenv, sch
   subject: list typ
   outputs: *)
Inductive valid_instance : tenv -> list typ -> sch -> Prop :=
  | valid_instance_c : forall E Ts Rs M,
      rangings E Ts Rs ->
      Rs = rng_open_list (sch_ranges M) Ts ->
      valid_instance E Ts M.

(* ****************************************************** *)
(** ** Environments *)

(* Validity of typing environments *)

(* inputs: tenv
   subject: env
   outputs: *)
Inductive valid_env : tenv -> env -> Prop :=
  | valid_env_empty : forall E,
      valid_env E empty
  | valid_env_push : forall E D x M,
      valid_env E D ->
      valid_scheme E M ->
      x # D ->
      valid_env E (D & x ~ M).

(* ****************************************************** *)
(** ** Stores *)

(** Grammar of values *)

Inductive value : trm -> Prop :=
  | value_constructor : forall c t,
      value t -> value (trm_constructor c t)
  | value_abs : forall t,
      term (trm_abs t) -> value (trm_abs t)
  | value_fix : forall t,
      term (trm_fix t) -> value (trm_fix t)
  | value_unit :
      value trm_unit
  | value_prod : forall t1 t2,
      value t1 ->
      value t2 ->
      value (trm_prod t1 t2)
  | value_loc : forall l,
      value (trm_loc l).

(** (pre-)store maps locations to values *)

Definition sto := LibEnv.env trm.

(** Store is a pre-store with value terms *)

Inductive store : sto -> Prop :=
  | store_empty : store empty
  | store_push : forall V l t,
      store V ->
      value t ->
      store (V & l ~ t).

(** (pre-)store typing maps locations to type. *)

Definition styp := LibEnv.env typ.

(** Store typing is a pre-store typing with unique bindings
    and well-formed types *)

Inductive store_type : styp -> Prop :=
  | store_type_empty : store_type empty
  | store_type_push : forall P l T,
      store_type P ->
      type T ->
      l # P ->
      store_type (P & l ~ T).

(** Validity of store typings *)

(* inputs: tenv
   subject: styp
   outputs: *)
Inductive valid_store_type : tenv -> styp -> Prop :=
  | valid_store_type_empty : forall E,
      valid_store_type E empty
  | valid_store_type_push : forall E P l T,
      valid_store_type E P ->
      kinding E T knd_type ->
      l # P ->
      valid_store_type E (P & l ~ T).

(* ****************************************************** *)
(** ** Description of typing *)

(* inputs: tenv, env, styp
   subject: trm
   outputs: typ *)
Inductive typing
  : tenv -> env -> styp -> trm -> typ -> Prop :=
  | typing_var : forall E D P x M T Us,
      binds x M D -> 
      valid_instance E Us M ->
      type_equal E T (instance M Us) knd_type ->
      typing E D P (trm_fvar x) T
  | typing_abs : forall L E D P T1 T2 t1,
      kinding E T1 knd_type ->
      (forall x, x \notin L -> 
        typing E (D & x ~ sch_empty T1) P (t1 ^ x) T2) -> 
      typing E D P (trm_abs t1) (typ_arrow T1 T2)
  | typing_app : forall E P D S T t1 t2, 
      typing E D P t1 (typ_arrow S T) ->
      typing E D P t2 S ->   
      typing E D P (trm_app t1 t2) T
  | typing_let_val : forall L M E D P T2 t1 t2,
      value t1 ->
      valid_scheme E M ->
      (forall Xs,
          fresh L (sch_arity M) Xs ->
          typing
            (E & Xs ~: M) D P
            t1 (instance_vars M Xs)) ->
      (forall x,
          x \notin L ->
          typing E (D & x ~ M) P (t2 ^ x) T2) -> 
      typing E D P (trm_let t1 t2) T2
  | typing_let : forall L E D P T1 T2 t1 t2, 
      typing E D P t1 T1 ->
      (forall x,
          x \notin L ->
          typing E (D & x ~ sch_empty T1) P (t2 ^ x) T2) ->
      typing E D P (trm_let t1 t2) T2
  | typing_constructor : forall c E D P T1 T2 T3 t,
      ranging E T1 (rng_range_above T2) ->
      subtype E
        (typ_constructor c T3)
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (CSet.singleton c) ->
      typing E D P t T3 ->
      typing E D P (trm_constructor c t) (typ_variant T1)
  | typing_match :
      forall L c E D P T1 T2 T3 T4 T5 T6 T7 T8 t1 t2 t3,
      (* Ranging already kinded type here. Should
         be replaced by subtyping when we merge rows
         and ranges. *)
      ranging E T1 (rng_range_below T2) ->
      ranging E T3 (rng_range_above T4) ->
      ranging E T5 (rng_range_above T6) ->
      subtype E
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (typ_constructor c T7)
        (CSet.singleton c) ->
      subtype E
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (typ_proj CSet.universe T4 (CSet.singleton c))
        (CSet.singleton c) ->
      subtype E
        (typ_proj CSet.universe T2 (CSet.cosingleton c))
        (typ_proj CSet.universe T6 (CSet.cosingleton c))
        (CSet.cosingleton c) ->
      typing E D P t1 (typ_variant T1) ->
      (forall x, x \notin L ->
         typing E (D & x ~ (sch_empty (typ_variant T3))) P
                (t2 ^ x) T8) ->
      (forall y, y \notin L -> 
         typing E (D & y ~ (sch_empty (typ_variant T5))) P
                (t3 ^ y) T8) ->
      typing E D P (trm_match t1 c t2 t3) T8
  | typing_destruct : forall L c E D P T1 T2 T3 T4 t1 t2,
      (* Ranging already kinded type here. Should
         be replaced by subtyping when we merge rows
         and ranges. *)
      ranging E T1 (rng_range_below T2) ->
      subtype E
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (typ_constructor c T3)
        (CSet.singleton c) ->
      subtype E
        (typ_proj CSet.universe T2 (CSet.cosingleton c))
        (typ_bot (CSet.cosingleton c))
        (CSet.cosingleton c) ->
      typing E D P t1 (typ_variant T1) ->
      (forall x, x \notin L ->
         typing E (D & x ~ (sch_empty T3)) P
                (t2 ^ x) T4) ->
      typing E D P (trm_destruct t1 c t2) T4
  | typing_absurd : forall E D P T1 T2 t1,
      kinding E T2 knd_type ->
      (* Ranging already kinded type here. Should
         be replaced by subtyping when we merge rows
         and ranges. *)
      ranging E T1
        (rng_range_below (typ_bot CSet.universe)) ->
      typing E D P t1 (typ_variant T1) ->
      typing E D P (trm_absurd t1) T2
  | typing_fix : forall L E D P T1 T2 t1,
      kinding E T1 knd_type ->
      kinding E T2 knd_type ->
      (forall x y,
          x \notin L -> y \notin (L \u \{x}) ->
          typing
            E (D & x ~ sch_empty (typ_arrow T1 T2)
                 & y ~ sch_empty T1)
            P (t1 ^* (y::x::nil)) T2) -> 
      typing E D P (trm_fix t1) (typ_arrow T1 T2)      
  | typing_unit : forall E D P,
      typing E D P trm_unit typ_unit
  | typing_prod : forall E D P T1 T2 t1 t2,
      typing E D P t1 T1 ->
      typing E D P t2 T2 ->
      typing E D P (trm_prod t1 t2) (typ_prod T1 T2)
  | typing_fst : forall E D P T1 T2 t1,
      typing E D P t1 (typ_prod T1 T2) ->
      typing E D P (trm_fst t1) T1
  | typing_snd : forall E D P T1 T2 t1,
      typing E D P t1 (typ_prod T1 T2) ->
      typing E D P (trm_snd t1) T2
  | typing_loc : forall E D P l T1 T2,
      binds l T1 P ->
      type_equal E T1 T2 knd_type ->
      typing E D P (trm_loc l) (typ_ref T2)
  | typing_ref : forall E D P t1 T,
      typing E D P t1 T ->
      typing E D P (trm_ref t1) (typ_ref T)
  | typing_get : forall E D P t1 T,
      typing E D P t1 (typ_ref T) ->
      typing E D P (trm_get t1) T
  | typing_set : forall E D P t1 t2 T,
      typing E D P t1 (typ_ref T) ->
      typing E D P t2 T ->
      typing E D P (trm_set t1 t2) typ_unit.

(* inputs: tenv, env, styp
   subject: trm
   outputs: sch *)
Inductive typing_scheme
  : tenv -> env -> styp -> trm -> sch -> Prop :=
  | typing_scheme_c : forall L E D P t M,
      valid_scheme E M ->
      (forall Xs,
          fresh L (sch_arity M) Xs ->
          typing
            (E & Xs ~: M) D P
            t (instance_vars M Xs)) ->
      typing_scheme E D P t M.

(* inputs: tenv, env, styp
   subject: list trm
   outputs: list sch *)
Inductive typing_schemes
  : tenv -> env -> styp -> list trm -> list sch -> Prop :=
  | typing_schemes_nil : forall E D P,
      typing_schemes E D P nil nil
  | typing_schemes_cons : forall E D P t ts M Ms,
      typing_scheme E D P t M ->
      typing_schemes E D P ts Ms ->
      typing_schemes E D P (t :: ts) (M :: Ms).

(* inputs: tenv, env, loc, sto, styp
   subject:
   outputs: *)
Inductive typing_store_loc
  : loc -> tenv -> env -> sto -> styp -> Prop :=
  | typing_store_loc_fresh : forall l E D V P,
      l # V ->
      l # P ->
      typing_store_loc l E D V P
  | typing_store_loc_bound : forall E D P l V T t,
      binds l t V ->
      binds l T P ->
      typing E D P t T ->
      typing_store_loc l E D V P.

(* inputs: tenv, env, loc, sto, styp
   subject:
   outputs: *)
Inductive typing_store : tenv -> env -> sto -> styp -> Prop :=
  | typing_store_c : forall E D V P,
     (forall l, typing_store_loc l E D V P) ->
     typing_store E D V P.

(* ************************************************************* *)
(** ** Description of the semantics *)

(** Reduction rules *)

(* inputs: trm(1), sto(1)
   subject:
   outputs: trm(2), sto(2) *)
Inductive red : trm -> sto -> trm -> sto -> Prop :=
  | red_let_1 : forall V t1 t2,
      value t1 -> 
      red (trm_let t1 t2) V (t2 ^^ t1) V
  | red_let_2 : forall V V' t1 t1' t2,
      red t1 V t1' V' -> 
      red (trm_let t1 t2) V (trm_let t1' t2) V'
  | red_app_1 : forall V V' t1 t1' t2,
      red t1 V t1' V' -> 
      red (trm_app t1 t2) V (trm_app t1' t2) V'
  | red_app_2 : forall V V' t1 t2 t2', 
      red t2 V t2' V' ->
      red (trm_app t1 t2) V (trm_app t1 t2') V'
  | red_app_3 : forall V t1 t2, 
      value t2 ->  
      red (trm_app (trm_abs t1) t2) V (t1 ^^ t2) V
  | red_app_4 : forall V t1 t2,
      value t2 ->
      red (trm_app (trm_fix t1) t2) V 
          (t1 ^^* (t2::(trm_fix t1)::nil)) V
  | red_constructor : forall V V' c t t',
      red t V t' V' ->
      red (trm_constructor c t) V (trm_constructor c t') V'
  | red_match_1 : forall V V' c t1 t1' t2 t3,
      red t1 V t1' V' ->
      red (trm_match t1 c t2 t3) V (trm_match t1' c t2 t3) V'
  | red_match_2 : forall V c1 c2 t1 t2 t3,
      c1 = c2 ->
      value t1 ->
      red (trm_match (trm_constructor c1 t1) c2 t2 t3) V
          (t2 ^^ (trm_constructor c1 t1)) V
  | red_match_3 : forall V c1 c2 t1 t2 t3,
      c1 <> c2 ->
      value t1 ->
      red (trm_match (trm_constructor c1 t1) c2 t2 t3) V
          (t3 ^^ (trm_constructor c1 t1)) V
  | red_destruct_1 : forall V V' c t1 t1' t2,
      red t1 V t1' V' ->
      red (trm_destruct t1 c t2) V (trm_destruct t1' c t2) V'
  | red_destruct_2 : forall V c1 c2 t1 t2,
      c1 = c2 ->
      value t1 ->
      red (trm_destruct (trm_constructor c1 t1) c2 t2) V
          (t2 ^^ t1) V
  | red_absurd : forall V V' t t',
      red t V t' V' ->
      red (trm_absurd t) V (trm_absurd t') V'
  | red_prod_1 : forall V V' t1 t1' t2,
      red t1 V t1' V' -> 
      red (trm_prod t1 t2) V (trm_prod t1' t2) V'
  | red_prod_2 : forall V V' t1 t2 t2', 
      value t1 ->
      red t2 V t2' V' ->
      red (trm_prod t1 t2) V (trm_prod t1 t2') V'
  | red_fst_1 : forall V V' t t',
      red t V t' V' ->
      red (trm_fst t) V (trm_fst t') V'
  | red_fst_2 : forall V t1 t2, 
      value t1 -> 
      value t2 ->  
      red (trm_fst (trm_prod t1 t2)) V t1 V
  | red_snd_1 : forall V V' t t',
      red t V t' V' ->
      red (trm_snd t) V (trm_snd t') V'
  | red_snd_2 : forall V t1 t2, 
      value t1 -> 
      value t2 ->  
      red (trm_snd (trm_prod t1 t2)) V t2 V
  | red_ref_1 : forall V V' t t',
      red t V t' V' ->
      red (trm_ref t) V (trm_ref t') V'
  | red_ref_2 : forall V t l,
      value t ->
      l # V ->
      red (trm_ref t) V (trm_loc l) (V & l ~ t)
  | red_get_1 : forall V V' t t',
      red t V t' V' ->
      red (trm_get t) V (trm_get t') V'
  | red_get_2 : forall V t l,
      binds l t V ->
      red (trm_get (trm_loc l)) V t V
  | red_set_1 : forall V V' t1 t1' t2,
      red t1 V t1' V' ->
      red (trm_set t1 t2) V (trm_set t1' t2) V'
  | red_set_2 : forall V V' t1 t2 t2',
      value t1 ->
      red t2 V t2' V' ->
      red (trm_set t1 t2) V (trm_set t1 t2') V'
  | red_set_3 : forall V l t2,
      value t2 ->
      red (trm_set (trm_loc l) t2) V trm_unit (V & l ~ t2).

(* ***************************************************** *)
(** ** Description of the results *)

(** Goal is to prove preservation and progress *)

Definition preservation := forall E D P t t' V V' T,
  valid_tenv E ->
  valid_env E D ->
  valid_store_type E P ->
  store V ->
  typing E D P t T ->
  typing_store E D V P ->
  red t V t' V' ->
  exists P',
    extends P P'
    /\ valid_store_type E P'
    /\ store V'
    /\ typing E D P' t' T
    /\ typing_store E D V' P'.

Definition progress := forall E P V t T,
  valid_tenv E ->
  valid_store_type E P ->
  store V ->
  typing E empty P t T ->
  typing_store E empty V P ->
     value t 
  \/ exists t' V', red t V t' V'.
