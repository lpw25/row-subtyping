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
  | knd_range : typ -> typ -> knd.

Definition typ_nil := typ_bot (CSet.empty).

(** Type schemes. *)

Inductive sch : Type := Sch { 
  sch_kinds : list knd ; 
  sch_body  : typ }.

Definition sch_empty T := Sch nil T.

Fixpoint sch_arity (M : sch) : nat :=
  List.length (sch_kinds M).

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

(** Opening a kind. *)

Definition knd_open (K : knd) (Us : list typ) : knd :=
  match K with
  | knd_type => knd_type
  | knd_row cs => knd_row cs
  | knd_range T1 T2 =>
    knd_range (typ_open T1 Us) (typ_open T2 Us)
  end.

Definition knd_open_vars K Xs := knd_open K (typ_fvars Xs).

Definition knd_open_list Ks Us :=
  List.map (fun K => knd_open K Us) Ks.

Definition knd_open_vars_list Ks Xs :=
  knd_open_list Ks (typ_fvars Xs).

(** Instanciation of a type scheme *)

Definition instance (M : sch) (Us : list typ) : typ :=
  typ_open (sch_body M) Us.

Definition instance_vars M Xs :=
  instance M (typ_fvars Xs).

(** Locally closed types *)

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
  | type_proj : forall cs1 T cs2,
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
  | kind_range : forall T1 T2,
      type T1 ->
      type T2 ->
      kind (knd_range T1 T2).

Inductive kinds : list knd -> Prop :=
  | kinds_nil : kinds nil
  | kinds_cons : forall K Ks,
      kind K ->
      kinds Ks ->
      kinds (K :: Ks).

(** Definition of a well-formed scheme *)

Inductive kinds_and_type : list knd -> typ -> Prop :=
  | kinds_and_type_c : forall Ks T,
      kinds Ks ->
      type T ->
      kinds_and_type Ks T.

Inductive scheme : sch -> Prop :=
  | scheme_c : forall L M,
      (forall Xs,
          fresh L (sch_arity M) Xs ->
          kinds_and_type
            (knd_open_vars_list (sch_kinds M) Xs)
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

(* ************************************************************* *)
(** ** Description of typing environments *)

(** A binding is either mapping type or term variables. 
 [X ~:: K] is a kinding asumption and [x ~: T] is
 a typing assumption *)

Inductive bind : Type :=
  | bind_knd : knd -> bind
  | bind_typ : sch -> bind.

(** Pre-environment is an associative list of bindings. *)

Definition env := LibEnv.env bind.

Function bind_typs (xs : list var) (Ms : list sch) : env :=
  match xs with
  | nil => empty
  | x :: xs =>
    match Ms with
    | nil => empty
    | M :: Ms =>
      (x ~ bind_typ M) & bind_typs xs Ms
    end
  end.

Function bind_knds (Xs : list var) (Ks : list knd) : env :=
  match Xs with
  | nil => empty
  | X :: Xs =>
    match Ks with
    | nil => empty
    | K :: Ks =>
      (X ~ bind_knd K) & bind_knds Xs Ks
    end
  end.

Definition bind_sch_kinds (Xs : list var) (M : sch) : env :=
  bind_knds Xs (knd_open_vars_list (sch_kinds M) Xs).

Notation "X ~:: K" := (X ~ bind_knd K)
  (at level 23, left associativity) : env_scope.
Notation "x ~: T" := (x ~ bind_typ T)
  (at level 23, left associativity) : env_scope.
Notation "Xs ~::* M" := (bind_sch_kinds Xs M)
  (at level 23, left associativity) : env_scope.

(** Environment is a pre-environment with unique bindings *)

Inductive environment : env -> Prop :=
  | environment_empty :
      environment empty
  | environment_knd : forall E X K,
      environment E ->
      kind K ->
      X # E ->
      environment (E & X ~:: K)
  | environment_typ : forall E x M,
      environment E ->
      scheme M ->
      x # E ->
      environment (E & x ~: M).

Definition no_term_bindings E :=
  forall x M, not (binds x (bind_typ M) E).

(* ************************************************************* *)
(** ** Description of kinding and equality *)

(* Validity of kinds *)

Inductive valid_kind : bool -> env -> knd -> Prop :=
  | valid_kind_type : forall chk E,
      valid_env chk E ->
      valid_kind chk E knd_type
  | valid_kind_row :  forall chk E cs,
      valid_env chk E ->
      CSet.Nonempty cs ->
      valid_kind chk E (knd_row cs)
  | valid_kind_range : forall chk E T1 T2,
      subtype chk E T2 T1 CSet.universe ->
      valid_kind chk E (knd_range T1 T2)

(** The kinding judgement *)

with kinding : bool -> env -> typ -> knd -> Prop :=
  | kinding_var : forall chk E X K,
      valid_env chk E ->
      binds X (bind_knd K) E ->
      kinding chk E (typ_fvar X) K
  | kinding_constructor : forall chk E c T cs,
      kinding chk E T knd_type ->
      cs = CSet.singleton c ->
      kinding chk E (typ_constructor c T) (knd_row cs)
  | kinding_or : forall chk E T1 T2 cs1 cs2 cs12,
      kinding chk E T1 (knd_row cs1) ->
      kinding chk E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      kinding chk E (typ_or cs1 T1 cs2 T2) (knd_row cs12)
  | kinding_proj : forall chk E T cs1 cs2,
      kinding chk E T (knd_row cs1) ->
      CSet.Subset cs2 cs1 ->
      CSet.Nonempty cs2 ->
      kinding chk E (typ_proj cs1 T cs2) (knd_row cs2)
  | kinding_variant : forall chk E T,
      kinding chk E T
        (knd_range (typ_top CSet.universe) (typ_bot CSet.universe)) ->
      kinding chk E (typ_variant T) knd_type
  | kinding_arrow : forall chk E T1 T2,
      kinding chk E T1 knd_type -> 
      kinding chk E T2 knd_type -> 
      kinding chk E (typ_arrow T1 T2) knd_type
  | kinding_ref : forall chk E T,
      kinding chk E T knd_type ->
      kinding chk E (typ_ref T) knd_type
  | kinding_unit : forall chk E,
      valid_env chk E ->
      kinding chk E typ_unit knd_type
  | kinding_prod : forall chk E T1 T2,
      kinding chk E T1 knd_type -> 
      kinding chk E T2 knd_type -> 
      kinding chk E (typ_prod T1 T2) knd_type
  | kinding_top : forall chk E cs,
      valid_env chk E ->
      CSet.Nonempty cs ->
      kinding chk E (typ_top cs) (knd_row cs)
  | kinding_bot : forall chk E cs,
      valid_env chk E ->
      CSet.Nonempty cs ->
      kinding chk E (typ_bot cs) (knd_row cs)
  | kinding_meet : forall chk E T1 T2 cs,
      kinding chk E T1 (knd_row cs) ->
      kinding chk E T2 (knd_row cs) ->
      kinding chk E (typ_meet T1 T2) (knd_row cs)
  | kinding_join : forall chk E T1 T2 cs,
      kinding chk E T1 (knd_row cs) ->
      kinding chk E T2 (knd_row cs) ->
      kinding chk E (typ_join T1 T2) (knd_row cs)
  | kinding_range_subsumption : forall chk E T T1 T2 T1' T2',
      kinding chk E T (knd_range T1 T2) ->
      subtype chk E T1 T1' CSet.universe ->
      subtype chk E T2' T2 CSet.universe ->
      kinding chk E T (knd_range T1' T2')

(* Validity of type schemes *)

with valid_kinds : bool -> env -> list knd -> Prop :=
  | valid_kinds_nil : forall chk E,
      valid_env chk E ->
      valid_kinds chk E nil
  | valid_kinds_cons : forall chk E K Ks,
      valid_kind chk E K ->
      valid_kinds chk E Ks ->
      valid_kinds chk E (K :: Ks)

with valid_kinds_and_type : bool -> env -> list knd -> typ -> Prop :=
  | valid_kinds_and_type_c : forall chk E Ks T,
      valid_kinds chk E Ks ->
      kinding chk E T knd_type ->
      valid_kinds_and_type chk E Ks T

with valid_scheme : bool -> env -> sch -> Prop :=
  | valid_scheme_c : forall L chk E M,
      valid_env chk E ->
      (forall Xs,
          fresh L (sch_arity M) Xs ->
          valid_kinds_and_type chk (E & Xs ~::* M)
            (knd_open_vars_list (sch_kinds M) Xs)
            (typ_open_vars (sch_body M) Xs)) ->
      valid_scheme chk E M

(* Validity of environments *)

with valid_env_aux : env -> env -> Prop :=
  | valid_env_aux_empty : forall E,
      environment E ->
      valid_env_aux E empty
  | valid_env_aux_kind : forall E F X K,
      valid_env_aux E F ->
      valid_kind false E K ->
      X # F ->
      valid_env_aux E (F & X ~:: K)
  | valid_env_aux_type : forall E F x M,
      valid_env_aux E F ->
      valid_scheme false E M ->
      x # F ->
      valid_env_aux E (F & x ~: M)

with valid_env : bool -> env -> Prop :=
  | valid_env_check : forall E,
      valid_env_aux E E ->
      valid_env true E
  | valid_env_no_check : forall E,
      environment E ->
      valid_env false E

(** Core of the equality relation on types *)

with type_equal_core : bool -> env -> typ -> typ -> knd -> Prop :=
  | type_equal_core_or_commutative : forall chk E T1 T2 cs1 cs2 cs12,
      kinding chk E T1 (knd_row cs1) ->
      kinding chk E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_core chk E
        (typ_or cs1 T1 cs2 T2) (typ_or cs2 T2 cs1 T1) (knd_row cs12)
  | type_equal_core_or_associative :
      forall chk E T1 cs1 T2 cs2 T3 cs3 cs12 cs23 cs123,
      kinding chk E T1 (knd_row cs1) ->
      kinding chk E T2 (knd_row cs2) ->
      kinding chk E T3 (knd_row cs3) ->
      CSet.Disjoint cs1 cs2 ->
      CSet.Disjoint cs1 cs3 ->
      CSet.Disjoint cs2 cs3 ->
      cs12 = CSet.union cs1 cs2 ->
      cs23 = CSet.union cs2 cs3 ->
      cs123 = CSet.union cs1 cs23 ->
      type_equal_core chk E
        (typ_or cs1 T1 cs23 (typ_or cs2 T2 cs3 T3))
        (typ_or cs12 (typ_or cs1 T1 cs2 T2) cs3 T3)
        (knd_row cs123)
  | type_equal_core_or_bot : forall chk E cs1 cs2 cs12,
      valid_env chk E ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_core chk E
        (typ_or cs1 (typ_bot cs1) cs2 (typ_bot cs2)) (typ_bot cs12)
        (knd_row cs12)
  | type_equal_core_or_top : forall chk E cs1 cs2 cs12,
      valid_env chk E ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_core chk E
        (typ_or cs1 (typ_top cs1) cs2 (typ_top cs2)) (typ_top cs12)
        (knd_row cs12)
  | type_equal_core_or_meet_distribution :
      forall chk E T1 T2 T3 T4 cs1 cs2 cs12,
      kinding chk E T1 (knd_row cs1) ->
      kinding chk E T2 (knd_row cs2) ->
      kinding chk E T3 (knd_row cs1) ->
      kinding chk E T4 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_core chk E
        (typ_or cs1 (typ_meet T1 T3) cs2 (typ_meet T2 T4))
        (typ_meet (typ_or cs1 T1 cs2 T2) (typ_or cs1 T3 cs2 T4))
        (knd_row cs12)
  | type_equal_core_or_join_distribution :
      forall chk E T1 T2 T3 T4 cs1 cs2 cs12,
      kinding chk E T1 (knd_row cs1) ->
      kinding chk E T2 (knd_row cs2) ->
      kinding chk E T3 (knd_row cs1) ->
      kinding chk E T4 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_core chk E
        (typ_or cs1 (typ_join T1 T3) cs2 (typ_join T2 T4))
        (typ_join (typ_or cs1 T1 cs2 T2) (typ_or cs1 T3 cs2 T4))
        (knd_row cs12)
  | type_equal_core_or_proj : forall chk E T cs1 cs2 cs3 cs23,
      kinding chk E T (knd_row cs1) ->
      CSet.Disjoint cs2 cs3 ->
      CSet.Subset cs2 cs1 ->
      CSet.Nonempty cs2 ->
      CSet.Subset cs3 cs1 ->
      CSet.Nonempty cs3 ->
      cs23 = CSet.union cs2 cs3 ->
      type_equal_core chk E
        (typ_or cs2 (typ_proj cs1 T cs2) cs3 (typ_proj cs1 T cs3))
        (typ_proj cs1 T cs23)
        (knd_row cs23)
  | type_equal_core_proj_id : forall chk E T cs,
      kinding chk E T (knd_row cs) ->
      type_equal_core chk E (typ_proj cs T cs) T (knd_row cs)
  | type_equal_core_proj_compose : forall chk E T cs1 cs2 cs3,
      kinding chk E T (knd_row cs1) ->
      CSet.Subset cs2 cs1 ->
      CSet.Subset cs3 cs2 ->
      CSet.Nonempty cs3 ->
      type_equal_core chk E
        (typ_proj cs2 (typ_proj cs1 T cs2) cs3)
        (typ_proj cs1 T cs3)
        (knd_row cs3)
  | type_equal_core_proj_or_l : forall chk E T1 T2 cs1 cs1' cs2 cs12,
      kinding chk E T1 (knd_row cs1) ->
      kinding chk E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      CSet.Subset cs1' cs1 ->
      CSet.Nonempty cs1' ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_core chk E
        (typ_proj cs12 (typ_or cs1 T1 cs2 T2) cs1')
        (typ_proj cs1 T1 cs1')
        (knd_row cs1')
  | type_equal_core_proj_or_r : forall chk E T1 T2 cs1 cs2 cs2' cs12,
      kinding chk E T1 (knd_row cs1) ->
      kinding chk E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      CSet.Subset cs2' cs2 ->
      CSet.Nonempty cs2' ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_core chk E
        (typ_proj cs12 (typ_or cs1 T1 cs2 T2) cs2')
        (typ_proj cs2 T2 cs2')
        (knd_row cs2')
  | type_equal_core_proj_or_both :
      forall chk E T1 T2 cs1 cs2 cs1' cs2' cs12 cs12',
      kinding chk E T1 (knd_row cs1) ->
      kinding chk E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      CSet.Subset cs1' cs1 ->
      CSet.Nonempty cs1' ->
      CSet.Subset cs2' cs2 ->
      CSet.Nonempty cs2' ->
      cs12 = CSet.union cs1 cs2 ->
      cs12' = CSet.union cs1' cs2' ->
      type_equal_core chk E
        (typ_proj cs12 (typ_or cs1 T1 cs2 T2) cs12')
        (typ_or cs1' (typ_proj cs1 T1 cs1')
                cs2' (typ_proj cs2 T2 cs2'))
        (knd_row cs12')
  | type_equal_core_proj_meet : forall chk E T1 T2 cs cs',
      kinding chk E T1 (knd_row cs) ->
      kinding chk E T2 (knd_row cs) ->
      CSet.Subset cs' cs ->
      CSet.Nonempty cs' ->
      type_equal_core chk E
        (typ_proj cs (typ_meet T1 T2) cs')
        (typ_meet (typ_proj cs T1 cs') (typ_proj cs T2 cs'))
        (knd_row cs')
  | type_equal_core_proj_join : forall chk E T1 T2 cs cs',
      kinding chk E T1 (knd_row cs) ->
      kinding chk E T2 (knd_row cs) ->
      CSet.Subset cs' cs ->
      CSet.Nonempty cs' ->
      type_equal_core chk E
        (typ_proj cs (typ_join T1 T2) cs')
        (typ_join (typ_proj cs T1 cs') (typ_proj cs T2 cs'))
        (knd_row cs')
  | type_equal_core_meet_commutative : forall chk E T1 T2 cs,
      kinding chk E T1 (knd_row cs) ->
      kinding chk E T2 (knd_row cs) ->
      type_equal_core chk E (typ_meet T1 T2) (typ_meet T2 T1) (knd_row cs)
  | type_equal_core_meet_associative : forall chk E T1 T2 T3 cs,
      kinding chk E T1 (knd_row cs) ->
      kinding chk E T2 (knd_row cs) ->
      kinding chk E T3 (knd_row cs) ->
      type_equal_core chk E
        (typ_meet T1 (typ_meet T2 T3))
        (typ_meet (typ_meet T1 T2) T3)
        (knd_row cs)
  | type_equal_core_meet_identity : forall chk E T1 cs,
      kinding chk E T1 (knd_row cs) ->
      type_equal_core chk E (typ_meet T1 (typ_top cs)) T1 (knd_row cs)
  | type_equal_core_meet_absorption : forall chk E T1 T2 cs,
      kinding chk E T1 (knd_row cs) ->
      kinding chk E T2 (knd_row cs) ->
      type_equal_core chk E (typ_meet T1 (typ_join T1 T2)) T1 (knd_row cs)
  | type_equal_core_meet_distribution : forall chk E T1 T2 T3 cs,
      kinding chk E T1 (knd_row cs) ->
      kinding chk E T2 (knd_row cs) ->
      kinding chk E T3 (knd_row cs) ->
      type_equal_core chk E
        (typ_meet T1 (typ_join T2 T3))
        (typ_join (typ_meet T1 T2) (typ_meet T1 T3))
        (knd_row cs)
  | type_equal_core_join_commutative : forall chk E T1 T2 cs,
      kinding chk E T1 (knd_row cs) ->
      kinding chk E T2 (knd_row cs) ->
      type_equal_core chk E (typ_join T1 T2) (typ_join T2 T1) (knd_row cs)
  | type_equal_core_join_associative : forall chk E T1 T2 T3 cs,
      kinding chk E T1 (knd_row cs) ->
      kinding chk E T2 (knd_row cs) ->
      kinding chk E T3 (knd_row cs) ->
      type_equal_core chk E
        (typ_join T1 (typ_join T2 T3))
        (typ_join (typ_join T1 T2) T3)
        (knd_row cs)
  | type_equal_core_join_identity : forall chk E T1 cs,
      kinding chk E T1 (knd_row cs) ->
      type_equal_core chk E (typ_join T1 (typ_bot cs)) T1 (knd_row cs)
  | type_equal_core_join_absorption : forall chk E T1 T2 cs,
      kinding chk E T1 (knd_row cs) ->
      kinding chk E T2 (knd_row cs) ->
      type_equal_core chk E (typ_join T1 (typ_meet T1 T2)) T1 (knd_row cs)
  | type_equal_core_join_distribution : forall chk E T1 T2 T3 cs,
      kinding chk E T1 (knd_row cs) ->
      kinding chk E T2 (knd_row cs) ->
      kinding chk E T3 (knd_row cs) ->
      type_equal_core chk E
        (typ_join T1 (typ_meet T2 T3))
        (typ_meet (typ_join T1 T2) (typ_join T1 T3))
        (knd_row cs)

(* Symetric closure of type_equal_core *)

with type_equal_symm : bool -> env -> typ -> typ -> knd -> Prop :=
  | type_equal_symm_l : forall chk E T1 T2 K,
      type_equal_core chk E T1 T2 K ->
      type_equal_symm chk E T1 T2 K
  | type_equal_symm_r : forall chk E T1 T2 K,
      type_equal_core chk E T1 T2 K ->
      type_equal_symm chk E T2 T1 K

(* Congruence closure of type_equal_symm *)

with type_equal_cong : bool -> env -> typ -> typ -> knd -> Prop :=
  | type_equal_cong_constructor : forall chk E c T1 T1' cs,
      type_equal_cong chk E T1 T1' knd_type ->
      cs = CSet.singleton c ->
      type_equal_cong chk E
        (typ_constructor c T1) (typ_constructor c T1')
        (knd_row cs)
  | type_equal_cong_or_l : forall chk E T1 T1' T2 cs1 cs2 cs12,
      kinding chk E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_cong chk E T1 T1' (knd_row cs1) ->
      type_equal_cong chk E
        (typ_or cs1 T1 cs2 T2) (typ_or cs1 T1' cs2 T2) (knd_row cs12)
  | type_equal_cong_or_r : forall chk E T1 T2 T2' cs1 cs2 cs12,
      kinding chk E T1 (knd_row cs1) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_cong chk E T2 T2' (knd_row cs2) ->
      type_equal_cong chk E
        (typ_or cs1 T1 cs2 T2) (typ_or cs1 T1 cs2 T2') (knd_row cs12)
  | type_equal_cong_proj : forall chk E T1 T1' cs1 cs2,
      CSet.Subset cs2 cs1 ->
      CSet.Nonempty cs2 ->
      type_equal_cong chk E T1 T1' (knd_row cs1) ->
      type_equal_cong chk E
        (typ_proj cs1 T1 cs2) (typ_proj cs1 T1' cs2) (knd_row cs2)
  | type_equal_cong_arrow_l : forall chk E T1 T1' T2,
      kinding chk E T2 knd_type ->
      type_equal_cong chk E T1 T1' knd_type ->
      type_equal_cong chk E (typ_arrow T1 T2) (typ_arrow T1' T2) knd_type
  | type_equal_cong_arrow_r : forall chk E T1 T2 T2',
      kinding chk E T1 knd_type ->
      type_equal_cong chk E T2 T2' knd_type ->
      type_equal_cong chk E (typ_arrow T1 T2) (typ_arrow T1 T2') knd_type
  | type_equal_cong_prod_l : forall chk E T1 T1' T2,
      kinding chk E T2 knd_type ->
      type_equal_cong chk E T1 T1' knd_type ->
      type_equal_cong chk E (typ_prod T1 T2) (typ_prod T1' T2) knd_type
  | type_equal_cong_prod_r : forall chk E T1 T2 T2',
      kinding chk E T1 knd_type ->
      type_equal_cong chk E T2 T2' knd_type ->
      type_equal_cong chk E (typ_prod T1 T2) (typ_prod T1 T2') knd_type
  | type_equal_cong_ref : forall chk E T1 T1',
      type_equal_cong chk E T1 T1' knd_type ->
      type_equal_cong chk E (typ_ref T1) (typ_ref T1') knd_type
  | type_equal_cong_meet_l : forall chk E T1 T1' T2 cs,
      kinding chk E T2 (knd_row cs) ->
      type_equal_cong chk E T1 T1' (knd_row cs) ->
      type_equal_cong chk E
        (typ_meet T1 T2) (typ_meet T1' T2) (knd_row cs)
  | type_equal_cong_meet_r : forall chk E T1 T2 T2' cs,
      kinding chk E T1 (knd_row cs) ->
      type_equal_cong chk E T2 T2' (knd_row cs) -> 
      type_equal_cong chk E
        (typ_meet T1 T2) (typ_meet T1 T2') (knd_row cs)
  | type_equal_cong_join_l : forall chk E T1 T1' T2 cs,
      kinding chk E T2 (knd_row cs) ->
      type_equal_cong chk E T1 T1' (knd_row cs) ->
      type_equal_cong chk E
        (typ_join T1 T2) (typ_join T1' T2) (knd_row cs)
  | type_equal_cong_join_r : forall chk E T1 T2 T2' cs,
      kinding chk E T1 (knd_row cs) ->
      type_equal_cong chk E T2 T2' (knd_row cs) ->
      type_equal_cong chk E
        (typ_join T1 T2) (typ_join T1 T2') (knd_row cs)
  | type_equal_cong_symm : forall chk E T1 T1' K,
      type_equal_symm chk E T1 T1' K ->
      type_equal_cong chk E T1 T1' K

(* Reflexive transitive closure of type_equal_cong *)

with type_equal : bool -> env -> typ -> typ -> knd -> Prop :=
  | type_equal_refl : forall chk E T K,
      kinding chk E T K ->
      type_equal chk E T T K
  | type_equal_step : forall chk E T1 T2 T3 K,
      type_equal_cong chk E T1 T2 K ->
      type_equal chk E T2 T3 K ->
      type_equal chk E T1 T3 K

with subtype : bool -> env -> typ -> typ -> cset -> Prop :=
  | subtype_c : forall chk E T1 T2 cs,
      type_equal chk E T1 (typ_meet T1 T2) (knd_row cs) ->
      subtype chk E T1 T2 cs.

Scheme valid_kind_mutind := Induction for valid_kind Sort Prop
  with kinding_mutind := Induction for kinding Sort Prop
  with valid_kinds_mutind := Induction for valid_kinds Sort Prop
  with valid_kinds_and_type_mutind :=
         Induction for valid_kinds_and_type Sort Prop
  with valid_scheme_mutind := Induction for valid_scheme Sort Prop
  with valid_env_aux_mutind := Induction for valid_env_aux Sort Prop
  with valid_env_mutind := Induction for valid_env Sort Prop
  with type_equal_core_mutind :=
         Induction for type_equal_core Sort Prop
  with type_equal_symm_mutind :=
         Induction for type_equal_symm Sort Prop
  with type_equal_cong_mutind :=
         Induction for type_equal_cong Sort Prop
  with type_equal_mutind := Induction for type_equal Sort Prop
  with subtype_mutind := Induction for subtype Sort Prop.

Combined Scheme combined_kinding_mutind
  from valid_kind_mutind, kinding_mutind,
       valid_kinds_mutind, valid_kinds_and_type_mutind,
       valid_scheme_mutind, valid_env_aux_mutind, valid_env_mutind,
       type_equal_core_mutind,
       type_equal_symm_mutind, type_equal_cong_mutind,
       type_equal_mutind, subtype_mutind.

Inductive kindings : bool -> env -> list typ -> list knd -> Prop :=
  | kindings_nil : forall chk E,
      valid_env chk E ->
      kindings chk E nil nil
  | kindings_cons : forall chk E T Ts K Ks,
      kinding chk E T K ->
      kindings chk E Ts Ks ->
      kindings chk E (T :: Ts) (K :: Ks).

Inductive valid_schemes : bool -> env -> list sch -> Prop :=
  | valid_schemes_nil : forall chk E,
      valid_env chk E ->
      valid_schemes chk E nil
  | valid_schemes_cons : forall chk E M Ms,
      valid_scheme chk E M ->
      valid_schemes chk E Ms ->
      valid_schemes chk E (M :: Ms).

Inductive valid_instance : env -> list typ -> sch -> Prop :=
  | valid_instance_c : forall E Ts M,
      kindings true E Ts (knd_open_list (sch_kinds M) Ts) ->
      kinding true E (typ_open (sch_body M) Ts) knd_type ->
      valid_instance E Ts M.

(* ************************************************************* *)
(** ** Description of stores *)

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

Inductive valid_store_type : env -> styp -> Prop :=
  | valid_store_type_empty : forall E,
      valid_env true E ->
      valid_store_type E empty
  | valid_store_type_push : forall E P l T,
      valid_store_type E P ->
      kinding true E T knd_type ->
      l # P ->
      valid_store_type E (P & l ~ T).

(* ************************************************************* *)
(** ** Description of typing *)

Inductive typing : env -> styp -> trm -> typ -> Prop :=
  | typing_var : forall E P x M T Us,
      valid_env true E ->
      valid_store_type E P ->
      binds x (bind_typ M) E -> 
      valid_instance E Us M ->
      type_equal true E T (instance M Us) knd_type ->
      typing E P (trm_fvar x) T
  | typing_abs : forall L E P T1 T2 t1,
      kinding true E T1 knd_type ->
      (forall x, x \notin L -> 
        typing (E & x ~: sch_empty T1) P (t1 ^ x) T2) -> 
      typing E P (trm_abs t1) (typ_arrow T1 T2)
  | typing_app : forall E P S T t1 t2, 
      typing E P t1 (typ_arrow S T) ->
      typing E P t2 S ->   
      typing E P (trm_app t1 t2) T
  | typing_let_val : forall L M E P T2 t1 t2,
      value t1 ->
      (forall Xs, fresh L (sch_arity M) Xs ->
         typing
           (E & Xs ~::* M) P
           t1 (instance_vars M Xs)) ->
      (forall x, x \notin L -> typing (E & x ~: M) P (t2 ^ x) T2) -> 
      typing E P (trm_let t1 t2) T2
  | typing_let : forall L E P T1 T2 t1 t2, 
      typing E P t1 T1 ->
      (forall x, x \notin L -> typing (E & x ~: sch_empty T1) P (t2 ^ x) T2) ->
      typing E P (trm_let t1 t2) T2
  | typing_constructor : forall c E P T1 T2 T3 t,
      kinding true E T1 (knd_range (typ_top CSet.universe) T2) ->
      subtype true E
        (typ_constructor c T3)
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (CSet.singleton c) ->
      typing E P t T3 ->
      typing E P (trm_constructor c t) (typ_variant T1)
  | typing_match : forall L c E P T1 T2 T3 T4 T5 T6 T7 T8 t1 t2 t3,
      kinding true E T1 (knd_range T2 (typ_bot CSet.universe)) ->
      kinding true E T3 (knd_range (typ_top CSet.universe) T4) ->
      kinding true E T5 (knd_range (typ_top CSet.universe) T6) ->
      subtype true E
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (typ_constructor c T7)
        (CSet.singleton c) ->
      subtype true E
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (typ_proj CSet.universe T4 (CSet.singleton c))
        (CSet.singleton c) ->
      subtype true E
        (typ_proj CSet.universe T2 (CSet.cosingleton c))
        (typ_proj CSet.universe T6 (CSet.cosingleton c))
        (CSet.cosingleton c) ->
      typing E P t1 (typ_variant T1) ->
      (forall x, x \notin L ->
         typing (E & x ~: (sch_empty (typ_variant T3))) P
                (t2 ^ x) T8) ->
      (forall y, y \notin L -> 
         typing (E & y ~: (sch_empty (typ_variant T5))) P
                (t3 ^ y) T8) ->
      typing E P (trm_match t1 c t2 t3) T8
  | typing_destruct : forall L c E P T1 T2 T3 T4 t1 t2,
      kinding true E T1 (knd_range T2 (typ_bot CSet.universe)) ->
      subtype true E
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (typ_constructor c T3)
        (CSet.singleton c) ->
      subtype true E
        (typ_proj CSet.universe T2 (CSet.cosingleton c))
        (typ_bot (CSet.cosingleton c))
        (CSet.cosingleton c) ->
      typing E P t1 (typ_variant T1) ->
      (forall x, x \notin L ->
         typing (E & x ~: (sch_empty T3)) P
                (t2 ^ x) T4) ->
      typing E P (trm_destruct t1 c t2) T4
  | typing_absurd : forall E P T1 T2 t1,
      kinding true E T1 (knd_range (typ_bot CSet.universe)
                              (typ_bot CSet.universe)) ->
      kinding true E T2 knd_type ->
      typing E P t1 (typ_variant T1) ->
      typing E P (trm_absurd t1) T2
  | typing_fix : forall L E P T1 T2 t1,
      (forall x y,
          x \notin L -> y \notin (L \u \{x}) ->
          typing
            (E & x ~: sch_empty (typ_arrow T1 T2) & y ~: sch_empty T1)
            P (t1 ^* (x::y::nil)) T2) -> 
      typing E P (trm_fix t1) (typ_arrow T1 T2)      
  | typing_unit : forall E P,
      valid_env true E ->
      valid_store_type E P ->
      typing E P trm_unit typ_unit
  | typing_prod : forall E P T1 T2 t1 t2,
      typing E P t1 T1 ->
      typing E P t2 T2 ->
      typing E P (trm_prod t1 t2) (typ_prod T1 T2)
  | typing_fst : forall E P T1 T2 t1,
      typing E P t1 (typ_prod T1 T2) ->
      typing E P (trm_fst t1) T1
  | typing_snd : forall E P T1 T2 t1,
      typing E P t1 (typ_prod T1 T2) ->
      typing E P (trm_snd t1) T2
  | typing_loc : forall E P l T1 T2,
      valid_env true E ->
      valid_store_type E P ->
      binds l T1 P ->
      type_equal true E T1 T2 knd_type ->
      typing E P (trm_loc l) (typ_ref T2)
  | typing_ref : forall E P t1 T,
      typing E P t1 T ->
      typing E P (trm_ref t1) (typ_ref T)
  | typing_get : forall E P t1 T,
      typing E P t1 (typ_ref T) ->
      typing E P (trm_get t1) T
  | typing_set : forall E P t1 t2 T,
      typing E P t1 (typ_ref T) ->
      typing E P t2 T ->
      typing E P (trm_set t1 t2) typ_unit.

Inductive typing_scheme : env -> styp -> trm -> sch -> Prop :=
  | typing_scheme_c : forall L E P t M,
      valid_scheme true E M ->
      valid_store_type E P ->
      (forall Xs,
          fresh L (sch_arity M) Xs ->
          typing (E & Xs ~::* M) P t (instance_vars M Xs)) ->
      typing_scheme E P t M.

Inductive typing_schemes
  : env -> styp -> list trm -> list sch -> Prop :=
  | typing_schemes_nil : forall E P,
      valid_env true E ->
      valid_store_type E P ->
      typing_schemes E P nil nil
  | typing_schemes_cons : forall E P t ts M Ms,
      typing_scheme E P t M ->
      typing_schemes E P ts Ms ->
      typing_schemes E P (t :: ts) (M :: Ms).

Definition typing_store E V P :=
     store V
  /\ valid_store_type E P
  /\ (forall l, l # V -> l # P)
  /\ (forall l T, binds l T P -> 
        exists t, binds l t V
               /\ typing E P t T).

(* ************************************************************* *)
(** ** Description of the semantics *)

(** Reduction rules *)

Inductive red : trm -> sto -> trm -> sto -> Prop :=
  | red_let_1 : forall V t1 t2,
      store V ->
      term (trm_let t1 t2) ->
      value t1 -> 
      red (trm_let t1 t2) V (t2 ^^ t1) V
  | red_let_2 : forall V V' t1 t1' t2,
      term_body t2 ->
      red t1 V t1' V' -> 
      red (trm_let t1 t2) V (trm_let t1' t2) V'
  | red_app_1 : forall V V' t1 t1' t2,
      term t2 ->
      red t1 V t1' V' -> 
      red (trm_app t1 t2) V (trm_app t1' t2) V'
  | red_app_2 : forall V V' t1 t2 t2', 
      value t1 ->
      red t2 V t2' V' ->
      red (trm_app t1 t2) V (trm_app t1 t2') V'
  | red_app_3 : forall V t1 t2, 
      store V ->
      term_body t1 -> 
      value t2 ->  
      red (trm_app (trm_abs t1) t2) V (t1 ^^ t2) V
  | red_app_4 : forall V t1 t2,
      store V ->
      term_body2 t1 -> 
      value t2 ->
      red (trm_app (trm_fix t1) t2) V 
          (t1 ^^* ((trm_fix t1)::t2::nil)) V
  | red_constructor : forall V V' c t t',
      red t V t' V' ->
      red (trm_constructor c t) V (trm_constructor c t') V'
  | red_match_1 : forall V V' c t1 t1' t2 t3,
      term_body t2 ->
      term_body t3 ->
      red t1 V t1' V' ->
      red (trm_match t1 c t2 t3) V (trm_match t1' c t2 t3) V'
  | red_match_2 : forall V c1 c2 t1 t2 t3,
      store V ->
      c1 = c2 ->
      value (trm_constructor c1 t1) ->
      term_body t2 ->
      term_body t3 ->
      red (trm_match (trm_constructor c1 t1) c2 t2 t3) V
          (t2 ^^ (trm_constructor c1 t1)) V
  | red_match_3 : forall V c1 c2 t1 t2 t3,
      store V ->
      c1 <> c2 ->
      value (trm_constructor c1 t1) ->
      term_body t2 ->
      term_body t3 ->
      red (trm_match (trm_constructor c1 t1) c2 t2 t3) V
          (t3 ^^ (trm_constructor c1 t1)) V
  | red_destruct_1 : forall V V' c t1 t1' t2,
      term_body t2 ->
      red t1 V t1' V' ->
      red (trm_destruct t1 c t2) V (trm_destruct t1' c t2) V'
  | red_destruct_2 : forall V c1 c2 t1 t2,
      store V ->
      c1 = c2 ->
      value (trm_constructor c1 t1) ->
      term_body t2 ->
      red (trm_destruct (trm_constructor c1 t1) c2 t2) V
          (t2 ^^ t1) V
  | red_absurd : forall V V' t t',
      red t V t' V' ->
      red (trm_absurd t) V (trm_absurd t') V'
  | red_prod_1 : forall V V' t1 t1' t2,
      term t2 ->
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
      store V ->
      value t1 -> 
      value t2 ->  
      red (trm_fst (trm_prod t1 t2)) V t1 V
  | red_snd_1 : forall V V' t t',
      red t V t' V' ->
      red (trm_snd t) V (trm_snd t') V'
  | red_snd_2 : forall V t1 t2, 
      store V ->
      value t1 -> 
      value t2 ->  
      red (trm_snd (trm_prod t1 t2)) V t2 V
  | red_ref_1 : forall V V' t t',
      red t V t' V' ->
      red (trm_ref t) V (trm_ref t') V'
  | red_ref_2 : forall V t l,
      store V ->
      value t ->
      l # V ->
      red (trm_ref t) V (trm_loc l) (V & l ~ t)
  | red_get_1 : forall V V' t t',
      red t V t' V' ->
      red (trm_get t) V (trm_get t') V'
  | red_get_2 : forall V t l,
      store V ->
      binds l t V ->
      red (trm_get (trm_loc l)) V t V
  | red_set_1 : forall V V' t1 t1' t2,
      term t2 ->
      red t1 V t1' V' ->
      red (trm_set t1 t2) V (trm_set t1' t2) V'
  | red_set_2 : forall V V' t1 t2 t2',
      value t1 ->
      red t2 V t2' V' ->
      red (trm_set t1 t2) V (trm_set t1 t2') V'
  | red_set_3 : forall V l t2,
      store V ->
      value t2 ->
      red (trm_set (trm_loc l) t2) V trm_unit (V & l ~ t2).

(* ************************************************************** *)
(** ** Description of the results *)

(** Goal is to prove preservation and progress *)

Definition preservation := forall E P t t' V V' T,
  typing E P t T ->
  typing_store E V P ->
  red t V t' V' ->
  exists P',
    extends P P'
    /\ typing E P' t' T
    /\ typing_store E V' P'.


Definition progress := forall E P V t T,
  no_term_bindings E ->
  typing E P t T ->
  typing_store E V P ->
     value t 
  \/ exists t' V', red t V t' V'.
