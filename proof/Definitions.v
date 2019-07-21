(************************************************
 *          Row Subtyping - Definitions         *
 *                 Leo White                    *
 ************************************************)

(* The definition of the type system *) 

Set Implicit Arguments.
Require Import  List LibLN Cofinite.
Implicit Types x : var.
Implicit Types X : var.

(* *************************************************************** *)
(** ** Description of types *)

(* Kinds *)

Inductive knd : Type :=
  | knd_type : knd
  | knd_row : cset -> knd.

Notation knd_row_all :=
  (knd_row CSet.universe).

(** Representation of pre-types *)

Inductive typ : Type :=
  | typ_bvar : nat -> typ
  | typ_fvar : var -> typ
  | typ_constructor : nat -> typ -> typ
  | typ_or : cset -> cset -> typ -> typ -> typ
  | typ_proj : cset -> cset -> typ -> typ
  | typ_variant : typ -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_ref   : typ -> typ
  | typ_unit : typ
  | typ_prod : typ -> typ -> typ
  | typ_mu : knd -> typ -> typ
  | typ_top : knd -> typ
  | typ_bot : knd -> typ
  | typ_meet : typ -> typ -> typ
  | typ_join : typ -> typ -> typ.

Definition typ_fvars Xs :=
  List.map typ_fvar Xs.

(* Range kinds *)

Inductive rng : Type := Rng {
  rng_lower : typ ;
  rng_upper : typ ;
  rng_kind : knd; }.

Notation rng_all K :=
  (Rng (typ_bot K) (typ_top K) K).

Notation rng_only_lower T K :=
  (Rng T (typ_top K) K).

Notation rng_only_upper T K :=
  (Rng (typ_bot K) T K).

(** Type schemes. *)

Inductive sch : Type := Sch { 
  sch_ranges : list rng ; 
  sch_body  : typ }.

Definition sch_empty T := Sch nil T.

Fixpoint sch_arity (M : sch) : nat :=
  List.length (sch_ranges M).

(** Opening a type. *)

Fixpoint typ_var_open (k : nat) (Us : list typ) (i : nat) (T : typ) : typ :=
  match k with
  | 0 => List.nth i Us T
  | S k =>
    match i with
    | 0 => T
    | S i => typ_var_open k Us i T
    end
  end.

Fixpoint typ_open_rec (k : nat) (T : typ) (Us : list typ)
  {struct T} : typ :=
  match T with
  | typ_bvar i => typ_var_open k Us i (typ_bvar i)
  | typ_fvar x => typ_fvar x 
  | typ_constructor c T =>
    typ_constructor c (typ_open_rec k T Us)
  | typ_or cs1 cs2 T1 T2 =>
    typ_or cs1 cs2 (typ_open_rec k T1 Us) (typ_open_rec k T2 Us)
  | typ_proj cs1 cs2 T =>
    typ_proj cs1 cs2 (typ_open_rec k T Us)
  | typ_variant T => typ_variant (typ_open_rec k T Us)
  | typ_arrow T1 T2 =>
    typ_arrow (typ_open_rec k T1 Us) (typ_open_rec k T2 Us)
  | typ_ref T => typ_ref (typ_open_rec k T Us)
  | typ_unit => typ_unit
  | typ_prod T1 T2 =>
    typ_prod (typ_open_rec k T1 Us) (typ_open_rec k T2 Us)
  | typ_mu K T => typ_mu K (typ_open_rec (S k) T Us)
  | typ_top K => typ_top K
  | typ_bot K => typ_bot K
  | typ_meet T1 T2 =>
    typ_meet (typ_open_rec k T1 Us) (typ_open_rec k T2 Us)
  | typ_join T1 T2 =>
    typ_join (typ_open_rec k T1 Us) (typ_open_rec k T2 Us)
  end.

Definition typ_open T Us := typ_open_rec 0 T Us.

Definition typ_open_vars T Xs := typ_open T (typ_fvars Xs).

Notation typ_open_var T X :=
  (typ_open_vars T (X :: nil)).

(** Opening a range. *)

Definition rng_open (R : rng) (Us : list typ) : rng :=
  Rng (typ_open (rng_lower R) Us)
      (typ_open (rng_upper R) Us) (rng_kind R).

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
      type (typ_or cs1 cs2 T1 T2)
  | type_proj : forall T cs1 cs2,
      type T ->
      type (typ_proj cs1 cs2 T)
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
  | type_mu : forall L T K,
      (forall X, X \notin L -> type (typ_open_var T X)) -> 
      type (typ_mu K T)
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
      CSet.Nonempty cs -> kind (knd_row cs).

Inductive kinds : list knd -> Prop :=
  | kinds_nil : kinds nil
  | kinds_cons : forall K Ks,
      kind K ->
      kinds Ks ->
      kinds (K :: Ks).

(** Well-formed ranges *)

Inductive range : rng -> Prop :=
  | range_c : forall T1 T2 K,
      kind K ->
      type T1 ->
      type T2 ->
      range (Rng T1 T2 K).

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

Inductive scheme_aux : vars -> sch -> Prop :=
  | scheme_aux_c : forall L M,
      (forall Xs,
          fresh L (sch_arity M) Xs ->
          ranges_and_type
            (rng_open_vars_list (sch_ranges M) Xs)
            (instance_vars M Xs)) ->
      scheme_aux L M.

Inductive scheme : sch -> Prop :=
  | scheme_c : forall L M,
      scheme_aux L M -> scheme M.  

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

Fixpoint trm_var_open (k : nat) (us : list trm) (i : nat) (t : trm) : trm :=
  match k with
  | 0 => List.nth i us t
  | S k =>
    match i with
    | 0 => t
    | S i => trm_var_open k us i t
    end
  end.

Fixpoint trm_open_rec (k : nat) (us : list trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i  => trm_var_open k us i (trm_bvar i)
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
          term (t ^* (y::x::nil))) ->
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
  x \notin L -> y \notin (L \u \{x}) -> term (t ^* (y::x::nil)).

(* ****************************************************** *)
(** ** Description of range environments *)

(** Pre-environment is an associative list of bindings. *)

Definition tenv := LibEnv.env rng.

Definition bind_sch_ranges (Xs : list var) (M : sch) : tenv :=
  Xs ~* (rng_open_vars_list (sch_ranges M) Xs).

Notation "Xs ~: M" := (bind_sch_ranges Xs M)
  (at level 23, left associativity) : env_scope.

(** Environment is a pre-environment with unique bindings *)

Inductive type_environment_extension
  : tenv -> tenv -> Prop :=
  | type_environment_extension_empty : forall E,
      type_environment_extension E empty
  | type_environment_extension_push : forall E1 E2 X R,
      type_environment_extension E1 E2 ->
      range R ->
      X # E1 ->
      X # E2 ->
      type_environment_extension E1 (E2 & X ~ R).

Definition type_environment E :=
  type_environment_extension empty E.

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
(** ** Syntactic equality on knds and typs *)

Definition eq_knd k1 k2 :=
  match k1, k2 with
  | knd_type, knd_type => true
  | knd_type, _ => false
  | knd_row cs1, knd_row cs2 =>
    CSet.equal cs1 cs2
  | knd_row _, _ => false
  end.

Fixpoint eq_typ T1 T2 : bool :=
  match T1, T2 with
  | typ_bvar n1, typ_bvar n2 =>
    Nat.eqb n1 n2
  | typ_bvar _, _ => false
  | typ_fvar X1, typ_fvar X2 =>
    var_compare X1 X2
  | typ_fvar _, _ => false
  | typ_constructor c1 T1, typ_constructor c2 T2 =>
    Nat.eqb c1 c2 && eq_typ T1 T2
  | typ_constructor _ _, _ => false
  | typ_or csa1 csb1 Ta1 Tb1, typ_or csa2 csb2 Ta2 Tb2 =>
    CSet.equal csa1 csa2 && CSet.equal csb1 csb2
    && eq_typ Ta1 Ta2 && eq_typ Tb1 Tb2
  | typ_or _ _ _ _, _ => false
  | typ_proj csa1 csb1 T1, typ_proj csa2 csb2 T2 =>
    CSet.equal csa1 csa2 && CSet.equal csb1 csb2
    && eq_typ T1 T2
  | typ_proj _ _ _, _ => false
  | typ_variant T1, typ_variant T2 =>
    eq_typ T1 T2
  | typ_variant _, _ => false
  | typ_arrow Ta1 Tb1, typ_arrow Ta2 Tb2 =>
    eq_typ Ta1 Ta2 && eq_typ Tb1 Tb2
  | typ_arrow _ _, _ => false
  | typ_ref T1, typ_ref T2 =>
    eq_typ T1 T2
  | typ_ref _, _ => false
  | typ_unit, typ_unit => true
  | typ_unit, _ => false
  | typ_prod Ta1 Tb1, typ_prod Ta2 Tb2 =>
    eq_typ Ta1 Ta2 && eq_typ Tb1 Tb2
  | typ_prod _ _, _ => false
  | typ_mu K1 T1, typ_mu K2 T2 =>
    eq_knd K1 K2 && eq_typ T1 T2
  | typ_mu _ _, _ => false
  | typ_top K1, typ_top K2 =>
    eq_knd K1 K2
  | typ_top _, _ => false
  | typ_bot K1, typ_bot K2 =>
    eq_knd K1 K2
  | typ_bot _, _ => false
  | typ_meet Ta1 Tb1, typ_meet Ta2 Tb2 =>
    eq_typ Ta1 Ta2 && eq_typ Tb1 Tb2
  | typ_meet _ _, _ => false
  | typ_join Ta1 Tb1, typ_join Ta2 Tb2 =>
    eq_typ Ta1 Ta2 && eq_typ Tb1 Tb2
  | typ_join _ _, _ => false
  end.

(** ************************************************** *)
(** ** Description of recursive environment *)

Definition qenv := list (typ * typ * knd).

Bind Scope list_scope with qenv.

Inductive in_qenv : qenv -> typ -> typ -> knd -> Prop :=
  | in_qenv_head : forall T1 T2 K Q,
      in_qenv ((T1, T2, K) :: Q) T1 T2 K
  | in_qenv_tail : forall T1 T2 K Q T1' T2' K',
      in_qenv Q T1' T2' K' ->
      in_qenv ((T1, T2, K) :: Q) T1' T2' K'.

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

Definition rngs_kinds Rs :=
  List.map rng_kind Rs.

(* inputs: tenv(1), tenv(1)
   subject: typ
   outputs: knd *)
Inductive kinding : tenv -> tenv -> typ -> knd -> Prop :=
  | kinding_var : forall E1 E2 X T1 T2 K,
      binds X (Rng T1 T2 K) E1 ->
      kinding E1 E2 (typ_fvar X) K
  | kinding_constructor : forall E1 E2 c T cs,
      kinding (E1 & E2) empty T knd_type ->
      cs = CSet.singleton c ->
      kinding E1 E2 (typ_constructor c T) (knd_row cs)
  | kinding_or : forall E1 E2 T1 T2 cs1 cs2 cs12,
      kinding E1 E2 T1 (knd_row cs1) ->
      kinding E1 E2 T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      kinding E1 E2 (typ_or cs1 cs2 T1 T2) (knd_row cs12)
  | kinding_proj : forall E1 E2 T cs1 cs2,
      kinding E1 E2 T (knd_row cs1) ->
      CSet.Subset cs2 cs1 ->
      CSet.Nonempty cs2 ->
      kinding E1 E2 (typ_proj cs1 cs2 T) (knd_row cs2)
  | kinding_variant : forall E1 E2 T,
      kinding (E1 & E2) empty T knd_row_all ->
      kinding E1 E2 (typ_variant T) knd_type
  | kinding_arrow : forall E1 E2 T1 T2,
      kinding (E1 & E2) empty T1 knd_type -> 
      kinding (E1 & E2) empty T2 knd_type -> 
      kinding E1 E2 (typ_arrow T1 T2) knd_type
  | kinding_ref : forall E1 E2 T,
      kinding (E1 & E2) empty T knd_type ->
      kinding E1 E2 (typ_ref T) knd_type
  | kinding_unit : forall E1 E2,
      kinding E1 E2 typ_unit knd_type
  | kinding_prod : forall E1 E2 T1 T2,
      kinding (E1 & E2) empty T1 knd_type -> 
      kinding (E1 & E2) empty T2 knd_type -> 
      kinding E1 E2 (typ_prod T1 T2) knd_type
  | kinding_mu : forall L E1 E2 T K,
      kind K ->
      (forall X,
        X \notin L ->
        kinding E1 (E2 & X ~ rng_all K)
          (typ_open_var T X) K) ->
      kinding E1 E2 (typ_mu K T) K
  | kinding_top : forall E1 E2 K,
      kind K ->
      kinding E1 E2 (typ_top K) K
  | kinding_bot : forall E1 E2 K,
      kind K ->
      kinding E1 E2 (typ_bot K) K
  | kinding_meet : forall E1 E2 T1 T2 K,
      kinding E1 E2 T1 K ->
      kinding E1 E2 T2 K ->
      kinding E1 E2 (typ_meet T1 T2) K
  | kinding_join : forall E1 E2 T1 T2 K,
      kinding E1 E2 T1 K ->
      kinding E1 E2 T2 K ->
      kinding E1 E2 (typ_join T1 T2) K.

(* inputs: tenv(1), tenv(2)
   subject: list typ
   outputs: list knd *)
Inductive kindings : tenv -> tenv -> list typ -> list knd -> Prop :=
  | kindings_nil : forall E1 E2,
      kindings E1 E2 nil nil
  | kindings_cons : forall E1 E2 T Ts K Ks,
      kinding E1 E2 T K ->
      kindings E1 E2 Ts Ks ->
      kindings E1 E2 (T :: Ts) (K :: Ks).

(** ************************************************** *)
(** ** Equality *)

(** The different versions of the system *)
Inductive version : Type :=
  | version_row_subtyping
  | version_full_subtyping.

(** Core of the equality relation on types *)

(* inputs: tenv(1), tenv(2), typ(1), typ(2), knd
   subjects:
   outputs: *)
Inductive type_equal_core'
  : version -> knd -> typ -> typ -> Prop :=
  | type_equal_core_or_commutative :
      forall v T1 T2 cs1 cs2 cs12,
      type_equal_core' v (knd_row cs12)
        (typ_or cs1 cs2 T1 T2) (typ_or cs2 cs1 T2 T1)
  | type_equal_core_or_associative :
      forall v T1 T2 T3 cs1 cs2 cs3 cs12 cs23 cs123,
      type_equal_core' v (knd_row cs123)
        (typ_or cs1 cs23 T1 (typ_or cs2 cs3 T2 T3))
        (typ_or cs12 cs3 (typ_or cs1 cs2 T1 T2) T3)
  | type_equal_core_or_bot : forall v cs1 cs2 cs12,
      type_equal_core' v (knd_row cs12)
        (typ_or cs1 cs2 (typ_bot (knd_row cs1))
                (typ_bot (knd_row cs2)))
        (typ_bot (knd_row cs12))
  | type_equal_core_or_top : forall v cs1 cs2 cs12,
      type_equal_core' v (knd_row cs12)
        (typ_or cs1 cs2 (typ_top (knd_row cs1))
                (typ_top (knd_row cs2)))
        (typ_top (knd_row cs12))
  | type_equal_core_or_proj :
      forall v T cs1 cs2 cs3 cs23,
      type_equal_core' v (knd_row cs23)
        (typ_or cs2 cs3 (typ_proj cs1 cs2 T)
                (typ_proj cs1 cs3 T))
        (typ_proj cs1 cs23 T)
  | type_equal_core_proj_id : forall v T cs1,
      type_equal_core' v (knd_row cs1)
        (typ_proj cs1 cs1 T) T
  | type_equal_core_proj_compose : forall v T cs1 cs2 cs3,
      type_equal_core' v (knd_row cs3)
        (typ_proj cs2 cs3 (typ_proj cs1 cs2 T))
        (typ_proj cs1 cs3 T)
  | type_equal_core_proj_or_l :
      forall v T1 T2 cs1 cs2 cs3 cs12,
      type_equal_core' v (knd_row cs3)
        (typ_proj cs12 cs3 (typ_or cs1 cs2 T1 T2))
        (typ_proj cs1 cs3 T1)
  | type_equal_core_proj_or_r :
      forall v T1 T2 cs1 cs2 cs3 cs12,
      type_equal_core' v (knd_row cs3)
        (typ_proj cs12 cs3 (typ_or cs1 cs2 T1 T2))
        (typ_proj cs2 cs3 T2)
  | type_equal_core_proj_or_both :
      forall v T1 T2 cs1 cs2 cs3 cs4 cs12 cs34,
      type_equal_core' v (knd_row cs34)
        (typ_proj cs12 cs34 (typ_or cs1 cs2 T1 T2))
        (typ_or cs3 cs4 (typ_proj cs1 cs3 T1)
                (typ_proj cs2 cs4 T2))
  | type_equal_core_meet_commutative : forall v T1 T2 K,
      type_equal_core' v K (typ_meet T1 T2) (typ_meet T2 T1)
  | type_equal_core_meet_associative : forall v T1 T2 T3 K,
      type_equal_core' v K
        (typ_meet T1 (typ_meet T2 T3))
        (typ_meet (typ_meet T1 T2) T3)
  | type_equal_core_meet_identity : forall v T1 K,
      type_equal_core' v K (typ_meet T1 (typ_top K)) T1
  | type_equal_core_meet_absorption : forall v T1 T2 K,
      type_equal_core' v K (typ_meet T1 (typ_join T1 T2)) T1
  | type_equal_core_meet_distribution :
      forall v T1 T2 T3 K,
      type_equal_core' v K
        (typ_meet T1 (typ_join T2 T3))
        (typ_join (typ_meet T1 T2) (typ_meet T1 T3))
  | type_equal_core_join_commutative : forall v T1 T2 K,
      type_equal_core' v K (typ_join T1 T2) (typ_join T2 T1)
  | type_equal_core_join_associative : forall v T1 T2 T3 K,
      type_equal_core' v K
        (typ_join T1 (typ_join T2 T3))
        (typ_join (typ_join T1 T2) T3)
  | type_equal_core_join_identity : forall v T1 K,
      type_equal_core' v K (typ_join T1 (typ_bot K)) T1
  | type_equal_core_join_absorption : forall v T1 T2 K,
      type_equal_core' v K (typ_join T1 (typ_meet T1 T2)) T1
  | type_equal_core_join_distribution :
      forall v T1 T2 T3 K,
      type_equal_core' v K
        (typ_join T1 (typ_meet T2 T3))
        (typ_meet (typ_join T1 T2) (typ_join T1 T3))
  | type_equal_core_or_meet :
      forall v T1 T2 T3 T4 cs1 cs2 cs12,
      type_equal_core' v (knd_row cs12)
        (typ_or cs1 cs2 (typ_meet T1 T3) (typ_meet T2 T4))
        (typ_meet (typ_or cs1 cs2 T1 T2)
                  (typ_or cs1 cs2 T3 T4))
  | type_equal_core_or_join :
      forall v T1 T2 T3 T4 cs1 cs2 cs12,
      type_equal_core' v (knd_row cs12)
        (typ_or cs1 cs2 (typ_join T1 T3) (typ_join T2 T4))
        (typ_join (typ_or cs1 cs2 T1 T2)
                  (typ_or cs1 cs2 T3 T4))
  | type_equal_core_proj_meet : forall v T1 T2 cs1 cs2,
      type_equal_core' v (knd_row cs2)
        (typ_proj cs1 cs2 (typ_meet T1 T2))
        (typ_meet (typ_proj cs1 cs2 T1)
                  (typ_proj cs1 cs2 T2))
  | type_equal_core_proj_join : forall v T1 T2 cs1 cs2,
      type_equal_core' v (knd_row cs2)
        (typ_proj cs1 cs2 (typ_join T1 T2))
        (typ_join (typ_proj cs1 cs2 T1)
                  (typ_proj cs1 cs2 T2))
  | type_equal_core_variant_meet : forall v T1 T2,
      type_equal_core' v knd_type
        (typ_variant (typ_meet T1 T2))
        (typ_meet (typ_variant T1) (typ_variant T2))
  | type_equal_core_variant_join : forall v T1 T2,
      type_equal_core' v knd_type
        (typ_variant (typ_join T1 T2))
        (typ_join (typ_variant T1) (typ_variant T2))
  | type_equal_core_constructor_meet : forall c T1 T2 cs,
      type_equal_core' version_full_subtyping (knd_row cs)
        (typ_constructor c (typ_meet T1 T2))
        (typ_meet (typ_constructor c T1)
                  (typ_constructor c T2))
  | type_equal_core_constructor_join : forall c T1 T2 cs,
      type_equal_core' version_full_subtyping (knd_row cs)
        (typ_constructor c (typ_join T1 T2))
        (typ_join (typ_constructor c T1)
                  (typ_constructor c T2))
  | type_equal_core_arrow_meet : forall T1 T2 T3 T4,
      type_equal_core' version_full_subtyping knd_type
        (typ_arrow (typ_join T1 T3) (typ_meet T2 T4))
        (typ_meet (typ_arrow T1 T2) (typ_arrow T3 T4))
  | type_equal_core_arrow_join : forall T1 T2 T3 T4,
      type_equal_core' version_full_subtyping knd_type
        (typ_arrow (typ_meet T1 T3) (typ_join T2 T4))
        (typ_join (typ_arrow T1 T2) (typ_arrow T3 T4))
  | type_equal_core_prod_meet : forall T1 T2 T3 T4,
      type_equal_core' version_full_subtyping knd_type
        (typ_prod (typ_meet T1 T3) (typ_meet T2 T4))
        (typ_meet (typ_prod T1 T2) (typ_prod T3 T4))
  | type_equal_core_prod_join : forall T1 T2 T3 T4,
      type_equal_core' version_full_subtyping knd_type
        (typ_prod (typ_join T1 T3) (typ_join T2 T4))
        (typ_join (typ_prod T1 T2) (typ_prod T3 T4))
  | type_equal_core_unroll : forall v T1 K,
      type_equal_core' v K
        (typ_mu K T1) (typ_open T1 ((typ_mu K T1) :: nil)).

Notation type_equal_core v T1 T2 K :=
  (type_equal_core' v K T1 T2).

(* Reflexive, symetric, transitive, congruence closure
   of type_equal_core plus variable bounds *)

(* inputs: tenv(1), tenv(1)
   subjects: typ(1), typ(2)
   outputs: knd *)
Inductive type_equal'
  : version -> tenv -> tenv -> qenv -> qenv ->
      knd -> typ -> typ -> Prop :=
  | type_equal_range_lower : forall v E1 E2 Q1 Q2 X T1 T2 K,
      binds X (Rng T1 T2 K) E1 ->
      type_equal' v E1 E2 Q1 Q2 K
        T1 (typ_meet T1 (typ_fvar X))
  | type_equal_range_upper : forall v E1 E2 Q1 Q2 X T1 T2 K,
      binds X (Rng T1 T2 K) E1 ->
      type_equal' v E1 E2 Q1 Q2 K
        (typ_fvar X) (typ_meet (typ_fvar X) T2)
  | type_equal_constructor : forall v E1 E2 Q1 Q2 c T1 T1' cs,
      type_equal' v (E1 & E2) empty
       ((typ_constructor c T1, typ_constructor c T1',
         knd_row cs) :: Q2 ++ Q1) nil
       knd_type T1 T1' ->
      cs = CSet.singleton c ->
      type_equal' v E1 E2 Q1 Q2 (knd_row cs)
        (typ_constructor c T1) (typ_constructor c T1')
  | type_equal_or : forall v E1 E2 Q1 Q2 T1 T1' T2 T2' cs1 cs2 cs12,
      type_equal' v E1 E2 Q1
        ((typ_or cs1 cs2 T1 T2, typ_or cs1 cs2 T1' T2',
          knd_row cs12) :: Q2)
        (knd_row cs1) T1 T1' ->
      type_equal' v E1 E2 Q1
        ((typ_or cs1 cs2 T1 T2, typ_or cs1 cs2 T1' T2',
          knd_row cs12) :: Q2)
        (knd_row cs2) T2 T2' ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal' v E1 E2 Q1 Q2 (knd_row cs12)
        (typ_or cs1 cs2 T1 T2) (typ_or cs1 cs2 T1' T2')
  | type_equal_proj : forall v E1 E2 Q1 Q2 T1 T1' cs1 cs2,
      type_equal' v E1 E2 Q1
        ((typ_proj cs1 cs2 T1, typ_proj cs1 cs2 T1',
         knd_row cs2) :: Q2)
        (knd_row cs1) T1 T1' ->
      CSet.Subset cs2 cs1 ->
      CSet.Nonempty cs2 ->
      type_equal' v E1 E2 Q1 Q2 (knd_row cs2)
        (typ_proj cs1 cs2 T1) (typ_proj cs1 cs2 T1')
  | type_equal_variant : forall v E1 E2 Q1 Q2 T1 T1',
      type_equal' v (E1 & E2) empty
        ((typ_variant T1, typ_variant T1', knd_type) :: Q2 ++ Q1) nil
        knd_row_all T1 T1' ->
      type_equal' v E1 E2 Q1 Q2 knd_type
        (typ_variant T1) (typ_variant T1')
  | type_equal_arrow : forall v E1 E2 Q1 Q2 T1 T1' T2 T2',
      type_equal' v (E1 & E2) empty
        ((typ_arrow T1 T2, typ_arrow T1' T2', knd_type) :: Q2 ++ Q1) nil
        knd_type T1 T1' ->
      type_equal' v (E1 & E2) empty
        ((typ_arrow T1 T2, typ_arrow T1' T2', knd_type) :: Q2 ++ Q1) nil
        knd_type T2 T2' ->
      type_equal' v E1 E2 Q1 Q2 knd_type
        (typ_arrow T1 T2) (typ_arrow T1' T2')
  | type_equal_prod : forall v E1 E2 Q1 Q2 T1 T1' T2 T2',
      type_equal' v (E1 & E2) empty
        ((typ_prod T1 T2, typ_prod T1' T2', knd_type) :: Q2 ++ Q1) nil
        knd_type T1 T1' ->
      type_equal' v (E1 & E2) empty
        ((typ_prod T1 T2, typ_prod T1' T2', knd_type) :: Q2 ++ Q1) nil
        knd_type T2 T2' ->
      type_equal' v E1 E2 Q1 Q2 knd_type
        (typ_prod T1 T2) (typ_prod T1' T2')
  | type_equal_ref : forall v E1 E2 Q1 Q2 T1 T1',
      type_equal' v (E1 & E2) empty
        ((typ_ref T1, typ_ref T1', knd_type) :: Q2 ++ Q1) nil
        knd_type T1 T1' ->
      type_equal' v E1 E2 Q1 Q2 knd_type (typ_ref T1) (typ_ref T1')
  | type_equal_meet : forall v E1 E2 Q1 Q2 T1 T1' T2 T2' K,
      type_equal' v E1 E2 Q1
        ((typ_meet T1 T2, typ_meet T1' T2', K) :: Q2)
        K T1 T1' ->
      type_equal' v E1 E2 Q1
        ((typ_meet T1 T2, typ_meet T1' T2', K) :: Q2)
        K T2 T2' -> 
      type_equal' v E1 E2 Q1 Q2 K (typ_meet T1 T2) (typ_meet T1' T2')
  | type_equal_join : forall v E1 E2 Q1 Q2 T1 T1' T2 T2' K,
      type_equal' v E1 E2 Q1
        ((typ_join T1 T2, typ_join T1' T2', K) :: Q2)
        K T1 T1' ->
      type_equal' v E1 E2 Q1
        ((typ_join T1 T2, typ_join T1' T2', K) :: Q2)
        K T2 T2' ->
      type_equal' v E1 E2 Q1 Q2 K (typ_join T1 T2) (typ_join T1' T2')
  | type_equal_of_core : forall v T1 T1' K,
      type_equal_core v T1 T1' K ->
      forall E1 E2 Q1 Q2,
      kinding E1 E2 T1 K ->
      kinding E1 E2 T1' K ->
      type_equal' v E1 E2 Q1 Q2 K T1 T1'
  | type_equal_rec : forall v E1 E2 Q1 Q2 T1 T1' K,
      in_qenv Q1 T1 T1' K ->
      kinding E1 E2 T1 K ->
      kinding E1 E2 T1' K ->
      type_equal' v E1 E2 Q1 Q2 K T1 T1'
  | type_equal_reflexive : forall v E1 E2 Q1 Q2 T1 K,
      kinding E1 E2 T1 K ->
      type_equal' v E1 E2 Q1 Q2 K T1 T1
  | type_equal_symmetric : forall v E1 E2 Q1 Q2 T1 T2 K,
      type_equal' v E1 E2 Q1 ((T2, T1, K) :: Q2) K T1 T2 ->
      type_equal' v E1 E2 Q1 Q2 K T2 T1
  | type_equal_transitive : forall v E1 E2 Q1 Q2 T1 T2 T3 K,
      type_equal' v E1 E2 Q1 ((T1, T3, K) :: Q2) K T1 T2 ->
      type_equal' v E1 E2 Q1 ((T1, T3, K) :: Q2) K T2 T3 ->
      type_equal' v E1 E2 Q1 Q2 K T1 T3.

Notation type_equal v E1 E2 Q1 Q2 T1 T2 K :=
  (type_equal' v E1 E2 Q1 Q2 K T1 T2).

(* Subtyping *)

Definition subtype' v E1 E2 Q1 Q2 K T1 T2 :=
  type_equal v E1 E2 Q1 Q2 T1 (typ_meet T1 T2) K.

Notation subtype v E1 E2 Q1 Q2 T1 T2 K :=
  (subtype' v E1 E2 Q1 Q2 K T1 T2).

(** ************************************************** *)
(* Validity of ranges, schemes and kinding environments *)

(* Validity of ranges *)

(* inputs: tenv(1), tenv(2)
   subject: rng
   outputs: *)
Inductive valid_range : version -> tenv -> tenv -> rng -> Prop :=
  | valid_range_c : forall v E1 E2 T1 T2 K,
      kind K ->
      kinding E1 E2 T1 K ->
      kinding E1 E2 T2 K ->
      subtype v E1 E2 nil nil T1 T2 K ->
      valid_range v E1 E2 (Rng T1 T2 K).

(* Validity of kinding environments *)

(* inputs: tenv(1), tenv(3)
   subject: tenv(2)
   outputs: *)
Inductive valid_tenv_rec : version -> tenv -> tenv -> tenv -> Prop :=
  | valid_tenv_rec_empty : forall v E1 E2,
      valid_tenv_rec v E1 empty E2
  | valid_tenv_rec_push : forall v E1 E2 E3 X R,
      valid_tenv_rec v E1 E2 (X ~ R & E3) ->
      valid_range v (E1 & E2) (X ~ R & E3) R ->
      X # E1 ->
      X # E2 ->
      X # E3 ->
      valid_tenv_rec v E1 (E2 & X ~ R) E3.

(* inputs: tenv(1)
   subject: tenv(2)
   outputs: *)
Definition valid_tenv_extension v E1 E2 :=
  valid_tenv_rec v E1 E2 empty.

(* inputs:
   subject: tenv
   outputs: *)
Definition valid_tenv v E :=
  valid_tenv_extension v empty E.

(* Validity of type schemes *)

(* inputs: tenv(1)
   subjects: tenv(2), typ
   outputs: *)
Inductive valid_tenv_extension_and_type
  : version -> tenv -> tenv -> typ -> Prop :=
  | valid_tenv_extension_and_type_c : forall v E1 E2 T,
      valid_tenv_extension v E1 E2 ->
      kinding (E1 & E2) empty T knd_type ->
      valid_tenv_extension_and_type v E1 E2 T.

(* inputs: tenv
   subject: sch
   outputs: *)
Inductive valid_scheme_aux : version -> vars -> tenv -> sch -> Prop :=
  | valid_scheme_aux_c : forall v L E M,
      (forall Xs,
          fresh L (sch_arity M) Xs ->
          valid_tenv_extension_and_type v E (Xs ~: M)
            (instance_vars M Xs)) ->
      valid_scheme_aux v L E M.

(* inputs: tenv
   subject: sch
   outputs: *)
Inductive valid_scheme : version -> tenv -> sch -> Prop :=
  | valid_scheme_c : forall L v E M,
      valid_scheme_aux v L E M -> valid_scheme v E M.

(* inputs: tenv
   subject: list sch
   outputs: *)
Inductive valid_schemes : version -> tenv -> list sch -> Prop :=
  | valid_schemes_nil : forall v E,
      valid_schemes v E nil
  | valid_schemes_cons : forall v E M Ms,
      valid_scheme v E M ->
      valid_schemes v E Ms ->
      valid_schemes v E (M :: Ms).

(** ************************************************** *)
(** Ranging *)

(* inputs: tenv(1), tenv(2)
   subject: typ
   outputs: rng *)
Inductive ranging : version -> tenv -> tenv -> typ -> rng -> Prop :=
  | ranging_c : forall v E1 E2 T T1 T2 K,
      kinding E1 E2 T K ->
      subtype v E1 E2 nil nil T1 T K ->
      subtype v E1 E2 nil nil T T2 K ->
      ranging v E1 E2 T (Rng T1 T2 K).

(* inputs: tenv(1), tenv(2)
   subject: list typ
   outputs: list rng *)
Inductive rangings
  : version -> tenv -> tenv -> list typ -> list rng -> Prop :=
  | rangings_nil : forall v E1 E2,
      rangings v E1 E2 nil nil
  | rangings_cons : forall v E1 E2 T Ts R Rs,
      ranging v E1 E2 T R ->
      rangings v E1 E2 Ts Rs ->
      rangings v E1 E2 (T :: Ts) (R :: Rs).

(** Validity of instances *)

(* inputs: tenv, sch
   subject: list typ
   outputs: *)
Inductive valid_instance
  : version -> tenv -> list typ -> sch -> Prop :=
  | valid_instance_c : forall v E Ts Rs M,
      rangings v E empty Ts Rs ->
      Rs = rng_open_list (sch_ranges M) Ts ->
      valid_instance v E Ts M.

(* ****************************************************** *)
(** ** Environments *)

(* Validity of typing environments *)

(* inputs: tenv
   subject: env
   outputs: *)
Inductive valid_env : version -> tenv -> env -> Prop :=
  | valid_env_empty : forall v E,
      valid_env v E empty
  | valid_env_push : forall v E D x M,
      valid_env v E D ->
      valid_scheme v E M ->
      x # D ->
      valid_env v E (D & x ~ M).

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
      kinding E empty T knd_type ->
      l # P ->
      valid_store_type E (P & l ~ T).

(* ****************************************************** *)
(** ** Description of typing *)

(* inputs: tenv, env, styp
   subject: trm
   outputs: typ *)
Inductive typing
  : version -> tenv -> env -> styp -> trm -> typ -> Prop :=
  | typing_equal : forall E D P t T1 T2,
      typing version_row_subtyping E D P t T1 ->
      type_equal version_row_subtyping E empty nil nil T1 T2 knd_type ->
      typing version_row_subtyping E D P t T2
  | typing_subsumption : forall E D P t T1 T2,
      typing version_full_subtyping E D P t T1 ->
      subtype version_full_subtyping E empty nil nil T1 T2 knd_type ->
      typing version_full_subtyping E D P t T2
  | typing_var : forall v E D P x M T Us,
      binds x M D -> 
      valid_instance v E Us M ->
      T = instance M Us ->
      typing v E D P (trm_fvar x) T
  | typing_abs : forall L v E D P T1 T2 t1,
      kinding E empty T1 knd_type ->
      (forall x, x \notin L -> 
        typing v E (D & x ~ sch_empty T1) P (t1 ^ x) T2) -> 
      typing v E D P (trm_abs t1) (typ_arrow T1 T2)
  | typing_app : forall v E P D T1 T2 t1 t2, 
      typing v E D P t1 (typ_arrow T1 T2) ->
      typing v E D P t2 T1 ->   
      typing v E D P (trm_app t1 t2) T2
  | typing_let_val : forall L M v E D P T2 t1 t2,
      value t1 ->
      valid_scheme_aux v L E M ->
      (forall Xs,
          fresh L (sch_arity M) Xs ->
          typing v
            (E & Xs ~: M) D P
            t1 (instance_vars M Xs)) ->
      (forall x,
          x \notin L ->
          typing v E (D & x ~ M) P (t2 ^ x) T2) -> 
      typing v E D P (trm_let t1 t2) T2
  | typing_let : forall L v E D P T1 T2 t1 t2, 
      kinding E empty T1 knd_type ->
      typing v E D P t1 T1 ->
      (forall x,
          x \notin L ->
          typing v E (D & x ~ sch_empty T1) P (t2 ^ x) T2) ->
      typing v E D P (trm_let t1 t2) T2
  | typing_constructor : forall c v E D P T1 T2 t,
      typing v E D P t T1 ->
      subtype v E empty nil nil
        (typ_constructor c T1)
        (typ_proj CSet.universe (CSet.singleton c) T2)
        (knd_row (CSet.singleton c)) ->
      typing v E D P (trm_constructor c t) (typ_variant T2)
  | typing_match :
      forall L c v E D P T1 T2 T3 T4 t1 t2 t3,
      typing v E D P t1 (typ_variant T1) ->
      subtype v E empty nil nil
        (typ_proj CSet.universe (CSet.singleton c) T1)
        (typ_proj CSet.universe (CSet.singleton c) T2)
        (knd_row (CSet.singleton c)) ->
      subtype v E empty nil nil
        (typ_proj CSet.universe (CSet.cosingleton c) T1)
        (typ_proj CSet.universe (CSet.cosingleton c) T3)
        (knd_row (CSet.cosingleton c)) ->
      (forall x, x \notin L ->
         typing v E (D & x ~ (sch_empty (typ_variant T2))) P
                (t2 ^ x) T4) ->
      (forall y, y \notin L -> 
         typing v E (D & y ~ (sch_empty (typ_variant T3))) P
                (t3 ^ y) T4) ->
      typing v E D P (trm_match t1 c t2 t3) T4
  | typing_destruct : forall L c v E D P T1 T2 T3 t1 t2,
      typing v E D P t1 (typ_variant T1) ->
      subtype v E empty nil nil
        (typ_proj CSet.universe (CSet.singleton c) T1)
        (typ_constructor c T2)
        (knd_row (CSet.singleton c)) ->
      subtype v E empty nil nil
        (typ_proj CSet.universe (CSet.cosingleton c) T1)
        (typ_bot (knd_row (CSet.cosingleton c)))
        (knd_row (CSet.cosingleton c)) ->
      (forall x, x \notin L ->
         typing v E (D & x ~ (sch_empty T2)) P
                (t2 ^ x) T3) ->
      typing v E D P (trm_destruct t1 c t2) T3
  | typing_absurd : forall v E D P T1 T2 t1,
      typing v E D P t1 (typ_variant T1) ->
      subtype v E empty nil nil
        T1 (typ_bot knd_row_all) knd_row_all ->
      kinding E empty T2 knd_type ->
      typing v E D P (trm_absurd t1) T2
  | typing_fix : forall L v E D P T1 T2 t1,
      kinding E empty T1 knd_type ->
      kinding E empty T2 knd_type ->
      (forall x y,
          x \notin L -> y \notin (L \u \{x}) ->
          typing
            v E (D & x ~ sch_empty (typ_arrow T1 T2)
                 & y ~ sch_empty T1)
            P (t1 ^* (y::x::nil)) T2) -> 
      typing v E D P (trm_fix t1) (typ_arrow T1 T2)
  | typing_unit : forall v E D P,
      typing v E D P trm_unit typ_unit
  | typing_prod : forall v E D P T1 T2 t1 t2,
      typing v E D P t1 T1 ->
      typing v E D P t2 T2 ->
      typing v E D P (trm_prod t1 t2) (typ_prod T1 T2)
  | typing_fst : forall v E D P T1 T2 t1,
      typing v E D P t1 (typ_prod T1 T2) ->
      typing v E D P (trm_fst t1) T1
  | typing_snd : forall v E D P T1 T2 t1,
      typing v E D P t1 (typ_prod T1 T2) ->
      typing v E D P (trm_snd t1) T2
  | typing_loc : forall v E D P l T1,
      binds l T1 P ->
      typing v E D P (trm_loc l) (typ_ref T1)
  | typing_ref : forall v E D P t1 T1,
      typing v E D P t1 T1 ->
      typing v E D P (trm_ref t1) (typ_ref T1)
  | typing_get : forall v E D P t1 T1,
      typing v E D P t1 (typ_ref T1) ->
      typing v E D P (trm_get t1) T1
  | typing_set : forall v E D P t1 t2 T1,
      typing v E D P t1 (typ_ref T1) ->
      typing v E D P t2 T1 ->
      typing v E D P (trm_set t1 t2) typ_unit.

(* inputs: tenv(1), env, styp
   subject: tenv(2), trm
   outputs: typ *)
Inductive valid_tenv_extension_and_typing
  : version -> tenv -> tenv -> env -> styp -> trm -> typ -> Prop :=
  | valid_tenv_extension_and_typing_c : forall v E1 E2 D P t T,
      valid_tenv_extension v E1 E2 ->
      typing v (E1 & E2) D P t T ->
      valid_tenv_extension_and_typing v E1 E2 D P t T.

(* inputs: tenv, env, styp
   subject: trm
   outputs: sch *)
Inductive typing_scheme
  : version -> tenv -> env -> styp -> trm -> sch -> Prop :=
  | typing_scheme_c : forall L v E D P t M,
      (forall Xs,
          fresh L (sch_arity M) Xs ->
          valid_tenv_extension_and_typing v E (Xs ~: M)
            D P t (instance_vars M Xs)) ->
      typing_scheme v E D P t M.

(* inputs: tenv, env, styp
   subject: list trm
   outputs: list sch *)
Inductive typing_schemes
  : version -> tenv -> env -> styp -> list trm -> list sch -> Prop :=
  | typing_schemes_nil : forall v E D P,
      typing_schemes v E D P nil nil
  | typing_schemes_cons : forall v E D P t ts M Ms,
      typing_scheme v E D P t M ->
      typing_schemes v E D P ts Ms ->
      typing_schemes v E D P (t :: ts) (M :: Ms).

(* inputs: tenv, env, loc, sto, styp
   subject:
   outputs: *)
Inductive typing_store_loc
  : loc -> version -> tenv -> env -> sto -> styp -> Prop :=
  | typing_store_loc_fresh : forall l v E D V P,
      l # V ->
      l # P ->
      typing_store_loc l v E D V P
  | typing_store_loc_bound : forall l v E D P V T t,
      binds l t V ->
      binds l T P ->
      typing v E D P t T ->
      typing_store_loc l v E D V P.

(* inputs: tenv, env, loc, sto, styp
   subject:
   outputs: *)
Inductive typing_store
  : version -> tenv -> env -> sto -> styp -> Prop :=
  | typing_store_c : forall v E D V P,
     (forall l, typing_store_loc l v E D V P) ->
     typing_store v E D V P.

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

Definition preservation := forall v E D P t t' V V' T,
  valid_tenv v E ->
  valid_env v E D ->
  valid_store_type E P ->
  store V ->
  typing v E D P t T ->
  typing_store v E D V P ->
  red t V t' V' ->
  exists P',
    extends P P'
    /\ valid_store_type E P'
    /\ store V'
    /\ typing v E D P' t' T
    /\ typing_store v E D V' P'.

Definition progress := forall v E P V t T,
  valid_tenv v E ->
  valid_store_type E P ->
  store V ->
  typing v E empty P t T ->
  typing_store v E empty V P ->
     value t 
  \/ exists t' V', red t V t' V'.

(* *************************************************************** *)
(** ** Add hints for various constructors *)

Hint Constructors kind kinds type types range ranges
  ranges_and_type scheme_aux scheme schemes term terms
  type_environment_extension environment store store_type in_qenv
  kinding kindings type_equal_core' type_equal'
  valid_range valid_tenv_rec
  valid_tenv_extension_and_type valid_scheme valid_schemes
  valid_env ranging rangings valid_instance valid_env
  valid_store_type value typing
  valid_tenv_extension_and_typing typing_scheme typing_schemes
  red. 

Hint Unfold type_environment valid_tenv_extension valid_tenv.
