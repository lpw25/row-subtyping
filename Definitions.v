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
  | typ_row : typ -> typ
  | typ_variant : typ -> typ
  | typ_arrow : typ -> typ -> typ
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

Inductive sch : Type :=
  | sch_empty : typ -> sch
  | sch_bind : knd -> sch -> sch.

Fixpoint sch_arity (M : sch) : nat :=
  match M with
  | sch_empty _ => 0
  | sch_bind _ M => S (sch_arity M)
  end.

Fixpoint sch_body (M : sch) : typ :=
  match M with
  | sch_empty T => T
  | sch_bind _ M => sch_body M
  end.

(** Opening a type. *)

Fixpoint typ_open_k (k : nat) (U : typ) (T : typ) {struct T}: typ :=
  match T with
  | typ_bvar i => If k = i then U else (typ_bvar i)
  | typ_fvar x => typ_fvar x 
  | typ_constructor c T => typ_constructor c (typ_open_k k U T)
  | typ_or cs1 T1 cs2 T2 =>
    typ_or cs1 (typ_open_k k U T1) cs2 (typ_open_k k U T2)
  | typ_proj cs1 T cs2 => typ_proj cs1 (typ_open_k k U T) cs2
  | typ_row T => typ_row (typ_open_k k U T)
  | typ_variant T => typ_variant (typ_open_k k U T)
  | typ_arrow T1 T2 =>
    typ_arrow (typ_open_k k U T1) (typ_open_k k U T2)
  | typ_top cs => typ_top cs
  | typ_bot cs => typ_bot cs
  | typ_meet T1 T2 =>
    typ_meet (typ_open_k k U T1) (typ_open_k k U T2)
  | typ_join T1 T2 =>
    typ_join (typ_open_k k U T1) (typ_open_k k U T2)
  end.

Definition typ_open T U := typ_open_k 0 U T.

Definition typ_open_var T X := typ_open T (typ_fvar X).

(** Opening a kind. *)

Definition knd_open_k (k : nat) (U : typ) (K : knd) : knd :=
  match K with
  | knd_type => knd_type
  | knd_row cs => knd_row cs
  | knd_range T1 T2 =>
    knd_range (typ_open_k k U T1) (typ_open_k k U T2)
  end.

Definition knd_open K U := knd_open_k 0 U K.

Definition knd_open_var K X := knd_open K (typ_fvar X).

(** Instanciation of a type scheme *)

Fixpoint sch_open_k (k : nat) (U : typ) (M : sch) {struct M}: sch :=
  match M with
  | sch_empty T => sch_empty (typ_open_k k U T)
  | sch_bind K M => sch_bind (knd_open_k k U K) (sch_open_k (S k) U M)
  end.

Definition sch_open M U := sch_open_k 0 U M.

Definition sch_open_var M X := sch_open M (typ_fvar X).

Notation "M ^^ V" := (sch_open M V) 
  (at level 67, only parsing) : sch_scope.

Notation "M ^ X" := (sch_open_var M X) (only parsing) : sch_scope.

Bind Scope sch_scope with sch.
Open Scope sch_scope.

Fixpoint instance (M : sch) (Us : list typ)
         {struct Us} : typ :=
  match Us with
  | nil => sch_body M
  | U :: Us =>
    match M with
    | sch_empty T => T
    | sch_bind K M => instance (M ^^ U) Us
      end
  end.

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
  | type_row : forall T,
      type T ->
      type (typ_row T)
  | type_variant : forall T,
      type T ->
      type (typ_variant T)
  | type_arrow : forall T1 T2,
      type T1 -> 
      type T2 -> 
      type (typ_arrow T1 T2)
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

(** List of n locally closed types *)

Definition types n (L : list typ) :=
  n = length L /\ Forall type L.

(** Well-formed kinds *)

Inductive kind : knd -> Prop :=
  | kind_type : kind knd_type
  | kind_row : forall cs,
      CSet.Nonempty cs -> kind (knd_row cs)
  | kind_range : forall T1 T2,
      type T1 ->
      type T2 ->
      kind (knd_range T1 T2).

(** Definition of a well-formed scheme *)

Inductive scheme_vars : sch -> list var -> Prop :=
  | scheme_vars_empty : forall T,
      type T ->
      scheme_vars (sch_empty T) nil
  | scheme_vars_bind : forall X Xs K M,
      kind K ->
      scheme_vars (M ^ X) Xs ->
      scheme_vars (sch_bind K M) (X :: Xs).

Definition scheme M :=
  exists L, forall Xs,
      fresh L (sch_arity M) Xs ->
      scheme_vars M Xs.

(* ************************************************************** *)
(** ** Description of terms *)

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
  | trm_absurd : trm -> trm.

Fixpoint trm_open_rec (k : nat) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i => If k = i then u else (trm_bvar i)
  | trm_fvar x => trm_fvar x 
  | trm_abs t1 => trm_abs (trm_open_rec (S k) u t1) 
  | trm_let t1 t2 =>
      trm_let (trm_open_rec k u t1) (trm_open_rec (S k) u t2) 
  | trm_app t1 t2 =>
      trm_app (trm_open_rec k u t1) (trm_open_rec k u t2)
  | trm_constructor c t =>
      trm_constructor c (trm_open_rec k u t)
  | trm_match t1 c t2 t3 =>
      trm_match (trm_open_rec k u t1) c
                (trm_open_rec (S k) u t2)
                (trm_open_rec (S k) u t3)
  | trm_destruct t1 c t2 =>
      trm_destruct (trm_open_rec k u t1) c
                   (trm_open_rec (S k) u t2)
  | trm_absurd t1 => trm_absurd (trm_open_rec k u t1)
  end.

Definition trm_open t u := trm_open_rec 0 u t.

Notation "{ k ~> u } t" := (trm_open_rec k u t)
  (at level 67) : trm_scope.

Notation "t ^^ u" := (trm_open t u) (at level 67) : trm_scope.
Notation "t ^ x" := (trm_open t (trm_fvar x)) : trm_scope.

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
      term (trm_absurd t).


(** Definition of the body of an abstraction *)

Definition term_body t :=
  exists L, forall x, x \notin L -> term (t ^ x).

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

Function bind_knds (Xs : list var) (M : sch) {struct Xs} : env :=
  match Xs with
  | nil => empty
  | X :: Xs =>
    match M with
    | sch_empty _ => empty
    | sch_bind K M =>
      (X ~ bind_knd K) & bind_knds Xs (M ^ X)
    end
  end.

Notation "X ~:: K" := (X ~ bind_knd K)
  (at level 23, left associativity) : env_scope.
Notation "x ~: T" := (x ~ bind_typ T)
  (at level 23, left associativity) : env_scope.
Notation "Xs ~::* M" := (bind_knds Xs M)
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

(* ************************************************************* *)
(** ** Description of kinding and equality *)

(* Validity of kinds *)

Inductive valid_kind : env -> knd -> Prop :=
  | valid_kind_type : forall E,
      valid_env E ->
      valid_kind E knd_type
  | valid_kind_row :  forall E cs,
      valid_env E ->
      CSet.Nonempty cs ->
      valid_kind E (knd_row cs)
  | valid_kind_range : forall E T1 T2,
      subtype E T2 T1 CSet.universe ->
      valid_kind E (knd_range T1 T2)

(** The kinding judgement *)

with kinding : env -> typ -> knd -> Prop :=
  | kinding_var : forall E X K,
      valid_env E ->
      binds X (bind_knd K) E ->
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
  | kinding_row : forall E T,
      kinding E T (knd_row CSet.universe) ->
      kinding E (typ_row T) (knd_range T T)
  | kinding_variant : forall E T,
      kinding E T
        (knd_range (typ_top CSet.universe) (typ_bot CSet.universe)) ->
      kinding E (typ_variant T) knd_type
  | kinding_arrow : forall E T1 T2,
      kinding E T1 knd_type -> 
      kinding E T2 knd_type -> 
      kinding E (typ_arrow T1 T2) knd_type
  | kinding_top : forall E cs,
      valid_env E ->
      CSet.Nonempty cs ->
      kinding E (typ_top cs) (knd_row cs)
  | kinding_bot : forall E cs,
      valid_env E ->
      CSet.Nonempty cs ->
      kinding E (typ_bot cs) (knd_row cs)
  | kinding_meet : forall E T1 T2 cs,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      kinding E (typ_meet T1 T2) (knd_row cs)
  | kinding_join : forall E T1 T2 cs,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      kinding E (typ_join T1 T2) (knd_row cs)
  | kinding_range_subsumption : forall E T T1 T2 T1' T2',
      kinding E T (knd_range T1 T2) ->
      subtype E T1 T1' CSet.universe ->
      subtype E T2' T2 CSet.universe ->
      kinding E T (knd_range T1' T2')

(* Validity of type schemes *)

with valid_scheme_vars : env -> sch -> list var -> Prop :=
  | valid_scheme_vars_empty : forall E T,
      kinding E T knd_type ->
      valid_scheme_vars E (sch_empty T) nil
  | valid_scheme_vars_bind : forall X Xs E K M,
      valid_kind E K ->
      valid_scheme_vars (E & X ~:: K) (M ^ X) Xs ->
      valid_scheme_vars E (sch_bind K M) (X :: Xs)

with valid_scheme : env -> sch -> Prop :=
  | valid_scheme_c : forall E M L,
      (forall Xs, fresh L (sch_arity M) Xs -> valid_scheme_vars E M Xs) ->
      valid_scheme E M

(* Validity of environments *)

with valid_env : env -> Prop :=
  | valid_env_empty :
      valid_env empty
  | valid_env_kind : forall E X K,
      valid_env E ->
      valid_kind E K ->
      X # E ->
      valid_env (E & X ~:: K)
  | valid_env_type : forall E x M,
      valid_env E ->
      valid_scheme E M ->
      x # E ->
      valid_env (E & x ~: M)

(** Core of the equality relation on types *)

with type_equal_core : env -> typ -> typ -> knd -> Prop :=
  | type_equal_core_or_commutative : forall E T1 T2 cs1 cs2 cs12,
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_core E
        (typ_or cs1 T1 cs2 T2) (typ_or cs2 T2 cs1 T1) (knd_row cs12)
  | type_equal_core_or_associative :
      forall E T1 cs1 T2 cs2 T3 cs3 cs12 cs23 cs123,
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
      valid_env E ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_core E
        (typ_or cs1 (typ_bot cs1) cs2 (typ_bot cs2)) (typ_bot cs12)
        (knd_row cs12)
  | type_equal_core_or_top : forall E cs1 cs2 cs12,
      valid_env E ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_core E
        (typ_or cs1 (typ_top cs1) cs2 (typ_top cs2)) (typ_top cs12)
        (knd_row cs12)
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
        (typ_meet (typ_or cs1 T1 cs2 T2) (typ_or cs1 T3 cs2 T4))
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
        (typ_join (typ_or cs1 T1 cs2 T2) (typ_or cs1 T3 cs2 T4))
        (knd_row cs12)
  | type_equal_core_or_proj : forall E T cs1 cs2 cs3 cs23,
      kinding E T (knd_row cs1) ->
      CSet.Disjoint cs2 cs3 ->
      CSet.Subset cs2 cs1 ->
      CSet.Nonempty cs2 ->
      CSet.Subset cs3 cs1 ->
      CSet.Nonempty cs3 ->
      cs23 = CSet.union cs2 cs3 ->
      type_equal_core E
        (typ_or cs2 (typ_proj cs1 T cs2) cs3 (typ_proj cs1 T cs3))
        (typ_proj cs1 T cs23)
        (knd_row cs23)
  | type_equal_core_proj_id : forall E T cs,
      kinding E T (knd_row cs) ->
      type_equal_core E (typ_proj cs T cs) T (knd_row cs)
  | type_equal_core_proj_or_l : forall E T1 T2 cs1 cs1' cs2 cs12,
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      CSet.Subset cs1' cs1 ->
      CSet.Nonempty cs1' ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_core E
        (typ_proj cs12 (typ_or cs1 T1 cs2 T2) cs1')
        (typ_proj cs1 T1 cs1')
        (knd_row cs1')
  | type_equal_core_proj_or_r : forall E T1 T2 cs1 cs2 cs2' cs12,
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      CSet.Subset cs2' cs2 ->
      CSet.Nonempty cs2' ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_core E
        (typ_proj cs12 (typ_or cs1 T1 cs2 T2) cs2')
        (typ_proj cs2 T2 cs2')
        (knd_row cs2')
  | type_equal_core_proj_or_both :
      forall E T1 T2 cs1 cs2 cs1' cs2' cs12 cs12',
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      CSet.Subset cs1' cs1 ->
      CSet.Nonempty cs1' ->
      CSet.Subset cs2' cs2 ->
      CSet.Nonempty cs2' ->
      cs12 = CSet.union cs1 cs2 ->
      cs12' = CSet.union cs1' cs2' ->
      type_equal_core E
        (typ_proj cs12 (typ_or cs1 T1 cs2 T2) cs12')
        (typ_or cs1' (typ_proj cs1 T1 cs1')
                cs2' (typ_proj cs2 T2 cs2'))
        (knd_row cs12')
  | type_equal_core_proj_meet : forall E T1 T2 cs cs',
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      CSet.Subset cs' cs ->
      CSet.Nonempty cs' ->
      type_equal_core E
        (typ_proj cs (typ_meet T1 T2) cs')
        (typ_meet (typ_proj cs T1 cs') (typ_proj cs T2 cs'))
        (knd_row cs')
  | type_equal_core_proj_join : forall E T1 T2 cs cs',
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      CSet.Subset cs' cs ->
      CSet.Nonempty cs' ->
      type_equal_core E
        (typ_proj cs (typ_join T1 T2) cs')
        (typ_join (typ_proj cs T1 cs') (typ_proj cs T2 cs'))
        (knd_row cs')
  | type_equal_core_meet_commutative : forall E T1 T2 cs,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      type_equal_core E (typ_meet T1 T2) (typ_meet T2 T1) (knd_row cs)
  | type_equal_core_meet_associative : forall E T1 T2 T3 cs,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      kinding E T3 (knd_row cs) ->
      type_equal_core E
        (typ_meet T1 (typ_meet T2 T3))
        (typ_meet (typ_meet T1 T2) T3)
        (knd_row cs)
  | type_equal_core_meet_identity : forall E T1 cs,
      kinding E T1 (knd_row cs) ->
      type_equal_core E (typ_meet T1 (typ_top cs)) T1 (knd_row cs)
  | type_equal_core_meet_absorption : forall E T1 T2 cs,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      type_equal_core E (typ_meet T1 (typ_join T1 T2)) T1 (knd_row cs)
  | type_equal_core_meet_distribution : forall E T1 T2 T3 cs,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      kinding E T3 (knd_row cs) ->
      type_equal_core E
        (typ_meet T1 (typ_join T2 T3))
        (typ_join (typ_meet T1 T2) (typ_meet T1 T3))
        (knd_row cs)
  | type_equal_core_join_commutative : forall E T1 T2 cs,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      type_equal_core E (typ_join T1 T2) (typ_join T2 T1) (knd_row cs)
  | type_equal_core_join_associative : forall E T1 T2 T3 cs,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      kinding E T3 (knd_row cs) ->
      type_equal_core E
        (typ_join T1 (typ_join T2 T3))
        (typ_join (typ_join T1 T2) T3)
        (knd_row cs)
  | type_equal_core_join_identity : forall E T1 cs,
      kinding E T1 (knd_row cs) ->
      type_equal_core E (typ_join T1 (typ_bot cs)) T1 (knd_row cs)
  | type_equal_core_join_absorption : forall E T1 T2 cs,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      type_equal_core E (typ_join T1 (typ_meet T1 T2)) T1 (knd_row cs)
  | type_equal_core_join_distribution : forall E T1 T2 T3 cs,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      kinding E T3 (knd_row cs) ->
      type_equal_core E
        (typ_join T1 (typ_meet T2 T3))
        (typ_meet (typ_join T1 T2) (typ_join T1 T3))
        (knd_row cs)

(* Symetric closure of type_equal_core *)

with type_equal_symm : env -> typ -> typ -> knd -> Prop :=
  | type_equal_symm_l : forall E T1 T2 K,
      type_equal_core E T1 T2 K ->
      type_equal_symm E T1 T2 K
  | type_equal_symm_r : forall E T1 T2 K,
      type_equal_core E T1 T2 K ->
      type_equal_symm E T2 T1 K

(* Congruence closure of type_equal_symm *)

with type_equal_cong : env -> typ -> typ -> knd -> Prop :=
  | type_equal_cong_constructor : forall E c T1 T1' cs,
      type_equal_cong E T1 T1' knd_type ->
      cs = CSet.singleton c ->
      type_equal_cong E
        (typ_constructor c T1) (typ_constructor c T1')
        (knd_row cs)
  | type_equal_cong_or_l : forall E T1 T1' T2 cs1 cs2 cs12,
      kinding E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_cong E T1 T1' (knd_row cs1) ->
      type_equal_cong E
        (typ_or cs1 T1 cs2 T2) (typ_or cs1 T1' cs2 T2) (knd_row cs12)
  | type_equal_cong_or_r : forall E T1 T2 T2' cs1 cs2 cs12,
      kinding E T1 (knd_row cs1) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_cong E T2 T2' (knd_row cs2) ->
      type_equal_cong E
        (typ_or cs1 T1 cs2 T2) (typ_or cs1 T1 cs2 T2') (knd_row cs12)
  | type_equal_cong_row : forall E T1 T1',
      type_equal_cong E T1 T1' (knd_row CSet.universe) ->
      type_equal_cong E (typ_row T1) (typ_row T1') (knd_range T1 T1)
  | type_equal_cong_variant : forall E T1 T1',
      type_equal_cong E T1 T1'
        (knd_range (typ_top CSet.universe) (typ_bot CSet.universe)) ->
      type_equal_cong E
        (typ_variant T1) (typ_variant T1') knd_type
  | type_equal_cong_arrow_l : forall E T1 T1' T2,
      kinding E T2 knd_type ->
      type_equal_cong E T1 T1' knd_type ->
      type_equal_cong E (typ_arrow T1 T2) (typ_arrow T1' T2) knd_type
  | type_equal_cong_arrow_r : forall E T1 T2 T2',
      kinding E T1 knd_type ->
      type_equal_cong E T2 T2' knd_type ->
      type_equal_cong E (typ_arrow T1 T2) (typ_arrow T1 T2') knd_type
  | type_equal_cong_meet_l : forall E T1 T1' T2 cs,
      kinding E T2 (knd_row cs) ->
      type_equal_cong E T1 T1' (knd_row cs) ->
      type_equal_cong E
        (typ_meet T1 T2) (typ_meet T1' T2) (knd_row cs)
  | type_equal_cong_meet_r : forall E T1 T2 T2' cs,
      kinding E T1 (knd_row cs) ->
      type_equal_cong E T2 T2' (knd_row cs) -> 
      type_equal_cong E
        (typ_meet T1 T2) (typ_meet T1 T2') (knd_row cs)
  | type_equal_cong_join_l : forall E T1 T1' T2 cs,
      kinding E T2 (knd_row cs) ->
      type_equal_cong E T1 T1' (knd_row cs) ->
      type_equal_cong E
        (typ_join T1 T2) (typ_join T1' T2) (knd_row cs)
  | type_equal_cong_join_r : forall E T1 T2 T2' cs,
      kinding E T1 (knd_row cs) ->
      type_equal_cong E T2 T2' (knd_row cs) ->
      type_equal_cong E
        (typ_join T1 T2) (typ_join T1 T2') (knd_row cs)
  | type_equal_cong_range_subsumption : forall E T1 T2 T3 T4 T3' T4',
      type_equal_cong E T1 T2 (knd_range T3 T4) ->
      subtype E T3 T3' CSet.universe ->
      subtype E T4' T4 CSet.universe ->
      type_equal_cong E T1 T2 (knd_range T3' T4')
  | type_equal_cong_symm : forall E T1 T1' K,
      type_equal_symm E T1 T1' K ->
      type_equal_cong E T1 T1' K

(* Reflexive transitive closure of type_equal_symm *)

with type_equal : env -> typ -> typ -> knd -> Prop :=
  | type_equal_refl : forall E T K,
      kinding E T K ->
      type_equal E T T K
  | type_equal_step : forall E T1 T2 T3 K,
      type_equal_cong E T1 T2 K ->
      type_equal E T2 T3 K ->
      type_equal E T1 T3 K

with subtype : env -> typ -> typ -> cset -> Prop :=
  | subtype_c : forall E T1 T2 cs,
      type_equal E T1 (typ_meet T1 T2) (knd_row cs) ->
      subtype E T1 T2 cs.

Scheme valid_kind_mutind := Induction for valid_kind Sort Prop
  with kinding_mutind := Induction for kinding Sort Prop
  with valid_scheme_vars_mutind :=
         Induction for valid_scheme_vars Sort Prop
  with valid_scheme_mutind := Induction for valid_scheme Sort Prop
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
  from valid_kind_mutind, kinding_mutind, valid_scheme_vars_mutind,
       valid_scheme_mutind, valid_env_mutind, type_equal_core_mutind,
       type_equal_symm_mutind, type_equal_cong_mutind,
       type_equal_mutind, subtype_mutind.

Inductive valid_instance : env -> list typ -> sch -> Prop :=
  | valid_instance_empty : forall E T,
      kinding E T knd_type ->
      valid_instance E nil (sch_empty T)
  | valid_instance_bind : forall E K M T Ts,
      kinding E T K ->
      valid_instance E Ts (M ^^ T) ->
      valid_instance E (T :: Ts) (sch_bind K M).

(* ************************************************************* *)
(** ** Description of typing *)

Inductive typing : env -> trm -> typ -> Prop :=
  | typing_var : forall E x M T Us, 
      valid_env E -> 
      binds x (bind_typ M) E -> 
      valid_instance E Us M ->
      type_equal E T (instance M Us) knd_type ->
      typing E (trm_fvar x) T
  | typing_abs : forall L E T1 T2 t1,
      kinding E T1 knd_type ->
      (forall x, x \notin L -> 
        typing (E & x ~: sch_empty T1) (t1 ^ x) T2) -> 
      typing E (trm_abs t1) (typ_arrow T1 T2)
  | typing_app : forall E S T t1 t2, 
      typing E t1 (typ_arrow S T) ->
      typing E t2 S ->   
      typing E (trm_app t1 t2) T
  | typing_let : forall M L E T2 t1 t2, 
      (forall Xs, fresh L (sch_arity M) Xs ->
         typing
           (E & Xs ~::* M)
           t1 (instance_vars M Xs)) ->
      (forall x, x \notin L -> typing (E & x ~: M) (t2 ^ x) T2) -> 
      typing E (trm_let t1 t2) T2
  | typing_constructor : forall c E T1 T2 T3 t,
      kinding E T1 (knd_range (typ_top CSet.universe) T2) ->
      subtype E
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (typ_constructor c T3)
        (CSet.singleton c) ->
      typing E t T3 ->
      typing E (trm_constructor c t) (typ_variant T1)
  | typing_match : forall c L E T1 T2 T3 T4 T5 T6 T7 T8 t1 t2 t3,
      kinding E T1 (knd_range T2 (typ_bot CSet.universe)) ->
      kinding E T3 (knd_range (typ_top CSet.universe) T4) ->
      kinding E T5 (knd_range (typ_top CSet.universe) T6) ->
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
      typing E t1 (typ_variant T1) ->
      (forall x, x \notin L ->
         typing (E & x ~: (sch_empty (typ_variant T3)))
                (t2 ^ x) T8) ->
      (forall y, y \notin L -> 
         typing (E & y ~: (sch_empty (typ_variant T5)))
                (t3 ^ y) T8) ->
      typing E (trm_match t1 c t2 t3) T8
  | typing_destruct : forall c L E T1 T2 T3 T4 t1 t2,
      kinding E T1 (knd_range T2 (typ_bot CSet.universe)) ->
      subtype E
        (typ_constructor c T3)
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (CSet.singleton c) ->
      typing E t1 (typ_variant T1) ->
      (forall x, x \notin L ->
         typing (E & x ~: (sch_empty T3))
                (t2 ^ x) T4) ->
      typing E (trm_destruct t1 c t2) T4
  | typing_absurd : forall E T1 T2 t1,
      kinding E T1 (knd_range (typ_bot CSet.universe)
                              (typ_bot CSet.universe)) ->
      kinding E T2 knd_type ->
      typing E t1 (typ_variant T1) ->
      typing E (trm_absurd t1) T2.

Definition typing_scheme E t M :=
  valid_scheme E M /\
  exists L, forall Xs,
    fresh L (sch_arity M) Xs ->
    typing (E & Xs ~::* M) t (instance_vars M Xs).

(* ************************************************************* *)
(** ** Description of the semantics *)

(** Grammar of values *)

Inductive value : trm -> Prop :=
  | value_constructor : forall c t,
      value t -> value (trm_constructor c t)
  | value_abs : forall t,
      term (trm_abs t) -> value (trm_abs t).

(** Reduction rules *)

Inductive red : trm -> trm -> Prop :=
  | red_let : forall t1 t2, 
      term (trm_let t1 t2) ->
      value t1 -> 
      red (trm_let t1 t2) (t2 ^^ t1)
  | red_let_1 : forall t1 t1' t2, 
      term_body t2 ->
      red t1 t1' -> 
      red (trm_let t1 t2) (trm_let t1' t2)
  | red_app_1 : forall t1 t1' t2,
      term t2 ->
      red t1 t1' -> 
      red (trm_app t1 t2) (trm_app t1' t2)
  | red_app_2 : forall t1 t2 t2', 
      value t1 ->
      red t2 t2' ->
      red (trm_app t1 t2) (trm_app t1 t2')
  | red_app_3 : forall t1 t2, 
      term_body t1 -> 
      value t2 ->  
      red (trm_app (trm_abs t1) t2) (t1 ^^ t2)
  | red_constructor : forall c t t',
      red t t' ->
      red (trm_constructor c t) (trm_constructor c t')
  | red_match_1 : forall c t1 t1' t2 t3,
      term_body t2 ->
      term_body t3 ->
      red t1 t1' ->
      red (trm_match t1 c t2 t3) (trm_match t1' c t2 t3)
  | red_match_2 : forall c1 c2 t1 t2 t3,
      c1 = c2 ->
      value (trm_constructor c1 t1) ->
      term_body t2 ->
      term_body t3 ->
      red (trm_match (trm_constructor c1 t1) c2 t2 t3)
          (t2 ^^ (trm_constructor c1 t1))
  | red_match_3 : forall c1 c2 t1 t2 t3,
      c1 <> c2 ->
      value (trm_constructor c1 t1) ->
      term_body t2 ->
      term_body t3 ->
      red (trm_match (trm_constructor c1 t1) c2 t2 t3)
          (t3 ^^ (trm_constructor c1 t1))
  | red_destruct_1 : forall c t1 t1' t2,
      term_body t2 ->
      red t1 t1' ->
      red (trm_destruct t1 c t2) (trm_destruct t1' c t2)
  | red_destruct_2 : forall c1 c2 t1 t2,
      c1 = c2 ->
      value (trm_constructor c1 t1) ->
      term_body t2 ->
      red (trm_destruct (trm_constructor c1 t1) c2 t2)
          (t2 ^^ t1)
  | red_absurd : forall t t',
      red t t' ->
      red (trm_absurd t) (trm_absurd t').

(* ************************************************************** *)
(** ** Description of the results *)

(** Goal is to prove preservation and progress *)

Definition preservation := forall E t t' T,
  typing E t T ->
  red t t' ->
  typing E t' T.


Definition progress := forall t T, 
  typing empty t T ->
     value t 
  \/ exists t', red t t'.
