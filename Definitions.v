(************************************************
 *          Row Subtyping - Definitions         *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import List LibLN.
Implicit Types x : var.
Implicit Types X : var.

(* *************************************************************** *)
(** ** Description of types *)

(* Finite and co-finite sets of constructors (nats) *)
Inductive constructors : Type :=
  | cons_finite : fset nat -> constructors
  | cons_cofinite : fset nat -> constructors.

Definition cons_universe :=
  cons_cofinite \{}.

Definition cons_disjoint cs1 cs2 :=
  match cs1, cs2 with
  | cons_finite f1, cons_finite f2 => disjoint f1 f2
  | cons_finite f1, cons_cofinite f2 => subset f1 f2
  | cons_cofinite f1, cons_finite f2 => subset f2 f1
  | cons_cofinite f1, cons_cofinite f2 => False
  end.

Definition cons_union cs1 cs2 := 
  match cs1, cs2 with
  | cons_finite f1, cons_finite f2 => cons_finite (f1 \u f2)
  | cons_finite f1, cons_cofinite f2 => cons_cofinite (f2 \- f1)
  | cons_cofinite f1, cons_finite f2 => cons_cofinite (f1 \- f2)
  | cons_cofinite f1, cons_cofinite f2 => cons_cofinite (f1 \n f2)
  end.

Definition cons_inter cs1 cs2 := 
  match cs1, cs2 with
  | cons_finite f1, cons_finite f2 => cons_finite (f1 \n f2)
  | cons_finite f1, cons_cofinite f2 => cons_finite (f1 \- f2)
  | cons_cofinite f1, cons_finite f2 => cons_finite (f2 \- f1)
  | cons_cofinite f1, cons_cofinite f2 => cons_cofinite (f1 \u f2)
  end.

Definition cons_subset cs1 cs2 :=
  match cs1, cs2 with
  | cons_finite f1, cons_finite f2 => subset f1 f2
  | cons_finite f1, cons_cofinite f2 => disjoint f1 f2
  | cons_cofinite f1, cons_finite f2 => False
  | cons_cofinite f1, cons_cofinite f2 => subset f2 f1
  end.

Definition cons_diff cs1 cs2 := 
  match cs1, cs2 with
  | cons_finite f1, cons_finite f2 => cons_finite (f1 \- f2)
  | cons_finite f1, cons_cofinite f2 => cons_finite (f1 \n f2)
  | cons_cofinite f1, cons_finite f2 => cons_cofinite (f1 \u f2)
  | cons_cofinite f1, cons_cofinite f2 => cons_finite (f2 \- f1)
  end.

Definition cons_non_empty cs :=
  match cs with
  | cons_finite f => exists c, c \in f
  | cons_cofinite _ => True
  end.

(* Kinds *)
Inductive knd : Type :=
  | knd_type : knd
  | knd_row : constructors -> knd.

(** Representation of pre-types *)

Inductive typ : Type :=
  | typ_bvar : nat -> typ
  | typ_fvar : var -> typ
  | typ_constructor : nat -> typ -> typ
  | typ_or : typ -> typ -> typ
  | typ_variant : typ -> typ -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_top : constructors -> typ
  | typ_bot : constructors -> typ
  | typ_meet : typ -> typ -> typ
  | typ_join : typ -> typ -> typ.

(** Types are inhabited, giving us a default value. *)

Definition typ_def := typ_bvar 0.

Definition typ_nil := typ_bot (cons_finite \{}).

Definition typ_row cs T R :=
  fold_right
    (fun c acc => typ_or (typ_constructor c T) acc)
    R cs.

(** Type schemes. *)

Record sch : Type := Sch { 
  sch_kinds : list knd ;
  sch_type  : typ }.

Definition sch_arity M := length (sch_kinds M).

(** Opening body of type schemes. *)

Fixpoint typ_open (T : typ) (Vs : list typ) {struct T} : typ :=
  match T with
  | typ_bvar i => nth i Vs typ_def
  | typ_fvar x => typ_fvar x 
  | typ_constructor c T => typ_constructor c (typ_open T Vs)
  | typ_or T1 T2 => typ_or (typ_open T1 Vs) (typ_open T2 Vs)
  | typ_variant T1 T2 => typ_variant (typ_open T1 Vs) (typ_open T2 Vs)
  | typ_arrow T1 T2 => typ_arrow (typ_open T1 Vs) (typ_open T2 Vs)
  | typ_top cs => typ_top cs
  | typ_bot cs => typ_bot cs
  | typ_meet T1 T2 => typ_meet (typ_open T1 Vs) (typ_open T2 Vs)
  | typ_join T1 T2 => typ_join (typ_open T1 Vs) (typ_open T2 Vs)
  end.

(** Opening body of type schemes with variables *)

Definition typ_fvars := 
  List.map typ_fvar.

Definition typ_open_vars T Xs := 
  typ_open T (typ_fvars Xs).

(** Instanciation of a type scheme *)

Definition sch_open M := 
  typ_open (sch_type M).

Definition sch_open_vars M := 
  typ_open_vars (sch_type M).

Notation "M ^^ Vs" := (sch_open M Vs) 
  (at level 67, only parsing) : typ_scope.
Notation "M ^ Xs" := 
  (sch_open_vars M Xs) (only parsing) : typ_scope.

Bind Scope typ_scope with typ.
Open Scope typ_scope.

(** Well-formed kinds *)
Inductive kind : knd -> Prop :=
  | kind_type : kind knd_type
  | kind_row : forall cs,
      cons_non_empty cs -> kind (knd_row cs).

Definition kinds n (L : list knd) :=
  n = length L /\ Forall kind L.

(** Locally closed types *)

Inductive type : typ -> Prop :=
  | type_fvar : forall X, 
      type (typ_fvar X)
  | type_constructor : forall c T,
      type T ->
      type (typ_constructor c T)
  | type_or : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_or T1 T2)
  | type_variant : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_variant T1 T2)
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

(** Body of a scheme *)

Definition type_body n T :=
  exists L, forall Xs,
  fresh L n Xs ->
  type (typ_open_vars T Xs).

(** Definition of a well-formed scheme *)

Definition scheme M :=
  type_body (sch_arity M) (sch_type M)
  /\ kinds (sch_arity M) (sch_kinds M).

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
  | trm_match : trm -> list nat -> trm -> trm -> trm
  | trm_destruct : trm -> list nat -> trm -> trm
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
  | trm_match t1 cs t2 t3 =>
      trm_match (trm_open_rec k u t1) cs
                (trm_open_rec (S k) u t2)
                (trm_open_rec (S k) u t3)
  | trm_destruct t1 cs t2 =>
      trm_destruct (trm_open_rec k u t1) cs
                   (trm_open_rec (S k) u t2)
  | trm_absurd t1 => trm_absurd (trm_open_rec k u t1)
  end.

Definition trm_open t u := trm_open_rec 0 u t.

Notation "{ k ~> u } t" := (trm_open_rec k u t) (at level 67).
Notation "t ^^ u" := (trm_open t u) (at level 67).
Notation "t ^ x" := (trm_open t (trm_fvar x)).

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
  | term_match : forall L t1 cs t2 t3,
      term t1 ->
      (forall x, x \notin L -> term (t2 ^ x)) ->
      (forall x, x \notin L -> term (t3 ^ x)) ->
      term (trm_match t1 cs t2 t3)
  | term_destruct : forall L t1 cs t2,
      term t1 ->
      (forall x, x \notin L -> term (t2 ^ x)) ->
      term (trm_destruct t1 cs t2)
  | term_absurd : forall t,
      term t ->
      term (trm_absurd t).


(** Definition of the body of an abstraction *)

Definition term_body t :=
  exists L, forall x, x \notin L -> term (t ^ x).

(* ************************************************************* *)
(** ** Description of typing environments *)

(** A binding is either mapping type or term variables. 
 [X ~:: T] is a kinding asumption and [x ~: T] is
 a typing assumption *)

Inductive bind : Type :=
  | bind_knd : knd -> bind
  | bind_typ : sch -> bind.

Definition bind_knds Xs Ks :=
  map bind_knd (Xs ~* Ks).

Notation "X ~:: K" := (X ~ bind_knd K)
  (at level 23, left associativity) : env_scope.
Notation "x ~: T" := (x ~ bind_typ T)
  (at level 23, left associativity) : env_scope.
Notation "Xs ~::* Ks" := (map bind_knd (Xs ~* Ks))
  (at level 23, left associativity) : env_scope.

(** Pre-environment is an associative list of bindings. *)

Definition env := LibEnv.env bind.

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
(** ** Description of typing *)

(** The kinding relation *)

Inductive kinding : env -> typ -> knd -> Prop :=
  | kinding_var : forall K E X,
      environment E ->
      binds X (bind_knd K) E ->
      kinding E (typ_fvar X) K
  | kinding_constructor : forall E c T,
      kinding E T knd_type ->
      kinding E (typ_constructor c T)
              (knd_row (cons_finite \{c}))
  | kinding_or : forall E cs1 T1 cs2 T2,
      cons_disjoint cs1 cs2 ->
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs2) ->
      kinding E (typ_or T1 T2) (knd_row (cons_union cs1 cs2))
  | kinding_variant : forall E T1 T2,
      kinding E T1 (knd_row cons_universe) ->
      kinding E T2 (knd_row cons_universe) ->
      kinding E (typ_variant T1 T2) knd_type
  | kinding_arrow : forall E T1 T2,
      kinding E T1 knd_type -> 
      kinding E T2 knd_type -> 
      kinding E (typ_arrow T1 T2) knd_type
  | kinding_top : forall E cs,
      cons_non_empty cs ->
      environment E ->
      kinding E (typ_top cs) (knd_row cs)
  | kinding_bot : forall E cs,
      cons_non_empty cs ->
      environment E ->
      kinding E (typ_bot cs) (knd_row cs)
  | kinding_meet : forall E cs T1 T2,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      kinding E (typ_meet T1 T2) (knd_row cs)
  | kinding_join : forall E cs T1 T2,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      kinding E (typ_join T1 T2) (knd_row cs).

Inductive kindings : env -> nat -> list typ -> list knd -> Prop :=
  | kindings_nil : forall E,
      environment E ->
      kindings E 0 nil nil
  | kindings_cons : forall n E T K Ts Ks,
      kinding E T K ->
      kindings E n Ts Ks ->
      kindings E (S n) (T :: Ts) (K :: Ks).

Definition kinding_body E n Ks T :=
  exists L, forall Xs, 
  fresh L n Xs ->
  kinds n Ks /\
  kinding (E & Xs ~::* Ks) (typ_open_vars T Xs) knd_type.

Definition kinding_scheme E M :=
  kinding_body E (sch_arity M) (sch_kinds M) (sch_type M).

(** A environment E is well-kinded if it contains no duplicate bindings
  and if each type in it is well-kinded with respect to the environment
  it is pushed on to. *)

Inductive kinding_env : env -> Prop :=
  | kinding_env_empty :
      kinding_env empty
  | kinding_env_kind : forall E X K,
      kinding_env E ->
      kind K ->
      X # E ->
      kinding_env (E & X ~:: K)
  | kinding_env_typ : forall E x M,
      kinding_env E ->
      kinding_scheme E M ->
      x # E ->
      kinding_env (E & x ~: M).

(* ************************************************************* *)
(** ** Description of typing *)

(** Equality relation on types *)

Inductive type_equal : env -> typ -> typ -> knd -> Prop :=
  | type_equal_var : forall E x K,
      environment E ->
      binds x (bind_knd K) E ->
      type_equal E (typ_fvar x) (typ_fvar x) K
  | type_equal_constructor : forall E c T T',
      type_equal E T T' knd_type ->
      type_equal E (typ_constructor c T) (typ_constructor c T')
                 (knd_row (cons_finite \{c}))
  | type_equal_or : forall E cs1 T1 T1' cs2 T2 T2',
      cons_disjoint cs1 cs2 ->
      type_equal E T1 T1' (knd_row cs1) ->
      type_equal E T2 T2' (knd_row cs2) ->
      type_equal E (typ_or T1 T2) (typ_or T1' T2')
                 (knd_row (cons_union cs1 cs2))
  | type_equal_variant : forall E T1 T1' T2 T2',
      type_equal E T1 T1' (knd_row cons_universe) ->
      type_equal E T2 T2' (knd_row cons_universe) ->
      type_equal E (typ_variant T1 T2) (typ_variant T1' T2') knd_type
  | type_equal_arrow : forall E T1 T1' T2 T2',
      type_equal E T1 T1' knd_type ->
      type_equal E T2 T2' knd_type ->
      type_equal E (typ_arrow T1 T2) (typ_arrow T1' T2') knd_type
  | type_equal_top : forall E cs,
      environment E ->
      cons_non_empty cs ->
      type_equal E (typ_top cs) (typ_top cs) (knd_row cs)
  | type_equal_bot : forall E cs,
      environment E ->
      cons_non_empty cs ->
      type_equal E (typ_bot cs) (typ_bot cs) (knd_row cs)
  | type_equal_meet : forall E cs T1 T1' T2 T2',
      type_equal E T1 T1' (knd_row cs) ->
      type_equal E T2 T2' (knd_row cs) -> 
      type_equal E (typ_meet T1 T2) (typ_meet T1' T2') (knd_row cs)
  | type_equal_join : forall E cs T1 T1' T2 T2',
      type_equal E T1 T1' (knd_row cs) ->
      type_equal E T2 T2' (knd_row cs) ->
      type_equal E (typ_join T1 T2) (typ_join T1' T2') (knd_row cs)
  | type_equal_trans : forall E T1 T2 T3 K,
      type_equal E T1 T2 K ->
      type_equal E T2 T3 K ->
      type_equal E T1 T3 K
  | type_equal_or_commutative : forall E cs1 T1 cs2 T2,
      cons_disjoint cs1 cs2 ->
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs2) ->
      type_equal E (typ_or T1 T2) (typ_or T2 T1)
                 (knd_row (cons_union cs1 cs2))
  | type_equal_or_associative_l : forall E cs1 T1 cs2 T2 cs3 T3,
      cons_disjoint cs1 cs2 ->
      cons_disjoint cs2 cs3 ->
      cons_disjoint cs1 cs3 ->
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs2) ->
      kinding E T3 (knd_row cs3) ->
      type_equal E (typ_or T1 (typ_or T2 T3))
                 (typ_or (typ_or T1 T2) T3)
                 (knd_row (cons_union cs1 (cons_union cs2 cs3)))
  | type_equal_or_associative_r : forall E cs1 T1 cs2 T2 cs3 T3,
      cons_disjoint cs1 cs2 ->
      cons_disjoint cs2 cs3 ->
      cons_disjoint cs1 cs3 ->
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs2) ->
      kinding E T3 (knd_row cs3) ->
      type_equal E (typ_or (typ_or T1 T2) T3)
                 (typ_or T1 (typ_or T2 T3))
                 (knd_row (cons_union cs1 (cons_union cs2 cs3)))
  | type_equal_or_bot_l : forall E cs1 cs2,
      environment E ->
      cons_disjoint cs1 cs2 ->
      cons_non_empty cs1 ->
      cons_non_empty cs2 ->
      type_equal E (typ_or (typ_bot cs1) (typ_bot cs2))
                 (typ_bot (cons_union cs1 cs2))
                 (knd_row (cons_union cs1 cs2))
  | type_equal_or_bot_r : forall E cs1 cs2,
      environment E ->
      cons_disjoint cs1 cs2 ->
      cons_non_empty cs1 ->
      cons_non_empty cs2 ->
      type_equal E (typ_bot (cons_union cs1 cs2))
                 (typ_or (typ_bot cs1) (typ_bot cs2))
                 (knd_row (cons_union cs1 cs2))
  | type_equal_or_top_l : forall E cs1 cs2,
      environment E ->
      cons_disjoint cs1 cs2 ->
      cons_non_empty cs1 ->
      cons_non_empty cs2 ->
      type_equal E (typ_or (typ_top cs1) (typ_top cs2))
                 (typ_top (cons_union cs1 cs2))
                 (knd_row (cons_union cs1 cs2))
  | type_equal_or_top_r : forall E cs1 cs2,
      environment E ->
      cons_disjoint cs1 cs2 ->
      cons_non_empty cs1 ->
      cons_non_empty cs2 ->
      type_equal E (typ_top (cons_union cs1 cs2))
                 (typ_or (typ_top cs1) (typ_top cs2))
                 (knd_row (cons_union cs1 cs2))
  | type_equal_or_meet_distribution_l : forall E cs1 T1 cs2 T2 T3 T4,
      cons_disjoint cs1 cs2 ->
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs2) ->
      kinding E T3 (knd_row cs1) ->
      kinding E T4 (knd_row cs2) ->
      type_equal E (typ_or (typ_meet T1 T3) (typ_meet T2 T4))
                 (typ_meet (typ_or T1 T2) (typ_or T3 T4))
                 (knd_row (cons_union cs1 cs2))
  | type_equal_or_meet_distribution_r : forall E cs1 T1 cs2 T2 T3 T4,
      cons_disjoint cs1 cs2 ->
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs2) ->
      kinding E T3 (knd_row cs1) ->
      kinding E T4 (knd_row cs2) ->
      type_equal E (typ_meet (typ_or T1 T2) (typ_or T3 T4))
                 (typ_or (typ_meet T1 T3) (typ_meet T2 T4))
                 (knd_row (cons_union cs1 cs2))
  | type_equal_or_join_distribution_l : forall E cs1 T1 cs2 T2 T3 T4,
      cons_disjoint cs1 cs2 ->
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs2) ->
      kinding E T3 (knd_row cs1) ->
      kinding E T4 (knd_row cs2) ->
      type_equal E (typ_or (typ_join T1 T3) (typ_join T2 T4))
                 (typ_join (typ_or T1 T2) (typ_or T3 T4))
                 (knd_row (cons_union cs1 cs2))
  | type_equal_or_join_distribution_r : forall E cs1 T1 cs2 T2 T3 T4,
      cons_disjoint cs1 cs2 ->
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs2) ->
      kinding E T3 (knd_row cs1) ->
      kinding E T4 (knd_row cs2) ->
      type_equal E (typ_join (typ_or T1 T2) (typ_or T3 T4))
                 (typ_or (typ_join T1 T3) (typ_join T2 T4))
                 (knd_row (cons_union cs1 cs2))
  | type_equal_meet_commutative : forall E cs T1 T2,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      type_equal E (typ_meet T1 T2) (typ_meet T2 T1) (knd_row cs)
  | type_equal_meet_associative_l : forall E cs T1 T2 T3,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      kinding E T3 (knd_row cs) ->
      type_equal E (typ_meet T1 (typ_meet T2 T3))
                 (typ_meet (typ_meet T1 T2) T3) (knd_row cs)
  | type_equal_meet_associative_r : forall E cs T1 T2 T3,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      kinding E T3 (knd_row cs) ->
      type_equal E (typ_meet (typ_meet T1 T2) T3)
                 (typ_meet T1 (typ_meet T2 T3)) (knd_row cs)
  | type_equal_meet_identity_l : forall E cs T,
      kinding E T (knd_row cs) ->
      type_equal E (typ_meet T (typ_top cs)) T (knd_row cs)
  | type_equal_meet_identity_r : forall E cs T,
      kinding E T (knd_row cs) ->
      type_equal E T (typ_meet T (typ_top cs)) (knd_row cs)
  | type_equal_meet_absorption_l : forall E cs T1 T2,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      type_equal E (typ_meet T1 (typ_join T1 T2)) T1 (knd_row cs)
  | type_equal_meet_absorption_r : forall E cs T1 T2,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      type_equal E T1 (typ_meet T1 (typ_join T1 T2)) (knd_row cs)
  | type_equal_meet_distribution_l : forall E cs T1 T2 T3,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      kinding E T3 (knd_row cs) ->
      type_equal E (typ_meet (typ_join T1 T2) (typ_join T1 T3))
                 (typ_join T1 (typ_meet T2 T3)) (knd_row cs)
  | type_equal_meet_distribution_r : forall E cs T1 T2 T3,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      kinding E T3 (knd_row cs) ->
      type_equal E (typ_join T1 (typ_meet T2 T3))
                 (typ_meet (typ_join T1 T2) (typ_join T1 T3))
                 (knd_row cs)
  | type_equal_join_commutative : forall E cs T1 T2,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      type_equal E (typ_join T1 T2) (typ_join T2 T1) (knd_row cs)
  | type_equal_join_associative_l : forall E cs T1 T2 T3,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      kinding E T3 (knd_row cs) ->
      type_equal E (typ_join T1 (typ_join T2 T3))
                 (typ_join (typ_join T1 T2) T3) (knd_row cs)
  | type_equal_join_associative_r : forall E cs T1 T2 T3,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      kinding E T3 (knd_row cs) ->
      type_equal E (typ_join (typ_join T1 T2) T3)
                 (typ_join T1 (typ_join T2 T3)) (knd_row cs)
  | type_equal_join_identity_l : forall E cs T,
      kinding E T (knd_row cs) ->
      type_equal E (typ_join T (typ_bot cs)) T (knd_row cs)
  | type_equal_join_identity_r : forall E cs T,
      kinding E T (knd_row cs) ->
      type_equal E T (typ_join T (typ_bot cs)) (knd_row cs)
  | type_equal_join_absorption_l : forall E cs T1 T2,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      type_equal E (typ_join T1 (typ_meet T1 T2)) T1 (knd_row cs)
  | type_equal_join_absorption_r : forall E cs T1 T2,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      type_equal E T1 (typ_join T1 (typ_meet T1 T2)) (knd_row cs)
  | type_equal_join_distribution_l : forall E cs T1 T2 T3,
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
      kinding E T3 (knd_row cs) ->
      type_equal E (typ_join T1 (typ_meet T2 T3))
                 (typ_meet (typ_join T1 T2) (typ_join T1 T3))
                 (knd_row cs)
  | type_equal_join_distribution : forall E cs T1 T2 T3,
      kinding E T1 (knd_row cs) -> 
      kinding E T2 (knd_row cs) ->
      kinding E T3 (knd_row cs) ->
      type_equal E (typ_meet (typ_join T1 T2) (typ_join T1 T3))
                 (typ_join T1 (typ_meet T2 T3)) (knd_row cs).


Definition subtype E T1 T2 :=
  type_equal E T1 (typ_meet T1 T2) (knd_row cons_universe).

Notation "E ||= T1 -<: T2" := (subtype E T1 T2) (at level 60).

Inductive typing : env -> trm -> typ -> Prop :=
  | typing_var : forall E x M Us, 
      kinding_env E -> 
      binds x (bind_typ M) E -> 
      kindings E (sch_arity M) Us (sch_kinds M) ->
      typing E (trm_fvar x) (M ^^ Us)
  | typing_abs : forall L E T1 T2 t1, 
      (forall x, x \notin L -> 
        typing (E & x ~ bind_typ (Sch nil T1)) (t1 ^ x) T2) -> 
      kinding E T1 knd_type ->
      typing E (trm_abs t1) (typ_arrow T1 T2)
  | typing_app : forall E S T t1 t2, 
      typing E t1 (typ_arrow S T) ->
      typing E t2 S ->   
      typing E (trm_app t1 t2) T
  | typing_let : forall M L E T2 t1 t2, 
      (forall Xs, fresh L (sch_arity M) Xs ->
         typing
           (E & Xs ~::* sch_kinds M)
           t1 (M ^ Xs)) ->
      (forall x, x \notin L -> typing (E & x ~ (bind_typ M)) (t2 ^ x) T2) -> 
      typing E (trm_let t1 t2) T2
  | typing_constructor : forall c E T1 T2 T3 t,
      typing E t T1 ->
      E ||= (typ_or (typ_constructor c T1)
                   (typ_bot (cons_cofinite \{c})))
           -<: T2 ->
      (E ||= T2 -<: T3) ->
      typing E (trm_constructor c t) (typ_variant T3 T2)
  | typing_match : forall cs L E T1 T2 T3 T4 T5
                          T6 T7 T8 T9 T10 t1 t2 t3,
      typing E t1 (typ_variant T1 T2) ->
      (forall x, x \notin L ->
         typing (E & x ~: (Sch nil (typ_variant T3 T4)))
                (t2 ^ x) T5) ->
      (forall y, y \notin L -> 
         typing (E & y ~: (Sch nil (typ_variant T6 T7)))
                (t3 ^ y) T5) ->
      kinding E T10 knd_type ->
      E ||= T1 -<: (typ_or T8 T9) ->
      E ||= (typ_or T8
                   (typ_bot (cons_cofinite (from_list cs))))
           -<: (typ_row cs T10
                       (typ_bot (cons_cofinite (from_list cs)))) ->
      E ||= (typ_or T8 (typ_bot (cons_cofinite (from_list cs))))
           -<: T4 ->
      E ||= (typ_or (typ_bot (cons_finite (from_list cs))) T9)
           -<: T7 ->
      E ||= T2 -<: T1 ->
      E ||= T4 -<: T3 ->
      E ||= T7 -<: T6 ->
      typing E (trm_match t1 cs t2 t3) T5
  | typing_destruct : forall cs L E T1 T2 T3 T4 t1 t2,
      typing E t1 (typ_variant T1 T2) ->
      (forall x, x \notin L ->
         typing (E & x ~: (Sch nil T3))
                (t2 ^ x) T4) ->
      kinding E T3 knd_type ->
      E ||= T1 -<: (typ_row cs T3
                    (typ_bot (cons_cofinite (from_list cs)))) ->
      E ||= T2 -<: T1 ->
      typing E (trm_destruct t1 cs t2) T4
  | typing_absurd : forall E T1 T2 T3 t1,
      kinding E T3 knd_type ->
      typing E t1 (typ_variant T1 T2) ->
      E ||= T1 -<: (typ_bot cons_universe) ->
      E ||= T2 -<: T1 ->
      typing E (trm_absurd t1) T3.

Notation "E |= t -: T" := (typing E t T) (at level 69).

Definition typing_scheme E t M :=
  kinds (sch_arity M) (sch_kinds M) /\
  exists L, forall Xs,
    fresh L (sch_arity M) Xs ->
    (E & Xs ~::* sch_kinds M) |= t -: (M ^ Xs).

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
  | red_match_2 : forall c cs t1 t2 t3,
      In c cs ->
      value (trm_constructor c t1) ->
      term_body t2 ->
      term_body t3 ->
      red (trm_match (trm_constructor c t1) cs t2 t3)
          (t2 ^^ (trm_constructor c t1))
  | red_match_3 : forall c cs t1 t2 t3,
      ~ In c cs ->
      value (trm_constructor c t1) ->
      term_body t2 ->
      term_body t3 ->
      red (trm_match (trm_constructor c t1) cs t2 t3)
          (t3 ^^ (trm_constructor c t1))
  | red_destruct_1 : forall c t1 t1' t2,
      term_body t2 ->
      red t1 t1' ->
      red (trm_destruct t1 c t2) (trm_destruct t1' c t2)
  | red_destruct_2 : forall c cs t1 t2,
      In c cs ->
      value (trm_constructor c t1) ->
      term_body t2 ->
      red (trm_destruct (trm_constructor c t1) cs t2)
          (t2 ^^ t1)
  | red_absurd : forall t1 t1',
      red t1 t1' ->
      red (trm_absurd t1) (trm_absurd t1').
                  
Notation "t --> t'" := (red t t') (at level 68).

(* ************************************************************** *)
(** ** Description of the results *)

(** Goal is to prove preservation and progress *)

Definition preservation := forall E t t' T,
  E |= t -: T ->
  t --> t' ->
  E |= t' -: T.


Definition progress := forall t T, 
  empty |= t -: T ->
     value t 
  \/ exists t', t --> t'.
