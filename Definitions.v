(************************************************
 *          Row Subtyping - Definitions         *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import Recdef List LibLN Cofinite.
Implicit Types x : var.
Implicit Types X : var.

(* *************************************************************** *)
(** ** Description of types *)

(** Representation of pre-types *)

Inductive typ : Type :=
  | typ_bvar : nat -> typ
  | typ_fvar : var -> typ
  | typ_constructor : nat -> typ -> typ
  | typ_or : typ -> typ -> typ
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

(** Types are inhabited, giving us a default value. *)

Definition typ_def := typ_bvar 0.

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
  | typ_or T1 T2 => typ_or (typ_open_k k U T1) (typ_open_k k U T2)
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

Function instance_rec (M : sch) (Us : list typ) (n : nat)
         {struct n} : typ :=
  match n with
  | 0 => sch_body M
  | S n =>
    match M with
    | sch_empty T => T
    | sch_bind K M =>
      match Us with
      | nil => sch_body M
      | U :: Us => instance_rec (M ^^ U) Us n
      end
    end
  end.

Definition instance M Us :=
  instance_rec M Us (sch_arity M). 

Definition instance_vars M Xs :=
  instance M (typ_fvars Xs).

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

Inductive scheme : sch -> Prop :=
  | scheme_empty : forall T,
      type T ->
      scheme (sch_empty T)
  | scheme_bind : forall L K M,
      kind K ->
      (forall X, X \notin L -> scheme (M ^ X)) ->
      scheme (sch_bind K M).

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

(** Core of the equality relation on types *)

Inductive type_equal_or : typ -> typ -> Prop :=
  | type_equal_or_commutative : forall T1 T2,
      type_equal_or (typ_or T1 T2) (typ_or T2 T1)
  | type_equal_or_associative : forall T1 T2 T3,
      type_equal_or (typ_or T1 (typ_or T2 T3)) (typ_or (typ_or T1 T2) T3)
  | type_equal_or_bot : forall cs cs1 cs2,
      type_equal_or (typ_or (typ_bot cs1) (typ_bot cs2)) (typ_bot cs)
  | type_equal_or_top : forall cs cs1 cs2,
      type_equal_or (typ_or (typ_top cs1) (typ_top cs2)) (typ_top cs)
  | type_equal_or_meet_distribution : forall T1 T2 T3 T4,
      type_equal_or
        (typ_or (typ_meet T1 T3) (typ_meet T2 T4))
        (typ_meet (typ_or T1 T2) (typ_or T3 T4))
  | type_equal_or_join_distribution : forall T1 T2 T3 T4,
      type_equal_or
        (typ_or (typ_join T1 T3) (typ_join T2 T4))
        (typ_join (typ_or T1 T2) (typ_or T3 T4)).

Inductive type_equal_meet : typ -> typ -> Prop :=
  | type_equal_meet_commutative : forall T1 T2,
      type_equal_meet (typ_meet T1 T2) (typ_meet T2 T1)
  | type_equal_meet_associative : forall T1 T2 T3,
      type_equal_meet
        (typ_meet T1 (typ_meet T2 T3))
        (typ_meet (typ_meet T1 T2) T3)
  | type_equal_meet_identity : forall T1 cs,
      type_equal_meet (typ_meet T1 (typ_top cs)) T1
  | type_equal_meet_absorption : forall T1 T2,
      type_equal_meet (typ_meet T1 (typ_join T1 T2)) T1
  | type_equal_meet_distribution : forall T1 T2 T3,
      type_equal_meet
        (typ_meet T1 (typ_join T2 T3))
        (typ_join (typ_meet T1 T2) (typ_meet T1 T3)).

Inductive type_equal_join : typ -> typ -> Prop :=
  | type_equal_join_commutative : forall T1 T2,
      type_equal_join (typ_join T1 T2) (typ_join T2 T1)
  | type_equal_join_associative : forall T1 T2 T3,
      type_equal_join
        (typ_join T1 (typ_join T2 T3))
        (typ_join (typ_join T1 T2) T3)
  | type_equal_join_identity : forall cs T1,
      type_equal_join (typ_join T1 (typ_bot cs)) T1
  | type_equal_join_absorption : forall T1 T2,
      type_equal_join (typ_join T1 (typ_meet T1 T2)) T1
  | type_equal_join_distribution : forall T1 T2 T3,
      type_equal_join
        (typ_join T1 (typ_meet T2 T3))
        (typ_meet (typ_join T1 T2) (typ_join T1 T3)).

Inductive type_equal_core : typ -> typ -> Prop :=
  | type_equal_core_or : forall T1 T2 T3,
      type_equal_or (typ_or T1 T2) T3 ->
      type_equal_core (typ_or T1 T2) T3
  | type_equal_core_meet : forall T1 T2 T3,
      type_equal_meet (typ_meet T1 T2) T3 ->
      type_equal_core (typ_meet T1 T2) T3
  | type_equal_core_join : forall T1 T2 T3,
      type_equal_join (typ_join T1 T2) T3 ->
      type_equal_core (typ_join T1 T2) T3.

Inductive type_equal_cong : typ -> typ -> Prop :=
  | type_equal_cong_core : forall T1 T1',
      type_equal_core T1 T1' ->
      type_equal_cong T1 T1'
  | type_equal_cong_constructor : forall c T1 T1',
      type_equal_cong T1 T1' ->
      type_equal_cong (typ_constructor c T1) (typ_constructor c T1')
  | type_equal_cong_or_l : forall T1 T1' T2,
      type_equal_cong T1 T1' ->
      type_equal_cong (typ_or T1 T2) (typ_or T1' T2)
  | type_equal_cong_or_r : forall T1 T2 T2',
      type_equal_cong T2 T2' ->
      type_equal_cong (typ_or T1 T2) (typ_or T1 T2')
  | type_equal_cong_row : forall T1 T1',
      type_equal_cong T1 T1' ->
      type_equal_cong (typ_row T1) (typ_row T1')
  | type_equal_cong_variant : forall T1 T1',
      type_equal_cong T1 T1' ->
      type_equal_cong (typ_variant T1) (typ_variant T1)
  | type_equal_cong_arrow_l : forall T1 T1' T2,
      type_equal_cong T1 T1' ->
      type_equal_cong (typ_arrow T1 T2) (typ_arrow T1' T2)
  | type_equal_cong_arrow_r : forall T1 T2 T2',
      type_equal_cong T2 T2' ->
      type_equal_cong (typ_arrow T1 T2) (typ_arrow T1 T2')
  | type_equal_cong_meet_l : forall T1 T1' T2,
      type_equal_cong T1 T1' ->
      type_equal_cong (typ_meet T1 T2) (typ_meet T1' T2)
  | type_equal_cong_meet_r : forall T1 T2 T2',
      type_equal_cong T2 T2' -> 
      type_equal_cong (typ_meet T1 T2) (typ_meet T1 T2')
  | type_equal_cong_join_l : forall T1 T1' T2,
      type_equal_cong T1 T1' ->
      type_equal_cong (typ_join T1 T2) (typ_join T1' T2)
  | type_equal_cong_join_r : forall T1 T2 T2',
      type_equal_cong T2 T2' ->
      type_equal_cong (typ_join T1 T2) (typ_join T1 T2').

Inductive type_equal_symm : typ -> typ -> Prop :=
  | type_equal_symm_l : forall T1 T2,
      type_equal_cong T1 T2 ->
      type_equal_symm T2 T1
  | type_equal_symm_r : forall T1 T2,
      type_equal_cong T2 T1 ->
      type_equal_symm T2 T1.

(** The kinding relation *)

Definition is_row_kind (K : knd) :=
  exists cs, K = knd_row cs.

Inductive kinding : env -> typ -> knd -> Prop :=
  | kinding_var : forall E X K,
      environment E ->
      binds X (bind_knd K) E ->
      kinding E (typ_fvar X) K
  | kinding_constructor : forall E c T K,
      kinding E T knd_type ->
      K = knd_row (CSet.singleton c) ->
      kinding E (typ_constructor c T) K
  | kinding_or : forall E T1 cs1 T2 cs2 K,
      kinding E T1 (knd_row cs1) ->
      kinding E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      K = knd_row (CSet.union cs1 cs2) ->
      kinding E (typ_or T1 T2) K
  | kinding_row : forall E T K,
      kinding E T (knd_row CSet.universe) ->
      K = knd_range T T ->
      kinding E (typ_row T) K
  | kinding_variant : forall E T T1 T2 K,
      kinding E T (knd_range T1 T2) ->
      K = knd_type ->
      kinding E (typ_variant T) K
  | kinding_arrow : forall E T1 T2 K,
      kinding E T1 knd_type -> 
      kinding E T2 knd_type -> 
      K = knd_type ->
      kinding E (typ_arrow T1 T2) K
  | kinding_top : forall E cs K,
      CSet.Nonempty cs ->
      environment E ->
      K = knd_row cs ->
      kinding E (typ_top cs) K
  | kinding_bot : forall E cs K,
      CSet.Nonempty cs ->
      environment E ->
      K = knd_row cs ->
      kinding E (typ_bot cs) K
  | kinding_meet : forall E T1 T2 K,
      kinding E T1 K ->
      kinding E T2 K ->
      is_row_kind K ->
      kinding E (typ_meet T1 T2) K
  | kinding_join : forall E T1 T2 K,
      kinding E T1 K ->
      kinding E T2 K ->
      is_row_kind K ->
      kinding E (typ_join T1 T2) K
  | kinding_subsumption : forall E T T1 T2 T1' T2' K,
      kinding E T (knd_range T1 T2) ->
      type_equal E T1' (typ_meet T1' T1) (knd_row CSet.universe) ->
      type_equal E T2 (typ_meet T2 T2') (knd_row CSet.universe) ->
      type_equal E T2' (typ_meet T2' T1') (knd_row CSet.universe) ->
      K = knd_range T1' T2' ->
      kinding E T K
      
with type_equal : env -> typ -> typ -> knd -> Prop :=
  | type_equal_refl : forall E T K,
      kinding E T K ->
      type_equal E T T K
  | type_equal_step : forall E T1 T2 T3 K,
      kinding E T1 K ->
      type_equal_symm T1 T2 ->
      type_equal E T2 T3 K ->
      type_equal E T1 T3 K.

Definition subtype E T1 T2 :=
  type_equal E T1 (typ_meet T1 T2) (knd_row CSet.universe).

Notation "E ||= T1 -<: T2" := (subtype E T1 T2) (at level 60).

Inductive valid_kind : env -> knd -> Prop :=
  | valid_type : forall E,
      environment E ->
      valid_kind E knd_type
  | valid_row :  forall E cs,
      environment E ->
      CSet.Nonempty cs ->
      valid_kind E (knd_row cs)
  | valid_range : forall E T1 T2,
      subtype E T2 T1 ->
      valid_kind E (knd_range T1 T2).

Inductive kinding_scheme : env -> sch -> Prop :=
  | kinding_scheme_empty : forall E T,
      kinding E T knd_type ->
      kinding_scheme E (sch_empty T)
  | kinding_scheme_bind : forall L E K M,
      valid_kind E K ->
      (forall X, X \notin L ->
         kinding_scheme (E & X ~:: K) (M ^ X)) ->
      kinding_scheme E (sch_bind K M).

(** A environment E is well-kinded if it contains no duplicate
  bindings and if each type in it is well-kinded with respect to
  the environment it is pushed on to. *)

Inductive kinding_env : env -> Prop :=
  | kinding_env_empty :
      kinding_env empty
  | kinding_env_kind : forall E X K,
      kinding_env E ->
      valid_kind E K ->
      X # E ->
      kinding_env (E & X ~:: K)
  | kinding_env_typ : forall E x M,
      kinding_env E ->
      kinding_scheme E M ->
      x # E ->
      kinding_env (E & x ~: M).

(* ************************************************************* *)
(** ** Description of typing *)

Inductive typing : env -> trm -> typ -> Prop :=
  | typing_var : forall E x M Us, 
      kinding_env E -> 
      binds x (bind_typ M) E -> 
      kindings E (sch_arity M) Us (sch_kinds M) ->
      typing E (trm_fvar x) (M ^^ Us)
  | typing_abs : forall L E T1 T2 t1, 
      (forall x, x \notin L -> 
        typing (E & x ~ bind_typ (Sch nil T1)) (t1 ^ x) T2) -> 
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
                   (typ_bot (CSet.cosingleton c)))
           -<: T2 ->
      (E ||= T2 -<: T3) ->
      typing E (trm_constructor c t) (typ_variant T3 T2)
  | typing_match : forall c L E T1 T2 T3 T4 T5
                          T6 T7 T8 T9 T10 t1 t2 t3,
      typing E t1 (typ_variant T1 T2) ->
      (forall x, x \notin L ->
         typing (E & x ~: (Sch nil (typ_variant T3 T4)))
                (t2 ^ x) T5) ->
      (forall y, y \notin L -> 
         typing (E & y ~: (Sch nil (typ_variant T6 T7)))
                (t3 ^ y) T5) ->
      E ||= T1 -<: (typ_or T8 T9) ->
      E ||= (typ_or T8
                   (typ_bot (CSet.cosingleton c)))
           -<: (typ_or (typ_constructor c T10)
                       (typ_bot (CSet.cosingleton c))) ->
      E ||= (typ_or T8 (typ_bot (CSet.cosingleton c)))
           -<: T4 ->
      E ||= (typ_or (typ_bot (CSet.singleton c)) T9)
           -<: T7 ->
      typing E (trm_match t1 c t2 t3) T5
  | typing_destruct : forall c L E T1 T2 T3 T4 t1 t2,
      typing E t1 (typ_variant T1 T2) ->
      (forall x, x \notin L ->
         typing (E & x ~: (Sch nil T3))
                (t2 ^ x) T4) ->
      E ||= T1 -<: (typ_or (typ_constructor c T3)
                      (typ_bot (CSet.cosingleton c))) ->
      typing E (trm_destruct t1 c t2) T4
  | typing_absurd : forall E T1 T2 T3 t1,
      kinding E T3 knd_type ->
      typing E t1 (typ_variant T1 T2) ->
      E ||= T1 -<: (typ_bot CSet.universe) ->
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
  | red_absurd : forall t1 t1',
      red t1 t1' ->
      red (trm_absurd t1) (trm_absurd t1').
                  
Notation "t ---> t'" := (red t t') (at level 68).

(* ************************************************************** *)
(** ** Description of the results *)

(** Goal is to prove preservation and progress *)

Definition preservation := forall E t t' T,
  E |= t -: T ->
  t ---> t' ->
  E |= t' -: T.


Definition progress := forall t T, 
  empty |= t -: T ->
     value t 
  \/ exists t', t ---> t'.
