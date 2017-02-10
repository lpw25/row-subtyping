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

(* Kinds *)
Inductive kind : Set :=
  | kind_type : kind
  | kind_row : kind.

(** Representation of pre-types *)

Inductive typ : Set :=
  | typ_bvar : nat -> typ
  | typ_fvar : var -> typ
  | typ_constructor : nat -> typ -> typ
  | typ_variant : typ -> typ -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_top : typ
  | typ_bot : typ
  | typ_meet : typ -> typ -> typ
  | typ_join : typ -> typ -> typ.

(** Types are inhabited, giving us a default value. *)

Definition typ_def := typ_bvar 0.

(** Type schemes. *)

Record sch : Set := Sch { 
  sch_kinds : list kind ;
  sch_type  : typ }.

Definition sch_arity M := length (sch_kinds M).

(** Opening body of type schemes. *)

Fixpoint typ_open (T : typ) (Vs : list typ) {struct T} : typ :=
  match T with
  | typ_bvar i => nth i Vs typ_def
  | typ_fvar x => typ_fvar x 
  | typ_constructor c T => typ_constructor c (typ_open T Vs)
  | typ_variant T1 T2 => typ_variant (typ_open T1 Vs) (typ_open T2 Vs)
  | typ_arrow T1 T2 => typ_arrow (typ_open T1 Vs) (typ_open T2 Vs)
  | typ_top => typ_top
  | typ_bot => typ_bot
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

(** Locally closed types *)

Inductive type : typ -> Prop :=
  | type_fvar : forall X, 
      type (typ_fvar X)
  | type_constructor : forall c T,
      type T ->
      type (typ_constructor c T)
  | type_variant : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_variant T1 T2)
  | type_arrow : forall T1 T2,
      type T1 -> 
      type T2 -> 
      type (typ_arrow T1 T2)
  | type_top : type (typ_top)
  | type_bot : type (typ_bot)
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
  type_body (sch_arity M) (sch_type M).

(* ************************************************************** *)
(** ** Description of terms *)

(** Representation of pre-terms *)

Inductive trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_abs : trm -> trm
  | trm_let : trm -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_constructor : nat -> trm -> trm
  | trm_match : trm -> nat -> trm -> trm -> trm
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
  | term_match : forall L t1 c t2 t3,
      term t1 ->
      (forall x, x \notin L -> term (t2 ^ x)) ->
      (forall x, x \notin L -> term (t3 ^ x)) ->
      term (trm_match t1 c t2 t3)
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

Inductive bind : Set :=
  | bind_kind : kind -> bind
  | bind_typ : sch -> bind.

Definition bind_kinds Xs Ks :=
  map bind_kind (Xs ~* Ks).

Notation "X ~:: K" := (X ~ bind_kind K)
  (at level 23, left associativity) : env_scope.
Notation "x ~: T" := (x ~ bind_typ T)
  (at level 23, left associativity) : env_scope.
Notation "Xs ~::* Ks" := (map bind_kind (Xs ~* Ks))
  (at level 23, left associativity) : env_scope.

(** Pre-environment is an associative list of bindings. *)

Definition env := LibEnv.env bind.

(** Environment is a pre-environment with unique bindings *)

Inductive environment : env -> Prop :=
  | environment_empty :
      environment empty
  | environment_kind : forall E X K,
      environment E ->
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

Inductive kinding : env -> typ -> kind -> Prop :=
  | kinding_var : forall K E X,
      environment E ->
      binds X (bind_kind K) E ->
      kinding E (typ_fvar X) K
  | kinding_constructor : forall E c T,
      kinding E T kind_type ->
      kinding E (typ_constructor c T) kind_row
  | kinding_variant : forall E T1 T2,
      kinding E T1 kind_row ->
      kinding E T2 kind_row ->
      kinding E (typ_variant T1 T2) kind_type
  | kinding_arrow : forall E T1 T2,
      kinding E T1 kind_type -> 
      kinding E T2 kind_type -> 
      kinding E (typ_arrow T1 T2) kind_type
  | kinding_top : forall E,
      environment E ->
      kinding E typ_top kind_row
  | kinding_bot : forall E,
      environment E ->
      kinding E typ_bot kind_row
  | kinding_meet : forall E T1 T2,
      kinding E T1 kind_row ->
      kinding E T2 kind_row ->
      kinding E (typ_meet T1 T2) kind_row
  | kinding_join : forall E T1 T2,
      kinding E T1 kind_row ->
      kinding E T2 kind_row ->
      kinding E (typ_join T1 T2) kind_row.

Inductive kindings : env -> nat -> list typ -> list kind -> Prop :=
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
  kinding (E & Xs ~::* Ks) (typ_open_vars T Xs) kind_type.

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

Inductive type_equal : env -> typ -> typ -> kind -> Prop :=
  | type_equal_var : forall E x K,
      environment E ->
      binds x (bind_kind K) E ->
      type_equal E (typ_fvar x) (typ_fvar x) K
  | type_equal_constructor : forall E c T T',
      type_equal E T T' kind_type ->
      type_equal E (typ_constructor c T) (typ_constructor c T') kind_row
  | type_equal_variant : forall E T1 T1' T2 T2',
      type_equal E T1 T1' kind_row ->
      type_equal E T2 T2' kind_row ->
      type_equal E (typ_variant T1 T2) (typ_variant T1' T2') kind_type
  | type_equal_arrow : forall E T1 T1' T2 T2',
      type_equal E T1 T1' kind_type ->
      type_equal E T2 T2' kind_type ->
      type_equal E (typ_arrow T1 T2) (typ_arrow T1' T2') kind_type
  | type_equal_top : forall E,
      environment E ->
      type_equal E typ_top typ_top kind_row
  | type_equal_bot : forall E,
      environment E ->
      type_equal E typ_bot typ_bot kind_row
  | type_equal_meet : forall E T1 T1' T2 T2',
      type_equal E T1 T1' kind_row ->
      type_equal E T2 T2' kind_row -> 
      type_equal E (typ_meet T1 T2) (typ_meet T1' T2') kind_row
  | type_equal_join : forall E T1 T1' T2 T2',
      type_equal E T1 T1' kind_row ->
      type_equal E T2 T2' kind_row ->
      type_equal E (typ_join T1 T2) (typ_join T1' T2') kind_row
  | type_equal_trans : forall E T1 T2 T3 K,
      type_equal E T1 T2 K ->
      type_equal E T2 T3 K ->
      type_equal E T1 T3 K
  | type_equal_meet_commutative : forall E T1 T2,
      kinding E T1 kind_row ->
      kinding E T2 kind_row ->
      type_equal E (typ_meet T1 T2) (typ_meet T2 T1) kind_row
  | type_equal_meet_associative_l : forall E T1 T2 T3,
      kinding E T1 kind_row ->
      kinding E T2 kind_row ->
      kinding E T3 kind_row ->
      type_equal E (typ_meet T1 (typ_meet T2 T3))
                 (typ_meet (typ_meet T1 T2) T3) kind_row
  | type_equal_meet_associative_r : forall E T1 T2 T3,
      kinding E T1 kind_row ->
      kinding E T2 kind_row ->
      kinding E T3 kind_row ->
      type_equal E (typ_meet (typ_meet T1 T2) T3)
                 (typ_meet T1 (typ_meet T2 T3)) kind_row
  | type_equal_meet_identity_l : forall E T,
      kinding E T kind_row ->
      type_equal E (typ_meet T typ_top) T kind_row
  | type_equal_meet_identity_r : forall E T,
      kinding E T kind_row ->
      type_equal E T (typ_meet T typ_top) kind_row
  | type_equal_meet_absorption_l : forall E T1 T2,
      kinding E T1 kind_row ->
      kinding E T2 kind_row ->
      type_equal E (typ_meet T1 (typ_join T1 T2)) T1 kind_row
  | type_equal_meet_absorption_r : forall E T1 T2,
      kinding E T1 kind_row ->
      kinding E T2 kind_row ->
      type_equal E T1 (typ_meet T1 (typ_join T1 T2)) kind_row
  | type_equal_meet_distribution_l : forall E T1 T2 T3,
      kinding E T1 kind_row ->
      kinding E T2 kind_row ->
      kinding E T3 kind_row ->
      type_equal E (typ_meet (typ_join T1 T2) (typ_join T1 T3))
                 (typ_join T1 (typ_meet T2 T3)) kind_row
  | type_equal_meet_distribution_r : forall E T1 T2 T3,
      kinding E T1 kind_row ->
      kinding E T2 kind_row ->
      kinding E T3 kind_row ->
      type_equal E (typ_join T1 (typ_meet T2 T3))
                 (typ_meet (typ_join T1 T2) (typ_join T1 T3)) kind_row
  | type_equal_join_commutative : forall E T1 T2,
      kinding E T1 kind_row ->
      kinding E T2 kind_row ->
      type_equal E (typ_join T1 T2) (typ_join T2 T1) kind_row
  | type_equal_join_associative_l : forall E T1 T2 T3,
      kinding E T1 kind_row ->
      kinding E T2 kind_row ->
      kinding E T3 kind_row ->
      type_equal E (typ_join T1 (typ_join T2 T3))
                 (typ_join (typ_join T1 T2) T3) kind_row
  | type_equal_join_associative_r : forall E T1 T2 T3,
      kinding E T1 kind_row ->
      kinding E T2 kind_row ->
      kinding E T3 kind_row ->
      type_equal E (typ_join (typ_join T1 T2) T3)
                 (typ_join T1 (typ_join T2 T3)) kind_row
  | type_equal_join_identity_l : forall E T,
      kinding E T kind_row ->
      type_equal E (typ_join T typ_bot) T kind_row
  | type_equal_join_identity_r : forall E T,
      kinding E T kind_row ->
      type_equal E T (typ_join T typ_bot) kind_row
  | type_equal_join_absorption_l : forall E T1 T2,
      kinding E T1 kind_row ->
      kinding E T2 kind_row ->
      type_equal E (typ_join T1 (typ_meet T1 T2)) T1 kind_row
  | type_equal_join_absorption_r : forall E T1 T2,
      kinding E T1 kind_row ->
      kinding E T2 kind_row ->
      type_equal E T1 (typ_join T1 (typ_meet T1 T2)) kind_row
  | type_equal_join_distribution_l : forall E T1 T2 T3,
      kinding E T1 kind_row ->
      kinding E T2 kind_row ->
      kinding E T3 kind_row ->
      type_equal E (typ_join T1 (typ_meet T2 T3))
                 (typ_meet (typ_join T1 T2) (typ_join T1 T3)) kind_row
  | type_equal_join_distribution : forall E T1 T2 T3,
      kinding E T1 kind_row -> 
      kinding E T2 kind_row ->
      kinding E T3 kind_row ->
      type_equal E (typ_meet (typ_join T1 T2) (typ_join T1 T3))
                 (typ_join T1 (typ_meet T2 T3)) kind_row.


Definition subtype E T1 T2 :=
  type_equal E T1 (typ_join T1 T2) kind_row.

Inductive typing : env -> trm -> typ -> Prop :=
  | typing_var : forall E x M Us, 
      kinding_env E -> 
      binds x (bind_typ M) E -> 
      kindings E (sch_arity M) Us (sch_kinds M) ->
      typing E (trm_fvar x) (M ^^ Us)
  | typing_abs : forall L E T1 T2 t1, 
      kinding E T1 kind_type ->
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
      subtype E (typ_constructor c T1) T2 ->
      subtype E T2 T3 ->
      typing E (trm_constructor c t) (typ_variant T3 T2)
  | typing_match : forall c L E T1 T2 T3 T4 T5 T6 t1 t2 t3,
      typing E t1 (typ_variant T1 T2) ->
      (forall x, x \notin L -> 
         typing (E & x ~ bind_typ (Sch nil T3)) (t2 ^ x) T4) ->
      (forall y, y \notin L -> 
         typing (E & y ~ bind_typ (Sch nil (typ_variant T5 T6)))
                (t3 ^ y) T4) ->
      subtype E T1 (typ_join (typ_constructor c T3) T6) ->
      subtype E T2 T1 ->
      subtype E T6 T5 ->
      typing E (trm_match t1 c t2 t3) T4
  | typing_absurd : forall E T1 T2 T3 t1,
      kinding E T3 kind_type ->
      typing E t1 (typ_variant T1 T2) ->
      subtype E typ_bot T2 ->
      subtype E T2 T1 ->
      typing E (trm_absurd t1) T3.

Notation "E |= t -: T" := (typing E t T) (at level 69).

Definition typing_scheme E t M :=
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
  | red_match_2 : forall c t1 t2 t3,
      value (trm_constructor c t1) ->
      term_body t2 ->
      term_body t3 ->
      red (trm_match (trm_constructor c t1) c t2 t3) (t2 ^^ t1)
  | red_match_3 : forall c d t1 t2 t3,
      c <> d ->
      value (trm_constructor d t1) ->
      term_body t2 ->
      term_body t3 ->
      red (trm_match (trm_constructor d t1) c t2 t3)
          (t3 ^^ (trm_constructor d t1))
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
