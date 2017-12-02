(************************************************
 *          Row Subtyping - Substitution        *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import List LibLN Definitions.

(* *************************************************************** *)
(** ** Free Variables *)

(** Computing free variables of a type. *)

Fixpoint typ_fv (T : typ) {struct T} : vars :=
  match T with
  | typ_bvar i => \{}
  | typ_fvar x => \{x}
  | typ_constructor c T1 => (typ_fv T1)
  | typ_or T1 T2 => (typ_fv T1) \u (typ_fv T2)
  | typ_row T1 => (typ_fv T1)
  | typ_variant T1 => (typ_fv T1)
  | typ_arrow T1 T2 => (typ_fv T1) \u (typ_fv T2)
  | typ_top cs => \{}
  | typ_bot cs => \{}
  | typ_meet T1 T2 => (typ_fv T1) \u (typ_fv T2)
  | typ_join T1 T2 => (typ_fv T1) \u (typ_fv T2)
  end.

(** Computing free variables of a list of terms. *)

Definition typ_fv_list :=
  fold_right (fun t acc => typ_fv t \u acc) \{}.

Definition knd_fv K :=
  match K with
  | knd_type => \{}
  | knd_row _ => \{}
  | knd_range T1 T2 => (typ_fv T1) \u (typ_fv T2)
  end.

(** Computing free variables of a type scheme. *)

Fixpoint sch_fv (M : sch) : vars :=
  match M with
  | sch_empty T => typ_fv T
  | sch_bind K M => (knd_fv K) \u (sch_fv M)
  end.

(** Computing free type variables of the values of an environment. *)

Definition bind_fv (B : bind) : vars :=
  match B with
  | bind_knd K => knd_fv K
  | bind_typ M => sch_fv M
  end.

Definition env_fv := 
  fv_in_values bind_fv.

(** Computing free variables of a term. *)

Fixpoint trm_fv (t : trm) {struct t} : vars :=
  match t with
  | trm_bvar i => \{}
  | trm_fvar x => \{x}
  | trm_abs t1 => trm_fv t1
  | trm_let t1 t2 => (trm_fv t1) \u (trm_fv t2)
  | trm_app t1 t2 => (trm_fv t1) \u (trm_fv t2)
  | trm_constructor c t1 => trm_fv t1
  | trm_match t1 c t2 t3 => (trm_fv t1) \u (trm_fv t2) \u (trm_fv t3)
  | trm_destruct t1 c t2 => (trm_fv t1) \u (trm_fv t2)
  | trm_absurd t1 => trm_fv t1
  end.

(* *************************************************************** *)
(** ** Substitution for free names *)

(** Substitution for names for types *)

Fixpoint typ_subst (Z : var) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_bvar i => typ_bvar i
  | typ_fvar X => If X = Z then U else (typ_fvar X)
  | typ_constructor c T1 => typ_constructor c (typ_subst Z U T1)
  | typ_or T1 T2 =>
      typ_or (typ_subst Z U T1) (typ_subst Z U T2)
  | typ_row T1 => typ_row (typ_subst Z U T1)
  | typ_variant T1 => typ_variant (typ_subst Z U T1)
  | typ_arrow T1 T2 =>
      typ_arrow (typ_subst Z U T1) (typ_subst Z U T2)
  | typ_top cs => typ_top cs
  | typ_bot cs => typ_bot cs
  | typ_meet T1 T2 =>
      typ_meet (typ_subst Z U T1) (typ_subst Z U T2)
  | typ_join T1 T2 =>
      typ_join (typ_subst Z U T1) (typ_subst Z U T2)
  end.

Fixpoint typ_substs (Zs : list var) (Us : list typ) (T : typ)
         {struct Zs} :=
  match Zs with
  | nil => T
  | Z :: Zs =>
    match Us with
    | nil => T
    | U :: Us => typ_substs Zs Us (typ_subst Z U T)
    end
  end.

(** Substitution for names for kinds. *)
Definition knd_subst Z U K :=
  match K with
  | knd_type => knd_type
  | knd_row cs => knd_row cs
  | knd_range T1 T2 => knd_range (typ_subst Z U T1) (typ_subst Z U T2)
  end.

Fixpoint knd_substs (Zs : list var) (Us : list typ) (K : knd)
         {struct Zs} :=
  match Zs with
  | nil => K
  | Z :: Zs =>
    match Us with
    | nil => K
    | U :: Us => knd_substs Zs Us (knd_subst Z U K)
    end
  end.

(** Substitution for names for schemes. *)

Fixpoint sch_subst (Z : var) (U : typ) (M : sch) {struct M} :=
  match M with
  | sch_empty T => sch_empty (typ_subst Z U T)
  | sch_bind K M => sch_bind (knd_subst Z U K) (sch_subst Z U M)
  end.

Fixpoint sch_substs (Zs : list var) (Us : list typ) (M : sch)
         {struct Zs} :=
  match Zs with
  | nil => M
  | Z :: Zs =>
    match Us with
    | nil => M
    | U :: Us => sch_substs Zs Us (sch_subst Z U M)
    end
  end.

(** Substitution for bindings *)
Definition binding_subst Z U B :=
  match B with
  | bind_knd K => bind_knd (knd_subst Z U K)
  | bind_typ M => bind_typ (sch_subst Z U M)
  end.

(** Substitution for environments *)
Definition environment_subst Z U E :=
  map (binding_subst Z U) E.

(** Substitution for name in a term. *)

Fixpoint trm_subst (z : var) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i => trm_bvar i 
  | trm_fvar x => If x = z then u else (trm_fvar x)
  | trm_abs t1 => trm_abs (trm_subst z u t1) 
  | trm_let t1 t2 => trm_let (trm_subst z u t1) (trm_subst z u t2) 
  | trm_app t1 t2 => trm_app (trm_subst z u t1) (trm_subst z u t2)
  | trm_constructor c t1 => trm_constructor c (trm_subst z u t1)
  | trm_match t1 c t2 t3 =>
      trm_match (trm_subst z u t1) c
                (trm_subst z u t2) (trm_subst z u t3)
  | trm_destruct t1 c t2 =>
      trm_destruct (trm_subst z u t1) c (trm_subst z u t2)
  | trm_absurd t1 => trm_absurd (trm_subst z u t1)
  end.

Notation "[ z ~> u ] t" := (trm_subst z u t) (at level 68).

(* =============================================================== *)
(** * Tactics *)

(* *************************************************************** *)
(** ** Instanciation of Tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : env => dom x) in
  let D := gather_vars_with (fun x : LibEnv.env bind => dom x) in
  let E := gather_vars_with (fun x : trm => trm_fv x) in
  let F := gather_vars_with (fun x : typ => typ_fv x) in
  let G := gather_vars_with (fun x : list typ => typ_fv_list x) in
  let H := gather_vars_with (fun x : env => env_fv x) in
  let I := gather_vars_with (fun x : LibEnv.env bind => env_fv x) in
  let J := gather_vars_with (fun x : sch => sch_fv x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u I \u J).

Tactic Notation "pick_fresh" ident(x) :=
  let L := gather_vars in (pick_fresh_gen L x).

Tactic Notation "pick_freshes" constr(n) ident(x) :=
  let L := gather_vars in (pick_freshes_gen L n x).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; autos*.

Tactic Notation "exists_fresh" ident(x) ident(Hfr) :=
  exists_fresh_gen gather_vars x Hfr.

(* *************************************************************** *)
(** ** Automation *)

Hint Extern 1 =>
  match goal with
  | H : forall x, x \notin ?L -> ?P |- ?P =>
    apply (H (proj1_sig (var_fresh L)) (proj2_sig (var_fresh L)))
  | H: forall Xs : list var,
      fresh ?L ?n Xs -> ?P |- ?P =>
    apply (H (proj1_sig (var_freshes L n))
             (proj2_sig (var_freshes L n)))
  end.

(* =============================================================== *)
(** ** Properties of fv *)

Lemma fv_list_map : forall ts1 ts2,
  typ_fv_list (ts1 ++ ts2) = typ_fv_list ts1 \u typ_fv_list ts2.
Proof.
  induction ts1; simpl; intros. 
  - rewrite* union_empty_l.
  - rewrite IHts1.
    rewrite* union_assoc.
Qed.

(* =============================================================== *)
(** Utilities *)

Lemma fresh_length : forall L n xs,
  fresh L n xs -> n = length xs.
Proof using.
  intros. gen n L. induction xs; simpl; intros n L Fr;
    destruct n; tryfalse*.
  easy.
  f_equal.
  rewrite* <- (@IHxs n (L \u \{a})).
Qed.

Lemma map_identity : forall A L,
    List.map (fun x : A => x) L = L.
Proof.
  intros.
  induction L; simpl; f_equal; auto.
Qed.

Lemma map_compose : forall A B C L (g : A -> B) (f : B -> C),
    List.map (fun x : A => f (g x)) L =
    List.map f (List.map g L).
Proof.
  intros.
  induction L; simpl; f_equal; auto.
Qed.

Lemma types_cons : forall T Ts,
    types (length (T :: Ts)) (T :: Ts) <->
    type T /\ types (length Ts) Ts.
Proof.
  intros. unfold types. simpl.
  intuition.
  - inversion H1; assumption.
  - inversion H1; assumption.
Qed.

(* =============================================================== *)
(** * Properties of terms *)

(** Substitution on indices is identity on well-formed terms. *)

Lemma trm_open_rec_core :forall t j v i u, i <> j ->
  {j ~> v}t = {i ~> u}({j ~> v}t) -> t = {i ~> u}t.
Proof.
  induction t; introv Neq Equ;
    simpl in *; inversion* Equ; f_equal*.
  case_nat*. case_nat*.
Qed.

Lemma trm_open_rec : forall t u,
  term t -> forall k, t = {k ~> u}t.
Proof.
  induction 1; intros; simpl; f_equal*. 
  { unfolds trm_open. pick_fresh x.
    apply* (@trm_open_rec_core t1 0 (trm_fvar x)). }
  { unfolds trm_open. pick_fresh x.
    apply* (@trm_open_rec_core t2 0 (trm_fvar x)). }
  { unfolds trm_open. pick_fresh x.
    apply* (@trm_open_rec_core t2 0 (trm_fvar x)). }
  { unfolds trm_open. pick_fresh x.
    apply* (@trm_open_rec_core t3 0 (trm_fvar x)). }
  { unfolds trm_open. pick_fresh x.
    apply* (@trm_open_rec_core t2 0 (trm_fvar x)). }
Qed.

(** Substitution for a fresh name is identity. *)

Lemma trm_subst_fresh : forall x t u, 
  x \notin trm_fv t ->  [x ~> u] t = t.
Proof.
  intros. induction t; simpls; f_equal*.
  case_var*. 
Qed.

(** Substitution distributes on the open operation. *)

Lemma trm_subst_open : forall x u t1 t2, term u -> 
  [x ~> u] (t1 ^^ t2) = ([x ~> u]t1) ^^ ([x ~> u]t2).
Proof.
  intros. unfold trm_open. generalize 0.
  induction t1; intros; simpl; f_equal*.
  case_nat*. case_var*. apply* trm_open_rec.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma trm_subst_open_var : forall x y u e, y <> x -> term u ->
  ([x ~> u]e) ^ y = [x ~> u] (e ^ y).
Proof.
  introv Neq Wu. rewrite* trm_subst_open.
  simpl. case_var*.
Qed.

(** Opening up an abstraction of body t with a term u is the same as
  opening up the abstraction with a fresh name x and then substituting u
  for x. *)

Lemma trm_subst_intro : forall x t u, 
  x \notin (trm_fv t) -> term u ->
  t ^^ u = [x ~> u](t ^ x).
Proof.
  introv Fr Wu. rewrite* trm_subst_open.
  rewrite* trm_subst_fresh. simpl. case_var*.
Qed.

(* =============================================================== *)
(** * Properties of types *)

(** Open on a type is the identity. *)

Lemma typ_open_rec_core : forall T j V i U, i <> j ->
  typ_open_k j V T = typ_open_k i U (typ_open_k j V T) ->
  T = typ_open_k i U T.
Proof.
  induction T; introv Neq Equ; simpl in *; inversion* Equ; f_equal*.
  case_nat*. case_nat*.
Qed.

Lemma typ_open_type : forall T U,
  type T -> forall k, T = typ_open_k k U T.
Proof.
  introv W.
  induction T; intro; unfold typ_open; simpls; inversion W; fequals*.
Qed.

(** Substitution for a fresh name is identity. *)

Lemma typ_subst_fresh : forall X U T, 
  X \notin typ_fv T -> 
  typ_subst X U T = T.
Proof.
  intros. induction T; simpls; f_equal*. case_var*. 
Qed.

Lemma typ_subst_fresh_list : forall X U Ts,
  X \notin typ_fv_list Ts ->
  List.map (typ_subst X U) Ts = Ts.
Proof.
  induction Ts; simpl; intros Fr.
  - easy.
  - f_equal*.
    rewrite~ typ_subst_fresh.
Qed.

Lemma typ_subst_fresh_typ_fvars : forall X U Xs,
  fresh (\{X}) (length Xs) Xs ->
  List.map (typ_subst X U) (typ_fvars Xs) = typ_fvars Xs.
Proof.
  intros. apply typ_subst_fresh_list.
  induction Xs; simpl.
  - auto.
  - destruct H. auto.
Qed.

(** Substitution distributes on the open operation. *)

Lemma typ_subst_open_k : forall k X U T1 T2, type U -> 
  typ_subst X U (typ_open_k k T1 T2) = 
   typ_open_k k (typ_subst X U T1) (typ_subst X U T2).
Proof.
  intros. induction T2; intros; unfold typ_open; simpl; f_equal*.
  - case_nat*.
  - case_var*. apply* typ_open_type.
Qed.

Lemma typ_subst_open : forall X U T1 T2, type U -> 
  typ_subst X U (typ_open T1 T2) = 
   typ_open (typ_subst X U T1) (typ_subst X U T2).
Proof.
  intros. unfold typ_open. apply typ_subst_open_k. assumption.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma typ_subst_open_var : forall X Y U T, 
  Y <> X -> type U ->
     typ_open_var (typ_subst X U T) Y
   = typ_subst X U (typ_open_var T Y).
Proof.
  introv Neq Wu. unfold typ_open_var. 
  rewrite* typ_subst_open. simpl.
  case_var*.
Qed.

(** Opening up a type T with a type U is the same as opening up T
    with a fresh name X and then substituting U for X. *)
Lemma typ_subst_intro : forall X T U, 
  X \notin (typ_fv T) -> type U ->
  typ_open T U = typ_subst X U (typ_open_var T X).
Proof.
  introv Fr Wu. unfold typ_open_var.
  rewrite* typ_subst_open.
  rewrite* typ_subst_fresh. simpl. case_var*.
Qed.

Lemma typ_substs_fresh : forall Xs Us T, 
  fresh (typ_fv T) (length Xs) Xs ->
  typ_substs Xs Us T = T.
Proof.
  introv H. generalize dependent Us.
  induction Xs; intro; simpl; auto.
  destruct Us; auto.
  destruct H.
  rewrite typ_subst_fresh; auto.
Qed.

Lemma typ_substs_fvars : forall Xs Ts,
    fresh (typ_fv_list Ts) (length Ts) Xs ->
    List.map (typ_substs Xs Ts) (typ_fvars Xs) = Ts.
Proof.
  introv Hf.
  assert (length Ts = length Xs)
    by apply (fresh_length _ _ _ Hf).
  generalize dependent Ts.
  induction Xs; introv Hf Hl;
    destruct Ts; simpl in *; try discriminate.
  - reflexivity.
  - inversion Hl.
    destruct Hf.
    case_var.
    rewrite typ_substs_fresh; auto.
    rewrite map_compose.
    rewrite typ_subst_fresh_typ_fvars; auto.
    f_equal; auto.
Qed.

Lemma typ_substs_open_k : forall k Xs Us T1 T2,
  types (length Us) Us -> 
  typ_substs Xs Us (typ_open_k k T1 T2) = 
   typ_open_k k (typ_substs Xs Us T1) (typ_substs Xs Us T2).
Proof.
  intros k Xs.
  induction Xs; introv H; simpl; auto.
  destruct Us; auto.
  rewrite types_cons in H.
  destruct H.
  rewrite typ_subst_open_k; auto.
Qed.

Lemma typ_substs_open : forall Xs Us T1 T2,
    types (length Us) Us -> 
    typ_substs Xs Us (typ_open T1 T2) = 
    typ_open (typ_substs Xs Us T1) (typ_substs Xs Us T2).
Proof.
  intros. unfold typ_open. apply typ_substs_open_k. assumption.
Qed.

Lemma typ_substs_open_var : forall Xs Y Us T,
    fresh \{Y} (length Xs) Xs ->
    types (length Us) Us ->
    typ_open_var (typ_substs Xs Us T) Y
    = typ_substs Xs Us (typ_open_var T Y).
Proof.
  introv Nin Wu. unfold typ_open_var. 
  rewrite typ_substs_open; auto.
  f_equal.
  rewrite typ_substs_fresh; auto.
Qed.

(** Open on a kind is the identity. *)

Lemma knd_open_rec_core : forall K j V i U, i <> j ->
  knd_open_k j V K = knd_open_k i U (knd_open_k j V K) ->
  K = knd_open_k i U K.
Proof.
  induction K; introv Neq Equ; simpl in *; inversion* Equ; fequal*;
    apply typ_open_rec_core with (j := j) (V := V); auto.
Qed.

Lemma knd_open_kind : forall K U,
  kind K -> forall k, K = knd_open_k k U K.
Proof.
  introv W. intro.
  destruct K; unfold knd_open; simpl; fequals*;
    inversion W; apply typ_open_type; auto.
Qed.

(** Substitution for a fresh name is identity. *)

Lemma knd_subst_fresh : forall X U K, 
  X \notin knd_fv K -> 
  knd_subst X U K = K.
Proof.
  intros. destruct K; simpls; f_equal*; apply typ_subst_fresh; auto.
Qed.

(** Substitution distributes on the open operation. *)

Lemma knd_subst_open_k : forall k X U K T, type U -> 
  knd_subst X U (knd_open_k k T K) = 
   knd_open_k k (typ_subst X U T) (knd_subst X U K).
Proof.
  intros.
  destruct K; unfold knd_open; simpl; f_equal*;
    apply typ_subst_open_k; auto.
Qed.

Lemma knd_subst_open : forall X U K T, type U -> 
  knd_subst X U (knd_open K T) = 
   knd_open (knd_subst X U K) (typ_subst X U T).
Proof.
  intros. unfold knd_open. apply knd_subst_open_k. assumption.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma knd_subst_open_var : forall X Y U K, 
  Y <> X -> type U ->
     knd_open_var (knd_subst X U K) Y
   = knd_subst X U (knd_open_var K Y).
Proof.
  introv Neq Wu. unfold knd_open_var. 
  rewrite* knd_subst_open. simpl.
  case_var*.
Qed.

(** Opening up a kind K with a type U is the same as opening up K
    with a fresh name X and then substituting U for X. *)
Lemma knd_subst_intro : forall X K U, 
  X \notin (knd_fv K) -> type U ->
  knd_open K U = knd_subst X U (knd_open_var K X).
Proof.
  introv Fr Wu. unfold knd_open_var.
  rewrite* knd_subst_open.
  rewrite* knd_subst_fresh. simpl. case_var*.
Qed.

Lemma knd_substs_fresh : forall Xs Us K, 
  fresh (knd_fv K) (length Xs) Xs ->
  knd_substs Xs Us K = K.
Proof.
  introv H. generalize dependent Us.
  induction Xs; intro; simpl; auto.
  destruct Us; auto.
  destruct H.
  rewrite knd_subst_fresh; auto.
Qed.

Lemma knd_substs_open_k : forall k Xs Us K T,
  types (length Us) Us -> 
  knd_substs Xs Us (knd_open_k k T K) = 
   knd_open_k k (typ_substs Xs Us T) (knd_substs Xs Us K).
Proof.
  intros k Xs.
  induction Xs; introv H; simpl; auto.
  destruct Us; auto.
  rewrite types_cons in H.
  destruct H.
  rewrite knd_subst_open_k; auto.
Qed.

Lemma knd_substs_open : forall Xs Us K T,
    types (length Us) Us -> 
    knd_substs Xs Us (knd_open K T) = 
    knd_open (knd_substs Xs Us K) (typ_substs Xs Us T).
Proof.
  intros. unfold knd_open. apply knd_substs_open_k. assumption.
Qed.

Lemma knd_substs_open_var : forall Xs Y Us T,
    fresh \{Y} (length Xs) Xs ->
    types (length Us) Us ->
    knd_open_var (knd_substs Xs Us T) Y
    = knd_substs Xs Us (knd_open_var T Y).
Proof.
  introv Nin Wu. unfold knd_open_var. 
  rewrite knd_substs_open; auto.
  f_equal.
  rewrite typ_substs_fresh; auto.
Qed.

(** Open on a scheme is the identity. *)

Lemma sch_open_rec_core :forall M j V i U, i <> j ->
  sch_open_k j V M = sch_open_k i U (sch_open_k j V M) ->
  M = sch_open_k i U M.
Proof.
  induction M; introv Neq Equ; simpl in *; inversion* Equ; fequal*.
  - apply typ_open_rec_core with (j := j) (V := V); auto.
  - apply knd_open_rec_core with (j := j) (V := V); auto.
Qed.    

Lemma sch_open_scheme : forall M U,
  scheme M -> forall k, M = sch_open_k k U M.
Proof.
  introv W.
  induction W; intros; simpl; f_equal*.
  - apply typ_open_type; auto.
  - apply knd_open_kind; auto.
  - unfolds sch_open_var, sch_open.
    pick_fresh X.
    apply sch_open_rec_core with (j := 0) (V := typ_fvar X); auto.
Qed.    

(** Substitution for a fresh name is identity. *)

Lemma sch_subst_fresh : forall X U M, 
  X \notin sch_fv M -> 
  sch_subst X U M = M.
Proof.
  intros. induction M; simpls; f_equal*.
  - apply typ_subst_fresh; auto.
  - apply knd_subst_fresh; auto.
Qed.

(** Substitution distributes on the open operation. *)

Lemma sch_subst_open_k : forall k X U M T, type U -> 
  sch_subst X U (sch_open_k k T M) = 
   sch_open_k k (typ_subst X U T) (sch_subst X U M).
Proof.
  intros. unfold sch_open. generalize dependent k.
  induction M; intro; simpl; f_equal*.
  - apply typ_subst_open_k; auto.
  - apply knd_subst_open_k; auto.
Qed.

Lemma sch_subst_open : forall X U M T, type U -> 
  sch_subst X U (sch_open M T) = 
   sch_open (sch_subst X U M) (typ_subst X U T).
Proof.
  intros. unfold sch_open. apply sch_subst_open_k. assumption.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma sch_subst_open_var : forall X Y U M, 
  Y <> X -> type U ->
     sch_open_var (sch_subst X U M) Y
   = sch_subst X U (sch_open_var M Y).
Proof.
  introv Neq Wu. unfold sch_open_var. 
  rewrite* sch_subst_open. simpl.
  case_var*.
Qed.

(** Opening up a scheme M with a type U is the same as opening up M
    with a fresh name X and then substituting U for X. *)
Lemma sch_subst_intro : forall X M U, 
  X \notin (sch_fv M) -> type U ->
  sch_open M U = sch_subst X U (sch_open_var M X).
Proof.
  introv Fr Wu. unfold sch_open_var.
  rewrite* sch_subst_open.
  rewrite* sch_subst_fresh. simpl. case_var*.
Qed.

Lemma sch_substs_fresh : forall Xs Us M, 
  fresh (sch_fv M) (length Xs) Xs ->
  sch_substs Xs Us M = M.
Proof.
  introv H. generalize dependent Us.
  induction Xs; intro; simpl; auto.
  destruct Us; auto.
  destruct H.
  rewrite sch_subst_fresh; auto.
Qed.

Lemma sch_substs_open_k : forall k Xs Us M T,
  types (length Us) Us -> 
  sch_substs Xs Us (sch_open_k k T M) = 
   sch_open_k k (typ_substs Xs Us T) (sch_substs Xs Us M).
Proof.
  intros k Xs.
  induction Xs; introv H; simpl; auto.
  destruct Us; auto.
  rewrite types_cons in H.
  destruct H.
  rewrite sch_subst_open_k; auto.
Qed.

Lemma sch_substs_open : forall Xs Us M T,
    types (length Us) Us -> 
    sch_substs Xs Us (sch_open M T) = 
    sch_open (sch_substs Xs Us M) (typ_substs Xs Us T).
Proof.
  intros. unfold sch_open. apply sch_substs_open_k. assumption.
Qed.

Lemma sch_substs_open_var : forall Xs Y Us M,
    fresh \{Y} (length Xs) Xs ->
    types (length Us) Us ->
    sch_open_var (sch_substs Xs Us M) Y
    = sch_substs Xs Us (sch_open_var M Y).
Proof.
  introv Nin Wu. unfold sch_open_var. 
  rewrite sch_substs_open; auto.
  f_equal.
  rewrite typ_substs_fresh; auto.
Qed.

(** Substitution distributes on the sch_body. *)

Lemma sch_subst_body : forall X U M, type U ->
    typ_subst X U (sch_body M) = sch_body (sch_subst X U M).
Proof.
  intros. induction M; simpl; auto.
Qed.

(** Substitution distributes on the instance operation. *)

Lemma sch_subst_instance_rec : forall k X U M Ts, type U -> 
  typ_subst X U (instance_rec M Ts k) = 
   instance_rec (sch_subst X U M) (List.map (typ_subst X U) Ts) k.
Proof.
  intros.
  generalize dependent M.
  generalize dependent Ts.
  induction k; intros; simpl.
  - apply sch_subst_body; assumption.
  - destruct M; simpl; try reflexivity.
    destruct Ts; simpl.
    + apply sch_subst_body; assumption.
    + rewrite <- sch_subst_open; auto.
Qed.

Lemma sch_subst_arity : forall X U M,
    sch_arity (sch_subst X U M) = sch_arity M.
Proof.
  intros.
  induction M; simpl; auto.
Qed.

Lemma sch_subst_instance : forall X U M Ts, type U -> 
  typ_subst X U (instance M Ts) = 
   instance (sch_subst X U M) (List.map (typ_subst X U) Ts).
Proof.
  intros. unfold instance.
  rewrite sch_subst_arity.
  apply sch_subst_instance_rec.
  assumption.
Qed.

Lemma sch_substs_instance : forall Xs Us M Ts,
    types (length Us) Us -> 
    typ_substs Xs Us (instance M Ts) = 
    instance (sch_substs Xs Us M) (List.map (typ_substs Xs Us) Ts).
Proof.
  intro.
  induction Xs; introv H; simpl.
  - rewrite map_identity. reflexivity.
  - destruct Us.
    + rewrite map_identity. reflexivity.
    + rewrite map_compose.
      apply types_cons in H.
      destruct H.
      rewrite sch_subst_instance; auto.
Qed.

Lemma typ_substs_intro_instance : forall M Xs Us,
  fresh (sch_fv M \u typ_fv_list Us) (sch_arity M) Xs -> 
  types (sch_arity M) Us ->
  instance M Us = typ_substs Xs Us (instance_vars M Xs).
Proof.
  introv Hf Ht. unfold instance_vars.
  replace (sch_arity M) with (length Xs) in *
    by (symmetry; apply (fresh_length _ _ _ Hf)).
  destruct Ht.
  rewrite sch_substs_instance; try (split; auto).
  rewrite sch_substs_fresh; auto.
  rewrite typ_substs_fvars; auto.
Qed.

Lemma sch_subst_empty : forall X U T,
    sch_subst X U (sch_empty T) =
    sch_empty (typ_subst X U T).
Proof.
  unfold sch_subst.
  reflexivity.
Qed.
