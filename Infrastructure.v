(************************************************
 *          Row Subtyping - Infrastructure      *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import List LibLN Definitions.

(* =============================================================== *)
(** * Additional Definitions used in the Proofs *)

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

Hint Constructors kind type scheme term environment type_equal_or
     type_equal_meet type_equal_join type_equal_core type_equal_cong
     type_equal_symm type_equal valid_kind kinding kinding_scheme
     kinding_instance kinding_env typing value red.

Hint Unfold is_row_kind.

Hint Extern 1 (types _ _) => split; auto.

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

(** Terms are stable by substitution *)

Lemma trm_subst_term : forall t z u,
  term u -> term t -> term ([z ~> u]t).
Proof.
  induction 2; simpls*.
  - case_var*.
  - apply_fresh term_abs as y. rewrite* trm_subst_open_var.
  - apply_fresh* term_let as y. rewrite* trm_subst_open_var.
  - apply_fresh* term_match as y; rewrite* trm_subst_open_var.
  - apply_fresh* term_destruct as y; rewrite* trm_subst_open_var.
Qed.

Hint Resolve trm_subst_term.

(** Conversion from locally closed abstractions and bodies *)

Lemma term_abs_to_body : forall t1, 
  term (trm_abs t1) -> term_body t1.
Proof.
  intros. unfold term_body. inversion* H.
Qed.

Lemma body_to_term_abs : forall t1, 
  term_body t1 -> term (trm_abs t1).
Proof.
  intros. inversion* H.
Qed.

Lemma term_let_to_body : forall t1 t2, 
  term (trm_let t1 t2) -> term_body t2.
Proof.
  intros. unfold term_body. inversion* H.
Qed.

Lemma body_to_term_let : forall t1 t2, 
  term_body t2 -> term t1 -> term (trm_let t1 t2).
Proof.
  intros. inversion* H.
Qed.

Lemma term_match_to_body1 : forall c t1 t2 t3,
  term (trm_match t1 c t2 t3) -> term_body t2.
Proof.
  intros. unfold term_body. inversion* H.
Qed.

Lemma term_match_to_body2 : forall c t1 t2 t3,
  term (trm_match t1 c t2 t3) -> term_body t3.
Proof.
  intros. unfold term_body. inversion* H.
Qed.

Lemma bodies_to_term_match : forall c t1 t2 t3,
  term t1 -> term_body t2 -> term_body t3 ->
  term (trm_match t1 c t2 t3).
Proof.
  intros. inversion H0. inversion H1.
  apply* (@term_match (x \u x0)).
Qed.

Lemma term_destruct_to_body : forall c t1 t2,
  term (trm_destruct t1 c t2) -> term_body t2.
Proof.
  intros. unfold term_body. inversion* H.
Qed.

Lemma body_to_term_destruct : forall c t1 t2,
  term t1 -> term_body t2 ->
  term (trm_destruct t1 c t2).
Proof.
  intros. inversion H0.
  apply* (@term_destruct x).
Qed.

Hint Resolve
     body_to_term_abs
     body_to_term_let
     bodies_to_term_match
     body_to_term_destruct.

Hint Extern 1 (term_body ?t) =>
  match goal with 
  | H: context [trm_abs t] |- _ => 
    apply term_abs_to_body 
  | H: context [trm_let ?t1 t] |- _ => 
    apply (@term_let_to_body t1) 
  | H: context [trm_match ?t1 ?c t ?t3] |- _ => 
    apply (@term_match_to_body1 c t1 t t3) 
  | H: context [trm_match ?t1 ?c ?t2 t] |- _ => 
    apply (@term_match_to_body2 c t1 t2 t)
  end.

(** ** Opening a body with a term gives a term *)

Lemma trm_open_term : forall t u,
  term_body t -> term u -> term (t ^^ u).
Proof.
  intros. destruct H. pick_fresh y. rewrite* (@trm_subst_intro y).
Qed.

Hint Resolve trm_open_term.

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

Lemma typ_subst_constructor : forall X U c T,
  typ_subst X U (typ_constructor c T) =
  typ_constructor c (typ_subst X U T).
Proof.
  auto.
Qed.

Lemma typ_subst_row : forall X U T,
  typ_subst X U (typ_row T) =
  typ_row (typ_subst X U T).
Proof.
  auto.
Qed.

Lemma typ_subst_variant : forall X U T,
  typ_subst X U (typ_variant T) =
  typ_variant (typ_subst X U T).
Proof.
  auto.
Qed.

Lemma typ_subst_join : forall X U T1 T2,
  typ_subst X U (typ_join T1 T2) =
  typ_join (typ_subst X U T1) (typ_subst X U T2).
Proof.
  auto.
Qed.

Lemma typ_subst_meet : forall X U T1 T2,
  typ_subst X U (typ_join T1 T2) =
  typ_join (typ_subst X U T1) (typ_subst X U T2).
Proof.
  auto.
Qed.

Lemma typ_subst_or : forall X U T1 T2,
  typ_subst X U (typ_or T1 T2) =
  typ_or (typ_subst X U T1) (typ_subst X U T2).
Proof.
  auto.
Qed.

Lemma typ_subst_bot : forall X U cs,
  typ_subst X U (typ_bot cs) =
  typ_bot cs.
Proof.
  auto.
Qed.

Lemma typ_subst_top : forall X U cs,
  typ_subst X U (typ_bot cs) =
  typ_bot cs.
Proof.
  auto.
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
  rewrite sch_substs_instance; auto.
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

(** Types are stable by type substitution *)

Lemma typ_subst_type : forall T Z U,
  type U -> type T -> type (typ_subst Z U T).
Proof.
  induction 2; simpls*. case_var*.
Qed.

Hint Resolve typ_subst_type.

(** Types are stable by iterated type substitution *)

Lemma typ_substs_types : forall Xs Us T,
  types (length Xs) Us ->
  type T ->
  type (typ_substs Xs Us T).
Proof.
  induction Xs; destruct Us; simpl; introv TU TT; auto.
  destruct TU. simpls. inversions H. inversions* H0.
Qed.

(** List of types are stable by type substitution *)

Lemma typ_subst_type_list : forall Z U Ts n,
  type U -> types n Ts -> 
  types n (List.map (typ_subst Z U) Ts).
Proof.
  unfold types, list_for_n.
  induction Ts; destruct n; simpl; intros TU [EQ TT]. 
  easy. easy. inversion EQ.
  inversions TT. forwards*: (IHTs n).
Qed.

(** ** Opening a body with a list of types gives a type *)

Lemma typ_open_types : forall n T Us,
  type_body n T ->
  types n Us -> 
  type (typ_open T Us).
Proof. 
  introv [L K] H. pick_freshes n Xs.
  lets Fr': Fr.
  rewrite (fresh_length _ _ _ Fr)  in H, Fr'.
  rewrite* (@typ_substs_intro Xs). apply* typ_substs_types.
Qed.

(* =============================================================== *)
(** * Properties of schemes *)

(** Substitution for a fresh name is identity. *)

Lemma sch_subst_fresh : forall X U M, 
  X \notin sch_fv M -> 
  sch_subst X U M = M.
Proof.
  intros. destruct M as [n T]. unfold sch_subst.
  rewrite* typ_subst_fresh.
Qed.

(** Trivial lemma to unfolding definition of [sch_subst] by rewriting. *)

Lemma sch_subst_fold : forall Z U T Ks,
  Sch Ks (typ_subst Z U T) = sch_subst Z U (Sch Ks T).
Proof.
  easy.
Qed. 

(** Distributivity of type substitution on opening of scheme. *)

Lemma sch_subst_open : forall Z U M Us,
   type U ->
    typ_subst Z U (sch_open M Us)
  = sch_open (sch_subst Z U M) (List.map (typ_subst Z U) Us).
Proof.
  unfold sch_open. intros. destruct M. simpl.
  rewrite* <- typ_subst_open.
Qed.

(** Distributivity of type substitution on opening of scheme with variables. *)

Lemma sch_subst_open_vars : forall Z U M Xs,
   fresh (\{Z}) (length Xs) Xs -> 
   type U ->
    typ_subst Z U (sch_open_vars M Xs)
  = sch_open_vars (sch_subst Z U M) Xs.
Proof.
  unfold sch_open_vars. intros. destruct M.
  rewrite* <- typ_subst_open_vars.
Qed.

(** Schemes are stable by type substitution. *)

Lemma sch_subst_type : forall Z U M,
  type U -> scheme M -> scheme (sch_subst Z U M).
Proof.
  unfold scheme, sch_subst, sch_arity.
  intros Z U [Ks T] TU S.
  simpls.
  destruct S as [[L H] Hk].
  split; auto.
  exists_fresh Xs Fr.
  rewrite typ_subst_open_vars; eauto.
Qed.

Hint Resolve sch_subst_type.

(** Scheme arity is preserved by type substitution. *)

Lemma sch_subst_arity : forall X U M, 
  sch_arity (sch_subst X U M) = sch_arity M.
Proof.
  easy.
Qed.

(** ** Opening a scheme with a list of types gives a type *)

Lemma sch_open_types : forall M Us,
  scheme M ->
  types (sch_arity M) Us ->
  type (sch_open M Us).
Proof.
  intros [Ks T] Us [Hb Hk] [Ha Ht].
  simpls. apply* typ_open_types.
Qed.

Hint Resolve sch_open_types.

(* =============================================================== *)
(** * Properties of environment *)

Lemma environment_typ_push_inv : forall E x M,
    environment (E & x ~ (bind_typ M)) ->
    environment E /\ x # E /\ scheme M.
Proof.
  introv H.
  inverts H as H1 H2 H3 H4.
  - false (empty_push_inv H1).
  - destruct (eq_push_inv H4) as [_ [Hv _]].
    false Hv.
  - destruct (eq_push_inv H4) as [Hx [Hv He]].
    inversion Hv.
    subst.
    easy.
Qed.

Lemma environment_kind_push_inv : forall E x K,
    environment (E & x ~ (bind_knd K)) ->
    environment E /\ x # E /\ kind K.
Proof.
  introv H.
  inverts H as H1 H2 H3 H4.
  - false (empty_push_inv H1).
  - destruct (eq_push_inv H4) as [Hx [Hk He]].
    inversion Hk.
    subst.
    easy.
  - destruct (eq_push_inv H4) as [_ [Hv _]].
    false Hv.
Qed.

Lemma environment_typ_middle_inv : forall E x M F,
    environment (E & x ~ (bind_typ M) & F) ->
    environment (E & F) /\ x # E /\ scheme M.
Proof.
  introv H.
  induction F using env_ind; rew_env_concat.
  - rewrite concat_empty_r in H.
    destruct* (environment_typ_push_inv H).
  - rewrite concat_assoc in H.
    destruct v.
    + destruct* (environment_kind_push_inv H).
    + destruct* (environment_typ_push_inv H).
Qed.

Lemma environment_kind_middle_inv : forall E x K F,
    environment (E & x ~ (bind_knd K) & F) ->
    environment (E & F) /\ x # E /\ kind K.
Proof.
  introv H.
  induction F using env_ind; rew_env_concat.
  - rewrite concat_empty_r in H.
    destruct* (environment_kind_push_inv H).
  - rewrite concat_assoc in H.
    destruct v.
    + destruct* (environment_kind_push_inv H).
    + destruct* (environment_typ_push_inv H).
Qed.

Lemma environment_concat_inv : forall E F G,
    environment (E & F & G) -> environment (E & G).
Proof.
  intros E F G.
  induction F using env_ind; rew_env_concat; auto.
  intro H.
  destruct v.
  - destruct* (environment_kind_middle_inv H).
  - destruct* (environment_typ_middle_inv H).
Qed.

Lemma environment_concat_inv_l : forall E F,
  environment (E & F) ->
  environment E.
Proof.
  introv H.
  rewrite <- (concat_empty_r F) in H.
  rewrite concat_assoc in H.
  rewrite <- (concat_empty_r E).
  apply (environment_concat_inv H).
Qed.

Lemma environment_concat_inv_r : forall E F,
  environment (E & F) ->
  environment F.
Proof.
  introv H.
  rewrite <- (concat_empty_l E) in H.
  rewrite <- (concat_empty_l F).
  apply (environment_concat_inv H).
Qed.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H: environment (E & _) |- _ =>
      apply (environment_concat_inv_l H)
  | H: environment (_ & E) |- _ =>
      apply (environment_concat_inv_r H)
  end.

Lemma environment_subst_inv_r : forall E F X T,
  environment (E & F) ->
  type T ->
  environment (E & environment_subst X T F).
Proof.
  introv He Ht.
  unfold environment_subst.
  induction F using env_ind;
    rew_env_concat; autorewrite with rew_env_map; auto.
  rewrite concat_assoc in *.
  destruct v; simpl.
  - destruct (environment_kind_push_inv He).
    apply* environment_knd.
  - destruct (environment_typ_push_inv He).
    apply*  environment_typ.
Qed.

Lemma environment_subst_empty : forall X T,
    environment_subst X T empty = empty.
Proof.
  intros.
  unfold environment_subst.
  rewrite map_empty.
  auto.
Qed.

Lemma environment_subst_push : forall X T E Y B,
    environment_subst X T (E & Y ~ B)
    = environment_subst X T E & Y ~ binding_subst X T B.
Proof.
  intros.
  unfold environment_subst.
  rewrite map_push.
  auto.
Qed.

Lemma dom_environment_subst : forall X T E,
    dom (environment_subst X T E) = dom E.
Proof.
  intros.
  unfold environment_subst.
  rewrite dom_map.
  easy.
Qed.

Lemma environment_subst_kinds : forall X T E Xs Ks,
    fresh \{X} (length Ks) Xs ->
    environment_subst X T (E & Xs ~::* Ks) =
    environment_subst X T E & Xs ~::* Ks.
Proof.
  introv Hf.
  unfold environment_subst.
  rewrite map_concat.
  lets Hlx : (eq_sym (fresh_length _ _ _ Hf)).
  gen Ks.
  induction Xs; destruct Ks;
    introv Hf Hl; tryfalse; auto.
  - rewrite singles_nil.
    rewrite! map_empty.
    easy.
  - inversion Hl.
    rewrite singles_cons.
    rewrite! map_push.
    simpl binding_subst.
    rewrite! concat_assoc.
    rewrite* IHXs.
    destruct* Hf.
Qed.   
    
Lemma environment_substs_empty : forall Xs Ts,
    length Xs = length Ts ->
    environment_substs Xs Ts empty = empty.
Proof.
  introv Hl.
  gen Ts.
  induction Xs; destruct Ts; intros; tryfalse; auto.
  simpl.
  rewrite environment_subst_empty.
  auto.
Qed.

Lemma environment_substs_push : forall Xs Ts E Y B,
    environment_substs Xs Ts (E & Y ~ B)
    = environment_substs Xs Ts E & Y ~ binding_substs Xs Ts B.
Proof.
  intros.
  gen E Ts B.
  induction Xs; destruct Ts; intros; tryfalse; auto.
  simpl.
  rewrite environment_subst_push.
  apply IHXs.
Qed.

Lemma dom_environment_substs : forall Xs Ts E,
    dom (environment_substs Xs Ts E) = dom E.
Proof.
  intros.
  gen Ts E.
  induction Xs; destruct Ts; intros; tryfalse; auto.
  simpl.
  rewrite IHXs.
  apply dom_environment_subst.
Qed.

Lemma fresh_kinds : forall E x n Xs Ks,
    fresh (dom E) (S n) (x :: Xs) ->
    length Xs = length Ks ->
    x # (E & Xs ~::* Ks).
Proof.
  introv Hf.
  destruct Hf as [Hu Hx].
  rewrite dom_concat.
  rewrite notin_union.
  split*.
  rewrite dom_map.
  rewrite dom_singles.
  - eapply fresh_single_notin.
    eapply fresh_union_r2.
    apply Hx.
  - { clear Hx.
      gen Ks.
      - induction Xs.
        + induction Ks; intros; tryfalse; auto.
        + induction Ks; intros; tryfalse.
          rewrite! LibList.length_cons.
          f_equal*. }
Qed.

Lemma environment_kinds : forall E n Xs Ks,
    environment E ->
    (fresh (dom E) n Xs) ->
    length Ks = n ->
    Forall kind Ks ->
    environment (E & Xs ~::* Ks).
Proof.
  introv He Hf Hlk.
  lets Hlx : (eq_sym (fresh_length _ _ _ Hf)).
  gen Ks n.
  induction Xs; destruct Ks;
    intros; subst; tryfalse; rew_kinds*.
  apply environment_knd.
  - eapply IHXs; iauto.
    + destruct* Hf.
    + inversion H; auto.
  - inversion H; auto.
  - eapply fresh_kinds; auto.
Qed.

(** Binding substitution is identity on bind_kind. *)

Lemma binding_subst_kind : forall x T K,
  binding_subst x T (bind_knd K) = bind_knd K.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma binds_subst_inv_r : forall E F X Y T K,
    binds X (bind_knd K) (E & F) ->
    binds X (bind_knd K) (E & environment_subst Y T F).
Proof.
  introv H.
  unfolds environment_subst.
  destruct (binds_concat_inv H).
  - apply binds_concat_right.
    erewrite <- binding_subst_kind .
    apply* binds_map.
  - apply* binds_concat_left.
Qed.

Hint Resolve binds_subst_inv_r.

Lemma binds_environment_subst : forall E F X T K x M,
    binds x (bind_typ M) (E & X ~:: K & F) ->
    X \notin (env_fv E) ->
    binds x (bind_typ (sch_subst X T M))
          (E & environment_subst X T F).
Proof.
  introv Hb Hn.
  destruct (binds_concat_inv Hb) as [Hbf | [Hf Hbex]].
  - apply binds_concat_right.
    unfold environment_subst.
    fold (binding_subst X T (bind_typ M)).
    apply* binds_map.
  - apply binds_concat_left.
    + { destruct (binds_concat_inv Hbex) as [Hbx | [_ Hbe]].
        - destruct (binds_single_inv Hbx).
          tryfalse.
        - rewrite* sch_subst_fresh.
          fold (bind_fv (bind_typ M)).
          apply fv_in_values_binds with (x := x) (E := E); auto. }
    + rewrite* dom_environment_subst.
Qed.

Hint Resolve binds_environment_subst.

Lemma ok_from_environment : forall E,
  environment E -> ok E.
Proof.
  introv He.
  induction He; auto. 
Qed.

Hint Resolve ok_from_environment.

Lemma scheme_from_env : forall E x M,
    environment E ->
    binds x (bind_typ M) E ->
    scheme M.
Proof.
  introv He Hb.
  induction E using env_ind; rew_env_concat.
  - false (binds_empty_inv Hb).
  - destruct (binds_push_inv Hb)
      as [ [ Hvar Hbind ] | [ Hvar Hbind ] ].
    + { subst.
        inversion He.
        - false (empty_push_inv H0).
        - destruct (eq_push_inv H) as [_ [Heq _]].
          false Heq.
        - destruct (eq_push_inv H) as [_ [Heq _]].
          inversion Heq.
          subst*. }
    + eapply IHE; auto.
Qed.

Lemma kind_from_env : forall E x K,
    environment E ->
    binds x (bind_knd K) E ->
    kind K.
Proof.
  introv He Hb.
  induction E using env_ind; rew_env_concat.
  - false (binds_empty_inv Hb).
  - destruct (binds_push_inv Hb)
      as [ [ Hvar Hbind ] | [ Hvar Hbind ] ].
    + { subst.
        inversion He.
        - false (empty_push_inv H0).
        - destruct (eq_push_inv H) as [_ [Heq _]].
          inversion Heq.
          subst*.
        - destruct (eq_push_inv H) as [_ [Heq _]].
          false Heq. }
    + eapply IHE; auto.
Qed.

Lemma kinds_from_env : forall E Xs Ks,
    environment (E & Xs ~::* Ks) ->
    length Xs = length Ks ->
    kinds (length Ks) Ks.
Proof.
  introv He Hl.
  split*.
  gen Xs.
  induction Ks; introv He Hl; auto.
  destruct Xs; tryfalse.
  rew_kinds in He.
  inversion He.
  - apply empty_push_inv in H0.
    tryfalse.
  - destruct (eq_push_inv H) as [? [Hb ?]].
    inversion Hb.
    inversion Hl.
    subst.
    eauto.
  - destruct (eq_push_inv H) as [_ [Hb _]].
    tryfalse.
Qed.

Lemma env_fv_empty :
  env_fv empty = \{}.
Proof.
  unfold env_fv, fv_in_values.
  rew_env_defs.
  simpl.
  auto.
Qed.

Lemma env_fv_push_inv : forall E X B,
    env_fv (E & X ~ B) = bind_fv B \u env_fv E.
Proof.
  intros.
  unfold env_fv, fv_in_values.
  rewrite values_def.
  rewrite <- cons_to_push.
  rewrite LibList.map_cons.
  simpl.
  auto.
Qed.

(** Substitution for a fresh name is identity. *)

Lemma binding_subst_fresh : forall X U B, 
  X \notin bind_fv B -> 
  binding_subst X U B = B.
Proof.
  intros.
  destruct B; simpl; auto.
  f_equal.
  simpl in H.
  apply sch_subst_fresh.
  assumption.
Qed.

Lemma binding_substs_fresh : forall Xs Us B, 
  fresh (bind_fv B) (length Xs) Xs ->
  binding_substs Xs Us B = B.
Proof.
  intros.
  gen Us.
  induction Xs; intros; auto.
  destruct Us; auto.
  simpl in H.
  simpl.
  rewrite* binding_subst_fresh.
Qed.

Lemma environment_subst_fresh : forall X U E, 
  X \notin env_fv E -> 
  environment_subst X U E = E.
Proof.
  intros.
  unfold environment_subst.
  induction E using env_ind.
  - rewrite* map_empty.
  - rewrite env_fv_push_inv in H.
    rewrite notin_union in H.
    rewrite map_push.
    rewrite* binding_subst_fresh.
    rewrite* IHE.
Qed.

Lemma environment_substs_fresh : forall Xs Us E, 
  fresh (env_fv E) (length Xs) Xs ->
  environment_substs Xs Us E = E.
Proof.
  intros.
  gen Us.
  induction Xs; intros; auto.
  destruct Us; auto.
  simpl in H.
  simpl.
  rewrite* environment_subst_fresh.
Qed.

Hint Rewrite in_empty in_singleton in_union : rew_in.

Tactic Notation "rew_in" :=
  autorewrite with rew_in.

Tactic Notation "rew_in" "in" hyp(H) :=
  autorewrite with rew_in in H.

Lemma typ_fv_open_vars : forall T Xs X,
    X \in typ_fv T ->
    X \in typ_fv (typ_open_vars T Xs).
Proof.
  introv Hfv.
  unfold typ_open_vars, typ_fvars.
  induction T;
    simpl; simpl in Hfv; rew_in; rew_in in Hfv; iauto.
Qed.

Lemma kinding_closed : forall E T K X,
    kinding E T K ->
    X \in typ_fv T ->
    X \in dom E.
Proof.
  introv Hk Hfv.
  induction Hk; simpl in Hfv; rew_in in Hfv; iauto.
  subst.
  eapply get_some_inv.
  apply H0.
Qed.

Lemma kinding_scheme_closed : forall E M X,
    kinding_scheme E M ->
    X \in sch_fv M ->
    X \in dom E.
Proof.
  introv Hks Hfv.
  unfold kinding_scheme, kinding_body in Hks.
  unfold sch_fv in Hfv.
  destruct Hks as [L Hk].
  pick_freshes (sch_arity M) Xs.
  destruct Hk with Xs as [_ Hkk]; auto.
  eapply kinding_closed with (X := X) in Hkk; auto.
  - rewrite dom_concat in Hkk.
    rew_in in Hkk.
    destruct* Hkk.
    rewrite dom_map in H.
    rewrite dom_singles in H.
    + assert (fresh \{X} (sch_arity M) Xs) by auto.
      eapply fresh_single_notin in H; auto.
      tryfalse.
    + apply fresh_length in Fr.
      unfold sch_arity in Fr.
      rewrite! liblist_length_eq_length.
      auto.
  - apply* typ_fv_open_vars.
Qed.

Lemma kinding_env_closed : forall E X,
    kinding_env E ->
    X \in env_fv E ->
    X \in dom E.
Proof.
  introv Hk Hfv.
  induction Hk.
  - rewrite env_fv_empty in Hfv.
    rew_in in Hfv.
    iauto.
  - rewrite env_fv_push_inv in Hfv.
    rewrite dom_push.
    rew_in.
    right.
    rew_in in Hfv.
    destruct* Hfv.
  - rewrite env_fv_push_inv in Hfv.
    rewrite dom_push.
    rew_in.
    right.
    rew_in in Hfv.
    destruct* Hfv.
    simpl in H1.
    apply kinding_scheme_closed with M; auto.
Qed.

(* =============================================================== *)
(** * Properties of judgments *)

(* *************************************************************** *)
(** ** Regularity of relations *)

(** A kinding relation is restricted to well-formed objects. *)

Lemma kinding_regular : forall E T K,
  kinding E T K -> environment E /\ type T /\ kind K.
Proof.
  split; induction H; subst;
    intuition eauto using kind_from_env with constrs.
  - inversion H3.
    inversion H5.
    auto with constrs.
Qed.

Lemma kindings_regular : forall E n Ts Ks,
  kindings E n Ts Ks ->
  environment E /\ types n Ts /\ kinds n Ks.
Proof.
  split; induction* H.
  split.
  - split.
    + simpl.
      f_equal.
      destruct IHkindings as [[Hl Ht] Hk]; auto.
    + lets [_ [Ht Hk]] : (kinding_regular H).
      lets [[_ Hts] Hks] : IHkindings.
      apply* Forall_cons.
  - split.
    + simpl.
      f_equal.
      destruct IHkindings as [_ [Hl Hks]]; auto.
    + destruct IHkindings as [_ [Hl Hks]]; auto.
      lets [_ [Ht Hk]] : (kinding_regular H).
      apply* Forall_cons.
Qed.  

Lemma kindings_length : forall E n Ts Ks,
    kindings E n Ts Ks ->
    length Ts = n /\ length Ks = n.
Proof.
  intros.
  induction H; simpl; iauto.
Qed.

Lemma kinding_body_regular : forall E n Ks T,
    kinding_body E n Ks T ->
    environment E /\ kinds n Ks /\ type_body n T.
Proof.
  introv H.
  destruct H as [L H].
  splits.
  - pick_freshes n Xs.
    destruct H with Xs as [_ Hk]; auto.
    eapply kinding_regular in Hk; auto.
    destruct* Hk.
  - pick_freshes n Xs.
    destruct H with Xs as [Hkd _]; auto.
  - exists_fresh Xs Hf.
    destruct H with Xs as [_ Hk]; auto.
    eapply kinding_regular in Hk; auto.
    destruct* Hk.
Qed.

Lemma kinding_scheme_regular : forall E M,
    kinding_scheme E M -> environment E /\ scheme M.
Proof.
  introv Hks.
  destruct (kinding_body_regular Hks) as [He [Hk Ht]].
  split; auto.
  split; auto.
Qed.

Lemma kinding_env_regular : forall E,
    kinding_env E -> environment E.
Proof.
  introv H.
  induction* H.
  apply* environment_typ.
  apply kinding_scheme_regular in H0.
  iauto.
Qed.

(* Automation of kinding regularity lemmas *)

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : kinding _ _ K |- _ =>
      apply (proj33 (kinding_regular H))
  | H1 : environment ?E, H2 : binds _ (bind_knd K) ?E |- _ =>
      apply (kind_from_env H1 H2)
  | H1 : kinding_env ?E, H2 : binds _ (bind_knd K) ?E |- _ =>
      apply (kind_from_env (kinding_env_regular H1) H2)
  end.

Hint Extern 1 (type ?T) =>
  match goal with
  | H: kinding _ T _ |- _ =>
      apply (proj32 (kinding_regular H))
  end.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H: kinding_scheme _ M |- _ =>
      apply (proj2 (kinding_scheme_regular H))
  | H1 : environment ?E, H2 : binds _ (bind_typ M) ?E |- _ =>
      apply (scheme_from_env H1 H2)
  | H1 : kinding_env ?E, H2 : binds _ (bind_typ M) ?E |- _ =>
      apply (scheme_from_env (kinding_env_regular H1) H2)
end.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H: kinding_env E |- _ =>
      apply (kinding_env_regular H)
  | H: kinding E _ _ |- _ =>
      apply (proj31 (kinding_regular H))
  | H: kindings E _ _ _ |- _ =>
      apply (proj31 (kindings_regular H))
  | H: kinding_body E _ _ _ |- _ =>
      apply (proj31 (kinding_body_regular H))
  | H: kinding_scheme E _ |- _ =>
      apply (proj1 (kinding_scheme_regular H))
  end.

Hint Extern 1 (environment (?E & ?F)) =>
  match goal with
  | H: environment (E & _ & F) |- _ =>
      apply (environment_concat_inv H)
  end.

Hint Extern 1 (kinds ?n ?Ks) =>
  match goal with
  | H: kindings _ n _ Ks |- _ =>
      apply (proj33 (kindings_regular H))
  | H : kinding_body _ n Ks _ |- _ =>
      apply (proj32 (kinding_body_regular H))
  end.

Hint Extern 1 (types ?n ?Ts) =>
  match goal with
  | H: kindings _ n Ts _ |- _ =>
      apply (proj32 (kindings_regular H))
  end.

Hint Extern 1 (type_body ?n ?T) =>
  match goal with
  | H: kinding_body _ n _ T |- _ =>
      apply (proj33 (kinding_body_regular H))
  end.

Ltac invert_kind_rec Hs :=
  try match goal with
  | [ H : kind (knd_row _) |- _ ] =>
    let b := inList H Hs in
    match b with
    | true => fail 1
    | false =>
      try invert_kind_rec (H, Hs);
      inversion H
    end
  | [ H : kinding _ _ (knd_row ?cs) |- _ ] =>
    let b := inList H Hs in
    match b with
    | true => fail 1
    | false =>
      try invert_kind_rec (H, Hs);
      let Hk := fresh "Hk" in
      assert (kind (knd_row cs))
        as Hk by (apply (proj33 (kinding_regular H)));
      inversion Hk
    end
  end.

Ltac invert_kind :=
  invert_kind_rec tt;
  subst.

Ltac invert_type_rec Hs :=
  try match goal with
  | [ H : type (typ_constructor _ _)  |- _ ] =>
    invert_type_rec_body H Hs
  | [ H : type (typ_or _ _)  |- _ ] =>
    invert_type_rec_body H Hs
  | [ H : type (typ_variant _ _)  |- _ ] =>
    invert_type_rec_body H Hs
  | [ H : type (typ_arrow _ _)  |- _ ] =>
    invert_type_rec_body H Hs
  | [ H : type (typ_meet _ _)  |- _ ] =>
    invert_type_rec_body H Hs
  | [ H : type (typ_join _ _)  |- _ ] =>
    invert_type_rec_body H Hs
  end

with invert_type_rec_body H Hs :=
  let b := inList H Hs in
  match b with
  | true => fail 1
  | false =>
    try invert_type_rec (H, Hs);
    inversion H
  end.

Ltac invert_type :=
  invert_type_rec tt;
  subst.

Lemma type_equal_step_regular : forall E T1 T2,
  type_equal_step E T1 T2 ->
  environment E ->
  (type T1 -> type T2) /\ (type T2 -> type T1).
Proof.
  introv Hs.
  induction Hs; intuition auto;
    match goal with
    | [ |- type _ ] =>
      subst;
      invert_type;
      invert_type;
      subst;
      auto
    end.
Qed.

(** Type equality preserves regularity *)

Lemma type_equal_regular : forall E T1 T2 K,
  type_equal E T1 T2 K ->
  environment E /\ type T1 /\ type T2 /\ kind K.
Proof.
  introv He.
  induction He; intuition auto.
  - destruct (type_equal_step_regular H); auto.
  - destruct (type_equal_step_regular H); auto.
Qed.

Lemma subtype_regular : forall E T1 T2,
    subtype E T1 T2 -> environment E /\ type T1 /\ type T2.
Proof.
  introv Hs.
  destruct (type_equal_regular Hs) as [ He [ _ [ Ht Hk ] ] ].
  inversion* Ht.
Qed.

(* Automation of equality regularity lemmas *)

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal _ _ _ K |- _ =>
      apply (proj44 (type_equal_regular H))
  end.

Hint Extern 1 (type ?T) =>
  match goal with
  | H: type_equal _ T _ _ |- _ =>
      apply (proj42 (type_equal_regular H))
  | H: type_equal _ _ T _ |- _ =>
      apply (proj43 (type_equal_regular H))
  | H: subtype _ T _ |- _ =>
      apply (proj32 (subtype_regular H))
  | H: subtype _ _ T |- _ =>
      apply (proj33 (subtype_regular H))
  end.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H: type_equal E _ _ _ |- _ =>
      apply (proj41 (type_equal_regular H))
  | H: subtype E _ _ |- _ =>
      apply (proj31 (subtype_regular H))
  end.

Hint Extern 1 (environment (?E & environment_subst ?X ?T ?F)) =>
  match goal with
  | H1: environment (E & X ~:: ?K & F), H2: kinding E T ?K |- _ =>
      apply (environment_subst_inv_r X
               (environment_concat_inv H1)
               (proj32 (kinding_regular H2)))
  | H1: environment (E & X ~:: ?K & F), H2: type_equal E T T ?K |- _ =>
      apply (environment_subst_inv_r X
               (environment_concat_inv H1)
               (proj41 (type_equal_regular H2)))
  | H1: environment (E & X ~:: _ & F), H2: type T |- _ =>
      apply (environment_subst_inv_r X (environment_concat_inv H1) H2)
  | H1: environment (E & F), H2: type T |- _ =>
      apply (environment_subst_inv_r X H1 H2)
  end.

(** A typing relation is restricted to well-formed objects. *)

Lemma typing_regular : forall E e T,
  typing E e T -> environment E /\ term e /\ type T.
Proof.
  splits 3.
  - induction* H.
    pick_freshes (sch_arity M) Xs.
    eapply environment_concat_inv_l.
    apply* H0.
  - induction H; eauto.
  - induction* H.
    inversion* IHtyping1.
Qed.

Lemma typing_scheme_regular : forall E e M,
    typing_scheme E e M -> environment E /\ term e /\ scheme M.
Proof.
  unfold typing_scheme.
  introv [Hks [L Ht]].
  splits*.
  - pick_freshes (sch_arity M) Xs.
    eapply typing_regular in Ht; auto.
    eapply environment_concat_inv_l; iauto.
  - pick_freshes (sch_arity M) Xs.
    eapply typing_regular in Ht; iauto.
  - unfold scheme, type_body.
    split*.
    exists L.
    introv Hf.
    eapply typing_regular in Ht; iauto.
Qed.

(** Automation of typing regularity lemma *)

Hint Extern 1 (environment ?E) =>
  match goal with
  | H: typing E _ _ |- _ =>
      apply (proj31 (typing_regular H))
  | H: typing_scheme E _ _ |- _ =>
      apply (proj31 (typing_scheme_regular H))
  end.

Hint Extern 1 (term ?e) =>
  match goal with
  | H: typing _ e _ |- _ =>
      apply (proj32 (typing_regular H))
  | H: typing_scheme _ e _ |- _ =>
      apply (proj32 (typing_scheme_regular H))
  end.

Hint Extern 1 (type ?T) =>
  match goal with
  | H: typing _ _ T |- _ =>
      apply (proj33 (typing_regular H))
  end.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H: typing_scheme _ _ M |- _ =>
      apply (proj33 (typing_scheme_regular H))
  end.

(** The value predicate is restricted to well-formed terms. *)

Lemma value_regular : forall e,
  value e -> term e.
Proof.
  introv Hv.
  induction* Hv.
Qed.

Hint Resolve value_regular.

(** A reduction relation is restricted to well-formed terms. *)

Lemma red_regular : forall e e',
  red e e' -> term e /\ term e'.
Proof.
  introv Hr.
  induction Hr; iauto.
  inversion* H0.
Qed.

Hint Extern 1 (term ?t) =>
  match goal with
  | H: red t _ |- _ => apply (proj1 (red_regular H))
  | H: red _ t |- _ => apply (proj2 (red_regular H))
  end.