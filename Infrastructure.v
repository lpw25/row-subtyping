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
  | typ_variant T1 T2 => (typ_fv T1) \u (typ_fv T2)
  | typ_arrow T1 T2 => (typ_fv T1) \u (typ_fv T2)
  | typ_top => \{}
  | typ_bot => \{}
  | typ_meet T1 T2 => (typ_fv T1) \u (typ_fv T2)
  | typ_join T1 T2 => (typ_fv T1) \u (typ_fv T2)
  end.

(** Computing free variables of a list of terms. *)

Definition typ_fv_list :=
  fold_right (fun t acc => typ_fv t \u acc) \{}.

(** Computing free variables of a type scheme. *)

Definition sch_fv M := 
  typ_fv (sch_type M).

(** Computing free type variables of the values of an environment. *)

Definition bind_fv (B : bind) : vars :=
  match B with
  | bind_kind K => \{}
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
  | typ_variant T1 T2 =>
      typ_variant (typ_subst Z U T1) (typ_subst Z U T2)
  | typ_arrow T1 T2 =>
      typ_arrow (typ_subst Z U T1) (typ_subst Z U T2)
  | typ_top => typ_top
  | typ_bot => typ_bot
  | typ_meet T1 T2 =>
      typ_meet (typ_subst Z U T1) (typ_subst Z U T2)
  | typ_join T1 T2 =>
      typ_join (typ_subst Z U T1) (typ_subst Z U T2)
  end.

(** Iterated substitution for types  *)

Fixpoint typ_substs (Zs : list var) (Us : list typ) (T : typ)
   {struct Zs} : typ :=
  match Zs, Us with
  | Z::Zs', U::Us' => typ_substs Zs' Us' (typ_subst Z U T)
  | _, _ => T
  end.    

(** Substitution for names for schemes. *)

Definition sch_subst Z U M := 
  Sch (sch_kinds M) (typ_subst Z U (sch_type M)).

(** Iterated substitution for schemes. *)

Definition sch_substs Zs Us M := 
  Sch (sch_kinds M) (typ_substs Zs Us (sch_type M)).

(** Substitution for bindings *)
Definition binding_subst Z U B :=
  match B with
  | bind_kind K => bind_kind K
  | bind_typ M => bind_typ (sch_subst Z U M)
  end.

Definition environment_subst Z U E :=
  map (binding_subst Z U) E.

Fixpoint environment_substs (Zs : list var) (Us : list typ) (E : env)
   {struct Zs} : env :=
  match Zs, Us with
  | Z::Zs', U::Us' => environment_substs Zs' Us' (environment_subst Z U E)
  | _, _ => E
  end.    

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

Hint Constructors type term environment type_equal kinding kinding_env typing value red.

Lemma typ_def_fresh : typ_fv typ_def = \{}.
Proof.
  easy.
Qed.

Hint Extern 1 (_ \notin typ_fv typ_def) =>
  rewrite typ_def_fresh.

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

Lemma kinds_nil : forall E,
    E & nil ~::* nil = E.
Proof.    
  intro.
  rewrite singles_nil.
  rewrite map_empty.
  rewrite concat_empty_r.
  auto.
Qed.

Lemma kinds_cons : forall E X Xs K Ks,
    E & (X :: Xs) ~::* (K :: Ks) = E & Xs ~::* Ks & X ~:: K.
Proof.    
  intros.
  rewrite singles_cons.
  rewrite map_push.
  rewrite concat_assoc.
  auto.
Qed.

Hint Rewrite kinds_nil : rew_kinds.
Hint Rewrite kinds_cons : rew_kinds.

Tactic Notation "rew_kinds" :=
  autorewrite with rew_kinds.

Tactic Notation "rew_kinds" "*" :=
  autorewrite with rew_kinds; auto.

Tactic Notation "rew_kinds" "in" hyp(H) :=
  autorewrite with rew_kinds in H.

Tactic Notation "rew_kinds" "*" "in" hyp(H) :=
  autorewrite with rew_kinds in H; auto.

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

Hint Resolve body_to_term_abs body_to_term_let bodies_to_term_match.

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

Lemma typ_open_type : forall T Us,
  type T -> T = typ_open T Us.
Proof.
  introv W. induction T; simpls; inversions W; f_equal*.
Qed.

(** Substitution for a fresh name is identity. *)

Lemma typ_subst_fresh : forall X U T, 
  X \notin typ_fv T -> 
  typ_subst X U T = T.
Proof.
  intros. induction T; simpls; f_equal*. case_var*. 
Qed.

Lemma typ_subst_fresh_list : forall z u ts,
  z \notin typ_fv_list ts ->
  ts = List.map (typ_subst z u) ts.
Proof.
  induction ts; simpl; intros Fr.
  - easy.
  -
    f_equal*.
    rewrite~ typ_subst_fresh.
Qed.

Lemma typ_subst_fresh_trm_fvars : forall z u xs,
  fresh (\{z}) (length xs) xs ->
  typ_fvars xs = List.map (typ_subst z u) (typ_fvars xs).
Proof.
  intros. apply typ_subst_fresh_list.
  induction xs; simpl.
  - auto.
  - destruct H. auto.
Qed.

Lemma typ_substs_fresh : forall xs us t, 
  fresh (typ_fv t) (length xs) xs -> 
  typ_substs xs us t = t.
Proof.
  induction xs; simpl; intros us t Fr.
  easy. destruct us. easy.
  inversions Fr. rewrite* typ_subst_fresh.
Qed.

(** Substitution distributes on the open operation. *)

Lemma typ_subst_open : forall X U T1 T2, type U -> 
  typ_subst X U (typ_open T1 T2) = 
   typ_open (typ_subst X U T1) (List.map (typ_subst X U) T2).
Proof.
  intros. induction T1; intros; simpl; f_equal*.
  - symmetry. apply map_nth with (f := typ_subst X U) (d := typ_def). 
  - case_var*. apply* typ_open_type.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma typ_subst_open_vars : forall X Ys U T, 
  fresh \{X} (length Ys) Ys -> 
  type U ->
     typ_open_vars (typ_subst X U T) Ys
   = typ_subst X U (typ_open_vars T Ys).
Proof.
  introv Fr Tu. unfold typ_open_vars.
  rewrite* typ_subst_open. f_equal.
  induction Ys; simpls.
  - easy.
  - destruct Fr.
    case_var. f_equal*.
Qed.

Lemma app_last : forall A (x : A) l1 l2,
  l1 ++ (x::l2) = (l1 ++(x :: nil)) ++ l2.
Proof.
  intros.
  rewrite <- app_assoc.
  easy.
Qed.

Lemma forall_app : forall A (l1 : list A) (l2 : list A) P,
    Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof.
  introv H1 H2.
  induction* H1.
  apply* Forall_cons.
Qed.

(** Opening up an abstraction of body t with a term u is the same as
  opening up the abstraction with a fresh name x and then substituting u
  for x. *)

Lemma typ_substs_intro_ind : forall T Xs Us Vs, 
  fresh (typ_fv T \u typ_fv_list Vs \u typ_fv_list Us) (length Xs) Xs -> 
  types (length Xs) Us ->
  types (length Vs) Vs ->
  typ_open T (Vs ++ Us) =
  typ_substs Xs Us (typ_open T (Vs ++ (typ_fvars Xs))).
Proof.
  induction Xs; simpl; introv Fr Tu Tv;
   destruct Tu; destruct Us; tryfalse; auto.
  inversions H0. lets [Fr1 Fr2]: Fr. simpls.
  rewrite app_last.
  forwards K: (IHXs Us (Vs ++ (t :: nil))); clear IHXs; auto.
    { rewrite* fv_list_map. }
    { split~. apply forall_app.
      - lets* [_ Tv2] : Tv.
      - auto. }
  rewrite K. clear K. 
  f_equal. rewrite~ typ_subst_open. rewrite~ typ_subst_fresh.
  f_equal. rewrite map_app.
  simpl. case_var; tryfalse*.
  rewrite <- app_last. 
  f_equal.
  - apply~ typ_subst_fresh_list.
  - f_equal. apply* typ_subst_fresh_trm_fvars.
Qed.

Lemma typ_substs_intro : forall Xs Us T, 
  fresh (typ_fv T \u typ_fv_list Us) (length Xs) Xs -> 
  types (length Xs) Us ->
  (typ_open T Us) = typ_substs Xs Us (typ_open_vars T Xs).
Proof.
  intros. apply* (@typ_substs_intro_ind T Xs Us nil).
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

Lemma fresh_length : forall L n xs,
  fresh L n xs -> n = length xs.
Proof using.
  intros. gen n L. induction xs; simpl; intros n L Fr;
    destruct n; tryfalse*.
  easy.
  f_equal.
  rewrite* <- (@IHxs n (L \u \{a})).
Qed.

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
  destruct S as [L H].
  exists_fresh Xs Fr.
  rewrite* typ_subst_open_vars.
  rewrite* (fresh_length _ _ _ Fr) in Fr.
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
  intros [Ks T] Us Hb [Ha Ht].
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
  - destruct (eq_push_inv H3) as [_ [Hv _]].
    false Hv.
  - destruct (eq_push_inv H4) as [Hx [Hv He]].
    inversion Hv.
    subst.
    easy.
Qed.

Lemma environment_kind_push_inv : forall E x K,
    environment (E & x ~ (bind_kind K)) ->
    environment E /\ x # E.
Proof.
  introv H.
  inverts H as H1 H2 H3 H4.
  - false (empty_push_inv H1).
  - destruct (eq_push_inv H3) as [Hx [_ He]].
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
    environment (E & x ~ (bind_kind K) & F) ->
    environment (E & F) /\ x # E.
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
    apply* environment_kind.
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

Lemma environment_substs_empty : forall Xs Ts,
    length Xs = length Ts ->
    environment_substs Xs Ts empty = empty.
Proof.
  introv Hl.
  gen Ts.
  induction Xs.
  - induction Ts; introv Hl; tryfalse; auto.
  - induction Ts; introv Hl; tryfalse.
    simpl.
    rewrite environment_subst_empty.
    auto.
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
    environment (E & Xs ~::* Ks).
Proof.
  introv He Hf Hlk.
  lets Hlx : (eq_sym (fresh_length _ _ _ Hf)).
  gen Ks n.
  induction Xs.
  - induction Ks; intros; subst; tryfalse.
    rew_kinds*.
  - induction Ks; intros; subst; tryfalse.
    rew_kinds.
    apply environment_kind.
    + eapply IHXs; intuition.
      destruct* Hf.
    + eapply fresh_kinds; auto.
Qed.

(** Binding substitution is identity on bind_kind. *)

Lemma binding_subst_kind : forall x T K,
  binding_subst x T (bind_kind K) = bind_kind K.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma binds_subst_inv_r : forall E F X Y T K,
    binds X (bind_kind K) (E & F) ->
    binds X (bind_kind K) (E & environment_subst Y T F).
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

(* =============================================================== *)
(** * Properties of judgments *)

(* *************************************************************** *)
(** ** Regularity of relations *)

(** A kinding relation is restricted to well-formed objects. *)

Lemma kinding_regular : forall E T K,
  kinding E T K -> environment E /\ type T.
Proof.
  split; induction* H.
Qed.

Lemma kindings_regular : forall E n Ts Ks,
  kindings E n Ts Ks -> environment E /\ types n Ts.
Proof.
  split; induction* H.
  split.
  - simpl.
    f_equal.
    destruct* IHkindings.
  - lets [_ Ht] : (kinding_regular H).
    lets [_ Hts] : IHkindings.
    apply* Forall_cons.
Qed.  

Lemma kinding_body_regular : forall E n Ks T,
    kinding_body E n Ks T ->
    environment E /\ type_body n T.
Proof.
  introv H.
  destruct H as [L H].
  split.
  - pick_freshes n Xs.
    eapply kinding_regular in H; auto.
    destruct* H.
  - exists_fresh Xs Hf.
    eapply kinding_regular in H; auto.
    destruct* H.
Qed.

Lemma kinding_scheme_regular : forall E M,
    kinding_scheme E M -> environment E /\ scheme M.
Proof.
  introv H.
  destruct (kinding_body_regular H).
  split*.
Qed.

Lemma kinding_env_regular : forall E,
    kinding_env E -> environment E.
Proof.
  introv H.
  induction* H.
  apply* environment_typ.
  eapply proj2.
  apply kinding_scheme_regular.
  apply H0.
Qed.

(* Automation of kinding regularity lemmas *)

Hint Extern 1 (type ?T) =>
  match goal with
  | H: kinding _ T _ |- _ =>
      apply (proj2 (kinding_regular H))
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
      apply (proj1 (kinding_regular H))
  | H: kindings E _ _ _ |- _ =>
      apply (proj1 (kindings_regular H))
  | H: kinding_body E _ _ _ |- _ =>
      apply (proj1 (kinding_body_regular H))
  | H: kinding_scheme E _ |- _ =>
      apply (proj1 (kinding_scheme_regular H))
  end.

Hint Extern 1 (environment (?E & ?F)) =>
  match goal with
  | H: environment (E & _ & F) |- _ =>
      apply (environment_concat_inv H)
  end.

Hint Extern 1 (types ?n ?Ts) =>
  match goal with
  | H: kindings _ n Ts _ |- _ =>
      apply (proj2 (kindings_regular H))
  end.

Hint Extern 1 (type_body ?n ?T) =>
  match goal with
  | H: kinding_body _ n _ T |- _ =>
      apply (proj2 (kinding_body_regular H))
  end.

(** Type equality preserves regularity *)

Lemma type_equal_regular : forall E T1 T2 K,
    type_equal E T1 T2 K -> environment E /\ type T1 /\ type T2.
Proof.
  introv Ht.
  induction* Ht. 
Qed.

Lemma subtype_regular : forall E T1 T2,
    subtype E T1 T2 -> environment E /\ type T1 /\ type T2.
Proof.
  introv Hs.
  destruct (type_equal_regular Hs) as [ He [ _ Ht ] ].
  inversion* Ht.
Qed.

(* Automation of equality regularity lemmas *)

Hint Extern 1 (type ?T) =>
  match goal with
  | H: type_equal _ T _ _ |- _ =>
      apply (proj32 (type_equal_regular H))
  | H: type_equal _ _ T _ |- _ =>
      apply (proj33 (type_equal_regular H))
  | H: subtype _ T _ |- _ =>
      apply (proj32 (subtype_regular H))
  | H: subtype _ _ T |- _ =>
      apply (proj33 (subtype_regular H))
  end.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H: type_equal E _ _ _ |- _ =>
      apply (proj31 (type_equal_regular H))
  | H: subtype E _ _ |- _ =>
      apply (proj31 (subtype_regular H))
  end.

Hint Extern 1 (environment (?E & environment_subst ?X ?T ?F)) =>
  match goal with
  | H1: environment (E & X ~:: ?K & F), H2: kinding E T ?K |- _ =>
      apply (environment_subst_inv_r X
               (environment_concat_inv H1)
               (proj2 (kinding_regular H2)))
  | H1: environment (E & X ~:: ?K & F), H2: type_equal E T T ?K |- _ =>
      apply (environment_subst_inv_r X
               (environment_concat_inv H1)
               (proj31 (type_equal_regular H2)))
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

(** Automation of typing regularity lemma *)

Hint Extern 1 (environment ?E) =>
  match goal with
  | H: typing E _ _ |- _ =>
      apply (proj31 (typing_regular H))
  end.

Hint Extern 1 (term ?e) =>
  match goal with
  | H: typing _ e _ |- _ =>
      apply (proj32 (typing_regular H))
  end.

Hint Extern 1 (type ?T) =>
  match goal with
  | H: typing _ _ T |- _ =>
      apply (proj33 (typing_regular H))
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
  induction* Hr.
  inversion* H.    
Qed.

Hint Extern 1 (term ?t) =>
  match goal with
  | H: red t _ |- _ => apply (proj1 (red_regular H))
  | H: red _ t |- _ => apply (proj2 (red_regular H))
  end.