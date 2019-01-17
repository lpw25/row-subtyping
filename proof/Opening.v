(************************************************
 *          Row Subtyping - Opening             *
 *                 Leo White                    *
 ************************************************)

(* Some lemmas relating to opening and local closure *)

Set Implicit Arguments.
Require Import List LibLN Cofinite Disjoint Utilities
        Definitions.

(* *************************************************************** *)
(** * Terms *)

(** Open with nil is the identity. *)

Lemma var_open_nil : forall k n t,
    var_open k nil n t = t.
Proof.
  intros.
  generalize dependent n.
  induction k; destruct n; simpl; auto.
Qed.
  
Lemma trm_open_rec_nil : forall t k,
    trm_open_rec k nil t = t.
Proof.
  intros.
  generalize dependent k.
  induction t; intros; simpl;
    rewrite? IHt; rewrite? IHt1; rewrite? IHt2; rewrite? IHt3;
    rewrite? var_open_nil; auto.
Qed.

Lemma trm_open_nil : forall t,
    trm_open t nil = t.
Proof.
  unfold trm_open.
  auto using trm_open_rec_nil.
Qed.

(** Substitution on indices is identity on well-formed
    terms. *)

Lemma var_open_below_domain : forall n k us t,
    n < k ->
    var_open k us n t = t.
Proof.
  unfold lt.
  introv Hle.
  generalize dependent n.
  induction k; introv Hle.
  - inversion Hle.
  - destruct n; simpl; auto with arith.
Qed.

Lemma var_open_above_domain : forall n k us t,
    n >= k + length us ->
    var_open k us n t = t.
Proof.
  unfold gt, lt.
  introv Hle.
  generalize dependent n.
  induction k; introv Hle; simpl.
  - auto using nth_overflow.
  - destruct n; simpl; auto with arith.
Qed.
    
Lemma var_open_rec_core :forall n j vs i us,
    j + length vs <= i ->
    var_open j vs n (trm_bvar n)
    = {i ~> us}(var_open j vs n (trm_bvar n)) ->
    trm_bvar n = var_open i us n (trm_bvar n).
Proof.
  introv Hlt Heq.
  destruct (Compare_dec.le_lt_dec (j + length vs) n).
  - rewrite var_open_above_domain in Heq; auto.
  - rewrite var_open_below_domain; auto.
    Omega.omega.
Qed.    

Lemma trm_open_rec_core :forall t j vs i us,
    j + length vs <= i ->
    {j ~> vs}t = {i ~> us}({j ~> vs}t) ->
    t = {i ~> us}t.
Proof.
  induction t; introv Hl Heq; simpl in *;
    assert (S j + length vs <= S i) by Omega.omega;
    assert (S (S j) + length vs <= S (S i)) by Omega.omega;
    inversion Heq; f_equal; eauto using var_open_rec_core.
Qed.

Lemma trm_open_rec : forall t us,
  term t -> forall k, t = {k ~> us}t.
Proof.
  introv Ht.
  induction Ht; intro; simpl; f_equal; auto.
  - pick_fresh_gen L x.
    apply trm_open_rec_core with (j := 0) (vs := (trm_fvar x)::nil);
      simpl; try Omega.omega; eauto.
  - pick_fresh_gen L x.
    apply trm_open_rec_core with (j := 0) (vs := (trm_fvar x)::nil);
      simpl; try Omega.omega; eauto.
  - pick_fresh_gen L x.
    apply trm_open_rec_core with (j := 0) (vs := (trm_fvar x)::nil);
      simpl; try Omega.omega; eauto.
  - pick_fresh_gen L x.
    apply trm_open_rec_core with (j := 0) (vs := (trm_fvar x)::nil);
      simpl; try Omega.omega; eauto.
  - pick_fresh_gen L x.
    apply trm_open_rec_core with (j := 0) (vs := (trm_fvar x)::nil);
      simpl; try Omega.omega; eauto.
  - pick_fresh_gen L x. pick_fresh_gen (L \u \{x}) y.
    apply trm_open_rec_core
      with (j := 0) (vs := (trm_fvar y)::(trm_fvar x)::nil);
      simpl; try Omega.omega.
    assert
      (forall k : nat,
        t ^* y :: x :: nil = {k ~> us} (t ^* y :: x :: nil)) as IH
        by auto.
    apply IH; auto.
Qed.

(* *************************************************************** *)
(** * Types *)

(** Types of fvars *)
Lemma types_fvars : forall Xs,
    types (typ_fvars Xs).
Proof.
  induction Xs; simpl; auto.
Qed.

Hint Resolve types_fvars.

(** Length of typ_fvars *)

Lemma length_typ_fvars : forall Xs,
    length (typ_fvars Xs) = length Xs.
Proof.
  intros.
  induction Xs; simpl; auto.
Qed.

(** Open with nil is the identity. *)

Lemma typ_open_nil : forall T,
    typ_open T nil = T.
Proof.
  intros.
  induction T; simpl;
    rewrite? IHT; rewrite? IHT1; rewrite? IHT2; auto.
  - destruct n; auto.
Qed.

Lemma typ_open_vars_nil : forall T,
    typ_open_vars T nil = T.
Proof.
  intros.
  unfold typ_open_vars.
  apply typ_open_nil.
Qed.

(** Open on a type is the identity. *)

Lemma typ_open_type : forall T Us,
  type T -> T = typ_open T Us.
Proof.
  introv Htyp.
  induction Htyp; simpl; rewrite <- ? IHHtyp;
    rewrite <- ? IHHtyp1; rewrite <- ? IHHtyp2; auto.
Qed.

(* Bounds of ranges are types *)

Lemma rng_lower_type : forall R,
  range R ->
  type (rng_lower R).
Proof.
  introv Hr.
  destruct Hr; simpl; auto.
Qed.

Lemma rng_upper_type : forall R,
  range R ->
  type (rng_upper R).
Proof.
  introv Hr.
  destruct Hr; simpl; auto.
Qed.

(* *************************************************************** *)
(** * Kinds *)

Lemma rng_kind_kind : forall R,
  range R ->
  kind (rng_kind R).
Proof.
  introv Hr.
  destruct Hr; simpl; auto.
Qed.

Lemma rngs_kinds_kinds : forall R,
  ranges R ->
  kinds (rngs_kinds R).
Proof.
  introv Hrs.
  induction Hrs; simpl; auto using rng_kind_kind.
Qed.

(** Range lists have kinds of the same length *)

Lemma length_rngs_kinds : forall Rs,
    length Rs = length (rngs_kinds Rs).
Proof.
  intros.
  induction Rs; simpl; auto.
Qed.

Lemma kind_row_all :
  kind knd_row_all.
Proof.
  auto with csetdec.
Qed.

Hint Resolve kind_row_all.

(* *************************************************************** *)
(** * Ranges *)

Lemma rng_open_list_length : forall Rs Us,
    length (rng_open_list Rs Us) = length Rs.
Proof.
  intros.
  induction Rs; simpl; auto.
Qed.

Lemma rng_open_vars_list_length : forall Rs Xs,
    length (rng_open_vars_list Rs Xs) = length Rs.
Proof.
  unfold rng_open_vars_list.
  auto using rng_open_list_length.
Qed.

(** Open with nil is the identity. *)

Lemma rng_open_nil : forall R,
    rng_open R nil = R.
Proof.
  intros.
  destruct R; unfold rng_open; simpl.
  f_equal; rewrite typ_open_nil; auto.
Qed.

Lemma rng_open_vars_nil : forall R,
    rng_open_vars R nil = R.
Proof.
  intros.
  unfold rng_open_vars.
  apply rng_open_nil.
Qed.

Lemma rng_open_list_nil : forall Rs,
    rng_open_list Rs nil = Rs.
Proof.
  intros.
  induction Rs; simpl; auto.
  rewrite rng_open_nil.
  rewrite IHRs.
  auto.
Qed.

Lemma rng_open_vars_list_nil : forall Rs,
    rng_open_vars_list Rs nil = Rs.
Proof.
  intros.
  unfold rng_open_vars_list.
  apply rng_open_list_nil.
Qed.

(** Open on a range is the identity. *)

Lemma rng_open_range : forall R Us,
  range R -> R = rng_open R Us.
Proof.
  introv Hr.
  induction Hr; unfold rng_open; simpl; auto.
  rewrite <- typ_open_type; auto.
  rewrite <- typ_open_type; auto.
Qed.

Lemma rng_open_ranges : forall Rs Us,
    ranges Rs -> Rs = rng_open_list Rs Us.
Proof.
  introv Hr.
  induction Hr; simpl; f_equal; auto using rng_open_range.
Qed.

(** Length of range list not affected by opening *)

Lemma length_rng_open_list : forall Rs Us,
    length Rs = length (rng_open_list Rs Us).
Proof.
  intros.
  unfold rng_open_list.
  rewrite List.map_length.
  reflexivity.
Qed.

Lemma length_rng_open_vars_list : forall Rs Xs,
    length Rs = length (rng_open_vars_list Rs Xs).
Proof.
  intros.
  unfold rng_open_vars_list.
  unfold rng_open_list.
  rewrite List.map_length.
  reflexivity.
Qed.

(** Kind of a range not affected by opening *)

Lemma rng_kind_open : forall R Us,
  rng_kind R = rng_kind (rng_open R Us).
Proof.
  intros.
  induction R; simpl; auto.
Qed.

Lemma rng_kind_open_vars : forall R Xs,
  rng_kind R = rng_kind (rng_open_vars R Xs).
Proof.
  intros.
  induction R; simpl; auto.
Qed.

(** Kinds of a range list not affected by opening *)

Lemma rngs_kinds_open_list : forall Rs Us,
  rngs_kinds Rs = rngs_kinds (rng_open_list Rs Us).
Proof.
  intros.
  induction Rs; simpl; auto.
  f_equal; auto using rng_kind_open.
Qed.

Lemma rngs_kinds_open_vars_list : forall Rs Xs,
  rngs_kinds Rs = rngs_kinds (rng_open_vars_list Rs Xs).
Proof.
  intros.
  induction Rs; simpl; auto.
  f_equal; auto using rng_kind_open.
Qed.

(* *************************************************************** *)
(** * Schemes *)

Lemma sch_arity_length : forall M,
    sch_arity M = length (sch_ranges M).
Proof.
  intros.
  destruct M as [Rs T].
  simpl.
  reflexivity.
Qed.

Lemma instance_empty_nil : forall T,
  instance (sch_empty T) nil = T.
Proof.
  intros.
  unfold instance.
  rewrite typ_open_nil.
  auto.
Qed.

Lemma instance_vars_empty_nil : forall T,
  instance_vars (sch_empty T) nil = T.
Proof.
  intros.
  unfold instance_vars; simpl.
  apply instance_empty_nil.
Qed.

Lemma scheme_empty_type : forall T,
    type T <-> scheme (sch_empty T).
Proof.
  split.
  - introv Ht.
    apply scheme_c with (L := \{}).
    apply scheme_aux_c.
    simpl.
    introv Fr.
    fresh_length Fr as Hl.
    destruct Xs; try discriminate.
    rewrite instance_vars_empty_nil.
    auto.
  - introv Hs.
    inversion Hs as [L ? Hsa]; subst.
    inversion Hsa as [? ? H]; subst.
    simpl in H.
    specialize (H nil I).
    rewrite instance_vars_empty_nil in H.
    destruct H.
    auto.
Qed.

Lemma scheme_for_empty_type : forall T,
    type T -> scheme (sch_empty T).
Proof.
  introv Ht.
  rewrite <- scheme_empty_type.
  assumption.
Qed.

Hint Resolve scheme_for_empty_type.

