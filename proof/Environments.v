(************************************************
 *          Row Subtyping - Well-formedness     *
 *                 Leo White                    *
 ************************************************)

(* Useful lemmas for manipulating environments,
   type environments and store types. *)

Set Implicit Arguments.
Require Import List PeanoNat LibLN
        Cofinite Disjoint Utilities Definitions Opening.

(* *************************************************************** *)
(** * Type environments *)

Lemma ok_from_type_environment_extension : forall E1 E2,
  type_environment_extension E1 E2 -> ok E2.
Proof.
  introv He.
  induction He; auto. 
Qed.

Lemma ok_from_type_environment : forall E,
  type_environment E -> ok E.
Proof.
  apply ok_from_type_environment_extension.
Qed.

(* Domains *)

Hint Rewrite dom_empty dom_single dom_concat : rew_tenv_dom.

Hint Rewrite from_list_nil from_list_cons : rew_tenv_dom.

Lemma tenv_dom_singles : forall Xs (Rs : list rng),
  length Xs = length Rs ->
  dom (Xs ~* Rs) = from_list Xs.
Proof.
  introv Hl.
  generalize dependent Rs.
  induction Xs; introv Hl; destruct Rs; inversion Hl;
    autorewrite with rew_env_concat;
    autorewrite with rew_tenv_dom; auto.
  rewrite union_comm.
  f_equal; auto.
Qed.

Lemma tenv_dom_ranges : forall Xs M,
  sch_arity M = length Xs ->
  dom (Xs ~: M) = from_list Xs.
Proof.
  introv Hl.
  destruct M as [Rs T].
  unfold bind_sch_ranges.
  simpl in *.
  rewrite length_rng_open_vars_list with (Xs := Xs) in Hl.
  rewrite tenv_dom_singles; auto.
Qed.

Hint Rewrite tenv_dom_singles using auto : rew_tenv_dom.

Hint Rewrite tenv_dom_ranges using auto : rew_tenv_dom.

(* Extensions to environments *)

Lemma type_environment_extension_extend : forall E1 E2 E3,
    type_environment_extension E1 E2 ->
    type_environment_extension (E1 & E2) E3 ->
    type_environment_extension E1 (E2 & E3).
Proof.
  introv He1 He2.
  remember (E1 & E2) as E12.
  induction He2; subst;
    autorewrite with rew_env_concat; auto.    
Qed.

Lemma type_environment_extend : forall E1 E2,
    type_environment E1 ->
    type_environment_extension E1 E2 ->
    type_environment (E1 & E2).
Proof.
  introv He1 He2.
  apply type_environment_extension_extend;
  autorewrite with rew_env_concat; auto.
Qed.

Lemma type_environment_extend_inv : forall E1 E2,
    type_environment (E1 & E2) ->
    type_environment_extension E1 E2.
Proof.
  introv He.
  induction E2 using env_ind;
    autorewrite with rew_env_concat in *; auto.
  inversion He; subst.
  - exfalso; eauto using empty_push_inv.
  - assert (E3 & X ~ R = E1 & E2 & x ~ v)
      as Heq by assumption.
    destruct (eq_push_inv Heq) as [? [? ?]]; subst.
    auto.
Qed.

(* Constructor for concatenations *)

Lemma type_environment_extension_concat : forall E1 E2 E3,
    type_environment_extension E1 E2 ->
    type_environment_extension E1 E3 ->
    ok (E2 & E3) ->
    type_environment_extension E1 (E2 & E3).
Proof.
  introv He1 He2 Hok.
  induction He2;
    autorewrite with rew_env_concat in *; auto.
  remember (E2 & E0 & X ~ R) as E3.
  unfold type_environment in *.
  destruct Hok; auto.
  destruct (eq_push_inv HeqE3) as [? [? ?]]; subst; auto.
Qed.

Lemma type_environment_concat : forall E1 E2,
    type_environment E1 ->
    type_environment E2 ->
    ok (E1 & E2) ->
    type_environment (E1 & E2).
Proof.
  apply type_environment_extension_concat.
Qed.

(* Constructor for reverse push *)

Lemma type_environment_extension_rev_push : forall E1 E2 X R,
    type_environment_extension E1 E2 ->
    range R ->
    X # E1 ->
    X # E2 ->
    type_environment_extension E1 (X ~ R & E2).
Proof.
  introv He Hr Hn1 Hn2.
  induction He.
  - rewrite concat_empty_r.
    rewrite <- concat_empty_l.
    auto.
  - rewrite concat_assoc.
    auto.
Qed.

(* Constructors for single, singles and sch_bind_rngs *)

Lemma type_environment_extension_single : forall E X R,
    X # E ->
    range R ->
    type_environment_extension E (X ~ R).
Proof.
  introv Hn Hr.
  rewrite <- concat_empty_l.
  auto.
Qed.

Lemma type_environment_extension_push_singles :
  forall E1 E2 Xs Rs,
    type_environment_extension E1 E2 ->
    fresh (dom E1 \u dom E2) (length Rs) Xs ->
    ranges Rs ->
    type_environment_extension E1 (E2 & Xs ~* Rs).
Proof.
  introv He Hf Hrs.
  generalize dependent Rs.
  generalize dependent E2.
  induction Xs; introv He Hf Hrs; simpl.
  - rewrite (fresh_length_nil _ _ Hf).
    rewrite singles_nil.
    autorewrite with rew_env_concat; auto.
  - destruct Rs; simpl in *; destruct Hf.
    inversion Hrs; subst.
    autorewrite with rew_env_concat.
    apply type_environment_extension_push;
      autorewrite with rew_tenv_dom; try symmetry;
        eauto using fresh_length.
Qed.

Lemma type_environment_extension_singles : forall E Xs Rs,
    fresh (dom E) (length Rs) Xs ->
    ranges Rs ->
    type_environment_extension E (Xs ~* Rs).
Proof.
  introv Hf Hrs.
  rewrite <- concat_empty_l.
  apply type_environment_extension_push_singles;
    autorewrite with rew_tenv_dom; auto.
Qed.

Lemma type_environment_push_singles : forall E Xs Rs,
    type_environment E ->
    fresh (dom E) (length Rs) Xs ->
    ranges Rs ->
    type_environment (E & Xs ~* Rs).
Proof.
  introv He Hf Hrs.
  apply type_environment_extension_push_singles;
    autorewrite with rew_env_dom; auto.
Qed.

Lemma type_environment_singles : forall Xs Rs,
    fresh \{} (length Rs) Xs ->
    ranges Rs ->
    type_environment (Xs ~* Rs).
Proof.
  introv Hf Hrs.
  rewrite <- concat_empty_l.
  apply type_environment_push_singles;
    autorewrite with rew_tenv_dom; auto.
Qed.

Lemma type_environment_extension_push_ranges :
  forall L E1 E2 Xs M,
    type_environment_extension E1 E2 ->
    scheme_aux L M ->
    fresh (dom E1 \u dom E2 \u L) (sch_arity M) Xs ->
    type_environment_extension E1 (E2 & Xs ~: M).
Proof.
  introv He Hs Hf.
  destruct Hs as [? ? H].
  destruct M as [Rs T].
  unfold bind_sch_ranges.
  simpl in *.
  apply type_environment_extension_push_singles;
    rewrite ?rng_open_vars_list_length; auto.
  assert (ranges_and_type (rng_open_vars_list Rs Xs)
            (instance_vars (Sch Rs T) Xs)) as Hrt by auto.
  destruct Hrt; auto.
Qed.

Lemma type_environment_push_ranges : forall L E Xs M,
    type_environment E ->
    scheme_aux L M ->
    fresh (dom E \u L) (sch_arity M) Xs ->
    type_environment (E & Xs ~: M).
Proof.
  introv He Hs Hf.
  apply type_environment_extension_push_ranges with L;
    autorewrite with rew_env_dom; auto.
Qed.

Lemma type_environment_extension_ranges : forall L E Xs M,
    scheme_aux L M ->
    fresh (dom E \u L) (sch_arity M) Xs ->
    type_environment_extension E (Xs ~: M).
Proof.
  introv Hs Hf.
  rewrite <- concat_empty_l.
  apply type_environment_extension_push_ranges with L;
    autorewrite with rew_tenv_dom; auto.
Qed.

Lemma type_environment_ranges : forall L Xs M,
    scheme_aux L M ->
    fresh L (sch_arity M) Xs ->
    type_environment (Xs ~: M).
Proof.
  introv Hs Hf.
  apply type_environment_extension_ranges with L;
    autorewrite with rew_env_dom; auto.
Qed.

(* Inversions for various constructors *)

Lemma type_environment_push_inv : forall E1 E2 X R,
    type_environment_extension E1 (E2 & X ~ R) ->
    type_environment_extension E1 E2 /\ X # E1 /\ X # E2 /\ range R.
Proof.
  introv He.
  remember (E2 & X ~ R) as Ex.
  destruct He.
  - apply empty_push_inv in HeqEx; contradiction.
  - destruct (eq_push_inv HeqEx) as [? [? ?]]; subst.
    split; auto.
Qed.

Lemma type_environment_concat_inv : forall E1 E2 E3,
    type_environment_extension E1 (E2 & E3) ->
    type_environment_extension E1 E2
    /\ type_environment_extension E1 E3.
Proof.
  introv He.
  remember (E2 & E3) as Es.
  generalize dependent E3.
  generalize dependent E2.
  induction He; introv HeqEs; subst.
  - destruct (empty_concat_inv HeqEs); subst; auto.
  - induction E3 using env_ind;
      autorewrite with rew_env_concat in *; subst; auto.
    destruct (eq_push_inv HeqEs) as [? [? ?]]; subst.
    specialize (@IHHe E0 E3).
    intuition auto.
Qed.

Lemma type_environment_push_singles_inv : forall E1 E2 Xs Rs,
    type_environment_extension E1 (E2 & Xs ~* Rs) ->
    length Rs = length Xs ->
    type_environment_extension E1 E2
    /\ fresh (dom E1 \u dom E2) (length Rs) Xs
    /\ ranges Rs.
Proof.
  introv He Hl.
  generalize dependent Rs.
  induction Xs; introv He Hl; destruct Rs; try discriminate;
    simpl in *; autorewrite with rew_env_concat in *; auto.
  destruct (type_environment_push_inv He) as [He2 [? [? ?]]].
  destruct (type_environment_concat_inv He2) as [? ?].
  inversion Hl.
  assert (a # Xs ~* Rs)
    by eauto using ok_middle_inv_r,
       ok_from_type_environment_extension.
  assert (ok (E2 & Xs ~* Rs))
    by eauto using ok_remove, ok_from_type_environment_extension.
  destruct IHXs with (Rs := Rs) as [? [? ?]];
    auto using type_environment_concat.
  autorewrite with rew_tenv_dom in *;
    auto using fresh_from_notin.
Qed.

Lemma type_environment_singles_inv : forall E Xs Rs,
    type_environment_extension E (Xs ~* Rs) ->
    length Rs = length Xs ->
    fresh (dom E) (length Rs) Xs /\ ranges Rs.
Proof.
  introv He Hl.
  rewrite <- concat_empty_l in He.
  destruct (type_environment_push_singles_inv He Hl) as [? [? ?]].
  auto.
Qed.
   
(* Middle constructors and inversions *)

Lemma type_environment_middle : forall E1 E2 X R,
    type_environment (E1 & E2) ->
    range R ->
    X # E1 & E2 ->
    type_environment (E1 & X ~ R & E2).
Proof.
  introv He Hs Hn.
  destruct (type_environment_concat_inv He) as [? ?].
  auto using type_environment_concat, ok_middle,
    ok_from_type_environment.
Qed.

Lemma type_environment_middle_inv : forall E1 E2 E3 X R,
    type_environment_extension E1 (E2 & X ~ R & E3) ->
    type_environment_extension E1 (E2 & E3)
    /\ range R /\ X # E1 /\ X # E2 & E3.
Proof.
  introv He.
  assert (ok (E2 & X ~ R & E3)) as Hok
    by eauto using ok_from_type_environment_extension.
  destruct (ok_middle_inv Hok).
  apply ok_remove in Hok.
  destruct (type_environment_concat_inv He) as [He2 ?].
  destruct (type_environment_push_inv He2) as [? [? [? ?]]].
  auto using type_environment_extension_concat.
Qed.

Lemma type_environment_middle_singles : forall E1 E2 Xs Rs,
    type_environment (E1 & E2) ->
    fresh (dom E1 \u dom E2) (length Rs) Xs ->
    ranges Rs ->
    type_environment (E1 & Xs ~* Rs & E2).
Proof.
  introv He Hf Hrs.
  destruct (type_environment_concat_inv He).
  destruct (ok_concat_inv (ok_from_type_environment He))
    as [? [? ?]].
  fresh_length Hf as Hl.
  assert (type_environment (E1 & Xs ~* Rs))
    by auto using type_environment_push_singles.
  apply type_environment_concat; auto.
  apply ok_concat; auto using ok_from_type_environment.
  autorewrite with rew_tenv_dom; auto.
Qed.

Lemma type_environment_middle_singles_inv : forall E1 E2 E3 Xs Rs,
    type_environment_extension E1 (E2 & Xs ~* Rs & E3) ->
    length Rs = length Xs ->
    type_environment_extension E1 (E2 & E3)
    /\ fresh (dom E1 \u dom E2 \u dom E3) (length Rs) Xs
    /\ ranges Rs.
Proof.
  introv He Hl.
  destruct (type_environment_concat_inv He) as [He2 ?].
  destruct (type_environment_push_singles_inv He2) as [? [? ?]];
    auto.
  destruct (ok_concat_inv (ok_from_type_environment_extension He))
    as [? [? ?]].
  split.
  - eauto using type_environment_extension_concat,
      ok_remove, ok_from_type_environment_extension.
  - autorewrite with rew_tenv_dom in *;
      auto using fresh_disjoint.
Qed.
  
Lemma type_environment_middle_ranges : forall L E1 E2 Xs M,
    type_environment (E1 & E2) ->
    scheme_aux L M ->
    fresh (dom (E1 & E2) \u L) (sch_arity M) Xs ->
    type_environment (E1 & Xs ~: M & E2).
Proof.
  introv He Hs Hf.
  autorewrite with rew_tenv_dom in Hf.
  fresh_length Hf as Hl.
  destruct (type_environment_concat_inv He) as [? ?].
  assert (type_environment (E1 & Xs ~: M))
    by (apply type_environment_push_ranges with L; auto).
  assert (ok (E1 & E2)) as Hok
    by auto using ok_from_type_environment.
  destruct (ok_concat_inv Hok) as [? [? ?]].
  apply type_environment_concat; auto.
  apply ok_concat;
   autorewrite with rew_tenv_dom;
     auto using ok_from_type_environment.
Qed.
 
(* Various parital inversions *)

Lemma type_environment_concat_inv_l : forall E1 E2,
    type_environment (E1 & E2) ->
    type_environment E1.
Proof.
  introv He.
  destruct (type_environment_concat_inv He).
  assumption.
Qed.

Lemma type_environment_concat_inv_r : forall E1 E2,
    type_environment (E1 & E2) ->
    type_environment E2.
Proof.
  introv He.
  destruct (type_environment_concat_inv He).
  assumption.
Qed.

Lemma type_environment_remove : forall E1 E2 E3 E4,
    type_environment_extension E1 (E2 & E3 & E4) ->
    type_environment_extension E1 (E2 & E4).
Proof.
  introv He.
  destruct (type_environment_concat_inv He) as [He2 ?].
  destruct (type_environment_concat_inv He2) as [? ?].
  eauto using type_environment_extension_concat,
    ok_remove, ok_from_type_environment_extension.
Qed.

Lemma type_environment_remove_l : forall E1 E2 E3,
    type_environment_extension E1 (E2 & E3) ->
    type_environment_extension E1 E2.
Proof.
  introv He.
  rewrite <- concat_empty_r.
  apply type_environment_remove with E3.
  rewrite concat_empty_r.
  assumption.
Qed.

Lemma type_environment_extension_strengthen : forall E1 E2 E3 E4,
    type_environment_extension (E1 & E2 & E3) E4 ->
    type_environment_extension (E1 & E3) E4.
Proof.
  introv He.
  remember (E1 & E2 & E3) as E123.
  induction He; subst; auto.
Qed.

Lemma type_environment_extension_strengthen_l : forall E1 E2 E3,
    type_environment_extension (E1 & E2) E3 ->
    type_environment_extension E1 E3.
Proof.
  introv He.
  rewrite <- concat_empty_r with (E := E1 & E2) in He.
  rewrite <- concat_empty_r with (E := E1).
  eauto using type_environment_extension_strengthen.  
Qed.

Lemma type_environment_middle_inv_fresh : forall E1 E2 X R,
    type_environment (E1 & X ~ R & E2) ->
    X # (E1 & E2).
Proof.
  introv He.
  assert (ok (E1 & X ~ R & E2)) as Hok
    by auto using ok_from_type_environment.
  destruct (ok_middle_inv Hok).
  auto.
Qed.

Lemma type_environment_push_inv_fresh : forall E1 X R,
    type_environment (E1 & X ~ R) ->
    X # E1.
Proof.
  introv He.
  rewrite <- concat_empty_r in He.
  rewrite <- (concat_empty_r E1).
  eauto using type_environment_middle_inv_fresh.
Qed.

Lemma type_environment_push_inv_range : forall E1 X R,
    type_environment (E1 & X ~ R) ->
    range R.
Proof.
  introv He.
  destruct (type_environment_push_inv He) as [? [? [? ?]]].
  assumption.
Qed.

Lemma type_environment_singles_inv_ranges : forall E Xs Rs,
    type_environment_extension E (Xs ~* Rs) ->
    length Rs = length Xs ->
    ranges Rs.
Proof.
  introv He Hl.
  destruct (type_environment_singles_inv He Hl).
  assumption.
Qed.

Lemma type_environment_ranges_inv_ranges : forall E Xs M,
    type_environment_extension E (Xs ~: M) ->
    sch_arity M = length Xs ->
    ranges (rng_open_vars_list (sch_ranges M) Xs).
Proof.
  introv He Hl.
  apply type_environment_singles_inv_ranges
    with (E := E) (Xs := Xs); auto.
  rewrite sch_arity_length in Hl.
  rewrite rng_open_vars_list_length.
  assumption.
Qed.

Lemma type_environment_middle_inv_env : forall E1 E2 X R,
    type_environment (E1 & X ~ R & E2) ->
    type_environment (E1 & E2).
Proof.
  introv He.
  destruct (type_environment_concat_inv He) as [He2 ?].
  destruct (type_environment_concat_inv He2) as [? ?].
  eauto using type_environment_concat,
    ok_remove, ok_from_type_environment.
Qed.

Lemma type_environment_middle_inv_range : forall E1 E2 X R,
    type_environment (E1 & X ~ R & E2) ->
    range R.
Proof.
  introv He.
  destruct (type_environment_concat_inv He) as [He2 ?].
  eauto using type_environment_push_inv_range.
Qed.

Lemma type_environment_middle_singles_swap : forall E1 E2 Xs Rs Ys,
  length Xs = length Rs ->
  fresh (dom E1 \u dom E2) (length Rs) Ys ->
  type_environment (E1 & Xs ~* Rs & E2) ->
  type_environment (E1 & Ys ~* Rs & E2).
Proof.
  introv Hl Hf He.
  destruct (type_environment_middle_singles_inv He)
    as [? [? ?]]; auto using type_environment_middle_singles.
Qed.

Lemma binds_tenv_weakening : forall E1 E2 E3 X R,
    binds X R (E1 & E3) ->
    type_environment (E1 & E2 & E3) ->
    binds X R (E1 & E2 & E3).
Proof.
  introv Hb He.
  assert (ok (E1 & E2 & E3))
    by auto using ok_from_type_environment.
  apply binds_weaken; assumption.
Qed.

Lemma binds_tenv_weakening_l : forall E1 E2 X R,
    binds X R E1 ->
    type_environment (E1 & E2) ->
    binds X R (E1 & E2).
Proof.
  introv Hb He.
  rewrite <- concat_empty_r.
  apply binds_tenv_weakening;
    rewrite concat_empty_r; auto.
Qed.

Lemma binds_tenv_weakening_l2 : forall E1 E2 E3 X R,
    binds X R E1 ->
    type_environment (E1 & E2 & E3) ->
    binds X R (E1 & E2 & E3).
Proof.
  introv Hb He.
  rewrite <- concat_assoc.
  apply binds_tenv_weakening_l; auto.
  rewrite concat_assoc.
  auto.
Qed.

(* Combined extension and inversion *)
Lemma type_environment_extend_middle_inv : forall E1 E2 E3 X R,
    type_environment_extension E1 (E2 & X ~ R) ->
    type_environment_extension (E1 & (E2 & X ~ R)) E3 ->
    type_environment_extension E1 E2
    /\ type_environment_extension (E1 & E2) E3
    /\ range R /\ X # E1 /\ X # E2 /\ X # E3.
Proof.
  introv He1 He2.
  assert (type_environment_extension E1 (E2 & X ~ R & E3))
    as He3 by auto using type_environment_extension_extend.
  destruct (type_environment_middle_inv He3)
    as [He4 [Hn1 [Hn2 Hr]]].
  rewrite concat_assoc in He2.
  apply type_environment_extension_strengthen_l in He2.
  destruct (type_environment_push_inv He1) as [He5 _].  
  split; auto.
Qed.

(* Lemmas around binding and weakening *)

Lemma binds_tenv_extend : forall x v E1 E2,
    type_environment_extension E1 E2 ->
    binds x v E1 -> binds x v (E1 & E2).
Proof.
  introv He Hb.
  induction E2 using env_ind.
  - rewrite concat_empty_r; assumption.
  - remember (E2 & x0 ~ v0) as E3.
    destruct He.
    + destruct (empty_push_inv HeqE3).
    + destruct (eq_push_inv HeqE3) as [? [? ?]]; subst.
      rewrite concat_assoc.
      apply binds_push_neq; auto.
      intro; subst.
      eauto using binds_fresh_inv.
Qed.

Lemma type_environment_push_weakening : forall E1 E2 E3 X R,
    X # E2 ->
    type_environment (E1 & E3 & X ~ R) ->
    type_environment (E1 & E2 & E3) ->
    type_environment (E1 & E2 & E3 & X ~ R).
Proof.
  introv Hin He1 He2.
  destruct (type_environment_push_inv He1) as [? [? [? ?]]].
  auto.
Qed.

Lemma type_environment_singles_weakening : forall E1 E2 E3 Xs Rs,
    fresh (dom E2) (length Rs) Xs ->
    type_environment (E1 & E3 & Xs ~* Rs) ->
    type_environment (E1 & E2 & E3) ->
    type_environment (E1 & E2 & E3 & Xs ~* Rs).
Proof.
  introv Hf He1 He2.
  fresh_length Hf as Hl.
  destruct (type_environment_push_singles_inv He1)
    as [? [? ?]]; auto.
  apply type_environment_push_singles; auto.
  autorewrite with rew_tenv_dom in *.
  auto.
Qed.
 
Lemma type_environment_ranges_weakening : forall E1 E2 E3 Xs M,
    fresh (dom E2) (sch_arity M) Xs ->
    type_environment (E1 & E3 & Xs ~: M) ->
    type_environment (E1 & E2 & E3) ->
    type_environment (E1 & E2 & E3 & Xs ~: M).
Proof.
  introv Hf He1 He2.
  destruct M as [Rs ?].
  unfold bind_sch_ranges in *.
  simpl in *.
  apply type_environment_singles_weakening; auto.
  rewrite <- length_rng_open_vars_list.
  assumption.
Qed.

Lemma type_environment_extension_singles_weakening :
  forall E1 E2 E3 Xs Rs,
    fresh (dom E2) (length Rs) Xs ->
    type_environment_extension (E1 & E3) (Xs ~* Rs) ->
    type_environment (E1 & E2 & E3) ->
    type_environment_extension (E1 & E2 & E3) (Xs ~* Rs).
Proof.
  introv Hf He1 He2.
  fresh_length Hf as Hl.
  destruct (type_environment_singles_inv He1); auto.
  apply type_environment_extension_singles;
    autorewrite with rew_env_dom in *; auto.
Qed.

Lemma type_environment_extension_ranges_weakening :
  forall E1 E2 E3 Xs M,
    fresh (dom E2) (sch_arity M) Xs ->
    type_environment_extension (E1 & E3) (Xs ~: M) ->
    type_environment (E1 & E2 & E3) ->
    type_environment_extension (E1 & E2 & E3) (Xs ~: M).
Proof.
  introv Hf He1 He2.
  destruct M as [Rs ?].
  unfold bind_sch_ranges in *.
  simpl in *.
  apply type_environment_extension_singles_weakening;
    try rewrite <- length_rng_open_vars_list; auto.
Qed.

Lemma range_from_tenv : forall E X R,
    type_environment E ->
    binds X R E ->
    range R.
Proof.
  introv He Hb.
  induction He.
  - apply binds_empty_inv in Hb; contradiction.
  - destruct (binds_push_inv Hb) as [[Hx Hbnd]|[Hx Hbnd]];
      auto.
    inversion Hbnd; subst; assumption.
Qed.

Lemma type_from_tenv_lower : forall E X T1 T2 K,
    type_environment E ->
    binds X (Rng T1 T2 K) E ->
    type T1.
Proof.
  introv He Hb.
  remember (Rng T1 T2 K) as R.
  replace T1 with (rng_lower R) by (subst; auto).
  eauto using range_from_tenv, rng_lower_type.
Qed.

Lemma type_from_tenv_upper : forall E X T1 T2 K,
    type_environment E ->
    binds X (Rng T1 T2 K) E ->
    type T2.
Proof.
  introv He Hb.
  remember (Rng T1 T2 K) as R.
  replace T2 with (rng_upper R) by (subst; auto).
  eauto using range_from_tenv, rng_upper_type.
Qed.

Lemma kind_from_tenv : forall E X T1 T2 K,
    type_environment E ->
    binds X (Rng T1 T2 K) E ->
    kind K.
Proof.
  introv He Hb.
  remember (Rng T1 T2 K) as R.
  replace K with (rng_kind R) by (subst; auto).
  eauto using range_from_tenv, rng_kind_kind.
Qed.

(* *************************************************************** *)
(** * Environments *)

Lemma ok_from_environment : forall D,
  environment D -> ok D.
Proof.
  introv He.
  induction He; auto. 
Qed.

(* Domains *)

Hint Rewrite from_list_nil from_list_cons : rew_env_dom.

Lemma env_dom_singles : forall xs (Ms : list sch),
  length Ms = length xs ->
  dom (xs ~* Ms) = from_list xs.
Proof.
  introv Hl.
  generalize dependent Ms.
  induction xs; introv Hl; destruct Ms; inversion Hl;
    autorewrite with rew_env_concat;
    autorewrite with rew_env_dom; auto.
  rewrite union_comm.
  f_equal; auto.
Qed.

Hint Rewrite env_dom_singles using auto : rew_env_dom.

(* Constructor for pushing twice *)

Lemma environment_push2 : forall E x1 x2 M1 M2,
    environment E ->
    scheme M1 ->
    scheme M2 ->
    x1 # E ->
    x2 # E ->
    x1 <> x2 ->
    environment (E & x1 ~ M1 & x2 ~ M2).
Proof.
  introv He Hs1 Hs2 Hf1 Hf2 Hn.
  auto.
Qed.

(* Constructor for concatenations *)

Lemma environment_concat : forall D1 D2,
    environment D1 ->
    environment D2 ->
    ok (D1 & D2) ->
    environment (D1 & D2).
Proof.
  introv He1 He2 Hok.
  induction He2;
    autorewrite with rew_env_concat in *; auto.
  remember (D1 & E & x ~ M) as D3.
  destruct Hok; auto.
  destruct (eq_push_inv HeqD3) as [? [? ?]]; subst; auto.
Qed.

Lemma environment_singles : forall D xs Ms,
    environment D ->
    fresh (dom D) (length Ms) xs ->
    schemes Ms ->
    environment (D & xs ~* Ms).
Proof.
  introv He Hf Hss.
  generalize dependent Ms.
  generalize dependent D.
  induction xs; introv He Hf Hss; simpl.
  - rewrite (fresh_length_nil _ _ Hf).
    rewrite singles_nil.
    autorewrite with rew_env_concat; auto.
  - destruct Ms; simpl in *; destruct Hf.
    inversion Hss; subst.
    rewrite singles_cons, concat_assoc.
    apply environment_push;
      autorewrite with rew_env_dom;
        eauto using fresh_length.
Qed.

(* Inversions for various constructors *)

Lemma environment_push_inv : forall D x M,
    environment (D & x ~ M) ->
    environment D /\ x # D /\ scheme M.
Proof.
  introv He.
  remember (D & x ~ M) as Dx.
  destruct He.
  - apply empty_push_inv in HeqDx; contradiction.
  - destruct (eq_push_inv HeqDx) as [? [Hb ?]].
    inversion Hb; subst.
    auto.
Qed.

Lemma environment_concat_inv : forall D1 D2,
    environment (D1 & D2) ->
    environment D1 /\ environment D2.
Proof.
  introv He.
  remember (D1 & D2) as Ds.
  generalize dependent D2.
  generalize dependent D1.
  induction He; introv HeqDs.
  - destruct (empty_concat_inv HeqDs); subst.
    split; auto.
  - induction D2 using env_ind;
      autorewrite with rew_env_concat in *; subst.
    + intuition auto.
    + destruct (eq_push_inv HeqDs) as [? [? ?]]; subst.
      specialize (IHHe D1 D2).
      intuition auto.
Qed.

Lemma environment_singles_inv : forall D xs Ms,
    environment (D & xs ~* Ms) ->
    length Ms = length xs ->
    environment D /\ fresh (dom D) (length Ms) xs /\ schemes Ms.
Proof.
  introv He Hl.
  generalize dependent Ms.
  induction xs; introv He Hl; induction Ms; try discriminate;
    simpl in *; autorewrite with rew_env_concat in *; auto.
  destruct (environment_push_inv He) as [He2 [? ?]].
  destruct (environment_concat_inv He2) as [? ?].
  inversion Hl.
  assert (a # xs ~* Ms)
    by eauto using ok_middle_inv_r, ok_from_environment.
  assert (ok (D & xs ~* Ms))
    by eauto using ok_remove, ok_from_environment.    
  destruct IHxs with (Ms := Ms) as [? [? ?]];
    auto using environment_concat.
  autorewrite with rew_env_dom in *;
    auto using fresh_from_notin.
Qed.
    
(* Middle constructors and inversions *)

Lemma environment_middle : forall D1 D2 x M,
    environment (D1 & D2) ->
    scheme M ->
    x # D1 & D2 ->
    environment (D1 & x ~ M & D2).
Proof.
  introv He Hs Hn.
  destruct (environment_concat_inv He) as [? ?].
  auto using environment_concat, ok_middle, ok_from_environment.
Qed.

Lemma environment_middle_inv : forall D1 D2 x M,
    environment (D1 & x ~ M & D2) ->
    environment (D1 & D2) /\ scheme M /\ x # D1 & D2.
Proof.
  introv He.
  assert (ok (D1 & x ~ M & D2)) as Hok
    by auto using ok_from_environment.
  destruct (ok_middle_inv Hok).
  apply ok_remove in Hok.
  destruct (environment_concat_inv He) as [He2 ?].
  destruct (environment_push_inv He2) as [? [? ?]].
  auto using environment_concat.
Qed.
  
Lemma environment_middle_singles : forall D1 D2 xs Ms,
    environment (D1 & D2) ->
    fresh (dom D1 \u dom D2) (length Ms) xs ->
    schemes Ms ->
    environment (D1 & xs ~* Ms & D2).
Proof.
  introv He Hf Hss.
  destruct (environment_concat_inv He).
  destruct (ok_concat_inv (ok_from_environment He)) as [? [? ?]].
  fresh_length Hf as Hl.
  assert (environment (D1 & xs ~* Ms))
    by auto using environment_singles.
  apply environment_concat; auto.
  apply ok_concat; auto using ok_from_environment.
  autorewrite with rew_env_dom; auto.
Qed.

Lemma environment_middle_singles_inv : forall D1 D2 xs Ms,
    environment (D1 & xs ~* Ms & D2) ->
    length Ms = length xs ->
    environment (D1 & D2)
    /\ fresh (dom D1 \u dom D2) (length Ms) xs /\ schemes Ms.
Proof.
  introv He Hl.
  destruct (environment_concat_inv He) as [He2 ?].
  destruct (environment_singles_inv He2) as [? [? ?]]; auto.
  destruct (ok_concat_inv (ok_from_environment He)) as [? [? ?]].
  split.
  - eauto using environment_concat,
      ok_remove, ok_from_environment.
  - autorewrite with rew_env_dom in *; auto using fresh_disjoint.
Qed.
  
(* Various parital inversions *)

Lemma environment_concat_inv_l : forall D1 D2,
    environment (D1 & D2) ->
    environment D1.
Proof.
  introv He.
  destruct (environment_concat_inv He).
  assumption.
Qed.

Lemma environment_concat_inv_r : forall D1 D2,
    environment (D1 & D2) ->
    environment D2.
Proof.
  introv He.
  destruct (environment_concat_inv He).
  assumption.
Qed.

Lemma environment_remove : forall D1 D2 D3,
    environment (D1 & D2 & D3) ->
    environment (D1 & D3).
Proof.
  introv He.
  destruct (environment_concat_inv He) as [He2 ?].
  destruct (environment_concat_inv He2) as [? ?].
  eauto using environment_concat, ok_remove, ok_from_environment.
Qed.

Lemma environment_middle_inv_fresh : forall D1 D2 x M,
    environment (D1 & x ~ M & D2) ->
    x # (D1 & D2).
Proof.
  introv He.
  assert (ok (D1 & x ~ M & D2)) as Hok
    by auto using ok_from_environment.
  destruct (ok_middle_inv Hok).
  auto.
Qed.

Lemma environment_push_inv_fresh : forall D x M,
    environment (D & x ~ M) ->
    x # D.
Proof.
  introv He.
  rewrite <- concat_empty_r in He.
  rewrite <- (concat_empty_r D).
  eauto using environment_middle_inv_fresh.
Qed.

Lemma environment_push_inv_scheme : forall D X M,
    environment (D & X ~ M) ->
    scheme M.
Proof.
  introv He.
  destruct (environment_push_inv He) as [? [? ?]].
  assumption.
Qed.

Lemma environment_middle_inv_env : forall D1 D2 x M,
    environment (D1 & x ~ M & D2) ->
    environment (D1 & D2).
Proof.
  introv He.
  destruct (environment_concat_inv He) as [He2 ?].
  destruct (environment_concat_inv He2) as [? ?].
  eauto using environment_concat, ok_remove, ok_from_environment.
Qed.

Lemma environment_middle_inv_scheme : forall D1 D2 x M,
    environment (D1 & x ~ M & D2) ->
    scheme M.
Proof.
  introv He.
  destruct (environment_concat_inv He) as [He2 ?].
  eauto using environment_push_inv_scheme.
Qed.

Lemma binds_env_weakening : forall D1 D2 D3 X B,
    binds X B (D1 & D3) ->
    environment (D1 & D2 & D3) ->
    binds X B (D1 & D2 & D3).
Proof.
  introv Hb He.
  assert (ok (D1 & D2 & D3))
    by auto using ok_from_environment.
  apply binds_weaken; assumption.
Qed.

Lemma environment_push_weakening : forall D1 D2 D3 x M,
    x # D2 ->
    environment (D1 & D3 & x ~ M) ->
    environment (D1 & D2 & D3) ->
    environment (D1 & D2 & D3 & x ~ M).
Proof.
  introv Hin He1 He2.
  destruct (environment_push_inv He1) as [? [? ?]].
  auto.
Qed.

Lemma scheme_from_env : forall D x M,
    environment D ->
    binds x M D ->
    scheme M.
Proof.
  introv He Hb.
  induction He.
  - apply binds_empty_inv in Hb; contradiction.
  - destruct (binds_push_inv Hb) as [[Hx Hbnd]|[Hx Hbnd]];
      subst; auto.
Qed.

(* *************************************************************** *)
(** * Properties of stores and store types *)

Lemma ok_from_store_type : forall P,
  store_type P -> ok P.
Proof.
  introv Hs.
  induction Hs; auto. 
Qed.

Hint Rewrite dom_empty dom_single dom_concat : rew_styp_dom.

Hint Rewrite from_list_nil from_list_cons : rew_styp_dom.

Lemma binds_store_type_weakening : forall P1 P2 P3 X T,
    binds X T (P1 & P3) ->
    store_type (P1 & P2 & P3) ->
    binds X T (P1 & P2 & P3).
Proof.
  introv Hb He.
  assert (ok (P1 & P2 & P3))
    by auto using ok_from_store_type.
  apply binds_weaken; assumption.
Qed.

Lemma store_type_retract : forall P1 P2,
    store_type (P1 & P2) -> store_type P1.
Proof.
  introv Hs.
  induction P2 using env_ind;
    autorewrite with rew_env_concat in *; auto.
  remember (P1 & P2 & x ~ v) as P3.
  destruct Hs.
  - destruct (empty_concat_inv HeqP3) as [_ Hem].
    apply empty_single_inv in Hem.
    contradiction.
  - destruct (eq_push_inv HeqP3) as [_ [_ Hem]].
    rewrite Hem in Hs.
    auto.
Qed.

Lemma type_from_store_type : forall P l T,
    store_type P ->
    binds l T P ->
    type T.
Proof.
  introv Hs Hb.
  induction Hs.
  - apply binds_empty_inv in Hb; contradiction.
  - destruct (binds_push_inv Hb) as [[Hl Hbnd]|[Hl Hbnd]];
      subst; auto.
Qed.

Lemma value_from_store : forall V l t,
    store V ->
    binds l t V ->
    value t.
Proof.
  introv Hs Hb.
  induction Hs.
  - apply binds_empty_inv in Hb; contradiction.
  - destruct (binds_push_inv Hb) as [[Hl Hbnd]|[Hl Hbnd]];
      subst; auto.
Qed.

(* *************************************************************** *)
(** * Properties of equation environments *)

Lemma in_qenv_concat_l : forall Q1 Q2 T1 T2 K,
    in_qenv Q1 T1 T2 K ->
    in_qenv (Q1 ++ Q2) T1 T2 K.
Proof.
  introv Hin.
  induction Hin; simpl; auto. 
Qed.

Lemma in_qenv_concat_r : forall Q1 Q2 T1 T2 K,
    in_qenv Q2 T1 T2 K ->
    in_qenv (Q1 ++ Q2) T1 T2 K.
Proof.
  introv Hin.
  induction Q1 as [|[[T1' T2'] K']]; simpl; auto.
Qed.

Lemma in_qenv_concat_inv : forall Q1 Q2 T1 T2 K (C : Prop),
    in_qenv (Q1 ++ Q2) T1 T2 K ->
    (in_qenv Q1 T1 T2 K -> C) ->
    (in_qenv Q2 T1 T2 K -> C) ->
    C.
Proof.
  introv Hin Hc1 Hc2.
  induction Q1 as [|[[T1' T2'] K']]; simpl in *; auto.
  inversion Hin; subst; auto.
Qed.

Lemma in_qenv_nil_inv : forall T1 T2 K,
    in_qenv nil T1 T2 K -> False.
Proof.
  introv Hin.
  inversion Hin.
Qed.

Lemma in_qenv_middle_inv :
  forall Q1 Q2 T1 T2 K T1' T2' K' (C : Prop),
    in_qenv (Q1 ++ (T1, T2, K) :: Q2) T1' T2' K' ->
    (in_qenv (Q1 ++ Q2) T1' T2' K' -> C) ->
    (T1 = T1' -> T2 = T2' -> K = K' -> C) ->
    C.
Proof.    
  introv Hin Hc1 Hc2.
  apply in_qenv_concat_inv
    with (Q1 := Q1) (Q2 := (T1, T2, K) :: Q2)
         (T1 := T1') (T2 := T2') (K := K');
    auto using in_qenv_concat_l; introv Hin2.
  inversion Hin2; subst; auto using in_qenv_concat_r.
Qed.