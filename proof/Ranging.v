(************************************************
 *          Row Subtyping - Ranging             *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import LibLN Cofinite Disjoint Definitions Utilities
        Substitution Wellformedness Kinding Subtyping.

(* ****************************************************** *)
(** ** Add hints for constructors *)

Hint Constructors valid_range valid_ranges valid_ranges_and_type
  valid_scheme valid_schemes valid_tenv_aux valid_tenv valid_env
  ranging rangings valid_instance.

Hint Extern 1 (valid_scheme _ _) =>
  let L' := gather_vars in
  let L' := beautify_fset L' in
  apply valid_scheme_c with (L := L').

(* *************************************************************** *)
(** Length of rangings *)

Lemma rangings_length : forall E Ts Rs,
  rangings E Ts Rs ->
  length Ts = length Rs.
Proof.
  introv Hrs.
  induction Hrs; simpl; auto.
Qed.

(* *************************************************************** *)
(** Valid bindings *)

Lemma valid_range_from_valid_tenv_aux : forall X E1 E2 R,
    valid_tenv_aux E1 E2 ->
    binds X R E2 ->
    valid_range E1 R.
Proof.
  introv He Hb.
  induction He.
  - apply binds_empty_inv in Hb; contradiction.
  - destruct (binds_push_inv Hb) as [[Hx Hbnd]|[Hx Hbnd]];
      subst; auto.
Qed.

Lemma valid_range_from_valid_tenv : forall X E R,
    valid_tenv E ->
    binds X R E ->
    valid_range E R.
Proof.
  introv He Hb.
  destruct He as [E He].
  eauto using valid_range_from_valid_tenv_aux.
Qed.

(* *************************************************************** *)
(** Valid output *)

Lemma output_ranging : forall E T R,
  ranging E T R ->
  valid_tenv E ->
  valid_range E R.
Proof.
  introv Hr He.
  induction Hr; subst; auto.
  - assert (kind (knd_row cs)) as Hk
      by eauto using output_kinding with wellformed.
    inversion Hk; subst.
    auto.
  - eauto using valid_range_from_valid_tenv.
  - assert (valid_range E (rng_range T1 T2)) as Hr2 by auto.
    inversion Hr2; subst.
    apply valid_range_range.
    apply subtype_transitive with T2; auto with wellformed.
    apply subtype_transitive with T1; auto with wellformed.
Qed.

Lemma output_rangings : forall E Ts Rs,
  rangings E Ts Rs ->
  valid_tenv E ->
  valid_ranges E Rs.
Proof.
  introv Hr He.
  induction Hr; eauto using output_ranging.
Qed.

(* *************************************************************** *)
(** Weakening *)

Lemma ranging_weakening : forall E1 E2 E3 T R,
   ranging (E1 & E3) T R -> 
   type_environment (E1 & E2 & E3) ->
   ranging (E1 & E2 & E3) T R.
Proof.
  introv Hr He.
  remember (E1 & E3) as E13.
  induction Hr; subst;
    eauto using kinding_weakening, subtype_weakening,
      binds_tenv_weakening.
Qed.

Lemma rangings_weakening : forall E1 E2 E3 Ts Rs,
   rangings (E1 & E3) Ts Rs -> 
   type_environment (E1 & E2 & E3) ->
   rangings (E1 & E2 & E3) Ts Rs.
Proof.
  introv Hr He.
  remember (E1 & E3) as E13.
  induction Hr; subst; eauto using ranging_weakening.
Qed.

Lemma ranging_weakening_l : forall E1 E2 T R,
   ranging E1 T R -> 
   type_environment (E1 & E2) ->
   ranging (E1 & E2) T R.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E1 & E2).
  apply ranging_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma rangings_weakening_l : forall E1 E2 Ts Rs,
   rangings E1 Ts Rs -> 
   type_environment (E1 & E2) ->
   rangings (E1 & E2) Ts Rs.
Proof.
  introv Hks He.
  induction Hks; subst; auto using ranging_weakening_l.
Qed.

Lemma valid_range_weakening : forall E1 E2 E3 R,
   valid_range (E1 & E3) R -> 
   type_environment (E1 & E2 & E3) ->
   valid_range (E1 & E2 & E3) R.
Proof.
  introv Hr He.
  remember (E1 & E3) as E13.
  induction Hr; subst; auto using subtype_weakening.
Qed.

Lemma valid_ranges_weakening : forall E1 E2 E3 Rs,
   valid_ranges (E1 & E3) Rs -> 
   type_environment (E1 & E2 & E3) ->
   valid_ranges (E1 & E2 & E3) Rs.
Proof.
  introv Hr He.
  remember (E1 & E3) as E13.
  induction Hr; subst; auto using valid_range_weakening.
Qed.

Lemma valid_ranges_weakening_l : forall E1 E2 Rs,
   valid_ranges E1 Rs -> 
   type_environment (E1 & E2) ->
   valid_ranges (E1 & E2) Rs.
Proof.
  introv Hr He.
  rewrite <- concat_empty_r with (E := E1 & E2).
  apply valid_ranges_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma valid_ranges_and_type_weakening : forall E1 E2 E3 Rs T,
   valid_ranges_and_type (E1 & E3) Rs T -> 
   type_environment (E1 & E2 & E3) ->
   valid_ranges_and_type (E1 & E2 & E3) Rs T.
Proof.
  introv Hr He.
  remember (E1 & E3) as E13.
  induction Hr; subst;
    auto using valid_ranges_weakening, kinding_weakening.
Qed.

Lemma valid_scheme_weakening : forall E1 E2 E3 M,
   valid_scheme (E1 & E3) M -> 
   type_environment (E1 & E2 & E3) ->
   valid_scheme (E1 & E2 & E3) M.
Proof.
  introv Hs He.
  remember (E1 & E3) as E13.
  assert (scheme M) by auto with wellformed.
  induction Hs; subst.
  apply_fresh valid_scheme_c as Xs.
  rewrite <- concat_assoc.
  apply valid_ranges_and_type_weakening;
    rewrite concat_assoc; auto.
  apply type_environment_push_ranges; auto.
  autorewrite with rew_tenv_dom; auto.
Qed.

Lemma valid_schemes_weakening : forall E1 E2 E3 Ms,
   valid_schemes (E1 & E3) Ms -> 
   type_environment (E1 & E2 & E3) ->
   valid_schemes (E1 & E2 & E3) Ms.
Proof.
  introv Hss He.
  remember (E1 & E3) as E13.
  induction Hss; subst; auto using valid_scheme_weakening.
Qed.

Lemma valid_tenv_aux_weakening : forall E1 E2 E3 E4,
   valid_tenv_aux (E1 & E3) E4 -> 
   type_environment (E1 & E2 & E3) ->
   valid_tenv_aux (E1 & E2 & E3) E4.
Proof.
  introv Hv He.
  remember (E1 & E3) as E13.
  induction Hv; subst; auto using valid_range_weakening.
Qed.

Lemma valid_tenv_aux_weakening_l : forall E1 E2 E3,
   valid_tenv_aux E1 E3 -> 
   type_environment (E1 & E2) ->
   valid_tenv_aux (E1 & E2) E3.
Proof.
  introv He1 He2.
  rewrite <- concat_empty_r with (E := E1 & E2).
  apply valid_tenv_aux_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma valid_instance_weakening : forall E1 E2 E3 Ts M,
   valid_instance (E1 & E3) Ts M -> 
   type_environment (E1 & E2 & E3) ->
   valid_instance (E1 & E2 & E3) Ts M.
Proof.
  introv Hv He.
  remember (E1 & E3) as E13.
  induction Hv; subst; eauto using rangings_weakening.
Qed.

Lemma valid_instance_weakening_l : forall E1 E2 Ts M,
   valid_instance E1 Ts M -> 
   type_environment (E1 & E2) ->
   valid_instance (E1 & E2) Ts M.
Proof.
  introv He1 He2.
  rewrite <- concat_empty_r with (E := E1 & E2).
  apply valid_instance_weakening;
    rewrite concat_empty_r; assumption.
Qed.

(* *************************************************************** *)
(** Closed *)

Lemma ranging_closed : forall E T R X,
    ranging E T R ->
    X # E ->
    X \notin (typ_fv T).
Proof.
  introv Hr Hn.
  induction Hr; eauto using kinding_closed.
Qed.

Lemma rangings_closed : forall E Ts Rs X,
    rangings E Ts Rs ->
    X # E ->
    X \notin (typ_fv_list Ts).
Proof.
  introv Hrs Hn.
  induction Hrs; simpl; eauto using ranging_closed.
Qed.

Lemma valid_range_closed : forall E R X,
    valid_range E R ->
    X # E ->
    X \notin (rng_fv R).
Proof.
  introv Hv Hn.
  induction Hv; simpl; eauto using subtype_closed_l, subtype_closed_r.
Qed.

Lemma valid_ranges_closed : forall E Rs X,
    valid_ranges E Rs ->
    X # E ->
    X \notin (rng_fv_list Rs).
Proof.
  introv Hvs Hn.
  induction Hvs; simpl; eauto using valid_range_closed.
Qed.

Lemma valid_ranges_and_type_closed_rngs : forall E Rs T X,
    valid_ranges_and_type E Rs T ->
    X # E ->
    X \notin (rng_fv_list Rs).
Proof.
  introv Hrs Hn.
  induction Hrs; eauto using valid_ranges_closed.
Qed.

Lemma valid_ranges_and_type_closed_typ : forall E Rs T X,
    valid_ranges_and_type E Rs T ->
    X # E ->
    X \notin (typ_fv T).
Proof.
  introv Hrs Hn.
  induction Hrs; eauto using kinding_closed.
Qed.

Lemma valid_scheme_closed : forall E M X,
    valid_scheme E M ->
    X # E ->
    X \notin (sch_fv M).
Proof.
  introv Hs Hn.
  destruct Hs.
  pick_freshes (sch_arity M) Ys.
  fresh_length Fr as Hl.
  assert (X # (E & Ys ~: M))
    by (autorewrite with rew_tenv_dom; auto).
  assert
    (valid_ranges_and_type (E & Ys ~: M)
        (rng_open_vars_list (sch_ranges M) Ys)
        (typ_open_vars (sch_body M) Ys)) by auto.
  replace (sch_fv M)
      with (rng_fv_list (sch_ranges M) \u typ_fv (sch_body M))
    by (destruct M; auto). 
  rewrite notin_union; split;
    eauto using notin_subset, rng_open_vars_list_fv_inv,
      typ_open_vars_fv_inv, valid_ranges_and_type_closed_rngs,
      valid_ranges_and_type_closed_typ.
Qed.

Lemma valid_scheme_closed_list : forall E M Xs,
    valid_scheme E M ->
    disjoint (from_list Xs) (dom E) ->
    disjoint (from_list Xs) (sch_fv M).
Proof.
  introv Hv Hd.
  induction Xs.
  - rewrite from_list_nil; auto.
  - rewrite from_list_cons in *.
    rewrite disjoint_union_l; split; auto.
    rewrite disjoint_all_in_notin.
    introv Hin.
    rewrite in_singleton in Hin; subst.
    eauto using valid_scheme_closed.
Qed.

Lemma valid_schemes_closed : forall E Ms X,
    valid_schemes E Ms ->
    X # E ->
    X \notin (sch_fv_list Ms).
Proof.
  introv Hss Hn.
  induction Hss; simpl; eauto using valid_scheme_closed.
Qed.

Lemma valid_tenv_aux_closed : forall E1 E2 X,
    valid_tenv_aux E1 E2 ->
    X # E1 ->
    X \notin (tenv_fv E2).
Proof.
  introv He Hn.
  induction He; autorewrite with rew_tenv_fv;
    eauto using valid_range_closed.
Qed.

Lemma valid_tenv_closed : forall E X,
    valid_tenv E ->
    X # E ->
    X \notin (tenv_fv E).
Proof.
  introv Hv Hn.
  inversion Hv; subst.
  eauto using valid_tenv_aux_closed.
Qed.

Lemma valid_tenv_closed_list : forall E Xs,
    valid_tenv E ->
    disjoint (from_list Xs) (dom E) ->
    disjoint (from_list Xs) (tenv_fv E).
Proof.
  introv Hv Hd.
  induction Xs.
  - rewrite from_list_nil; auto.
  - rewrite from_list_cons in *.
    rewrite disjoint_union_l; split; auto.
    rewrite disjoint_all_in_notin.
    introv Hin.
    rewrite in_singleton in Hin; subst.
    auto using valid_tenv_closed.
Qed.

Lemma valid_instance_closed : forall E X Ts M,
    valid_instance E Ts M ->
    X # E ->
    X \notin (typ_fv_list Ts).
Proof.
  introv Hv Hn.
  inversion Hv; subst.
  eauto using rangings_closed.
Qed.  

(* *************************************************************** *)
(** Constructor and inversion for concatenation of valid_tenv_aux  *)

Lemma valid_tenv_aux_concat : forall E1 E2 E3,
    valid_tenv_aux E1 E2 ->
    valid_tenv_aux E1 E3 ->
    type_environment (E2 & E3) ->
    valid_tenv_aux E1 (E2 & E3).
Proof.
  introv He1 He2 Henv.
  induction E3 using env_ind;
    autorewrite with rew_env_concat in *; auto.
  remember (E3 & x ~ v) as E3x.
  destruct He2; subst.
  - exfalso; eapply empty_push_inv; eassumption.
  - destruct (eq_push_inv HeqE3x) as [? [? ?]]; subst; auto.
    destruct (type_environment_push_inv Henv) as [? [? ?]].
    eauto using environment_concat_inv_l.
Qed.

Lemma valid_tenv_aux_concat_inv : forall E1 E2 E3,
    valid_tenv_aux E1 (E2 & E3) ->
    valid_tenv_aux E1 E2 /\ valid_tenv_aux E1 E3.
Proof.
  introv He.
  induction E3 using env_ind;
    autorewrite with rew_env_concat in *; auto.
  remember (E2 & E3 & x ~ v) as E23x.
  destruct He; subst.
  - exfalso; eapply empty_push_inv; eassumption.
  - destruct (eq_push_inv HeqE23x) as [? [? ?]]; subst;
      intuition auto.
Qed.

Lemma valid_tenv_aux_remove : forall E1 E2 E3 E4,
    valid_tenv_aux E1 (E2 & E3 & E4) ->
    valid_tenv_aux E1 (E2 & E4).
Proof.
  introv He.
  assert (type_environment (E2 & E3 & E4))
    by auto with wellformed.
  destruct (valid_tenv_aux_concat_inv He) as [He1 He2].
  destruct (valid_tenv_aux_concat_inv He1).
  eauto using valid_tenv_aux_concat, type_environment_remove.
Qed.

(* *************************************************************** *)
(** Useful lemmas for type substitution proofs *)

Lemma rangings_add_subst_ranges : forall E1 E2 Zs Us Rs Xs M,
    fresh (dom E1 \u dom E2 \u from_list Zs) (sch_arity M) Xs ->
    rangings (tenv_subst Zs Us (E1 & E2)) Us
      (rng_subst_list Zs Us Rs) ->
    type_environment (E1 & Zs ~* Rs & E2) ->
    scheme M ->
    rangings (tenv_subst Zs Us (E1 & (E2 & Xs ~: M))) Us
      (rng_subst_list Zs Us Rs).
Proof.
  introv Hf Hrs He Hs.
  fresh_length Hf as Hl.
  rewrite concat_assoc.
  rewrite tenv_subst_concat.
  rewrite tenv_subst_ranges; auto with wellformed.
  apply rangings_weakening_l; auto.
  apply type_environment_push_ranges;
    eauto using tenv_subst_type_environment,
      type_environment_remove with wellformed;
    autorewrite with rew_sch_arity;
    autorewrite with rew_tenv_subst;
    autorewrite with rew_tenv_dom;
    try apply sch_subst_scheme; auto with wellformed.
Qed.

Lemma type_environment_push_subst_ranges : forall E1 E2 Xs Rs Ys M,
    type_environment (E1 & Xs ~* Rs & E2) ->
    length Xs = length Rs ->
    fresh (dom E1 \u from_list Xs \u dom E2) (sch_arity M) Ys ->
    scheme M ->
    type_environment (E1 & Xs ~* Rs & (E2 & Ys ~: M)).
Proof.
  introv He Hl Hf Hs.
  rewrite concat_assoc.
  apply type_environment_push_ranges;
    autorewrite with rew_tenv_dom; auto.
Qed.

(* *************************************************************** *)
(** Preserved by type substitution *)

Lemma ranging_typ_subst_var : forall E1 E2 E3 Xs Rs Us Ys Ts X R,
    binds X R (E1 & Xs ~* Rs & E2) ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    rangings E3 Us (rng_subst_list Ys Ts Rs) ->
    ranging E3 (typ_var_subst Xs Us X) (rng_subst Ys Ts R)
    \/ (binds X R (E1 & E2)
        /\ typ_var_subst Xs Us X = typ_fvar X).
Proof.
  introv Hb Hl1 He Hrs.
  assert (length Us = length Rs) as Hl2
    by (erewrite length_rng_subst_list; eauto using rangings_length).
  generalize dependent Rs.
  generalize dependent Us.
  induction Xs; introv Hb Hl1 He Hrs Hl2; destruct Rs; destruct Us;
    try discriminate; simpl in *;
    autorewrite with rew_env_concat in *; auto.
  inversion Hrs; inversion Hl1; inversion Hl2; subst.
  case_var.
  - apply binds_middle_eq_inv in Hb; subst;
      auto using ok_from_type_environment.
  - eauto using binds_subst, type_environment_remove.
Qed.

Lemma ranging_typ_subst : forall E1 E2 Xs Rs Us T R,
    ranging (E1 & Xs ~* Rs & E2) T R ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    rangings (tenv_subst Xs Us (E1 & E2))
      Us (rng_subst_list Xs Us Rs) ->
    ranging (tenv_subst Xs Us (E1 & E2))
      (typ_subst Xs Us T) (rng_subst Xs Us R).
Proof.
  introv Hr Hl He Hrs.
  assert (kindings (tenv_subst Xs Us (E1 & E2))
            Us (rngs_knds (rng_subst_list Xs Us Rs)))
    by eauto using kinding_typ_subst, rangings_kindings.
  remember (E1 & Xs ~* Rs & E2) as E3.
  induction Hr; subst; simpl;
    eauto using subtype_typ_subst, kinding_typ_subst.
  - destruct ranging_typ_subst_var
      with (E1 := E1) (E2 := E2) (E3 := tenv_subst Xs Us (E1 & E2))
           (Xs := Xs) (Rs := Rs) (Us := Us) (Ys := Xs) (Ts := Us)
           (X := X) (R := R)
      as [?|[Hb Heq]]; auto.
    rewrite Heq.
    eauto using tenv_subst_binds, rng_knd_subst.
Qed.

Lemma ranging_typ_subst_l : forall E Xs Rs Us T R,
    ranging (E & Xs ~* Rs) T R ->
    length Xs = length Rs ->
    type_environment (E & Xs ~* Rs) ->
    rangings (tenv_subst Xs Us E)
      Us (rng_subst_list Xs Us Rs) ->
    ranging (tenv_subst Xs Us E)
      (typ_subst Xs Us T) (rng_subst Xs Us R).
Proof.
  introv Hr Hl He Hrs.
  rewrite <- (concat_empty_r E).
  rewrite <- (concat_empty_r E) in Hrs.
  rewrite <- (concat_empty_r (E & Xs ~* Rs)) in Hr, He.
  eauto using ranging_typ_subst.
Qed.

Lemma rangings_typ_subst : forall E1 E2 Xs Rs1 Us Ts Rs2,
    rangings (E1 & Xs ~* Rs1 & E2) Ts Rs2 ->
    length Xs = length Rs1 ->
    type_environment (E1 & Xs ~* Rs1 & E2) ->
    rangings (tenv_subst Xs Us (E1 & E2))
      Us (rng_subst_list Xs Us Rs1) ->
    rangings (tenv_subst Xs Us (E1 & E2))
      (typ_subst_list Xs Us Ts) (rng_subst_list Xs Us Rs2).
Proof.
  introv Hrs1 Hl He Hrs2.
  remember (E1 & Xs ~* Rs1 & E2) as E3.
  induction Hrs1; subst; simpl; eauto using ranging_typ_subst.
Qed.

Lemma valid_range_typ_subst : forall E1 E2 Xs Rs Us R,
    valid_range (E1 & Xs ~* Rs & E2) R ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    rangings (tenv_subst Xs Us (E1 & E2))
      Us (rng_subst_list Xs Us Rs) ->
    valid_range (tenv_subst Xs Us (E1 & E2)) (rng_subst Xs Us R).
Proof.
  introv Hr Hl He Hrs.
  remember (E1 & Xs ~* Rs & E2) as E3.
  induction Hr; subst; simpl; eauto using subtype_typ_subst.
Qed.

Lemma valid_ranges_typ_subst : forall E1 E2 Xs Rs1 Us Rs2,
    valid_ranges (E1 & Xs ~* Rs1 & E2) Rs2 ->
    length Xs = length Rs1 ->
    type_environment (E1 & Xs ~* Rs1 & E2) ->
    rangings (tenv_subst Xs Us (E1 & E2))
      Us (rng_subst_list Xs Us Rs1) ->
    valid_ranges (tenv_subst Xs Us (E1 & E2))
      (rng_subst_list Xs Us Rs2).
Proof.
  introv Hrs1 Hl He Hrs2.
  remember (E1 & Xs ~* Rs1 & E2) as E3.
  induction Hrs1; subst; simpl; eauto using valid_range_typ_subst.
Qed.

Lemma valid_ranges_and_type_typ_subst : forall E1 E2 Xs Rs1 Us Rs2 T,
    valid_ranges_and_type (E1 & Xs ~* Rs1 & E2) Rs2 T ->
    length Xs = length Rs1 ->
    type_environment (E1 & Xs ~* Rs1 & E2) ->
    rangings (tenv_subst Xs Us (E1 & E2))
      Us (rng_subst_list Xs Us Rs1) ->
    valid_ranges_and_type (tenv_subst Xs Us (E1 & E2))
      (rng_subst_list Xs Us Rs2) (typ_subst Xs Us T).
Proof.
  introv Hrs1 Hl He Hrs2.
  assert (kindings (tenv_subst Xs Us (E1 & E2))
            Us (rngs_knds (rng_subst_list Xs Us Rs1)))
    by eauto using kinding_typ_subst, rangings_kindings.
  remember (E1 & Xs ~* Rs1 & E2) as E3.
  induction Hrs1; subst; simpl;
    eauto using valid_ranges_typ_subst, kinding_typ_subst.
Qed.

Lemma valid_scheme_typ_subst : forall E1 E2 Xs Rs Us M,
    valid_scheme (E1 & Xs ~* Rs & E2) M ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    rangings (tenv_subst Xs Us (E1 & E2))
      Us (rng_subst_list Xs Us Rs) ->
    valid_scheme (tenv_subst Xs Us (E1 & E2)) (sch_subst Xs Us M).
Proof.
  introv Hs Hl He Hrs.
  remember (E1 & Xs ~* Rs & E2) as E3.
  assert (scheme M) by auto with wellformed.
  induction Hs; subst; simpl; auto.
  apply_fresh valid_scheme_c as Ys.
  fresh_length FrYs as Hl2.
  autorewrite with rew_sch_arity in Hl2, FrYs.
  replace (tenv_subst Xs Us (E1 & E2) & Ys ~: sch_subst Xs Us M)
    with (tenv_subst Xs Us (E1 & E2 & Ys ~: M))
    by (autorewrite with rew_tenv_subst; auto with wellformed).
  rewrite <- concat_assoc; simpl.
  rewrite typ_subst_open_vars; auto with wellformed.
  rewrite <- rng_subst_list_open_vars; auto with wellformed.
  apply valid_ranges_and_type_typ_subst with Rs;
    auto using rangings_add_subst_ranges,
      type_environment_push_subst_ranges.
    rewrite ?concat_assoc; auto.
Qed.

Lemma valid_schemes_typ_subst : forall E1 E2 Xs Rs Us Ms,
    valid_schemes (E1 & Xs ~* Rs & E2) Ms ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    rangings (tenv_subst Xs Us (E1 & E2))
      Us (rng_subst_list Xs Us Rs) ->
    valid_schemes (tenv_subst Xs Us (E1 & E2))
      (sch_subst_list Xs Us Ms).
Proof.
  introv Hss Hl He Hrs.
  remember (E1 & Xs ~* Rs & E2) as E3.
  induction Hss; subst; simpl; eauto using valid_scheme_typ_subst.
Qed.

Lemma valid_tenv_aux_typ_subst : forall E1 E2 Xs Rs Us E3,
    valid_tenv_aux (E1 & Xs ~* Rs & E2) E3 ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    rangings (tenv_subst Xs Us (E1 & E2))
      Us (rng_subst_list Xs Us Rs) ->
    valid_tenv_aux (tenv_subst Xs Us (E1 & E2)) (tenv_subst Xs Us E3).
Proof.
  introv He1 Hl He2 Hrs.
  remember (E1 & Xs ~* Rs & E2) as E4.
  induction He1; subst; simpl;
    rewrite ?tenv_subst_empty, ?tenv_subst_push; auto.
  apply valid_tenv_aux_push;
    autorewrite with rew_tenv_dom;
    eauto using valid_range_typ_subst.
Qed.  

Lemma valid_tenv_typ_subst : forall E1 E2 Xs Rs Us,
    valid_tenv (E1 & Xs ~* Rs & E2) ->
    length Xs = length Rs ->
    rangings (tenv_subst Xs Us (E1 & E2))
      Us (rng_subst_list Xs Us Rs) ->
    valid_tenv (tenv_subst Xs Us (E1 & E2)).
Proof.
  introv He Hl Hrs.
  remember (E1 & Xs ~* Rs & E2) as E4.
  assert (type_environment E4) by auto with wellformed.
  destruct He as [? He]; subst.
  apply valid_tenv_aux_remove in He.
  eauto using valid_tenv_aux_typ_subst.
Qed.

Lemma valid_instance_typ_subst : forall E1 E2 Xs Rs Us Ts M,
    valid_instance (E1 & Xs ~* Rs & E2) Ts M ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    rangings (tenv_subst Xs Us (E1 & E2))
      Us (rng_subst_list Xs Us Rs) ->
    valid_instance (tenv_subst Xs Us (E1 & E2))
      (typ_subst_list Xs Us Ts) (sch_subst Xs Us M).
Proof.
  introv Hv Hl He Hrs.
  remember (E1 & Xs ~* Rs & E2) as E3.
  induction Hv; subst; simpl. 
  eapply valid_instance_c; eauto using rangings_typ_subst.
  rewrite rng_subst_list_open; auto with wellformed.
Qed.

(* *************************************************************** *)
(** * Kinding from valid_instance  *)

Lemma valid_instance_kinding : forall E Ts M,
    valid_instance E Ts M ->
    valid_scheme E M ->
    type_environment E ->
    kinding E (instance M Ts) knd_type.
Proof.
  introv Hv Hs He.
  destruct Hs as [? ? ? Hs].
  destruct Hv as [? ? ? ? Hv ?]; subst.
  pick_freshes (sch_arity M) Ys.
  assert (fresh L (sch_arity M) Ys) as Hf by auto.
  fresh_length Hf as Hl.
  specialize (Hs Ys Hf).
  inversion Hs; subst.
  destruct M; unfold instance;
    unfold bind_sch_ranges in *; simpl in *.
  assert (length Ts = length sch_ranges)
    by (erewrite <- rng_open_list_length;
        eauto using rangings_length).
  rewrite typ_subst_intro with (Xs := Ys); auto with wellformed.
  rewrite rng_subst_list_intro with (Xs := Ys) in Hv;
    auto with wellformed.
  rewrite <- tenv_subst_fresh
    with (E := E) (Xs := Ys) (Us := Ts); auto.
  assert (type_environment
            (E & Ys ~* rng_open_vars_list sch_ranges Ys))
    by (apply type_environment_push_singles;
        rewrite ?rng_open_vars_list_length; auto with wellformed).
  apply kinding_typ_subst_l
    with (Rs := rng_open_vars_list sch_ranges Ys);
      rewrite ?rng_open_vars_list_length; auto.
  rewrite tenv_subst_fresh with (E := E); auto.
  eauto using rangings_kindings.
Qed.

(* *************************************************************** *)
(** * Constructor of valid "kinds" bindings  *)

Lemma valid_tenv_aux_push_singles : forall E1 E2 Xs Rs,
    valid_tenv_aux E1 E2 ->
    fresh (dom E2) (length Rs) Xs ->
    valid_ranges E1 Rs ->
    valid_tenv_aux E1 (E2 & Xs ~* Rs).
Proof.
  introv He Hf Hrs.
  fresh_length Hf as Hl.
  generalize dependent Rs.
  induction Xs; introv Hf Hrs Hl; destruct Rs;
    try discriminate; autorewrite with rew_env_concat; auto.
  inversion Hrs; inversion Hl; destruct Hf; subst.
  apply valid_tenv_aux_push; autorewrite with rew_tenv_dom; auto.
Qed.

Lemma valid_tenv_push_singles : forall E Xs Rs,
    valid_tenv E ->
    fresh (dom E) (length Rs) Xs ->
    valid_ranges (E & Xs ~* Rs) Rs ->
    valid_tenv (E & Xs ~* Rs).
Proof.
  introv He Hf Hrs.
  fresh_length Hf as Hl.
  destruct He as [E He].
  apply valid_tenv_aux_weakening_l with (E2 := Xs ~* Rs) in He;
    auto using type_environment_push_singles with wellformed.
  auto using valid_tenv_aux_push_singles.
Qed.

Lemma valid_tenv_push_bind_sch_ranges : forall E Xs M,
    valid_tenv E ->
    fresh (dom E) (sch_arity M) Xs ->
    valid_ranges (E & Xs ~: M)
      (rng_open_vars_list (sch_ranges M) Xs) ->
    valid_tenv (E & Xs ~: M).
Proof.
  introv He Hf Hrs.
  eapply valid_tenv_push_singles; eauto.
  rewrite rng_open_vars_list_length.
  rewrite sch_arity_length in Hf.
  auto.
Qed.

Lemma disjoint_tenv_fv_kinds : forall Xs M L,
    length Xs = sch_arity M ->
    disjoint (sch_fv M \u from_list Xs) L ->
    disjoint (tenv_fv (Xs ~: M)) L.
Proof.
  introv Hl Hd.
  apply disjoint_subset_l
    with (B := rng_fv_list (sch_ranges M) \u from_list Xs);
    auto using tenv_fv_ranges.
  apply disjoint_union_l; split; auto.
  apply disjoint_subset_l with (B := sch_fv M);
    auto using sch_fv_ranges.
Qed.

Lemma rangings_singles_fvars : forall E Xs Rs,
  type_environment E ->
  ranges Rs ->
  fresh (dom E) (length Rs) Xs ->
  rangings (E & Xs ~* Rs) (typ_fvars Xs) Rs.
Proof.
  introv He Hrs Hf.
  fresh_length Hf as Hl.
  generalize dependent E.  
  generalize dependent Rs.
  induction Xs; introv Hrs Hl He Hf; destruct Rs; simpl in *;
    try discriminate; autorewrite with rew_env_concat in *; auto.
  inversion Hl; inversion Hrs; destruct Hf; subst.
  apply rangings_cons.
  - auto using ranging_var, binds_push_eq.
  - apply rangings_weakening_l; auto.
    apply type_environment_push;
      autorewrite with rew_tenv_dom;
      auto using type_environment_push_singles.
Qed.

Lemma scheme_ranges : forall Xs M,
  scheme M ->
  fresh \{} (sch_arity M) Xs ->
  ranges (rng_open_vars_list (sch_ranges M) Xs).
Proof.
  introv Hs Hf.
  fresh_length Hf as Hl.
  destruct Hs as [L M Hrs].
  pick_freshes (sch_arity M) Ys.
  assert (fresh L (sch_arity M) Ys) as Hf2 by auto.
  assert (fresh (rng_fv_list (sch_ranges M)) (length Xs) Ys)
    by (apply fresh_subset with (L := sch_fv M);
          auto using sch_fv_ranges).
  specialize (Hrs Ys Hf2).
  inversion Hrs; subst.
  unfold rng_open_vars_list.
  rewrite rng_subst_list_intro with (Xs := Ys);
    try rewrite length_typ_fvars; auto.
  rewrite rng_subst_range_list; auto.
Qed.  

Lemma rangings_fvars : forall E Xs M,
  type_environment E ->
  scheme M ->
  fresh (dom E) (sch_arity M) Xs ->
  rangings (E & Xs ~: M) (typ_fvars Xs)
    (rng_open_vars_list (sch_ranges M) Xs).
Proof.
  introv He Hs Hf.
  fresh_length Hf as Hl.
  assert (ranges (rng_open_vars_list (sch_ranges M) Xs))
    by auto using scheme_ranges.
  destruct M; unfold bind_sch_ranges; simpl in *.
  inversion Hs.
  apply rangings_singles_fvars;
    try rewrite <- length_rng_open_vars_list; auto.
Qed.

Lemma valid_ranges_change_vars : forall E M Xs Ys Rs,
    fresh (dom E \u tenv_fv E \u sch_fv M) (sch_arity M) Xs ->
    fresh (dom E \u tenv_fv E \u sch_fv M
               \u from_list Xs \u rng_fv_list Rs)
      (sch_arity M) Ys ->
    scheme M ->
    type_environment E ->
    valid_ranges (E & Xs ~: M) Rs ->
    valid_ranges (E & Ys ~: M) (rng_subst_list Xs (typ_fvars Ys) Rs).
Proof.
  introv Hf1 Hf2 Hs He Hr.
  fresh_length Hf1 as Hl1.
  fresh_length Hf2 as Hl2.
  assert (type_environment (E & Xs ~: M & Ys ~: M))
    by (apply type_environment_push_ranges;
        autorewrite with rew_tenv_dom;
        auto using type_environment_push_ranges).
  apply valid_ranges_weakening_l with (E2 := Ys ~: M) in Hr; auto.
  assert (disjoint (from_list Xs) (from_list Ys)) by auto.
  assert (disjoint (tenv_fv (Ys ~: M)) (from_list Xs))
    by auto using disjoint_tenv_fv_kinds.
  assert (fresh (rng_fv_list (sch_ranges M)) (length Ys) Xs)
    by (apply fresh_subset with (L := sch_fv M);
          auto using sch_fv_ranges).
  apply valid_ranges_typ_subst
    with (Us := typ_fvars Ys) in Hr;
    rewrite ?tenv_subst_fresh in Hr;
    rewrite ?rng_open_vars_list_length, <- ?sch_arity_length;
    autorewrite with rew_tenv_fv; auto.
  rewrite <- rng_subst_list_intro;
    try rewrite length_typ_fvars;
    auto.
  rewrite tenv_subst_fresh;
    autorewrite with rew_tenv_fv; auto.
  apply rangings_fvars; auto.
Qed.

Lemma valid_tenv_push_ranges : forall E Xs M,
    valid_tenv E ->
    fresh (dom E) (sch_arity M) Xs ->
    valid_scheme E M ->
    valid_tenv (E & Xs ~: M).
Proof.
  introv He Hf Hs.
  fresh_length Hf as Hl.
  assert (scheme M) by auto with wellformed.
  assert (disjoint (from_list Xs) (sch_fv M))
   by eauto using valid_scheme_closed_list.
  destruct Hs; subst.
  unfold bind_sch_ranges in *.
  apply valid_tenv_push_bind_sch_ranges; auto.
  pick_freshes (sch_arity M) Ys.
  assert (fresh (rng_fv_list (sch_ranges M)) (length Xs) Ys)
    by (apply fresh_subset with (L := sch_fv M);
          auto using sch_fv_ranges).
  assert (disjoint (from_list Xs) (from_list Ys)) by auto.
  assert (disjoint (from_list Xs) (tenv_fv E))
   by auto using valid_tenv_closed_list.
  assert (fresh (rng_fv_list (sch_ranges M)) (sch_arity M) Xs)
    by (apply fresh_subset with (L := sch_fv M);
          auto using sch_fv_ranges, fresh_disjoint).
  assert
    (fresh (rng_fv_list (rng_open_vars_list (sch_ranges M) Ys))
      (sch_arity M) Xs)
    by (apply fresh_subset
          with (L := rng_fv_list (sch_ranges M) \u from_list Ys);
            auto using rng_open_vars_list_fv, fresh_disjoint).
  assert (valid_ranges_and_type
            (E & Ys ~* rng_open_vars_list (sch_ranges M) Ys)
            (rng_open_vars_list (sch_ranges M) Ys)
            (typ_open_vars (sch_body M) Ys)) as Hrs by auto.
  inversion Hrs; subst.
  unfold rng_open_vars_list.
  rewrite rng_subst_list_intro with (Xs := Ys);
    try rewrite length_typ_fvars; auto.
  apply valid_ranges_change_vars with (Xs := Ys);
    eauto using fresh_disjoint with wellformed.
Qed.

(* *************************************************************** *)
(* Valid empty schemes *)

Lemma valid_scheme_empty : forall E T,
    kinding E T knd_type <-> valid_scheme E (sch_empty T).
Proof.
  split.
  - introv Hk.
    apply valid_scheme_c with (L := typ_fv T).
    introv Hf.
    simpl in Hf.
    fresh_length Hf as Hl.
    destruct Xs; simpl in Hl; try discriminate.
    unfold bind_sch_ranges; simpl.
    autorewrite with rew_env_concat.
    rewrite typ_open_vars_nil; auto.
  - introv Hv.
    remember (sch_empty T) as M.
    destruct Hv as [L E ? Hrs]; subst.
    unfold bind_sch_ranges in Hrs.
    specialize (Hrs nil).
    rewrite typ_open_vars_nil, rng_open_vars_list_nil in Hrs.
    unfold sch_empty in Hrs; simpl in Hrs;
      autorewrite with rew_env_concat in Hrs.
    destruct Hrs; auto.
Qed.

(* directed versions for use with `auto` *)
Lemma valid_scheme_empty_of_kinding : forall E T,
    kinding E T knd_type ->
    valid_scheme E (sch_empty T).
Proof.
  introv Hv.
  rewrite <- valid_scheme_empty.
  assumption.
Qed.

Lemma kinding_of_valid_scheme_empty : forall E T,
    valid_scheme E (sch_empty T) ->
    kinding E T knd_type.
Proof.
  introv Hv.
  rewrite valid_scheme_empty.
  assumption.
Qed.

(* *************************************************************** *)
(** Different ranges for the same type are subtypes *)

Lemma subtype_from_ranges : forall E T1 T2 T3 T4 T5,
    ranging E T1 (rng_range T2 T3) ->
    ranging E T1 (rng_range T4 T5) ->
    valid_tenv E ->
    subtype E T5 T2 CSet.universe.
Proof.
  introv Hr1 Hr2 He.
  remember (rng_range T2 T3) as R.
  generalize dependent T2.
  generalize dependent T3.
  induction Hr1; introv HeqR; inversion HeqR; subst.
  - remember (rng_range T4 T5) as R.
    remember (typ_fvar X) as T.
    generalize dependent T4.
    generalize dependent T5.
    induction Hr2; introv HeqR;
      inversion HeqR; inversion HeqT; subst.
    + assert
        (rng_range T2 T3 = rng_range T4 T5) as Heq
          by eauto using binds_func.
      inversion Heq; subst.
      assert (valid_range E (rng_range T4 T5)) as Hv
        by eauto using valid_range_from_valid_tenv.
      inversion Hv; subst.
      auto.
    + assert (valid_range E (rng_range T1 T0)) as Hv
        by eauto using output_ranging.
      inversion Hv; subst.
      eauto using subtype_transitive with wellformed.
  - eauto using subtype_transitive with wellformed.
Qed.

(* *************************************************************** *)
(** Ranges can be sub-kinded to the lattice bounds *)

Lemma ranging_range_top_bot : forall E T1 T2 T3,
    ranging E T1 (rng_range T2 T3) ->
    valid_tenv E ->
    ranging E T1
      (rng_range (typ_top CSet.universe) (typ_bot CSet.universe)).
Proof.
  introv Hr He.
  remember (rng_range T2 T3) as R.
  generalize dependent T2.
  generalize dependent T3.
  induction Hr; introv HeqR; inversion HeqR; subst; eauto.
  - assert (valid_range E (rng_range T2 T3)) as Hv
      by eauto using valid_range_from_valid_tenv.
    inversion Hv; subst.
    apply ranging_range_subsumption with (T1 := T2) (T2 := T3);
      eauto using subtype_top, subtype_bot,
        subtype_kinding_1, subtype_kinding_2 with wellformed.
Qed.  
