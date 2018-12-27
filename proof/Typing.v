(************************************************
 *           Row Subtyping - Typing             *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import LibLN Cofinite Disjoint Definitions Utilities
        Substitution Wellformedness Kinding Subtyping Ranging.

(* ****************************************************** *)
(** ** Add hints for constructors *)

Hint Constructors valid_env valid_store_type
  value typing typing_scheme typing_schemes.

Hint Extern 1 (typing _ _ _ (trm_abs _) _) =>
  let L' := gather_vars in
  let L' := beautify_fset L' in
  apply typing_abs with (L := L').

Hint Extern 1 (typing _ _ _ (trm_let _ _) _) =>
  let L' := gather_vars in
  let L' := beautify_fset L' in
  apply typing_let_val with (L := L').

Hint Extern 1 (typing _ _ _ (trm_let _ _) _) =>
  let L' := gather_vars in
  let L' := beautify_fset L' in
  apply typing_let with (L := L').

Hint Extern 1 (typing _ _ _ (trm_match _ _ _ _) _) =>
  let L' := gather_vars in
  let L' := beautify_fset L' in
  apply typing_match with (L := L').

Hint Extern 1 (typing _ _ _ (trm_destruct _ _ _) _) =>
  let L' := gather_vars in
  let L' := beautify_fset L' in
  apply typing_destruct with (L := L').

Hint Extern 1 (typing _ _ _ (trm_fix _) _) =>
  let L' := gather_vars in
  let L' := beautify_fset L' in
  apply typing_fix with (L := L').

Hint Extern 1 (typing_scheme _ _ _ _ _) =>
  let L' := gather_vars in
  let L' := beautify_fset L' in
  apply typing_scheme_c with (L := L').

(* *************************************************************** *)
(** Length of typing_schemes *)

Lemma typing_schemes_length : forall E D P ts Ms,
  typing_schemes E D P ts Ms ->
  length ts = length Ms.
Proof.
  introv Hss.
  induction Hss; simpl; auto.
Qed.

(* *************************************************************** *)
(** Valid bindings *)

Lemma valid_scheme_from_valid_env : forall X E D M,
    valid_env E D ->
    binds X M D ->
    valid_scheme E M.
Proof.
  introv He Hb.
  induction He.
  - apply binds_empty_inv in Hb; contradiction.
  - destruct (binds_push_inv Hb) as [[Hx Hbnd]|[Hx Hbnd]];
      subst; auto.
Qed.

(* *************************************************************** *)
(** Valid output *)

Lemma output_typing : forall E D P t T,
  typing E D P t T ->
  type_environment E ->
  kinding E T knd_type.
Proof.
  introv Ht He.
  induction Ht; auto with fresh kinding.
  - eauto using ranging_kinding.
Qed.

Lemma output_typing_scheme : forall E D P t M,
  typing_scheme E D P t M ->
  valid_scheme E M.
Proof.
  introv Hs.
  destruct Hs; auto.
Qed.

(* ****************************************************** *)
(** ** Typing empty scheme *)

Lemma typing_scheme_empty : forall E D P t T,
    type_environment E ->
    typing E D P t T <-> typing_scheme E D P t (sch_empty T).
Proof.
  introv He.
  split; introv Ht.
  - assert (kinding E T knd_type)
      by eauto using output_typing.
    apply typing_scheme_c with (L := \{});
      try rewrite <- valid_scheme_empty;
      simpl; auto.
    introv Hf.
    fresh_length Hf as Hl.
    destruct Xs; try discriminate.
    unfold sch_empty, instance_vars, instance, bind_sch_ranges;
      simpl; autorewrite with rew_env_concat;
        rewrite typ_open_nil; auto.
  - remember (sch_empty T) as M.
    destruct Ht; subst.
    unfold sch_empty, instance_vars, instance, bind_sch_ranges in *;
      simpl in *.
    assert
      (typing (E & nil ~* nil) D P t
         (typ_open T (typ_fvars nil))) by auto.
    simpl in *; autorewrite with rew_env_concat in *;
      rewrite typ_open_nil in *; auto.
Qed.

(* ****************************************************** *)
(** ** Weakening type environment *)

Lemma typing_tenv_weakening : forall E1 E2 E3 D P t T,
    typing (E1 & E3) D P t T ->
    type_environment (E1 & E2 & E3) ->
    typing (E1 & E2 & E3) D P t T.
Proof.
  introv Ht He.
  remember (E1 & E3) as E13.
  generalize dependent E3.
  induction Ht; introv Heq He; subst;
    eauto using binds_env_weakening,
      kinding_weakening, subtype_weakening, type_equal_weakening,
      ranging_weakening, valid_instance_weakening.
  - apply typing_let_val
      with (M := M) (L := L \u dom E1 \u dom E2 \u dom E3);
      eauto using valid_scheme_weakening.
    intros Xs Hf.
    assert (type_environment (E1 & E2 & E3 & Xs ~: M)) as He2
      by (apply type_environment_push_ranges;
          autorewrite with rew_tenv_dom; auto with wellformed).
    rewrite <- concat_assoc.
    rewrite <- concat_assoc in He2.
    auto using concat_assoc.
  - eapply typing_match with (T1 := T1) (T2 := T2) (T3 := T3);
      eauto using binds_env_weakening,
        kinding_weakening, subtype_weakening, type_equal_weakening,
        ranging_weakening, valid_instance_weakening.
  - eapply typing_destruct with (T1 := T1) (T2 := T2) (T3 := T3);
      eauto using binds_env_weakening,
        kinding_weakening, subtype_weakening, type_equal_weakening,
        ranging_weakening, valid_instance_weakening.
Qed.    

Lemma typing_tenv_weakening_l : forall E1 E2 D P t T,
    typing E1 D P t T ->
    type_environment (E1 & E2) ->
    typing (E1 & E2) D P t T.
Proof.
  introv Ht He.
  rewrite <- concat_empty_r with (E := E1 & E2).
  apply typing_tenv_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma typing_scheme_tenv_weakening : forall E1 E2 E3 D P t M,
    typing_scheme (E1 & E3) D P t M ->
    type_environment (E1 & E2 & E3) ->
    typing_scheme (E1 & E2 & E3) D P t M.
Proof.
  introv Ht He.
  remember (E1 & E3) as E13.
  destruct Ht; subst.
  apply typing_scheme_c
    with (L := L \u dom E1 \u dom E2 \u dom E3);
      eauto using valid_scheme_weakening.
  intros Xs Hf.
  assert (type_environment (E1 & E2 & E3 & Xs ~: M)) as He2
    by (apply type_environment_push_ranges;
        autorewrite with rew_tenv_dom; auto with wellformed).
  rewrite <- concat_assoc.
  apply typing_tenv_weakening;
    rewrite concat_assoc;
    eauto using valid_scheme_weakening.
Qed.

Lemma typing_schemes_tenv_weakening : forall E1 E2 E3 D P ts Ms,
    typing_schemes (E1 & E3) D P ts Ms ->
    type_environment (E1 & E2 & E3) ->
    typing_schemes (E1 & E2 & E3) D P ts Ms.
Proof.
  introv Ht He.
  remember (E1 & E3) as E13.
  induction Ht; subst;
    auto using typing_scheme_tenv_weakening.
Qed.

Lemma typing_schemes_tenv_weakening_l : forall E1 E2 D P ts Ms,
    typing_schemes E1 D P ts Ms ->
    type_environment (E1 & E2) ->
    typing_schemes (E1 & E2) D P ts Ms.
Proof.
  introv Ht Hv.
  rewrite <- concat_empty_r with (E := E1 & E2).
  apply typing_schemes_tenv_weakening;
    rewrite concat_empty_r; assumption.
Qed.

Lemma valid_store_type_weakening : forall E1 E2 E3 P,
    valid_store_type (E1 & E3) P ->
    type_environment (E1 & E2 & E3) ->
    valid_store_type (E1 & E2 & E3) P.
Proof.
  introv Hv He.
  remember (E1 & E3) as E13.
  induction Hv; subst; auto using kinding_weakening.
Qed.

Lemma valid_store_type_weakening_l : forall E1 E2 P,
    valid_store_type E1 P ->
    type_environment (E1 & E2) ->
    valid_store_type (E1 & E2) P.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E1 & E2).
  apply valid_store_type_weakening;
    rewrite concat_empty_r; auto.
Qed.

(* ****************************************************** *)
(** ** Type subtitution *)

Lemma typing_typ_subst : forall E1 E2 Xs Rs Us D P t T,
    typing (E1 & Xs ~* Rs & E2) D P t T ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    rangings (tenv_subst Xs Us (E1 & E2))
      Us (rng_subst_list Xs Us Rs) ->
    typing (tenv_subst Xs Us (E1 & E2))
      (env_subst Xs Us D) (styp_subst Xs Us P) t
           (typ_subst Xs Us T).
Proof.
  introv Ht Hl He Hrs.
  remember (E1 & Xs ~* Rs & E2) as E3 in Ht.
  generalize dependent E2.
  induction Ht; introv Heq He Hrs; subst; eauto.
  - eapply typing_var;
      eauto using env_subst_binds, valid_instance_typ_subst.
    rewrite <- sch_subst_instance;
      eauto using type_equal_typ_subst with wellformed.
  - assert (kindings (tenv_subst Xs Us (E1 & E2))
            Us (rngs_knds (rng_subst_list Xs Us Rs)))
      by eauto using kinding_typ_subst, rangings_kindings.
    apply_fresh typing_abs as x;
      eauto using kinding_typ_subst.
    fold (typ_subst Xs Us T1).
    replace (sch_empty (typ_subst Xs Us T1))
      with (sch_subst Xs Us (sch_empty T1)) by reflexivity.
    rewrite <- env_subst_push.
    auto.
  - apply typing_let_val
      with (L := L \u from_list Xs \u dom E1 \u dom E2)
           (M := sch_subst Xs Us M);
      eauto using valid_scheme_typ_subst.
    + introv Hf.
      autorewrite with rew_sch_arity in Hf.
      fresh_length Hf as Hl2.
      rewrite <- tenv_subst_ranges;
        autorewrite with rew_env_dom; auto with wellformed.
      rewrite <- tenv_subst_concat.
      rewrite <- concat_assoc.
      unfold instance_vars.
      rewrite <- typ_subst_fresh_typ_fvars
        with (Xs := Xs) (Us := Us); auto.
      rewrite <- sch_subst_instance; auto with wellformed.
      eauto using concat_assoc, rangings_add_subst_ranges,
        type_environment_push_subst_ranges
          with wellformed.
    + introv Hn.
      rewrite <- env_subst_push; auto.
  - apply typing_let
      with (L := L \u from_list Xs \u dom E1 \u dom E2)
             (T1 := typ_subst Xs Us T1); auto.
    introv Hn.
    replace (sch_empty (typ_subst Xs Us T1))
      with (sch_subst Xs Us (sch_empty T1)) by reflexivity.
    rewrite <- env_subst_push; auto.
  - apply typing_constructor
      with (T2 := typ_subst Xs Us T2) (T3 := typ_subst Xs Us T3); auto.
    + replace (rng_range_above (typ_subst Xs Us T2))
        with (rng_subst Xs Us (rng_range_above T2))
        by reflexivity.
      eauto using ranging_typ_subst.
    + replace (typ_constructor c (typ_subst Xs Us T3))
        with (typ_subst Xs Us (typ_constructor c T3))
        by reflexivity.
      replace (typ_proj CSet.universe (typ_subst Xs Us T2)
                        (CSet.singleton c))
        with (typ_subst Xs Us (typ_proj CSet.universe T2
                                        (CSet.singleton c)))
        by reflexivity.
      eauto using subtype_typ_subst.
  - apply typing_match
      with (T1 := typ_subst Xs Us T1) (T2 := typ_subst Xs Us T2)
           (T3 := typ_subst Xs Us T3) (T4 := typ_subst Xs Us T4)
           (T5 := typ_subst Xs Us T5) (T6 := typ_subst Xs Us T6)
           (T7 := typ_subst Xs Us T7)
           (L := L \u dom E1 \u dom E2); auto.
    + replace (rng_range_below (typ_subst Xs Us T2))
        with (rng_subst Xs Us (rng_range_below T2))
        by reflexivity.
      eauto using ranging_typ_subst.
    + replace (rng_range_above (typ_subst Xs Us T4))
        with (rng_subst Xs Us (rng_range_above T4))
        by reflexivity.
      eauto using ranging_typ_subst.
    + replace (rng_range_above (typ_subst Xs Us T6))
        with (rng_subst Xs Us (rng_range_above T6))
        by reflexivity.
      eauto using ranging_typ_subst.
    + replace
        (typ_proj CSet.universe (typ_subst Xs Us T2)
           (CSet.singleton c))
        with (typ_subst Xs Us
                (typ_proj CSet.universe T2 (CSet.singleton c)))
        by reflexivity.
      replace (typ_constructor c (typ_subst Xs Us T7))
        with (typ_subst Xs Us (typ_constructor c T7)) by reflexivity.
      eauto using subtype_typ_subst.
    + replace
        (typ_proj CSet.universe (typ_subst Xs Us T2)
           (CSet.singleton c))
        with (typ_subst Xs Us
                (typ_proj CSet.universe T2 (CSet.singleton c)))
        by reflexivity.
      replace
        (typ_proj CSet.universe (typ_subst Xs Us T4)
           (CSet.singleton c))
        with (typ_subst Xs Us
                (typ_proj CSet.universe T4 (CSet.singleton c)))
        by reflexivity.
      eauto using subtype_typ_subst.
    + replace
        (typ_proj
           CSet.universe (typ_subst Xs Us T2) (CSet.cosingleton c))
        with (typ_subst Xs Us
                (typ_proj CSet.universe T2 (CSet.cosingleton c)))
        by reflexivity.
      replace
        (typ_proj
           CSet.universe (typ_subst Xs Us T6) (CSet.cosingleton c))
        with (typ_subst Xs Us
                (typ_proj CSet.universe T6 (CSet.cosingleton c)))
        by reflexivity.
      eauto using subtype_typ_subst.
    + replace (sch_empty (typ_variant (typ_subst Xs Us T3)))
        with (sch_subst Xs Us (sch_empty (typ_variant T3)))
        by reflexivity.
      introv Hn.
      rewrite <- env_subst_push.
      auto.
    + replace (sch_empty (typ_variant (typ_subst Xs Us T5)))
        with (sch_subst Xs Us (sch_empty (typ_variant T5)))
        by reflexivity.
      introv Hn.
      rewrite <- env_subst_push.
      auto.
  - apply typing_destruct
      with (T1 := typ_subst Xs Us T1) (T2 := typ_subst Xs Us T2)
           (T3 := typ_subst Xs Us T3)
           (L := L \u dom E1 \u dom E2); auto.
    + replace (rng_range_below (typ_subst Xs Us T2))
        with (rng_subst Xs Us (rng_range_below T2))
        by reflexivity.
      eauto using ranging_typ_subst.
    + replace
        (typ_proj CSet.universe (typ_subst Xs Us T2)
           (CSet.singleton c))
        with (typ_subst Xs Us
                (typ_proj CSet.universe T2 (CSet.singleton c)))
        by reflexivity.
      replace (typ_constructor c (typ_subst Xs Us T3))
        with (typ_subst Xs Us (typ_constructor c T3)) by reflexivity.
      eauto using subtype_typ_subst.
    + replace
        (typ_proj
           CSet.universe (typ_subst Xs Us T2) (CSet.cosingleton c))
        with (typ_subst Xs Us
                (typ_proj CSet.universe T2 (CSet.cosingleton c)))
        by reflexivity.
      replace (typ_bot (CSet.cosingleton c))
        with (typ_subst Xs Us (typ_bot (CSet.cosingleton c)))
        by reflexivity.
      eauto using subtype_typ_subst.
    + replace (sch_empty (typ_subst Xs Us T3))
        with (sch_subst Xs Us (sch_empty T3)) by reflexivity.
      introv Hn.
      rewrite <- env_subst_push.
      auto.
  - assert (kindings (tenv_subst Xs Us (E1 & E2))
            Us (rngs_knds (rng_subst_list Xs Us Rs)))
      by eauto using kinding_typ_subst, rangings_kindings.
    apply typing_absurd with (T1 := typ_subst Xs Us T1);
      eauto using kinding_typ_subst.
    + replace (rng_range_below (typ_bot CSet.universe))
        with (rng_subst Xs Us
                (rng_range_below (typ_bot CSet.universe)))
        by reflexivity.
      eauto using ranging_typ_subst.
  - assert (kindings (tenv_subst Xs Us (E1 & E2))
            Us (rngs_knds (rng_subst_list Xs Us Rs)))
      by eauto using kinding_typ_subst, rangings_kindings.
    apply_fresh typing_fix as x; eauto using kinding_typ_subst.
    introv Hn1 Hn2.
    fold (typ_subst Xs Us (typ_arrow T1 T2)).
    replace (sch_empty (typ_subst Xs Us (typ_arrow T1 T2)))
      with (sch_subst Xs Us (sch_empty (typ_arrow T1 T2)))
      by reflexivity.
    fold (typ_subst Xs Us T1).
    replace (sch_empty (typ_subst Xs Us T1))
      with (sch_subst Xs Us (sch_empty T1)) by reflexivity.
    rewrite <- env_subst_push.
    rewrite <- env_subst_push.
    auto.
  - apply typing_prod; auto.
  - apply typing_loc with (T1 := typ_subst Xs Us T1);
      eauto using styp_subst_binds.
    eauto using type_equal_typ_subst.
  - apply typing_ref; auto.
Qed.

Lemma typing_typ_subst_l : forall E Xs Rs Us D P t T,
    typing (E & Xs ~* Rs) D P t T ->
    length Xs = length Rs ->
    type_environment (E & Xs ~* Rs) ->
    rangings (tenv_subst Xs Us E)
      Us (rng_subst_list Xs Us Rs) ->
    typing (tenv_subst Xs Us E)
      (env_subst Xs Us D) (styp_subst Xs Us P) t
           (typ_subst Xs Us T).
Proof.
  introv Ht Hl He Hrs.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r with (E := E & Xs ~* Rs) in He, Ht.
  rewrite <- concat_empty_r with (E := E) in Hrs.
  eauto using typing_typ_subst.
Qed.

Lemma typing_instance : forall E M D P t Us,
  typing_scheme E D P t M ->
  valid_instance E Us M ->
  type_environment E ->
  typing E D P t (instance M Us). 
Proof.
  introv Hs Hv He.
  destruct Hs.
  pick_freshes (sch_arity M) Xs.
  fresh_length Fr as Hl.
  inversion Hv; subst; simpl in *.
  assert (type_environment (E & Xs ~: M))
    by auto using type_environment_push_ranges with wellformed.
  assert (length Us = sch_arity M)
    by (erewrite rangings_length,
          <- length_rng_open_list, sch_arity_length; eauto).
  rewrite typ_subst_intro_instance with (Xs := Xs);
    auto with wellformed.
  unfold bind_sch_ranges, instance_vars, instance in *.
  destruct M; simpl in *.
  rewrite <- styp_subst_fresh with (Xs := Xs) (Us := Us) (P := P);
    auto.
  rewrite <- env_subst_fresh with (Xs := Xs) (Us := Us) (D := D);
    auto.
  rewrite <- tenv_subst_fresh with (Xs := Xs) (Us := Us) (E := E);
    auto.
  apply typing_typ_subst_l
    with (Rs := rng_open_vars_list sch_ranges Xs);
    rewrite <- ?length_rng_open_vars_list; auto. 
  rewrite tenv_subst_fresh with (Xs := Xs) (Us := Us) (E := E); auto.
  rewrite <- rng_subst_list_intro; auto with wellformed.
Qed.

(* ****************************************************** *)
(** ** Respects type equality *)

Lemma typing_equal_binding : forall E D1 D2 T1 T2 x P t T,
    type_equal E T1 T2 knd_type ->
    type_environment E ->
    environment (D1 & x ~ sch_empty T1 & D2) ->
    typing E (D1 & x ~ sch_empty T1 & D2) P t T ->
    typing E (D1 & x ~ sch_empty T2 & D2) P t T.
Proof.
  introv Hte He1 He2 Ht.
  assert (scheme (sch_empty T2))
    by auto with wellformed.
  assert (environment (D1 & x ~ sch_empty T2 & D2)) as He3
    by eauto using environment_middle, environment_middle_inv_env,
       environment_middle_inv_fresh with wellformed.
  remember (D1 & x ~ sch_empty T1 & D2) as D3.
  remember (D1 & x ~ sch_empty T2 & D2) as D4.
  symmetry in HeqD3.
  symmetry in HeqD4.
  generalize dependent D2.
  generalize dependent D4.
  induction Ht; introv He Heq1 Heq2; eauto.
  - subst.
    case_if_eq x x0.
    + { assert (binds x0 M (D1 & x0 ~ sch_empty T1 & D2)) as Hb
          by assumption.
        apply binds_middle_eq_inv in Hb;
          auto using ok_from_environment; subst.
        assert (valid_instance E Us (sch_empty T1)) as Hi by assumption.
        inversion Hi; subst.
        apply typing_var with (M := sch_empty T2) (Us := nil); eauto.
        - eauto using binds_middle_eq,
            ok_middle_inv_r, ok_from_environment.
        - assert (length Us = 0) as Hl
           by (erewrite rangings_length; eauto; simpl; auto).
          rewrite List.length_zero_iff_nil in Hl; subst.
          rewrite instance_empty_nil in *.
          apply type_equal_transitive with (T2 := T1); auto. }
    + apply typing_var with (M := M) (Us := Us);
        eauto using binds_env_weakening, binds_subst.
  - apply typing_abs
      with (L := L \u dom E \u dom D \u dom D4); auto; subst.
    introv Hn.
    eauto 6 using concat_assoc with wellformed.
  - apply typing_let_val
      with (L := L \u dom E \u dom D \u dom D4) (M := M); auto; subst.
    + introv Hf.
      eauto using type_equal_weakening_l,
        type_environment_push_ranges with wellformed.
    + introv Hn.
      eauto using concat_assoc with wellformed.
  - apply typing_let
      with (L := L \u dom E \u dom D \u dom D4) (T1 := T0);
      eauto; subst.
    introv Hn.
    assert (type T0) by eauto using output_typing, wellformed_kinding.
    eauto 6 using concat_assoc with wellformed.
  - apply typing_match
      with (L := L \u dom E \u dom D \u dom D4) (T1 := T0)
           (T2 := T3) (T3 := T4) (T4 := T5) (T5 := T6)
           (T6 := T7) (T7 := T8); subst; eauto.
    + introv Hn.
      assert (type (typ_variant T4)) by auto with wellformed.
      eauto 6 using concat_assoc with wellformed.
    + introv Hn.
      assert (type (typ_variant T6)) by auto with wellformed.
      eauto 6 using concat_assoc with wellformed.      
  - apply typing_destruct
      with (L := L \u dom E \u dom D \u dom D4) (T1 := T0)
           (T2 := T3) (T3 := T4) (T4 := T5); subst; eauto.
    introv Hn.
    assert (kinding E T4 knd_type) by auto with kinding.
    eauto 6 using concat_assoc with wellformed.  
  - apply typing_fix with (L := L \u dom E \u dom D \u dom D4);
      subst; auto.
    introv Hn1 Hn2.
    assert (type T0) by auto with wellformed.
    assert (type (typ_arrow T0 T3)) by auto with wellformed.
    assert (environment
              (D1 & x ~ sch_empty T1 & D2
               & x0 ~ sch_empty (typ_arrow T0 T3)
               & y ~ sch_empty T0))
      by eauto using environment_push2 with wellformed.
    assert (environment
              (D1 & x ~ sch_empty T2 & D2
               & x0 ~ sch_empty (typ_arrow T0 T3)
               & y ~ sch_empty T0))
      by eauto using environment_push2 with wellformed.
    eauto using concat_assoc2.
Qed.

Lemma typing_equal_binding_l : forall E D T1 T2 x P t T,
    type_equal E T1 T2 knd_type ->
    type_environment E ->
    environment (D & x ~ sch_empty T1) ->
    typing E (D & x ~ sch_empty T1) P t T ->
    typing E (D & x ~ sch_empty T2) P t T.
Proof.
  introv Hte He1 He2 Ht.
  rewrite <- concat_empty_r
    with (E := D & x ~ sch_empty T2).
  rewrite <- concat_empty_r
    with (E := D & x ~ sch_empty T1) in Ht, He2.
  eauto using typing_equal_binding.
Qed.

Lemma typing_equal_binding_l2 : forall E D T1 T1' T2 T2' x y P t T,
    type_equal E T1 T1' knd_type ->
    type_equal E T2 T2' knd_type ->
    type_environment E ->
    environment (D & x ~ sch_empty T1 & y ~ sch_empty T2) ->
    typing E (D & x ~ sch_empty T1 & y ~ sch_empty T2) P t T ->
    typing E (D & x ~ sch_empty T1' & y ~ sch_empty T2') P t T.
Proof.
  introv Hte1 Hte2 He1 He2 Ht.
  assert (environment (D & x ~ sch_empty T1 & y ~ sch_empty T2'))
    by eauto using environment_concat_inv_l,
       environment_push_inv_fresh with wellformed.
  apply typing_equal_binding with (T1 := T1); auto.
  apply typing_equal_binding_l with (T1 := T2); auto.
Qed.

Lemma typing_equal_cong : forall E D P t T1 T2,
    type_equal_cong E T1 T2 knd_type ->
    type_environment E ->
    environment D ->
    typing E D P t T1 ->
    typing E D P t T2.
Proof.
  introv Hte He1 He2 Ht.
  generalize dependent T2.
  induction Ht; introv Hte.
  - apply typing_var with (M := M) (Us := Us); auto.
    apply type_equal_transitive with (T2 := T); auto.
    auto using type_equal_single, type_equal_cong_symmetric.
  - inversion Hte; subst.
    + apply typing_abs with (L := L \u dom D);
        auto with kinding.
      introv Hn.
      apply typing_equal_binding_l with (T1 := T1);
        auto using type_equal_single with wellformed.
    + apply typing_abs with (L := L \u dom D);
        auto with wellformed.
    + exfalso; eauto using type_equal_symm_inv_type.
  - eauto using output_typing.
  - apply typing_let_val with (L := L \u dom E \u dom D) (M := M);
      auto with wellformed.   
  - apply typing_let with (L := L \u dom E \u dom D) (T1 := T1);
      eauto 6 using output_typing, wellformed_kinding.
  - inversion Hte; subst.
    + assert (type_equal_cong E T1 T1' knd_range) as Heq
          by assumption.
      inversion Heq; subst.
      exfalso; eauto using type_equal_symm_inv_range.
    + exfalso; eauto using type_equal_symm_inv_type.
  - apply typing_match
      with (L := L \u dom D) (T1 := T1) (T2 := T2) (T3 := T3)
           (T4 := T4) (T5 := T5) (T6 := T6) (T7 := T7);
      auto with wellformed.
  - assert (kinding E T3 knd_type) by auto with kinding.
    apply typing_destruct
      with (L := L \u dom D) (T1 := T1)
           (T2 := T2) (T3 := T3); auto with wellformed.
  - eauto with kinding.
  - inversion Hte; subst.
    + apply typing_fix with (L := L \u dom D);
        auto with kinding.
      introv Hn1 Hn2.
      apply typing_equal_binding_l2
        with (T1 := typ_arrow T1 T2) (T2 := T1);
        eauto with kinding wellformed.
    + apply typing_fix with (L := L \u dom D);
        auto with kinding.
      introv Hn1 Hn2.
      apply typing_equal_binding_l2
        with (T1 := typ_arrow T1 T2) (T2 := T1);
        eauto using environment_push2 with kinding wellformed.
    + exfalso; eauto using type_equal_symm_inv_type.
  - inversion Hte.
    exfalso; eauto using type_equal_symm_inv_type.
  - inversion Hte; subst; auto.
    exfalso; eauto using type_equal_symm_inv_type.
  - assert (kinding E (typ_prod T1 T2) knd_type) by
      eauto using output_typing.
    eauto with kinding.
  - assert (kinding E (typ_prod T1 T2) knd_type) by
      eauto using output_typing.
    eauto with kinding.
  - inversion Hte; subst.
    + assert (type_equal E T1 T1' knd_type)
        by eauto using type_equal_post_step.
      eauto.
    + exfalso; eauto using type_equal_symm_inv_type.
  - inversion Hte; subst; auto.
    exfalso; eauto using type_equal_symm_inv_type.
  - auto.
  - inversion Hte.
    exfalso; eauto using type_equal_symm_inv_type.
Qed.

Lemma typing_equal : forall E D P t T1 T2,
    type_equal E T1 T2 knd_type ->
    type_environment E ->
    environment D ->
    typing E D P t T1 ->
    typing E D P t T2.
Proof.
  introv Hte He1 He2 Ht.
  remember knd_type as K.
  induction Hte; subst;
    eauto using typing_equal_cong.
Qed.

(* ****************************************************** *)
(** ** Weakening term environment *)

Lemma typing_env_weakening : forall E D1 D2 D3 P t T,
    typing E (D1 & D3) P t T ->
    type_environment E ->
    environment (D1 & D2 & D3) ->
    typing E (D1 & D2 & D3) P t T.
Proof.
  introv Ht He1 He2.
  remember (D1 & D3) as D13.
  generalize dependent D3.
  induction Ht; introv Heq He; subst;
    eauto using binds_env_weakening.
  - apply typing_abs with (L \u dom D1 \u dom D2 \u dom D3); auto.
    intros x Hn.
    assert (environment (D1 & D2 & D3 & x ~ sch_empty T1)) as He3
      by auto with wellformed.
    rewrite <- concat_assoc.
    rewrite <- concat_assoc in He3.
    auto using concat_assoc.
  - apply typing_let_val
      with (L := L \u dom E \u dom D1 \u dom D2 \u dom D3) (M := M);
      auto using type_environment_push_ranges with wellformed.
    intros x Hn.
    assert (environment (D1 & D2 & D3 & x ~ M)) as He3
      by auto with wellformed.
    rewrite <- concat_assoc.
    rewrite <- concat_assoc in He3.
    auto using concat_assoc.
  - apply typing_let
      with (L := L \u dom D1 \u dom D2 \u dom D3) (T1 := T1);
      auto.
    intros x Hn.
    assert (kinding E T1 knd_type) by eauto using output_typing.
    assert (environment (D1 & D2 & D3 & x ~ sch_empty T1)) as He2
      by auto with wellformed.
    rewrite <- concat_assoc.
    rewrite <- concat_assoc in He2.
    auto using concat_assoc.
  - apply typing_match
      with (L := L \u dom D1 \u dom D2 \u dom D3) (T1 := T1)
           (T2 := T2) (T3 := T3) (T4 := T4) (T5 := T5) (T6 := T6)
           (T7 := T7); auto.
    + intros x Hn.
      assert (environment
                (D1 & D2 & D3
                 & x ~ sch_empty (typ_variant T3))) as He3
        by auto with wellformed.
      rewrite <- concat_assoc.
      rewrite <- concat_assoc in He3.
      auto using concat_assoc.
    + intros x Hn.
      assert (environment
                (D1 & D2 & D3
                 & x ~ sch_empty (typ_variant T5))) as He3
        by auto with wellformed.
      rewrite <- concat_assoc.
      rewrite <- concat_assoc in He3.
      auto using concat_assoc.
  - apply typing_destruct
      with (L := L \u dom D1 \u dom D2 \u dom D3) (T1 := T1)
           (T2 := T2) (T3 := T3); auto.
    intros x Hn.
    assert (kinding E T3 knd_type) by auto with kinding.
    assert (environment (D1 & D2 & D3 & x ~ sch_empty T3)) as He2
      by auto with wellformed.
    rewrite <- concat_assoc.
    rewrite <- concat_assoc in He2.
    auto using concat_assoc.
  - apply typing_fix
      with (L := L \u dom D1 \u dom D2 \u dom D3); auto.
    intros x y Hn1 Hn2.
(*    assert (kinding E T3 knd_type) by auto with kinding. *)
    assert (environment
              (D1 & D2 & D3
               & x ~ sch_empty (typ_arrow T1 T2)
               & y ~ sch_empty T1)) as He2
      by auto with wellformed.
    rewrite <- concat_assoc2.
    rewrite <- concat_assoc2 in He2.
    auto using concat_assoc2.
Qed.    

Lemma typing_env_weakening_l : forall E D1 D2 P t T,
    typing E D1 P t T ->
    type_environment E ->
    environment (D1 & D2) ->
    typing E (D1 & D2) P t T.
Proof.
  introv Ht He1 He2.
  rewrite <- concat_empty_r with (E := D1 & D2).
  apply typing_env_weakening; rewrite ?concat_empty_r; auto.
Qed.

Lemma typing_scheme_env_weakening : forall E D1 D2 D3 P t M,
    typing_scheme E (D1 & D3) P t M ->
    type_environment E ->
    environment (D1 & D2 & D3) ->
    typing_scheme E (D1 & D2 & D3) P t M.
Proof.
  introv Ht He1 He2.
  remember (D1 & D3) as D13.
  destruct Ht; subst.
  apply typing_scheme_c
    with (L := L \u dom E \u dom D1 \u dom D2 \u dom D3);
      eauto using valid_scheme_weakening.
  intros Xs Hf.
  apply typing_env_weakening;
    auto using type_environment_push_ranges with wellformed.
Qed.

Lemma typing_schemes_env_weakening : forall E D1 D2 D3 P ts Ms,
    typing_schemes E (D1 & D3) P ts Ms ->
    type_environment E ->
    environment (D1 & D2 & D3) ->
    typing_schemes E (D1 & D2 & D3) P ts Ms.
Proof.
  introv Ht He1 He2.
  remember (D1 & D3) as D13.
  induction Ht; subst;
    auto using typing_scheme_env_weakening.
Qed.

Lemma typing_schemes_env_weakening_l : forall E D1 D2 P ts Ms,
    typing_schemes E D1 P ts Ms ->
    type_environment E ->
    environment (D1 & D2) ->
    typing_schemes E (D1 & D2) P ts Ms.
Proof.
  introv Ht He1 He2.
  rewrite <- concat_empty_r with (E := D1 & D2).
  apply typing_schemes_env_weakening;
    rewrite ?concat_empty_r; auto.
Qed.

(* *************************************************************** *)
(** Somes useful for proofs about term subtitution *)

Lemma typing_schemes_add_subst_typ_bind :
  forall E D1 D2 P x M Ms ts,
    x \notin (dom D1 \u dom D2) ->
    typing_schemes E (D1 & D2) P ts Ms ->
    scheme M ->
    type_environment E ->
    environment (D1 & D2) ->
    typing_schemes E (D1 & (D2 & x ~ M)) P ts Ms.
Proof.
  introv Hn Hss Hs He1 He2.
  rewrite concat_assoc.
  apply typing_schemes_env_weakening_l; auto.
Qed.

Lemma typing_schemes_add_subst_typ_bind_empty :
  forall E D1 D2 P x T Ms ts,
    x \notin (dom D1 \u dom D2) ->
    typing_schemes E (D1 & D2) P ts Ms ->
    type T ->
    type_environment E ->
    environment (D1 & D2) ->
    typing_schemes E (D1 & (D2 & x ~ sch_empty T)) P ts Ms.
Proof.
  introv Hn Hss Hk He1 He2.
  apply typing_schemes_add_subst_typ_bind; auto.
Qed.

Lemma typing_schemes_add_subst_typ_bind_empty2 :
  forall E D1 D2 P x T y U Ms ts,
    x \notin (dom D1 \u dom D2) ->
    y \notin (dom D1 \u dom D2 \u \{x}) ->
    typing_schemes E (D1 & D2) P ts Ms ->
    type T ->
    type U ->
    type_environment E ->
    environment (D1 & D2) ->
    typing_schemes
      E (D1 & (D2 & x ~ sch_empty T & y ~ sch_empty U)) P ts Ms.
Proof.
  introv Hn1 Hn2 Hss Hk1 Hk2 He1 He2.
  rewrite concat_assoc2.
  apply typing_schemes_env_weakening_l;
    auto using environment_push2.
  apply typing_schemes_env_weakening_l; auto.
Qed.  

Lemma typing_schemes_add_subst_kinds_bind :
  forall E D1 D2 P Xs M Ms ts,
    fresh (dom E) (sch_arity M) Xs ->
    typing_schemes E (D1 & D2) P ts Ms ->
    scheme M ->
    type_environment E ->
    typing_schemes (E & Xs ~: M) (D1 & D2) P ts Ms.
Proof.
  introv Hf Hss Hs He.
  apply typing_schemes_tenv_weakening_l;
    auto using type_environment_push_ranges.
Qed.

Lemma type_environment_add_subst_typ_bind : forall D1 D2 xs Ms x M,
    environment (D1 & xs ~* Ms & D2) ->
    length xs = length Ms ->
    x \notin (dom D1 \u from_list xs \u dom D2) ->
    scheme M ->
    environment (D1 & xs ~* Ms & D2 & x ~ M).
Proof.
  introv He Hl Hn Hs.
  apply environment_push; autorewrite with rew_env_dom; auto.
Qed.

Lemma environment_add_subst_typ_bind :
    forall D1 D2 xs Ms x M,
    environment (D1 & xs ~* Ms & D2) ->
    length xs = length Ms ->
    x \notin (dom D1 \u from_list xs \u dom D2) ->
    scheme M ->
    environment (D1 & xs ~* Ms & D2 & x ~ M).
Proof.
  introv He Hl Hn Hk.
  apply environment_push; autorewrite with rew_env_dom; auto.
Qed.

Lemma environment_add_subst_typ_bind_empty :
    forall D1 D2 xs Ms x T,
    environment (D1 & xs ~* Ms & D2) ->
    length xs = length Ms ->
    x \notin (dom D1 \u from_list xs \u dom D2) ->
    type T ->
    environment (D1 & xs ~* Ms & D2 & x ~ sch_empty T).
Proof.
  introv He Hl Hn Hk.
  apply environment_push; autorewrite with rew_env_dom; auto.
Qed.

Lemma environment_add_subst_typ_bind_empty2 :
    forall D1 D2 xs Ms x T1 y T2,
    environment (D1 & xs ~* Ms & D2) ->
    length xs = length Ms ->
    x \notin (dom D1 \u from_list xs \u dom D2) ->
    y \notin (dom D1 \u from_list xs \u dom D2 \u \{x}) ->
    type T1 ->
    type T2 ->
    environment (D1 & xs ~* Ms & D2
                 & x ~ sch_empty T1 & y ~ sch_empty T2).
Proof.
  introv He Hl Hn1 Hn2 Hk1 Hk2.
  apply environment_push; autorewrite with rew_env_dom; auto.
  apply environment_push; autorewrite with rew_env_dom; auto.
Qed.

(* ****************************************************** *)
(** ** Term substitution *)

Lemma value_trm_subst : forall xs ss t,
    value t ->
    terms ss ->
    value (trm_subst xs ss t).
Proof.
  introv Hv Ht.
  induction Hv; simpl; auto.
  - apply value_abs.
    replace (trm_abs (trm_subst xs ss t))
      with (trm_subst xs ss (trm_abs t))
      by auto.
    auto using trm_subst_term.
  - apply value_fix.
    replace (trm_fix (trm_subst xs ss t))
      with (trm_subst xs ss (trm_fix t))
      by auto.
    auto using trm_subst_term.
Qed.

Lemma typing_trm_subst_var : forall E D1 D2 P xs Ms ts x M,
    binds x M (D1 & xs ~* Ms & D2) ->
    length xs = length Ms ->
    environment (D1 & xs ~* Ms & D2) ->
    typing_schemes E (D1 & D2) P ts Ms ->
    typing_scheme E (D1 & D2) P (trm_var_subst xs ts x) M
    \/ (binds x M (D1 & D2)
        /\ trm_var_subst xs ts x = trm_fvar x).
Proof.
  introv Hb Hl He Hss.
  assert (length ts = length Ms) as Hl2
    by eauto using typing_schemes_length.
  generalize dependent Ms.
  generalize dependent ts.
  induction xs; introv Hb Hl1 He Hss Hl2; destruct Ms; destruct ts;
    try discriminate; simpl in *;
    autorewrite with rew_env_concat in *; auto.
  inversion Hss; subst.
  case_var.
  - apply binds_middle_eq_inv in Hb; subst;
      auto using ok_from_environment.
  - eauto using binds_subst, environment_remove.
Qed.

Lemma typing_trm_subst : forall E D1 D2 P xs Ms ts t T,
    typing E (D1 & xs ~* Ms & D2) P t T ->
    length xs = length Ms ->
    type_environment E ->
    environment (D1 & xs ~* Ms & D2) ->
    typing_schemes E (D1 & D2) P ts Ms ->
    typing E (D1 & D2) P (trm_subst xs ts t) T.
Proof.
  introv Ht Hl He1 He2 Hss.
  remember (D1 & xs ~* Ms & D2) as D12.
  generalize dependent D2.
  induction Ht; introv Heq Hss; subst; simpl; eauto.
  - destruct typing_trm_subst_var
      with (E := E) (D1 := D1) (D2 := D2) (P := P) (xs := xs) (Ms := Ms)
           (ts := ts) (x := x) (M := M) as [Hs | [Hb Heq]]; auto.
    + apply typing_equal with (T1 := instance M Us);
        eauto using type_equal_symmetric, environment_remove,
          typing_instance.
    + rewrite Heq.
      apply typing_var with (M := M) (Us := Us); auto.
  - apply typing_abs with (L := L \u from_list xs \u dom D1 \u dom D2);
      auto.
    intros x Hf.
    rewrite trm_subst_open_var; auto with wellformed.
    rewrite <- concat_assoc.
    eauto using concat_assoc, typing_schemes_add_subst_typ_bind_empty,
      environment_remove, environment_add_subst_typ_bind_empty
        with wellformed.
  - apply typing_let_val
      with (L := L \u from_list xs \u dom E \u dom D1 \u dom D2)
        (M := M); auto using value_trm_subst with wellformed.
    + introv Hf.
      auto using type_environment_push_ranges,
        typing_schemes_add_subst_kinds_bind with wellformed.
    + introv Hn.
      rewrite trm_subst_open_var; auto with wellformed.
      rewrite <- concat_assoc.
      eauto using concat_assoc, typing_schemes_add_subst_typ_bind,
        environment_remove, environment_add_subst_typ_bind
          with wellformed.
  - assert (kinding E T1 knd_type) by eauto using output_typing.
    apply typing_let
      with (L := L \u from_list xs \u dom D1 \u dom D2) (T1 := T1);
      auto.
    introv Hn.
    rewrite trm_subst_open_var; auto with wellformed.
    rewrite <- concat_assoc.
    eauto using concat_assoc, typing_schemes_add_subst_typ_bind_empty,
      environment_remove, environment_add_subst_typ_bind_empty
        with wellformed.
  - apply typing_match
      with (L := L \u from_list xs \u dom D1 \u dom D2)
           (T1 := T1) (T2 := T2) (T3 := T3)
           (T4 := T4) (T5 := T5) (T6 := T6) (T7 := T7); auto.
    + introv Hn.
      rewrite trm_subst_open_var; auto with wellformed.
      rewrite <- concat_assoc.
      assert (type (typ_variant T3)) by auto with wellformed.
      eauto using concat_assoc, typing_schemes_add_subst_typ_bind_empty,
        environment_remove, environment_add_subst_typ_bind_empty
          with wellformed.
    + introv Hn.
      rewrite trm_subst_open_var; auto with wellformed.
      rewrite <- concat_assoc.
      assert (type (typ_variant T5)) by auto with wellformed.
      eauto using concat_assoc, typing_schemes_add_subst_typ_bind_empty,
        environment_remove, environment_add_subst_typ_bind_empty
          with wellformed.
  - apply typing_destruct
      with (L := L \u from_list xs \u dom D1 \u dom D2)
           (T1 := T1) (T2 := T2) (T3 := T3); auto.
    introv Hn.
    rewrite trm_subst_open_var; auto with wellformed.
    rewrite <- concat_assoc.
    assert (kinding E T3 knd_type) by auto with kinding.
    eauto using concat_assoc, typing_schemes_add_subst_typ_bind_empty,
      environment_remove, environment_add_subst_typ_bind_empty
        with wellformed.
  - apply typing_fix
      with (L := L \u from_list xs \u dom D1 \u dom D2); auto.
    introv Hn1 Hn2.
    rewrite trm_subst_open_vars; auto with wellformed.
    rewrite <- concat_assoc2.
    assert (type (typ_arrow T1 T2)) by auto with wellformed.
    eauto using concat_assoc2, typing_schemes_add_subst_typ_bind_empty2,
      environment_remove, environment_add_subst_typ_bind_empty2
        with wellformed.
Qed.

Lemma typing_trm_subst_l : forall E D xs Ms P ts t T,
    typing E (D & xs ~* Ms) P t T ->
    length xs = length Ms ->
    type_environment E ->
    environment (D & xs ~* Ms) ->
    typing_schemes E D P ts Ms ->
    typing E D P (trm_subst xs ts t) T.
Proof.
  introv Ht Hl He1 He2 Hts.
  rewrite <- concat_empty_r with (E := D).
  rewrite <- concat_empty_r with (E := D & xs ~* Ms) in Ht, He2.
  rewrite <- concat_empty_r with (E := D) in Hts.
  eauto using typing_trm_subst.
Qed.

Lemma typing_trm_subst_single : forall E D1 D2 x M P s t T,
    typing E (D1 & x ~ M & D2) P t T ->
    type_environment E ->
    environment (D1 & x ~ M & D2) ->
    typing_scheme E (D1 & D2) P s M ->
    typing E (D1 & D2) P (trm_subst_single x s t) T.
Proof.
  introv Ht He1 He2 Hs.
  apply typing_trm_subst with (Ms := cons M nil);
    simpl; autorewrite with rew_env_concat; auto.
Qed.

Lemma typing_trm_subst_single_l : forall E D x M P s t T,
    typing E (D & x ~ M) P t T ->
    type_environment E ->
    environment (D & x ~ M) ->
    typing_scheme E D P s M ->
    typing E D P (trm_subst_single x s t) T.
Proof.
  introv Ht He1 He2 Hts.
  rewrite <- concat_empty_r with (E := D).
  rewrite <- concat_empty_r with (E := D & x ~ M) in Ht, He2.
  rewrite <- concat_empty_r with (E := D) in Hts.
  eauto using typing_trm_subst_single.
Qed.

Lemma typing_trm_subst_empty : forall E D1 D2 x P s t T1 T2,
    typing E (D1 & x ~ sch_empty T2 & D2) P t T1 ->
    type_environment E ->
    environment (D1 & x ~ sch_empty T2 & D2) ->
    typing E (D1 & D2) P s T2 ->
    typing E (D1 & D2) P (trm_subst (x::nil) (s::nil) t) T1.
Proof.
  introv Ht1 He1 He2 Ht2.
  apply typing_trm_subst with (Ms := cons (sch_empty T2) nil);
    simpl; autorewrite with rew_env_concat; auto.
  apply typing_schemes_cons; auto.
  apply typing_scheme_empty; auto.
Qed.

Lemma typing_trm_subst_empty_l : forall E D x P s t T1 T2,
    typing E (D & x ~ sch_empty T2) P t T1 ->
    type_environment E ->
    environment (D & x ~ sch_empty T2) ->
    typing E D P s T2 ->
    typing E D P (trm_subst (x::nil) (s::nil) t) T1.
Proof.
  introv Ht He1 He2 Hts.
  rewrite <- concat_empty_r with (E := D).
  rewrite <- concat_empty_r with (E := D & x ~ sch_empty T2) in Ht, He2.
  rewrite <- concat_empty_r with (E := D) in Hts.
  eauto using typing_trm_subst_empty.
Qed.

Lemma typing_trm_subst_empty2 : forall E D1 D2 x y P s r t T1 T2 T3,
    typing E (D1 & x ~ sch_empty T2 & y ~ sch_empty T3 & D2) P t T1 ->
    type_environment E ->
    environment (D1 & x ~ sch_empty T2 & y ~ sch_empty T3 & D2) ->
    typing E (D1 & D2) P s T2 ->
    typing E (D1 & D2) P r T3 ->
    typing E (D1 & D2) P
      (trm_subst (cons y (x::nil)) (cons r (s::nil)) t) T1.
Proof.
  introv Ht1 He1 He2 Ht2 Ht3.
  apply typing_trm_subst
    with (Ms := cons (sch_empty T3) (cons (sch_empty T2) nil));
    simpl; autorewrite with rew_env_concat; auto.
  apply typing_schemes_cons.
  - apply typing_scheme_empty; auto.
  - apply typing_schemes_cons; auto.
    apply typing_scheme_empty; auto.
Qed.

Lemma typing_trm_subst_empty2_l : forall E D x y P s r t T1 T2 T3,
    typing E (D & x ~ sch_empty T2 & y ~ sch_empty T3) P t T1 ->
    type_environment E ->
    environment (D & x ~ sch_empty T2 & y ~ sch_empty T3) ->
    typing E D P s T2 ->
    typing E D P r T3 ->
    typing E D P (trm_subst (cons y (x::nil)) (cons r (s::nil)) t) T1.
Proof.
  introv Ht1 He1 He2 Ht2 Ht3.
  rewrite <- concat_empty_r with (E := D).
  rewrite <- concat_empty_r
    with (E := D & x ~ sch_empty T2 & y ~ sch_empty T3) in Ht1, He2.
  rewrite <- concat_empty_r with (E := D) in Ht2, Ht3.
  eapply typing_trm_subst_empty2; eauto.
Qed.

(* ****************************************************** *)
(** ** Extending the store *)

Lemma typing_extend_store_type : forall E D P P' t T,
    typing E D P t T ->
    type_environment E ->
    extends P P' ->
    valid_store_type E P' ->
    typing E D P' t T.
Proof.
  introv Ht He Hex Hs.
  induction Ht; eauto.
  - apply typing_let_val with (L := L \u dom E) (M := M); auto.
    auto using type_environment_push_ranges,
      valid_store_type_weakening_l with wellformed.
Qed.

Lemma typing_store_ref : forall E D V P l t T,
    typing_store E D V P ->
    type_environment E ->
    l # P ->
    valid_store_type E P ->
    typing E D P t T ->
    typing_store E D (V & l ~ t) (P & l ~ T).
Proof.
  introv Hs Hn Hv He Ht.
  assert (kinding E T knd_type)
    by eauto using output_typing.
  destruct Hs.
  apply typing_store_c.
  intro l'.
  case_if_eq l l'.
  - eauto using typing_store_loc_bound,
      typing_extend_store_type.   
  - assert (typing_store_loc l' E D V P) as Hsl
      by auto.
    destruct Hsl.
    + auto using typing_store_loc_fresh.
    + eapply typing_store_loc_bound;
        eauto using typing_extend_store_type.
Qed.

Lemma typing_store_set : forall E D V P l t T,
    typing_store E D V P ->
    type_environment E ->
    binds l T P ->
    valid_store_type E P ->
    typing E D P t T ->
    typing_store E D (V & l ~ t) P.
Proof.
  introv Hs Hb Hv He Ht.
  assert (kinding E T knd_type)
    by eauto using output_typing.
  destruct Hs.
  apply typing_store_c.
  intro l'.
  case_if_eq l l'.
  - eauto using typing_store_loc_bound,
      typing_extend_store_type.   
  - assert (typing_store_loc l' E D V P) as Hsl
      by auto.
    destruct Hsl.
    + auto using typing_store_loc_fresh.
    + eapply typing_store_loc_bound;
        eauto using typing_extend_store_type.
Qed.