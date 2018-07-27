(************************************************
 *           Row Subtyping - Typing             *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import LibLN Cofinite Disjoint Definitions Substitution
        Wellformedness Kinding Subtyping.

Hint Constructors value typing typing_scheme typing_schemes.

Lemma typing_scheme_empty : forall E P t T,
    typing E P t T <-> typing_scheme E P t (sch_empty T).
Proof.
  split; introv Ht.
  - apply typing_scheme_c with (L := \{});
      try rewrite <- valid_scheme_empty;
      simpl; auto with typing_validated.
    introv Hf.
    fresh_length Hf as Hl.
    destruct Xs; try discriminate.
    unfold sch_empty, instance_vars, instance, bind_sch_kinds; simpl.
    rewrite typ_open_nil, concat_empty_r.
    auto.
  - remember (sch_empty T) as M.
    destruct Ht; subst.
    unfold sch_empty, instance_vars, instance, bind_sch_kinds in *;
      simpl in *.
    assert
      (typing (E & bind_knds nil nil) P t
         (typ_open T (typ_fvars nil))) by auto.
    simpl in *; rewrite typ_open_nil, concat_empty_r in *.
    auto.
Qed.

Lemma typing_weakening : forall E F G P t T,
    typing (E & G) P t T ->
    valid_env true (E & F & G) ->
    typing (E & F & G) P t T.
Proof.
  introv Ht Hv.
  apply validated_typing in Ht.
  remember (E & G) as EG.
  generalize dependent G.
  induction Ht; introv Heq Hv; subst;
    eauto 6 using valid_instance_weakening, binds_weakening,
                kinding_weakening, subtype_weakening,
                type_equal_weakening, valid_store_type_weakening
          with valid_env_regular.   
  - apply typing_abs with (L := L \u dom E \u dom F \u dom G);
      auto using kinding_weakening.
    intros x Hn.
    assert (valid_env true (E & F & G & x ~: sch_empty T1))
      as He by auto using valid_env_type_weakening.
    rewrite <- concat_assoc.
    rewrite <- concat_assoc in He.
    auto using concat_assoc.
  - apply typing_let_val
      with (M := M) (L := L \u dom E \u dom F \u dom G); auto.
    + intros Xs Hl.
      assert (valid_env true (E & F & G & Xs ~::* M))
        as He by auto using valid_env_kinds_weakening.
      rewrite <- concat_assoc.
      rewrite <- concat_assoc in He.
      auto using concat_assoc.
    + intros x Hl.
      assert (valid_env true (E & F & G & x ~: M))
        as He by auto using valid_env_type_weakening.
      rewrite <- concat_assoc.
      rewrite <- concat_assoc in He.
      auto using concat_assoc.
  - apply typing_let
      with (L := L \u dom E \u dom F \u dom G) (T1 := T1); auto.
    intros x Hn.
    assert (valid_env true (E & F & G & x ~: sch_empty T1))
      as He by auto using valid_env_type_weakening.
    rewrite <- concat_assoc.
    rewrite <- concat_assoc in He.
    auto using concat_assoc.
  - apply typing_match
      with (L := L \u dom E \u dom F \u dom G)
           (T1 := T1) (T2 := T2) (T3 := T3) (T4 := T4)
           (T5 := T5) (T6 := T6) (T7 := T7);
      auto using kinding_weakening, subtype_weakening.
    + intros x Hn.
      assert
        (valid_env true (E & F & G & x ~: sch_empty (typ_variant T3)))
        as He by auto using valid_env_type_weakening.
      rewrite <- concat_assoc.
      rewrite <- concat_assoc in He.
      auto using concat_assoc.
    + intros y Hn.
      assert
        (valid_env true (E & F & G & y ~: sch_empty (typ_variant T5)))
        as He by auto using valid_env_type_weakening.
      rewrite <- concat_assoc.
      rewrite <- concat_assoc in He.
      auto using concat_assoc.
  - apply typing_destruct
      with (L := L \u dom E \u dom F \u dom G)
           (T1 := T1) (T2 := T2) (T3 := T3);
      auto using kinding_weakening, subtype_weakening.
    intros x Hn.
    assert
      (valid_env true (E & F & G & x ~: sch_empty T3))
      as He by auto using valid_env_type_weakening.
    rewrite <- concat_assoc.
    rewrite <- concat_assoc in He.
    auto using concat_assoc.
  - apply typing_fix with (L := L \u dom E \u dom F \u dom G);
      auto using kinding_weakening.
    intros x y Hn1 Hn2.
    assert
      (valid_env true
         (E & G & x ~: sch_empty (typ_arrow T1 T2)
          & y ~: sch_empty T1)) as He1
      by auto.
    assert
      (valid_env true
         (E & G & x ~: sch_empty (typ_arrow T1 T2))) as He2
        by eauto using valid_env_remove_typ_bind_l.
    assert
      (valid_env true
         (E & F & G & x ~: sch_empty (typ_arrow T1 T2))) as He3
      by auto using valid_env_type_weakening.
    rewrite <- concat_assoc in He3.
    rewrite <- concat_assoc with (E := E) in He1.
    assert
      (valid_env true
         (E & F & (G & x ~: sch_empty (typ_arrow T1 T2))
          & y ~: sch_empty T1)) as He4
        by auto using valid_env_type_weakening.
    rewrite <- concat_assoc with (E := E & F) in He4.
    rewrite <- concat_assoc2 with (E := E & F).
    auto using concat_assoc2.
Qed.

Lemma typing_weakening_l : forall E F P t T,
    typing E P t T ->
    valid_env true (E & F) ->
    typing (E & F) P t T.
Proof.
  introv Ht Hv.
  rewrite <- concat_empty_r with (E := E & F).
  apply typing_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma typing_scheme_weakening : forall E F G P t M,
    typing_scheme (E & G) P t M ->
    valid_env true (E & F & G) ->
    typing_scheme (E & F & G) P t M.
Proof.
  introv Ht He.
  remember (E & G) as EG.
  destruct Ht; subst.
  apply typing_scheme_c with (L := L \u dom (E & F & G));
    eauto using valid_scheme_weakening, valid_store_type_weakening.
  intros Xs Hf.
  rewrite <- concat_assoc.
  apply typing_weakening;
    rewrite concat_assoc;
    eauto using valid_env_kinds, valid_scheme_weakening.
Qed.

Lemma typing_scheme_weakening_l : forall E F P t M,
    typing_scheme E P t M ->
    valid_env true (E & F) ->
    typing_scheme (E & F) P t M.
Proof.
  introv Ht Hv.
  rewrite <- concat_empty_r with (E := E & F).
  apply typing_scheme_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma typing_schemes_weakening : forall E F G P ts Ms,
    typing_schemes (E & G) P ts Ms ->
    valid_env true (E & F & G) ->
    typing_schemes (E & F & G) P ts Ms.
Proof.
  introv Ht He.
  remember (E & G) as EG.
  induction Ht; subst;
    auto using valid_store_type_weakening, typing_scheme_weakening.
Qed.

Lemma typing_schemes_weakening_l : forall E F P ts Ms,
    typing_schemes E P ts Ms ->
    valid_env true (E & F) ->
    typing_schemes (E & F) P ts Ms.
Proof.
  introv Ht Hv.
  rewrite <- concat_empty_r with (E := E & F).
  apply typing_schemes_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma typing_typ_subst : forall E F Xs Ks Vs P t T,
    typing (E & bind_knds Xs Ks & F) P t T ->
    kindings true (env_subst Xs Vs (E & F)) Vs
      (knd_subst_list Xs Vs Ks) ->
    typing (env_subst Xs Vs (E & F)) (styp_subst Xs Vs P) t
           (typ_subst Xs Vs T).
Proof.
  introv Ht Hks.
  apply validated_typing in Ht.
  remember (E & bind_knds Xs Ks & F) as EXF.
  generalize dependent F.
  induction Ht; introv Heq Hks; subst; eauto.
  - apply typing_var
        with (M := sch_subst Xs Vs M)
             (Us := typ_subst_list Xs Vs Us);
      eauto using valid_instance_typ_subst,
                  valid_store_type_typ_subst,
                  binds_typ_middle_bind_knds_inv,
                  env_subst_binds_typ
            with kindings_regular kindings_validated.
    replace knd_type with (knd_subst Xs Vs knd_type) by reflexivity.
    rewrite<- sch_subst_instance; auto with kindings_regular.
    apply type_equal_typ_subst with (Js := Ks); assumption.
  - apply_fresh typing_abs as x.
    + replace knd_type with (knd_subst Xs Vs knd_type) by reflexivity.
      eauto using kinding_typ_subst.
    + fold (typ_subst Xs Vs T1).
      replace (sch_empty (typ_subst Xs Vs T1))
        with (sch_subst Xs Vs (sch_empty T1)) by reflexivity.
      rewrite <- env_subst_typ.
      rewrite <- concat_assoc.    
      auto using concat_assoc, kindings_add_subst_typ_bind_empty.
  - apply typing_let_val
      with (L := L \u from_list Xs \u dom E \u dom F)
           (M := sch_subst Xs Vs M).
    + assumption.
    + introv Hf.
      autorewrite with rew_sch_arity in Hf.
      fresh_length Hf as Hl.
      rewrite <- env_subst_bind_sch_kinds;
        autorewrite with rew_env_dom; auto with kindings_regular.
      rewrite <- env_subst_concat.
      rewrite <- concat_assoc.
      unfold instance_vars.
      rewrite <- typ_subst_fresh_typ_fvars
        with (Xs := Xs) (Us := Vs); auto.
      rewrite <- sch_subst_instance; auto with kindings_regular.
      eauto using concat_assoc, kindings_add_subst_kinds_bind.
    + introv Hn.
      rewrite <- env_subst_typ.
      rewrite <- concat_assoc.
      auto using concat_assoc, kindings_add_subst_typ_bind.
  - apply typing_let
      with (L := L \u from_list Xs \u dom E \u dom F)
             (T1 := typ_subst Xs Vs T1); auto.
    introv Hn.
    replace (sch_empty (typ_subst Xs Vs T1))
      with (sch_subst Xs Vs (sch_empty T1)) by reflexivity.
    rewrite <- env_subst_typ.
    rewrite <- concat_assoc.
    auto using concat_assoc, kindings_add_subst_typ_bind_empty.
  - apply typing_constructor
      with (T2 := typ_subst Xs Vs T2) (T3 := typ_subst Xs Vs T3);
      auto.
    + replace (knd_range (typ_top CSet.universe) (typ_subst Xs Vs T2))
        with (knd_subst Xs Vs (knd_range (typ_top CSet.universe) T2))
        by reflexivity.
      eauto using kinding_typ_subst.
    + replace
        (typ_proj CSet.universe (typ_subst Xs Vs T2)
           (CSet.singleton c))
        with (typ_subst Xs Vs
                (typ_proj CSet.universe T2 (CSet.singleton c)))
        by reflexivity.
      replace (typ_constructor c (typ_subst Xs Vs T3))
        with (typ_subst Xs Vs (typ_constructor c T3)) by reflexivity.
      eauto using subtype_typ_subst.
  - apply typing_match
      with (T1 := typ_subst Xs Vs T1) (T2 := typ_subst Xs Vs T2)
           (T3 := typ_subst Xs Vs T3) (T4 := typ_subst Xs Vs T4)
           (T5 := typ_subst Xs Vs T5) (T6 := typ_subst Xs Vs T6)
           (T7 := typ_subst Xs Vs T7)
           (L := L \u dom E \u dom F); auto.
    + replace (knd_range (typ_subst Xs Vs T2) (typ_bot CSet.universe))
        with (knd_subst Xs Vs (knd_range T2 (typ_bot CSet.universe)))
        by reflexivity.
      eauto using kinding_typ_subst.
    + replace (knd_range (typ_top CSet.universe) (typ_subst Xs Vs T4))
        with (knd_subst Xs Vs (knd_range (typ_top CSet.universe) T4))
        by reflexivity.
      eauto using kinding_typ_subst.
    + replace (knd_range (typ_top CSet.universe) (typ_subst Xs Vs T6))
        with (knd_subst Xs Vs (knd_range (typ_top CSet.universe) T6))
        by reflexivity.
      eauto using kinding_typ_subst.
    + replace
        (typ_proj CSet.universe (typ_subst Xs Vs T2)
           (CSet.singleton c))
        with (typ_subst Xs Vs
                (typ_proj CSet.universe T2 (CSet.singleton c)))
        by reflexivity.
      replace (typ_constructor c (typ_subst Xs Vs T7))
        with (typ_subst Xs Vs (typ_constructor c T7)) by reflexivity.
      eauto using subtype_typ_subst.
    + replace
        (typ_proj CSet.universe (typ_subst Xs Vs T2)
           (CSet.singleton c))
        with (typ_subst Xs Vs
                (typ_proj CSet.universe T2 (CSet.singleton c)))
        by reflexivity.
      replace
        (typ_proj CSet.universe (typ_subst Xs Vs T4)
           (CSet.singleton c))
        with (typ_subst Xs Vs
                (typ_proj CSet.universe T4 (CSet.singleton c)))
        by reflexivity.
      eauto using subtype_typ_subst.
    + replace
        (typ_proj
           CSet.universe (typ_subst Xs Vs T2) (CSet.cosingleton c))
        with (typ_subst Xs Vs
                (typ_proj CSet.universe T2 (CSet.cosingleton c)))
        by reflexivity.
      replace
        (typ_proj
           CSet.universe (typ_subst Xs Vs T6) (CSet.cosingleton c))
        with (typ_subst Xs Vs
                (typ_proj CSet.universe T6 (CSet.cosingleton c)))
        by reflexivity.
      eauto using subtype_typ_subst.
    + replace (sch_empty (typ_variant (typ_subst Xs Vs T3)))
        with (sch_subst Xs Vs (sch_empty (typ_variant T3)))
        by reflexivity.
      introv Hn.
      rewrite <- env_subst_typ.
      rewrite <- concat_assoc.
      eauto using concat_assoc, kindings_add_subst_typ_bind_empty,
        kinding_range_top_bot.
    + replace (sch_empty (typ_variant (typ_subst Xs Vs T5)))
        with (sch_subst Xs Vs (sch_empty (typ_variant T5)))
        by reflexivity.
      introv Hn.
      rewrite <- env_subst_typ.
      rewrite <- concat_assoc.
      eauto using concat_assoc, kindings_add_subst_typ_bind_empty,
        kinding_range_top_bot.
  - apply typing_destruct
      with (T1 := typ_subst Xs Vs T1) (T2 := typ_subst Xs Vs T2)
           (T3 := typ_subst Xs Vs T3)
           (L := L \u dom E \u dom F); auto.
    + replace (knd_range (typ_subst Xs Vs T2) (typ_bot CSet.universe))
        with (knd_subst Xs Vs (knd_range T2 (typ_bot CSet.universe)))
        by reflexivity.
      eauto using kinding_typ_subst.
    + replace
        (typ_proj CSet.universe (typ_subst Xs Vs T2)
           (CSet.singleton c))
        with (typ_subst Xs Vs
                (typ_proj CSet.universe T2 (CSet.singleton c)))
        by reflexivity.
      replace (typ_constructor c (typ_subst Xs Vs T3))
        with (typ_subst Xs Vs (typ_constructor c T3)) by reflexivity.
      eauto using subtype_typ_subst.
    + replace
        (typ_proj
           CSet.universe (typ_subst Xs Vs T2) (CSet.cosingleton c))
        with (typ_subst Xs Vs
                (typ_proj CSet.universe T2 (CSet.cosingleton c)))
        by reflexivity.
      replace (typ_bot (CSet.cosingleton c))
        with (typ_subst Xs Vs (typ_bot (CSet.cosingleton c)))
        by reflexivity.
      eauto using subtype_typ_subst.
    + replace (sch_empty (typ_subst Xs Vs T3))
        with (sch_subst Xs Vs (sch_empty T3)) by reflexivity.
      introv Hn.
      rewrite <- env_subst_typ.
      rewrite <- concat_assoc.
      auto using concat_assoc, kindings_add_subst_typ_bind_empty.
  - apply typing_absurd with (T1 := typ_subst Xs Vs T1); auto.
    + replace (knd_range
                 (typ_bot CSet.universe) (typ_bot CSet.universe))
        with (knd_subst Xs Vs
                (knd_range (typ_bot CSet.universe)
                           (typ_bot CSet.universe)))
        by reflexivity.
      eauto using kinding_typ_subst.
    + replace knd_type with (knd_subst Xs Vs knd_type) by reflexivity.
      eauto using kinding_typ_subst.
  - apply_fresh typing_fix as x.
    introv Hn1 Hn2.
    fold (typ_subst Xs Vs (typ_arrow T1 T2)).
    replace (sch_empty (typ_subst Xs Vs (typ_arrow T1 T2)))
      with (sch_subst Xs Vs (sch_empty (typ_arrow T1 T2)))
      by reflexivity.
    fold (typ_subst Xs Vs T1).
    replace (sch_empty (typ_subst Xs Vs T1))
      with (sch_subst Xs Vs (sch_empty T1)) by reflexivity.
    rewrite <- env_subst_typ.
    rewrite <- env_subst_typ.
    rewrite <- concat_assoc2.
    auto using concat_assoc2, kindings_add_subst_typ_bind_empty2.
  - apply typing_unit;
      eauto using valid_store_type_typ_subst with kindings_validated.
  - apply typing_prod; auto.
  - apply typing_loc with (T1 := typ_subst Xs Vs T1);
      eauto
        using valid_store_type_typ_subst, styp_subst_binds
        with kindings_validated.
    fold (knd_subst Xs Vs knd_type).
    eauto using type_equal_typ_subst.
  - apply typing_ref; auto.
Qed.

Lemma typing_typ_subst_l : forall E Xs Ks Us P t T,
    typing (E & bind_knds Xs Ks) P t T ->
    kindings true (env_subst Xs Us E) Us
      (knd_subst_list Xs Us Ks) ->
    typing (env_subst Xs Us E) (styp_subst Xs Us P) t
           (typ_subst Xs Us T).
Proof.
  introv Ht Hks.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r with (E := E & bind_knds Xs Ks) in Ht.
  rewrite <- concat_empty_r with (E := E) in Hks.
  eauto using typing_typ_subst.
Qed.

Lemma typing_scheme_typ_subst : forall E F Xs Ks Vs P t M,
    typing_scheme (E & bind_knds Xs Ks & F) P t M ->
    kindings true (env_subst Xs Vs (E & F)) Vs
      (knd_subst_list Xs Vs Ks) ->
    typing_scheme (env_subst Xs Vs (E & F)) (styp_subst Xs Vs P) t
           (sch_subst Xs Vs M).
Proof.
  introv Ht Hk.
  remember (E & bind_knds Xs Ks & F) as EXF.
  destruct Ht; subst.
  apply typing_scheme_c
    with (L := L \u dom E \u dom F \u from_list Xs);
    eauto using valid_scheme_typ_subst, valid_store_type_typ_subst.
  intros Ys Hf.
  rewrite sch_subst_arity in Hf.
  rewrite <- env_subst_bind_sch_kinds; auto with kindings_regular.
  rewrite <- env_subst_concat.
  rewrite <- concat_assoc.
  unfold instance_vars, instance in *.
  rewrite <- sch_subst_body; auto with kindings_regular.
  fold (typ_open_vars (typ_subst Xs Vs (sch_body M)) Ys).
  rewrite typ_subst_open_vars; auto with kindings_regular.
  apply typing_typ_subst with (Ks := Ks);
    auto using kindings_add_subst_kinds_bind;
    rewrite concat_assoc; eauto.
Qed.

Lemma typing_scheme_typ_subst_l : forall E Xs Ks Us P t M,
    typing_scheme (E & bind_knds Xs Ks) P t M ->
    kindings true (env_subst Xs Us E) Us
      (knd_subst_list Xs Us Ks) ->
    typing_scheme (env_subst Xs Us E) (styp_subst Xs Us P) t
           (sch_subst Xs Us M).
Proof.
  introv Ht Hks.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r with (E := E & bind_knds Xs Ks) in Ht.
  rewrite <- concat_empty_r with (E := E) in Hks.
  eauto using typing_scheme_typ_subst.
Qed.

Lemma typing_schemes_typ_subst : forall E F Xs Ks Vs P ts Ms,
    typing_schemes (E & bind_knds Xs Ks & F) P ts Ms ->
    kindings true (env_subst Xs Vs (E & F)) Vs
      (knd_subst_list Xs Vs Ks) ->
    typing_schemes (env_subst Xs Vs (E & F)) (styp_subst Xs Vs P) ts
           (sch_subst_list Xs Vs Ms).
Proof.
  introv Hts Hk.
  remember (E & bind_knds Xs Ks & F) as EXF.
  induction Hts; subst;
    eauto using typing_schemes_cons, valid_store_type_typ_subst,
      typing_scheme_typ_subst with kindings_validated.
Qed.

Lemma typing_schemes_typ_subst_l : forall E Xs Ks Us P ts Ms,
    typing_schemes (E & bind_knds Xs Ks) P ts Ms ->
    kindings true (env_subst Xs Us E) Us
      (knd_subst_list Xs Us Ks) ->
    typing_schemes (env_subst Xs Us E) (styp_subst Xs Us P) ts
           (sch_subst_list Xs Us Ms).
Proof.
  introv Hts Hks.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r with (E := E & bind_knds Xs Ks) in Hts.
  rewrite <- concat_empty_r with (E := E) in Hks.
  eauto using typing_schemes_typ_subst.
Qed.

Lemma typing_instance : forall E M P t Us,
  typing_scheme E P t M ->
  valid_instance E Us M ->
  typing E P t (instance M Us). 
Proof.
  introv Hs Hv.
  destruct Hs.
  pick_freshes (sch_arity M) Xs.
  fresh_length Fr as Hl.
  apply validated_valid_instance in Hv.
  inversion Hv; subst; simpl in *.
  assert (length Us = sch_arity M)
    by (erewrite kindings_length,
          <- length_knd_open_list, sch_arity_length; eauto).
  rewrite typ_subst_intro_instance with (Xs := Xs); auto.
  unfold bind_sch_kinds, instance_vars, instance in *.
  destruct M; simpl in *.
  rewrite <- styp_subst_fresh with (Xs := Xs) (Us := Us) (P := P);
    auto.
  rewrite <- env_subst_fresh with (Xs := Xs) (Us := Us) (E := E);
    auto.
  apply typing_typ_subst_l
    with (Ks := knd_open_vars_list sch_kinds Xs); auto.
  rewrite env_subst_fresh with (Xs := Xs) (Us := Us) (E := E); auto.
  rewrite <- knd_subst_list_intro; auto.
Qed.

(* Respects type equality *)

Lemma typing_equal_binding : forall E F T1 T2 x P t T,
    type_equal true E T1 T2 knd_type ->
    typing (E & x ~: sch_empty T1 & F) P t T ->
    typing (E & x ~: sch_empty T2 & F) P t T.
Proof.
  introv He Ht.
  assert (valid_scheme true E (sch_empty T2))
    by auto using valid_scheme_empty_of_kinding
         with type_equal_validated.
  apply validated_typing in Ht.
  remember (E & x ~: sch_empty T1 & F) as ExF.
  generalize dependent F.
  induction Ht; intros; subst;
    eauto using kinding_swap_typ_bind, subtype_swap_typ_bind,
      valid_store_type_swap_typ_bind, valid_env_swap_typ_bind,
      type_equal_swap_typ_bind.
  - assert (valid_env true (E & x ~: sch_empty T2 & F))
      by eauto using valid_env_swap_typ_bind with typing_validated.
    case_if_eq x x0.
    + { assert (bind_typ M = bind_typ (sch_empty T1)) as Heq
          by eauto using binds_middle_eq_inv, ok_from_environment.
        assert
          (valid_instance (E & x0 ~: sch_empty T1 & F) Us M) as Hi
          by assumption.
        inversion Heq; subst; inversion Hi; subst; simpl in *.
        apply typing_var with (M := sch_empty T2) (Us := nil); auto.
        - eauto using valid_store_type_swap_typ_bind.
        - eauto using binds_middle_eq, ok_middle_inv_r,
                      ok_from_environment, valid_instance_weakening,
                      valid_instance_remove_typ_bind.
        - apply valid_instance_c; auto; simpl.
          rewrite <- concat_assoc.
          apply kinding_weakening_l;
            try rewrite typ_open_nil;
            auto with type_equal_validated.
          rewrite concat_assoc.
          eauto using valid_env_swap_typ_bind.
        - assert (length Us = 0) as Hl
           by (erewrite kindings_length; eauto; simpl; auto).
          rewrite List.length_zero_iff_nil in Hl; subst.
          rewrite instance_empty_nil in *.
          apply type_equal_transitive with (T2 := T1);
            eauto using type_equal_swap_typ_bind.
          rewrite <- concat_assoc.
          apply type_equal_weakening_l; auto.
          rewrite concat_assoc.
          eauto using valid_env_swap_typ_bind. }
    + apply typing_var with (M := M) (Us := Us);
        eauto
          using valid_instance_weakening,
                valid_instance_remove_typ_bind,
                type_equal_weakening, type_equal_remove_typ_bind,
                binds_weakening, binds_subst,
                valid_store_type_swap_typ_bind
          with valid_env_regular.
  - econstructor;
      eauto using kinding_swap_typ_bind.
    introv Hn.
    rewrite<- concat_assoc.
    eauto using concat_assoc.
  - econstructor; try assumption.
    + introv Hf.
      rewrite<- concat_assoc.
      eauto using concat_assoc.
    + introv Hn.
      rewrite<- concat_assoc.
      eauto using concat_assoc.
  - eapply typing_let; eauto.
    introv Hn.
    rewrite<- concat_assoc.
    eauto using concat_assoc.
  - apply typing_match
      with (L := L) (T1 := T0) (T2 := T3) (T3 := T4)
           (T4 := T5) (T5 := T6) (T6 := T7) (T7 := T8);
      eauto using kinding_swap_typ_bind, subtype_swap_typ_bind.
    + introv Hn.
      rewrite<- concat_assoc.
      eauto using concat_assoc.
    + introv Hn.
      rewrite<- concat_assoc.
      eauto using concat_assoc.
  - econstructor;
      eauto using kinding_swap_typ_bind, subtype_swap_typ_bind.
    introv Hn.
    rewrite<- concat_assoc.
    eauto using concat_assoc.
  - apply typing_fix with (L := L).
    intros y z Hn1 Hn2.
    rewrite<- concat_assoc2.
    auto using concat_assoc2.
Qed.

Lemma typing_equal_binding_l : forall E T1 T2 x P t T,
    type_equal true E T1 T2 knd_type ->
    typing (E & x ~: sch_empty T1) P t T ->
    typing (E & x ~: sch_empty T2) P t T.
Proof.
  introv Hte Ht.
  rewrite<- concat_empty_r with (E := E & x ~: sch_empty T2).
  rewrite<- concat_empty_r with (E := E & x ~: sch_empty T1) in Ht.
  eauto using typing_equal_binding.
Qed.

Lemma typing_equal_binding_l2 : forall E T1 T1' T2 T2' x y P t T,
    type_equal true E T1 T1' knd_type ->
    type_equal true E T2 T2' knd_type ->
    typing (E & x ~: sch_empty T1 & y ~: sch_empty T2) P t T ->
    typing (E & x ~: sch_empty T1' & y ~: sch_empty T2') P t T.
Proof.
  introv Hte1 Hte2 Ht.
  assert (environment (E & x ~: sch_empty T1 & y ~: sch_empty T2))
    as He by auto with typing_regular.
  apply environment_middle_inv_fresh in He.
  eauto using environment_middle_inv_fresh, typing_equal_binding,
      typing_equal_binding_l, type_equal_add_typ_bind_l,
        valid_scheme_empty_of_kinding
          with type_equal_validated.
Qed.

Lemma typing_equal_cong : forall E P t T1 T2,
    type_equal_cong true E T1 T2 knd_type ->
    typing E P t T1 -> typing E P t T2.
Proof.
  introv He Ht.
  apply validated_typing in Ht.
  generalize dependent T2.
  induction Ht; introv He.
  - apply typing_var with (M := M) (Us := Us); auto.
    apply type_equal_transitive with (T2 := T);
      eauto using type_equal_cong_symmetric.
  - inversion He; subst.
    + apply typing_abs with (L := L);
        auto with type_equal_cong_validated.
      introv Hn.
      apply typing_equal_binding_l with (T1 := T1);
        eauto with type_equal_cong_validated.
    + apply typing_abs with (L := L \u dom E);
        auto using type_equal_cong_weakening_l.
    + { assert
          (type_equal_symm true E (typ_arrow T1 T2) T0 knd_type)
          as Hes by assumption.
        inversion Hes.
        - assert
            (type_equal_core true E (typ_arrow T1 T2) T0 knd_type)
            as Hec by assumption.
          inversion Hec.
        - assert
            (type_equal_core true E T0 (typ_arrow T1 T2) knd_type)
            as Hec by assumption.
          inversion Hec. }
  - eauto.
  - apply typing_let_val with (L := L \u dom E) (M := M);
      auto using type_equal_cong_weakening_l.
  - apply typing_let with (L := L \u dom E) (T1 := T1);
      auto using type_equal_cong_weakening_l.
  - inversion He; subst.
    + { assert
          (type_equal_symm true E (typ_variant T1) T0 knd_type)
          as Hes by assumption.
        inversion Hes.
        - assert
            (type_equal_core true E (typ_variant T1) T0 knd_type)
            as Hec by assumption.
          inversion Hec.
        - assert
            (type_equal_core true E T0 (typ_variant T1) knd_type)
            as Hec by assumption.
          inversion Hec. }
  - apply typing_match
      with (L := L) (T1 := T1) (T2 := T2) (T3 := T3)
           (T4 := T4) (T5 := T5) (T6 := T6) (T7 := T7);
      auto using type_equal_cong_weakening_l.
  - apply typing_destruct
      with (L := L) (T1 := T1) (T2 := T2) (T3 := T3);
      auto using type_equal_cong_weakening_l.
  - eauto with type_equal_cong_validated.
  - inversion He; subst.
    + apply typing_fix with (L := L);
        auto with type_equal_cong_validated.
      introv Hn1 Hn2.
      assert
        (type_equal_cong true
          (E & x ~: sch_empty (typ_arrow T1 T2) & y ~: sch_empty T1)
          (typ_arrow T1 T2) (typ_arrow T1' T2) knd_type)
        by (rewrite <- concat_assoc;
            apply type_equal_cong_weakening_l; auto;
            rewrite concat_assoc; auto).
      apply typing_equal_binding_l2
        with (T1 := typ_arrow T1 T2) (T2 := T1);
        eauto with type_equal_cong_validated.
    + apply typing_fix with (L := L);
        auto with type_equal_cong_validated.
      introv Hn1 Hn2.
      assert
        (type_equal_cong true
          (E & x ~: sch_empty (typ_arrow T1 T2) & y ~: sch_empty T1)
          T2 T2' knd_type)
        by (rewrite <- concat_assoc;
            apply type_equal_cong_weakening_l; auto;
            rewrite concat_assoc; auto).
      apply typing_equal_binding_l2
        with (T1 := typ_arrow T1 T2) (T2 := T1);
        eauto with type_equal_cong_validated.
    + { assert
          (type_equal_symm true E (typ_arrow T1 T2) T0 knd_type)
          as Hes by assumption.
        inversion Hes.
        - assert
            (type_equal_core true E (typ_arrow T1 T2) T0 knd_type)
            as Hec by assumption.
          inversion Hec.
        - assert
            (type_equal_core true E T0 (typ_arrow T1 T2) knd_type)
            as Hec by assumption.
          inversion Hec. }
  - inversion He.
    assert (type_equal_symm true E typ_unit T2 knd_type) as He2
      by assumption.
    inversion He2.
    + assert (type_equal_core true E typ_unit T2 knd_type) as He3
        by assumption.
      inversion He3.
    + assert (type_equal_core true E T2 typ_unit knd_type) as He3
        by assumption.
      inversion He3.
  - inversion He; subst; auto.
    assert (type_equal_symm true E (typ_prod T1 T2) T0 knd_type)
      as He2 by assumption.
    inversion He2.
    + assert (type_equal_core true E (typ_prod T1 T2) T0 knd_type)
        as He3 by assumption.
      inversion He3.
    + assert (type_equal_core true  E T0 (typ_prod T1 T2) knd_type)
        as He3 by assumption.
      inversion He3.
  - eauto.
  - eauto.
  - inversion He; subst.
    + assert (type_equal true E T1 T1' knd_type)
        by eauto using type_equal_post_step.
      eauto.
    + { assert
          (type_equal_symm true E (typ_ref T2) T0 knd_type) as Hes
          by assumption.
        inversion Hes.
        - assert
            (type_equal_core true E (typ_ref T2) T0 knd_type) as Hec
            by assumption.
          inversion Hec.
        - assert
            (type_equal_core true E T0 (typ_ref T2) knd_type) as Hec
            by assumption.
          inversion Hec. }
  - inversion He; subst; auto.
    assert (type_equal_symm true E (typ_ref T) T2 knd_type) as He2
        by assumption.
    inversion He2.
    + assert (type_equal_core true E (typ_ref T) T2 knd_type) as He3
        by assumption.
      inversion He3.
    + assert (type_equal_core true E T2 (typ_ref T) knd_type) as He3
        by assumption.
      inversion He3.
  - auto.
  - inversion He.
    assert (type_equal_symm true E typ_unit T2 knd_type) as He2
        by assumption.
    inversion He2.
    + assert (type_equal_core true E typ_unit T2 knd_type) as He3
        by assumption.
      inversion He3.
    + assert (type_equal_core true E T2 typ_unit knd_type) as He3
        by assumption.
      inversion He3.
Qed.

Lemma typing_equal : forall E P t T1 T2,
    type_equal true E T1 T2 knd_type ->
    typing E P t T1 -> typing E P t T2.
Proof.
  introv Hte Ht.
  remember true as chk.
  remember knd_type as K.
  induction Hte; subst;
    eauto using typing_equal_cong.
Qed.

(* *************************************************************** *)
(** Somes lemmas about typing schemes useful for proving term
    subtitution on typings *)

Lemma typing_schemes_add_subst_typ_bind :
  forall E F P x M xs Ms ts,
    x \notin (dom E \u dom F) ->
    typing_schemes (E & F) P ts Ms ->
    valid_scheme true (E & bind_typs xs Ms & F) M ->
    typing_schemes (E & (F & x ~: M)) P ts Ms.
Proof.
  introv Hn Hks Hs.
  rewrite concat_assoc.
  apply typing_schemes_weakening_l; auto.
  apply valid_env_add_typ_bind_l;
    eauto using valid_scheme_remove_bind_typs
      with typing_schemes_validated.
Qed.

Lemma typing_schemes_add_subst_typ_bind_empty :
  forall E F P x T xs Ms ts,
    x \notin (dom E \u dom F) ->
    typing_schemes (E & F) P ts Ms ->
    kinding true (E & bind_typs xs Ms & F) T knd_type ->
    typing_schemes (E & (F & x ~: sch_empty T)) P ts Ms.
Proof.
  introv Hn Hss Hk.
  rewrite concat_assoc.
  eauto using typing_schemes_weakening_l,
    valid_env_add_typ_bind_l, kinding_remove_bind_typs,
      valid_scheme_empty_of_kinding
        with typing_schemes_validated.
Qed.

Lemma typing_schemes_add_subst_typ_bind_empty2 :
  forall E F P x T y U xs Ms ts,
    x \notin (dom E \u dom F) ->
    y \notin (dom E \u dom F \u \{x}) ->
    typing_schemes (E & F) P ts Ms ->
    kinding true (E & bind_typs xs Ms & F) T knd_type ->
    kinding true (E & bind_typs xs Ms & F) U knd_type ->
    typing_schemes
      (E & (F & x ~: sch_empty T & y ~: sch_empty U)) P ts Ms.
Proof.
  introv Hn1 Hn2 Hss Hk1 Hk2.
  rewrite concat_assoc.
  rewrite concat_assoc.
  rewrite <- concat_assoc.
  apply typing_schemes_weakening_l; auto.
  rewrite concat_assoc.
  apply valid_env_add_typ_bind_l;
    try rewrite <- valid_scheme_empty;
    eauto using kinding_remove_bind_typs
      with typing_schemes_validated.
  apply valid_env_add_typ_bind_l;
    try rewrite <- valid_scheme_empty;
    eauto using kinding_remove_bind_typs
      with typing_schemes_validated.
  apply kinding_add_typ_bind_l;
    try rewrite <- valid_scheme_empty;
    eauto using kinding_remove_bind_typs
      with typing_schemes_validated.
Qed.

Lemma typing_schemes_add_subst_kinds_bind :
  forall E F P Xs M xs Ms ts,
    fresh (dom E \u dom F) (sch_arity M) Xs ->
    typing_schemes (E & F) P ts Ms ->
    valid_scheme true (E & bind_typs xs Ms & F) M ->
    typing_schemes (E & (F & Xs ~::* M)) P ts Ms.
Proof.
  introv Hf Hss Hs.
  rewrite concat_assoc.
  apply typing_schemes_weakening_l; auto.
  apply valid_env_kinds;
    autorewrite with rew_env_dom;
    eauto using valid_scheme_remove_bind_typs
      with typing_schemes_validated.
Qed.

(* Term substitution *)

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

Lemma binds_var_trm_subst : forall E F P xs Ms ts x M,
    environment (E & bind_typs xs Ms & F) ->
    binds x (bind_typ M) (E & bind_typs xs Ms & F) ->
    typing_schemes (E & F) P ts Ms ->
    typing_scheme (E & F) P (trm_var_subst xs ts x) M
    \/ (binds x (bind_typ M) (E & F)
        /\ trm_var_subst xs ts x = trm_fvar x).
Proof.
  introv He Hb Hss.
  assert (length ts = length Ms) as Hl2
    by eauto using typing_schemes_length.
  generalize dependent Ms.
  generalize dependent ts.
  induction xs; introv He Hb Hss Hl; destruct Ms; destruct ts;
    try discriminate; simpl in *;
    autorewrite with rew_env_concat in *; auto.
  inversion Hss; subst.
  case_var.
  - rewrite <- concat_assoc in Hb, He.
    apply binds_middle_eq_inv in Hb; auto using ok_from_environment.
    inversion Hb; subst.
    auto.
  - rewrite <- concat_assoc in Hb, He.
    apply IHxs with (Ms := Ms) (ts := ts); auto.
    + rewrite <- concat_assoc.
      eauto using environment_remove.
    + rewrite <- concat_assoc.
      destruct (binds_middle_inv Hb) as [?|[[? [? ?]]|[? [? ?]]]];
        try contradiction; auto.
Qed.

Lemma typing_trm_subst : forall E F P xs Ms ts t T,
    typing (E & bind_typs xs Ms & F) P t T ->
    typing_schemes (E & F) P ts Ms ->
    typing (E & F) P (trm_subst xs ts t) T.
Proof.
  introv Ht Hss.
  remember (E & bind_typs xs Ms & F) as ExF.
  apply validated_typing in Ht.
  generalize dependent F.
  induction Ht; intros; subst; simpl;
    eauto using kinding_remove_bind_typs, subtype_remove_bind_typs,
      valid_env_remove_bind_typs, valid_store_type_remove_bind_typs,
      type_equal_remove_bind_typs.
  - destruct binds_var_trm_subst
      with (E := E) (F := F) (P := P) (xs := xs) (Ms := Ms)
           (ts := ts) (x := x) (M := M) as [Hs | [Hb Heq]]; auto.
    + apply typing_equal with (T1 := instance M Us);
        eauto using type_equal_symmetric, type_equal_remove_bind_typs.
      apply typing_instance;
        eauto using valid_instance_remove_bind_typs.
    + rewrite Heq.
      apply typing_equal with (T1 := instance M Us);
        eauto using type_equal_symmetric, type_equal_remove_bind_typs.
      apply typing_var with (M := M) (Us := Us);
        eauto using valid_env_remove_bind_typs,
          valid_store_type_remove_bind_typs,
            valid_instance_remove_bind_typs, kinding_remove_bind_typs           with type_equal_validated.
  - apply typing_abs with (L := L \u from_list xs \u dom E \u dom F);
      eauto using kinding_remove_bind_typs.
    intros x Hf.
    rewrite trm_subst_open_var; auto with typing_schemes_regular.
    rewrite <- concat_assoc.
    eauto using concat_assoc, typing_schemes_add_subst_typ_bind_empty.
  - apply typing_let_val
      with (L := L \u from_list xs \u dom E \u dom F) (M := M).
    + auto using value_trm_subst with typing_schemes_regular.
    + introv Hf.
      rewrite<- concat_assoc.
      eauto using concat_assoc,
        typing_schemes_add_subst_kinds_bind.
    + introv Hn.
      rewrite trm_subst_open_var; auto with typing_schemes_regular.
      rewrite<- concat_assoc.
      eauto using concat_assoc,
        typing_schemes_add_subst_typ_bind.
  - apply typing_let
      with (L := L \u from_list xs \u dom E \u dom F) (T1 := T1);
      auto.
    introv Hn.
    rewrite trm_subst_open_var; auto with typing_schemes_regular.
    rewrite<- concat_assoc.
    eauto using concat_assoc, typing_schemes_add_subst_typ_bind_empty.
  - apply typing_match
      with (L := L \u from_list xs \u dom E \u dom F)
           (T1 := T1) (T2 := T2) (T3 := T3)
           (T4 := T4) (T5 := T5) (T6 := T6) (T7 := T7);
      eauto using kinding_remove_bind_typs, subtype_remove_bind_typs.
    + introv Hn.
      rewrite trm_subst_open_var; auto with typing_schemes_regular.
      rewrite <- concat_assoc.
      eauto using concat_assoc, kinding_range_top_bot,
        typing_schemes_add_subst_typ_bind_empty.
    + introv Hn.
      rewrite trm_subst_open_var; auto with typing_schemes_regular.
      rewrite <- concat_assoc.
      eauto using concat_assoc, kinding_range_top_bot,
        typing_schemes_add_subst_typ_bind_empty.
  - apply typing_destruct
      with (L := L \u from_list xs \u dom E \u dom F)
           (T1 := T1) (T2 := T2) (T3 := T3);
      eauto using kinding_remove_bind_typs, subtype_remove_bind_typs.
    introv Hn.
    rewrite trm_subst_open_var; auto with typing_schemes_regular.
    rewrite <- concat_assoc.
    eauto using concat_assoc, typing_schemes_add_subst_typ_bind_empty.
  - apply typing_fix with (L := L \u from_list xs \u dom E \u dom F).
    introv Hn1 Hn2.
    rewrite trm_subst_open_vars; auto with typing_schemes_regular.
    rewrite <- concat_assoc2.
    eauto using concat_assoc2,
      typing_schemes_add_subst_typ_bind_empty2.
Qed.

Lemma typing_trm_subst_l : forall E xs Ms P ts t T,
    typing (E & bind_typs xs Ms) P t T ->
    typing_schemes E P ts Ms ->
    typing E P (trm_subst xs ts t) T.
Proof.
  introv Ht Hts.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r with (E := E & bind_typs xs Ms) in Ht.
  rewrite <- concat_empty_r with (E := E) in Hts.
  eauto using typing_trm_subst.
Qed.

Lemma typing_trm_subst_single : forall E F x M P s t T,
    typing (E & x ~: M & F) P t T ->
    typing_scheme (E & F) P s M ->
    typing (E & F) P (trm_subst_single x s t) T.
Proof.
  introv Ht Hs.
  apply typing_trm_subst with (Ms := cons M nil);
    simpl; autorewrite with rew_env_concat;
      auto with typing_scheme_validated.
Qed.

Lemma typing_trm_subst_single_l : forall E x M P s t T,
    typing (E & x ~: M) P t T ->
    typing_scheme E P s M ->
    typing E P (trm_subst_single x s t) T.
Proof.
  introv Ht Hts.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r with (E := E & x ~: M) in Ht.
  rewrite <- concat_empty_r with (E := E) in Hts.
  eauto using typing_trm_subst_single.
Qed.

Lemma typing_trm_subst_empty : forall E F x P s t T1 T2,
    typing (E & x ~: sch_empty T2 & F) P t T1 ->
    typing (E & F) P s T2 ->
    typing (E & F) P (trm_subst (x::nil) (s::nil) t) T1.
Proof.
  introv Ht1 Ht2.
  apply typing_trm_subst with (Ms := cons (sch_empty T2) nil);
    simpl; autorewrite with rew_env_concat; auto.
  apply typing_schemes_cons; auto with typing_validated.
  apply typing_scheme_empty; auto.
Qed.

Lemma typing_trm_subst_empty_l : forall E x P s t T1 T2,
    typing (E & x ~: sch_empty T2) P t T1 ->
    typing E P s T2 ->
    typing E P (trm_subst (x::nil) (s::nil) t) T1.
Proof.
  introv Ht Hts.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r with (E := E & x ~: sch_empty T2) in Ht.
  rewrite <- concat_empty_r with (E := E) in Hts.
  eauto using typing_trm_subst_empty.
Qed.

Lemma typing_trm_subst_empty2 : forall E F x y P s r t T1 T2 T3,
    typing (E & x ~: sch_empty T2 & y ~: sch_empty T3 & F) P t T1 ->
    typing (E & F) P s T2 ->
    typing (E & F) P r T3 ->
    typing (E & F) P
      (trm_subst (cons x (y::nil)) (cons s (r::nil)) t) T1.
Proof.
  introv Ht1 Ht2 Ht3.
  apply typing_trm_subst
    with (Ms := cons (sch_empty T2) (cons (sch_empty T3) nil));
    simpl; autorewrite with rew_env_concat; auto.
  apply typing_schemes_cons.
  - apply typing_scheme_empty; auto.
  - apply typing_schemes_cons; auto with typing_validated.
    apply typing_scheme_empty; auto.
Qed.

Lemma typing_trm_subst_empty2_l : forall E x y P s r t T1 T2 T3,
    typing (E & x ~: sch_empty T2 & y ~: sch_empty T3) P t T1 ->
    typing E P s T2 ->
    typing E P r T3 ->
    typing E P (trm_subst (cons x (y::nil)) (cons s (r::nil)) t) T1.
Proof.
  introv Ht1 Ht2 Ht3.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r
    with (E := E & x ~: sch_empty T2 & y ~: sch_empty T3) in Ht1.
  rewrite <- concat_empty_r with (E := E) in Ht2.
  rewrite <- concat_empty_r with (E := E) in Ht3.
  eauto using typing_trm_subst_empty2.
Qed.

Lemma typing_extend_store_type : forall E P P' t T,
    typing E P t T ->
    extends P P' ->
    valid_store_type E P' ->
    typing E P' t T.
Proof.
  introv Ht He Hs.
  apply validated_typing in Ht.
  induction Ht; eauto.
  - apply typing_abs with (L := L \u dom E); auto.
    auto using valid_store_type_add_typ_bind_l,
      valid_scheme_empty_of_kinding.
  - apply typing_let_val with (L := L \u dom E) (M := M); auto.
    + auto using valid_store_type_weakening_l.
    + auto using valid_store_type_add_typ_bind_l.
  - apply typing_let with (L := L \u dom E) (T1 := T1); auto.
    auto using valid_store_type_add_typ_bind_l,
      valid_scheme_empty_of_kinding.
  - apply typing_match with (L := L \u dom E) (T1 := T1) (T2 := T2)
      (T3 := T3) (T4 := T4) (T5 := T5) (T6 := T6) (T7 := T7); auto.
    + assert (valid_scheme true E (sch_empty (typ_variant T3)))
        by eauto using valid_scheme_empty_of_kinding,
            kinding_range_top_bot.
      eauto using valid_store_type_add_typ_bind_l.
    + assert (valid_scheme true E (sch_empty (typ_variant T5)))
        by eauto using valid_scheme_empty_of_kinding,
           kinding_range_top_bot.
      eauto using valid_store_type_add_typ_bind_l.
  - apply typing_destruct
      with (L := L \u dom E) (T1 := T1) (T2 := T2) (T3 := T3); auto.
    auto using valid_store_type_add_typ_bind_l,
      valid_scheme_empty_of_kinding.
  - apply typing_fix with (L := L \u dom E).
    intros x y Hn1 Hn2.
    assert (valid_scheme true E (sch_empty (typ_arrow T1 T2)))
      by auto using valid_scheme_empty_of_kinding.
    assert
      (valid_scheme true (E & x ~: sch_empty (typ_arrow T1 T2))
        (sch_empty T1))
      by auto using kinding_add_typ_bind_l,
           valid_scheme_empty_of_kinding.
    auto using valid_store_type_add_typ_bind_l.
Qed.