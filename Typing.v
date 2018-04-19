(************************************************
 *           Row Subtyping - Typing             *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import LibLN Cofinite Definitions Substitution
        Wellformedness Kinding Subtyping.

Hint Constructors typing.

Lemma valid_scheme_empty : forall E T,
    kinding E T knd_type ->
    valid_scheme E (sch_empty T).
Proof.
  introv Hk.
  apply valid_scheme_c with (L := \{}).
  introv Hf.
  fresh_length Hf as Hl.
  destruct Xs; try discriminate; auto.
Qed.

Lemma typing_weakening : forall E F G t T,
    typing (E & G) t T ->
    valid_env (E & F & G) ->
    typing (E & F & G) t T.
Proof.
  introv Ht Hv.
  apply validated_typing in Ht.
  remember (E & G) as EG.
  generalize dependent G.
  induction Ht; introv Heq Hv; subst;
    eauto using valid_instance_weakening, binds_weakening,
                kinding_weakening, subtype_weakening,
                type_equal_weakening
          with valid_env_regular.    
  - apply typing_abs with (L := L \u dom E \u dom F \u dom G);
      auto using kinding_weakening.
    intros x Hn.
    assert (valid_env (E & F & G & x ~: sch_empty T1))
      as He by auto using valid_env_type_weakening.
    rewrite <- concat_assoc.
    rewrite <- concat_assoc in He.
    auto using concat_assoc.
  - apply typing_let
      with (M := M) (L := L \u dom E \u dom F \u dom G).
    + intros Xs Hl.
      assert (valid_env (E & F & G & Xs ~::* M))
        as He by auto using valid_env_kinds_weakening.
      rewrite <- concat_assoc.
      rewrite <- concat_assoc in He.
      auto using concat_assoc.
    + intros x Hl.
      assert (valid_env (E & F & G & x ~: M))
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
        (valid_env (E & F & G & x ~: sch_empty (typ_variant T3)))
        as He by auto using valid_env_type_weakening.
      rewrite <- concat_assoc.
      rewrite <- concat_assoc in He.
      auto using concat_assoc.
    + intros y Hn.
      assert
        (valid_env (E & F & G & y ~: sch_empty (typ_variant T5)))
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
      (valid_env (E & F & G & x ~: sch_empty T3))
      as He by auto using valid_env_type_weakening.
    rewrite <- concat_assoc.
    rewrite <- concat_assoc in He.
    auto using concat_assoc.
Qed.

Lemma typing_weakening_l : forall E F t T,
    typing E t T ->
    valid_env (E & F) ->
    typing (E & F) t T.
Proof.
  introv Ht Hv.
  rewrite <- concat_empty_r with (E := E & F).
  apply typing_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma typing_typ_subst : forall E F X K S t T,
    typing (E & X ~:: K & F) t T ->
    kinding E S K ->
    typing (E & env_subst X S F) t (typ_subst X S T).
Proof.
  introv Ht Hk.
  remember (E & X ~:: K & F) as EXF.
  generalize dependent F.
  induction Ht; introv Heq; subst; eauto.
  - apply typing_var
        with (M := sch_subst X S M)
             (Us := (List.map (typ_subst X S) Us));
      eauto using valid_env_typ_subst, valid_instance_typ_subst,
                  sch_subst_instance, binds_typ_typ_subst
            with kinding_regular.
    replace knd_type with (knd_subst X S knd_type) by reflexivity.
    rewrite<- sch_subst_instance; auto with kinding_regular.
    apply type_equal_typ_subst with (J := K); assumption.
  - apply typing_abs with (L := L \u \{X} \u dom E \u dom F).
    + replace knd_type with (knd_subst X S knd_type) by reflexivity.
      eauto using kinding_typ_subst.
    + fold (typ_subst X S T1).
      replace (sch_empty (typ_subst X S T1))
        with (sch_subst X S (sch_empty T1)) by reflexivity.
      introv Hn.
      rewrite <- concat_assoc.
      rewrite <- env_subst_typ.
      auto using concat_assoc.
  - apply typing_let
      with (L := L \u \{X} \u dom E \u dom F) (M := sch_subst X S M).
    + introv Hf.
      autorewrite with rew_sch_arity in Hf.
      fresh_length Hf as Hl.
      rewrite <- env_subst_bind_knds;
        autorewrite with rew_env_dom; auto with kinding_regular.
      rewrite <- concat_assoc.
      rewrite <- env_subst_concat.
      unfold instance_vars.
      rewrite <- typ_subst_fresh_typ_fvars
        with (X := X) (U := S); auto.
      rewrite <- sch_subst_instance; auto with kinding_regular.
      eauto using concat_assoc.
    + introv Hn.
      rewrite <- concat_assoc.
      rewrite <- env_subst_typ.
      auto using concat_assoc.
  - apply typing_constructor
      with (T2 := typ_subst X S T2) (T3 := typ_subst X S T3); auto.
    + replace (knd_range (typ_top CSet.universe) (typ_subst X S T2))
        with (knd_subst X S (knd_range (typ_top CSet.universe) T2))
        by reflexivity.
      eauto using kinding_typ_subst.
    + replace
        (typ_proj CSet.universe (typ_subst X S T2) (CSet.singleton c))
        with (typ_subst X S
                (typ_proj CSet.universe T2 (CSet.singleton c)))
        by reflexivity.
      replace (typ_constructor c (typ_subst X S T3))
        with (typ_subst X S (typ_constructor c T3)) by reflexivity.
      eauto using subtype_typ_subst.
  - apply typing_match
      with (T1 := typ_subst X S T1) (T2 := typ_subst X S T2)
           (T3 := typ_subst X S T3) (T4 := typ_subst X S T4)
           (T5 := typ_subst X S T5) (T6 := typ_subst X S T6)
           (T7 := typ_subst X S T7) (L := L); auto.
    + replace (knd_range (typ_subst X S T2) (typ_bot CSet.universe))
        with (knd_subst X S (knd_range T2 (typ_bot CSet.universe)))
        by reflexivity.
      eauto using kinding_typ_subst.
    + replace (knd_range (typ_top CSet.universe) (typ_subst X S T4))
        with (knd_subst X S (knd_range (typ_top CSet.universe) T4))
        by reflexivity.
      eauto using kinding_typ_subst.
    + replace (knd_range (typ_top CSet.universe) (typ_subst X S T6))
        with (knd_subst X S (knd_range (typ_top CSet.universe) T6))
        by reflexivity.
      eauto using kinding_typ_subst.
    + replace
        (typ_proj CSet.universe (typ_subst X S T2) (CSet.singleton c))
        with (typ_subst X S
                (typ_proj CSet.universe T2 (CSet.singleton c)))
        by reflexivity.
      replace (typ_constructor c (typ_subst X S T7))
        with (typ_subst X S (typ_constructor c T7)) by reflexivity.
      eauto using subtype_typ_subst.
    + replace
        (typ_proj CSet.universe (typ_subst X S T2) (CSet.singleton c))
        with (typ_subst X S
                (typ_proj CSet.universe T2 (CSet.singleton c)))
        by reflexivity.
      replace
        (typ_proj CSet.universe (typ_subst X S T4) (CSet.singleton c))
        with (typ_subst X S
                (typ_proj CSet.universe T4 (CSet.singleton c)))
        by reflexivity.
      eauto using subtype_typ_subst.
    + replace
        (typ_proj
           CSet.universe (typ_subst X S T2) (CSet.cosingleton c))
        with (typ_subst X S
                (typ_proj CSet.universe T2 (CSet.cosingleton c)))
        by reflexivity.
      replace
        (typ_proj
           CSet.universe (typ_subst X S T6) (CSet.cosingleton c))
        with (typ_subst X S
                (typ_proj CSet.universe T6 (CSet.cosingleton c)))
        by reflexivity.
      eauto using subtype_typ_subst.
    + replace (sch_empty (typ_variant (typ_subst X S T3)))
        with (sch_subst X S (sch_empty (typ_variant T3)))
        by reflexivity.
      introv Hn.
      rewrite <- concat_assoc.
      rewrite <- env_subst_typ.
      auto using concat_assoc.
    + replace (sch_empty (typ_variant (typ_subst X S T5)))
        with (sch_subst X S (sch_empty (typ_variant T5)))
        by reflexivity.
      introv Hn.
      rewrite <- concat_assoc.
      rewrite <- env_subst_typ.
      auto using concat_assoc.
  - apply typing_destruct
      with (T1 := typ_subst X S T1) (T2 := typ_subst X S T2)
           (T3 := typ_subst X S T3) (L := L); auto.
    + replace (knd_range (typ_subst X S T2) (typ_bot CSet.universe))
        with (knd_subst X S (knd_range T2 (typ_bot CSet.universe)))
        by reflexivity.
      eauto using kinding_typ_subst.
    + replace
        (typ_proj CSet.universe (typ_subst X S T2) (CSet.singleton c))
        with (typ_subst X S
                (typ_proj CSet.universe T2 (CSet.singleton c)))
        by reflexivity.
      replace (typ_constructor c (typ_subst X S T3))
        with (typ_subst X S (typ_constructor c T3)) by reflexivity.
      eauto using subtype_typ_subst.
    + replace (sch_empty (typ_subst X S T3))
        with (sch_subst X S (sch_empty T3)) by reflexivity.
      introv Hn.
      rewrite <- concat_assoc.
      rewrite <- env_subst_typ.
      auto using concat_assoc.
  - apply typing_absurd with (T1 := typ_subst X S T1); auto.
    + replace (knd_range
                 (typ_bot CSet.universe) (typ_bot CSet.universe))
        with (knd_subst X S
                (knd_range (typ_bot CSet.universe)
                           (typ_bot CSet.universe)))
        by reflexivity.
      eauto using kinding_typ_subst.
    + replace knd_type with (knd_subst X S knd_type) by reflexivity.
      eauto using kinding_typ_subst.
Qed.

Lemma typing_typ_subst_l : forall E X K S t T,
    typing (E & X ~:: K) t T ->
    kinding E S K ->
    typing E t (typ_subst X S T).
Proof.
  introv Ht Hk.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r with (E := E & X ~:: K) in Ht.
  replace empty with (env_subst X S empty)
    by (unfold env_subst; apply map_empty).
  eauto using typing_typ_subst.
Qed.      

Lemma typing_typ_substs_l : forall E Xs M Us t T,
    fresh (dom E) (sch_arity M) Xs ->
    typing (E & Xs ~::* M) t T ->
    valid_instance E Us M ->
    typing E t (typ_substs Xs Us T).
Proof.
  introv Hf Ht Hv.
  generalize dependent Us.
  generalize dependent M.
  generalize dependent T.
  induction Xs; introv Hf Ht Hv.
  - simpl. simpl in Ht. rewrite concat_empty_r in Ht.
    auto using typing_weakening_l with valid_instance_validated.
  - assert (types (sch_arity M) Us) as Hts
      by auto with valid_instance_regular.
    destruct Hts as [Hl2 Hts].
    destruct Us; destruct M; try discriminate.
    simpl.
    fresh_length Hf as Hl1.
    inversion Hl2.
    inversion Hl1.
    inversion Hf.
    inversion Hv.
    inversion Hts.
    subst.
    apply IHXs with (M := sch_open M t0);
      autorewrite with rew_sch_arity; eauto.
    assert (valid_instance E Us (sch_open M t0))
      as Hv2 by assumption.
    apply valid_instance_closed with (X := a) in Hv2; auto.
    assert (a \notin sch_fv M) by eauto using sch_open_fv_inv.
    rewrite sch_subst_intro with (X := a) (U := t0); auto.
    rewrite <- env_subst_bind_knds;
      autorewrite with rew_sch_arity; auto.
    apply typing_typ_subst with (K := k); auto.
    rewrite <- concat_assoc.
    auto.
Qed.

Lemma typing_instance : forall L E M t Us,
  (forall Xs,
    fresh L (sch_arity M) Xs ->
    typing (E & Xs ~::* M) t (instance_vars M Xs)) ->
  valid_instance E Us M ->
  typing E t (instance M Us). 
Proof.
  introv Hs Hv.
  pick_freshes (sch_arity M) Xs.
  rewrite typ_substs_intro_instance with (Xs := Xs);
    auto with valid_instance_regular.
  apply typing_typ_substs_l with (M := M); auto.
Qed.

(* Respects type equality *)

Lemma typing_equal_binding : forall E F T1 T2 x t T,
    type_equal E T1 T2 knd_type ->
    typing (E & x ~: sch_empty T1 & F) t T ->
    typing (E & x ~: sch_empty T2 & F) t T.
Proof.
  introv He Ht.
  assert (valid_scheme E (sch_empty T2))
    by (rewrite valid_scheme_empty_type;
        auto with type_equal_validated).
  apply validated_typing in Ht.
  remember (E & x ~: sch_empty T1 & F) as ExF.
  generalize dependent F.
  induction Ht; intros; subst;
    eauto using kinding_swap_typ_bind, subtype_swap_typ_bind.
  - assert (valid_env (E & x ~: sch_empty T2 & F))
      by eauto using valid_env_swap_typ_bind with typing_validated.
    case_if_eq x x0.
    + { assert (bind_typ M = bind_typ (sch_empty T1)) as Heq
          by eauto using binds_middle_eq_inv, ok_from_environment.
        assert
          (valid_instance (E & x0 ~: sch_empty T1 & F) Us M) as Hi
          by assumption.
        inversion Heq; subst; inversion Hi; subst; simpl in *.
        apply typing_var with (M := sch_empty T2) (Us := nil); auto.
        - eauto using binds_middle_eq, ok_middle_inv_r,
                      ok_from_environment, valid_instance_weakening,
                      valid_instance_remove_typ_bind.
        - eauto
            using kinding_weakening_l, valid_env_retract
            with type_equal_validated.
        - apply type_equal_transitive with (T2 := T1);
            eauto using type_equal_swap_typ_bind,
                        type_equal_weakening_l, valid_env_retract. }
    + apply typing_var with (M := M) (Us := Us);
        eauto
          using valid_instance_weakening,
                valid_instance_remove_typ_bind,
                type_equal_weakening, type_equal_remove_typ_bind,
                binds_weakening, binds_subst
          with valid_env_regular.
  - econstructor;
      eauto using kinding_swap_typ_bind.
    introv Hn.
    rewrite<- concat_assoc.
    eauto using concat_assoc.
  - econstructor.
    + introv Hf.
      rewrite<- concat_assoc.
      eauto using concat_assoc.
    + introv Hn.
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
Qed.

Lemma typing_equal_binding_l : forall E T1 T2 x t T,
    type_equal E T1 T2 knd_type ->
    typing (E & x ~: sch_empty T1) t T ->
    typing (E & x ~: sch_empty T2) t T.
Proof.
  introv Hte Ht.
  rewrite<- concat_empty_r with (E := E & x ~: sch_empty T2).
  rewrite<- concat_empty_r with (E := E & x ~: sch_empty T1) in Ht.
  eauto using typing_equal_binding.
Qed.

Lemma typing_equal_cong : forall E t T1 T2,
    type_equal_cong E T1 T2 knd_type ->
    typing E t T1 -> typing E t T2.
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
          (type_equal_symm E (typ_arrow T1 T2) T0 knd_type) as Hes
          by assumption.
        inversion Hes.
        - assert
            (type_equal_core E (typ_arrow T1 T2) T0 knd_type) as Hec
            by assumption.
          inversion Hec.
        - assert
            (type_equal_core E T0 (typ_arrow T1 T2) knd_type) as Hec
            by assumption.
          inversion Hec. }
  - eauto.
  - apply typing_let with (L := L \u dom E) (M := M);
      auto using type_equal_cong_weakening_l.
  - inversion He; subst.
    + apply typing_constructor with (T2 := T2) (T3 := T3); auto.
      eauto using kinding_type_equal_cong_range.
    + { assert
          (type_equal_symm E (typ_variant T1) T0 knd_type) as Hes
          by assumption.
        inversion Hes.
        - assert
            (type_equal_core E (typ_variant T1) T0 knd_type) as Hec
            by assumption.
          inversion Hec.
        - assert
            (type_equal_core E T0 (typ_variant T1) knd_type) as Hec
            by assumption.
          inversion Hec. }
  - apply typing_match
      with (L := L) (T1 := T1) (T2 := T2) (T3 := T3)
           (T4 := T4) (T5 := T5) (T6 := T6) (T7 := T7);
      auto using type_equal_cong_weakening_l.
  - apply typing_destruct
      with (L := L) (T1 := T1) (T2 := T2) (T3 := T3);
      auto using type_equal_cong_weakening_l.
  - eauto with type_equal_cong_validated.
Qed.

Lemma typing_equal : forall E t T1 T2,
    type_equal E T1 T2 knd_type ->
    typing E t T1 -> typing E t T2.
Proof.
  introv Hte Ht.
  remember knd_type as K.
  induction Hte; subst;
    eauto using typing_equal_cong.
Qed.

(* Term substitution *)

Lemma typing_trm_subst : forall L E F x M s t T,
    typing (E & x ~: M & F) t T ->
    (forall Xs,
      fresh L (sch_arity M) Xs ->
      typing (E & Xs ~::* M) s (instance_vars M Xs)) ->
    typing (E & F) (trm_subst x s t) T.
Proof.
  introv Ht Hs.
  assert (term s)
    by (pick_freshes_gen L (sch_arity M) Ys;
        specialize (Hs Ys Fr);
        auto with typing_regular).
  remember (E & x ~: M & F) as ExF.
  apply validated_typing in Ht.
  generalize dependent F.
  induction Ht; intros; subst; simpl;
    eauto using kinding_remove_typ_bind, subtype_remove_typ_bind.
  - case_var.
    + assert (bind_typ M0 = bind_typ M) as Heq
        by eauto using binds_middle_eq_inv, ok_from_environment.
      inversion Heq; subst.
      apply typing_equal with (T1 := instance M Us);
        eauto using type_equal_symmetric, type_equal_remove_typ_bind.
      apply typing_instance with (L := L \u dom F);
        eauto using valid_instance_remove_typ_bind, valid_env_remove_typ_bind.
      introv Hf.
      assert (typing (E & Xs ~::* M) s (instance_vars M Xs)) as Ht
        by auto.
      assert (valid_env (E & Xs ~::* M))
        by auto with typing_validated.
      apply typing_weakening;
        eauto using valid_env_kinds_weakening_l, valid_env_remove_typ_bind.
    + apply typing_var with (M := M0) (Us := Us);
        eauto using valid_env_remove_typ_bind,
          valid_instance_remove_typ_bind, type_equal_remove_typ_bind. 
      apply binds_subst with (x2 := x) (v2 := bind_typ M); auto.
  - apply typing_abs with (L := L0 \u \{x}).
    + eauto using kinding_remove_typ_bind.
    + introv Hn.
      rewrite trm_subst_open_var; auto.
      rewrite<- concat_assoc.
      auto using concat_assoc.
  - apply typing_let with (L := L0 \u \{x}) (M := M0).
    + introv Hf.
      rewrite<- concat_assoc.
      auto using concat_assoc.
    + introv Hn.
      rewrite trm_subst_open_var; auto.
      rewrite<- concat_assoc.
      auto using concat_assoc.
  - apply typing_match
      with (L := L0 \u \{x}) (T1 := T1) (T2 := T2) (T3 := T3)
           (T4 := T4) (T5 := T5) (T6 := T6) (T7 := T7);
      eauto using kinding_remove_typ_bind, subtype_remove_typ_bind.
    + introv Hn.
      rewrite trm_subst_open_var; auto.
      rewrite<- concat_assoc.
      auto using concat_assoc.
    + introv Hn.
      rewrite trm_subst_open_var; auto.
      rewrite<- concat_assoc.
      auto using concat_assoc.
  - apply typing_destruct
      with (L := L0 \u \{x}) (T1 := T1) (T2 := T2) (T3 := T3);
      eauto using kinding_remove_typ_bind, subtype_remove_typ_bind.
    introv Hn.
    rewrite trm_subst_open_var; auto.
    rewrite<- concat_assoc.
    auto using concat_assoc.
Qed.

Lemma typing_trm_subst_l : forall L E x M s t T,
    typing (E & x ~: M) t T ->
    (forall Xs,
      fresh L (sch_arity M) Xs ->
      typing (E & Xs ~::* M) s (instance_vars M Xs)) ->
    typing E (trm_subst x s t) T.
Proof.
  introv Ht Hts.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r with (E := E & x ~: M) in Ht.
  eauto using typing_trm_subst.
Qed.

Lemma typing_trm_subst_empty : forall E F x s t T1 T2,
    typing (E & x ~: sch_empty T2 & F) t T1 ->
    typing E s T2 ->
    typing (E & F) (trm_subst x s t) T1.
Proof.
  introv Ht1 Ht2.
  apply typing_trm_subst with (L := \{}) (M := sch_empty T2); auto.
  introv Hf.
  fresh_length Hf as Hl.
  destruct Xs; try discriminate; unfold instance_vars; simpl.
  rewrite concat_empty_r.
  assumption.
Qed.

Lemma typing_trm_subst_empty_l : forall E x s t T1 T2,
    typing (E & x ~: sch_empty T2) t T1 ->
    typing E s T2 ->
    typing E (trm_subst x s t) T1.
Proof.
  introv Ht Hts.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r with (E := E & x ~: sch_empty T2) in Ht.
  eauto using typing_trm_subst_empty.
Qed.
