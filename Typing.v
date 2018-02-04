(************************************************
 *           Row Subtyping - Typing             *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import LibLN Cofinite Definitions
        Substitution Wellformedness Kinding.

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
  generalize dependent E.
  generalize dependent G.
  generalize dependent F.
  induction Ht; introv Heq Hv; subst;
    eauto using valid_instance_weakening, binds_weakening,
                kinding_weakening, subtype_weakening
          with valid_env_regular.    
  - apply typing_abs with (L := L \u dom E0 \u dom F \u dom G);
      auto using kinding_weakening.
    intros x Hn.
    assert (valid_env (E0 & F & G & x ~: sch_empty T1))
      as He by auto using valid_env_type_weakening.
    rewrite <- concat_assoc.
    rewrite <- concat_assoc in He.
    auto using concat_assoc.
  - apply typing_let
      with (M := M) (L := L \u dom E0 \u dom F \u dom G).
    + intros Xs Hl.
      assert (valid_env (E0 & F & G & Xs ~::* M))
        as He by auto using valid_env_kinds_weakening.
      rewrite <- concat_assoc.
      rewrite <- concat_assoc in He.
      auto using concat_assoc.
    + intros x Hl.
      assert (valid_env (E0 & F & G & x ~: M))
        as He by auto using valid_env_type_weakening.
      rewrite <- concat_assoc.
      rewrite <- concat_assoc in He.
      auto using concat_assoc.
  - apply typing_match
      with (L := L \u dom E0 \u dom F \u dom G)
           (T1 := T1) (T2 := T2) (T3 := T3) (T4 := T4)
           (T5 := T5) (T6 := T6) (T7 := T7);
      auto using kinding_weakening, subtype_weakening.
    + intros x Hn.
      assert
        (valid_env (E0 & F & G & x ~: sch_empty (typ_variant T3)))
        as He by auto using valid_env_type_weakening.
      rewrite <- concat_assoc.
      rewrite <- concat_assoc in He.
      auto using concat_assoc.
    + intros y Hn.
      assert
        (valid_env (E0 & F & G & y ~: sch_empty (typ_variant T5)))
        as He by auto using valid_env_type_weakening.
      rewrite <- concat_assoc.
      rewrite <- concat_assoc in He.
      auto using concat_assoc.
  - apply typing_destruct
      with (L := L \u dom E0 \u dom F \u dom G)
           (T1 := T1) (T2 := T2) (T3 := T3);
      auto using kinding_weakening, subtype_weakening.
    intros x Hn.
    assert
      (valid_env (E0 & F & G & x ~: sch_empty T3))
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
  generalize dependent E.
  generalize dependent F.
  induction Ht; introv Heq Hk; subst; eauto.
  - apply typing_var
        with (M := sch_subst X S M)
             (Us := (List.map (typ_subst X S) Us));
      eauto using valid_env_typ_subst, valid_instance_typ_subst,
                  sch_subst_instance, binds_typ_typ_subst
            with kinding_regular.
  - apply typing_abs with (L := L \u \{X} \u dom E0 \u dom F).
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
      with (L := L \u \{X} \u dom E0 \u dom F) (M := sch_subst X S M).
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

Lemma typing_trm_subst : forall L E F x M s t T,
    typing (E & x ~: M & F) t T ->
    (forall Xs,
      fresh L (sch_arity M) Xs ->
      typing (E & Xs ~::* M) s (instance_vars M Xs)) ->
    typing (E & F) (trm_subst x s t) T.
Proof.
  introv Ht Hs.
  remember (E & x ~: M & F) as ExF.
  induction Ht; simpl.
  - case_var.
    + subst.
      assert (environment (E & x ~: M & F)) as He
        by auto with valid_env_regular.
      apply ok_from_environment in He.
      assert (bind_typ M0 = bind_typ M) as Heq
        by eauto using binds_middle_eq_inv.
      inversion Heq; subst.
      assert (valid_env (E & F))
        by eauto using valid_env_typ_bind.
      apply typing_instance with (L := L \u dom F);
        eauto using valid_instance_typ_bind.
      introv Hf.
      assert (typing (E & Xs ~::* M) s (instance_vars M Xs)) as Ht
        by auto.
      assert (valid_env (E & Xs ~::* M))
        by auto with typing_validated.
      apply typing_weakening;
        auto using valid_env_kinds_weakening_l.
    + subst.
      apply typing_var with (M := M0) (Us := Us);
        eauto using valid_env_typ_bind, valid_instance_typ_bind.
      apply binds_subst with (x2 := x) (v2 := bind_typ M); auto.
  - 