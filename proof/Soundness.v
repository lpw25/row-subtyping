
(************************************************
 *          Row Subtyping - Soundness           *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import Coq.Arith.PeanoNat LibLN Utilities Cofinite
        Disjoint Definitions Opening FreeVars Environments
        Subst Wellformedness Weakening Substitution Kinding
        Subtyping Inversion Coercible Typing.

(* *************************************************************** *)
(** * Values do not reduce *)

Lemma values_do_not_reduce : forall t t' V V',
    value t ->
    ~ red t V t' V'.
Proof.
  introv Hv.
  unfold not.
  introv Hr.
  generalize dependent t'.
  generalize dependent V.
  generalize dependent V'.
  induction Hv; introv Hr;
    inversion Hr; subst; eauto.
Qed.

(* *************************************************************** *)
(** * Preservation *)

Lemma preservation : preservation.
Proof.
  unfold preservation.
  introv He Hd Hp Hst Ht Hs Hr.
  generalize dependent T.
  generalize dependent P.
  induction Hr; introv Hp Hs Ht.
  - exists P.
    splits; auto.
    invert_typing Ht He Hd Hp.
    + pick_fresh x.
      rewrite trm_subst_single_intro with (x := x);
        auto with wellformed.
      apply typing_trm_subst_single_l with (M := M);
        eauto using typing_coercible, typing_scheme_c'
          with wellformed.
    + assert (kinding E empty T1 knd_type)
        by eauto using output_typing with wellformed.
      pick_fresh x.
      rewrite trm_subst_single_intro with (x := x);
        auto with wellformed.
      apply typing_trm_subst_empty_l with (T2 := T1);
        eauto using typing_coercible with wellformed.
  - invert_typing Ht He Hd Hp.
    + assert (value t1) as Hvl by assumption.
      exfalso.
      apply (values_do_not_reduce Hvl Hr).
    + assert (typing v E D P t1 T1) as Ht2 by auto.
      destruct (IHHr Hst _ Hp Hs _ Ht2)
        as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
      exists P'.
      splits; auto.
      apply typing_let with (L := L \u dom D \u dom E) (T1 := T1);
        eauto using output_typing.
      introv Hn.
      apply typing_extend_store_type with (P := P);
        eauto using typing_coercible with wellformed.
  - invert_typing Ht He Hd Hp.
    assert (typing v E D P t1 (typ_arrow T1 T2)) as Ht2 by auto.
    destruct (IHHr Hst _ Hp Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
    eauto using typing_coercible, typing_extend_store_type
      with wellformed.
  - invert_typing Ht He Hd Hp.
    assert (typing v E D P t2 T1) as Ht2 by auto.
    destruct (IHHr Hst _ Hp Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
    eauto using typing_coercible, typing_extend_store_type
      with wellformed.
  - exists P.
    splits; auto.
    invert_typing Ht He Hd Hp.
    assert (typing v E D P (trm_abs t1) (typ_arrow T1 T2))
      as Ht2 by assumption.
    invert_typing Ht2 He Hd Hp.
    pick_fresh x.
    rewrite trm_subst_single_intro with (x := x);
      auto with wellformed.
    assert (coercible v E T3 T2)
      by eauto using invert_coercible_arrow_right.
    assert (coercible v E T1 T0)
      by eauto using invert_coercible_arrow_left.
    apply typing_trm_subst_empty_l with (T2 := T0);
      eauto using typing_coercible with wellformed.
  - exists P.
    splits; auto.
    invert_typing Ht He Hd Hp.
    assert (typing v E D P (trm_fix t1) (typ_arrow T1 T2))
      as Ht2 by assumption.
    invert_typing Ht2 He Hd Hp.
    pick_fresh x.
    pick_fresh y.
    rewrite trm_subst_intro with (xs := cons y (x::nil));
      auto with wellformed.
    assert (coercible v E T3 T2)
      by eauto using invert_coercible_arrow_right.
    assert (coercible v E T1 T0)
      by eauto using invert_coercible_arrow_left.
    apply typing_trm_subst_empty2_l
      with (T2 := typ_arrow T0 T3) (T3 := T0);
      eauto using typing_coercible with wellformed.
  - invert_typing Ht He Hd Hp.
    assert (typing v E D P t T1) as Ht2 by auto.
    destruct (IHHr Hst _ Hp Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
    eauto using typing_coercible.
  - invert_typing Ht He Hd Hp.
    assert (typing v E D P t1 (typ_variant T1)) as Ht2 by auto.
    destruct (IHHr Hst _ Hp Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
    apply typing_coercible with T4; auto.
    apply typing_match with (L := L \u dom E \u dom D)
      (T1 := T1) (T2 := T2) (T3 := T3) (T4 := T4);
      eauto using typing_extend_store_type with wellformed.
  - subst.
    exists P.
    splits; auto.
    invert_typing Ht He Hd Hp.
    assert
      (typing v E D P (trm_constructor c2 t1) (typ_variant T1))
      as Ht2 by assumption.
    invert_typing Ht2 He Hd Hp.
    assert (valid_tenv_extension v E empty) by auto.
    assert (kinding E empty T2 knd_row_all)
      by auto with kinding.
    pick_fresh x.
    rewrite trm_subst_single_intro with (x := x);
      auto with wellformed.
    apply typing_trm_subst_empty_l with (T2 := typ_variant T2);
      eauto using typing_coercible with wellformed.
    apply typing_constructor with (T1 := T0); auto.
    subst_subtype (typ_constructor c2 T0).
    subst_subtype ((typ_proj CSet.universe (CSet.singleton c2) T2)).
    assert (subtype v E empty T5 T1 knd_row_all) as Hs2
      by (apply invert_coercible_variant; auto).
    rewrite Hs2.
    sreflexivity.
  - exists P.
    splits; auto.
    invert_typing Ht He Hd Hp.
    assert
      (typing v E D P (trm_constructor c1 t1) (typ_variant T1))
      as Ht2 by assumption.
    invert_typing Ht2 He Hd Hp.
    assert (valid_tenv_extension v E empty) by auto.
    assert (kinding E empty T3 knd_row_all)
      by auto with kinding.
    pick_fresh x.
    rewrite trm_subst_single_intro with (x := x);
      auto with wellformed.
    apply typing_trm_subst_empty_l with (T2 := typ_variant T3);
      eauto using typing_coercible with wellformed.
    apply typing_constructor with (T1 := T0); auto.
    subst_subtype (typ_constructor c1 T0).
    assert (subtype v E empty T5 T1 knd_row_all) as Hs2
      by (apply invert_coercible_variant; auto).
    rewrite Hs2.
    apply subtype_proj_subset with (cs3 := CSet.cosingleton c2);
      auto with csetdec.
  - invert_typing Ht He Hd Hp.
    assert (typing v E D P t1 (typ_variant T1)) as Ht2 by auto.
    destruct (IHHr Hst _ Hp Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
    apply typing_coercible with T3; auto.
    apply typing_destruct with (L := L \u dom D)
      (T1 := T1) (T2 := T2); auto.
    eauto using typing_extend_store_type with wellformed.
  - subst.
    exists P.
    splits; auto.
    invert_typing Ht He Hd Hp.
    assert
      (typing v E D P (trm_constructor c2 t1) (typ_variant T1))
      as Ht2 by assumption.
    invert_typing Ht2 He Hd Hp.
    pick_fresh x.
    rewrite trm_subst_single_intro with (x := x);
      auto with wellformed.
    assert (coercible v E T0 T2)
      by eauto using invert_coercible_variant_constructor.
    apply typing_trm_subst_empty_l with (T2 := T2);
      eauto using typing_coercible with wellformed.
  - invert_typing Ht He Hd Hp.
    assert (typing v E D P t (typ_variant T1)) as Ht2 by auto.
    destruct (IHHr Hst _ Hp Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
    eauto using typing_coercible.
  - invert_typing Ht He Hd Hp.
    assert (typing v E D P t1 T1) as Ht2 by auto.
    destruct (IHHr Hst _ Hp Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
    eauto using typing_coercible, typing_extend_store_type
      with wellformed.
  - invert_typing Ht He Hd Hp.
    assert (typing v E D P t2 T2) as Ht2 by auto.
    destruct (IHHr Hst _ Hp Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
    eauto using typing_coercible, typing_extend_store_type
      with wellformed.
  - invert_typing Ht He Hd Hp.
    assert (typing v E D P t (typ_prod T1 T2)) as Ht2 by auto.
    destruct (IHHr Hst _ Hp Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
    eauto using typing_coercible.
  - exists P.
    splits; auto.
    invert_typing Ht He Hd Hp.
    assert
      (typing v E D P (trm_prod t1 t2) (typ_prod T1 T2))
      as Ht2 by assumption.
    invert_typing Ht2 He Hd Hp.
    assert (coercible v E T0 T1)
      by eauto using invert_coercible_prod_left.
    eauto using typing_coercible.
  - invert_typing Ht He Hd Hp.
    assert (typing v E D P t (typ_prod T1 T2)) as Ht2 by auto.
    destruct (IHHr Hst _ Hp Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
    eauto using typing_coercible.
  - exists P.
    splits; auto.
    invert_typing Ht He Hd Hp.
    assert
      (typing v E D P (trm_prod t1 t2) (typ_prod T1 T2))
      as Ht2 by assumption.
    invert_typing Ht2 He Hd Hp.
    assert (coercible v E T3 T2)
      by eauto using invert_coercible_prod_right.
    eauto using typing_coercible.
  - invert_typing Ht He Hd Hp.
    assert (typing v E D P t T1) as Ht2 by auto.
    destruct (IHHr Hst _ Hp Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
    eauto using typing_coercible.
  - invert_typing Ht He Hd Hp.
    exists (P & l ~ T1).
    remember Hs as Hs'.
    destruct Hs' as [? ? ? ? ? Hsl].
    destruct (Hsl l).
    + splits; eauto using typing_store_ref, typing_coercible,
        output_typing with wellformed. 
    + exfalso. eauto using binds_fresh_inv.
  - invert_typing Ht He Hd Hp.
    assert (typing v E D P t (typ_ref T1)) as Ht2 by auto.
    destruct (IHHr Hst _ Hp Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; eauto using typing_coercible.
  - exists P.
    splits; auto.
    invert_typing Ht He Hd Hp.
    assert (typing v E D P (trm_loc l) (typ_ref T1)) as Ht2
        by assumption.
    invert_typing Ht2 He Hd Hp.
    destruct Hs as [? ? ? ? ? Hsl].
    destruct (Hsl l).
    + exfalso. eauto using binds_fresh_inv.
    + replace t0 with t in *
        by eauto using binds_functional.
      replace T0 with T2 in *
        by eauto using binds_functional.
      assert (coercible v E T2 T1)
        by eauto using invert_coercible_ref_covariant.
      eauto using typing_coercible.
  - invert_typing Ht He Hd Hp.
    assert (typing v E D P t1 (typ_ref T1)) as Ht2 by auto.
    destruct (IHHr Hst _ Hp Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
    eauto using typing_coercible,
      typing_extend_store_type with wellformed.
  - invert_typing Ht He Hd Hp.
    assert (typing v E D P t2 T1) as Ht2 by auto.
    destruct (IHHr Hst _ Hp Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
    eauto using typing_coercible,
      typing_extend_store_type with wellformed.
  - exists P.
    invert_typing Ht He Hd Hp.
    assert (typing v E D P (trm_loc l) (typ_ref T1)) as Ht2
        by assumption.
    invert_typing Ht2 He Hd Hp.
    splits; eauto using typing_coercible.
    assert (coercible v E T1 T0) as Hc
      by eauto using invert_coercible_ref_contravariant.
    eauto using typing_store_set, typing_coercible
      with wellformed kinding.
Qed.

(* *************************************************************** *)
(** * Progress *)

Lemma progress : progress.
Proof.
  unfold progress.
  introv He Hp Hv Ht Hs.
  assert (valid_env v E empty) as Hd by auto.
  remember empty as D.
  assert (term t) as Htrm by auto with wellformed.
  induction_with_envs Ht He Hd Hp; subst; auto.
  - exfalso; eauto using binds_empty_inv.
  - inversion Htrm; subst.
    assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by auto.
    assert (value t2 \/ (exists t2' V2', red t2 V t2' V2'))
      as IH2 by auto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]];
      destruct IH2 as [Hv2|[t2' [V2' He2]]];
        eauto.
    eapply invert_value_arrow with (t := t1); try eassumption;
      intros; subst; eauto.
  - pick_freshes_gen L (sch_arity M) Xs.
    assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]]; eauto 6.
  - inversion Htrm; subst.
    assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]]; eauto.
  - inversion Htrm; subst.
    assert (value t \/ (exists t' V', red t V t' V'))
      as IH by eauto.
    destruct IH as [Hv1|[t' [V' He1]]]; eauto.
  - inversion Htrm; subst.
    assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]]; eauto.
    eapply invert_value_variant with (t := t1); try eassumption;
      intros; subst.
    destruct (Nat.eq_dec c c0); subst; eauto.
  - inversion Htrm; subst.
    assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]]; eauto.
    eapply invert_value_variant with (t := t1); try eassumption;
      intros; subst.    
    destruct (Nat.eq_dec c c0); subst; eauto.
    exfalso.
    eapply typing_constructor_inv
      with (c := c0) (t1 := t0); try eassumption; intros.
    apply invert_subtype_constructor_bot
      with (v := v) (E1 := E) (E2 := empty) (c := c0)
           (cs := CSet.singleton c0) (T1 := T0); auto.
    assert (subtype v E empty (typ_constructor c0 T0)
             (typ_proj CSet.universe (CSet.singleton c0) T4)
             (knd_row (CSet.singleton c0)))
      as Hs1 by assumption.
    assert (subtype v E empty T4 T1 knd_row_all)
      as Hs2 by auto using invert_coercible_variant.
    assert (subtype v E empty
              (typ_proj CSet.universe (CSet.cosingleton c) T1)
              (typ_bot (knd_row (CSet.cosingleton c)))
              (knd_row (CSet.cosingleton c)))
      as Hs3 by assumption.
    apply subtype_proj_subset_bottom
      with (cs3 := CSet.singleton c0) in Hs3; auto with csetdec.
    rewrite Hs1.
    rewrite Hs2.
    rewrite Hs3.
    sreflexivity.
  - inversion Htrm; subst.
    assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]]; eauto.
    eapply invert_value_variant with (t := t1);
      try eassumption; intros; subst.
    exfalso.
    eapply typing_constructor_inv
      with (c := c) (t1 := t0); try eassumption; intros.
    apply invert_subtype_constructor_bot
      with (v := v) (E1 := E) (E2 := empty) (c := c)
           (cs := CSet.singleton c) (T1 := T0); auto.
    assert (subtype v E empty (typ_constructor c T0)
             (typ_proj CSet.universe (CSet.singleton c) T3)
             (knd_row (CSet.singleton c)))
      as Hs1 by assumption.
    assert (subtype v E empty T3 T1 knd_row_all)
      as Hs2 by auto using invert_coercible_variant.
    assert (subtype v E empty T1 (typ_bot knd_row_all) knd_row_all)
      as Hs3 by assumption.
    rewrite Hs1.
    rewrite Hs2.
    rewrite Hs3.
    rewrite type_equal_proj_bot; auto with csetdec.
    sreflexivity.
  - inversion Htrm; subst.
    assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by auto.
    assert (value t2 \/ (exists t2' V2', red t2 V t2' V2'))
      as IH2 by auto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]];
      destruct IH2 as [Hv2|[t2' [V2' He2]]];
        eauto.
  - inversion Htrm; subst.
    assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]]; eauto.
    eapply invert_value_prod with (t := t1); try eassumption;
      intros; subst; eauto.
  - inversion Htrm; subst.
    assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]]; eauto.
    eapply invert_value_prod with (t := t1); try eassumption;
      intros; subst; eauto.
  - inversion Htrm; subst.
    assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]]; eauto.
    pick_fresh_gen (dom V) l; eauto.
  - inversion Htrm; subst.
    assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]]; eauto.
    eapply invert_value_ref with (t := t1); try eassumption;
      intros; subst.
    eapply typing_loc_inv with (l := l); try eassumption;
      intros.
    destruct Hs as [? ? ? ? ? Hsl].
    destruct (Hsl l).
    + exfalso; eauto using binds_fresh_inv.
    + eauto.
  - inversion Htrm; subst.
    assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by eauto.
    assert (value t2 \/ (exists t2' V2', red t2 V t2' V2'))
      as IH2 by auto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]];
      destruct IH2 as [Hv2|[t2' [V2' He2]]]; eauto.
    eapply invert_value_ref with (t := t1); try eassumption;
      intros; subst.
    eauto.
Qed.
