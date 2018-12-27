
(************************************************
 *          Row Subtyping - Soundness           *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import Arith LibLN.
Require Import Cofinite Disjoint Definitions Substitution
        Wellformedness Kinding Subtyping Ranging Typing.

Hint Constructors red.

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
  introv He1 He2 Hv Hst Ht Hs Hr.
  generalize dependent T.
  generalize dependent P.
  induction Hr; introv Hv Hs Ht.
  - exists P.
    splits; auto.
    inversion Ht; subst.
    + pick_fresh x.
      rewrite trm_subst_single_intro with (x := x);
        auto with wellformed.
      apply typing_trm_subst_single_l with (M := M);
        eauto with wellformed.
    + assert (kinding E T1 knd_type)
        by eauto using output_typing with wellformed.
      pick_fresh x.
      rewrite trm_subst_single_intro with (x := x);
        auto with wellformed.
      apply typing_trm_subst_empty_l with (T2 := T1);
        auto with wellformed.
  - inversion Ht; subst.
    + assert (value t1) as Hvl by assumption.
      exfalso.
      apply (values_do_not_reduce Hvl Hr).
    + assert (typing E D P t1 T1) as Ht2 by auto.
      destruct (IHHr Hst _ Hv Hs _ Ht2)
        as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
      exists P'.
      splits; auto.
      apply typing_let with (L := L \u dom E) (T1 := T1);
        auto.
      introv Hn.
      apply typing_extend_store_type with (P := P);
        auto with wellformed. 
  - inversion Ht; subst.
    assert (typing E D P t1 (typ_arrow S T)) as Ht2 by auto.
    destruct (IHHr Hst _ Hv Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
    eauto using typing_extend_store_type with wellformed.
  - inversion Ht; subst.
    assert (typing E D P t2 S) as Ht2 by auto.
    destruct (IHHr Hst _ Hv Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
    eauto using typing_extend_store_type with wellformed.
  - exists P.
    splits; auto.
    inversion Ht; subst.
    assert (typing E D P (trm_abs t1) (typ_arrow S T)) as Ht2
      by assumption.
    inversion Ht2; subst.
    pick_fresh x.
    rewrite trm_subst_single_intro with (x := x);
      auto with wellformed.
    apply typing_trm_subst_empty_l with (T2 := S);
      auto with wellformed.
  - exists P.
    splits; auto.
    inversion Ht; subst.
    assert (typing E D P (trm_fix t1) (typ_arrow S T)) as Ht2
      by assumption.
    inversion Ht2; subst.
    pick_fresh x.
    pick_fresh y.
    rewrite trm_subst_intro with (xs := cons y (x::nil));
      auto with wellformed.
    apply typing_trm_subst_empty2_l
      with (T2 := typ_arrow S T) (T3 := S); auto with wellformed.
  - inversion Ht; subst.
    assert (typing E D P t T3) as Ht2 by auto.
    destruct (IHHr Hst _ Hv Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
    eauto using typing_extend_store_type.
  - inversion Ht; subst.
    assert (typing E D P t1 (typ_variant T1)) as Ht2 by auto.
    destruct (IHHr Hst _ Hv Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
    apply typing_match with (L := L \u dom E \u dom D)
      (T1 := T1) (T2 := T2) (T3 := T3) (T4 := T4) (T5 := T5)
      (T6 := T6) (T7 := T7);
      eauto using typing_extend_store_type with wellformed.
  - exists P.
    splits; auto.
    inversion Ht; subst.
    assert
      (typing E D P (trm_constructor c2 t1) (typ_variant T1))
      as Ht2 by assumption.
    inversion Ht2; subst.
    pick_fresh x.
    rewrite trm_subst_single_intro with (x := x); auto with wellformed.
    apply typing_trm_subst_empty_l with (T2 := typ_variant T3);
      auto with wellformed.
    apply typing_constructor with (T2 := T4) (T3 := T9); auto.
    apply subtype_transitive
      with (T2 := typ_proj CSet.universe T8 (CSet.singleton c2));
      auto with wellformed.
    apply subtype_transitive
      with (T2 := typ_proj CSet.universe T2 (CSet.singleton c2));
      auto with wellformed.
    eauto using subtype_proj, subtype_from_ranges
      with wellformed csetdec.
  - exists P.
    splits; auto.
    inversion Ht; subst.
    assert
      (typing E D P (trm_constructor c1 t1) (typ_variant T1))
      as Ht2 by assumption.
    inversion Ht2; subst.
    pick_fresh x.
    rewrite trm_subst_single_intro with (x := x);
      auto with wellformed.
    apply typing_trm_subst_empty_l with (T2 := typ_variant T5);
      auto with wellformed.
    apply typing_constructor with (T2 := T6) (T3 := T9); auto.
    apply subtype_transitive
      with (T2 := typ_proj CSet.universe T8 (CSet.singleton c1));
      auto with wellformed.
    apply subtype_transitive
      with (T2 := typ_proj CSet.universe T2 (CSet.singleton c1));
      auto with wellformed.
    + eauto using subtype_proj, subtype_from_ranges
        with wellformed csetdec.
    + eauto using subtype_proj_subset with wellformed csetdec.
  - inversion Ht; subst.
    assert (typing E D P t1 (typ_variant T1)) as Ht2 by auto.
    destruct (IHHr Hst _ Hv Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
    apply typing_destruct with (L := L \u dom D)
      (T1 := T1) (T2 := T2) (T3 := T3); auto.
    eauto using typing_extend_store_type with wellformed.
  - exists P.
    splits; auto.
    inversion Ht; subst.
    assert
      (typing E D P (trm_constructor c2 t1) (typ_variant T1))
      as Ht2 by assumption.
    assert (type_environment E) by auto with wellformed.
    assert (kinding E T3 knd_type) by auto with kinding.
    inversion Ht2; subst.
    pick_fresh x.
    rewrite trm_subst_single_intro with (x := x);
      auto with wellformed.
    apply typing_trm_subst_empty_l with (T2 := T3);
      auto with wellformed.
    apply typing_equal with (T1 := T5);
      auto with wellformed.
    apply subtype_preserves_constructor
      with (c := c2); auto. 
    apply subtype_transitive
      with (T2 := typ_proj CSet.universe T4 (CSet.singleton c2));
      auto.
    apply subtype_transitive
      with (T2 := typ_proj CSet.universe T2 (CSet.singleton c2));
      auto.
    eauto using subtype_proj, subtype_from_ranges with csetdec.
  - inversion Ht; subst.
    assert (typing E D P t (typ_variant T1)) as Ht2 by auto.
    destruct (IHHr Hst _ Hv Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
    eauto using typing_extend_store_type.
  - inversion Ht; subst.
    assert (typing E D P t1 T1) as Ht2 by auto.
    destruct (IHHr Hst _ Hv Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
    eauto using typing_extend_store_type with wellformed.
  - inversion Ht; subst.
    assert (typing E D P t2 T2) as Ht2 by auto.
    destruct (IHHr Hst _ Hv Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
    eauto using typing_extend_store_type with wellformed.
  - inversion Ht; subst.
    assert (typing E D P t (typ_prod T T2)) as Ht2 by auto.
    destruct (IHHr Hst _ Hv Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
    eauto using typing_extend_store_type.
  - exists P.
    splits; auto.
    inversion Ht; subst.
    assert
      (typing E D P (trm_prod t1 t2) (typ_prod T T2))
      as Ht2 by assumption.
    inversion Ht2; subst.
    auto.
  - inversion Ht; subst.
    assert (typing E D P t (typ_prod T1 T)) as Ht2 by auto.
    destruct (IHHr Hst _ Hv Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
    eauto using typing_extend_store_type.
  - exists P.
    splits; auto.
    inversion Ht; subst.
    assert
      (typing E D P (trm_prod t1 t2) (typ_prod T1 T))
      as Ht2 by assumption.
    inversion Ht2; subst.
    auto.
  - inversion Ht; subst.
    assert (typing E D P t T0) as Ht2 by auto.
    destruct (IHHr Hst _ Hv Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
  - inversion Ht; subst.   
    assert (kinding E T0 knd_type)
      by eauto using output_typing with wellformed.
    exists (P & l ~ T0).
    remember Hs as Hs'.
    destruct Hs' as [? ? ? ? Hsl].
    destruct (Hsl l).
    + splits; auto using typing_store_ref with wellformed.
        apply typing_loc with (T1 := T0); auto.
    + exfalso. eauto using binds_fresh_inv.
  - inversion Ht; subst.
    assert (typing E D P t (typ_ref T)) as Ht2 by auto.
    destruct (IHHr Hst _ Hv Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
  - exists P.
    splits; auto.
    inversion Ht; subst.
    assert (typing E D P (trm_loc l) (typ_ref T)) as Ht2
        by assumption.
    inversion Ht2; subst.
    destruct Hs as [? ? ? ? Hsl].
    destruct (Hsl l).
    + exfalso. eauto using binds_fresh_inv.
    + replace t0 with t in * by eauto using binds_func.
      replace T0 with T1 in * by eauto using binds_func.
      eauto using typing_equal with wellformed.
  - inversion Ht; subst.
    assert (typing E D P t1 (typ_ref T0)) as Ht2 by auto.
    destruct (IHHr Hst _ Hv Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
    eauto using typing_extend_store_type with wellformed.
  - inversion Ht; subst.
    assert (typing E D P t2 T0) as Ht2 by auto.
    destruct (IHHr Hst _ Hv Hs _ Ht2)
      as [P' [Hex [Hv' [Hst' [Ht' Hs']]]]].
    exists P'.
    splits; auto.
    eauto using typing_extend_store_type with wellformed.
  - exists P.
    inversion Ht; subst.
    assert (typing E D P (trm_loc l) (typ_ref T0)) as Ht2
        by assumption.
    inversion Ht2; subst.
    splits; auto.
    eapply typing_store_set;
      eauto using typing_equal, type_equal_symmetric
        with wellformed.
Qed.

(* *************************************************************** *)
(** * Progress *)

Lemma progress : progress.
Proof.
  unfold progress.
  introv He Hv Hst Ht Hs.
  remember empty as D.
  assert (term t) as Htrm by auto with wellformed.
  induction Ht; subst; auto.
  - exfalso; eauto using binds_empty_inv.
  - inversion Htrm; subst.
    assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by auto.
    assert (value t2 \/ (exists t2' V2', red t2 V t2' V2'))
      as IH2 by auto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]];
      destruct IH2 as [Hv2|[t2' [V2' He2]]];
        eauto.
    destruct Hv1; inversion Ht1; subst; eauto.
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
    destruct Hv1; inversion Ht; subst.
    destruct (Nat.eq_dec c c0); subst; eauto.
  - inversion Htrm; subst.
    assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]]; eauto.
    destruct Hv1; inversion Ht; subst.
    destruct (Nat.eq_dec c c0); subst; eauto.
    exfalso.
    apply no_subtype_constructor_bot
      with (E := E) (T := T6) (c := c0); auto with wellformed.
    apply subtype_transitive
      with (T2 := typ_proj CSet.universe T5 (CSet.singleton c0));
      auto with wellformed.
    apply subtype_transitive
      with (T2 := typ_proj CSet.universe T2 (CSet.singleton c0));
      eauto using subtype_proj, subtype_from_ranges
        with wellformed csetdec.
    eauto using subtype_proj_subset_bottom
      with wellformed csetdec.
  - inversion Htrm; subst.
    assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]]; eauto.
    destruct Hv1; inversion Ht; subst.
    exfalso.
    apply no_subtype_constructor_bot
      with (E := E) (T := T4) (c := c); auto with wellformed.
    apply subtype_transitive
      with (T2 := typ_proj CSet.universe T3 (CSet.singleton c));
      auto with wellformed.
    apply subtype_transitive
      with (T2 :=
              typ_proj CSet.universe
                (typ_bot CSet.universe) (CSet.singleton c));
      eauto using subtype_proj, subtype_from_ranges
        with wellformed csetdec.
    auto using subtype_reflexive, type_equal_proj_bot
      with wellformed csetdec.
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
    destruct Hv1; inversion Ht; subst; eauto.
  - inversion Htrm; subst.
    assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]]; eauto.
    destruct Hv1; inversion Ht; subst; eauto.
  - inversion Htrm; subst.
    assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]]; eauto.
    pick_fresh_gen (dom V) l; eauto.
  - inversion Htrm; subst.
    assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]]; eauto.
    destruct Hv1; inversion Ht; subst.
    destruct Hs as [? ? ? ? Hsl].
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
    destruct Hv1; inversion Ht1; subst.
    eauto.
Qed.
