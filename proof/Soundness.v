
(************************************************
 *          Row Subtyping - Soundness           *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import Arith LibLN.
Require Import Cofinite Disjoint Definitions Substitution
        Wellformedness Kinding Subtyping Typing.

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
  introv Ht Hs Hr.
  apply validated_typing in Ht.
  generalize dependent T.
  generalize dependent P.
  induction Hr; introv Hs Ht.
  - exists P.
    splits; auto.
    inversion Ht; subst.
    + pick_fresh x.
      rewrite trm_subst_single_intro with (x := x); auto.
      apply typing_trm_subst_single_l with (M := M); eauto.
    + pick_fresh x.
      rewrite trm_subst_single_intro with (x := x); auto.
      apply typing_trm_subst_empty_l with (T2 := T1); auto.
  - inversion Ht; subst.
    + assert (value t1) as Hv by assumption.
      exfalso.
      apply (values_do_not_reduce Hv Hr).
    + assert (typing_validated E P t1 T1) as Ht2 by auto.
      destruct (IHHr _ Hs _ Ht2) as [P' [He [Ht' Hs']]].
      exists P'.
      splits; auto.
      apply typing_let with (L := L \u dom E) (T1 := T1); auto.
      introv Hn.
      apply typing_extend_store_type with (P := P);
        auto using valid_store_type_add_typ_bind_l,
          valid_scheme_empty_of_kinding
            with typing_store_validated.
  - inversion Ht; subst.
    assert (typing_validated E P t1 (typ_arrow S T)) as Ht2 by auto.
    destruct (IHHr _ Hs _ Ht2) as [P' [He [Ht' Hs']]].
    exists P'.
    splits; auto.
    eauto using typing_extend_store_type with typing_store_validated.
  - inversion Ht; subst.
    assert (typing_validated E P t2 S) as Ht2 by auto.
    destruct (IHHr _ Hs _ Ht2) as [P' [He [Ht' Hs']]].
    exists P'.
    splits; auto.
    eauto using typing_extend_store_type with typing_store_validated.
  - exists P.
    splits; auto.
    inversion Ht; subst.
    assert (typing_validated E P (trm_abs t1) (typ_arrow S T)) as Ht2
      by assumption.
    inversion Ht2; subst.
    pick_fresh x.
    rewrite trm_subst_single_intro with (x := x); auto.
    apply typing_trm_subst_empty_l with (T2 := S); auto.
  - exists P.
    splits; auto.
    inversion Ht; subst.
    assert (typing_validated E P (trm_fix t1) (typ_arrow S T)) as Ht2
      by assumption.
    inversion Ht2; subst.
    pick_fresh x.
    pick_fresh y.
    rewrite trm_subst_intro with (xs := cons x (y::nil)); auto.
    apply typing_trm_subst_empty2_l
      with (T2 := typ_arrow S T) (T3 := S); auto.
  - inversion Ht; subst.
    assert (typing_validated E P t T3) as Ht2 by auto.
    destruct (IHHr _ Hs _ Ht2) as [P' [He [Ht' Hs']]].
    exists P'.
    splits; auto.
    eauto using typing_extend_store_type with typing_store_validated.
  - inversion Ht; subst.
    assert (typing_validated E P t1 (typ_variant T1)) as Ht2 by auto.
    destruct (IHHr _ Hs _ Ht2) as [P' [He [Ht' Hs']]].
    exists P'.
    splits; auto.
    apply typing_match with (L := L \u dom E) (T1 := T1) (T2 := T2)
      (T3 := T3) (T4 := T4) (T5 := T5) (T6 := T6) (T7 := T7); auto;
      eauto 8 using typing_extend_store_type,
        valid_store_type_add_typ_bind_l,
        valid_scheme_empty_of_kinding, kinding_range_top_bot
        with typing_store_validated.
  - exists P.
    splits; auto.
    inversion Ht; subst.
    assert
      (typing_validated E P (trm_constructor c2 t1) (typ_variant T1))
      as Ht2 by assumption.
    inversion Ht2; subst.
    pick_fresh x.
    rewrite trm_subst_single_intro with (x := x); auto.
    apply typing_trm_subst_empty_l with (T2 := typ_variant T3); auto.
    apply typing_constructor with (T2 := T4) (T3 := T9); auto.
    apply subtype_transitive
      with (T2 := typ_proj CSet.universe T8 (CSet.singleton c2));
      auto.
    apply subtype_transitive
      with (T2 := typ_proj CSet.universe T2 (CSet.singleton c2));
      auto.
    eauto using subtype_proj, subtype_from_ranges with csetdec.
  - exists P.
    splits; auto.
    inversion Ht; subst.
    assert
      (typing_validated E P (trm_constructor c1 t1) (typ_variant T1))
      as Ht2 by assumption.
    inversion Ht2; subst.
    pick_fresh x.
    rewrite trm_subst_single_intro with (x := x); auto.
    apply typing_trm_subst_empty_l with (T2 := typ_variant T5); auto.
    apply typing_constructor with (T2 := T6) (T3 := T9); auto.
    apply subtype_transitive
      with (T2 := typ_proj CSet.universe T8 (CSet.singleton c1));
      auto.
    apply subtype_transitive
      with (T2 := typ_proj CSet.universe T2 (CSet.singleton c1)).
    + eauto using subtype_proj, subtype_from_ranges with csetdec.
    + eauto using subtype_proj_subset with csetdec.
  - inversion Ht; subst.
    assert (typing_validated E P t1 (typ_variant T1)) as Ht2 by auto.
    destruct (IHHr _ Hs _ Ht2) as [P' [He [Ht' Hs']]].
    exists P'.
    splits; auto.
    apply typing_destruct with (L := L \u dom E)
      (T1 := T1) (T2 := T2) (T3 := T3); auto.
    eauto 6 using typing_extend_store_type, 
      valid_store_type_add_typ_bind_l,
      valid_scheme_empty_of_kinding with typing_store_validated.
  - exists P.
    splits; auto.
    inversion Ht; subst.
    assert
      (typing_validated E P (trm_constructor c2 t1) (typ_variant T1))
      as Ht2 by assumption.
    inversion Ht2; subst.
    pick_fresh x.
    rewrite trm_subst_single_intro with (x := x); auto.
    apply typing_trm_subst_empty_l with (T2 := T3); auto.
    apply typing_equal with (T1 := T5); auto.
    apply subtype_preserves_constructor
      with (c := c2). 
    apply subtype_transitive
      with (T2 := typ_proj CSet.universe T4 (CSet.singleton c2));
      auto.
    apply subtype_transitive
      with (T2 := typ_proj CSet.universe T2 (CSet.singleton c2));
      auto.
    eauto using subtype_proj, subtype_from_ranges with csetdec.
  - inversion Ht; subst.
    assert (typing_validated E P t (typ_variant T1)) as Ht2 by auto.
    destruct (IHHr _ Hs _ Ht2) as [P' [He [Ht' Hs']]].
    exists P'.
    splits; auto.
    eauto using typing_extend_store_type with typing_store_validated.
  - inversion Ht; subst.
    assert (typing_validated E P t1 T1) as Ht2 by auto.
    destruct (IHHr _ Hs _ Ht2) as [P' [He [Ht' Hs']]].
    exists P'.
    splits; auto.
    eauto using typing_extend_store_type with typing_store_validated.
  - inversion Ht; subst.
    assert (typing_validated E P t2 T2) as Ht2 by auto.
    destruct (IHHr _ Hs _ Ht2) as [P' [He [Ht' Hs']]].
    exists P'.
    splits; auto.
    eauto using typing_extend_store_type with typing_store_validated.
  - inversion Ht; subst.
    assert (typing_validated E P t (typ_prod T T2)) as Ht2 by auto.
    destruct (IHHr _ Hs _ Ht2) as [P' [He [Ht' Hs']]].
    exists P'.
    splits; auto.
    eauto using typing_extend_store_type with typing_store_validated.
  - exists P.
    splits; auto.
    inversion Ht; subst.
    assert
      (typing_validated E P (trm_prod t1 t2) (typ_prod T T2))
      as Ht2 by assumption.
    inversion Ht2; subst.
    auto.
  - inversion Ht; subst.
    assert (typing_validated E P t (typ_prod T1 T)) as Ht2 by auto.
    destruct (IHHr _ Hs _ Ht2) as [P' [He [Ht' Hs']]].
    exists P'.
    splits; auto.
    eauto using typing_extend_store_type with typing_store_validated.
  - exists P.
    splits; auto.
    inversion Ht; subst.
    assert
      (typing_validated E P (trm_prod t1 t2) (typ_prod T1 T))
      as Ht2 by assumption.
    inversion Ht2; subst.
    auto.
  - inversion Ht; subst.
    assert (typing_validated E P t T0) as Ht2 by auto.
    destruct (IHHr _ Hs _ Ht2) as [P' [He [Ht' Hs']]].
    exists P'.
    splits; auto.
  - inversion Ht; subst.
    exists (P & l ~ T0).
    destruct Hs as [_ [_ [? Hv]]].
    splits; eauto using extends_push.
    splits; auto.
    introv Hb.
    destruct (binds_push_inv Hb) as [[? ?]|[? Hb2]].
    + subst.
      exists t.
      split; auto.
      eauto 7 using typing_extend_store_type.
    + destruct (Hv _ _ Hb2) as [t1 [? ?]].
      exists t1.
      split; auto.
      eauto 6 using typing_extend_store_type.
  - inversion Ht; subst.
    assert (typing_validated E P t (typ_ref T)) as Ht2 by auto.
    destruct (IHHr _ Hs _ Ht2) as [P' [He [Ht' Hs']]].
    exists P'.
    splits; auto.
  - exists P.
    splits; auto.
    inversion Ht; subst.
    assert (typing_validated E P (trm_loc l) (typ_ref T)) as Ht2
        by assumption.
    inversion Ht2; subst.
    assert (binds l T1 P) as Hb2 by assumption.
    destruct Hs as [_ [_ [_ Hv]]].
    destruct (Hv _ _ Hb2) as [t' [? ?]].
    replace t with t' by eauto using binds_func.
    eauto using typing_equal.
  - inversion Ht; subst.
    assert (typing_validated E P t1 (typ_ref T0)) as Ht2 by auto.
    destruct (IHHr _ Hs _ Ht2) as [P' [He [Ht' Hs']]].
    exists P'.
    splits; auto.
    eauto using typing_extend_store_type with typing_store_validated.
  - inversion Ht; subst.
    assert (typing_validated E P t2 T0) as Ht2 by auto.
    destruct (IHHr _ Hs _ Ht2) as [P' [He [Ht' Hs']]].
    exists P'.
    splits; auto.
    eauto using typing_extend_store_type with typing_store_validated.
  - inversion Ht; subst.
    exists P.
    splits; auto.
    assert (typing_validated E P (trm_loc l) (typ_ref T0)) as Ht2
        by assumption.
    inversion Ht2; subst.
    destruct Hs as [_ [_ [Hn Hv]]].
    splits; auto.
    introv Hb.
    case_if_eq l l0.
    + exists t2.
      split; auto.
      replace T with T1 by eauto using binds_func.
      eauto using typing_equal, type_equal_symmetric.   
    + destruct (Hv _ _ Hb) as [t' [? ?]].
      exists t'.
      split; auto.
Qed.

(* *************************************************************** *)
(** * Progress *)

Lemma progress : progress.
Proof.
  unfold progress.
  introv Hb Ht Hv.
  apply validated_typing in Ht.
  assert (store V) by auto with typing_store_regular.
  induction Ht; auto.
  - exfalso; eapply Hb; eauto.
  - assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by auto.
    assert (value t2 \/ (exists t2' V2', red t2 V t2' V2'))
      as IH2 by auto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]];
      destruct IH2 as [Hv2|[t2' [V2' He2]]];
        eauto.
    destruct Hv1; inversion Ht1; subst; eauto.
  - pick_freshes_gen L (sch_arity M) Xs.
    assert (no_term_bindings (E & Xs ~::* M))
      by auto with no_term_bindings.
    assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]]; eauto 6.
  - assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]]; eauto 6.
  - assert (value t \/ (exists t' V', red t V t' V'))
      as IH by eauto.
    destruct IH as [Hv1|[t' [V' He1]]]; eauto 6.
  - assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]]; eauto.
    destruct Hv1; inversion Ht; subst.
    destruct (Nat.eq_dec c c0); subst; eauto 6.
  - assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]]; eauto.
    destruct Hv1; inversion Ht; subst.
    destruct (Nat.eq_dec c c0); subst; eauto 6.
    exfalso.
    apply no_subtype_constructor_bot
      with (chk := true) (E := E) (T := T6) (c := c0).
    apply subtype_transitive
      with (T2 := typ_proj CSet.universe T5 (CSet.singleton c0));
      auto.
    apply subtype_transitive
      with (T2 := typ_proj CSet.universe T2 (CSet.singleton c0));
      eauto using subtype_proj, subtype_from_ranges with csetdec.
    eauto using subtype_proj_subset_bottom with csetdec.
  - assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]]; eauto.
    destruct Hv1; inversion Ht; subst.
    exfalso.
    apply no_subtype_constructor_bot
      with (chk := true) (E := E) (T := T4) (c := c).
    apply subtype_transitive
      with (T2 := typ_proj CSet.universe T3 (CSet.singleton c));
      auto.
    apply subtype_transitive
      with (T2 :=
              typ_proj CSet.universe
                (typ_bot CSet.universe) (CSet.singleton c));
      eauto using subtype_proj, subtype_from_ranges with csetdec.
    auto using subtype_reflexive, type_equal_proj_bot with csetdec.
  - assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by auto.
    assert (value t2 \/ (exists t2' V2', red t2 V t2' V2'))
      as IH2 by auto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]];
      destruct IH2 as [Hv2|[t2' [V2' He2]]];
        eauto.
  - assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]]; eauto.
    destruct Hv1; inversion Ht; subst; eauto.
  - assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]]; eauto.
    destruct Hv1; inversion Ht; subst; eauto.
  - assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]]; eauto.
    pick_fresh_gen (dom V) l; eauto.
  - assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]]; eauto.
    destruct Hv1; inversion Ht; subst.
    destruct Hv as [_ [_ [_ Hv2]]].
    assert (binds l T1 P) as Hb2 by assumption.
    destruct (Hv2 _ _ Hb2) as [t2 [Hb3 _]].
    eauto.
  - assert (value t1 \/ (exists t1' V1', red t1 V t1' V1'))
      as IH1 by eauto.
    assert (value t2 \/ (exists t2' V2', red t2 V t2' V2'))
      as IH2 by auto.
    destruct IH1 as [Hv1|[t1' [V1' He1]]];
      destruct IH2 as [Hv2|[t2' [V2' He2]]]; eauto.
    destruct Hv1; inversion Ht1; subst.
    eauto.
Qed.
