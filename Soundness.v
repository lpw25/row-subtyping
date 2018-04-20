
(************************************************
 *          Row Subtyping - Soundness           *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import Arith LibLN.
Require Import Cofinite Definitions Substitution
        Wellformedness Kinding Subtyping Typing.

Hint Constructors value red.

(* *************************************************************** *)
(** * Preservation *)

Lemma preservation : preservation.
Proof.
  unfold preservation.
  introv Ht Hr.
  generalize dependent T.
  generalize dependent E.
  induction Hr; introv Ht.
  - apply validated_typing in Ht.
    inversion Ht; subst.
    pick_fresh x.
    rewrite trm_subst_intro with (x := x); auto.
    apply typing_trm_subst_l with (L := L) (M := M); auto.
  - inversion Ht; subst.
    eauto.
  - inversion Ht; subst.
    eauto.
  - inversion Ht; subst.
    eauto.
  - apply validated_typing in Ht.
    inversion Ht; subst.
    assert (typing_validated E (trm_abs t1) (typ_arrow S T)) as Ht2
      by assumption.
    inversion Ht2; subst.
    pick_fresh x.
    rewrite trm_subst_intro with (x := x); auto.
    apply typing_trm_subst_empty_l with (T2 := S); auto.
  - inversion Ht; subst.
    eauto.
  - inversion Ht; subst.
    eauto.
  - apply validated_typing in Ht.
    inversion Ht; subst.
    assert
      (typing_validated E (trm_constructor c2 t1) (typ_variant T1))
      as Ht2 by assumption.
    inversion Ht2; subst.
    pick_fresh x.
    rewrite trm_subst_intro with (x := x); auto.
    apply typing_trm_subst_empty_l with (T2 := typ_variant T3); auto.
    apply typing_constructor with (T2 := T4) (T3 := T9); auto.
    apply subtype_transitive
      with (T2 := typ_proj CSet.universe T8 (CSet.singleton c2));
      auto.
    apply subtype_transitive
      with (T2 := typ_proj CSet.universe T2 (CSet.singleton c2));
      auto.
    eauto using subtype_proj, subtype_from_ranges with csetdec.
  - apply validated_typing in Ht.
    inversion Ht; subst.
    assert
      (typing_validated E (trm_constructor c1 t1) (typ_variant T1))
      as Ht2 by assumption.
    inversion Ht2; subst.
    pick_fresh x.
    rewrite trm_subst_intro with (x := x); auto.
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
    eauto.
  - apply validated_typing in Ht.
    inversion Ht; subst.
    assert
      (typing_validated E (trm_constructor c2 t1) (typ_variant T1))
      as Ht2 by assumption.
    inversion Ht2; subst.
    pick_fresh x.
    rewrite trm_subst_intro with (x := x); auto.
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
    eauto.
Qed.

(* *************************************************************** *)
(** * Progress *)

Lemma progress : progress.
Proof.
  unfold progress.
  introv Hb Ht.
  apply validated_typing in Ht.
  induction Ht; auto.
  - exfalso; eapply Hb; eauto.
  - assert (value t1 \/ (exists t1', red t1 t1')) as IH1 by auto.
    assert (value t2 \/ (exists t2', red t2 t2')) as IH2 by auto.
    destruct IH1 as [Hv1|[t1' He1]]; destruct IH2 as [Hv2|[t2' He2]];
      eauto.
    destruct Hv1; inversion Ht1; subst; eauto.
  - pick_freshes_gen L (sch_arity M) Xs.
    assert (no_term_bindings (E & Xs ~::* M))
      by auto with no_term_bindings.
    assert (value t1 \/ (exists t1', red t1 t1')) as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' He1]]; eauto.
  - assert (value t \/ (exists t', red t t')) as IH by eauto.
    destruct IH as [Hv1|[t1' He1]]; eauto.
  - assert (value t1 \/ (exists t1', red t1 t1')) as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' He1]]; eauto.
    destruct Hv1; inversion Ht; subst.
    destruct (Nat.eq_dec c c0); subst; eauto.
  - assert (value t1 \/ (exists t1', red t1 t1')) as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' He1]]; eauto.
    destruct Hv1; inversion Ht; subst.
    destruct (Nat.eq_dec c c0); subst; eauto.
    exfalso.
    apply no_subtype_constructor_bot
      with (E := E) (T := T6) (c := c0).
    apply subtype_transitive
      with (T2 := typ_proj CSet.universe T5 (CSet.singleton c0));
      auto.
    apply subtype_transitive
      with (T2 := typ_proj CSet.universe T2 (CSet.singleton c0));
      eauto using subtype_proj, subtype_from_ranges with csetdec.
    eauto using subtype_proj_subset_bottom with csetdec.
  - assert (value t1 \/ (exists t1', red t1 t1')) as IH1 by eauto.
    destruct IH1 as [Hv1|[t1' He1]]; eauto.
    destruct Hv1; inversion Ht; subst.
    exfalso.
    apply no_subtype_constructor_bot
      with (E := E) (T := T4) (c := c).
    apply subtype_transitive
      with (T2 := typ_proj CSet.universe T3 (CSet.singleton c));
      auto.
    apply subtype_transitive
      with (T2 :=
              typ_proj CSet.universe
                (typ_bot CSet.universe) (CSet.singleton c));
      eauto using subtype_proj, subtype_from_ranges with csetdec.
    auto using subtype_reflexive, type_equal_proj_bot with csetdec.
Qed.
