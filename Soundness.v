
(************************************************
 *          Row Subtyping - Soundness           *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import LibLN Cofinite Definitions Substitution
        Wellformedness Kinding Subtyping Typing.

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

Qed.
