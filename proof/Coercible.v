(************************************************
 *          Row Subtyping - Coercible           *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import Arith.
Require Import LibLN Utilities Cofinite Disjoint Definitions
        Opening FreeVars Environments Subst Wellformedness
        Weakening Substitution Kinding Subtyping Inversion.

(* *************************************************************** *)
(** Coercibility *)

Inductive coercible : version -> tenv -> typ -> typ -> Prop :=
| coercible_row : forall E T1 T2,
    type_equal version_row_subtyping E empty T1 T2 knd_type ->
    coercible version_row_subtyping E T1 T2
| coercible_full : forall E T1 T2,
    subtype version_full_subtyping E empty T1 T2 knd_type ->
    coercible version_full_subtyping E T1 T2.

Hint Constructors coercible.

Lemma coercible_refl : forall v E T,
    kinding E empty T knd_type ->
    coercible v E T T.
Proof.
  introv Hk.
  destruct v; auto using subtype_reflexive_kinding.
Qed.

Lemma coercible_transitive : forall v E T1 T2 T3,
    coercible v E T1 T2 ->
    coercible v E T2 T3 ->
    valid_tenv v E ->
    coercible v E T1 T3.
Proof.
  introv Hc1 Hc2 He.
  inversion Hc1; inversion Hc2; subst; try discriminate.
  - eauto.
  - eauto using subtype_transitive.
Qed.

Lemma wellformed_coercible_1 : forall v E T1 T2,
    coercible v E T1 T2 ->
    type_environment E ->
    type T1.
Proof.
  introv Hc He.
  assert (type_environment_extension E empty) by auto.
  inversion Hc; subst; auto with wellformed.
Qed.

Lemma wellformed_coercible_2 : forall v E T1 T2,
    coercible v E T1 T2 ->
    type_environment E ->
    type T2.
Proof.
  introv Hc He.
  assert (type_environment_extension E empty) by auto.
  inversion Hc; subst; auto with wellformed.
Qed.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : coercible _ ?E T _,
    He : type_environment ?E |- _ =>
      apply (wellformed_coercible_1 H He)
  | H : coercible _ ?E T _,
    He : valid_tenv _ ?E |- _ =>
      apply (wellformed_coercible_1 H (wellformed_valid_tenv He))
  | H : coercible _ ?E _ T,
    He : type_environment ?E |- _ =>
      apply (wellformed_coercible_2 H He)
  | H : coercible _ ?E _ T,
    He : valid_tenv _ ?E |- _ =>
      apply (wellformed_coercible_2 H (wellformed_valid_tenv He))
  end : wellformed.

Lemma subtype_coercible : forall v E T1 T2,
    coercible v E T1 T2 ->
    valid_tenv v E ->
    subtype v E empty T1 T2 knd_type.
Proof.
  introv Hc.
  inversion Hc; subst; auto using subtype_reflexive.
Qed.

Lemma kinding_coercible_1 : forall v E T1 T2,
    coercible v E T1 T2 ->
    valid_tenv v E ->
    kinding E empty T1 knd_type.
Proof.
  introv Hc He.
  assert (valid_tenv_extension v E empty) by auto.
  inversion Hc; subst; auto with kinding.
Qed.

Lemma kinding_coercible_2 : forall v E T1 T2,
    coercible v E T1 T2 ->
    valid_tenv v E ->
    kinding E empty T2 knd_type.
Proof.
  introv Hc.
  assert (valid_tenv_extension v E empty) by auto.
  inversion Hc; subst; auto with kinding.
Qed.

Ltac coercible_kinding :=
  match goal with
  | |- kinding ?E _ ?T _ =>
    match goal with
    | He : valid_tenv ?v ?E,
      H : coercible ?v ?E ?Th _ |- _ =>
      match Th with
      | context[T] =>
          extract_kinding E
            (kinding_coercible_1 H He) T
      end
    | He : valid_tenv ?v ?E,
      H : coercible ?v ?E _ ?Th |- _ =>
      match Th with
      | context[T] =>
          extract_kinding E
            (kinding_coercible_2 H He) T
      end
    end
  end.

Hint Extern 1 (kinding _ _ _ _) =>
  coercible_kinding : kinding.

Lemma typing_coercible : forall v E D P t T1 T2,
    typing v E D P t T1 ->
    coercible v E T1 T2 ->
    typing v E D P t T2.
Proof.
  introv Ht Hc.
  inversion Hc; subst; eauto.
Qed.

(* *************************************************************** *)
(** Inversions *)

Lemma invert_coercible_arrow_left : forall v E T1 T2 T3 T4,
    coercible v E (typ_arrow T1 T2) (typ_arrow T3 T4) ->
    valid_tenv v E ->
    coercible v E T3 T1.
Proof.
  introv Hc He.
  inversion Hc; subst.
  - apply coercible_row.
    rewrite <- concat_empty_r with (E := E).
    apply invert_subtype_arrow_left_row
      with (T2 := T4) (T4 := T2); auto using subtype_reflexive.
  - apply coercible_full.
    rewrite <- concat_empty_r with (E := E).
    apply invert_subtype_arrow_left
      with (T2 := T2) (T4 := T4); auto.
Qed.

Lemma invert_coercible_arrow_right :
  forall v E T1 T2 T3 T4,
    coercible v E (typ_arrow T1 T2) (typ_arrow T3 T4) ->
    valid_tenv v E ->
    coercible v E T2 T4.
Proof.
  introv Hc He.
  inversion Hc; subst.
  - apply coercible_row.
    rewrite <- concat_empty_r with (E := E).
    apply invert_subtype_arrow_right_row
      with (T1 := T1) (T3 := T3); auto using subtype_reflexive.
  - apply coercible_full.
    rewrite <- concat_empty_r with (E := E).
    apply invert_subtype_arrow_right
      with (T1 := T1) (T3 := T3); auto.  
Qed.

Lemma invert_coercible_ref_covariant : forall v E T1 T2,
    coercible v E (typ_ref T1) (typ_ref T2) ->
    valid_tenv v E ->
    coercible v E T1 T2.
Proof.
  introv Hc He.
  inversion Hc; subst.
  - apply coercible_row.
    rewrite <- concat_empty_r with (E := E).
    apply invert_subtype_ref; auto using subtype_reflexive.
  - apply coercible_full.
    apply subtype_reflexive; auto.
    rewrite <- concat_empty_r with (E := E).
    apply invert_subtype_ref; auto.  
Qed.

Lemma invert_coercible_ref_contravariant : forall v E T1 T2,
    coercible v E (typ_ref T1) (typ_ref T2) ->
    valid_tenv v E ->
    coercible v E T2 T1.
Proof.
  introv Hc He.
  inversion Hc; subst.
  - apply coercible_row.
    rewrite <- concat_empty_r with (E := E).
    apply invert_subtype_ref; auto using subtype_reflexive.
  - apply coercible_full.
    apply subtype_reflexive; auto.
    rewrite <- concat_empty_r with (E := E).
    symmetry.
    apply invert_subtype_ref; auto.  
Qed.

Lemma invert_coercible_prod_left :
  forall v E T1 T2 T3 T4,
    coercible v E (typ_prod T1 T2) (typ_prod T3 T4) ->
    valid_tenv v E ->
    coercible v E T1 T3.
Proof.
  introv Hc He.
  inversion Hc; subst.
  - apply coercible_row.
    rewrite <- concat_empty_r with (E := E).
    apply invert_subtype_prod_left_row
      with (T2 := T2) (T4 := T4); auto using subtype_reflexive.
  - apply coercible_full.
    rewrite <- concat_empty_r with (E := E).
    apply invert_subtype_prod_left
      with (T2 := T2) (T4 := T4); auto.  
Qed.

Lemma invert_coercible_prod_right :
  forall v E T1 T2 T3 T4,
    coercible v E (typ_prod T1 T2) (typ_prod T3 T4) ->
    valid_tenv v E ->
    coercible v E T2 T4.
Proof.
  introv Hc He.
  inversion Hc; subst.
  - apply coercible_row.
    rewrite <- concat_empty_r with (E := E).
    apply invert_subtype_prod_right_row
      with (T1 := T1) (T3 := T3); auto using subtype_reflexive.
  - apply coercible_full.
    rewrite <- concat_empty_r with (E := E).
    apply invert_subtype_prod_right
      with (T1 := T1) (T3 := T3); auto.
Qed.

Lemma invert_coercible_variant : forall v E T1 T2,
    coercible v E (typ_variant T1) (typ_variant T2) ->
    valid_tenv v E ->
    subtype v E empty T1 T2 knd_row_all.
Proof.
  introv Hc He.
  apply subtype_coercible in Hc; auto.
  rewrite <- concat_empty_r with (E := E).
  apply invert_subtype_variant; auto.
Qed.

Lemma invert_coercible_variant_constructor :
  forall v E c T1 T2 T3 T4,
    coercible v E (typ_variant T1) (typ_variant T2) ->
    subtype v E empty
      (typ_constructor c T3)
      (typ_proj CSet.universe (CSet.singleton c) T1)
      (knd_row (CSet.singleton c)) ->
    subtype v E empty
      (typ_proj CSet.universe (CSet.singleton c) T2)
      (typ_constructor c T4)
      (knd_row (CSet.singleton c)) ->
    valid_tenv v E ->
    coercible v E T3 T4.
Proof.
  introv Hc Hs1 Hs2 He.
  inversion Hc; subst.
  - apply coercible_row.
    rewrite <- concat_empty_r with (E := E).
    apply invert_subtype_constructor_row
      with (c := c) (cs := CSet.singleton c) (T1 := T3) (T2 := T4);
      auto.
    rewrite Hs1.
    rewrite <- Hs2.
    apply subtype_proj; auto with csetdec.
    rewrite <- concat_empty_r with (E := E).
    apply invert_subtype_variant; auto using subtype_reflexive. 
  - apply coercible_full.
    rewrite <- concat_empty_r with (E := E).
    apply invert_subtype_constructor
      with (c := c) (cs := CSet.singleton c) (T1 := T3) (T2 := T4);
      auto.
    rewrite Hs1.
    rewrite <- Hs2.
    apply subtype_proj; auto with csetdec.
    rewrite <- concat_empty_r with (E := E).
    apply invert_subtype_variant; auto.
Qed.

(* *************************************************************** *)
(** Impossible inversions *)

Lemma invert_coercible_variant_arrow : forall v E T1 T2 T3,
    coercible v E (typ_variant T1) (typ_arrow T2 T3) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_variant_arrow, subtype_reflexive.
Qed.

Lemma invert_coercible_variant_ref : forall v E T1 T2,
    coercible v E (typ_variant T1) (typ_ref T2) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_variant_ref, subtype_reflexive.
Qed.

Lemma invert_coercible_variant_unit : forall v E T1,
    coercible v E (typ_variant T1) typ_unit ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_variant_unit, subtype_reflexive.
Qed.

Lemma invert_coercible_variant_prod : forall v E T1 T2 T3,
    coercible v E (typ_variant T1) (typ_prod T2 T3) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_variant_prod, subtype_reflexive.
Qed.

Lemma invert_coercible_variant_bot : forall v E T1,
    coercible v E (typ_variant T1) (typ_bot knd_type) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_variant_bot, subtype_reflexive.
Qed.

Lemma invert_coercible_arrow_variant : forall v E T1 T2 T3,
    coercible v E (typ_arrow T1 T2) (typ_variant T3) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_arrow_variant, subtype_reflexive.
Qed.

Lemma invert_coercible_arrow_ref : forall v E T1 T2 T3,
    coercible v E (typ_arrow T1 T2) (typ_ref T3) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_arrow_ref, subtype_reflexive.
Qed.

Lemma invert_coercible_arrow_unit : forall v E T1 T2,
    coercible v E (typ_arrow T1 T2) typ_unit ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_arrow_unit, subtype_reflexive.
Qed.

Lemma invert_coercible_arrow_prod : forall v E T1 T2 T3 T4,
    coercible v E (typ_arrow T1 T2) (typ_prod T3 T4) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_arrow_prod, subtype_reflexive.
Qed.

Lemma invert_coercible_arrow_bot : forall v E T1 T2,
    coercible v E (typ_arrow T1 T2) (typ_bot knd_type) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_arrow_bot, subtype_reflexive.
Qed.

Lemma invert_coercible_ref_variant : forall v E T1 T2,
    coercible v E (typ_ref T1) (typ_variant T2) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_ref_variant, subtype_reflexive.
Qed.

Lemma invert_coercible_ref_arrow : forall v E T1 T2 T3,
    coercible v E (typ_ref T1) (typ_arrow T2 T3) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_ref_arrow, subtype_reflexive.
Qed.

Lemma invert_coercible_ref_unit : forall v E T1,
    coercible v E (typ_ref T1) typ_unit ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_ref_unit, subtype_reflexive.
Qed.

Lemma invert_coercible_ref_prod : forall v E T1 T2 T3,
    coercible v E (typ_ref T1) (typ_prod T2 T3) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_ref_prod, subtype_reflexive.
Qed.

Lemma invert_coercible_ref_bot : forall v E T1,
    coercible v E (typ_ref T1) (typ_bot knd_type) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_ref_bot, subtype_reflexive.
Qed.

Lemma invert_coercible_unit_variant : forall v E T1,
    coercible v E typ_unit (typ_variant T1) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_unit_variant, subtype_reflexive.
Qed.

Lemma invert_coercible_unit_arrow : forall v E T1 T2,
    coercible v E typ_unit (typ_arrow T1 T2) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_unit_arrow, subtype_reflexive.
Qed.

Lemma invert_coercible_unit_ref : forall v E T1,
    coercible v E typ_unit (typ_ref T1) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_unit_ref, subtype_reflexive.
Qed.

Lemma invert_coercible_unit_prod : forall v E T1 T2,
    coercible v E typ_unit (typ_prod T1 T2) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_unit_prod, subtype_reflexive.
Qed.

Lemma invert_coercible_unit_bot : forall v E,
    coercible v E typ_unit (typ_bot knd_type) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_unit_bot, subtype_reflexive.
Qed.

Lemma invert_coercible_prod_variant : forall v E T1 T2 T3,
    coercible v E (typ_prod T1 T2) (typ_variant T3) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_prod_variant, subtype_reflexive.
Qed.

Lemma invert_coercible_prod_arrow : forall v E T1 T2 T3 T4,
    coercible v E (typ_prod T1 T2) (typ_arrow T3 T4) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_prod_arrow, subtype_reflexive.
Qed.

Lemma invert_coercible_prod_ref : forall v E T1 T2 T3,
    coercible v E (typ_prod T1 T2) (typ_ref T3) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_prod_ref, subtype_reflexive.
Qed.

Lemma invert_coercible_prod_unit : forall v E T1 T2,
    coercible v E (typ_prod T1 T2) typ_unit ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_prod_unit, subtype_reflexive.
Qed.

Lemma invert_coercible_prod_bot : forall v E T1 T2,
    coercible v E (typ_prod T1 T2) (typ_bot knd_type) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_prod_bot, subtype_reflexive.
Qed.

Lemma invert_coercible_top_variant : forall v E T1,
    coercible v E (typ_top knd_type) (typ_variant T1) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_top_variant, subtype_reflexive.
Qed.

Lemma invert_coercible_top_arrow : forall v E T1 T2,
    coercible v E (typ_top knd_type) (typ_arrow T1 T2) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_top_arrow, subtype_reflexive.
Qed.

Lemma invert_coercible_top_ref : forall v E T1,
    coercible v E (typ_top knd_type) (typ_ref T1) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_top_ref, subtype_reflexive.
Qed.

Lemma invert_coercible_top_unit : forall v E,
    coercible v E (typ_top knd_type) typ_unit ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_top_unit, subtype_reflexive.
Qed.

Lemma invert_coercible_top_prod : forall v E T1 T2,
    coercible v E (typ_top knd_type) (typ_prod T1 T2) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_top_prod, subtype_reflexive.
Qed.

Lemma invert_coercible_top_bot : forall v E,
    coercible v E (typ_top knd_type) (typ_bot knd_type) ->
    valid_tenv v E ->
    False.
Proof.
  introv Hc He.
  inversion Hc; subst;
    eauto using invert_subtype_top_bot, subtype_reflexive.
Qed.
