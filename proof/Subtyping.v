(************************************************
 *          Row Subtyping - Subtyping           *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import Arith.
Require Import LibLN Utilities Cofinite Disjoint Definitions
        Opening FreeVars Environments Subst Wellformedness
        Weakening Substitution Kinding.

(* ****************************************************** *)
(** Lifted versions of core equality constructors *)

Definition type_equal_or_commutative v T1 T2 cs1 cs2 :=
  type_equal_of_core
    (type_equal_core_or_commutative v T1 T2 cs1 cs2).

Definition type_equal_or_associative v T1 T2 T3 cs1 cs2 cs3 cs12 cs23 :=
  type_equal_of_core
    (type_equal_core_or_associative v T1 T2 T3 cs1 cs2 cs3 cs12 cs23).

Definition type_equal_or_bot v cs1 cs2 cs12 :=
  type_equal_of_core
    (type_equal_core_or_bot v cs1 cs2 cs12).

Definition type_equal_or_top v cs1 cs2 cs12 :=
  type_equal_of_core
    (type_equal_core_or_top v cs1 cs2 cs12).

Definition type_equal_or_proj v T cs1 cs2 cs3 cs23 :=
  type_equal_of_core
    (type_equal_core_or_proj v T cs1 cs2 cs3 cs23).

Definition type_equal_proj_id v T cs1 :=
  type_equal_of_core
    (type_equal_core_proj_id v T cs1).

Definition type_equal_proj_compose v T cs1 cs2 cs3 :=
  type_equal_of_core
    (type_equal_core_proj_compose v T cs1 cs2 cs3).

Definition type_equal_proj_or_l v T1 T2 cs1 cs2 cs3 cs12 :=
  type_equal_of_core
    (type_equal_core_proj_or_l v T1 T2 cs1 cs2 cs3 cs12).

Definition type_equal_proj_or_r v T1 T2 cs1 cs2 cs3 cs12 :=
  type_equal_of_core
    (type_equal_core_proj_or_r v T1 T2 cs1 cs2 cs3 cs12).

Definition type_equal_proj_or_both v T1 T2 cs1 cs2 cs3 cs4 cs12 cs34 :=
  type_equal_of_core
    (type_equal_core_proj_or_both v T1 T2 cs1 cs2 cs3 cs4 cs12 cs34).

Definition type_equal_meet_commutative v T1 T2 :=
  type_equal_of_core
    (type_equal_core_meet_commutative v T1 T2).

Definition type_equal_meet_associative v T1 T2 T3 :=
  type_equal_of_core
    (type_equal_core_meet_associative v T1 T2 T3).

Definition type_equal_meet_identity v T1 K :=
  type_equal_of_core
    (type_equal_core_meet_identity v T1 K).

Definition type_equal_meet_absorption v T1 T2 :=
  type_equal_of_core
    (type_equal_core_meet_absorption v T1 T2).

Definition type_equal_meet_distribution v T1 T2 T3 :=
  type_equal_of_core
    (type_equal_core_meet_distribution v T1 T2 T3).

Definition type_equal_join_commutative v T1 T2 :=
  type_equal_of_core
    (type_equal_core_join_commutative v T1 T2).

Definition type_equal_join_associative v T1 T2 T3 :=
  type_equal_of_core
    (type_equal_core_join_associative v T1 T2 T3).

Definition type_equal_join_identity v T1 K :=
  type_equal_of_core
    (type_equal_core_join_identity v T1 K).

Definition type_equal_join_absorption v T1 T2 :=
  type_equal_of_core
    (type_equal_core_join_absorption v T1 T2).

Definition type_equal_join_distribution v T1 T2 T3 :=
  type_equal_of_core
    (type_equal_core_join_distribution v T1 T2 T3).

Definition type_equal_or_meet v T1 T2 T3 T4 cs1 cs2 :=
  type_equal_of_core
    (type_equal_core_or_meet v T1 T2 T3 T4 cs1 cs2).

Definition type_equal_or_join v T1 T2 T3 T4 cs1 cs2 :=
  type_equal_of_core
    (type_equal_core_or_join v T1 T2 T3 T4 cs1 cs2).

Definition type_equal_proj_meet v T1 T2 cs1 cs2 :=
  type_equal_of_core
    (type_equal_core_proj_meet v T1 T2 cs1 cs2).

Definition type_equal_proj_join v T1 T2 cs1 cs2 :=
  type_equal_of_core
    (type_equal_core_proj_join v T1 T2 cs1 cs2).

Definition type_equal_variant_meet v T1 T2 :=
  type_equal_of_core
    (type_equal_core_variant_meet v T1 T2).

Definition type_equal_variant_join v T1 T2 :=
  type_equal_of_core
    (type_equal_core_variant_join v T1 T2).

Definition type_equal_constructor_meet c T1 T2 :=
  type_equal_of_core
    (type_equal_core_constructor_meet c T1 T2).

Definition type_equal_constructor_join c T1 T2 :=
  type_equal_of_core
    (type_equal_core_constructor_join c T1 T2).

Definition type_equal_arrow_meet T1 T2 T3 T4 :=
  type_equal_of_core
    (type_equal_core_arrow_meet T1 T2 T3 T4).

Definition type_equal_arrow_join T1 T2 T3 T4 :=
  type_equal_of_core
    (type_equal_core_arrow_join T1 T2 T3 T4).

Definition type_equal_prod_meet T1 T2 T3 T4 :=
  type_equal_of_core
    (type_equal_core_prod_meet T1 T2 T3 T4).

Definition type_equal_prod_join T1 T2 T3 T4 :=
  type_equal_of_core
    (type_equal_core_prod_join T1 T2 T3 T4).

Lemma type_equal_constructor_nonrec :
  forall v E1 E2 c T1 T1' cs,
    type_equal' v (E1 & E2) empty nil nil knd_type T1 T1' ->
    cs = CSet.singleton c ->
    type_equal' v E1 E2 nil nil (knd_row cs)
      (typ_constructor c T1) (typ_constructor c T1').
Proof.
  introv Hte Heq.
  apply type_equal_constructor; try assumption.
  apply type_equal_weakening_eqn_nils; assumption.
Qed.

Lemma type_equal_or_nonrec :
  forall v E1 E2 T1 T1' T2 T2' cs1 cs2 cs12,
    type_equal' v E1 E2 nil nil (knd_row cs1) T1 T1' ->
    type_equal' v E1 E2 nil nil (knd_row cs2) T2 T2' ->
    CSet.Disjoint cs1 cs2 ->
    cs12 = CSet.union cs1 cs2 ->
    type_equal' v E1 E2 nil nil (knd_row cs12)
       (typ_or cs1 cs2 T1 T2) (typ_or cs1 cs2 T1' T2').
Proof.
  introv Hte1 Hte2 Hd Heq.
  apply type_equal_or; try assumption;
    apply type_equal_weakening_eqn_nils; assumption.
Qed.

Lemma type_equal_proj_nonrec :
  forall v E1 E2 T1 T1' cs1 cs2,
    type_equal' v E1 E2 nil nil (knd_row cs1) T1 T1' ->
    CSet.Subset cs2 cs1 ->
    CSet.Nonempty cs2 ->
    type_equal' v E1 E2 nil nil (knd_row cs2)
      (typ_proj cs1 cs2 T1) (typ_proj cs1 cs2 T1').
Proof.
  introv Hte Hs Hn.
  apply type_equal_proj; try assumption.
  apply type_equal_weakening_eqn_nils; assumption.
Qed.

Lemma type_equal_variant_nonrec : forall v E1 E2 T1 T1',
    type_equal' v (E1 & E2) empty nil nil knd_row_all T1 T1' ->
    type_equal' v E1 E2 nil nil knd_type
      (typ_variant T1) (typ_variant T1').
Proof.
  introv Hte.
  apply type_equal_variant.
  apply type_equal_weakening_eqn_nils; assumption.
Qed.

Lemma type_equal_arrow_nonrec : forall v E1 E2 T1 T1' T2 T2',
    type_equal' v (E1 & E2) empty nil nil knd_type T1 T1' ->
    type_equal' v (E1 & E2) empty nil nil knd_type T2 T2' ->
    type_equal' v E1 E2 nil nil knd_type
      (typ_arrow T1 T2) (typ_arrow T1' T2').
Proof.
  introv Hte1 Hte2.
  apply type_equal_arrow;
    apply type_equal_weakening_eqn_nils; assumption.
Qed.

Lemma type_equal_prod_nonrec : forall v E1 E2 T1 T1' T2 T2',
    type_equal' v (E1 & E2) empty nil nil knd_type T1 T1' ->
    type_equal' v (E1 & E2) empty nil nil knd_type T2 T2' ->
    type_equal' v E1 E2 nil nil knd_type
      (typ_prod T1 T2) (typ_prod T1' T2').
Proof.
  introv Hte1 Hte2.
  apply type_equal_prod;
    apply type_equal_weakening_eqn_nils; assumption.
Qed.

Lemma type_equal_ref_nonrec : forall v E1 E2 T1 T1',
    type_equal' v (E1 & E2) empty nil nil knd_type T1 T1' ->
    type_equal' v E1 E2 nil nil knd_type
      (typ_ref T1) (typ_ref T1').
Proof.
  introv Hte.
  apply type_equal_ref.
  apply type_equal_weakening_eqn_nils; assumption.
Qed.

Lemma type_equal_meet_nonrec : forall v E1 E2 T1 T1' T2 T2' K,
    type_equal' v E1 E2 nil nil K T1 T1' ->
    type_equal' v E1 E2 nil nil K T2 T2' -> 
    type_equal' v E1 E2 nil nil K
      (typ_meet T1 T2) (typ_meet T1' T2').
Proof.
  introv Hte1 Hte2.
  apply type_equal_meet;
    apply type_equal_weakening_eqn_nils; assumption.
Qed.
  
Lemma type_equal_join_nonrec : forall v E1 E2 T1 T1' T2 T2' K,
    type_equal' v E1 E2 nil nil K T1 T1' ->
    type_equal' v E1 E2 nil nil K T2 T2' ->
    type_equal' v E1 E2 nil nil K
      (typ_join T1 T2) (typ_join T1' T2').
Proof.
  introv Hte1 Hte2.
  apply type_equal_join;
    apply type_equal_weakening_eqn_nils; assumption.
Qed.

Lemma type_equal_symmetric_nonrec : forall v E1 E2 T1 T2 K,
    type_equal' v E1 E2 nil nil K T1 T2 ->
    type_equal' v E1 E2 nil nil K T2 T1.
Proof.
  introv Hte.
  apply type_equal_symmetric.
  apply type_equal_weakening_eqn_nils; assumption.
Qed.

Lemma type_equal_transitive_nonrec : forall v E1 E2 T1 T2 T3 K,
    type_equal' v E1 E2 nil nil K T1 T2 ->
    type_equal' v E1 E2 nil nil K T2 T3 ->
    type_equal' v E1 E2 nil nil K T1 T3.
Proof.
  introv Hte1 Hte2.
  apply type_equal_transitive with T2;
    apply type_equal_weakening_eqn_nils; assumption.
Qed.

(* ****************************************************** *)
(** Type equality as a relation *)

Add Parametric Relation
    (v : version) (E1 : tenv) (E2 : tenv) (K : knd)
  : typ (type_equal' v E1 E2 nil nil K)
      symmetry proved by
        (fun T1 T2 =>
           @type_equal_symmetric_nonrec v E1 E2 T1 T2 K)
      transitivity proved by
        (fun T1 T2 T3 =>
           @type_equal_transitive_nonrec v E1 E2 T1 T2 T3 K)
      as type_equal_rel.
     
Hint Extern 1 (Morphisms.ProperProxy
                 (type_equal' _ _ _ _ _ _) ?T) =>
    apply type_equal_reflexive; eauto with kinding wellformed
  : typeclass_instances.

Tactic Notation
  "subst_equal" constr(T1) :=
  match goal with
  | H : type_equal ?v ?E1 ?E2 nil nil T1 ?T2 ?K |- _ =>
      setoid_rewrite H        
  | H : type_equal ?v ?E1 ?E2 nil nil ?T2 T1 ?K |- _ =>
      setoid_rewrite <- H
  | H : subtype ?v ?E1 ?E2 nil nil T1 ?T2 ?K |- _ =>
      let H' := fresh "H" in
      pose proof H as H';
      unfold subtype in H';
      setoid_rewrite H';
      clear H'
  end.

Tactic Notation
  "subst_equal" constr(T1) "at" integer(P) :=
  match goal with
  | H : type_equal ?v ?E1 ?E2 nil nil T1 ?T2 ?K |- _ =>
      setoid_rewrite H at P
  | H : type_equal ?v ?E1 ?E2 nil nil ?T2 T1 ?K |- _ =>
      setoid_rewrite <- H at P
  | H : subtype ?v ?E1 ?E2 T1 nil nil ?T2 ?K |- _ =>
      let H' := fresh "H" in
      pose proof H as H';
      unfold subtype in H';
      setoid_rewrite H' at P;
      clear H'
  end.

Tactic Notation
  "subst_equal" "<-" constr(T1) :=
  match goal with
  | H : type_equal ?v ?E1 ?E2 nil nil T1 ?T2 ?K |- _ =>
      setoid_rewrite <- H        
  | H : type_equal ?v ?E1 ?E2 nil nil ?T2 T1 ?K |- _ =>
      setoid_rewrite H
  | H : subtype ?v ?E1 ?E2 nil nil T1 ?T2 ?K |- _ =>
      let H' := fresh "H" in
      pose proof H as H';
      unfold subtype in H';
      setoid_rewrite <- H';
      clear H'
  end.

Tactic Notation
  "subst_equal" "<-" constr(T1) "at" integer(P) :=
  match goal with
  | H : type_equal ?v ?E1 ?E2 nil nil T1 ?T2 ?K |- _ =>
      setoid_rewrite <- H at P
  | H : type_equal ?v ?E1 ?E2 ?T2 nil nil T1 ?K |- _ =>
      setoid_rewrite H at P
  | H : subtype ?v ?E1 ?E2 nil nil T1 ?T2 ?K |- _ =>
      let H' := fresh "H" in
      pose proof H as H';
      unfold subtype in H';
      setoid_rewrite <- H' at P;
      clear H'
  end.

Tactic Notation
   "treflexivity" :=
  apply type_equal_reflexive; auto with kinding wellformed.

(* ****************************************************** *)
(** Type constructors as equality morphisms *)

Instance typ_constructor_eq_morph
  (v : version) (E1 : tenv) (E2 : tenv) (c : nat)
  : Morphisms.Proper
      (type_equal' v (E1 & E2) empty nil nil knd_type ==>
           type_equal' v E1 E2 nil nil
             (knd_row (CSet.singleton c)))
      (typ_constructor c) | 3
  := { }.
  unfold Morphisms.respectful.
  auto using type_equal_constructor_nonrec.
Qed.

Instance typ_or_eq_morph
  (v : version) (E1 : tenv) (E2 : tenv) (cs1  : cset) (cs2 : cset)
  `{ Hd : CSet.Disjoint cs1 cs2 }
  : Morphisms.Proper
      (type_equal' v E1 E2 nil nil (knd_row cs1) ==>
         type_equal' v E1 E2 nil nil (knd_row cs2) ==>
           type_equal' v E1 E2 nil nil
             (knd_row (CSet.union cs1 cs2)))
      (typ_or cs1 cs2) | 3
  := { }.
  unfold Morphisms.respectful.
  auto using type_equal_or_nonrec.
Qed.

Instance typ_proj_eq_morph
  (v : version) (E1 : tenv) (E2 : tenv) (cs1  : cset) (cs2 : cset)
  `{ Hs : CSet.Subset cs2 cs1 }
  `{ Hs : CSet.Nonempty cs2 }
  : Morphisms.Proper
      (type_equal' v E1 E2 nil nil (knd_row cs1) ==>
           type_equal' v E1 E2 nil nil (knd_row cs2))
      (typ_proj cs1 cs2) | 3
  := { }.
  unfold Morphisms.respectful.
  auto using type_equal_proj_nonrec.
Qed.

Instance typ_variant_eq_morph
  (v : version) (E1 : tenv) (E2 : tenv)
  : Morphisms.Proper
      (type_equal' v (E1 & E2) empty nil nil knd_row_all ==>
         type_equal' v E1 E2 nil nil knd_type)
      typ_variant | 3
  := { }.
  unfold Morphisms.respectful.
  auto using type_equal_variant_nonrec.
Qed.

Instance typ_arrow_eq_morph
  (v : version) (E1 : tenv) (E2 : tenv)
  : Morphisms.Proper
      (type_equal' v (E1 & E2) empty nil nil knd_type ==>
         type_equal' v (E1 & E2) empty nil nil knd_type ==>
           type_equal' v E1 E2 nil nil knd_type)
      typ_arrow | 3
  := { }.
  unfold Morphisms.respectful.
  auto using type_equal_arrow_nonrec.
Qed.

Instance typ_ref_eq_morph
  (v : version) (E1 : tenv) (E2 : tenv)
  : Morphisms.Proper
      (type_equal' v (E1 & E2) empty nil nil knd_type ==>
         type_equal' v E1 E2 nil nil knd_type)
      typ_ref | 3
  := { }.
  unfold Morphisms.respectful.
  auto using type_equal_ref_nonrec.
Qed.

Instance typ_prod_eq_morph
  (v : version) (E1 : tenv) (E2 : tenv)
  : Morphisms.Proper
      (type_equal' v (E1 & E2) empty nil nil knd_type ==>
         type_equal' v (E1 & E2) empty nil nil knd_type ==>
           type_equal' v E1 E2 nil nil knd_type)
      typ_prod | 3
  := { }.
  unfold Morphisms.respectful.
  auto using type_equal_prod_nonrec.
Qed.

Instance typ_meet_eq_morph
  (v : version) (E1 : tenv) (E2 : tenv) (K : knd)
  : Morphisms.Proper
      (type_equal' v E1 E2 nil nil K ==>
         type_equal' v E1 E2 nil nil K ==>
           type_equal' v E1 E2 nil nil K)
      typ_meet | 3
  := { }.
  unfold Morphisms.respectful.
  auto using type_equal_meet_nonrec.
Qed.

Instance typ_join_eq_morph
  (v : version) (E1 : tenv) (E2 : tenv) (K : knd)
  : Morphisms.Proper
      (type_equal' v E1 E2 nil nil K ==>
         type_equal' v E1 E2 nil nil K ==>
           type_equal' v E1 E2 nil nil K)
      typ_join | 3
  := { }.
  unfold Morphisms.respectful.
  auto using type_equal_join_nonrec.
Qed.

(* ***************************************************** *)
(** Idempotence of join and meet *)

Lemma type_equal_join_idempotent_kind : forall v E1 E2 T K,
    kind K ->
    kinding E1 E2 T K ->
    type_equal v E1 E2 nil nil T (typ_join T T) K.
Proof.
  introv Hknd Hk.
  rewrite <- type_equal_join_absorption
    with (T1 := T) (T2 := typ_top K) at 1 by auto.
  rewrite type_equal_meet_identity with (T1 := T) by auto.
  treflexivity.
Qed.

Lemma type_equal_join_idempotent : forall v E1 E2 T K,
    kinding E1 E2 T K ->
    type_environment E1 ->
    type_environment_extension E1 E2 ->
    type_equal v E1 E2 nil nil T (typ_join T T) K.
Proof.
  introv Hk He1 He2.
  auto using type_equal_join_idempotent_kind with wellformed.
Qed.

Lemma type_equal_meet_idempotent_kind : forall v E1 E2 T K,
    kind K ->
    kinding E1 E2 T K ->
    type_equal v E1 E2 nil nil T (typ_meet T T) K.
Proof.
  introv Hknd Hk.
  rewrite <- type_equal_meet_absorption
    with (T1 := T) (T2 := typ_bot K) at 1 by auto.
  rewrite type_equal_join_identity with (T1 := T) by auto.
  treflexivity.
Qed.

Lemma type_equal_meet_idempotent : forall v E1 E2 T K,
    kinding E1 E2 T K ->
    type_environment E1 ->
    type_environment_extension E1 E2 ->
    type_equal v E1 E2 nil nil T (typ_meet T T) K.
Proof.
  introv Hk He1 He2.
  auto using type_equal_meet_idempotent_kind with wellformed.
Qed.

(* ****************************************************** *)
(** Annihilating elements *)

Lemma type_equal_meet_annihilation_l_kind : forall v E1 E2 T K,
    kind K ->
    kinding E1 E2 T K ->
    type_equal v E1 E2 nil nil
      (typ_meet (typ_bot K) T) (typ_bot K) K.
Proof.
  introv Hknd Hk.
  rewrite <- type_equal_join_identity with (T1 := T) by auto.
  rewrite type_equal_join_commutative by auto.
  rewrite type_equal_meet_absorption by auto.
  treflexivity.
Qed.

Lemma type_equal_meet_annihilation_r_kind : forall v E1 E2 T K,
    kind K ->
    kinding E1 E2 T K ->
    type_equal v E1 E2 nil nil
      (typ_meet T (typ_bot K)) (typ_bot K) K.
Proof.
  introv Hknd Hk.
  rewrite type_equal_meet_commutative by auto.
  rewrite type_equal_meet_annihilation_l_kind by auto.
  treflexivity.
Qed.

Lemma type_equal_meet_annihilation_l : forall v E1 E2 T K,
    kinding E1 E2 T K ->
    type_environment E1 ->
    type_environment_extension E1 E2 ->
    type_equal v E1 E2 nil nil
      (typ_meet (typ_bot K) T) (typ_bot K) K.
Proof.
  introv Hk He1 He2.
  auto using type_equal_meet_annihilation_l_kind
    with wellformed.
Qed.

Lemma type_equal_meet_annihilation_r : forall v E1 E2 T K,
    kinding E1 E2 T K ->
    type_environment E1 ->
    type_environment_extension E1 E2 ->
    type_equal v E1 E2 nil nil
      (typ_meet T (typ_bot K)) (typ_bot K) K.
Proof.
  introv Hk He1 He2.
  auto using type_equal_meet_annihilation_r_kind
    with wellformed.
Qed.

Lemma type_equal_join_annihilation_l_kind : forall v E1 E2 T K,
    kind K ->
    kinding E1 E2 T K ->
    type_equal v E1 E2 nil nil
      (typ_join (typ_top K) T) (typ_top K) K.
Proof.
  introv Hknd Hk.
  rewrite <- type_equal_meet_identity with (T1 := T) by auto.
  rewrite type_equal_meet_commutative by auto.
  rewrite type_equal_join_absorption by auto.
  treflexivity.
Qed.

Lemma type_equal_join_annihilation_r_kind : forall v E1 E2 T K,
    kind K ->
    kinding E1 E2 T K ->
    type_equal v E1 E2 nil nil
      (typ_join T (typ_top K)) (typ_top K) K.
Proof.
  introv Hknd Hk.
  rewrite type_equal_join_commutative by auto.
  rewrite type_equal_join_annihilation_l_kind by auto.
  treflexivity.
Qed.

Lemma type_equal_join_annihilation_l : forall v E1 E2 T K,
    kinding E1 E2 T K ->
    type_environment E1 ->
    type_environment_extension E1 E2 ->
    type_equal v E1 E2 nil nil
      (typ_join (typ_top K) T) (typ_top K) K.
Proof.
  introv Hk He1 He2.
  auto using type_equal_join_annihilation_l_kind
    with wellformed.
Qed.

Lemma type_equal_join_annihilation_r : forall v E1 E2 T K,
    kinding E1 E2 T K ->
    type_environment E1 ->
    type_environment_extension E1 E2 ->
    type_equal v E1 E2 nil nil
      (typ_join T (typ_top K)) (typ_top K) K.
Proof.
  introv Hk He1 He2.
  auto using type_equal_join_annihilation_r_kind
    with wellformed.
Qed.

(* ****************************************************** *)
(** Subtyping is a partial order *)

Lemma subtype_refl_kinding : forall v E1 E2 T K,
    kind K ->
    kinding E1 E2 T K ->
    subtype v E1 E2 nil nil T T K.
Proof.
  introv Hknd Hk.
  unfold subtype.
  auto using type_equal_meet_idempotent_kind.
Qed.

Lemma subtype_refl : forall v E1 E2 T K,
    kinding E1 E2 T K ->
    type_environment E1 ->
    type_environment_extension E1 E2 ->
    subtype v E1 E2 nil nil T T K.
Proof.
  introv Hk He.
  unfold subtype.
  auto using type_equal_meet_idempotent.
Qed.

Lemma subtype_reflexive_kinding : forall v E1 E2 T1 T2 K,
    type_equal v E1 E2 nil nil T1 T2 K ->
    kind K ->
    kinding E1 E2 T1 K ->
    subtype v E1 E2 nil nil T1 T2 K.
Proof.
  introv Hte Hknd Hk.
  unfold subtype.
  rewrite <- Hte.
  auto using type_equal_meet_idempotent_kind.
Qed.

Lemma subtype_reflexive : forall v E1 E2 T1 T2 K,
    type_equal v E1 E2 nil nil T1 T2 K ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    subtype v E1 E2 nil nil T1 T2 K.
Proof.
  introv Hte He1 He2.
  auto using subtype_reflexive_kinding
    with kinding wellformed.
Qed.

Lemma subtype_transitive_kinding : forall v E1 E2 T1 T2 T3 K,
    subtype v E1 E2 nil nil T1 T2 K ->
    subtype v E1 E2 nil nil T2 T3 K ->
    kinding E1 E2 T1 K ->
    kinding E1 E2 T2 K ->
    kinding E1 E2 T3 K ->
    subtype v E1 E2 nil nil T1 T3 K.
Proof.
  introv Hs1 Hs2 Hk1 Hk2 Hk3.
  unfold subtype in *.
  rewrite Hs1 at 1.
  rewrite Hs2 at 1.
  rewrite type_equal_meet_associative by auto.
  rewrite <- Hs1.
  treflexivity.
Qed.

Lemma subtype_transitive : forall v E1 E2 T1 T2 T3 K,
    subtype v E1 E2 nil nil T1 T2 K ->
    subtype v E1 E2 nil nil T2 T3 K ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    subtype v E1 E2 nil nil T1 T3 K.
Proof.
  introv Hs1 Hs2 He1 He2.
  eauto using subtype_transitive_kinding with kinding.
Qed.

Lemma subtype_antisymmetric_kinding : forall v E1 E2 T1 T2 K,
    subtype v E1 E2 nil nil T1 T2 K ->
    subtype v E1 E2 nil nil T2 T1 K ->
    kinding E1 E2 T1 K ->
    kinding E1 E2 T2 K ->
    type_equal v E1 E2 nil nil T1 T2 K.
Proof.
  introv Hs1 Hs2 Hk1 Hk2.
  unfold subtype in *.
  rewrite Hs1.
  rewrite type_equal_meet_commutative by auto.
  rewrite <- Hs2.
  treflexivity.
Qed.

Lemma subtype_antisymmetric : forall v E1 E2 T1 T2 K,
    subtype v E1 E2 nil nil T1 T2 K ->
    subtype v E1 E2 nil nil T2 T1 K ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    type_equal v E1 E2 nil nil T1 T2 K.
Proof.
  introv Hs1 Hs2 He1 He2.
  auto using subtype_antisymmetric_kinding with kinding.
Qed.

(* *************************************************************** *)
(** Typing lattice is bounded *)

Lemma subtype_top_kind : forall v E1 E2 T K,
    kind K ->
    kinding E1 E2 T K ->
    subtype v E1 E2 nil nil T (typ_top K) K.
Proof.
  introv Hknd Hk.
  unfold subtype.
  rewrite type_equal_meet_identity by auto.
  treflexivity.
Qed.

Lemma subtype_top : forall v E1 E2 T K,
    kinding E1 E2 T K ->
    type_environment E1 ->
    type_environment_extension E1 E2 ->
    subtype v E1 E2 nil nil T (typ_top K) K.
Proof.
  introv Hk He1 He2.
  auto using subtype_top_kind with wellformed.
Qed.

Lemma subtype_bot_kind : forall v E1 E2 T K,
    kind K ->
    kinding E1 E2 T K ->
    subtype v E1 E2 nil nil (typ_bot K) T K.
Proof.
  introv Hknd Hk.
  unfold subtype.
  rewrite <- type_equal_meet_absorption
    with (T1 := typ_bot K) (T2 := T) at 1 by auto.
  rewrite type_equal_join_commutative by auto.
  rewrite type_equal_join_identity by auto.
  treflexivity.
Qed.

Lemma subtype_bot : forall v E1 E2 T K,
    kinding E1 E2 T K ->
    type_environment E1 ->
    type_environment_extension E1 E2 ->
    subtype v E1 E2 nil nil (typ_bot K) T K.
Proof.
  introv Hk He1 He2.
  auto using subtype_bot_kind with wellformed.
Qed.

(* ****************************************************** *)
(** Conversion to the dual representation of subtyping *)

Lemma subtype_dual_kinding : forall v E1 E2 T1 T2 K,
    kinding E1 E2 T1 K ->
    kinding E1 E2 T2 K ->
    subtype v E1 E2 nil nil T1 T2 K
    <-> type_equal v E1 E2 nil nil T2 (typ_join T2 T1) K.
Proof.
  introv Hk1 Hk2.
  unfold subtype.
  split.
  - introv Hs.
    rewrite <- type_equal_join_absorption
      with (T1 := T2) (T2 := T1) at 1 by auto.
    rewrite type_equal_meet_commutative by auto.
    rewrite <- Hs.
    treflexivity.
  - introv Hte.
    rewrite <- type_equal_meet_absorption
      with (T1 := T1) (T2 := T2) at 1 by auto.
    rewrite type_equal_join_commutative by auto.
    rewrite <- Hte.
    treflexivity.
Qed.

Lemma subtype_dual : forall v E1 E2 T1 T2 K,
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    subtype v E1 E2 nil nil T1 T2 K
    <-> type_equal v E1 E2 nil nil T2 (typ_join T2 T1) K.
Proof.
  introv He1 He2.
  split.
  - introv Hs.
    rewrite <- subtype_dual_kinding; auto with kinding.
  - introv Hte.
    rewrite subtype_dual_kinding; auto with kinding.
Qed.

(* *************************************************************** *)
(** Congruence of subtyping *)

Lemma subtype_constructor : forall E1 E2 c T1 T1' cs,
    subtype version_full_subtyping (E1 & E2) empty nil nil
      T1 T1' knd_type ->
    cs = CSet.singleton c ->
    valid_tenv version_full_subtyping E1 ->
    valid_tenv_extension version_full_subtyping E1 E2 ->
    subtype version_full_subtyping E1 E2 nil nil
      (typ_constructor c T1) (typ_constructor c T1') (knd_row cs).
Proof.
  introv Hs Heq He1 He2; subst.
  unfold subtype in *.
  rewrite Hs at 1.
  rewrite type_equal_constructor_meet; auto with kinding.
Qed.

Lemma subtype_or : forall v E1 E2 T1 T1' T2 T2' cs1 cs2 cs,
    subtype v E1 E2 nil nil T1 T1' (knd_row cs1) ->
    subtype v E1 E2 nil nil T2 T2' (knd_row cs2) ->
    CSet.Disjoint cs1 cs2 ->
    cs = CSet.union cs1 cs2 ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    subtype v E1 E2 nil nil (typ_or cs1 cs2 T1 T2)
      (typ_or cs1 cs2 T1' T2') (knd_row cs).
Proof.
  introv Hs1 Hs2 Hd Heq He1 He2; subst.
  unfold subtype in *.
  rewrite Hs1 at 1.
  rewrite Hs2 at 1.
  rewrite type_equal_or_meet by auto with kinding.
  treflexivity.
Qed.

Lemma subtype_proj : forall v E1 E2 T1 T1' cs1 cs2,
    subtype v E1 E2 nil nil T1 T1' (knd_row cs1) ->
    CSet.Subset cs2 cs1 ->
    CSet.Nonempty cs2 ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    subtype v E1 E2 nil nil (typ_proj cs1 cs2 T1)
      (typ_proj cs1 cs2 T1') (knd_row cs2).
Proof.
  introv Hs Hsb Hn He1 He2.
  unfold subtype in *.
  rewrite Hs at 1.
  rewrite type_equal_proj_meet by auto with kinding.
  treflexivity.
Qed.

Lemma subtype_variant : forall v E1 E2 T1 T1',
    subtype v (E1 & E2) empty nil nil T1 T1' knd_row_all ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    subtype v E1 E2 nil nil (typ_variant T1)
      (typ_variant T1') knd_type.
Proof.
  introv Hs He1 He2.
  unfold subtype in *.
  rewrite Hs at 1.
  rewrite type_equal_variant_meet by auto with kinding.
  treflexivity.
Qed.

Lemma subtype_arrow : forall E1 E2 T1 T1' T2 T2',
    subtype version_full_subtyping (E1 & E2) empty nil nil
      T1' T1 knd_type ->
    subtype version_full_subtyping (E1 & E2) empty nil nil
      T2 T2' knd_type ->
    valid_tenv version_full_subtyping E1 ->
    valid_tenv_extension version_full_subtyping E1 E2 ->
    subtype version_full_subtyping E1 E2 nil nil
      (typ_arrow T1 T2) (typ_arrow T1' T2') knd_type.
Proof.
  introv Hs1 Hs2 He1 He2.
  rewrite subtype_dual in Hs1; auto using valid_tenv_extend.
  unfold subtype in *.
  rewrite Hs1 at 1.
  rewrite Hs2 at 1.
  rewrite type_equal_arrow_meet by auto with kinding.
  treflexivity.
Qed.

Lemma subtype_prod : forall E1 E2 T1 T1' T2 T2',
    subtype version_full_subtyping (E1 & E2) empty nil nil
      T1 T1' knd_type ->
    subtype version_full_subtyping (E1 & E2) empty nil nil
      T2 T2' knd_type ->
    valid_tenv version_full_subtyping E1 ->
    valid_tenv_extension version_full_subtyping E1 E2 ->
    subtype version_full_subtyping E1 E2 nil nil
      (typ_prod T1 T2) (typ_prod T1' T2') knd_type.
Proof.
  introv Hs1 Hs2 He1 He2.
  unfold subtype in *.
  rewrite Hs1 at 1.
  rewrite Hs2 at 1.
  rewrite type_equal_prod_meet by auto with kinding.
  treflexivity.
Qed.

Lemma subtype_meet : forall v E1 E2 T1 T1' T2 T2' K,
    subtype v E1 E2 nil nil T1 T1' K ->
    subtype v E1 E2 nil nil T2 T2' K ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    subtype v E1 E2 nil nil (typ_meet T1 T2) (typ_meet T1' T2') K.
Proof.
  introv Hs1 Hs2 He1 He2.
  unfold subtype in *.
  rewrite Hs1 at 1.
  rewrite Hs2 at 1.
  rewrite type_equal_meet_associative
    by auto with kinding.
  rewrite type_equal_meet_commutative with (T1 := T1)
    by auto with kinding.
  rewrite <- type_equal_meet_associative with (T3 := T2)
    by auto with kinding.
  rewrite type_equal_meet_commutative with (T1 := T1')
    by auto with kinding.
  rewrite <- type_equal_meet_associative
    by auto with kinding.
  treflexivity.
Qed.

Lemma subtype_join : forall v E1 E2 T1 T1' T2 T2' K,
    subtype v E1 E2 nil nil T1 T1' K ->
    subtype v E1 E2 nil nil T2 T2' K ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    subtype v E1 E2 nil nil (typ_join T1 T2) (typ_join T1' T2') K.
Proof.
  introv Hs1 Hs2 He1 He2.
  rewrite subtype_dual in Hs1, Hs2; auto.
  rewrite subtype_dual; auto.
  rewrite Hs1 at 1.
  rewrite Hs2 at 1.
  rewrite type_equal_join_associative
    by auto with kinding.
  rewrite type_equal_join_commutative with (T1 := T1')
    by auto with kinding.
  rewrite <- type_equal_join_associative with (T3 := T2')
    by auto with kinding.
  rewrite type_equal_join_commutative with (T1 := T1)
    by auto with kinding.
  rewrite <- type_equal_join_associative
    by auto with kinding.
  treflexivity.
Qed.

(* ****************************************************** *)
(** Subtyping as a relation *)

Existing Class valid_tenv.
Existing Class valid_tenv_extension.
Existing Instance valid_tenv_extend.
Existing Instance valid_tenv_extension_empty.

Add Parametric Relation
    (v : version) (E1 : tenv) (E2 : tenv) (K : knd)
    `{ He1 : valid_tenv v E1 } `{ He2 : valid_tenv_extension v E1 E2 }
  : typ (subtype' v E1 E2 nil nil K)
      transitivity proved by
        (fun T1 T2 T3 H1 H2 =>
           @subtype_transitive v E1 E2 T1 T2 T3 K H1 H2 He1 He2)
      as subtype_rel.
     
Hint Extern 1
  (Morphisms.ProperProxy (subtype' ?v ?E1 ?E2 ?Q1 ?Q2 ?K) ?T) =>
    apply subtype_refl; auto with kinding wellformed
  : typeclass_instances.

Instance subrelation_equal_subtype
  (v : version) (E1 : tenv) (E2 : tenv) (K : knd)
  `{ He1 : valid_tenv v E1 } `{ He2 : valid_tenv_extension v E1 E2 }
  : subrelation (type_equal' v E1 E2 nil nil K)
                (subtype' v E1 E2 nil nil K) | 4
  := { }.
  eauto using subtype_reflexive with kinding.
Qed.

Instance subrelation_equal_subtype_flip
  (v : version) (E1 : tenv) (E2 : tenv) (K : knd)
  `{ Hv : valid_tenv v E1 } `{ Hv : valid_tenv_extension v E1 E2 }
  : subrelation (type_equal' v E1 E2 nil nil K)
                (Basics.flip (subtype' v E1 E2 nil nil K)) | 4
  := { }.
  introv Hte.
  symmetry in Hte.
  unfold Basics.flip.
  eauto using subtype_reflexive with kinding.
Qed.

(* Increase priority of subrelations to speed up resolution *)
Hint Extern 4 (@Morphisms.Proper _ _ (subtype' _ _ _ _ _ _)) =>
  Morphisms.proper_subrelation : typeclass_instances.

Hint Extern 4 (@Morphisms.Proper _ _ (subtype' _ _ _ _ _ _ _)) =>
  Morphisms.proper_subrelation : typeclass_instances.

Tactic Notation
  "subst_subtype" constr(T1) :=
  match goal with
  | H : subtype ?v ?E1 ?E2 nil nil T1 ?T2 ?K |- _ =>
      setoid_rewrite H        
  | H : subtype ?v ?E1 ?E2 nil nil ?T2 T1 ?K |- _ =>
      setoid_rewrite <- H
  end.

Tactic Notation
  "subst_subtype" constr(T1) "at" integer(P) :=
  match goal with
  | H : subtype ?v ?E1 ?E2 nil nil T1 ?T2 ?K |- _ =>
      setoid_rewrite H at P
  | H : subtype ?v ?E1 ?E2 nil nil ?T2 T1 ?K |- _ =>
      setoid_rewrite <- H at P
  end.

Tactic Notation
  "subst_subtype" "<-" constr(T1) :=
  match goal with
  | H : subtype ?v ?E1 ?E2 nil nil T1 ?T2 ?K |- _ =>
      setoid_rewrite <- H        
  | H : subtype ?v ?E1 ?E2 nil nil ?T2 T1 ?K |- _ =>
      setoid_rewrite H
  end.

Tactic Notation
  "subst_subtype" "<-" constr(T1) "at" integer(P) :=
  match goal with
  | H : subtype ?v ?E1 ?E2 nil nil T1 ?T2 ?K |- _ =>
      setoid_rewrite <- H at P
  | H : subtype ?v ?E1 ?E2 nil nil ?T2 T1 ?K |- _ =>
      setoid_rewrite H at P
  end.

Tactic Notation
   "sreflexivity" :=
  apply subtype_refl; auto with kinding wellformed.

(* ****************************************************** *)
(** Type constructors as subtyping morphisms *)

Instance typ_constructor_sub_morph_full
  (E1 : tenv) (E2 : tenv) (c : nat)
  `{ He1 : valid_tenv version_full_subtyping E1 }
  `{ He2 : valid_tenv_extension version_full_subtyping E1 E2 }
  : Morphisms.Proper
      (subtype' version_full_subtyping
         (E1 & E2) empty nil nil knd_type ++>
           subtype' version_full_subtyping
              E1 E2 nil nil (knd_row (CSet.singleton c)))
      (typ_constructor c) | 4
  := { }.
  unfold Morphisms.respectful.
  auto using subtype_constructor.
Qed.

Instance typ_constructor_sub_morph
  (v : version) (E1 : tenv) (E2 : tenv) (c : nat)
  `{ He1 : valid_tenv v E1 }
  `{ He2 : valid_tenv_extension v E1 E2 }
  : Morphisms.Proper
      (type_equal' v (E1 & E2) empty nil nil knd_type ==>
           subtype' v E1 E2 nil nil (knd_row (CSet.singleton c)))
      (typ_constructor c) | 4
  := { }.
  unfold Morphisms.respectful.
  auto using subtype_reflexive, type_equal_constructor_nonrec.
Qed.

Instance typ_or_sub_morph
  (v : version) (E1 : tenv) (E2 : tenv) (cs1  : cset) (cs2 : cset)
  `{ He1 : valid_tenv v E1 }
  `{ He2 : valid_tenv_extension v E1 E2 }
  `{ Hd : CSet.Disjoint cs1 cs2 }
  : Morphisms.Proper
      (subtype' v E1 E2 nil nil (knd_row cs1) ++>
         subtype' v E1 E2 nil nil (knd_row cs2) ++>
           subtype' v E1 E2 nil nil (knd_row (CSet.union cs1 cs2)))
      (typ_or cs1 cs2) | 4
  := { }.
  unfold Morphisms.respectful.
  auto using subtype_or.
Qed.

Instance typ_proj_sub_morph
  (v : version) (E1 : tenv) (E2 : tenv) (cs1  : cset) (cs2 : cset)
  `{ He1 : valid_tenv v E1 }
  `{ He2 : valid_tenv_extension v E1 E2 }
  `{ Hs : CSet.Subset cs2 cs1 }
  `{ Hs : CSet.Nonempty cs2 }
  : Morphisms.Proper
      (subtype' v E1 E2 nil nil (knd_row cs1) ++>
           subtype' v E1 E2 nil nil (knd_row cs2))
      (typ_proj cs1 cs2) | 4
  := { }.
  unfold Morphisms.respectful.
  auto using subtype_proj.
Qed.

Instance typ_variant_sub_morph
  (v : version) (E1 : tenv) (E2 : tenv)
  `{ He1 : valid_tenv v E1 }
  `{ He2 : valid_tenv_extension v E1 E2 }
  : Morphisms.Proper
      (subtype' v (E1 & E2) empty nil nil knd_row_all ++>
         subtype' v E1 E2 nil nil knd_type)
      typ_variant | 4
  := { }.
  unfold Morphisms.respectful.
  auto using subtype_variant.
Qed.

Instance typ_arrow_sub_morph_full
  (E1 : tenv) (E2 : tenv)
  `{ He1 : valid_tenv version_full_subtyping E1 }
  `{ He2 : valid_tenv_extension version_full_subtyping E1 E2 }
  : Morphisms.Proper
      (subtype' version_full_subtyping
         (E1 & E2) empty nil nil knd_type -->
           subtype' version_full_subtyping
             (E1 & E2) empty nil nil knd_type ++>
               subtype' version_full_subtyping
                  E1 E2 nil nil knd_type)
      typ_arrow | 4
  := { }.
  unfold Morphisms.respectful.
  auto using subtype_arrow.
Qed.

Instance typ_arrow_sub_morph
  (v : version) (E1 : tenv) (E2 : tenv)
  `{ He1 : valid_tenv v E1 }
  `{ He2 : valid_tenv_extension v E1 E2 }
  : Morphisms.Proper
      (type_equal' v (E1 & E2) empty nil nil knd_type ==>
         type_equal' v (E1 & E2) empty nil nil knd_type ==>
           subtype' v E1 E2 nil nil knd_type)
      typ_arrow | 4
  := { }.
  unfold Morphisms.respectful.
  auto using subtype_reflexive, type_equal_arrow_nonrec.
Qed.

Instance typ_ref_sub_morph
  (v : version) (E1 : tenv) (E2 : tenv)
  `{ He1 : valid_tenv v E1 }
  `{ He1 : valid_tenv_extension v E1 E2 }
  : Morphisms.Proper
      (type_equal' v (E1 & E2) empty nil nil knd_type ==>
         subtype' v E1 E2 nil nil knd_type)
      typ_ref | 4
  := { }.
  unfold Morphisms.respectful.
  auto using subtype_reflexive, type_equal_ref_nonrec.
Qed.

Instance typ_prod_sub_morph_full
  (E1 : tenv) (E2 : tenv)
  `{ He1 : valid_tenv version_full_subtyping E1 }
  `{ He2 : valid_tenv_extension version_full_subtyping E1 E2 }
  : Morphisms.Proper
      (subtype' version_full_subtyping
         (E1 & E2) empty nil nil knd_type ++>
           subtype' version_full_subtyping
             (E1 & E2) empty nil nil knd_type ++>
               subtype' version_full_subtyping
                 E1 E2 nil nil knd_type)
      typ_prod | 4
  := { }.
  unfold Morphisms.respectful.
  auto using subtype_prod.
Qed.

Instance typ_prod_sub_morph
  (v : version) (E1 : tenv) (E2 : tenv)
  `{ He1 : valid_tenv v E1 }
  `{ He2 : valid_tenv_extension v E1 E2 }
  : Morphisms.Proper
      (type_equal' v (E1 & E2) empty nil nil knd_type ==>
         type_equal' v (E1 & E2) empty nil nil knd_type ==>
           subtype' v E1 E2 nil nil knd_type)
      typ_prod | 4
  := { }.
  unfold Morphisms.respectful.
  auto using subtype_reflexive, type_equal_prod_nonrec.
Qed.

Instance typ_meet_sub_morph
  (v : version) (E1 : tenv) (E2 : tenv) (K : knd)
  `{ He1 : valid_tenv v E1 }
  `{ He2 : valid_tenv_extension v E1 E2 }
  : Morphisms.Proper
      (subtype' v E1 E2 nil nil K ++>
         subtype' v E1 E2 nil nil K ++>
           subtype' v E1 E2 nil nil K)
      typ_meet | 4
  := { }.
  unfold Morphisms.respectful.
  auto using subtype_meet.
Qed.

Instance typ_join_sub_morph
  (v : version) (E1 : tenv) (E2 : tenv) (K : knd)
  `{ He1 : valid_tenv v E1 }
  `{ He2 : valid_tenv_extension v E1 E2 }
  : Morphisms.Proper
      (subtype' v E1 E2 nil nil K ++>
         subtype' v E1 E2 nil nil K ++>
           subtype' v E1 E2 nil nil K)
      typ_join | 4
  := { }.
  unfold Morphisms.respectful.
  auto using subtype_join.
Qed.

(* *************************************************************** *)
(** Meet is the greatest lower bound *)

Lemma subtype_lower_bound_l_kind : forall v E1 E2 T1 T2 K,
    kind K ->
    kinding E1 E2 T1 K ->
    kinding E1 E2 T2 K ->
    subtype v E1 E2 nil nil (typ_meet T1 T2) T1 K.
Proof.
  introv Hknd Hk1 Hk2.
  unfold subtype.
  rewrite type_equal_meet_commutative at 2 by auto.
  rewrite <- type_equal_meet_associative by auto.
  rewrite <- type_equal_meet_idempotent_kind by auto.
  rewrite type_equal_meet_commutative by auto.
  treflexivity.
Qed.

Lemma subtype_lower_bound_l : forall v E1 E2 T1 T2 K,
    kinding E1 E2 T1 K ->
    kinding E1 E2 T2 K ->
    type_environment E1 ->
    type_environment_extension E1 E2 ->
    subtype v E1 E2 nil nil (typ_meet T1 T2) T1 K.
Proof.
  introv Hk1 Hk2 He1 He2.
  auto using subtype_lower_bound_l_kind with wellformed.
Qed.

Lemma subtype_lower_bound_r_kind : forall v E1 E2 T1 T2 K,
    kind K ->
    kinding E1 E2 T1 K ->
    kinding E1 E2 T2 K ->
    subtype v E1 E2 nil nil (typ_meet T1 T2) T2 K.
Proof.
  introv Hknd Hk1 Hk2.
  unfold subtype.
  rewrite <- type_equal_meet_associative by auto.
  rewrite <- type_equal_meet_idempotent_kind by auto.
  treflexivity.
Qed.

Lemma subtype_lower_bound_r : forall v E1 E2 T1 T2 K,
    kinding E1 E2 T1 K ->
    kinding E1 E2 T2 K ->
    type_environment E1 ->
    type_environment_extension E1 E2 ->
    subtype v E1 E2 nil nil (typ_meet T1 T2) T2 K.
Proof.
  introv Hk1 Hk2 He1 He2.
  auto using subtype_lower_bound_r_kind with wellformed.
Qed.

Lemma subtype_greatest_lower_bound_kinding :
  forall v E1 E2 T1 T2 T3 K,
    subtype v E1 E2 nil nil T3 T1 K ->
    subtype v E1 E2 nil nil T3 T2 K ->
    kind K ->
    kinding E1 E2 T1 K ->
    kinding E1 E2 T2 K ->
    kinding E1 E2 T3 K ->
    subtype v E1 E2 nil nil T3 (typ_meet T1 T2) K.
Proof.
  introv Hs1 Hs2 Hknd Hk1 Hk2 Hk3.
  unfold subtype in *.
  rewrite Hs2 at 1.
  rewrite Hs1 at 1.
  rewrite type_equal_meet_associative by auto.
  treflexivity.
Qed.

Lemma subtype_greatest_lower_bound : forall v E1 E2 T1 T2 T3 K,
    subtype v E1 E2 nil nil T3 T1 K ->
    subtype v E1 E2 nil nil T3 T2 K ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    subtype v E1 E2 nil nil T3 (typ_meet T1 T2) K.
Proof.
  introv Hs1 Hs2 He1 He2.
  apply subtype_greatest_lower_bound_kinding;
    auto with kinding wellformed.
Qed.

(* *************************************************************** *)
(** Join is the least upper bound *)

Lemma subtype_upper_bound_l_kind : forall v E1 E2 T1 T2 K,
    kind K ->
    kinding E1 E2 T1 K ->
    kinding E1 E2 T2 K ->
    subtype v E1 E2 nil nil T1 (typ_join T1 T2) K.
Proof.
  introv Hknd Hk1 Hk2.
  rewrite subtype_dual_kinding; auto.
  rewrite type_equal_join_commutative with (T1 := T1) at 2 by auto.
  rewrite <- type_equal_join_associative by auto.
  rewrite <- type_equal_join_idempotent_kind by auto.
  rewrite type_equal_join_commutative at 1 by auto.
  treflexivity.
Qed.

Lemma subtype_upper_bound_l : forall v E1 E2 T1 T2 K,
    kinding E1 E2 T1 K ->
    kinding E1 E2 T2 K ->
    type_environment E1 ->
    type_environment_extension E1 E2 ->
    subtype v E1 E2 nil nil T1 (typ_join T1 T2) K.
Proof.
  introv Hk1 Hk2 He1 He2.
  auto using subtype_upper_bound_l_kind with wellformed.
Qed.

Lemma subtype_upper_bound_r_kind : forall v E1 E2 T1 T2 K,
    kind K ->
    kinding E1 E2 T1 K ->
    kinding E1 E2 T2 K ->
    subtype v E1 E2 nil nil T2 (typ_join T1 T2) K.
Proof.
  introv Hknd Hk1 Hk2.
  rewrite subtype_dual_kinding; auto.
  rewrite <- type_equal_join_associative by auto.
  rewrite <- type_equal_join_idempotent_kind by auto.
  treflexivity.
Qed.

Lemma subtype_upper_bound_r : forall v E1 E2 T1 T2 K,
    kinding E1 E2 T1 K ->
    kinding E1 E2 T2 K ->
    type_environment E1 ->
    type_environment_extension E1 E2 ->
    subtype v E1 E2 nil nil T2 (typ_join T1 T2) K.
Proof.
  introv Hk1 Hk2 He1 He2.
  auto using subtype_upper_bound_r_kind with wellformed.
Qed.

Lemma subtype_least_upper_bound_kinding : forall v E1 E2 T1 T2 T3 K,
    subtype v E1 E2 nil nil T1 T3 K ->
    subtype v E1 E2 nil nil T2 T3 K ->
    kind K ->
    kinding E1 E2 T1 K ->
    kinding E1 E2 T2 K ->
    kinding E1 E2 T3 K ->
    subtype v E1 E2 nil nil (typ_join T1 T2) T3 K.
Proof.
  introv Hs1 Hs2 Hknd Hk1 Hk2 Hk3.
  rewrite subtype_dual_kinding; auto.
  rewrite subtype_dual_kinding in Hs1, Hs2; auto.
  rewrite Hs2 at 1.
  rewrite Hs1 at 1.
  rewrite type_equal_join_associative by auto.
  treflexivity.
Qed.

Lemma subtype_least_upper_bound : forall v E1 E2 T1 T2 T3 K,
    subtype v E1 E2 nil nil T1 T3 K ->
    subtype v E1 E2 nil nil T2 T3 K ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    subtype v E1 E2 nil nil (typ_join T1 T2) T3 K.
Proof.
  introv Hs1 Hs2 He1 He2.
  auto using subtype_least_upper_bound_kinding
    with kinding wellformed.
Qed.

(* ****************************************************** *)
(** Projection on top and bottom *)

Lemma type_equal_proj_bot : forall v E1 E2 cs1 cs2,
    CSet.Subset cs2 cs1 ->
    CSet.Nonempty cs2 ->
    type_equal v E1 E2 nil nil
      (typ_proj cs1 cs2 (typ_bot (knd_row cs1)))
      (typ_bot (knd_row cs2)) (knd_row cs2).
Proof.
  introv Hs Hn.
  remember (CSet.is_empty (CSet.diff cs1 cs2)) as emp.
  symmetry in Heqemp.
  destruct emp.
  - rewrite CSet.is_empty_spec1 in Heqemp.
    assert (CSet.Equal cs1 cs2) as Heq by csetdec.
    apply CSet.eq_leibniz in Heq; subst.
    rewrite type_equal_proj_id by auto.
    treflexivity.
  - rewrite CSet.is_empty_spec2 in Heqemp.
    rewrite <- type_equal_or_bot
      with (cs1 := cs2) (cs2 := CSet.diff cs1 cs2)
      by auto with csetdec.
    rewrite type_equal_proj_or_l by auto with csetdec.
    rewrite type_equal_proj_id by auto with csetdec.
    treflexivity.
Qed.

Lemma type_equal_proj_top : forall v E1 E2 cs1 cs2,
    CSet.Subset cs2 cs1 ->
    CSet.Nonempty cs2 ->
    type_equal v E1 E2 nil nil
      (typ_proj cs1 cs2 (typ_top (knd_row cs1)))
      (typ_top (knd_row cs2)) (knd_row cs2).
Proof.
  introv Hs Hn.
  remember (CSet.is_empty (CSet.diff cs1 cs2)) as emp.
  symmetry in Heqemp.
  destruct emp.
  - rewrite CSet.is_empty_spec1 in Heqemp.
    assert (CSet.Equal cs1 cs2) as Heq by csetdec.
    apply CSet.eq_leibniz in Heq; subst.
    rewrite type_equal_proj_id by auto.
    treflexivity.
  - rewrite CSet.is_empty_spec2 in Heqemp.
    rewrite <- type_equal_or_top
      with (cs1 := cs2) (cs2 := CSet.diff cs1 cs2)
      by auto with csetdec.
    rewrite type_equal_proj_or_l by auto with csetdec.
    rewrite type_equal_proj_id by auto with csetdec.
    treflexivity.
Qed.

(* *************************************************************** *)
(** Subtyping of projections can be restricted to a subset *)

Lemma subtype_proj_subset : forall v E1 E2 T1 T2 cs1 cs2 cs3 cs4,
    subtype v E1 E2 nil nil (typ_proj cs1 cs3 T1)
      (typ_proj cs2 cs3 T2) (knd_row cs3) ->
    CSet.Subset cs4 cs3 ->
    CSet.Nonempty cs4 ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    subtype v E1 E2 nil nil (typ_proj cs1 cs4 T1)
      (typ_proj cs2 cs4 T2) (knd_row cs4).
Proof.
  introv Hs Hsb Hn He1 He2.
  assert (kinding E1 E2 (typ_proj cs1 cs3 T1) (knd_row cs3)) as Hk1
    by auto with kinding.
  assert (kinding E1 E2 (typ_proj cs2 cs3 T2) (knd_row cs3)) as Hk2
    by auto with kinding.
  inversion Hk1; inversion Hk2; subst.
  assert (CSet.Subset cs4 cs2) by csetdec.
  apply subtype_proj with (cs2 := cs4) in Hs; auto.
  rewrite <- type_equal_proj_compose with (cs2 := cs3)
    by auto with csetdec.
  rewrite Hs.
  rewrite type_equal_proj_compose by auto.
  sreflexivity.
Qed.

Lemma subtype_proj_subset_bottom : forall v E1 E2 T cs1 cs2 cs3,
    subtype v E1 E2 nil nil (typ_proj cs1 cs2 T)
      (typ_bot (knd_row cs2)) (knd_row cs2) ->
    CSet.Subset cs3 cs2 ->
    CSet.Nonempty cs3 ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    subtype v E1 E2 nil nil (typ_proj cs1 cs3 T)
      (typ_bot (knd_row cs3)) (knd_row cs3).
Proof.
  introv Hs Hsb Hn He1 He2.
  assert (kinding E1 E2 (typ_proj cs1 cs2 T) (knd_row cs2)) as Hk
    by auto with kinding.
  inversion Hk; subst.
  rewrite <- type_equal_proj_bot with (cs1 := cs1) (cs2 := cs3)
    by auto with csetdec.
  apply subtype_proj_subset with cs2; auto with csetdec.
  rewrite Hs.
  rewrite type_equal_proj_bot by auto.
  sreflexivity.
Qed.  
