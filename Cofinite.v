(************************************************
 *          Row Subtyping - Cofinite            *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.

Require Import MSets.
Require Import MSetList.
Require Import Arith.

(**************************************************************)
(* CSet                                                       *)
(**************************************************************)

Module CSet.

  Module E <: OrderedTypeWithLeibniz.
    Include PeanoNat.Nat.
    Definition eq_leibniz a b (H:eq a b) := H.
  End E.

  Module MSet := MakeWithLeibniz(E).

  Module MSetFacts := Facts(MSet).

  Module MSetProperties := Properties(MSet).

  Module MSetEqProperties := EqProperties(MSet).

  Module MSetDecide := Decide(MSet).

  Definition elt := nat.

  Inductive t : Type :=
    | finite : MSet.t -> t
    | cofinite : MSet.t -> t.

  Definition empty := finite MSet.empty.

  Definition is_empty cs :=
    match cs with
    | finite ms => MSet.is_empty ms
    | cofinite _ => false
    end.

  Definition universe := cofinite MSet.empty.

  Definition is_universe cs :=
    match cs with
    | finite _ => false
    | cofinite ms => MSet.is_empty ms
    end.

  Definition mem x cs :=
    match cs with
    | finite ms => MSet.mem x ms
    | cofinite ms => negb (MSet.mem x ms)
    end.

  Definition add x cs :=
    match cs with
    | finite ms => finite (MSet.add x ms)
    | cofinite ms => cofinite (MSet.remove x ms)
    end. 

  Definition singleton x :=
    finite (MSet.singleton x).

  Definition cosingleton x :=
    cofinite (MSet.singleton x).

  Definition remove x cs :=
    match cs with
    | finite ms => finite (MSet.remove x ms)
    | cofinite ms => cofinite (MSet.add x ms)
    end. 

  Definition union cs1 cs2 :=
    match cs1, cs2 with
    | finite ms1, finite ms2 => finite (MSet.union ms1 ms2)
    | finite ms1, cofinite ms2 => cofinite (MSet.diff ms2 ms1)
    | cofinite ms1, finite ms2 => cofinite (MSet.diff ms1 ms2)
    | cofinite ms1, cofinite ms2 => cofinite (MSet.inter ms1 ms2)
    end.

  Definition inter cs1 cs2 := 
    match cs1, cs2 with
    | finite ms1, finite ms2 => finite (MSet.inter ms1 ms2)
    | finite ms1, cofinite ms2 => finite (MSet.diff ms1 ms2)
    | cofinite ms1, finite ms2 => finite (MSet.diff ms2 ms1)
    | cofinite ms1, cofinite ms2 => cofinite (MSet.union ms1 ms2)
    end.

  Definition diff cs1 cs2 := 
    match cs1, cs2 with
    | finite ms1, finite ms2 => finite (MSet.diff ms1 ms2)
    | finite ms1, cofinite ms2 => finite (MSet.inter ms1 ms2)
    | cofinite ms1, finite ms2 => cofinite (MSet.union ms1 ms2)
    | cofinite ms1, cofinite ms2 => finite (MSet.diff ms2 ms1)
    end.

  Definition equal cs1 cs2 :=
    match cs1, cs2 with
    | finite ms1, finite ms2 => MSet.equal ms1 ms2
    | finite _, cofinite _ => false
    | cofinite _, finite _ => false
    | cofinite ms1, cofinite ms2 => MSet.equal ms1 ms2
    end.

  Definition subset cs1 cs2 :=
    match cs1, cs2 with
    | finite ms1, finite ms2 => MSet.subset ms1 ms2
    | finite ms1, cofinite ms2 => MSet.is_empty (MSet.inter ms1 ms2)
    | cofinite ms1, finite ms2 => false
    | cofinite ms1, cofinite ms2 => MSet.subset ms2 ms1
    end.

  Definition disjoint cs1 cs2 :=
    is_empty (inter cs1 cs2).

  Local Definition not_in_mset ms :=
    match MSet.max_elt ms with
    | None => 0
    | Some max => S max
    end.

  Definition choose cs :=
    match cs with
    | finite ms => MSet.choose ms
    | cofinite ms => Some (not_in_mset ms)
    end.

  (** Return one element of the given set, or [None] if
  the set is empty. Which element is chosen is unspecified.
  Equal sets could return different elements. *)

  Definition In x cs :=
    match cs with
    | finite ms => MSet.In x ms
    | cofinite ms => ~ MSet.In x ms
    end.

  Definition Equal cs1 cs2 := forall x : elt, In x cs1 <-> In x cs2.

  Definition Subset cs1 cs2 := forall x : elt, In x cs1 -> In x cs2.

  Definition Empty cs := forall x : elt, ~ In x cs.

  Definition Nonempty cs := exists x : elt, In x cs.

  Definition Universe cs := forall x : elt, In x cs.

  Definition Nonuniverse cs := exists x : elt, ~ In x cs.

  Definition For_all (P : elt -> Prop) cs := forall x, In x cs -> P x.

  Definition Exists (P : elt -> Prop) cs := exists x, In x cs /\ P x.

  Definition Disjoint cs1 cs2 :=
    forall x : elt, In x cs1 -> ~ In x cs2.

  Definition eq : t -> t -> Prop := Equal.

  Local Lemma not_in_mset_spec : forall ms,
    ~ (MSet.In (not_in_mset ms) ms).
  Proof.
    intro ms.
    unfold not_in_mset.
    remember (MSet.max_elt ms) as max.
    destruct max as [max | ].
    - intro H.
      apply MSet.max_elt_spec2 with (x := max) in H; auto.
    - apply MSet.max_elt_spec3.
      auto.
  Qed.

  Local Lemma choose_not_in_mset : forall ms,
    exists x : elt, ~ (MSet.In x ms).
  Proof.
    intro ms.
    exists (x := not_in_mset ms).
    apply not_in_mset_spec.
  Qed.

  Local Lemma not_not_in_to_in : forall ms1 ms2,
      ~ (forall x : elt, ~ MSet.In x ms2 -> MSet.In x ms1).
  Proof.
    intros ms1 ms2 Hto.
    destruct (choose_not_in_mset (MSet.union ms1 ms2)) as [x Hnot].
    rewrite MSet.union_spec in Hnot.
    assert (~ MSet.In x ms1) as Hnot1 by intuition auto.
    assert (~ MSet.In x ms2) as Hnot2 by intuition auto.
    apply Hto in Hnot2.
    auto.
  Qed.

  Local Lemma not_in_iff_not_in : forall ms1 ms2,
      ~ (forall x : elt, MSet.In x ms1 <-> ~ MSet.In x ms2).
  Proof.
    intros ms1 ms2 Hiff.
    apply (@not_not_in_to_in ms1 ms2).
    intro x.
    destruct (Hiff x).
    assumption.
  Qed.

  Local Lemma not_not_in_iff_in : forall ms1 ms2,
      ~ (forall x : elt, ~ MSet.In x ms1 <-> MSet.In x ms2).
  Proof.
    intros ms1 ms2 H.
    apply not_in_iff_not_in with (ms1 := ms2) (ms2 := ms1).
    firstorder.
  Qed.

  Local Lemma is_empty_mset_spec2 : forall ms,
    MSet.is_empty ms = false <-> exists x, MSet.In x ms.
  Proof.
    intros ms.
    split; intro Hempty.
    - destruct (MSetEqProperties.choose_mem_3 _ Hempty)
        as [x [_ Hmem]].
      rewrite MSet.mem_spec in Hmem.
      exists x.
      assumption.
    - destruct Hempty.
      rewrite <- MSet.mem_spec in H.
      destruct ms.
      destruct this; auto.
  Qed.

  Local Lemma eq_not_in : forall ms1 ms2,
      MSet.eq ms1 ms2 <->
      forall x : elt, ~ MSet.In x ms1 <-> ~ MSet.In x ms2.
  Proof.
    intros ms1 ms2.
    split.
    - intro Heq.
      split; intro Hnot.
      + rewrite Heq in Hnot.
        auto.
      + rewrite <- Heq in Hnot.
        auto.
    - intro Hiff.
      split; intro Hin.
      + destruct (MSetProperties.In_dec a ms2) as [Hin2 | Hnot2];
          auto.
        rewrite <- Hiff in Hnot2.
        exfalso; auto.
      + destruct (MSetProperties.In_dec a ms1) as [Hin2 | Hnot2];
          auto.
        rewrite Hiff in Hnot2.
        exfalso; auto.
  Qed.

  Lemma In_dec : forall x cs, {In x cs} + {~ In x cs}.
    intros x cs.
    unfold In.
    destruct cs as [ms | ms];
      destruct (MSetProperties.In_dec x ms); intuition.
  Qed.

  Lemma eq_leibniz : forall cs1 cs2,
      eq cs1 cs2 -> cs1 = cs2.
  Proof.
    unfold eq.
    intros cs1 cs2.
    destruct cs1 as [ms1 | ms1]; destruct cs2 as [ms2 | ms2];
      unfold Equal, In; intro H.
    - f_equal; apply MSet.eq_leibniz; auto.
    - exfalso.
      apply not_in_iff_not_in with (ms1 := ms1) (ms2 := ms2).
      auto.
    - exfalso.
      apply not_not_in_iff_in with (ms1 := ms1) (ms2 := ms2).
      auto.
    - f_equal. apply MSet.eq_leibniz.
      rewrite eq_not_in.
      auto.
  Qed.

  Instance Equal_equiv :
    Equivalence Equal.
  Proof.  
    firstorder.
  Qed.

  Lemma eq_dec :
    forall cs1 cs2, { eq cs1 cs2 } + { ~ eq cs1 cs2 }.
  Proof.
    intros cs1 cs2.
    destruct cs1 as [ms1 | ms1]; destruct cs2 as [ms2 | ms2];
      unfold eq, Equal, In.
    - destruct MSet.eq_dec with (s := ms1) (s' := ms2); auto.
    - right.
      apply not_in_iff_not_in.
    - right.
      apply not_not_in_iff_in.
    - destruct MSet.eq_dec with (s := ms1) (s' := ms2).
      + left.
        rewrite <- eq_not_in.      
        auto.
      + right.
        rewrite <- eq_not_in.
        auto.
  Qed.

  Section Spec.
    Variable cs cs1 cs2: t.
    Variable x y : elt.

    Lemma mem_spec:
      mem x cs = true <-> In x cs.
    Proof.
      destruct cs as [ms | ms];
        unfold mem, In; rewrite <- MSet.mem_spec.
      - reflexivity.
      - rewrite negb_true_iff.
        rewrite Bool.not_true_iff_false.
        reflexivity.
    Qed.

    Lemma equal_spec :
      equal cs1 cs2 = true <-> Equal cs1 cs2.
    Proof.
      destruct cs1 as [ms1 | ms1]; destruct cs2 as [ms2 | ms2];
        unfold equal, Equal, In.
      - rewrite MSet.equal_spec.
        unfold MSet.Equal.
        reflexivity.
      - split.
        + discriminate.
        + intro Heq.
          exfalso.
          apply not_in_iff_not_in in Heq.
          assumption.
      - split.
        + discriminate.
        + intro Heq.
          exfalso.
          apply not_not_in_iff_in in Heq.
          assumption.
      - rewrite MSet.equal_spec.
        apply eq_not_in.
    Qed.
    
    Lemma subset_spec :
        subset cs1 cs2 = true <-> Subset cs1 cs2.
    Proof.
      clear cs.
      destruct cs1 as [ms1 | ms1]; destruct cs2 as [ms2 | ms2];
        unfold subset, Subset, In.
      - rewrite MSet.subset_spec.
        unfold MSet.Subset.
        reflexivity.
      - rewrite MSet.is_empty_spec.
        unfold MSet.Empty.
        split; intros H z.
        + specialize H with (a := z).
          rewrite MSet.inter_spec in H.
          firstorder.
        + rewrite MSet.inter_spec.
          firstorder.
      - split; intro H.
        + discriminate.
        + exfalso.
          apply (@not_not_in_to_in ms2 ms1).
          assumption.
      - rewrite MSet.subset_spec.
        unfold MSet.Subset.
        split; intros Hto z Hin.
        + auto.
        + destruct (MSetProperties.In_dec z ms1) as [? | Hnotin];
            auto.
          apply Hto in Hnotin.
          exfalso.
          auto.
    Qed.

    Lemma empty_spec :
      Empty empty.
    Proof.
      unfold empty, Empty, In.
      MSetDecide.fsetdec.
    Qed.

    Lemma universe_spec :
      Universe universe.
    Proof.
      unfold universe, Universe, In.
      MSetDecide.fsetdec.
    Qed.

    Lemma is_empty_spec1 :
      is_empty cs = true <-> Empty cs.
    Proof.
      destruct cs as [ms | ms]; unfold is_empty, Empty, In.
      - apply MSet.is_empty_spec.
      - split; intro H.
        + discriminate.
        + exfalso.
          destruct (choose_not_in_mset ms) as [z Hnotin].
          apply (H z).
          assumption.
    Qed.

    Lemma is_empty_spec2 :
      is_empty cs = false <-> Nonempty cs.
    Proof.
      destruct cs as [ms | ms]; unfold is_empty, Nonempty, In.
      - apply is_empty_mset_spec2.
      - split; auto; intro.
        apply choose_not_in_mset.
    Qed.

    Lemma is_universe_spec1 :
      is_universe cs = true <-> Universe cs.
    Proof.
      destruct cs as [ms | ms]; unfold is_universe, Universe, In.
      - split; intro H.
        + discriminate.
        + exfalso.
          destruct (choose_not_in_mset ms) as [z Hnotin].
          apply Hnotin.
          apply H.
      - rewrite MSet.is_empty_spec.
        unfold MSet.Empty.
        reflexivity.
    Qed.

    Lemma is_universe_spec2 :
      is_universe cs = false <-> Nonuniverse cs.
    Proof.
      destruct cs as [ms | ms]; unfold is_universe, Nonuniverse, In.
      - split; intro H.
        + apply choose_not_in_mset.
        + reflexivity.
      - split; intro H.
        + apply is_empty_mset_spec2 in H.
          destruct H as [z Hin].
          exists z.
          intuition.
        + destruct H as [z Hnotnotin].
          rewrite is_empty_mset_spec2.
          exists z.
          destruct (MSetProperties.In_dec z ms); intuition.
    Qed.

    Lemma add_spec :
      In y (add x cs) <-> y = x \/ In y cs.
    Proof.
      destruct cs as [ms | ms]; unfold add, In;
        split; MSetDecide.fsetdec.
    Qed.      

    Lemma remove_spec :
        In y (remove x cs) <-> In y cs /\ y <> x.
    Proof.
      destruct cs as [ms | ms]; unfold remove, In;
        split; MSetDecide.fsetdec.
    Qed.      

    Lemma singleton_spec :
        In y (singleton x) <-> y = x.
    Proof.
      unfold In, singleton.
      split; MSetDecide.fsetdec.
    Qed.

    Lemma cosingleton_spec :
        In y (cosingleton x) <-> y <> x.
    Proof.
      unfold In, cosingleton.
      split; MSetDecide.fsetdec.
    Qed.

    Lemma union_spec :
      In x (union cs1 cs2) <-> In x cs1 \/ In x cs2.
    Proof.
      destruct cs1 as [ms1 | ms1]; destruct cs2 as [ms2 | ms2];
        unfold union, In; split; MSetDecide.fsetdec.
    Qed.

    Lemma inter_spec :
        In x (inter cs1 cs2) <-> In x cs1 /\ In x cs2.
    Proof.
      destruct cs1 as [ms1 | ms1]; destruct cs2 as [ms2 | ms2];
        unfold inter, In; split; MSetDecide.fsetdec.
    Qed.

    Lemma diff_spec :
      In x (diff cs1 cs2) <-> In x cs1 /\ ~In x cs2.
    Proof.
      destruct cs1 as [ms1 | ms1]; destruct cs2 as [ms2 | ms2];
        unfold diff, In; split; MSetDecide.fsetdec.
    Qed.

    Lemma disjoint_spec :
        disjoint cs1 cs2 = true <-> Disjoint cs1 cs2.
    Proof.
      destruct cs1 as [ms1 | ms1]; destruct cs2 as [ms2 | ms2];
        unfold disjoint, is_empty, inter, Disjoint, In.
      - rewrite MSet.is_empty_spec.
        split. 
        + MSetDecide.fsetdec.
        + unfold MSet.Empty.
          intros H z.
          specialize H with (x := z).
          MSetDecide.fsetdec.
      - rewrite MSet.is_empty_spec.
        split.
        + MSetDecide.fsetdec. 
        + unfold MSet.Empty.
          intros H z.
          specialize H with (x := z).
          MSetDecide.fsetdec.
      - rewrite MSet.is_empty_spec.
        split.
        + MSetDecide.fsetdec.
        + unfold MSet.Empty.
          intros H z.
          specialize H with (x := z).
          MSetDecide.fsetdec.
      - split.
        + intro.
          discriminate.
        + intro H.
          exfalso.
          apply (@not_not_in_to_in ms2 ms1).
          intros z Hin1.
          specialize H with (x := z).
          destruct (MSetProperties.In_dec z ms2) as [? | Hnotin2];
            auto.
          exfalso.
          apply H; auto.
    Qed.

    Lemma choose_spec1 :
        choose cs = Some x -> In x cs.
    Proof.
      destruct cs as [ms | ms];
        unfold choose, In.
      - apply MSet.choose_spec1.
      - intro H.
        inversion H.
        apply not_in_mset_spec.
    Qed.      

    Lemma choose_spec2 :
        choose cs = None -> Empty cs.
    Proof.
      destruct cs as [ms | ms];
        unfold choose, Empty, In.
      - intro H.
        apply MSet.choose_spec2 in H.
        MSetDecide.fsetdec.
      - intro.
        discriminate.
    Qed.

  End Spec.

End CSet.

Import CSet.

Definition cset := CSet.t.

(**************************************************************)
(* CSetFacts                                                  *)
(**************************************************************)

Module CSetFacts.

  Notation eq_dec := E.eq_dec.
  Definition eqb x y := if eq_dec x y then true else false.

  Section ImplSpec.
    Variable cs cs1 cs2 : t.
    Variable x y : elt.

    Lemma In_1 : E.eq x y -> In x cs -> In y cs.
    Proof. intros E; rewrite E; auto. Qed.

    Lemma mem_1 : In x cs -> mem x cs = true.
    Proof. intros; apply <- mem_spec; auto. Qed.
    Lemma mem_2 : mem x cs = true -> In x cs.
    Proof. intros; apply -> mem_spec; auto. Qed.

    Lemma equal_1 : Equal cs1 cs2 -> equal cs1 cs2 = true.
    Proof. intros; apply <- equal_spec; auto. Qed.
    Lemma equal_2 : equal cs1 cs2 = true -> Equal cs1 cs2.
    Proof. intros; apply -> equal_spec; auto. Qed.

    Lemma subset_1 : Subset cs1 cs2 -> subset cs1 cs2 = true.
    Proof. intros; apply <- subset_spec; auto. Qed.
    Lemma subset_2 : subset cs1 cs2 = true -> Subset cs1 cs2.
    Proof. intros; apply -> subset_spec; auto. Qed.

    Lemma is_empty_1 : Empty cs -> is_empty cs = true.
    Proof. intros; apply <- is_empty_spec1; auto. Qed.
    Lemma is_empty_2 : is_empty cs = true -> Empty cs.
    Proof. intros; apply -> is_empty_spec1; auto. Qed.
    Lemma is_empty_3 : Nonempty cs -> is_empty cs = false.
    Proof. intros; apply <- is_empty_spec2; auto. Qed.
    Lemma is_empty_4 : is_empty cs = false -> Nonempty cs.
    Proof. intros; apply -> is_empty_spec2; auto. Qed.

    Lemma is_universe_1 : Universe cs -> is_universe cs = true.
    Proof. intros; apply <- is_universe_spec1; auto. Qed.
    Lemma is_universe_2 : is_universe cs = true -> Universe cs.
    Proof. intros; apply -> is_universe_spec1; auto. Qed.
    Lemma is_universe_3 : Nonuniverse cs -> is_universe cs = false.
    Proof. intros; apply <- is_universe_spec2; auto. Qed.
    Lemma is_universe_4 : is_universe cs = false -> Nonuniverse cs.
    Proof. intros; apply -> is_universe_spec2; auto. Qed.

    Lemma add_1 : E.eq x y -> In y (add x cs).
    Proof. intros; apply <- add_spec. auto with relations. Qed.
    Lemma add_2 : In y cs -> In y (add x cs).
    Proof. intros; apply <- add_spec; auto. Qed.
    Lemma add_3 : ~ E.eq x y -> In y (add x cs) -> In y cs.
    Proof.
      rewrite add_spec. intros H [H'|H']; auto.
      elim H; auto with relations.
    Qed.
    
    Lemma remove_1 : E.eq x y -> ~ In y (remove x cs).
    Proof. intros; rewrite remove_spec; intuition. Qed.
    Lemma remove_2 : ~ E.eq x y -> In y cs -> In y (remove x cs).
    Proof. intros; apply <- remove_spec; auto with relations. Qed.
    Lemma remove_3 : In y (remove x cs) -> In y cs.
    Proof. rewrite remove_spec; intuition. Qed.

    Lemma singleton_1 : In y (singleton x) -> E.eq x y.
    Proof. rewrite singleton_spec; auto with relations. Qed.
    Lemma singleton_2 : E.eq x y -> In y (singleton x).
    Proof. rewrite singleton_spec; auto with relations. Qed.

    Lemma cosingleton_1 : In y (cosingleton x) -> ~ E.eq x y.
    Proof. rewrite cosingleton_spec; auto with relations. Qed.
    Lemma cosingleton_2 : ~ E.eq x y -> In y (cosingleton x).
    Proof. rewrite cosingleton_spec; auto with relations. Qed.

    Lemma union_1 : In x (union cs1 cs2) -> In x cs1 \/ In x cs2.
    Proof. rewrite union_spec; auto. Qed.
    Lemma union_2 : In x cs1 -> In x (union cs1 cs2).
    Proof. rewrite union_spec; auto. Qed.
    Lemma union_3 : In x cs2 -> In x (union cs1 cs2).
    Proof. rewrite union_spec; auto. Qed.

    Lemma inter_1 : In x (inter cs1 cs2) -> In x cs1.
    Proof. rewrite inter_spec; intuition. Qed.
    Lemma inter_2 : In x (inter cs1 cs2) -> In x cs2.
    Proof. rewrite inter_spec; intuition. Qed.
    Lemma inter_3 : In x cs1 -> In x cs2 -> In x (inter cs1 cs2).
    Proof. rewrite inter_spec; intuition. Qed.

    Lemma diff_1 : In x (diff cs1 cs2) -> In x cs1.
    Proof. rewrite diff_spec; intuition. Qed.
    Lemma diff_2 : In x (diff cs1 cs2) -> ~ In x cs2.
    Proof. rewrite diff_spec; intuition. Qed.
    Lemma diff_3 : In x cs1 -> ~ In x cs2 -> In x (diff cs1 cs2).
    Proof. rewrite diff_spec; auto. Qed.

    Lemma disjoint_1 : Disjoint cs1 cs2 -> disjoint cs1 cs2 = true.
    Proof. intros; apply <- disjoint_spec; auto. Qed.
    Lemma disjoint_2 : disjoint cs1 cs2 = true -> Disjoint cs1 cs2.
    Proof. intros; apply -> disjoint_spec; auto. Qed.

  End ImplSpec.

  Notation empty_1 := empty_spec (only parsing).
  Notation universe_1 := universe_spec (only parsing).

  Hint Resolve mem_1 equal_1 subset_1 empty_1 universe_1
      is_empty_1 is_empty_3 is_universe_1 is_universe_3
      add_1 add_2 remove_1 remove_2 singleton_2
      cosingleton_2 union_1 union_2 union_3 inter_3 diff_3
      disjoint_1 : set.

  Hint Immediate In_1 mem_2 equal_2 subset_2 is_empty_2 is_empty_4
       is_universe_2 is_universe_4 add_3 remove_3 singleton_1
       cosingleton_1 inter_1 inter_2 diff_1 diff_2 disjoint_2
    : set.

  (** * Specifications written using equivalences :
        this is now provided by the default interface. *)

  Section IffSpec.
    Variable cs cs1 cs2 : t.
    Variable x y : elt.

    Lemma In_eq_iff : E.eq x y -> (In x cs <-> In y cs).
    Proof.
      intros E; rewrite E; intuition.
    Qed.

    Lemma mem_iff : In x cs <-> mem x cs = true.
    Proof. apply iff_sym, mem_spec. Qed.

    Lemma not_mem_iff : ~In x cs <-> mem x cs = false.
    Proof.
      rewrite <-mem_spec; destruct (mem x cs); intuition.
    Qed.

    Lemma equal_iff : Equal cs1 cs2 <-> equal cs1 cs2 = true.
    Proof. apply iff_sym, equal_spec. Qed.

    Lemma subset_iff : Subset cs1 cs2 <-> subset cs1 cs2 = true.
    Proof. apply iff_sym. apply subset_spec. Qed.

    Lemma empty_iff : In x empty <-> False.
    Proof. intuition; apply (empty_spec H). Qed.

    Lemma universe_iff : In x universe <-> True.
    Proof. intuition; apply (universe_spec H). Qed.

    Lemma is_empty_iff1 : Empty cs <-> is_empty cs = true.
    Proof. apply iff_sym, is_empty_spec1. Qed.

    Lemma is_empty_iff2 : Nonempty cs <-> is_empty cs = false.
    Proof. apply iff_sym, is_empty_spec2. Qed.

    Lemma is_universe_iff1 : Universe cs <-> is_universe cs = true.
    Proof. apply iff_sym, is_universe_spec1. Qed.

    Lemma is_universe_iff2 :
      Nonuniverse cs <-> is_universe cs = false.
    Proof. apply iff_sym, is_universe_spec2. Qed.

    Lemma singleton_iff : In y (singleton x) <-> E.eq x y.
    Proof. rewrite singleton_spec; intuition. Qed.

    Lemma cosingleton_iff : In y (cosingleton x) <-> ~ E.eq x y.
    Proof. rewrite cosingleton_spec; intuition. Qed.

    Lemma add_iff : In y (add x cs) <-> E.eq x y \/ In y cs.
    Proof. rewrite add_spec; intuition. Qed.

    Lemma add_neq_iff : ~ E.eq x y -> (In y (add x cs)  <-> In y cs).
    Proof.
      rewrite add_spec; intuition. elim H; auto with relations.
    Qed.

    Lemma remove_iff : In y (remove x cs) <-> In y cs /\ ~E.eq x y.
    Proof. rewrite remove_spec; intuition. Qed.

    Lemma remove_neq_iff :
      ~ E.eq x y -> (In y (remove x cs) <-> In y cs).
    Proof. rewrite remove_spec; intuition. Qed.

    Lemma disjoint_iff : Disjoint cs1 cs2 <-> disjoint cs1 cs2 = true.
    Proof. apply iff_sym. apply disjoint_spec. Qed.

  End IffSpec.

  Notation union_iff := union_spec (only parsing).
  Notation inter_iff := inter_spec (only parsing).
  Notation diff_iff := diff_spec (only parsing).

  (** Useful tactic for simplifying expressions like
      [In y (add x (union s s'))] *)

  Ltac set_iff :=
   repeat (progress (
    rewrite add_iff || rewrite remove_iff || rewrite singleton_iff
    || rewrite cosingleton_iff || rewrite union_iff
    || rewrite inter_iff || rewrite diff_iff
    || rewrite empty_iff || rewrite universe_iff)).

  (**  * Specifications written using boolean predicates *)

  Section BoolSpec.
    Variable cs cs1 cs2 : t.
    Variable x y : elt.

    Lemma mem_b : E.eq x y -> mem x cs = mem y cs.
    Proof.
    intros.
    generalize (mem_iff cs x) (mem_iff cs y)(In_eq_iff cs H).
    destruct (mem x cs); destruct (mem y cs); intuition.
    Qed.

    Lemma empty_b : mem y empty = false.
    Proof.
    generalize (empty_iff y)(mem_iff empty y).
    destruct (mem y empty); intuition.
    Qed.

    Lemma universe_b : mem y universe = true.
    Proof.
    generalize (universe_iff y)(mem_iff universe y).
    destruct (mem y universe); intuition.
    Qed.

    Lemma add_b : mem y (add x cs) = eqb x y || mem y cs.
    Proof.
    generalize (mem_iff (add x cs) y)(mem_iff cs y)(add_iff cs x y);
      unfold eqb.
    destruct (eq_dec x y); destruct (mem y cs);
      destruct (mem y (add x cs)); intuition.
    Qed.

    Lemma add_neq_b : ~ E.eq x y -> mem y (add x cs) = mem y cs.
    Proof.
    intros;
      generalize (mem_iff (add x cs) y)
        (mem_iff cs y) (add_neq_iff cs H).
    destruct (mem y cs); destruct (mem y (add x cs)); intuition.
    Qed.

    Lemma remove_b : mem y (remove x cs) = mem y cs && negb (eqb x y).
    Proof.
    generalize (mem_iff (remove x cs) y)
      (mem_iff cs y)(remove_iff cs x y);
      unfold eqb.
    destruct (eq_dec x y); destruct (mem y cs);
      destruct (mem y (remove x cs)); simpl; intuition.
    Qed.

    Lemma remove_neq_b : ~ E.eq x y -> mem y (remove x cs) = mem y cs.
    Proof.
    intros; generalize (mem_iff (remove x cs) y)
      (mem_iff cs y)(remove_neq_iff cs H).
    destruct (mem y cs); destruct (mem y (remove x cs)); intuition.
    Qed.

    Lemma singleton_b : mem y (singleton x) = eqb x y.
    Proof.
    generalize (mem_iff (singleton x) y)(singleton_iff x y);
      unfold eqb.
    destruct (eq_dec x y); destruct (mem y (singleton x)); intuition.
    Qed.

    Lemma cosingleton_b : mem y (cosingleton x) = negb (eqb x y).
    Proof.
    generalize (mem_iff (cosingleton x) y)(cosingleton_iff x y);
      unfold eqb, negb.
    destruct (eq_dec x y); destruct (mem y (cosingleton x));
      intuition.
    Qed.

    Lemma union_b : mem x (union cs1 cs2) = mem x cs1 || mem x cs2.
    Proof.
    generalize (mem_iff (union cs1 cs2) x)
      (mem_iff cs1 x)(mem_iff cs2 x)(union_iff cs1 cs2 x).
    destruct (mem x cs1); destruct (mem x cs2);
      destruct (mem x (union cs1 cs2)); intuition.
    Qed.

    Lemma inter_b : mem x (inter cs1 cs2) = mem x cs1 && mem x cs2.
    Proof.
    generalize (mem_iff (inter cs1 cs2) x)
      (mem_iff cs1 x)(mem_iff cs2 x)(inter_iff cs1 cs2 x).
    destruct (mem x cs1); destruct (mem x cs2);
      destruct (mem x (inter cs1 cs2)); intuition.
    Qed.

    Lemma diff_b :
      mem x (diff cs1 cs2) = mem x cs1 && negb (mem x cs2).
    Proof.
    generalize (mem_iff (diff cs1 cs2) x)
      (mem_iff cs1 x)(mem_iff cs2 x)(diff_iff cs1 cs2 x).
    destruct (mem x cs1); destruct (mem x cs2);
      destruct (mem x (diff cs1 cs2)); simpl; intuition.
    Qed.

  End BoolSpec.

  (** * Declarations of morphisms with respects to [E.eq] and
        [Equal] *)

  Instance In_m : Proper (E.eq==>Equal==>iff) In.
  Proof.
  unfold Equal; intros x y H s s' H0.
  rewrite (In_eq_iff s H); auto.
  Qed.

  Instance Empty_m : Proper (Equal==>iff) Empty.
  Proof.
  repeat red; unfold Empty; intros s s' E.
  setoid_rewrite E; auto.
  Qed.

  Instance Nonempty_m : Proper (Equal==>iff) Nonempty.
  Proof.
  repeat red; unfold Nonempty; intros s s' E.
  setoid_rewrite E; auto.
  Qed.

  Instance Universe_m : Proper (Equal==>iff) Universe.
  Proof.
  repeat red; unfold Universe; intros s s' E.
  setoid_rewrite E; auto.
  Qed.

  Instance is_empty_m : Proper (Equal==>Logic.eq) is_empty.
  Proof.
  intros s s' H.
  generalize (is_empty_iff1 s). rewrite H at 1. rewrite is_empty_iff1.
  destruct (is_empty s); destruct (is_empty s'); intuition.
  Qed.

  Instance is_universe_m : Proper (Equal==>Logic.eq) is_universe.
  Proof.
  intros s s' H.
  generalize (is_universe_iff1 s).
  rewrite H at 1. rewrite is_universe_iff1.
  destruct (is_universe s); destruct (is_universe s'); intuition.
  Qed.

  Instance mem_m : Proper (E.eq==>Equal==>Logic.eq) mem.
  Proof.
  intros x x' Hx s s' Hs.
  generalize (mem_iff s x). rewrite Hs, Hx at 1; rewrite mem_iff.
  destruct (mem x s), (mem x' s'); intuition.
  Qed.

  Instance singleton_m : Proper (E.eq==>Equal) singleton.
  Proof.
  intros x y H a. rewrite !singleton_iff, H; intuition.
  Qed.

  Instance cosingleton_m : Proper (E.eq==>Equal) cosingleton.
  Proof.
  intros x y H a. rewrite !cosingleton_iff, H; intuition.
  Qed.

  Instance add_m : Proper (E.eq==>Equal==>Equal) add.
  Proof.
  intros x x' Hx s s' Hs a. rewrite !add_iff, Hx, Hs; intuition.
  Qed.

  Instance remove_m : Proper (E.eq==>Equal==>Equal) remove.
  Proof.
  intros x x' Hx s s' Hs a. rewrite !remove_iff, Hx, Hs; intuition.
  Qed.

  Instance union_m : Proper (Equal==>Equal==>Equal) union.
  Proof.
  intros s1 s1' Hs1 s2 s2' Hs2 a.
  rewrite !union_iff, Hs1, Hs2; intuition.
  Qed.

  Instance inter_m : Proper (Equal==>Equal==>Equal) inter.
  Proof.
  intros s1 s1' Hs1 s2 s2' Hs2 a.
  rewrite !inter_iff, Hs1, Hs2; intuition.
  Qed.

  Instance diff_m : Proper (Equal==>Equal==>Equal) diff.
  Proof.
  intros s1 s1' Hs1 s2 s2' Hs2 a.
  rewrite !diff_iff, Hs1, Hs2; intuition.
  Qed.

  Instance Subset_m : Proper (Equal==>Equal==>iff) Subset.
  Proof.
  unfold Equal, Subset; firstorder.
  Qed.

  Instance subset_m : Proper (Equal==>Equal==>Logic.eq) subset.
  Proof.
  intros s1 s1' Hs1 s2 s2' Hs2.
  generalize (subset_iff s1 s2).
  rewrite Hs1, Hs2 at 1. rewrite subset_iff.
  destruct (subset s1 s2); destruct (subset s1' s2'); intuition.
  Qed.

  Instance equal_m : Proper (Equal==>Equal==>Logic.eq) equal.
  Proof.
  intros s1 s1' Hs1 s2 s2' Hs2.
  generalize (equal_iff s1 s2).
  rewrite Hs1,Hs2 at 1. rewrite equal_iff.
  destruct (equal s1 s2); destruct (equal s1' s2'); intuition.
  Qed.

  Instance Disjoint_m : Proper (Equal==>Equal==>iff) Disjoint.
  Proof.
  unfold Equal, Disjoint; firstorder.
  Qed.

  Instance disjoint_m : Proper (Equal==>Equal==>Logic.eq) disjoint.
  Proof.
  intros s1 s1' Hs1 s2 s2' Hs2.
  generalize (disjoint_iff s1 s2).
  rewrite Hs1, Hs2 at 1. rewrite disjoint_iff.
  destruct (disjoint s1 s2); destruct (disjoint s1' s2'); intuition.
  Qed.

  Instance SubsetSetoid : PreOrder Subset.
  Proof. firstorder. Qed.

  Definition Subset_refl := @PreOrder_Reflexive _ _ SubsetSetoid.
  Definition Subset_trans := @PreOrder_Transitive _ _ SubsetSetoid.

  Instance In_s_m :
    Morphisms.Proper (E.eq ==> Subset ++> impl) In | 1.
  Proof.
    simpl_relation. fold (In y y0). eauto with set.
  Qed.

  Instance Empty_s_m : Proper (Subset-->impl) Empty.
  Proof. firstorder. Qed.

  Instance Universe_s_m : Proper (Subset-->impl) Empty.
  Proof. firstorder. Qed.

  Instance add_s_m : Proper (E.eq==>Subset++>Subset) add.
  Proof.
  intros x x' Hx s s' Hs a. rewrite !add_iff, Hx; intuition.
  Qed.

  Instance remove_s_m : Proper (E.eq==>Subset++>Subset) remove.
  Proof.
  intros x x' Hx s s' Hs a. rewrite !remove_iff, Hx; intuition.
  Qed.

  Instance union_s_m : Proper (Subset++>Subset++>Subset) union.
  Proof.
  intros s1 s1' Hs1 s2 s2' Hs2 a.
  rewrite !union_iff, Hs1, Hs2; intuition.
  Qed.

  Instance inter_s_m : Proper (Subset++>Subset++>Subset) inter.
  Proof.
  intros s1 s1' Hs1 s2 s2' Hs2 a.
  rewrite !inter_iff, Hs1, Hs2; intuition.
  Qed.

  Instance diff_s_m : Proper (Subset++>Subset-->Subset) diff.
  Proof.
  intros s1 s1' Hs1 s2 s2' Hs2 a.
  rewrite !diff_iff, Hs1, Hs2; intuition.
  Qed.

End CSetFacts.

(**************************************************************)
(* CSetDecide                                                 *)
(**************************************************************)

Require Import Decidable Setoid DecidableTypeEx.

(** * Facts and Tactics for Propositional Logic
      These lemmas and tactics are in a module so that they do
      not affect the namespace if you import the enclosing
      module [Decide]. *)
Module CSetLogicalFacts.

  Export Decidable.
  Export Setoid.

  (** ** Lemmas and Tactics About Decidable Propositions *)

  (** ** Propositional Equivalences Involving Negation
        These are all written with the unfolded form of
        negation, since I am not sure if setoid rewriting will
        always perform conversion. *)

  (** ** Tactics for Negations *)

  Tactic Notation "fold" "any" "not" :=
    repeat (
      match goal with
      | H: context [?P -> False] |- _ =>
        fold (~ P) in H
      | |- context [?P -> False] =>
        fold (~ P)
      end).

  (** [push not using db] will pushes all negations to the
      leaves of propositions in the goal, using the lemmas in
      [db] to assist in checking the decidability of the
      propositions involved.  If [using db] is omitted, then
      [core] will be used.  Additional versions are provided
      to manipulate the hypotheses or the hypotheses and goal
      together. *)

  Ltac or_not_l_iff P Q tac :=
    (rewrite (or_not_l_iff_1 P Q) by tac) ||
    (rewrite (or_not_l_iff_2 P Q) by tac).

  Ltac or_not_r_iff P Q tac :=
    (rewrite (or_not_r_iff_1 P Q) by tac) ||
    (rewrite (or_not_r_iff_2 P Q) by tac).

  Ltac or_not_l_iff_in P Q H tac :=
    (rewrite (or_not_l_iff_1 P Q) in H by tac) ||
    (rewrite (or_not_l_iff_2 P Q) in H by tac).

  Ltac or_not_r_iff_in P Q H tac :=
    (rewrite (or_not_r_iff_1 P Q) in H by tac) ||
    (rewrite (or_not_r_iff_2 P Q) in H by tac).

  Tactic Notation "push" "not" "using" ident(db) :=
    let dec := solve_decidable using db in
    unfold not, iff;
    repeat (
      match goal with
      | |- context [True -> False] => rewrite not_true_iff
      | |- context [False -> False] => rewrite not_false_iff
      | |- context [(?P -> False) -> False] =>
        rewrite (not_not_iff P) by dec
      | |- context [(?P -> False) -> (?Q -> False)] =>
          rewrite (contrapositive P Q) by dec
      | |- context [(?P -> False) \/ ?Q] => or_not_l_iff P Q dec
      | |- context [?P \/ (?Q -> False)] => or_not_r_iff P Q dec
      | |- context [(?P -> False) -> ?Q] =>
        rewrite (imp_not_l P Q) by dec
      | |- context [?P \/ ?Q -> False] => rewrite (not_or_iff P Q)
      | |- context [?P /\ ?Q -> False] => rewrite (not_and_iff P Q)
      | |- context [(?P -> ?Q) -> False] =>
        rewrite (not_imp_iff P Q) by dec
      end);
    fold any not.

  Tactic Notation "push" "not" :=
    push not using core.

  Tactic Notation
    "push" "not" "in" "*" "|-" "using" ident(db) :=
    let dec := solve_decidable using db in
    unfold not, iff in * |-;
    repeat (
      match goal with
      | H: context [True -> False] |- _ =>
        rewrite not_true_iff in H
      | H: context [False -> False] |- _ =>
        rewrite not_false_iff in H
      | H: context [(?P -> False) -> False] |- _ =>
        rewrite (not_not_iff P) in H by dec
      | H: context [(?P -> False) -> (?Q -> False)] |- _ =>
        rewrite (contrapositive P Q) in H by dec
      | H: context [(?P -> False) \/ ?Q] |- _ =>
        or_not_l_iff_in P Q H dec
      | H: context [?P \/ (?Q -> False)] |- _ =>
        or_not_r_iff_in P Q H dec
      | H: context [(?P -> False) -> ?Q] |- _ =>
        rewrite (imp_not_l P Q) in H by dec
      | H: context [?P \/ ?Q -> False] |- _ =>
        rewrite (not_or_iff P Q) in H
      | H: context [?P /\ ?Q -> False] |- _ =>
        rewrite (not_and_iff P Q) in H
      | H: context [(?P -> ?Q) -> False] |- _ =>
        rewrite (not_imp_iff P Q) in H by dec
      end);
    fold any not.

  Tactic Notation "push" "not" "in" "*" "|-"  :=
    push not in * |- using core.

  Tactic Notation "push" "not" "in" "*" "using" ident(db) :=
    push not using db; push not in * |- using db.
  Tactic Notation "push" "not" "in" "*" :=
    push not in * using core.

  (** [pull not using db] will pull as many negations as
      possible toward the top of the propositions in the goal,
      using the lemmas in [db] to assist in checking the
      decidability of the propositions involved.  If [using
      db] is omitted, then [core] will be used.  Additional
      versions are provided to manipulate the hypotheses or
      the hypotheses and goal together. *)

  Tactic Notation "pull" "not" "using" ident(db) :=
    let dec := solve_decidable using db in
    unfold not, iff;
    repeat (
      match goal with
      | |- context [True -> False] => rewrite not_true_iff
      | |- context [False -> False] => rewrite not_false_iff
      | |- context [(?P -> False) -> False] =>
        rewrite (not_not_iff P) by dec
      | |- context [(?P -> False) -> (?Q -> False)] =>
        rewrite (contrapositive P Q) by dec
      | |- context [(?P -> False) \/ ?Q] => or_not_l_iff P Q dec
      | |- context [?P \/ (?Q -> False)] => or_not_r_iff P Q dec
      | |- context [(?P -> False) -> ?Q] =>
        rewrite (imp_not_l P Q) by dec
      | |- context [(?P -> False) /\ (?Q -> False)] =>
        rewrite <- (not_or_iff P Q)
      | |- context [?P -> ?Q -> False] =>
        rewrite <- (not_and_iff P Q)
      | |- context [?P /\ (?Q -> False)] =>
        rewrite <- (not_imp_iff P Q) by dec
      | |- context [(?Q -> False) /\ ?P] =>
        rewrite <- (not_imp_rev_iff P Q) by dec
      end);
    fold any not.

  Tactic Notation "pull" "not" :=
    pull not using core.

  Tactic Notation
    "pull" "not" "in" "*" "|-" "using" ident(db) :=
    let dec := solve_decidable using db in
    unfold not, iff in * |-;
    repeat (
      match goal with
      | H: context [True -> False] |- _ =>
        rewrite not_true_iff in H
      | H: context [False -> False] |- _ =>
        rewrite not_false_iff in H
      | H: context [(?P -> False) -> False] |- _ =>
        rewrite (not_not_iff P) in H by dec
      | H: context [(?P -> False) -> (?Q -> False)] |- _ =>
        rewrite (contrapositive P Q) in H by dec
      | H: context [(?P -> False) \/ ?Q] |- _ =>
        or_not_l_iff_in P Q H dec
      | H: context [?P \/ (?Q -> False)] |- _ =>
        or_not_r_iff_in P Q H dec
      | H: context [(?P -> False) -> ?Q] |- _ =>
        rewrite (imp_not_l P Q) in H by dec
      | H: context [(?P -> False) /\ (?Q -> False)] |- _ =>
        rewrite <- (not_or_iff P Q) in H
      | H: context [?P -> ?Q -> False] |- _ =>
        rewrite <- (not_and_iff P Q) in H
      | H: context [?P /\ (?Q -> False)] |- _ =>
        rewrite <- (not_imp_iff P Q) in H by dec
      | H: context [(?Q -> False) /\ ?P] |- _ =>
        rewrite <- (not_imp_rev_iff P Q) in H by dec
      end);
    fold any not.

  Tactic Notation "pull" "not" "in" "*" "|-"  :=
    pull not in * |- using core.

  Tactic Notation "pull" "not" "in" "*" "using" ident(db) :=
    pull not using db; pull not in * |- using db.
  Tactic Notation "pull" "not" "in" "*" :=
    pull not in * using core.

End CSetLogicalFacts.

Import CSetLogicalFacts.

Module CSetDecideAuxiliary.

  (** ** Generic Tactics
      We begin by defining a few generic, useful tactics. *)

  Ltac no_logical_interdep :=
    match goal with
      | H : ?P |- _ =>
        match type of P with
          | Prop =>
            match goal with
              H' : context [ H ] |- _ =>
              clear dependent H' end
          | _ => fail
        end; no_logical_interdep
      | _ => idtac
    end.

  Ltac abstract_term t :=
    tryif (is_var t) then fail "no need to abstract a variable"
    else (let x := fresh "x" in set (x := t) in *; try clearbody x).

  Ltac abstract_elements :=
    repeat
      (match goal with
         | |- context [ singleton ?t ] => abstract_term t
         | _ : context [ singleton ?t ] |- _ => abstract_term t
         | |- context [ cosingleton ?t ] => abstract_term t
         | _ : context [ cosingleton ?t ] |- _ => abstract_term t
         | |- context [ add ?t _ ] => abstract_term t
         | _ : context [ add ?t _ ] |- _ => abstract_term t
         | |- context [ remove ?t _ ] => abstract_term t
         | _ : context [ remove ?t _ ] |- _ => abstract_term t
         | |- context [ In ?t _ ] => abstract_term t
         | _ : context [ In ?t _ ] |- _ => abstract_term t
       end).

  (** [prop P holds by t] succeeds (but does not modify the
      goal or context) if the proposition [P] can be proved by
      [t] in the current context.  Otherwise, the tactic
      fails. *)
  Tactic Notation "prop" constr(P) "holds" "by" tactic(t) :=
    let H := fresh in
    assert P as H by t;
    clear H.

  (** This tactic acts just like [assert ... by ...] but will
      fail if the context already contains the proposition. *)
  Tactic Notation "assert" "new" constr(e) "by" tactic(t) :=
    match goal with
    | H: e |- _ => fail 1
    | _ => assert e by t
    end.

  (** [subst++] is similar to [subst] except that
      - it never fails (as [subst] does on recursive
        equations),
      - it substitutes locally defined variable for their
        definitions,
      - it performs beta reductions everywhere, which may
        arise after substituting a locally defined function
        for its definition.
      *)
  Tactic Notation "subst" "++" :=
    repeat (
      match goal with
      | x : _ |- _ => subst x
      end);
    cbv zeta beta in *.

  (** [decompose records] calls [decompose record H] on every
      relevant hypothesis [H]. *)
  Tactic Notation "decompose" "records" :=
    repeat (
      match goal with
      | H: _ |- _ => progress (decompose record H); clear H
      end).

  (** ** Discarding Irrelevant Hypotheses
      We will want to clear the context of any
      non-CSet-related hypotheses in order to increase the
      speed of the tactic.  To do this, we will need to be
      able to decide which are relevant.  We do this by making
      a simple inductive definition classifying the
      propositions of interest. *)

  Inductive CSet_elt_Prop : Prop -> Prop :=
  | eq_Prop : forall (S : Type) (x y : S),
      CSet_elt_Prop (x = y)
  | eq_elt_prop : forall x y,
      CSet_elt_Prop (E.eq x y)
  | In_elt_prop : forall x s,
      CSet_elt_Prop (In x s)
  | True_elt_prop :
      CSet_elt_Prop True
  | False_elt_prop :
      CSet_elt_Prop False
  | conj_elt_prop : forall P Q,
      CSet_elt_Prop P ->
      CSet_elt_Prop Q ->
      CSet_elt_Prop (P /\ Q)
  | disj_elt_prop : forall P Q,
      CSet_elt_Prop P ->
      CSet_elt_Prop Q ->
      CSet_elt_Prop (P \/ Q)
  | impl_elt_prop : forall P Q,
      CSet_elt_Prop P ->
      CSet_elt_Prop Q ->
      CSet_elt_Prop (P -> Q)
  | not_elt_prop : forall P,
      CSet_elt_Prop P ->
      CSet_elt_Prop (~ P).

  Inductive CSet_Prop : Prop -> Prop :=
  | elt_CSet_Prop : forall P,
      CSet_elt_Prop P ->
      CSet_Prop P
  | Empty_CSet_Prop : forall s,
      CSet_Prop (Empty s)
  | Nonempty_CSet_Prop : forall s,
      CSet_Prop (Nonempty s)
  | Universe_CSet_Prop : forall s,
      CSet_Prop (Universe s)
  | Subset_CSet_Prop : forall s1 s2,
      CSet_Prop (Subset s1 s2)
  | Equal_CSet_Prop : forall s1 s2,
      CSet_Prop (Equal s1 s2)
  | Disjoint_CSet_Prop : forall s1 s2,
      CSet_Prop (Disjoint s1 s2).

  (** Here is the tactic that will throw away hypotheses that
      are not useful (for the intended scope of the [fsetdec]
      tactic). *)
  Hint Constructors CSet_elt_Prop CSet_Prop : CSet_Prop.
  Ltac discard_nonCSet :=
    repeat (
      match goal with
      | H : context [ @Logic.eq ?T ?x ?y ] |- _ =>
        tryif (change T with E.t in H) then fail
        else tryif (change T with t in H) then fail
        else clear H
      | H : ?P |- _ =>
        tryif prop (CSet_Prop P) holds by
          (auto 100 with CSet_Prop)
        then fail
        else clear H
      end).

  (** ** Turning Set Operators into Propositional Connectives
      The lemmas from [CSetFacts] will be used to break down
      set operations into propositional formulas built over
      the predicates [In] and [E.eq] applied
      only to variables.  We are going to use them with
      [autorewrite].
      *)

  Hint Rewrite
    CSetFacts.empty_iff CSetFacts.universe_iff
    CSetFacts.singleton_iff CSetFacts.cosingleton_iff
    CSetFacts.add_iff CSetFacts.remove_iff
    CSetFacts.union_iff CSetFacts.inter_iff
    CSetFacts.diff_iff
  : set_simpl.

  Lemma eq_refl_iff (x : elt) : x = x <-> True.
  Proof.
   now split.
  Qed.

  Hint Rewrite eq_refl_iff : set_eq_simpl.

  Lemma Logical_eq_iff_Equal : forall t1 t2,
      t1 = t2 <-> Equal t1 t2.
  Proof.
    split.
    - intro; subst; apply reflexivity.
    - apply eq_leibniz.
  Qed.

  Hint Rewrite Logical_eq_iff_Equal : Logical_eq_iff_Equal.

  (** ** Decidability of CSet Propositions *)

  (** [In] is decidable. *)
  Lemma dec_In : forall x s,
    decidable (In x s).
  Proof.
    red; intros; generalize (CSetFacts.mem_iff s x);
      case (mem x s); intuition.
  Qed.

  (** element equality is decidable. *)
  Lemma dec_eq : forall (x y : elt),
    decidable (x = y).
  Proof.
    red; intros x y; destruct (E.eq_dec x y); auto.
  Qed.

  (** The hint database [CSet_decidability] will be given to
      the [push_neg] tactic from the module [Negation]. *)
  Hint Resolve dec_In dec_eq : CSet_decidability.

  (** ** Normalizing Propositions About Equality
      We have to deal with the fact that [E.eq] may be
      convertible with Coq's equality.  Thus, we will find the
      following tactics useful to replace one form with the
      other everywhere. *)

  (** The next tactic, [Logic_eq_to_E_eq], mentions the term
      [E.t]; thus, we must ensure that [E.t] is used in favor
      of any other convertible but syntactically distinct
      term. *)
  Ltac change_to_E_t :=
    repeat (
      match goal with
      | H : ?T |- _ =>
        progress (change T with E.t in H);
        repeat (
          match goal with
          | J : _ |- _ => progress (change T with E.t in J)
          | |- _ => progress (change T with E.t)
          end )
      | H : forall x : ?T, _ |- _ =>
        progress (change T with E.t in H);
        repeat (
          match goal with
          | J : _ |- _ => progress (change T with E.t in J)
          | |- _ => progress (change T with E.t)
          end )
      | |- exists x : ?T, _ =>
        progress (change T with E.t);
        repeat (
          match goal with
          | J : _ |- _ => progress (change T with E.t in J)
          end )
     end).

  (** These two tactics take us from Coq's built-in equality
      to [E.eq] (and vice versa) when possible. *)

  Ltac Logic_eq_to_E_eq :=
    repeat (
      match goal with
      | H: _ |- _ =>
        progress (change (@Logic.eq E.t) with E.eq in H)
      | |- _ =>
        progress (change (@Logic.eq E.t) with E.eq)
      end).

  Ltac E_eq_to_Logic_eq :=
    repeat (
      match goal with
      | H: _ |- _ =>
        progress (change E.eq with (@Logic.eq E.t) in H)
      | |- _ =>
        progress (change E.eq with (@Logic.eq E.t))
      end).

  (** This tactic works like the built-in tactic [subst], but
      at the level of set element equality (which may not be
      the convertible with Coq's equality). *)
  Ltac substCSet :=
    repeat (
      match goal with
      | H: E.eq ?x ?x |- _ => clear H
      | H: E.eq ?x ?y |- _ => rewrite H in *; clear H
      end);
    autorewrite with set_eq_simpl in *.

  (** ** Considering Decidability of Base Propositions
      This tactic adds assertions about the decidability of
      [E.eq] and [In] to the context.  This is necessary for
      the completeness of the [fsetdec] tactic.  However, in
      order to minimize the cost of proof search, we should be
      careful to not add more than we need.  Once negations
      have been pushed to the leaves of the propositions, we
      only need to worry about decidability for those base
      propositions that appear in a negated form. *)
  Ltac assert_decidability :=
    (** We actually don't want these rules to fire if the
        syntactic context in the patterns below is trivially
        empty, but we'll just do some clean-up at the
        afterward.  *)
    repeat (
      match goal with
      | H: context [~ E.eq ?x ?y] |- _ =>
        assert new (E.eq x y \/ ~ E.eq x y) by (apply dec_eq)
      | H: context [~ In ?x ?s] |- _ =>
        assert new (In x s \/ ~ In x s) by (apply dec_In)
      | |- context [~ E.eq ?x ?y] =>
        assert new (E.eq x y \/ ~ E.eq x y) by (apply dec_eq)
      | |- context [~ In ?x ?s] =>
        assert new (In x s \/ ~ In x s) by (apply dec_In)
      end);
    (** Now we eliminate the useless facts we added (because
        they would likely be very harmful to performance). *)
    repeat (
      match goal with
      | _: ~ ?P, H : ?P \/ ~ ?P |- _ => clear H
      end).

  Ltac inList x xs :=
    match xs with
    | tt => constr:false
    | (x, _) => constr:true
    | (_, ?xs') => inList x xs'
    end.

  Ltac inst_exists_rec xs :=
    match goal with
    | _ : context [ In ?x _ ] |-_ => add_inst_exists x xs
    | _ : context [ E.eq ?x _ ] |- _ => add_inst_exists x xs
    | _ : context [ E.eq _ ?x ] |- _ => add_inst_exists x xs
    | _ => idtac
    end
    with add_inst_exists x xs :=
      let b := inList x xs in
      match b with
      | true => fail 1
      | false =>
        match goal with
        | |- exists y : E.t, @?G y =>
          let H  := fresh "H" in
          enough ((exists y, G y) \/ G x) as H
              by (destruct H; [assumption | exists x; assumption])
        | |- (exists y : E.t, @?G1 y) \/ ?G2 =>
          let H  := fresh "H" in
          enough ((exists y, G1 y) \/ (G1 x \/ G2)) as H
              by (destruct H as [? | [? | ?]];
                  [left; assumption
                  |left; exists x; assumption
                  | right; assumption])
        end;
        inst_exists_rec (x, xs)
      end.

  Ltac inst_exists :=
    match goal with
    | |- exists y : E.t, _ =>
      inst_exists_rec tt;
      match goal with
      | |- _ \/ _ => right
      | |- exists y : E.t, _ => exists 0
      | _ => idtac
      end
    | _ => idtac
    end.

  (** ** Handling [Empty], [Subset], and [Equal]
      This tactic instantiates universally quantified
      hypotheses (which arise from the unfolding of [Empty],
      [Subset], and [Equal]) for each of the set element
      expressions that is involved in some membership or
      equality fact.  Then it throws away those hypotheses,
      which should no longer be needed. *)
  Inductive Relevant : E.t -> Prop :=
    | Relevant_c : forall x, Relevant x.

  Ltac inst_CSet_hypotheses :=
    repeat (
      match goal with
      | |- context [ In ?x _ ] =>
        assert new (Relevant x) by (apply Relevant_c)
      | |- context [ E.eq ?x _ ] =>
        assert new (Relevant x) by (apply Relevant_c)
      | |- context [ E.eq _ ?x ] =>
        assert new (Relevant x) by (apply Relevant_c)
      | _ : Relevant ?x,
        H : context [ In ?x _ ] |- _ =>
        repeat
          (match type of H with
           | context [ In ?y _ ] =>
             assert new (Relevant y) by (apply Relevant_c)
           | context [ E.eq ?y _ ] =>
             assert new (Relevant y) by (apply Relevant_c)
           | context [ E.eq _ ?y ] =>
             assert new (Relevant y) by (apply Relevant_c)
           end)
      | _ : Relevant ?x,
        H : context [ E.eq ?x _ ] |- _ =>
        repeat
          (match type of H with
           | context [ In ?y _ ] =>
             assert new (Relevant y) by (apply Relevant_c)
           | context [ E.eq ?y _ ] =>
             assert new (Relevant y) by (apply Relevant_c)
           | context [ E.eq _ ?y ] =>
             assert new (Relevant y) by (apply Relevant_c)
           end)
      | _ : Relevant ?x,
        H : context [ E.eq _ ?x ] |- _ =>
        repeat
          (match type of H with
           | context [ In ?y _ ] =>
             assert new (Relevant y) by (apply Relevant_c)
           | context [ E.eq ?y _ ] =>
             assert new (Relevant y) by (apply Relevant_c)
           | context [ E.eq _ ?y ] =>
             assert new (Relevant y) by (apply Relevant_c)
           end)
      end);
    repeat (
      match goal with
      | H : forall a : E.t, _,
        _ : Relevant ?x |- _ =>
        let P := type of (H x) in
        assert new P by (exact (H x))
      end);
    repeat (
      match goal with
      | H : forall a : E.t, _ |- _ =>
        clear H
      | H : Relevant _ |- _ =>
        clear H
      end).

  Local Lemma in_singleton : forall x, In x (singleton x).
  Proof. intro x. rewrite singleton_spec. reflexivity. Qed.

  Local Lemma not_in_singleton : forall x, ~ In (S x) (singleton x).
  Proof.
    intro x. rewrite singleton_spec.
    intro. apply (n_Sn x). symmetry. assumption.
  Qed.

  Local Lemma in_cosingleton : forall x, In (S x) (cosingleton x).
  Proof.
    intro x. rewrite cosingleton_spec.
    intro. apply (n_Sn x). symmetry. assumption.
  Qed.

  Local Lemma not_in_cosingleton : forall x, ~ In x (cosingleton x).
  Proof.
    intro x. rewrite cosingleton_spec.
    intro H. contradict H. reflexivity.
  Qed.

  Ltac add_in_constants :=
    repeat (
        match goal with
        | _ : context [ singleton ?x ] |- _ =>
          assert new (In x (singleton x))
            by (apply in_singleton)
        | _ : context [ singleton ?x ] |- _ =>
          assert new (~ In (S x) (singleton x))
            by (apply not_in_singleton)
        | |- context [ singleton ?x ] =>
          assert new (In x (singleton x))
            by (apply in_singleton)
        | |- context [ singleton ?x ] =>
          assert new (~ In (S x) (singleton x))
            by (apply not_in_singleton)
        | _ : context [ cosingleton ?x ] |- _ =>
          assert new (In (S x) (cosingleton x))
            by (apply in_cosingleton)
        | _ : context [ cosingleton ?x ] |- _ =>
          assert new (~ In x (cosingleton x))
            by (apply not_in_cosingleton)
        | |- context [ cosingleton ?x ] =>
          assert new (In (S x) (cosingleton x))
            by (apply in_cosingleton)
        | |- context [ cosingleton ?x ] =>
          assert new (~ In x (cosingleton x))
            by (apply not_in_cosingleton)
        | _ : context [ universe ] |- _ =>
          assert new (In 0 universe) by (apply universe_spec)
        | |- context [ universe ] =>
          assert new (In 0 universe) by (apply universe_spec)
        | _ : context [ empty ] |- _ =>
          assert new (~ In 0 empty) by (apply empty_spec)
        | |- context [ empty ] =>
          assert new (~ In 0 empty) by (apply empty_spec)
        end ).

  (** ** The Core [fsetdec] Auxiliary Tactics *)

  (** Here is the crux of the proof search.  Recursion through
      [intuition]!  (This will terminate if I correctly
      understand the behavior of [intuition].) *)
  Ltac csetdec_rec := progress substCSet; intuition csetdec_rec.

  (** If we add [unfold Empty, Subset, Equal in *; intros;] to
      the beginning of this tactic, it will satisfy the same
      specification as the [fsetdec] tactic; however, it will
      be much slower than necessary without the pre-processing
      done by the wrapper tactic [fsetdec]. *)
  Ltac csetdec_body :=
    autorewrite with set_eq_simpl in *;
    inst_exists;
    inst_CSet_hypotheses;
    autorewrite with set_simpl set_eq_simpl in *;
    push not in * using CSet_decidability;
    substCSet;
    assert_decidability;
    auto;
    (intuition csetdec_rec) ||
    fail 1
      "because the goal is beyond the scope of this tactic".

End CSetDecideAuxiliary.

Import CSetDecideAuxiliary.

(** * The [csetdec] Tactic
    Here is the top-level tactic (the only one intended for
    clients of this library).  It's specification is given at
    the top of the file. *)
Ltac csetdec :=
  (** We first unfold any occurrences of [iff]. *)
  unfold iff in *;
  (** We fold occurrences of [not] because it is better for
      [intros] to leave us with a goal of [~ P] than a goal of
      [False]. *)
  fold any not; intros;
  (** Rewrite logical equality to [Equal] *)
  autorewrite with Logical_eq_iff_Equal in *;
  (** We don't care about the value of elements : complex ones are
      abstracted as new variables (avoiding potential dependencies,
      see bug #2464) *)
  abstract_elements;
  (** We remove dependencies to logical hypothesis. This way,
      later "clear" will work nicely (see bug #2136) *)
  no_logical_interdep;
  (** Now we decompose conjunctions, which will allow the
      [discard_nonCSet] and [assert_decidability] tactics to
      do a much better job. *)
  decompose records;
  discard_nonCSet;
  (* Add In hypothesise for empty, universe, singelton and
     cosingleton. *)
  add_in_constants;
  (** We unfold these defined propositions on finite sets.  If
      our goal was one of them, then have one more item to
      introduce now. *)
  unfold Empty, Nonempty, Universe, Nonuniverse,
           Subset, Disjoint, Equal in *;
  intros;
  decompose records;
  (** We now want to get rid of all uses of [=] in favor of
      [E.eq].  However, the best way to eliminate a [=] is in
      the context is with [subst], so we will try that first.
      In fact, we may as well convert uses of [E.eq] into [=]
      when possible before we do [subst] so that we can even
      more mileage out of it.  Then we will convert all
      remaining uses of [=] back to [E.eq] when possible.  We
      use [change_to_E_t] to ensure that we have a canonical
      name for set elements, so that [Logic_eq_to_E_eq] will
      work properly.  *)
  change_to_E_t; E_eq_to_Logic_eq; subst++; Logic_eq_to_E_eq;
  (** The next optimization is to swap a negated goal with a
      negated hypothesis when possible.  Any swap will improve
      performance by eliminating the total number of
      negations, but we will get the maximum benefit if we
      swap the goal with a hypotheses mentioning the same set
      element, so we try that first.  If we reach the fourth
      branch below, we attempt any swap.  However, to maintain
      completeness of this tactic, we can only perform such a
      swap with a decidable proposition; hence, we first test
      whether the hypothesis is an [CSet_elt_Prop], noting
      that any [CSet_elt_Prop] is decidable. *)
  pull not using CSet_decidability;
  unfold not in *;
  match goal with
  | H: (In ?x ?r) -> False |- (In ?x ?s) -> False =>
    contradict H; csetdec_body
  | H: (In ?x ?r) -> False |- (E.eq ?x ?y) -> False =>
    contradict H; csetdec_body
  | H: (In ?x ?r) -> False |- (E.eq ?y ?x) -> False =>
    contradict H; csetdec_body
  | H: ?P -> False |- ?Q -> False =>
    tryif prop (CSet_elt_Prop P) holds by
      (auto 100 with CSet_Prop)
    then try (contradict H; csetdec_body)
    else csetdec_body
  | |- _ =>
    csetdec_body
  end.

Hint Extern 1 (CSet.Equal _ _) => csetdec : csetdec.
Hint Extern 1 (CSet.Subset _ _) => csetdec : csetdec.
Hint Extern 1 (CSet.Empty _) => csetdec : csetdec.
Hint Extern 1 (CSet.Nonempty _) => csetdec : csetdec.
Hint Extern 1 (CSet.Universe _) => csetdec : csetdec.
Hint Extern 1 (CSet.Nonuniverse _) => csetdec : csetdec.
Hint Extern 1 (CSet.Disjoint _ _) => csetdec : csetdec.
Hint Extern 1 (@Logic.eq CSet.t _ _) => csetdec : csetdec.


Module CSetDecideTestCases.

  Lemma test_eq_trans_1 : forall x y z s,
    E.eq x y ->
    ~ ~ E.eq z y ->
    In x s ->
    In z s.
  Proof. csetdec. Qed.

  Lemma test_eq_trans_2 : forall x y z r s,
    In x (singleton y) ->
    ~ In z r ->
    ~ ~ In z (add y r) ->
    In x s ->
    In z s.
  Proof. csetdec. Qed.

  Lemma test_eq_neq_trans_1 : forall w x y z s,
    E.eq x w ->
    ~ ~ E.eq x y ->
    ~ E.eq y z ->
    In w s ->
    In w (remove z s).
  Proof. csetdec. Qed.

  Lemma test_eq_neq_trans_2 : forall w x y z r1 r2 s,
    In x (singleton w) ->
    ~ In x r1 ->
    In x (add y r1) ->
    In y r2 ->
    In y (remove z r2) ->
    In w s ->
    In w (remove z s).
  Proof. csetdec. Qed.

  Lemma test_In_singleton : forall x,
    In x (singleton x).
  Proof. csetdec. Qed.

  Lemma test_add_In : forall x y s,
    In x (add y s) ->
    ~ E.eq x y ->
    In x s.
  Proof. csetdec. Qed.

  Lemma test_Subset_add_remove : forall x s,
    Subset s (add x (remove x s)).
  Proof. csetdec. Qed.

  Lemma test_eq_disjunction : forall w x y z,
    In w (add x (add y (singleton z))) ->
    E.eq w x \/ E.eq w y \/ E.eq w z.
  Proof. csetdec. Qed.

  Lemma test_not_In_disj : forall x y s1 s2 s3 s4,
    ~ In x (union s1 (union s2 (union s3 (add y s4)))) ->
    ~ (In x s1 \/ In x s4 \/ E.eq y x).
  Proof. csetdec. Qed.

  Lemma test_not_In_conj : forall x y s1 s2 s3 s4,
    ~ In x (union s1 (union s2 (union s3 (add y s4)))) ->
    ~ In x s1 /\ ~ In x s4 /\ ~ E.eq y x.
  Proof. csetdec. Qed.

  Lemma test_iff_conj : forall a x s s',
  (In a s' <-> E.eq x a \/ In a s) ->
  (In a s' <-> In a (add x s)).
  Proof. csetdec. Qed.

  Lemma test_set_ops_1 : forall x q r s,
    Subset (singleton x) s ->
    Empty (union q r) ->
    Empty (inter (diff s q) (diff s r)) ->
    ~ In x s.
  Proof.
    csetdec.
  Qed.

  Lemma eq_chain_test : forall x1 x2 x3 x4 s1 s2 s3 s4,
    Empty s1 ->
    In x2 (add x1 s1) ->
    In x3 s2 ->
    ~ In x3 (remove x2 s2) ->
    ~ In x4 s3 ->
    In x4 (add x3 s3) ->
    In x1 s4 ->
    Subset (add x4 s4) s4.
  Proof. csetdec. Qed.

  Lemma test_too_complex : forall x y z r s,
    E.eq x y ->
    (In x (singleton y) -> Subset r s) ->
    In z r ->
    In z s.
  Proof.
    (** [csetdec] is not intended to solve this directly. *)
    intros until s; intros Heq H Hr; lapply H; csetdec.
  Qed.

  Lemma function_test_1 :
    forall (f : t -> t),
    forall (g : elt -> elt),
    forall (s1 s2 : t),
    forall (x1 x2 : elt),
    Equal s1 (f s2) ->
    E.eq x1 (g (g x2)) ->
    In x1 s1 ->
    In (g (g x2)) (f s2).
  Proof. csetdec. Qed.

  Lemma function_test_2 :
    forall (f : t -> t),
    forall (g : elt -> elt),
    forall (s1 s2 : t),
    forall (x1 x2 : elt),
    Equal s1 (f s2) ->
    E.eq x1 (g x2) ->
    In x1 s1 ->
    g x2 = g (g x2) ->
    In (g (g x2)) (f s2).
  Proof.
    (** [csetdec] is not intended to solve this directly. *)
    intros until 3. intros g_eq. rewrite <- g_eq. csetdec.
  Qed.

  Lemma test_baydemir :
    forall (f : t -> t),
    forall (s : t),
    forall (x y : elt),
    In x (add y (f s)) ->
    ~ E.eq x y ->
    In x (f s).
  Proof.
    csetdec.
  Qed.

  Lemma test_equal_union :
    forall (s1 s2 : t),
    union s1 s2 = union s2 s1.
  Proof.
    csetdec.
  Qed.

End CSetDecideTestCases.
