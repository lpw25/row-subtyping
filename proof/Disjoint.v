(************************************************
 *          Row Subtyping - Disjoint            *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import List LibLN.


Lemma disjoint_empty_r : forall (A : vars),
    disjoint A \{}.
Proof.
  intros.
  unfold disjoint.
  apply inter_empty_r.
Qed.

Lemma disjoint_empty_l : forall (A : vars),
    disjoint \{} A.
Proof.
  auto using disjoint_comm, disjoint_empty_r.
Qed.

Lemma disjoint_comm_rew : forall (A B : vars),
    disjoint A B <-> disjoint B A.
Proof.
  intros.
  split; auto using disjoint_comm.
Qed.

Lemma disjoint_in_notin_l : forall (A B : vars) X,
    disjoint A B -> X \in A -> X \notin B.
Proof.
  introv Hd Hin.
  eauto using disjoint_in_notin.
Qed.

Lemma disjoint_in_notin_r : forall (A B : vars) X,
    disjoint A B -> X \in B -> X \notin A.
Proof.
  introv Hd Hin.
  eauto using disjoint_in_notin_l, disjoint_comm.
Qed.

Lemma disjoint_all_in_notin : forall (A B : vars),
    disjoint A B <-> forall X, X \in A -> X \notin B.
Proof.
  intros.
  split; introv H.
  - introv Hin.
    apply disjoint_in_notin_l with (A := A); auto.
  - unfold disjoint.
    apply fset_extens; unfold subset; intros X Hin.
    + rewrite in_inter in *.
      specialize (H X).
      exfalso.
      intuition auto.
    + rewrite in_empty in Hin.
      contradiction.
Qed.      

Lemma disjoint_union_r : forall (A B C : vars),
    disjoint A (B \u C) <-> disjoint A B /\ disjoint A C.
Proof.
  intros.
  split; introv H.
  - split;
      rewrite disjoint_all_in_notin in *;
      introv Hin;
      specialize (H X);
      intuition auto.
  - destruct H as [H1 H2].
    rewrite disjoint_all_in_notin in *.
    introv Hin.
    specialize (H1 X).
    specialize (H2 X).
    intuition auto.
Qed.

Lemma disjoint_union_r1 : forall (A B C : vars),
    disjoint A (B \u C) -> disjoint A B.
Proof.
  introv Hd.
  rewrite disjoint_union_r in Hd.
  apply (proj1 Hd).
Qed.

Lemma disjoint_union_r2 : forall (A B C : vars),
    disjoint A (B \u C) -> disjoint A C.
Proof.
  introv Hd.
  rewrite disjoint_union_r in Hd.
  apply (proj2 Hd).
Qed.

Lemma disjoint_union_l : forall (A B C : vars),
    disjoint (A \u B) C <-> disjoint A C /\ disjoint B C.
Proof.
  intros.
  rewrite disjoint_comm_rew.
  rewrite disjoint_union_r.
  intuition auto using disjoint_comm.
Qed.

Lemma disjoint_union_l1 : forall (A B C : vars),
    disjoint (A \u B) C -> disjoint A C.
Proof.
  introv Hd.
  rewrite disjoint_union_l in Hd.
  apply (proj1 Hd).
Qed.

Lemma disjoint_union_l2 : forall (A B C : vars),
    disjoint (A \u B) C -> disjoint B C.
Proof.
  introv Hd.
  rewrite disjoint_union_l in Hd.
  apply (proj2 Hd).
Qed.

Lemma disjoint_singleton_r : forall A (X : var),
    disjoint A \{X} <-> X \notin A.
Proof.
  intros.
  rewrite disjoint_all_in_notin.
  split; introv H.
  - specialize (H X).
    rewrite notin_singleton in *.
    introv Hin.
    apply H; auto.
  - introv Hin.
    rewrite notin_singleton.
    introv Heq; subst.
    auto.
Qed.

Lemma disjoint_singleton_l : forall A (X : var),
    disjoint \{X} A <-> X \notin A.
Proof.
  intros.
  rewrite disjoint_comm_rew.
  apply disjoint_singleton_r.
Qed.

Lemma disjoint_singleton_singleton : forall (X Y : var),
    disjoint \{X} \{Y} <-> X <> Y.
Proof.
  intros.
  rewrite disjoint_singleton_l.
  rewrite notin_singleton.
  reflexivity.
Qed.

Lemma disjoint_subset_l : forall (A B C : vars),
    subset A B ->
    disjoint B C ->
    disjoint A C.
Proof.    
  introv Hs Hd.
  rewrite disjoint_all_in_notin in *.
  unfold subset in Hs.
  auto.
Qed.

Lemma disjoint_subset_r : forall (A B C : vars),
    subset A B ->
    disjoint C B ->
    disjoint C A.
Proof.
  introv Hs Hd.
  rewrite disjoint_comm_rew in *.
  eauto using disjoint_subset_l.
Qed.

Lemma disjoint_from_list_nil_r : forall (A : vars),
    disjoint A (from_list nil).
Proof.
  rewrite from_list_nil.
  apply disjoint_empty_r.
Qed.

Lemma disjoint_from_list_nil_l : forall (A : vars),
    disjoint (from_list nil) A.
Proof.
  rewrite from_list_nil.
  apply disjoint_empty_l.
Qed.

Lemma disjoint_from_list_cons_r : forall (A : vars) X Xs,
    disjoint A (from_list (X :: Xs))
    <-> disjoint A \{X} /\ disjoint A (from_list Xs).
Proof.
  intros.
  rewrite from_list_cons.
  rewrite disjoint_union_r.
  reflexivity.
Qed.

Lemma disjoint_from_list_cons_l : forall (A : vars) X Xs,
    disjoint (from_list (X :: Xs)) A
    <-> disjoint \{X} A /\ disjoint (from_list Xs) A.
Proof.
  intros.
  rewrite from_list_cons.
  rewrite disjoint_union_l.
  reflexivity.
Qed.

Lemma fresh_disjoint_r : forall L n Xs,
    fresh L n Xs -> disjoint L (from_list Xs).
Proof.
  introv Hf.
  generalize dependent L.
  generalize dependent n.
  induction Xs; introv Hf; simpl in *.
  - apply disjoint_from_list_nil_r.
  - destruct n; try contradiction.
    rewrite disjoint_from_list_cons_r.
    destruct Hf.
    assert (fresh L n Xs) by auto.
    split; eauto.
    rewrite disjoint_singleton_r.
    auto.
Qed.     

Lemma fresh_disjoint_l : forall L n Xs,
    fresh L n Xs -> disjoint (from_list Xs) L.
Proof.
  introv Hf.
  eauto using disjoint_comm, fresh_disjoint_r.
Qed.

Ltac disjoint_solve_target_from L R H :=
  match type of H with
  | disjoint L R => constr:(H)
  | disjoint (?A \u ?B) ?C =>
     let H' :=
        match A with
        | context [L] => constr:(disjoint_union_l1 H)
        | _ => match B with
          | context [L] => constr:(disjoint_union_l2 H)
          | _ => fail 20
          end
        end in
     disjoint_solve_target_from L R H'
  | disjoint ?A (?B \u ?C) =>
     let H' :=
        match B with
        | context [R] => constr:(disjoint_union_r1 H)
        | _ => match C with
          | context [R] => constr:(disjoint_union_r2 H)
          | _ => fail 20
          end
        end in
     disjoint_solve_target_from L R H'
  end.

Ltac disjoint_solve_target L R :=
  match goal with
  | H: disjoint ?A ?B |- _ =>
    match A with
    | context[L] =>
      match B with
      | context[R] =>
        let F := disjoint_solve_target_from L R H in
        apply F
      end
    | context[R] =>
      match B with
      | context[L] =>
        let F := disjoint_solve_target_from R L H in
        rewrite disjoint_comm_rew;
        apply F
      end
    end
  end.

Ltac disjoint_solve_one :=
  match goal with
  | |- disjoint \{} _ =>
    apply disjoint_empty_l
  | |- disjoint _ \{} =>
    apply disjoint_empty_r
  | |- disjoint ?L ?R =>
    disjoint_solve_target L R
  end.

Ltac disjoint_solve_by_fresh :=
  match goal with
  | H : fresh _ _ ?Xs |- disjoint _ (from_list ?Xs) =>
    apply fresh_disjoint_r with (n := LibList.length Xs);
    fresh_solve
  | H : fresh _ _ ?Xs |- disjoint (from_list ?Xs) _ =>
    apply fresh_disjoint_l with (n := LibList.length Xs);
    fresh_solve
  end.

Ltac disjoint_solve_by_notin :=
  match goal with
  | H : ?X \notin _ |- disjoint _ \{?X} =>
    rewrite disjoint_singleton_r;
    notin_solve
  | H : ?X \notin _ |- disjoint \{?X} _ =>
    rewrite disjoint_singleton_l;
    notin_solve
  end.

Ltac disjoint_solve_by_neq :=
  match goal with
  | H : ?X <> ?Y |- disjoint \{?X} \{?Y} =>
    rewrite disjoint_singleton_singleton;
    apply H
  | H : ?X <> ?Y |- disjoint \{?Y} \{?X} =>
    rewrite disjoint_comm_rew;
    rewrite disjoint_singleton_singleton;
    apply H
  end.

Ltac disjoint_simpl :=
  try match goal with
  | |- disjoint _ (_ \u _) =>
        apply disjoint_union_r; split; disjoint_simpl
  | |- disjoint (_ \u _) _ =>
        apply disjoint_union_l; split; disjoint_simpl
  | |- disjoint _ (from_list (_ :: _)) =>
        apply disjoint_from_list_cons_r; split; disjoint_simpl
  | |- disjoint (from_list (_ :: _)) _ =>
        apply disjoint_from_list_cons_l; split; disjoint_simpl
  | |- disjoint (from_list nil) _ =>
        apply disjoint_from_list_nil_l
  | |- disjoint _ (from_list nil) =>
        apply disjoint_from_list_nil_r
  end.

Ltac disjoint_solve :=
  disjoint_simpl;
  first [ disjoint_solve_one
        | disjoint_solve_by_subset
        | disjoint_solve_by_fresh
        | disjoint_solve_by_notin
        | disjoint_solve_by_neq
        | idtac ]

with disjoint_solve_by_subset :=
  match goal with
  | H : subset ?A ?B |- disjoint ?A _ =>
    apply (disjoint_subset_l H);
    disjoint_solve
  | H : subset ?A ?B |- disjoint _ ?A =>
    apply (disjoint_subset_r H);
    disjoint_solve
  end.

Hint Extern 1 (disjoint _ _) => disjoint_solve.

Ltac notin_disjoint_solve :=
  match goal with
  | |- _ \notin _ =>
    apply disjoint_singleton_l;
    disjoint_solve
  end.

Hint Extern 1 (_ \notin _) => notin_disjoint_solve.
