(************************************************
 *          Row Subtyping - Utilities           *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import List LibLN Disjoint.

(* **************************************************** *)
(** Additional set lemmas *)

Lemma union_distribute : forall A (P : fset A) Q R,
    (P \u Q) \u R = (P \u R) \u (Q \u R).
Proof.
  intros.
  rewrite union_comm with (E := P).
  rewrite <- union_assoc.
  rewrite <- union_same with (E := R) at 1.
  rewrite union_assoc with (G := R).
  rewrite union_comm.
  rewrite <- union_assoc.
  rewrite union_comm with (E := R).
  reflexivity.
Qed.

Lemma notin_subset : forall A (X : A) P Q,
    X \notin Q ->
    subset P Q ->
    X \notin P.
Proof.
  unfold subset, notin, not.
  auto.
Qed.

(* **************************************************** *)
(** Lemmas about List.map *)

Lemma map_identity : forall A L,
    List.map (fun x : A => x) L = L.
Proof.
  intros.
  induction L; simpl; f_equal; auto.
Qed.

Lemma map_compose : forall A B C L (g : A -> B) (f : B -> C),
    List.map (fun x : A => f (g x)) L =
    List.map f (List.map g L).
Proof.
  intros.
  induction L; simpl; f_equal; auto.
Qed.

(* **************************************************** *)
(** Additional freshness lemmas *)

Lemma fresh_subset : forall L M n Xs,
    fresh L n Xs ->
    subset M L ->
    fresh M n Xs.
Proof.
  introv Hf Hs.
  generalize dependent M.
  generalize dependent n.
  induction Xs; introv Hf Hs; destruct n; auto; simpl in *.
  unfold subset in Hs.
  unfold notin, not in *.
  intuition auto.
Qed.

Lemma fresh_disjoint : forall L n Xs,
    fresh \{} n Xs ->
    disjoint L (from_list Xs) ->
    fresh L n Xs.
Proof.
  introv Hf Hd.
  generalize dependent L.
  generalize dependent n.
  induction Xs; introv Hf Hd; destruct n; auto; simpl in *.
  apply disjoint_from_list_cons_r in Hd.
  destruct Hd; destruct Hf.
  auto.
Qed.

Lemma fresh_length : forall L n Xs,
  fresh L n Xs -> n = length Xs.
Proof using.
  intros. gen n L. induction Xs; simpl; intros n L Fr;
    destruct n; tryfalse*.
  easy.
  f_equal.
  rewrite* <- (@IHXs n (L \u \{a})).
Qed.  

Tactic Notation "fresh_length" constr(Fr) "as" ident(H) :=
  match type of Fr with
  | fresh _ ?n ?Xs =>
    assert (n = length Xs) as H
      by apply (fresh_length _ _ _ Fr)
  | _ =>
    fail 1
      "because it is not a freshness predicate"
  end.

Lemma fresh_nil : forall L n,
  fresh L n nil -> n = 0.
Proof.
  introv Hf.
  fresh_length Hf as Hl.
  simpl in Hl.
  assumption.
Qed.

Lemma fresh_length_nil : forall A L (l : list A),
  fresh L (length l) nil -> l = nil.
Proof.
  introv Hf.
  apply fresh_nil in Hf.
  apply List.length_zero_iff_nil.
  assumption.
Qed.

Lemma fresh_from_notin : forall L X n Xs,
    fresh L n Xs ->
    X \notin (from_list Xs) ->
    fresh (L \u \{X}) n Xs.
Proof.
  introv Hf Hn.
  generalize dependent L.
  generalize dependent n.
  induction Xs; introv Hf; induction n; auto; simpl in *.
  rewrite from_list_cons in Hn.
  destruct Hf.
  split; auto.
  rewrite union_comm.
  rewrite union_assoc.
  auto.
Qed.

(* **************************************************** *)
(** Additional lemmas about environments *)

Lemma concat_assoc2 : forall A (E1 : LibEnv.env A) E2 E3 E4,
  E1 & (E2 & E3 & E4) = E1 & E2 & E3 & E4.
Proof.
  intros.
  rewrite concat_assoc.
  rewrite concat_assoc.
  reflexivity.
Qed.

Lemma binds_in_dom : forall A x (v : A) E,
  binds x v E -> x \in dom E.
Proof.
  eauto using binds_get, get_some_inv.
Qed.

Hint Rewrite singles_nil singles_cons : rew_env_concat.

(* **************************************************** *)
(** Some automation around fresh names *)

Ltac inList x xs :=
  match xs with
  | tt => constr:false
  | (x, _) => constr:true
  | (_, ?xs') => inList x xs'
  end.

Ltac spec_one_fresh x H L :=
  let Hspec := fresh "Hspec" in
  assert (Hspec := H);
  let Hn := fresh "Hn" in
  assert (x \notin L) as Hn by auto;
  specialize (Hspec x Hn);
  clear Hn.

Ltac spec_all_fresh x :=
  let rec loop Hs :=
    match goal with
    | H : forall y : var, y \notin ?L -> _ |- _ =>
      let b := inList H Hs in
      match b with
      | true => fail 1
      | false =>
        try spec_one_fresh x H L;
        loop (H, Hs)
      end
    | _ => idtac
    end
  in
  loop tt.

Ltac spec_one_freshes Xs H L n :=
  let Hspec := fresh "Hspec" in
  assert (Hspec := H);
  let Hf := fresh "Hn" in
  assert (fresh L n Xs) as Hf by auto;
  specialize (Hspec Xs Hf);
  clear Hf.

Ltac spec_all_freshes Xs n :=
  let rec inList2 x xs :=
    match xs with
    | tt => constr:false
    | (x, _) => constr:true
    | (_, ?xs') => inList2 x xs'
    end
  in
  let rec loop Hs :=
    match goal with
    | H : forall Ys : list var, fresh ?L n Ys -> _ |- _ =>
      let b := inList2 H Hs in
      match b with
      | true => fail 1
      | false =>
          try spec_one_freshes Xs H L n;
          loop (H, Hs)
      end
    | _ => idtac
    end
  in
  loop tt.

Ltac spec_fresh_gen L :=
  match goal with
  | H : forall y : var, y \notin _ -> _ |- _ =>
      let x := fresh "x" in
      let Hn := fresh "Hn" in
      let L' := beautify_fset L in
      destruct (var_fresh L') as [x Hn];
      spec_all_fresh x
  | _ => idtac
  end;
  match goal with
  | H: forall Ys : list var, fresh _ ?n Ys -> _ |- _ =>
      let Xs := fresh "Xs" in
      let Hf := fresh "Hf" in
      let L' := beautify_fset L in
      destruct (var_freshes L' n) as [Xs Hf];
      spec_all_freshes Xs n
  | _ => idtac
  end.

Ltac inst_fresh :=
  match goal with
  | |- forall Xs : list var, fresh _ ?n Xs -> _ =>
    let Xs := fresh "Xs" in
    let Hf := fresh "Hf" in
    intros Xs Hf;
    spec_all_freshes Xs n
  | |- forall x : var, x \notin _ -> _ =>
    let x := fresh "x" in
    let Hn := fresh "Hn" in
    intros x Hn;
    spec_all_fresh x
  end.

Hint Extern 1 => inst_fresh : fresh.

Ltac app_fresh :=
  match goal with
  | H : forall x, x \notin ?L -> ?P |- ?P =>
    apply (H (proj1_sig (var_fresh L)) (proj2_sig (var_fresh L)))
  | H : forall x, x \notin ?L -> ?Q -> ?P,
    Hq : ?Q |- ?P =>
    apply (H (proj1_sig (var_fresh L))
             (proj2_sig (var_fresh L)) Hq)
  | H : forall x, x \notin ?L -> ?Q1 -> ?Q2 -> ?P,
    Hq1 : ?Q1, Hq2 : ?Q2 |- ?P =>
    apply (H (proj1_sig (var_fresh L))
             (proj2_sig (var_fresh L)) Hq1 Hq2 )
  | H: forall Xs : list var,
      fresh ?L ?n Xs -> ?P |- ?P =>
    apply (H (proj1_sig (var_freshes L n))
             (proj2_sig (var_freshes L n)))
  | H : forall Xs : list var,
      fresh ?L ?n Xs -> ?Q -> ?P, Hq : ?Q |- ?P =>
    apply (H (proj1_sig (var_freshes L n))
             (proj2_sig (var_freshes L n)) Hq)
  | H : forall Xs : list var,
      fresh ?L ?n Xs -> ?Q1 -> ?Q2 -> ?P,
        Hq1 : ?Q1, Hq2 : ?Q2  |- ?P =>
    apply (H (proj1_sig (var_freshes L n))
             (proj2_sig (var_freshes L n)) Hq1 Hq2)
  end.

Hint Extern 1 => app_fresh : fresh.