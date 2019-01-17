(************************************************
 *          Row Subtyping - Utilities           *
 *                 Leo White                    *
 ************************************************)

(* General utilities *)

Set Implicit Arguments.
Require Import List LibLN Disjoint Bool Ring.

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

Lemma fresh_zero : forall L Xs,
  fresh L 0 Xs -> Xs = nil.
Proof.
  introv Hf.
  fresh_length Hf as Hl.
  symmetry in Hl.
  apply List.length_zero_iff_nil in Hl.
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

(* *************************************************************** *)
(** * Extra lemmas about the [ok] predicate *)

Lemma ok_middle : forall A E1 E2 x (v : A),
  ok (E1 & E2) ->
  x # (E1 & E2) ->
  ok (E1 & x ~ v & E2).
Proof.
  introv Hok Hn.
  induction E2 using env_ind;
    autorewrite with rew_env_concat in *;
    autorewrite with rew_env_dom in *; auto.
  destruct (ok_push_inv Hok).
  auto.
Qed.

Lemma ok_concat : forall A (E1 : LibEnv.env A) E2,
    ok E1 -> ok E2 ->
    disjoint (dom E1) (dom E2) ->
    ok (E1 & E2).
Proof.
  introv Hok1 Hok2 Hd.
  induction E2 using env_ind;
    autorewrite with rew_env_concat in *;
    autorewrite with rew_env_dom in *; auto.
  destruct (ok_push_inv Hok2).
  auto.
Qed.

Lemma ok_concat_inv : forall A (E1 : LibEnv.env A) E2,
    ok (E1 & E2) ->
    disjoint (dom E1) (dom E2) /\ ok E1 /\ ok E2.
Proof.
  introv Hok.
  splits; eauto using ok_concat_inv_l, ok_concat_inv_r.
  induction E2 using env_ind;
    autorewrite with rew_env_concat in *;
    autorewrite with rew_env_dom in *; auto.
  destruct (ok_push_inv Hok).
  autorewrite with rew_env_dom in *.
  auto.
Qed.

(* **************************************************** *)
(** Some automation around fresh names *)

Ltac inList x xs :=
  match xs with
  | tt => constr:(false)
  | (x, _) => constr:(true)
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
    | tt => constr:(false)
    | (x, _) => constr:(true)
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
  | H : forall x, x \notin ?L -> ?Q1 -> ?Q2 -> ?Q3 -> ?P,
    Hq1 : ?Q1, Hq2 : ?Q2, Hq3 : ?Q3 |- ?P =>
    apply (H (proj1_sig (var_fresh L))
             (proj2_sig (var_fresh L)) Hq1 Hq2 Hq3)
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
  | H : forall Xs : list var,
      fresh ?L ?n Xs -> ?Q1 -> ?Q2 -> ?Q3 -> ?P,
        Hq1 : ?Q1, Hq2 : ?Q2, Hq3 : ?Q3 |- ?P =>
    apply (H (proj1_sig (var_freshes L n))
             (proj2_sig (var_freshes L n)) Hq1 Hq2 Hq3)
  end.

Hint Extern 1 => app_fresh : fresh.

(* **************************************************** *)
(* Semi-ring for andb and orb *)

Lemma AndOrTheory :
  semi_ring_theory false true orb andb (eq(A:=bool)).
Proof.
  apply mk_srt; intros; Bool.destr_bool.
Qed.

Add Ring bool_ring :
  AndOrTheory (decidable bool_eq_ok, constants [bool_cst]).

Definition leb b1 b2 :=
  b1 = andb b1 b2.

Lemma leb_refl : forall b,
  leb b b.
Proof.
  intros.
  unfold leb.
  destruct b; auto.
Qed.

Lemma leb_lower_bound_l : forall b1 b2,
  leb (andb b1 b2) b1.
Proof.
  intros.
  unfold leb.
  destruct b1; destruct b2; auto.
Qed.

Lemma leb_lower_bound_r : forall b1 b2,
  leb (andb b1 b2) b2.
Proof.
  intros.
  unfold leb.
  destruct b1; destruct b2; auto.
Qed.

Lemma leb_upper_bound_l : forall b1 b2,
  leb b1 (orb b1 b2).
Proof.
  intros.
  unfold leb.
  destruct b1; destruct b2; auto.
Qed.

Lemma leb_upper_bound_r : forall b1 b2,
  leb b2 (orb b1 b2).
Proof.
  intros.
  unfold leb.
  destruct b1; destruct b2; auto.
Qed.

Lemma andb_orb_distribution : forall b1 b2 b3,
    b1 && (b2 || b3) =
    (b1 && b2) || (b1 && b3).
Proof.
  intros.
  ring.
Qed.

Lemma leb_false : forall b,
    leb b false ->
    b = false.
Proof.
  introv Hl.
  destruct b; auto.
Qed.