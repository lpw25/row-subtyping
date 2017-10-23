(************************************************
 *          Row Subtyping - Subtyping           *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import LibLN Definitions Infrastructure Kinding.

(* *************************************************************** *)
(** * Properties of type equality *)

(* *************************************************************** *)
(** Transitivity *)

Lemma type_equal_trans : forall E T1 T2 T3 K,
    type_equal E T1 T2 K ->
    type_equal E T2 T3 K ->
    type_equal E T1 T3 K.
Proof.
  introv He.
  induction He; eauto.
Qed.

(* *************************************************************** *)
(** Well-kindedness *)

Lemma type_equal_step_kinding : forall E T1 T2,
    type_equal_step E T1 T2 ->
    (forall K, kinding E T1 K -> kinding E T2 K)
    /\ (forall K, kinding E T2 K -> kinding E T1 K).
Proof.
  introv Hs.
  induction Hs;
    split; intuition auto;
      invert_kinding; eauto;
        eauto with constrs.
Qed.

Lemma type_equal_kinding : forall E T1 T2 K,
    type_equal E T1 T2 K ->
    kinding E T1 K /\ kinding E T2 K.
Proof.
  introv He.
  induction He; intuition auto.
  - apply type_equal_step_kinding in H.
    intuition auto.
  - apply type_equal_step_kinding in H.
    intuition auto.
Qed.

Hint Extern 1 (kinding ?E ?T ?K) =>
  match goal with
  | H: type_equal E T _ K |- _ =>
      apply (proj1 (type_equal_kinding H))
  | H: type_equal E _ T K |- _ =>
      apply (proj2 (type_equal_kinding H))
  end : kinding.

(* *************************************************************** *)
(** Symmetry *)

Lemma type_equal_symm : forall E T1 T2 K,
    type_equal E T1 T2 K ->
    type_equal E T2 T1 K.
Proof.
  introv He.
  induction He; auto.
  - destruct (type_equal_step_kinding H).
    destruct (type_equal_kinding He).
    eapply type_equal_trans; eauto.
  - destruct (type_equal_step_kinding H).
    destruct (type_equal_kinding He).
    eapply type_equal_trans; eauto.
Qed.

(* *************************************************************** *)
(** Single steps *)

Lemma type_equal_single_l : forall E T1 T2 K,
    kinding E T2 K ->
    type_equal_step E T1 T2 ->
    type_equal E T1 T2 K.
Proof.
  introv Hk Hs.
  eauto.
Qed.

Lemma type_equal_single_r : forall E T1 T2 K,
    kinding E T1 K ->
    type_equal_step E T1 T2 ->
    type_equal E T2 T1 K.
Proof.
  introv Hk Hs.
  eauto.
Qed.

(* *************************************************************** *)
(** Congruence *)

Lemma type_equal_constructor : forall E c T1 T1' K,
    type_equal E T1 T1' knd_type ->
    K = knd_row (cons_finite \{c}) ->
    type_equal E (typ_constructor c T1) (typ_constructor c T1') K.
Proof.
  introv He Hkeq.
  gen_eq K' : knd_type.
  induction He; intros; subst; eauto with kinding.
Qed.
  
Lemma type_equal_or : forall E T1 T1' T2 T2' cs1 cs2 K,
      type_equal E T1 T1' (knd_row cs1) ->
      type_equal E T2 T2' (knd_row cs2) ->
      cons_disjoint cs1 cs2 ->
      K = knd_row (cons_union cs1 cs2) ->
      type_equal E (typ_or T1 T2) (typ_or T1' T2') K.
Proof.
  introv He1 He2 Hdis Hkeq.
  apply type_equal_trans with (typ_or T1' T2).
  - gen_eq K' : (knd_row cs1).
    induction He1; intros; subst; eauto with kinding.
  - gen_eq K' : (knd_row cs2).
    induction He2; intros; subst; eauto with kinding.
Qed.

Lemma type_equal_variant : forall E T1 T1' T2 T2' K,
      type_equal E T1 T1' (knd_row cons_universe) ->
      type_equal E T2 T2' (knd_row cons_universe) ->
      K = knd_type ->
      type_equal E (typ_variant T1 T2) (typ_variant T1' T2') K.
Proof.
  introv He1 He2 Hkeq.
  apply type_equal_trans with (typ_variant T1' T2).
  - gen_eq K' : (knd_row cons_universe).
    induction He1; intros; subst; eauto with kinding.
  - gen_eq K' : (knd_row cons_universe).
    induction He2; intros; subst; eauto with kinding.
Qed.

Lemma type_equal_arrow : forall E T1 T1' T2 T2' K,
      type_equal E T1 T1' knd_type ->
      type_equal E T2 T2' knd_type ->
      K = knd_type ->
      type_equal E (typ_arrow T1 T2) (typ_arrow T1' T2') K.
Proof.
  introv He1 He2 Hkeq.
  apply type_equal_trans with (typ_arrow T1' T2).
  - gen_eq K' : knd_type.
    induction He1; intros; subst; eauto with kinding.
  - gen_eq K' : knd_type.
    induction He2; intros; subst; eauto with kinding.
Qed.

Lemma type_equal_meet : forall E T1 T1' T2 T2' K,
      type_equal E T1 T1' K ->
      type_equal E T2 T2' K ->
      is_row_kind K ->
      type_equal E (typ_meet T1 T2) (typ_meet T1' T2') K.
Proof.
  introv He1 He2 Hkeq.
  apply type_equal_trans with (typ_meet T1' T2).
  - induction He1; intros; subst; eauto with kinding.
  - induction He2; intros; subst; eauto with kinding.
Qed.

Lemma type_equal_join : forall E T1 T1' T2 T2' K,
      type_equal E T1 T1' K ->
      type_equal E T2 T2' K ->
      is_row_kind K ->
      type_equal E (typ_join T1 T2) (typ_join T1' T2') K.
Proof.
  introv He1 He2 Hkeq.
  apply type_equal_trans with (typ_join T1' T2).
  - induction He1; intros; subst; eauto with kinding.
  - induction He2; intros; subst; eauto with kinding.
Qed.

(* *************************************************************** *)
(** Idempotence of join and meet *)

Lemma type_equal_join_idempotent : forall E T cs,
    kinding E T (knd_row cs) ->
    type_equal E (typ_join T T) T (knd_row cs).
Proof.
  introv Hk.
  eapply type_equal_step_l
    with (typ_join T (typ_meet T (typ_top cs))).
  - eauto 8 with kinding.
  - eapply type_equal_single_r; eauto 10 with kinding.
Qed.    

Lemma type_equal_meet_idempotent : forall E T cs,
    kinding E T (knd_row cs) ->
    type_equal E (typ_meet T T) T (knd_row cs).
Proof.
  introv Hk.
  eapply type_equal_step_l
    with (typ_meet T (typ_join T (typ_bot cs))).
  - eauto 8 with kinding.
  - eapply type_equal_single_r; eauto 10 with kinding.
Qed.

Hint Resolve type_equal_join_idempotent.
Hint Resolve type_equal_meet_idempotent.

(* *************************************************************** *)
(** Not affected by type bindings *)

Lemma type_equal_step_bind_typ : forall E F T1 T2 x S,
    type_equal_step (E & x ~: S & F) T1 T2 ->
    type_equal_step (E & F) T1 T2.
Proof.
  introv Hs.
  gen_eq G : (E & x ~: S & F).
  induction Hs; intros; subst; eauto with bind_typ.
Qed.  

Lemma type_equal_bind_typ : forall E F T1 T2 K x S,
    type_equal (E & x ~: S & F) T1 T2 K ->
    type_equal (E & F) T1 T2 K.
Proof.
  introv He.
  gen_eq G : (E & x ~: S & F).
  induction He; intros; subst;
    eauto using type_equal_step_bind_typ with bind_typ.
Qed.  

(* *************************************************************** *)
(** Preserved by type substitution *)

Lemma type_equal_step_typ_subst : forall E F X T1 T2 S J,
  type_equal_step (E & X ~:: J & F) T1 T2 -> 
  kinding E S J -> 
  type_equal_step (E & (environment_subst X S F))
             (typ_subst X S T1) (typ_subst X S T2).
Proof.
  introv Hs Hk.
  gen_eq G: (E & X ~:: J & F).
  induction Hs; intros; subst; simpl typ_subst; auto;
    do 2 match goal with
    | H : kinding (E & X ~:: J & F) ?T1 _ |- _ =>
      apply kinding_typ_subst with (T := T1) (E := E) (S := S) in H
    end;
    eauto.
Qed.

Hint Resolve type_equal_step_typ_subst : typ_subst.

Lemma type_equal_typ_subst : forall E F X T1 T2 S K J,
  type_equal (E & X ~:: J & F) T1 T2 K -> 
  kinding E S J -> 
  type_equal (E & (environment_subst X S F))
             (typ_subst X S T1) (typ_subst X S T2) K.
Proof.
  introv Hkt Hks.
  gen_eq G: (E & X ~:: J & F).
  inductions Hkt; intros; subst; eauto with typ_subst.
Qed.

Hint Resolve type_equal_typ_subst : typ_subst.

(* *************************************************************** *)
(** Weakening *)

Lemma type_equal_step_weakening : forall E F G T1 T2,
   type_equal_step (E & G) T1 T2 -> 
   environment (E & F & G) ->
   type_equal_step (E & F & G) T1 T2.
Proof.
  introv Hs Henv.
  gen_eq D: (E & G).
  induction Hs; intros; subst; eauto with weaken.
Qed.

Hint Resolve type_equal_step_weakening : weaken.

Lemma type_equal_weakening : forall E F G T1 T2 K,
   type_equal (E & G) T1 T2 K -> 
   environment (E & F & G) ->
   type_equal (E & F & G) T1 T2 K.
Proof.
  introv Heq Henv.
  gen_eq D: (E & G).
  induction Heq; intros; subst; eauto with weaken.
Qed.

Hint Resolve type_equal_weakening : weaken.

(* *************************************************************** *)
(** Kind can be replaced *)

Lemma type_equal_replace_kind : forall E T1 T2 K1 K2,
    kinding E T1 K1 ->
    type_equal E T1 T2 K2 ->
    type_equal E T1 T2 K1.
Proof.
  introv Hk He.
  replace K1 with K2
    by eauto using kinding_unique with kinding.
  assumption.
Qed.    

(* *************************************************************** *)
(** * Properties of Subtyping *)

(* *************************************************************** *)
(** Reflexivity *)

Lemma subtype_refl : forall E T,
  kinding E T (knd_row cons_universe) -> 
  subtype E T T.
Proof.
  introv Hk.
  unfold subtype; auto using type_equal_symm.
Qed.

(* *************************************************************** *)
(** Transitivity *)

Lemma subtype_trans : forall E T1 T2 T3,
    subtype E T1 T2 ->
    subtype E T2 T3 ->
    subtype E T1 T3.
Proof.
  introv H12 H23.
  unfold subtype in *.
  assert (kinding E T1 (knd_row cons_universe))
    by eauto with kinding.
  assert (kinding E T2 (knd_row cons_universe))
    by eauto with kinding.
  assert (kinding E T3 (knd_row cons_universe)).
  { assert (kinding E (typ_meet T2 T3) (knd_row cons_universe))
      as Hk by eauto with kinding.
    inversion Hk; subst.
    inversion H7; subst.
    auto. }
  apply type_equal_trans with (typ_meet T1 T2); auto.
  apply type_equal_trans with (typ_meet T1 (typ_meet T2 T3));
    eauto using type_equal_meet.
  apply type_equal_trans with (typ_meet (typ_meet T1 T2) T3);
    eauto using type_equal_single_l with kinding.
  eauto 6 using type_equal_meet, type_equal_symm.
Qed.

(* *************************************************************** *)
(** Anti-symmetry *)

Lemma subtype_antisymm : forall E T1 T2,
    subtype E T1 T2 ->
    subtype E T2 T1 ->
    type_equal E T1 T2 (knd_row cons_universe).
Proof.
  introv H12 H21.
  unfold subtype in *.
  apply type_equal_trans with (typ_meet T1 T2); auto.
  apply type_equal_trans with (typ_meet T2 T1);
    auto using type_equal_symm.
  eauto with kinding.
Qed.

(* *************************************************************** *)
(* Well-kindedness *)

Lemma subtype_kinding : forall E T1 T2,
    subtype E T1 T2 ->
    kinding E T1 (knd_row cons_universe)
    /\ kinding E T2 (knd_row cons_universe).
Proof.
  introv He.
  destruct (type_equal_kinding He) as [ Hk Hj ].
  split; auto.
  inversion Hj; subst.
  inversion H5; subst.
  auto.
Qed.

Hint Extern 1 (kinding ?E ?T (knd_row cons_universe)) =>
  match goal with
  | H: subtype E T _ |- _ =>
      apply (proj1 (subtype_kinding H))
  | H: subtype E _ T |- _ =>
      apply (proj2 (subtype_kinding H))
  end : kinding.

(* *************************************************************** *)
(** Weakening *)

Lemma subtype_weakening : forall E F G T1 T2,
   subtype (E & G) T1 T2 -> 
   environment (E & F & G) ->
   subtype (E & F & G) T1 T2.
Proof.
  introv Hs He.
  apply type_equal_weakening; auto.
Qed.

Hint Resolve subtype_weakening : weaken.

(* *************************************************************** *)
(** Not affected by type bindings *)

Lemma subtype_bind_typ : forall E F T1 T2 x S,
    subtype (E & x ~: S & F) T1 T2 ->
    subtype (E & F) T1 T2.
Proof.
  unfold subtype.
  introv He.
  eapply type_equal_bind_typ.
  apply He.
Qed.  

Hint Resolve subtype_bind_typ : bind_typ.

(* *************************************************************** *)
(** Preserved by type substitution *)

Lemma subtype_typ_subst : forall E F X T1 T2 S J,
  subtype (E & X ~:: J & F) T1 T2 -> 
  kinding E S J -> 
  subtype (E & (environment_subst X S F))
          (typ_subst X S T1) (typ_subst X S T2).
Proof.
  unfold subtype.
  introv Hs Hk.
  lets H : (type_equal_typ_subst Hs Hk).
  simpl in H.
  auto.
Qed.

Hint Resolve subtype_typ_subst : typ_subst.

(* *************************************************************** *)
(* Let's try projection as a function *)
(*
Fixpoint projection (env : env) (cs : constructors) (t : typ)
  : option (option typ) :=
  match t with
  | typ_bvar _ => None
  | typ_fvar v =>
      match EnvOps.get v env with
      | None => None
      | Some (bind_typ _) => None
      | Some (bind_knd knd_type) => None
      | Some (bind_knd (knd_row cs')) =>
          match cons_subset cs' cs with
          | True => Some (Some t)
          | False =>
            let cs'' := cons_inter cs cs' in
            match cons_non_empty cs'' with
            | True => None
            | False => Some None
            end
          end
      end
  | typ_constructor c _ =>
      match mem c cs with
      | True => Some (Some t)
      | _ => Some None
      end
  | typ_or t1 t2 =>
      match projection t1, projection t2 with
      | Some (Some p1), Some (Some p2) => Some (Some (typ_or p1 p2))
      | Some (Some p), Some None => Some (Some p)
      | Some None, Some (Some p) => Some (Some p)
      | Some None, Some None => Some None
      | _, _ => None
      end
  | typ_variant _ _ => None
  | typ_arrow _ _ => None
  | typ_top cs' =>
      let cs'' := cons_inter cs cs' in
      match cons_non_empty cs'' with
      | True => Some (Some (typ_top cs''))
      | False => Some None
      end
  | typ_bot cs' =>
      let cs'' := cons_inter cs cs' in
      match cons_non_empty cs'' with
      | True => Some (Some (typ_bot cs''))
      | False => Some None
      end
  | typ_meet t1 t2 =>
      match projection t1, projection t2 with
      | Some (Some p1), Some (Some p2) => Some (Some (typ_meet p1 p2))
      | Some None, Some None => Some None
      | _, _ => None
      end
  | typ_join t1 t2 =>
      match projection t1, projection t2 with
      | Some (Some p1), Some (Some p2) => Some (Some (typ_join p1 p2))
      | Some None, Some None => Some None
      | _, _ => None
      end
  end.
*)

(* *************************************************************** *)
(** TODO: Describe and rename these lemmas *)

Inductive row_projection : env -> typ -> constructors ->
                           typ -> constructors -> Prop :=
  | row_projection_var : forall E cs X,
      row_projection E (typ_fvar X) cs (typ_fvar X) cs
  | row_projection_constructor : forall E c cs T,
      row_projection E (typ_constructor c T) cs
                       (typ_constructor c T) cs
  | row_projection_or : forall E cs1 cs2 cs3 cs4 T1 T2 T,
      kinding E T1 (knd_row cs3) ->
      kinding E T2 (knd_row cs4) ->
      or_projection E T1 cs3 T2 cs4 T cs1 ->
      row_projection E (typ_or T1 T2) cs2 T cs1
  | row_projection_meet : forall E cs1 cs2 T1 T2 T3 T4,
      row_projection E T1 cs2 T3 cs1 ->
      row_projection E T2 cs2 T4 cs1 ->
      row_projection E (typ_meet T1 T2) cs2 (typ_meet T3 T4) cs1
  | row_projection_join : forall E cs1 cs2 T1 T2 T3 T4,
      row_projection E T1 cs2 T3 cs1 ->
      row_projection E T2 cs2 T4 cs1 ->
      row_projection E (typ_join T1 T2) cs2 (typ_join T3 T4) cs1
  | row_projection_bot : forall E cs1 cs2,
      kinding E (typ_bot cs1) (knd_row cs1) ->
      cons_subset cs1 cs2 ->
      row_projection E (typ_bot cs2) cs2 (typ_bot cs1) cs1
  | row_projection_top : forall E cs1 cs2,
      kinding E (typ_top cs1) (knd_row cs1) ->
      cons_subset cs1 cs2 ->
      row_projection E (typ_top cs2) cs2 (typ_top cs1) cs1

with or_projection : env ->
                     typ -> constructors ->
                     typ -> constructors ->
                     typ -> constructors -> Prop :=
  | or_left : forall E T1 cs1 T2 cs2 T cs,
      cons_subset cs cs1 ->
      row_projection E T1 cs1 T cs ->
      or_projection E T1 cs1 T2 cs2 T cs
  | or_right : forall E T1 cs1 T2 cs2 T cs,
      cons_subset cs cs2 ->
      row_projection E T2 cs2 T cs ->
      or_projection E T1 cs1 T2 cs2 T cs
  | or_both : forall E T1 cs1 T2 cs2 T1' T2' cs,
      cons_non_empty (cons_inter cs cs1) ->
      cons_non_empty (cons_inter cs cs2) ->
      cs = (cons_union (cons_inter cs cs1) (cons_inter cs cs2)) ->
      row_projection E T1 cs1 T1' (cons_inter cs cs1) ->
      row_projection E T2 cs2 T2' (cons_inter cs cs2) ->
      or_projection E T1 cs1 T2 cs2 (typ_or T1' T2') cs.

Hint Constructors row_projection or_projection.

Scheme row_projection_mut := Induction for row_projection Sort Prop
  with or_projection_mut := Induction for or_projection Sort Prop.

Combined Scheme projection_mut from
         row_projection_mut, or_projection_mut.

Lemma row_projection_identity_ind : forall E cs1 cs2 T,
    kinding E T (knd_row cs1) ->
    cs1 = cs2 ->
    row_projection E T cs1 T cs2.
Proof.
  introv Hk.
  gen_eq K : (knd_row cs1).
  gen cs1 cs2.
  induction Hk; introv Hknd Heq; subst; auto;
    inversion Hknd; subst; auto;
    invert_kind; eauto with constrs.
Qed.    

Lemma row_projection_identity : forall E cs T,
    kinding E T (knd_row cs) ->
    row_projection E T cs T cs.
Proof.
  introv Hknd.
  apply row_projection_identity_ind; auto.
Qed.

Lemma row_projection_kinding_mut :
    (forall E T cs T' cs',
    kinding E T (knd_row cs) ->
    row_projection E T cs T' cs' ->
    kinding E T' (knd_row cs'))
/\ (forall E T1 cs1 T2 cs2 T' cs',
    kinding E T1 (knd_row cs1) ->
    kinding E T2 (knd_row cs2) ->
    kinding E (typ_or T1 T2) (knd_row (cons_union cs1 cs2)) ->
    or_projection E T1 cs1 T2 cs2 T' cs' ->
    kinding E T' (knd_row cs')).
Proof.
  apply projection_mut; intros; substs; intuition auto with constrs.
  - rewrite e.
    auto with constrs.
Qed.

Definition row_projection_kinding :=
  proj1 row_projection_kinding_mut.

Hint Resolve row_projection_kinding.

Lemma row_projection_idem : forall E cs T T',
    row_projection E T (knd_row cs) cs T' ->
    T = T'.
Proof.
  introv Hpr.
  gen_eq K : (knd_row cs).
  induction Hpr; intro; auto.
  - assert (cons_non_empty cs3) by auto.
    apply row_projection_kinding in Hpr.
    assert (cons_non_empty cs2) by iauto.
    inversion H2; subst.
    false.
    constrs.
  - assert (cons_non_empty cs2) by auto.
    apply row_projection_kinding in Hpr.
    assert (cons_non_empty cs3) by iauto.
    inversion H2; subst.
    false.
    constrs.
  - inversion H3; subst.
    replace T1' with T1
      by auto with constrs.
    replace T2' with T2
      by auto with constrs.
    auto.
  - replace T3 with T1 by auto.
    replace T4 with T2 by auto.
    auto.
  - replace T3 with T1 by auto.
    replace T4 with T2 by auto.
    auto.
  - inversion H2.
    auto.
  - inversion H2.
    auto.
Qed.

Ltac equal_kinds :=
  repeat
    match goal with
    | [ Hr : row_projection ?E ?T (knd_row ?cs) _ _ |- _ ] =>
      match goal with
      | [ Hk : kinding E T (knd_row cs) |- _ ] =>
        fail 1
      | _ =>
        let Hk := fresh "Hk" in
        assert (kinding E T (knd_row cs)) as Hk
            by (apply (proj1 (row_projection_kinding Hr)))
      end
    | [ He : type_equal ?E ?T _ (knd_row ?cs) |- _ ] =>
      match goal with
      | [ Hk : kinding E T (knd_row cs) |- _ ] =>
        fail 1
      | _ =>
        let Hk := fresh "Hk" in
        assert (kinding E T (knd_row cs)) as Hk
            by (apply (proj1 (type_equal_kinding He)))
      end
    | [ He : type_equal ?E _ ?T (knd_row ?cs) |- _ ] =>
      match goal with
      | [ Hk : kinding E T (knd_row cs) |- _ ] =>
        fail 1
      | _ =>
        let Hk := fresh "Hk" in
        assert (kinding E T (knd_row cs)) as Hk
            by (apply (proj2 (type_equal_kinding He)))
      end
    end;
  repeat
    match goal with
    | [ Hk1 : kinding ?E ?T (knd_row ?cs1),
        Hk2 : kinding ?E ?T (knd_row ?cs2) |- _ ] =>
      match goal with
      | [ Heq : (knd_row cs1) = (knd_row cs2) |- _ ] =>
        fail 1
      | [ Heq : (knd_row cs2) = (knd_row cs1) |- _ ] =>
        fail 1
      | _ =>
        let Heq := fresh "Heq" in
        assert ((knd_row cs1) = (knd_row cs2)) as Heq
            by apply (kinding_unique Hk1 Hk2);
        inversion Heq;
        clear Heq;
        clear Hk2
      end
    end;
  substs.

Lemma row_projection_unique : forall E cs T K T' T'',
    row_projection E T K cs T' ->
    row_projection E T K cs T'' ->
    T' = T''.
Proof.
  introv Hpr1 Hpr2.
  gen T''.
  induction Hpr1; introv Hpr2.
  - eauto using row_projection_idem.
  - inversion Hpr2; subst; equal_kinds; auto.
    + assert (cons_non_empty cs3) by auto.
      false.
      constrs.
    + assert (cons_non_empty cs1).
      { apply row_projection_kinding in Hpr1.
        iauto. }
      false.
      constrs.
    + false.
      constrs.
  - inversion Hpr2; subst; equal_kinds; auto.
    + assert (cons_non_empty cs2) by auto.
      false.
      constrs.
    + assert (cons_non_empty cs1).
      { apply row_projection_kinding in Hpr1.
        iauto. }
      false.
      constrs.
    + false.
      constrs.
  - inversion Hpr2; subst.
    + replace (cons_inter (cons_union cs2 cs3) cs2)
        with cs2 in Hpr1_1 by constrs.
      replace (cons_inter (cons_union cs2 cs3) cs3)
        with cs3 in Hpr1_2 by constrs.
      apply row_projection_idem in Hpr1_1.
      apply row_projection_idem in Hpr1_2.
      subst.
      reflexivity.
    + equal_kinds.
      false.
      constrs.
    + equal_kinds.
      false.
      constrs.
    + equal_kinds.
      f_equal; auto.
  - inversion Hpr2; subst.
    + apply row_projection_idem in Hpr1_1.
      apply row_projection_idem in Hpr1_2.
      subst.
      reflexivity.
    + f_equal; auto.
  - inversion Hpr2; subst.
    + apply row_projection_idem in Hpr1_1.
      apply row_projection_idem in Hpr1_2.
      subst.
      reflexivity.
    + f_equal; auto.
  - inversion Hpr2; subst; auto.
  - inversion Hpr2; subst; auto.
Qed.

Lemma type_equal_project : forall E cs T1 T2 T1' K,
    type_equal E T1 T2 K ->
    row_projection E T1 K cs T1' ->
    exists T2',
    row_projection E T2 K cs T2' /\
    type_equal E T1' T2' (knd_row cs).
Proof.
  introv He Hpr.
  gen T1' cs.
  induction He; introv Hpr.
  - eauto using type_equal_refl with kinding.
  - inversion Hpr; subst.
    exists (typ_constructor c T').
    auto with kinding.
  - inversion Hpr; subst.
    + exists (typ_or T1' T2').
      auto with kinding.
    + equal_kinds.
      destruct (IHHe1 _ _ H6) as [T1'' ?].
      exists T1''.
      iauto.
    + equal_kinds.
      destruct (IHHe2 _ _ H9) as [T2'' ?].
      exists T2''.
      iauto.
    + equal_kinds.
      destruct (IHHe1 _ _ H8) as [T1'' ?].
      destruct (IHHe2 _ _ H11) as [T2'' ?].
      exists (typ_or T1'' T2'').
      split; iauto.
      replace cs
        with (cons_union (cons_inter cs cs1) (cons_inter cs cs2))
        by constrs.
      intuition auto with constrs.
  - inversion Hpr.
  - inversion Hpr.
  - inversion Hpr; subst; eauto with kinding.
  - inversion Hpr; subst; eauto with kinding.
  - inversion Hpr; subst.
    + exists (typ_meet T1' T2').
      auto with kinding.
    + destruct (IHHe1 _ _ H2) as [T1'' ?].
      destruct (IHHe2 _ _ H6) as [T2'' ?].
      exists (typ_meet T1'' T2'').
      iauto.
  - inversion Hpr; subst.
    + exists (typ_join T1' T2').
      auto with kinding.
    + destruct (IHHe1 _ _ H2) as [T1'' ?].
      destruct (IHHe2 _ _ H6) as [T2'' ?].
      exists (typ_join T1'' T2'').
      iauto.
  - destruct (IHHe1 _ _ Hpr) as [T2' [Hpr2 ?]].
    destruct (IHHe2 _ _ Hpr2) as [T3' ?].
    iauto.
  - replace (cons_union cs1 cs2)
        with (cons_union cs2 cs1) in * by constrs.
    assert (cons_disjoint cs2 cs1) by constrs.
    inversion Hpr; subst.
    + exists (typ_or T2 T1).
      intuition auto using type_equal_symm.
    + equal_kinds.
      exists T1'.
      replace (cons_union cs3 cs4)
        with (cons_union cs4 cs3) in * by constrs.
      auto using type_equal_refl with kinding.
    + equal_kinds.
      exists T1'.
      replace (cons_union cs3 cs4)
        with (cons_union cs4 cs3) in * by constrs.
      auto using type_equal_refl with kinding.
    + equal_kinds.
      exists (typ_or T2' T1'0).
      replace (cons_union cs3 cs4)
        with (cons_union cs4 cs3) in * by constrs.
      split; auto.
      replace cs
        with (cons_union (cons_inter cs cs3) (cons_inter cs cs4))
        by constrs.
      auto with kinding constrs.
  - inversion Hpr; subst.
    + exists (typ_or (typ_or T1 T2) T3).
      split; auto.
      rewrite cons_union_associative.
      auto with constrs.
    + assert (kinding E (typ_or T2 T3) (knd_row (cons_union cs2 cs3)))
        by auto.
      equal_kinds.
      exists T1'.
      split; auto using type_equal_refl with kinding.
      rewrite cons_union_associative.
      apply row_projection_or_l; auto with kinding; constrs.
    + { inversion H14; subst.
        - assert
            (kinding E (typ_or T2 T3) (knd_row (cons_union cs2 cs3)))
            by auto.
          equal_kinds.
          assert (cons_non_empty cs2) by auto.
          assert (cons_non_empty cs3) by auto.
          exists (typ_or T2 T3).
          split; auto using type_equal_refl with kinding.
          rewrite cons_union_associative.
          apply row_projection_or_both; auto with constrs.
          + replace (cons_inter (cons_union cs2 cs3)
                                (cons_union cs4 cs2))
              with cs2 by constrs.
            apply row_projection_or_r; auto; constrs.
          + replace (cons_inter (cons_union cs2 cs3) cs3)
              with cs3 by constrs.
            apply row_projection_identity.
            auto with kinding.
        - equal_kinds.
          exists T1'.
          split; auto using type_equal_refl with kinding.
          rewrite cons_union_associative.
          apply row_projection_or_l; auto; constrs.
        - equal_kinds.
          exists T1'.
          split; auto using type_equal_refl with kinding.
          rewrite cons_union_associative.
          apply row_projection_or_r; auto; constrs.
        - equal_kinds.
          exists (typ_or T1'0 T2').
          split; auto using type_equal_refl with kinding.
          rewrite cons_union_associative.
          apply row_projection_or_both; auto with constrs.
          apply row_projection_or_r; auto with constrs.
          replace (cons_inter cs (cons_union cs4 cs6))
            with (cons_inter cs cs6) by constrs.
          auto. }
      + { inversion H16; substs.
          - assert
              (kinding E (typ_or T2 T3)
                       (knd_row (cons_union cs2 cs3)))
              by auto.
            rewrite <- H15 in H14.
            equal_kinds.
            exists (typ_or (typ_or T1'0 T2) T3).
            split.
            + { rewrite <- H15.
                rewrite cons_union_associative.
                apply row_projection_or_both.
                - constrs.
                - constrs.
                - constrs.

            + assert
                (kinding E (typ_or T1'0 (typ_or T2 T3)) (knd_row cs))
                by auto with kinding.
              assert
                (kinding E (typ_or T1'0 (typ_or T2 T3))
                         (knd_row (cons_union (cons_inter cs cs4)
                                              (cons_union cs2 cs3)))).
              { apply row_projection_kinding in H13.
                apply kinding_or; auto with constrs. }
              equal_kinds.
              apply type_equal_or_associative_l;
                auto with constrs kinding.
