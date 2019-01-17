(************************************************
 *          Row Subtyping - Inversion           *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import Arith.
Require Import LibLN Utilities Cofinite Disjoint Definitions
        Opening FreeVars Environments Subst Wellformedness
        Weakening Substitution Kinding Subtyping.

(* ****************************************************** *)
(** Useful lemmas *)

Lemma subtype_equal_bot : forall v E1 E2 T1 T2 K,
    type_equal v E1 E2 T1 (typ_bot K) K ->
    subtype v E1 E2 T2 T1 K ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    type_equal v E1 E2 T2 (typ_bot K) K.
Proof.
  introv Hte Hs He1 He2.
  pose subtype_bot as Hs2.
  unfold subtype in *.
  rewrite Hs.
  rewrite Hte.
  rewrite type_equal_meet_commutative by auto with kinding.
  rewrite <- Hs2 by auto with kinding wellformed.
  treflexivity.
Qed.

Lemma subtype_equal_top : forall v E1 E2 T1 T2 K,
    type_equal v E1 E2 T1 (typ_top K) K ->
    subtype v E1 E2 T1 T2 K ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    type_equal v E1 E2 T2 (typ_top K) K.
Proof.
  introv Hte Hs He1 He2.
  pose (@subtype_top v E1 E2 T2 K) as Hs2.
  rewrite subtype_dual in Hs by auto.
  rewrite subtype_dual in Hs2 by auto.
  rewrite Hs.
  rewrite Hte.
  rewrite type_equal_join_commutative by auto with kinding.
  rewrite <- Hs2 by auto with kinding wellformed.
  treflexivity.
Qed.

Lemma subtype_join_bot_l : forall v E1 E2 T1 T2 T3 K,
  subtype v E1 E2 T1 T3 K ->
  type_equal v E1 E2 T2 (typ_bot K) K ->
  valid_tenv v E1 ->
  valid_tenv_extension v E1 E2 ->
  subtype v E1 E2 (typ_join T1 T2) T3 K.
Proof.
  introv Hs Hte He1 He2.
  rewrite <- Hs.
  rewrite Hte.
  rewrite type_equal_join_identity by auto with kinding.
  sreflexivity.
Qed.

Lemma subtype_meet_top_r : forall v E1 E2 T1 T2 T3 K,
  subtype v E1 E2 T1 T2 K ->
  type_equal v E1 E2 T3 (typ_top K) K ->
  valid_tenv v E1 ->
  valid_tenv_extension v E1 E2 ->
  subtype v E1 E2 T1 (typ_meet T2 T3) K.
Proof.
  introv Hs Hte He1 He2.
  rewrite Hs.
  rewrite Hte.
  rewrite type_equal_meet_identity by auto with kinding.
  sreflexivity.
Qed.

(* *************************************************************** *)
(** Covariant subtyping inversions *)

(* Type representing covariant (and invariant) contexts *)
Inductive covariant_context : Type :=
  | ctx_variant : covariant_context
  | ctx_arrow_left_row : covariant_context
  | ctx_arrow_right : covariant_context
  | ctx_ref_co : covariant_context
  | ctx_prod_left : covariant_context
  | ctx_prod_right : covariant_context
  | ctx_constructor : nat -> cset -> covariant_context
  | ctx_unit : covariant_context.
  
Definition cov_input_kind z :=
  match z with
  | ctx_variant => knd_row_all
  | ctx_arrow_left_row => knd_type
  | ctx_arrow_right => knd_type
  | ctx_ref_co => knd_type
  | ctx_prod_left => knd_type
  | ctx_prod_right => knd_type
  | ctx_constructor _ _ => knd_type
  | ctx_unit => knd_type
  end.

Definition cov_output_kind z :=
  match z with
  | ctx_variant => knd_type
  | ctx_arrow_left_row => knd_type
  | ctx_arrow_right => knd_type
  | ctx_ref_co => knd_type
  | ctx_prod_left => knd_type
  | ctx_prod_right => knd_type
  | ctx_constructor _ cs => knd_row cs
  | ctx_unit => knd_type
  end.

Inductive valid_covariant_context : covariant_context -> Prop :=
  | valid_ctx_variant : valid_covariant_context ctx_variant
  | valid_ctx_arrow_left_row :
      valid_covariant_context ctx_arrow_left_row
  | valid_ctx_arrow_right : valid_covariant_context ctx_arrow_right
  | valid_ctx_ref_co : valid_covariant_context ctx_ref_co
  | valid_ctx_prod_left : valid_covariant_context ctx_prod_left
  | valid_ctx_prod_right : valid_covariant_context ctx_prod_right
  | valid_ctx_constructor : forall c cs,
      CSet.In c cs ->
      valid_covariant_context (ctx_constructor c cs)
  | valid_ctx_unit : valid_covariant_context ctx_unit.

Hint Constructors valid_covariant_context.

Inductive covariant_inv :
  covariant_context -> bool -> version -> tenv -> tenv ->
  typ -> typ -> Prop :=
  | covariant_inv_meet : forall z s v E1 E2 T1 T2 T3,
      covariant_inv z s v E1 E2 T1 T2 ->
      covariant_inv z s v E1 E2 T1 T3 ->
      covariant_inv z s v E1 E2 T1 (typ_meet T2 T3)
  | covariant_inv_join : forall z s1 s2 s3 v E1 E2 T1 T2 T3 T4 T5,
      covariant_inv z s1 v E1 E2 T2 T4 ->
      covariant_inv z s2 v E1 E2 T3 T5 ->
      type_equal v (E1 & E2) empty T1
                 (typ_join T2 T3) (cov_input_kind z) ->
      s3 = orb s1 s2 ->
      covariant_inv z s3 v E1 E2 T1 (typ_join T4 T5)
  | covariant_inv_top : forall z s v E1 E2 K2 T1,
      covariant_inv z s v E1 E2 T1 (typ_top K2)
  | covariant_inv_var : forall z s v E1 E2 X T1 T2 T3,
      binds X (Rng T2 T3 (cov_output_kind z)) E1 ->
      covariant_inv z s v E1 E2 T1 T2 ->
      covariant_inv z s v E1 E2 T1 (typ_fvar X)
  | covariant_inv_variant : forall s v E1 E2 T1 T2,
      subtype v (E1 & E2) empty T1 T2 knd_row_all ->
      covariant_inv ctx_variant s v E1 E2 T1 (typ_variant T2)
  | covariant_inv_arrow_left : forall s E1 E2 T1 T2 T3,
      subtype version_row_subtyping (E1 & E2) empty T1 T2 knd_type ->
      covariant_inv ctx_arrow_left_row s version_row_subtyping
        E1 E2 T1 (typ_arrow T2 T3)
  | covariant_inv_arrow_right : forall s v E1 E2 T1 T2 T3,
      subtype v (E1 & E2) empty T1 T3 knd_type ->
      covariant_inv ctx_arrow_right s v E1 E2 T1 (typ_arrow T2 T3)
  | covariant_inv_ref : forall s v E1 E2 T1 T2,
      subtype v (E1 & E2) empty T1 T2 knd_type ->
      covariant_inv ctx_ref_co s v E1 E2 T1 (typ_ref T2)
  | covariant_inv_prod_left : forall s v E1 E2 T1 T2 T3,
      subtype v (E1 & E2) empty T1 T2 knd_type ->
      covariant_inv ctx_prod_left s v E1 E2 T1 (typ_prod T2 T3)
  | covariant_inv_prod_right : forall s v E1 E2 T1 T2 T3,
      subtype v (E1 & E2) empty T1 T3 knd_type ->
      covariant_inv ctx_prod_right s v E1 E2 T1 (typ_prod T2 T3)
  | covariant_inv_or_l : forall c s v E1 E2 cs1 cs2 cs3 T1 T2 T3,
      covariant_inv (ctx_constructor c cs1) s v E1 E2 T1 T2 ->
      CSet.In c cs1 ->
      covariant_inv (ctx_constructor c cs3) s
        v E1 E2 T1 (typ_or cs1 cs2 T2 T3)
  | covariant_inv_or_r : forall c s v E1 E2 cs1 cs2 cs3 T1 T2 T3,
      covariant_inv (ctx_constructor c cs2) s v E1 E2 T1 T3 ->
      CSet.In c cs2 ->
      covariant_inv (ctx_constructor c cs3) s
        v E1 E2 T1 (typ_or cs1 cs2 T2 T3)
  | covariant_inv_proj : forall c s v E1 E2 cs1 cs2 T1 T2,
      covariant_inv (ctx_constructor c cs1) s v E1 E2 T1 T2 ->
      covariant_inv (ctx_constructor c cs2) s
        v E1 E2 T1 (typ_proj cs1 cs2 T2)
  | covariant_inv_constructor : forall c cs s v E1 E2 T1 T2,
      subtype v (E1 & E2) empty T1 T2 knd_type ->
      covariant_inv (ctx_constructor c cs) s
        v E1 E2 T1 (typ_constructor c T2)
  | covariant_inv_unit : forall s v E1 E2 T1,
      covariant_inv ctx_unit s v E1 E2 T1 typ_unit
  | covariant_inv_bot : forall z v E1 E2 T1 T2,
      type_equal v (E1 & E2) empty T1
        (typ_bot (cov_input_kind z)) (cov_input_kind z) ->
      covariant_inv z false v E1 E2 T1 T2.

Hint Constructors covariant_inv.

Lemma covariant_inv_meet_inv : forall z s v E1 E2 T1 T2 T3 (P : Prop),
    covariant_inv z s v E1 E2 T1 (typ_meet T2 T3) ->
    (s = false ->
     type_equal v (E1 & E2) empty T1
       (typ_bot (cov_input_kind z)) (cov_input_kind z) ->
     P) ->
    (covariant_inv z s v E1 E2 T1 T2 ->
     covariant_inv z s v E1 E2 T1 T3 ->
     P) ->
    P.
Proof.
  introv Hc Hp1 Hp2.
  inversion Hc; auto.
Qed.

Lemma covariant_inv_join_inv :
  forall z s1 v E1 E2 T1 T2 T3 (P : Prop),
    covariant_inv z s1 v E1 E2 T1 (typ_join T2 T3) ->
    (s1 = false ->
     type_equal v (E1 & E2) empty T1
       (typ_bot (cov_input_kind z)) (cov_input_kind z) ->
     P) ->
    (forall s2 s3 T4 T5,
        covariant_inv z s2 v E1 E2 T4 T2 ->
        covariant_inv z s3 v E1 E2 T5 T3 ->
        type_equal v (E1 & E2) empty T1
                   (typ_join T4 T5) (cov_input_kind z) ->
        s1 = orb s2 s3 ->
        P) ->
    P.
Proof.
  introv Hc Hp1 Hp2.
  inversion Hc; eauto.
Qed.

Lemma covariant_inv_var_inv : forall z s v E1 E2 X T1 (P : Prop),
    covariant_inv z s v E1 E2 T1 (typ_fvar X) ->
    (s = false ->
     type_equal v (E1 & E2) empty T1
       (typ_bot (cov_input_kind z)) (cov_input_kind z) ->
     P) ->
    (forall T2 T3,
        binds X (Rng T2 T3 (cov_output_kind z)) E1 ->
        covariant_inv z s v E1 E2 T1 T2 ->
        P) ->
    P.
Proof.
  introv Hc Hp1 Hp2.
  inversion Hc; eauto.
Qed.

Lemma covariant_inv_variant_inv : forall z s v E1 E2 T1 T2 (P : Prop),
    covariant_inv z s v E1 E2 T1 (typ_variant T2) ->
    (s = false ->
     type_equal v (E1 & E2) empty T1
       (typ_bot (cov_input_kind z)) (cov_input_kind z) ->
     P) ->
    (z = ctx_variant ->
     subtype v (E1 & E2) empty T1 T2 knd_row_all ->
     P) ->
    P.
Proof.
  introv Hc Hp1 Hp2.
  inversion Hc; auto.
Qed.

Lemma covariant_inv_arrow_inv : forall z s v E1 E2 T1 T2 T3 (P : Prop),
    covariant_inv z s v E1 E2 T1 (typ_arrow T2 T3) ->
    (s = false ->
     type_equal v (E1 & E2) empty T1
       (typ_bot (cov_input_kind z)) (cov_input_kind z) ->
     P) ->
    (z = ctx_arrow_left_row ->
     v = version_row_subtyping ->
     subtype v (E1 & E2) empty T1 T2 knd_type ->
     P) ->
    (z = ctx_arrow_right ->
     subtype v (E1 & E2) empty T1 T3 knd_type ->
     P) ->
    P.
Proof.
  introv Hc Hp1 Hp2 Hp3.
  inversion Hc; subst; auto.
Qed.

Lemma covariant_inv_ref_inv : forall z s v E1 E2 T1 T2 (P : Prop),
    covariant_inv z s v E1 E2 T1 (typ_ref T2) ->
    (s = false ->
     type_equal v (E1 & E2) empty T1
       (typ_bot (cov_input_kind z)) (cov_input_kind z) ->
     P) ->
    (z = ctx_ref_co ->
     subtype v (E1 & E2) empty T1 T2 knd_type ->
     P) ->
    P.
Proof.
  introv Hc Hp1 Hp2.
  inversion Hc; auto.
Qed.

Lemma covariant_inv_prod_inv : forall z s v E1 E2 T1 T2 T3 (P : Prop),
    covariant_inv z s v E1 E2 T1 (typ_prod T2 T3) ->
    (s = false ->
     type_equal v (E1 & E2) empty T1
       (typ_bot (cov_input_kind z)) (cov_input_kind z) ->
     P) ->
    (z = ctx_prod_left ->
     subtype v (E1 & E2) empty T1 T2 knd_type ->
     P) ->
    (z = ctx_prod_right ->
     subtype v (E1 & E2) empty T1 T3 knd_type ->
     P) ->
    P.
Proof.
  introv Hc Hp1 Hp2 Hp3.
  inversion Hc; auto.
Qed.

Lemma covariant_inv_or_inv :
  forall z s v E1 E2 cs1 cs2 T1 T2 T3 (P : Prop),
    covariant_inv z s v E1 E2 T1 (typ_or cs1 cs2 T2 T3) ->
    (s = false ->
     type_equal v (E1 & E2) empty T1
       (typ_bot (cov_input_kind z)) (cov_input_kind z) ->
     P) ->
    (forall c cs3,
        z = ctx_constructor c cs3 ->
        covariant_inv (ctx_constructor c cs1) s v E1 E2 T1 T2 ->
        CSet.In c cs1 ->
        P) ->
    (forall c cs3,
        z = ctx_constructor c cs3 ->
        covariant_inv (ctx_constructor c cs2) s v E1 E2 T1 T3 ->
        CSet.In c cs2 ->
        P) ->
    P.
Proof.
  introv Hc Hp1 Hp2 Hp3.
  inversion Hc; eauto.
Qed.

Lemma covariant_inv_proj_inv :
  forall z s v E1 E2 cs1 cs2 T1 T2 (P : Prop),
    covariant_inv z s v E1 E2 T1 (typ_proj cs1 cs2 T2) ->
    (s = false ->
     type_equal v (E1 & E2) empty T1
       (typ_bot (cov_input_kind z)) (cov_input_kind z) ->
     P) ->
    (forall c,
        z = ctx_constructor c cs2 ->
        covariant_inv (ctx_constructor c cs1) s v E1 E2 T1 T2 ->
        P) ->
    P.
Proof.
  introv Hc Hp1 Hp2.
  inversion Hc; subst; eauto.  
Qed.

Lemma covariant_inv_constructor_inv :
  forall z s v E1 E2 c T1 T2 (P : Prop),
    covariant_inv z s v E1 E2 T1 (typ_constructor c T2) ->
    (s = false ->
     type_equal v (E1 & E2) empty T1
       (typ_bot (cov_input_kind z)) (cov_input_kind z) ->
     P) ->
    (forall cs,
        z = ctx_constructor c cs ->
        subtype v (E1 & E2) empty T1 T2 knd_type ->
        P) ->
    P.
Proof.
  introv Hc Hp1 Hp2.
  inversion Hc; subst; eauto.
Qed.

Lemma covariant_inv_unit_inv :
  forall z s v E1 E2 T1 (P : Prop),
    covariant_inv z s v E1 E2 T1 typ_unit ->
    (s = false ->
     type_equal v (E1 & E2) empty T1
       (typ_bot (cov_input_kind z)) (cov_input_kind z) ->
     P) ->
    (z = ctx_unit -> P) ->
    P.
Proof.
  introv Hc Hp1 Hp2.
  inversion Hc; subst; eauto.
Qed.

Lemma covariant_inv_bot_inv :
  forall z s v E1 E2 T1 K (P : Prop),
    covariant_inv z s v E1 E2 T1 (typ_bot K) ->
    (s = false ->
     type_equal v (E1 & E2) empty T1
       (typ_bot (cov_input_kind z)) (cov_input_kind z) ->
     P) ->
    P.
Proof.
  introv Hc Hp1.
  inversion Hc; subst; eauto.
Qed.

Ltac invert_ctx_constructor_equalities :=
  repeat match goal with
  | Heq : ctx_constructor _ _ = ctx_constructor _ _ |- _ =>
    inversion Heq; clear Heq
  end.

Ltac discriminate_ctx_prod_mismatches :=
  try match goal with
  | Heq : ctx_prod_left = ctx_prod_right |- _ =>
    discriminate Heq
  | Heq : ctx_prod_right = ctx_prod_left |- _ =>
    discriminate Heq
  end.

Ltac discriminate_cov_ctx_arrow_mismatches :=
  try match goal with
  | Heq : ctx_arrow_left_row = ctx_arrow_right |- _ =>
    discriminate Heq
  | Heq : ctx_arrow_right = ctx_arrow_left_row |- _ =>
    discriminate Heq
  end.

Ltac discriminate_version :=
  try match goal with
  | Heq : version_full_subtyping = version_row_subtyping |- _ =>
    discriminate Heq
  | Heq : version_row_subtyping = version_full_subtyping |- _ =>
    discriminate Heq
  end.

Ltac equate_multiple_bindings :=
  repeat match goal with
  | Hb1 : binds ?X (Rng ?T1 ?T2 ?K1) ?E,
    Hb2 : binds ?X (Rng ?T3 ?T4 ?K2) ?E |- _ =>
    let Heq := fresh "Heq" in
    assert (Heq := binds_functional Hb1 Hb2);
    inversion Heq; subst; clear Heq; clear Hb2
  | Hb1 : binds ?X (Rng ?T1 ?T2 ?K1) ?E1,
    Hb2 : binds ?X (Rng ?T3 ?T4 ?K2) (?E1 & ?E2) |- _ =>
    let He := fresh "He" in
    assert (type_environment (E1 & E2)) as He
      by auto with wellformed;
    let Heq := fresh "Heq" in
    assert (Heq := binds_functional
                     (binds_tenv_weakening_l Hb1 He) Hb2);
    inversion Heq; subst; clear He; clear Heq; clear Hb2
  | Hb1 : binds ?X (Rng ?T1 ?T2 ?K1) ?E1,
    Hb2 : binds ?X (Rng ?T3 ?T4 ?K2) (?E1 & ?E2 & ?E3)
    |- _ =>
    let He := fresh "He" in
    assert (type_environment (E1 & E2 & E3)) as He
      by auto with wellformed;
    let Heq := fresh "Heq" in
    assert (Heq := binds_functional
                     (binds_tenv_weakening_l2 Hb1 He) Hb2);
    inversion Heq; subst; clear He; clear Heq; clear Hb2
  end.

Ltac invert_covariant_inv :=
  repeat match goal with
  | H : covariant_inv _ _ _ _ _ _ (typ_constructor _ _) |- _ =>
    apply (covariant_inv_constructor_inv H); clear H; intros;
    invert_ctx_constructor_equalities; subst
  | H : covariant_inv _ _ _ _ _ _ (typ_or _ _ _ _) |- _ =>
    apply (covariant_inv_or_inv H); clear H; intros;
    invert_ctx_constructor_equalities; subst
  | H : covariant_inv _ _ _ _ _ _ (typ_proj _ _ _) |- _ =>
    apply (covariant_inv_proj_inv H); clear H; intros;
    invert_ctx_constructor_equalities; subst
  | H : covariant_inv _ _ _ _ _ _ (typ_variant _) |- _ =>
    apply (covariant_inv_variant_inv H); clear H; intros
  | H : covariant_inv _ _ _ _ _ _ (typ_arrow _ _) |- _ =>
    apply (covariant_inv_arrow_inv H); clear H; intros;
    subst; discriminate_cov_ctx_arrow_mismatches;
    discriminate_version
  | H : covariant_inv _ _ _ _ _ _ (typ_ref _) |- _ =>
    apply (covariant_inv_ref_inv H); clear H; intros
  | H : covariant_inv _ _ _ _ _ _ (typ_prod _ _) |- _ =>
    apply (covariant_inv_prod_inv H); clear H; intros;
    subst; discriminate_ctx_prod_mismatches
  | H : covariant_inv _ _ _ _ _ _ typ_unit |- _ =>
    apply (covariant_inv_unit_inv H); clear H; intros
  | H : covariant_inv _ _ _ _ _ _ (typ_fvar _) |- _ =>
    apply (covariant_inv_var_inv H); clear H; intros;
    equate_multiple_bindings
  | H : covariant_inv _ _ _ _ _ _ (typ_bot _) |- _ =>
    apply (covariant_inv_bot_inv H); clear H; intros
  | H : covariant_inv _ _ _ _ _ _ (typ_meet _ _) |- _ =>
    apply (covariant_inv_meet_inv H); clear H; intros
  | H : covariant_inv _ _ _ _ _ _ (typ_join _ _) |- _ =>
    apply (covariant_inv_join_inv H); clear H; intros
  end.

Ltac choose_covariant_inv_join_type z Td T :=
  match T with
  | typ_meet ?T1 ?T2 =>
    let T1' := choose_covariant_inv_join_type z Td T1 in
    let T2' := choose_covariant_inv_join_type z Td T2 in
    constr:(typ_meet T1' T2')
  | typ_join ?T1 ?T2 =>
    let T1' := choose_covariant_inv_join_type z Td T1 in
    let T2' := choose_covariant_inv_join_type z Td T2 in
    constr:(typ_join T1' T2')
  | typ_or ?cs1 ?cs2 ?T1 ?T2 =>
    match z with
    | ctx_constructor ?c _ =>
      match goal with
      | Hin : CSet.In c cs1 |- _ =>
        choose_covariant_inv_join_type z Td T1
      | Hin : CSet.In c cs2 |- _ =>
        choose_covariant_inv_join_type z Td T2
      end
    end
  | typ_proj _ _ ?T1 =>
    choose_covariant_inv_join_type z Td T1
  | typ_variant ?T1 => constr:(typ_meet Td T1)
  | typ_constructor _ ?T1 => constr:(typ_meet Td T1)
  | typ_ref ?T1 => constr:(typ_meet Td T1)
  | typ_arrow ?T1 ?T2 =>
    match z with
    | ctx_arrow_left_row => constr:(typ_meet Td T1)
    | ctx_arrow_right => constr:(typ_meet Td T2)
    end
  | typ_prod ?T1 ?T2 =>
    match z with
    | ctx_prod_left => constr:(typ_meet Td T1)
    | ctx_prod_right => constr:(typ_meet Td T2)
    end
  | typ_unit => constr:(Td)
  | typ_bot (cov_output_kind ?z) => constr:(typ_bot (cov_input_kind z))
  | _ =>
    match goal with
    | H1 : covariant_inv _ _ _ _ _ ?Tt1 T,
      H2 : covariant_inv _ _ _ _ _ ?Tt2 T
      |- _ => constr:(typ_join Tt1 Tt2)
    | H : covariant_inv _ _ _ _ _ ?Tt T |- _ =>
      constr:(Tt)
    | Hte : type_equal _ _ _ ?Tb (typ_bot _) _ |- _ =>
      constr:(Tb)
    end
  end.

Ltac choose_covariant_inv_join_bool z sd T :=
  match T with
  | typ_meet ?T1 ?T2 =>
    let s1 := choose_covariant_inv_join_bool z sd T1 in
    let s2 := choose_covariant_inv_join_bool z sd T2 in
    constr:(andb s1 s2)
  | typ_join ?T1 ?T2 =>
    let s1 := choose_covariant_inv_join_bool z sd T1 in
    let s2 := choose_covariant_inv_join_bool z sd T2 in
    constr:(orb s1 s2)
  | typ_or ?cs1 ?cs2 ?T1 ?T2 =>
    match z with
    | ctx_constructor ?c _ =>
      match goal with
      | Hin : CSet.In c cs1 |- _ =>
        choose_covariant_inv_join_bool z sd T1
      | Hin : CSet.In c cs2 |- _ =>
        choose_covariant_inv_join_bool z sd T2
      end
    end
  | typ_proj _ _ ?T1 =>
    choose_covariant_inv_join_bool z sd T1
  | typ_variant _ => constr:(sd)
  | typ_constructor _ _ => constr:(sd)
  | typ_ref _ => constr:(sd)
  | typ_arrow _ _ => constr:(sd)
  | typ_prod _ _ => constr:(sd)
  | typ_unit => constr:(sd)
  | typ_bot (cov_output_kind ?z) => constr:(false)
  | _ =>
    match goal with
    | H1 : covariant_inv _ ?s1 _ _ _ _ T,
      H2 : covariant_inv _ ?s2 _ _ _ _ T
      |- _ => constr:(orb s1 s2)
    | H : covariant_inv _ ?s _ _ _ _ T |- _ => constr:(s)
    | Hte : type_equal _ _ _ ?Tb (typ_bot _) _ |- _ =>
      constr:(false)
    end
  end.

Ltac construct_covariant_inv_bot :=
  try match goal with
  | |- covariant_inv _ _ _ _ _ (typ_bot _) _ =>
    apply covariant_inv_bot;
    treflexivity
  | |- covariant_inv _ (?s && false) _ _ _
         (typ_meet _ (typ_bot _)) _ =>
    try replace (andb s false) with false by ring;
    apply covariant_inv_bot;
    rewrite type_equal_meet_annihilation_r
      by auto with wellformed;
    treflexivity
  | |- covariant_inv _ _ _ _ _ ?Tt _ =>
    match goal with
    | H : type_equal _ _ _ Tt (typ_bot _) _ |- _ =>
      apply covariant_inv_bot;
      apply H
    | H: type_equal _ _ _ Tt (typ_join ?Ttl ?Ttr) _,
      Hl : type_equal _ _ _ ?Ttl (typ_bot _) _,
      Hr : type_equal _ _ _ ?Ttr (typ_bot _) _ |- _ =>
      apply covariant_inv_bot;
      rewrite H;
      rewrite Hl;
      rewrite Hr;
      rewrite type_equal_join_identity by auto with kinding;
      treflexivity
    end
  end.

Ltac construct_covariant_inv :=
  construct_covariant_inv_bot;
  repeat match goal with
  | |- covariant_inv ?z _ _ _ _ ?Tt (typ_or ?csl ?csr ?Tl ?Tr) =>
    match goal with
    | H : covariant_inv _ _ _ _ _ Tt ?Ts |- _ =>
      match Tl with
      | context[Ts] =>
        match Tr with
        | context[Ts] =>
          match z with
          | ctx_constructor ?c ?cs =>
            destruct (CSet.In_dec c csl);
            [> apply covariant_inv_or_l
            | apply covariant_inv_or_r]
          end
        | _ => apply covariant_inv_or_l
        end
      | _ =>
        match Tr with
        | context[Ts] => apply covariant_inv_or_r
        end
      end
    | _ =>
      match z with
      | ctx_constructor ?c ?cs =>
        destruct (CSet.In_dec c csl);
        [> apply covariant_inv_or_l | apply covariant_inv_or_r]
      end     
    end
  | |- covariant_inv ?z ?s _ _ _ ?Tt (typ_join ?Ts1 ?Ts2) =>
    let s1' := choose_covariant_inv_join_bool z s Ts1 in
    let s2' := choose_covariant_inv_join_bool z s Ts2 in
    let T1' := choose_covariant_inv_join_type z Tt Ts1 in
    let T2' := choose_covariant_inv_join_type z Tt Ts2 in
    apply covariant_inv_join
      with (s1 := s1') (s2 := s2') (T2 := T1') (T3 := T2')
  | |- covariant_inv _ _ _ _ _ _ (typ_top _) =>
    apply covariant_inv_top
  | |- covariant_inv _ _ _ _ _ _ (typ_meet _ _) =>
    apply covariant_inv_meet
  | |- covariant_inv _ _ _ _ _ _ (typ_proj _ _ _) =>
    apply covariant_inv_proj
  | |- covariant_inv _ _ _ _ _ _ (typ_variant _) =>
    apply covariant_inv_variant
  | |- covariant_inv _ _ _ _ _ _ (typ_constructor _ _) =>
    apply covariant_inv_constructor
  | |- covariant_inv ctx_arrow_left_row _ _ _ _ _ (typ_arrow _ _) =>
    apply covariant_inv_arrow_left
  | |- covariant_inv ctx_arrow_right _ _ _ _ _ (typ_arrow _ _) =>
    apply covariant_inv_arrow_right
  | |- covariant_inv ctx_prod_left _ _ _ _ _ (typ_prod _ _) =>
    apply covariant_inv_prod_left
  | |- covariant_inv ctx_prod_right _ _ _ _ _ (typ_prod _ _) =>
    apply covariant_inv_prod_right
  | |- covariant_inv _ _ _ _ _ _ (typ_ref _) =>
    apply covariant_inv_ref
  | Hb : binds ?X (Rng ?Tl ?Tu _) _
    |- covariant_inv _ _ _ _ _ _ (typ_fvar ?X) =>
    apply covariant_inv_var with (T2 := Tl) (T3 := Tu)
  end;
  try assumption;
  construct_covariant_inv_bot.

Lemma covariant_inv_sub : forall z s1 s2 v E1 E2 K1 T1 T2 T3,
    covariant_inv z s1 v E1 E2 T1 T2 ->
    subtype v (E1 & E2) empty T3 T1 K1 ->
    leb s2 s1 ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    K1 = cov_input_kind z ->
    covariant_inv z s2 v E1 E2 T3 T2.
Proof.
  introv Hi Hs Hb He1 He2 Heq.
  generalize dependent T3.
  generalize dependent s2.
  subst.
  induction Hi; introv Hb Hs; subst; eauto.
  - apply covariant_inv_join
      with (s1 := andb s0 s1) (s2 := andb s0 s2)
           (T2 := typ_meet T0 T2) (T3 := typ_meet T0 T3); auto.
    + eauto using subtype_lower_bound_r,
        type_environment_extend, leb_lower_bound_r
          with kinding wellformed.
    + eauto using subtype_lower_bound_r,
        type_environment_extend, leb_lower_bound_r
          with kinding wellformed.
    + unfold subtype in Hs.
      rewrite Hs at 1.
      subst_equal T1.
      rewrite type_equal_meet_distribution by auto with kinding.
      treflexivity.
    + unfold leb in Hb.
      rewrite Hb at 1.
      rewrite andb_orb_distribution.
      reflexivity.      
  - apply covariant_inv_variant;
      eauto using subtype_transitive, valid_tenv_extend.
  - apply covariant_inv_arrow_left;
      eauto using subtype_transitive, valid_tenv_extend.
  - apply covariant_inv_arrow_right;
      eauto using subtype_transitive, valid_tenv_extend.
  - apply covariant_inv_ref;
      eauto using subtype_transitive, valid_tenv_extend.
  - apply covariant_inv_prod_left;
      eauto using subtype_transitive, valid_tenv_extend.
  - apply covariant_inv_prod_right;
      eauto using subtype_transitive, valid_tenv_extend.
  - apply covariant_inv_constructor;
      eauto using subtype_transitive, valid_tenv_extend.
  - rewrite leb_false with (b := s2) by assumption.
    eauto using subtype_equal_bot, valid_tenv_extend.
Qed.

Instance covariant_inv_eq_morph_impl
  (z : covariant_context) (s : bool) (v : version)
  (E1 : tenv) (E2 : tenv)
  `{ He1 : valid_tenv v E1 }
  `{ He2 : valid_tenv_extension v E1 E2 }
  : Morphisms.Proper
      (type_equal' v (E1 & E2) empty (cov_input_kind z) ==>
       eq ==> Basics.impl)
      (covariant_inv z s v E1 E2) | 3
  := { }.
  unfold Morphisms.respectful.
  intros T1 T1' Hte T2' T2 Heq Hi.
  rewrite <- Heq.
  apply covariant_inv_sub
    with (s1 := s) (K1 := cov_input_kind z) (T1 := T1);
    auto using leb_refl.
  rewrite Hte.
  sreflexivity.
Qed.

Instance covariant_inv_eq_morph_flip_impl
  (z : covariant_context) (s : bool) (v : version)
  (E1 : tenv) (E2 : tenv)
  `{ He1 : valid_tenv v E1 }
  `{ He2 : valid_tenv_extension v E1 E2 }
  : Morphisms.Proper
      (type_equal' v (E1 & E2) empty (cov_input_kind z) ==>
       eq ==> Basics.flip Basics.impl)
      (covariant_inv z s v E1 E2) | 3
  := { }.
  unfold Morphisms.respectful.
  intros T1 T1' Hte T2' T2 Heq Hi.
  rewrite Heq.
  apply covariant_inv_sub
    with (s1 := s) (K1 := cov_input_kind z) (T1 := T1');
    auto using leb_refl.
  rewrite Hte.
  sreflexivity.
Qed.

Instance covariant_inv_sub_morph_impl
  (z : covariant_context) (s : bool) (v : version)
  (E1 : tenv) (E2 : tenv)
  `{ He1 : valid_tenv v E1 }
  `{ He2 : valid_tenv_extension v E1 E2 }
  : Morphisms.Proper
      (subtype' v (E1 & E2) empty (cov_input_kind z) ==>
       eq ==> Basics.flip Basics.impl)
      (covariant_inv z s v E1 E2) | 3
  := { }.
  unfold Morphisms.respectful.
  intros T1 T1' Hte T2' T2 Heq Hi.
  rewrite Heq.
  apply covariant_inv_sub
    with (s1 := s) (K1 := cov_input_kind z) (T1 := T1');
    auto using leb_refl.
Qed.

Lemma covariant_inv_upper_bound : forall z s1 s2 v E1 E2 T1 T2 T3,
    covariant_inv z s1 v E1 E2 T1 T3 ->
    covariant_inv z s2 v E1 E2 T2 T3 ->
    kinding (E1 & E2) empty T1 (cov_input_kind z) ->
    kinding (E1 & E2) empty T2 (cov_input_kind z) ->
    kinding E1 E2 T3 (cov_output_kind z) ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    covariant_inv z (orb s1 s2) v E1 E2 (typ_join T1 T2) T3.
Proof.
  introv Hi1 Hi2 Hk1 Hk2 Hk3 He1 He2.
  generalize dependent T2.
  generalize dependent s2.
  induction Hi1; introv Hi2 Hk2; invert_covariant_inv; subst;
    auto using subtype_least_upper_bound, subtype_join_bot_l,
      valid_tenv_extend with kinding.
  - apply covariant_inv_join
      with (s1 := s1) (s2 := s2) (T2 := T2) (T3 := T3);
      try ring_simplify; auto.
    subst_equal T0.
    rewrite type_equal_join_identity by auto with kinding.
    assumption.
  - apply covariant_inv_join
      with (s1 := orb s1 s4) (s2 := orb s2 s5)
        (T2 := typ_join T2 T6) (T3 := typ_join T3 T7);
          try ring_simplify; auto with kinding.
    subst_equal T1.
    subst_equal T0.
    rewrite <- type_equal_join_associative by auto with kinding.
    rewrite type_equal_join_associative
      with (T1 := T3) by auto with kinding.
    rewrite type_equal_join_commutative
      with (T1 := T3) by auto with kinding.
    rewrite <- type_equal_join_associative by auto with kinding.
    rewrite type_equal_join_associative by auto with kinding.
    treflexivity.
  - eauto using kinding_from_valid_tenv_lower with wellformed.
  - eauto using kinding_from_valid_tenv_lower with wellformed.
  - inversion Hk3; subst.
    assert (not (CSet.In c0 cs1)) by csetdec.
    contradiction.
  - inversion Hk3; subst.
    assert (not (CSet.In c0 cs1)) by csetdec.
    contradiction.
  - subst_equal T1.
    rewrite type_equal_join_commutative by auto with kinding.
    rewrite type_equal_join_identity by auto with kinding.
    assumption.
Qed.

Ltac invert_cov_output_kind_equality Heq :=
  match type of Heq with
  | knd_row ?cs1 = cov_output_kind (ctx_constructor ?c ?cs2) =>
    inversion Heq; subst
  | knd_row ?cs1 = cov_output_kind ?z =>
    destruct z; try discriminate;
    inversion HeqK; subst
  | _ => idtac
  end.

Ltac invert_kindings_cov :=
  repeat
    match goal with
    | Hz : valid_covariant_context (ctx_constructor _ _) |- _ =>
      inversion Hz; subst; clear Hz
    | H : kinding _ _ (typ_or _ _ _ _) _ |- _ =>
      inversion H; subst; clear H
    | H : kinding _ _ (typ_proj _ _ _) _ |- _ =>
      inversion H; subst; clear H
    end.

Ltac solve_covariant_inv_side_conditions :=
  try match goal with
  | |- type_equal _ _ _ ?T ?T _ =>
    treflexivity
  | |- subtype _ _ _ (typ_meet ?T1 ?T2) ?T1 _ =>
    auto using subtype_lower_bound_l with kinding wellformed
  | |- subtype _ _ _ (typ_meet ?T1 ?T2) ?T2 _ =>
    auto using subtype_lower_bound_r with kinding wellformed
  | Hs1 : subtype _ _ _ ?T1 ?T2 _,
    Hs2 : subtype _ _ _ ?T1 ?T3 _
    |- subtype _ _ _ ?T1 (typ_meet ?T2 ?T3) _ =>
    apply subtype_greatest_lower_bound;
    auto using valid_tenv_extend
  | |- @eq bool ?s1 ?s2 =>
    try ring;
    repeat match goal with
    | s : bool |- _ => destruct s
    end; solve [auto]
  | Hs : subtype _ _ _ ?T1 (typ_meet ?T2 ?T3) _
    |- subtype _ _ _ ?T1 ?T2 _ =>
    rewrite Hs;
    apply subtype_lower_bound_l;
    auto with kinding wellformed
  | Hs : subtype _ _ _ ?T1 (typ_meet ?T2 ?T3) _
    |- subtype _ _ _ ?T1 ?T3 _ =>
    rewrite Hs;
    apply subtype_lower_bound_r;
    auto with kinding wellformed
  | Hs : subtype _ _ _ ?T1 (typ_join ?T2 ?T3) _ |-
    type_equal _ _ _ ?T1
      (typ_join (typ_meet ?T1 ?T2) (typ_meet ?T1 ?T3)) _ =>
    rewrite <- type_equal_meet_distribution
      by auto with kinding;
    auto
  | Hte1 : type_equal _ _ _ ?T1 (typ_join ?T2 ?T3) _,
    Hte2 : type_equal _ _ _ ?T3 (typ_bot _) _,
    Hs : subtype _ _ _ ?T2 ?T4 _
    |- subtype _ _ _ ?T1 (typ_join ?T4 _) _ =>
    rewrite Hte1;
    rewrite Hte2;
    rewrite type_equal_join_identity
      by auto with kinding;
    rewrite <- subtype_upper_bound_l
      by auto with kinding wellformed;
    rewrite Hs;
    sreflexivity
  | Hte1 : type_equal _ _ _ ?T1 (typ_join ?T2 ?T3) _,
    Hte2 : type_equal _ _ _ ?T2 (typ_bot _) _,
    Hs : subtype _ _ _ ?T3 ?T4 _
    |- subtype _ _ _ ?T1 (typ_join _ ?T4) _ =>
    rewrite Hte1;
    rewrite Hte2;
    rewrite type_equal_join_commutative
      by auto with kinding;
    rewrite type_equal_join_identity
      by auto with kinding;
    rewrite <- subtype_upper_bound_r
      by auto with kinding wellformed;
    rewrite Hs;
    sreflexivity
  | Hte : type_equal _ _ _ ?T1 (typ_join ?T2 ?T3) _,
    Hs1 : subtype _ _ _ ?T2 ?T4 _,
    Hs2 : subtype _ _ _ ?T3 ?T5 _
    |- subtype _ _ _ ?T1 (typ_join ?T4 ?T5) _ =>
    rewrite Hte;
    apply subtype_least_upper_bound;
      try rewrite Hs1; try rewrite Hs2;
      auto using valid_tenv_extend,
        subtype_upper_bound_l, subtype_upper_bound_r
          with kinding wellformed
  | Hte : type_equal _ _ _ ?T1 ?T2 _,
    Hs : subtype _ _ _ ?T3 ?T1 _
    |- subtype _ _ _ ?T3 ?T2 _ =>
    rewrite Hs;
    rewrite Hte;
    sreflexivity
  | Hte : type_equal _ _ _ ?T1 ?T2 _,
    Hs : subtype _ _ _ ?T3 ?T2 _
    |- subtype _ _ _ ?T3 ?T1 _ =>
    rewrite Hs;
    rewrite Hte;
    sreflexivity
  | Hi : covariant_inv ?z ?s _ _ _ ?Tsl ?Tt |-
    covariant_inv _ _ _ _ _ (typ_meet ?Tsl _) ?Tt =>
    apply covariant_inv_sub
      with (s1 := s) (K1 := cov_input_kind z) (T1 := Tsl);
      auto using subtype_lower_bound_l, leb_lower_bound_l
        with kinding wellformed
  | Hi : covariant_inv ?z ?s _ _ _ ?Tsr ?Tt |-
    covariant_inv _ _ _ _ _ (typ_meet _ ?Tsr) ?Tt =>
    apply covariant_inv_sub
      with (s1 := s) (K1 := cov_input_kind z) (T1 := Tsr);
      auto using subtype_lower_bound_r, leb_lower_bound_r
        with kinding wellformed
  | Hi : covariant_inv _ ?s1 _ _ _ ?Tsl ?Tt,
    Hte1 : type_equal _ _ _ ?Ts (typ_join ?Tsl ?Tsr) _,
    Hte2 : type_equal _ _ _ ?Tsr (typ_bot _) _ |-
    covariant_inv _ ?s2  _ _ _ ?Ts ?Tt =>
    rewrite Hte1;
    rewrite Hte2;
    rewrite type_equal_join_identity by auto with kinding;
    replace s2 with s1 by ring;
    assumption
  | Hi : covariant_inv _ ?s1 _ _ _ ?Tsr ?Tt,
    Hte1 : type_equal _ _ _ ?Ts (typ_join ?Tsl ?Tsr) _,
    Hte2 : type_equal _ _ _ ?Tsl (typ_bot _) _ |-
    covariant_inv _ ?s2  _ _ _ ?Ts ?Tt =>
    rewrite Hte1;
    rewrite Hte2;
    rewrite type_equal_join_commutative by auto with kinding;
    rewrite type_equal_join_identity by auto with kinding;
    replace s2 with s1 by ring;
    assumption
  | Hil : covariant_inv _ ?s1 _ _ _ ?Tsl ?Tt,
    Hir : covariant_inv _ ?s2 _ _ _ ?Tsr ?Tt,
    Hte : type_equal _ _ _ ?Ts (typ_join ?Tsl ?Tsr) _ |-
    covariant_inv _ (orb ?s1 ?s2) _ _ _ ?Ts ?Tt =>
    rewrite Hte;
    apply covariant_inv_upper_bound;
    auto with kinding wellformed
  | Hil : covariant_inv _ ?s1 _ _ _ ?Tsl ?Tt,
    Hir : covariant_inv _ ?s2 _ _ _ ?Tsr ?Tt
    |- covariant_inv _ (orb ?s1 ?s2) _ _ _
                     (typ_join ?Tsl ?Tsr) ?Tt =>
    apply covariant_inv_upper_bound;
    auto with kinding wellformed
  | H1 : CSet.In ?c ?cs1,
    H2 : ~ CSet.In ?c ?cs1 |- _ =>
    contradiction
  | Hk : kinding _ _ (typ_or ?cs1 ?cs2 _ _) _,
    H1 : CSet.In ?c ?cs1,
    H2 : CSet.In ?c ?cs2 |- _ =>
    inversion Hk; subst;
    assert (~ CSet.In c cs1) by csetdec;
    contradiction
  | Hk : kinding _ _ (typ_or ?cs _ (typ_or _ _ _ _) _) _
    |- CSet.In _ ?cs =>
    inversion Hk; subst;
    match goal with
    | Hk' : kinding _ _ (typ_or _ _ _ _) (knd_row cs) |- _ =>
      inversion Hk'; subst;
      csetdec
    end
  | |- CSet.In _ _ =>
    invert_kindings_cov;
    csetdec
  end.

Lemma type_equal_core_covariant_inv_l :
  forall z s v E1 E2 T1 T2 T3,
    covariant_inv z s v E1 E2 T1 T2 ->
    type_equal_core v T2 T3 (cov_output_kind z) ->
    valid_covariant_context z ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    kinding (E1 & E2) empty T1 (cov_input_kind z) ->
    kinding E1 E2 T2 (cov_output_kind z) ->
    kinding E1 E2 T3 (cov_output_kind z) ->
    covariant_inv z s v E1 E2 T1 T3.
Proof.
  introv Hi Hte Hz He1 He2 Hk1 Hk2 Hk3.
  remember (cov_output_kind z) as K.
  destruct Hte; invert_covariant_inv;
    invert_cov_output_kind_equality HeqK; subst;
    construct_covariant_inv; solve_covariant_inv_side_conditions.
  - invert_kindings_cov.
    assert (not (CSet.In c0 cs2)) by csetdec.
    contradiction.
  - invert_kindings_cov.
    assert (not (CSet.In c0 cs1)) by csetdec.
    contradiction.
  - rewrite <- type_equal_meet_distribution by auto with kinding.
    subst_equal T1 at 2.
    rewrite <- type_equal_meet_idempotent
      by auto with kinding wellformed.
    subst_equal T1.
    treflexivity.
  - subst_equal T1.
    rewrite type_equal_join_commutative by auto with kinding.
    treflexivity.
  - rewrite <- type_equal_join_associative by auto with kinding.
    rewrite <- type_equal_join_idempotent
      by auto with kinding wellformed.
    subst_equal T1.
    treflexivity.
  - subst_equal T1.
    subst_equal T5.
    rewrite type_equal_join_associative by auto with kinding.
    treflexivity.
Qed.

Lemma type_equal_core_covariant_inv_r :
  forall z s v E1 E2 T1 T2 T3,
    covariant_inv z s v E1 E2 T1 T2 ->
    type_equal_core v T3 T2 (cov_output_kind z) ->
    valid_covariant_context z ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    kinding (E1 & E2) empty T1 (cov_input_kind z) ->
    kinding E1 E2 T2 (cov_output_kind z) ->
    kinding E1 E2 T3 (cov_output_kind z) ->
    covariant_inv z s v E1 E2 T1 T3.
Proof.
  introv Hi Hte Hz He1 He2 Hk1 Hk2 Hk3.
  remember (cov_output_kind z) as K.
  destruct Hte; invert_covariant_inv;
    invert_cov_output_kind_equality HeqK; subst;
    construct_covariant_inv; solve_covariant_inv_side_conditions.
  - apply covariant_inv_join
      with (s1 := s) (s2 := false)
           (T2 := T1) (T3 := typ_bot (cov_input_kind z));
      construct_covariant_inv;
      solve_covariant_inv_side_conditions.
    rewrite type_equal_join_identity
      by auto with kinding wellformed.
    treflexivity.
  - subst_equal T1.
    rewrite type_equal_join_commutative by auto with kinding.
    treflexivity.
  - subst_equal T4.
    rewrite type_equal_join_commutative by auto with kinding.
    rewrite type_equal_join_identity by auto with kinding.
    subst_equal T1.
    subst_equal T4.
    treflexivity.
  - subst_equal T1.
    subst_equal T4.
    rewrite type_equal_join_associative by auto with kinding.
    treflexivity.
  - rewrite type_equal_join_identity
      by auto with kinding wellformed.
    treflexivity.
  - apply covariant_inv_join
      with (s1 := s) (s2 := false)
           (T2 := T1) (T3 := typ_bot (cov_input_kind z));
      construct_covariant_inv;
      solve_covariant_inv_side_conditions.
    rewrite type_equal_join_identity
      by auto with kinding wellformed.
    treflexivity.
  - apply covariant_inv_bot.
    subst_equal T1.
    rewrite type_equal_meet_annihilation_l
      by auto with kinding wellformed.
    treflexivity.
  - rewrite type_equal_join_distribution
      by auto with kinding.
    subst_equal <- T1.
    subst_equal T1 at 3.
    rewrite type_equal_meet_annihilation_r
      by auto with kinding wellformed.
    subst_equal T1.
    treflexivity.
  - rewrite <- type_equal_join_associative
      by auto with kinding.
    rewrite type_equal_join_distribution
      by auto with kinding.
    subst_equal <- T1.
    rewrite type_equal_join_distribution
      by auto with kinding.
    rewrite type_equal_join_commutative
      with (T1 := T6) (T2 := T5)
      by auto with kinding.
    rewrite type_equal_join_associative
      by auto with kinding.
    subst_equal <- T1.
    rewrite H2 at 2.
    rewrite type_equal_join_associative
      by auto with kinding.
    rewrite <- type_equal_join_idempotent
      by auto with kinding wellformed.
    subst_equal <- T1.
    rewrite type_equal_meet_absorption
      by auto with kinding.
    treflexivity.
Qed.

Lemma type_equal_covariant_inv' :
  forall z s v E1 E2 E3 T1 T2 T3,
    type_equal v E1 (E2 & E3) T2 T3 (cov_output_kind z) ->
    kinding (E1 & E2 & E3) empty T1 (cov_input_kind z) ->
    kinding (E1 & E2) E3 T2 (cov_output_kind z) ->
    kinding (E1 & E2) E3 T3 (cov_output_kind z) ->
    valid_covariant_context z ->
    valid_tenv v (E1 & E2) ->
    valid_tenv_extension v (E1 & E2) E3 ->
    (forall z s X T4 T5 T6,
        binds X (Rng T5 T6 (cov_output_kind z)) E1 ->
        valid_covariant_context z ->
        kinding (E1 & E2 & E3) empty T4 (cov_input_kind z) ->
        covariant_inv z s v (E1 & E2) E3 T4 T5 ->
        covariant_inv z s v (E1 & E2) E3 T4 T6) ->
    covariant_inv z s v (E1 & E2) E3 T1 T2 <->
    covariant_inv z s v (E1 & E2) E3 T1 T3.
Proof.
  introv Hte Hk1 Hk2 Hk3 Hz He1 He2 Hb.
  remember (cov_output_kind z) as K.
  remember (E2 & E3) as E23.
  generalize dependent z.
  generalize dependent s.
  generalize dependent T1.
  induction Hte; introv Heq Hk1 Hz; subst;
    autorewrite with rew_env_concat in *;
    split; introv Hi; invert_covariant_inv; subst;
      construct_covariant_inv;
      solve_covariant_inv_side_conditions.
  - apply binds_tenv_weakening_l; auto with wellformed.
  - apply binds_tenv_weakening_l; auto with wellformed.
  - eauto.
  - apply binds_tenv_weakening_l; auto with wellformed.
  - rewrite <- IHHte1 by auto with kinding; auto.
  - rewrite <- IHHte2 by auto with kinding; auto.
  - rewrite IHHte1 by auto with kinding; auto.
  - rewrite IHHte2 by auto with kinding; auto.
  - rewrite <- IHHte
      by (invert_kindings_cov; auto with kinding); auto.
  - rewrite IHHte
      by (invert_kindings_cov; auto with kinding); auto.
  - rewrite <- IHHte1 by auto with kinding; auto.
  - rewrite <- IHHte2 by auto with kinding; auto.
  - rewrite IHHte1 by auto with kinding; auto.
  - rewrite IHHte2 by auto with kinding; auto.
  - apply covariant_inv_join
      with (s1 := s2) (s2 := s3) (T2 := T4) (T3 := T5);
      solve_covariant_inv_side_conditions; auto.
    + rewrite <- IHHte1 by auto with kinding; auto.
    + rewrite <- IHHte2 by auto with kinding; auto.
  - apply covariant_inv_join
      with (s1 := s2) (s2 := s3) (T2 := T4) (T3 := T5);
      solve_covariant_inv_side_conditions; auto.
    + rewrite IHHte1 by auto with kinding; auto.
    + rewrite IHHte2 by auto with kinding; auto.
  - apply type_equal_core_covariant_inv_l with T1; auto.
  - apply type_equal_core_covariant_inv_r with T1'; auto.
  - rewrite IHHte by auto; auto.
  - rewrite <- IHHte by auto; auto.
  - apply type_equal_extend in Hte1;
      auto using type_environment_extend_inv with wellformed.
    rewrite <- IHHte2 by auto with kinding.
    rewrite <- IHHte1 by auto with kinding; auto.
  - apply type_equal_extend in Hte1;
      auto using type_environment_extend_inv with wellformed.
    rewrite IHHte1 by auto with kinding.
    rewrite IHHte2 by auto with kinding; auto.
Qed.

Lemma subtype_covariant_inv' : forall z s v E1 E2 E3 T1 T2 T3,
    subtype v E1 (E2 & E3)T2 T3 (cov_output_kind z) ->
    kinding (E1 & E2 & E3) empty T1 (cov_input_kind z) ->
    kinding (E1 & E2) E3 T2 (cov_output_kind z) ->
    kinding (E1 & E2) E3 T3 (cov_output_kind z) ->
    valid_covariant_context z ->
    valid_tenv v (E1 & E2)->
    valid_tenv_extension v (E1 & E2) E3 ->
    (forall z s X T4 T5 T6,
        binds X (Rng T5 T6 (cov_output_kind z)) E1 ->
        valid_covariant_context z ->
        kinding (E1 & E2 & E3) empty T4 (cov_input_kind z) ->
        covariant_inv z s v (E1 & E2) E3 T4 T5 ->
        covariant_inv z s v (E1 & E2) E3 T4 T6) ->
    covariant_inv z s v (E1 & E2) E3 T1 T2 ->
    covariant_inv z s v (E1 & E2) E3 T1 T3.
Proof.
  introv Hs Hk1 Hk2 Hk3 Hz He1 He2 Hb Hi.
  unfold subtype in Hs.
  assert (covariant_inv z s v (E1 & E2) E3
            T1 (typ_meet T2 T3)) as Hi2
    by (rewrite type_equal_covariant_inv' with (T3 := T2); auto).
  inversion Hi2; subst; auto.
Qed.

Lemma valid_tenv_rec_covariant_inv : forall v E1 E2 E3,
    valid_tenv_rec v empty E1 (E2 & E3) ->
    valid_tenv v (E1 & E2) ->
    valid_tenv_extension v (E1 & E2) E3 ->
    (forall z s X T1 T2 T3,
        binds X (Rng T2 T3 (cov_output_kind z)) E1 ->
        valid_covariant_context z ->
        kinding (E1 & E2 & E3) empty T1 (cov_input_kind z) ->
        covariant_inv z s v (E1 & E2) E3 T1 T2 ->
        covariant_inv z s v (E1 & E2) E3 T1 T3).
Proof.
  introv He1 He2 He3.
  remember empty as E0.
  remember (E2 & E3) as E23.
  generalize dependent E2.
  induction He1; introv Heq He2 He3 Hb Hz Hk Hi; subst.
  - exfalso; eauto using binds_empty_inv.
  - destruct (binds_push_inv Hb) as [[? ?]|[Hx Hbnd2]]; subst;
      autorewrite with rew_env_concat in *.
    + assert (valid_range v E2
                (X ~ Rng T2 T3 (cov_output_kind z) & E4 & E3)
                (Rng T2 T3 (cov_output_kind z))) as Hr by auto.
      inversion Hr; subst.
      rewrite <- concat_assoc with (E := E2).
      apply subtype_covariant_inv' with T2;
        try solve [autorewrite with rew_env_concat; eauto];
        try solve
            [apply kinding_extend; auto;
             apply type_environment_extend_inv;
               autorewrite with rew_env_concat;
               auto with wellformed].
      apply IHHe1; autorewrite with rew_env_concat; auto.
    + rewrite <- concat_assoc with (E := E2).
      eapply IHHe1; autorewrite with rew_env_concat; eauto.
Qed.

Lemma type_equal_covariant_inv :
  forall z s v E1 E2 T1 T2 T3,
    type_equal v E1 E2 T2 T3 (cov_output_kind z) ->
    kinding (E1 & E2) empty T1 (cov_input_kind z) ->
    valid_covariant_context z ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    covariant_inv z s v E1 E2 T1 T2 <->
    covariant_inv z s v E1 E2 T1 T3.
Proof.
  introv Hte Hk Hz He1 He2.
  replace E1 with (E1 & empty) by apply concat_empty_r.
  apply type_equal_covariant_inv';
    autorewrite with rew_env_concat; auto with kinding.
  introv Hb' Hz' Hk' Hi'.
  rewrite <- concat_empty_r with (E := E1).
  eapply valid_tenv_rec_covariant_inv;
    autorewrite with rew_env_concat; eauto.
  rewrite <- concat_empty_r with (E := E2).
  apply valid_tenv_rec_weakening_rec_r;
    autorewrite with rew_env_concat;
    try fold (type_environment E1);
    auto with wellformed.
Qed.

Lemma subtype_covariant_inv :
  forall z s v E1 E2 T1 T2 T3,
    subtype v E1 E2 T2 T3 (cov_output_kind z) ->
    kinding (E1 & E2) empty T1 (cov_input_kind z) ->
    valid_covariant_context z ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    covariant_inv z s v E1 E2 T1 T2 ->
    covariant_inv z s v E1 E2 T1 T3.
Proof.
  introv Hs Hk Hz He1 He2 Hi.
  unfold subtype in Hs.
  assert (covariant_inv z s v E1 E2 T1 (typ_meet T2 T3)) as Hi2
    by (rewrite type_equal_covariant_inv with (T3 := T2); auto).
  inversion Hi2; subst; auto.
Qed.

Lemma invert_subtype_variant : forall v E1 E2 T1 T2,
    subtype v E1 E2 (typ_variant T1) (typ_variant T2) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    subtype v (E1 & E2) empty T1 T2 knd_row_all.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_variant true v E1 E2 T1 (typ_variant T1))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_variant true v E1 E2 T1 (typ_variant T2))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi; subst; auto.
Qed.

Lemma invert_subtype_arrow_left_row_covariant : forall E1 E2 T1 T2 T3 T4,
    subtype version_row_subtyping E1 E2
      (typ_arrow T1 T2) (typ_arrow T3 T4) knd_type ->
    valid_tenv version_row_subtyping E1 ->
    valid_tenv_extension version_row_subtyping E1 E2 ->
    subtype version_row_subtyping (E1 & E2) empty T1 T3 knd_type.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_arrow_left_row true version_row_subtyping
            E1 E2 T1 (typ_arrow T1 T2))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_arrow_left_row true version_row_subtyping
            E1 E2 T1 (typ_arrow T3 T4))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi; subst; auto.
Qed.

Lemma invert_subtype_arrow_right : forall v E1 E2 T1 T2 T3 T4,
    subtype v E1 E2 (typ_arrow T1 T2) (typ_arrow T3 T4) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    subtype v (E1 & E2) empty T2 T4 knd_type.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_arrow_right true v E1 E2
                      T2 (typ_arrow T1 T2))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_arrow_right true v E1 E2
                      T2 (typ_arrow T3 T4))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi; subst; auto.
Qed.

Lemma invert_subtype_ref_covariant : forall v E1 E2 T1 T2,
    subtype v E1 E2 (typ_ref T1) (typ_ref T2) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    subtype v (E1 & E2) empty T1 T2 knd_type.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_ref_co true v E1 E2 T1 (typ_ref T1))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_ref_co true v E1 E2 T1 (typ_ref T2))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi; subst; auto.
Qed.

Lemma invert_subtype_prod_left : forall v E1 E2 T1 T2 T3 T4,
    subtype v E1 E2 (typ_prod T1 T2) (typ_prod T3 T4) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    subtype v (E1 & E2) empty T1 T3 knd_type.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_prod_left true v E1 E2
                      T1 (typ_prod T1 T2))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_prod_left true v E1 E2
                      T1 (typ_prod T3 T4))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi; subst; auto.
Qed.

Lemma invert_subtype_prod_right : forall v E1 E2 T1 T2 T3 T4,
    subtype v E1 E2 (typ_prod T1 T2) (typ_prod T3 T4) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    subtype v (E1 & E2) empty T2 T4 knd_type.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_prod_right true v E1 E2
                      T2 (typ_prod T1 T2))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_prod_right true v E1 E2
                      T2 (typ_prod T3 T4))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi; subst; auto.
Qed.

Lemma invert_subtype_constructor : forall v c cs E1 E2 T1 T2,
    subtype v E1 E2 (typ_constructor c T1)
      (typ_constructor c T2) (knd_row cs)->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    subtype v (E1 & E2) empty T1 T2 knd_type.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv (ctx_constructor c cs) true v E1 E2
            T1 (typ_constructor c T1))
    by auto using subtype_refl with kinding wellformed.
  assert (kinding E1 E2 (typ_constructor c T1) (knd_row cs)) as Hk
      by auto with kinding.
  inversion Hk; subst.
  assert (covariant_inv (ctx_constructor c (CSet.singleton c))
            true v E1 E2 T1 (typ_constructor c T2))
    as Hi by eauto using subtype_covariant_inv with kinding csetdec.
  inversion Hi; subst; auto.
Qed.

(* *************************************************************** *)
(** Impossible subtyping inversions *)

Lemma invert_subtype_variant_arrow : forall v E1 E2 T1 T2 T3,
    subtype v E1 E2 (typ_variant T1) (typ_arrow T2 T3) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_variant true v E1 E2 T1 (typ_variant T1))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_variant true v E1 E2 T1 (typ_arrow T2 T3))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_variant_ref : forall v E1 E2 T1 T2,
    subtype v E1 E2 (typ_variant T1) (typ_ref T2) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_variant true v E1 E2 T1 (typ_variant T1))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_variant true v E1 E2 T1 (typ_ref T2))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_variant_unit : forall v E1 E2 T1,
    subtype v E1 E2 (typ_variant T1) typ_unit knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_variant true v E1 E2 T1 (typ_variant T1))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_variant true v E1 E2 T1 typ_unit)
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_variant_prod : forall v E1 E2 T1 T2 T3,
    subtype v E1 E2 (typ_variant T1) (typ_prod T2 T3) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_variant true v E1 E2 T1 (typ_variant T1))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_variant true v E1 E2 T1 (typ_prod T2 T3))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_variant_bot : forall v E1 E2 T1,
    subtype v E1 E2 (typ_variant T1) (typ_bot knd_type) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_variant true v E1 E2 T1 (typ_variant T1))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_variant true v E1 E2 T1 (typ_bot knd_type))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_arrow_variant : forall v E1 E2 T1 T2 T3,
    subtype v E1 E2 (typ_arrow T1 T2) (typ_variant T3) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_arrow_right true v E1 E2
                      T2 (typ_arrow T1 T2))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_arrow_right true v E1 E2
                        T2 (typ_variant T3))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_arrow_ref : forall v E1 E2 T1 T2 T3,
    subtype v E1 E2 (typ_arrow T1 T2) (typ_ref T3) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_arrow_right true v E1 E2
                      T2 (typ_arrow T1 T2))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_arrow_right true v E1 E2
                        T2 (typ_ref T3))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_arrow_unit : forall v E1 E2 T1 T2,
    subtype v E1 E2 (typ_arrow T1 T2) typ_unit knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_arrow_right true v E1 E2
                      T2 (typ_arrow T1 T2))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_arrow_right true v E1 E2
                        T2 typ_unit)
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_arrow_prod : forall v E1 E2 T1 T2 T3 T4,
    subtype v E1 E2 (typ_arrow T1 T2) (typ_prod T3 T4) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_arrow_right true v E1 E2
                      T2 (typ_arrow T1 T2))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_arrow_right true v E1 E2
                        T2 (typ_prod T3 T4))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_arrow_bot : forall v E1 E2 T1 T2,
    subtype v E1 E2 (typ_arrow T1 T2) (typ_bot knd_type) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_arrow_right true v E1 E2
                      T2 (typ_arrow T1 T2))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_arrow_right true v E1 E2
                        T2 (typ_bot knd_type))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_ref_variant : forall v E1 E2 T1 T2,
    subtype v E1 E2 (typ_ref T1) (typ_variant T2) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_ref_co true v E1 E2 T1 (typ_ref T1))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_ref_co true v E1 E2 T1 (typ_variant T2))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_ref_arrow : forall v E1 E2 T1 T2 T3,
    subtype v E1 E2 (typ_ref T1) (typ_arrow T2 T3) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_ref_co true v E1 E2 T1 (typ_ref T1))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_ref_co true v E1 E2 T1 (typ_arrow T2 T3))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_ref_unit : forall v E1 E2 T1,
    subtype v E1 E2 (typ_ref T1) typ_unit knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_ref_co true v E1 E2 T1 (typ_ref T1))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_ref_co true v E1 E2 T1 typ_unit)
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_ref_prod : forall v E1 E2 T1 T2 T3,
    subtype v E1 E2 (typ_ref T1) (typ_prod T2 T3) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_ref_co true v E1 E2 T1 (typ_ref T1))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_ref_co true v E1 E2 T1 (typ_prod T2 T3))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_ref_bot : forall v E1 E2 T1,
    subtype v E1 E2 (typ_ref T1) (typ_bot knd_type) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_ref_co true v E1 E2 T1 (typ_ref T1))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_ref_co true v E1 E2 T1 (typ_bot knd_type))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_unit_variant : forall v E1 E2 T1,
    subtype v E1 E2 typ_unit (typ_variant T1) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_unit true v E1 E2 typ_unit typ_unit)
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_unit true v E1 E2
                        typ_unit (typ_variant T1))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_unit_arrow : forall v E1 E2 T1 T2,
    subtype v E1 E2 typ_unit (typ_arrow T1 T2) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_unit true v E1 E2 typ_unit typ_unit)
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_unit true v E1 E2
                        typ_unit (typ_arrow T1 T2))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_unit_ref : forall v E1 E2 T1,
    subtype v E1 E2 typ_unit (typ_ref T1) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_unit true v E1 E2 typ_unit typ_unit)
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_unit true v E1 E2 typ_unit (typ_ref T1))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_unit_prod : forall v E1 E2 T1 T2,
    subtype v E1 E2 typ_unit (typ_prod T1 T2) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_unit true v E1 E2 typ_unit typ_unit)
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_unit true v E1 E2
                        typ_unit (typ_prod T1 T2))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_unit_bot : forall v E1 E2,
    subtype v E1 E2 typ_unit (typ_bot knd_type) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_unit true v E1 E2 typ_unit typ_unit)
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_unit true v E1 E2
                        typ_unit (typ_bot knd_type))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_prod_variant : forall v E1 E2 T1 T2 T3,
    subtype v E1 E2 (typ_prod T1 T2) (typ_variant T3) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_prod_left true v E1 E2
                      T1 (typ_prod T1 T2))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_prod_left true v E1 E2
                      T1 (typ_variant T3))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_prod_arrow : forall v E1 E2 T1 T2 T3 T4,
    subtype v E1 E2 (typ_prod T1 T2) (typ_arrow T3 T4) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_prod_left true v E1 E2
                      T1 (typ_prod T1 T2))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_prod_left true v E1 E2
                      T1 (typ_arrow T3 T4))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_prod_ref : forall v E1 E2 T1 T2 T3,
    subtype v E1 E2 (typ_prod T1 T2) (typ_ref T3) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_prod_left true v E1 E2
                      T1 (typ_prod T1 T2))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_prod_left true v E1 E2
                      T1 (typ_ref T3))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_prod_unit : forall v E1 E2 T1 T2,
    subtype v E1 E2 (typ_prod T1 T2) typ_unit knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_prod_left true v E1 E2
                      T1 (typ_prod T1 T2))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_prod_left true v E1 E2
                      T1 typ_unit)
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_prod_bot : forall v E1 E2 T1 T2,
    subtype v E1 E2 (typ_prod T1 T2) (typ_bot knd_type) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_prod_left true v E1 E2
                      T1 (typ_prod T1 T2))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_prod_left true v E1 E2
                      T1 (typ_bot knd_type))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_constructor_bot : forall v c cs E1 E2 T1,
    subtype v E1 E2 (typ_constructor c T1)
      (typ_bot (knd_row cs)) (knd_row cs) ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv (ctx_constructor c cs) true v
            E1 E2 T1 (typ_constructor c T1))
    by auto using subtype_refl with kinding wellformed.
  assert (kinding E1 E2 (typ_constructor c T1) (knd_row cs)) as Hk
      by auto with kinding.
  inversion Hk; subst.
  assert (covariant_inv (ctx_constructor c (CSet.singleton c))
             true v E1 E2 T1 (typ_bot (knd_row (CSet.singleton c))))
    as Hi by eauto using subtype_covariant_inv with kinding csetdec.
  inversion Hi.
Qed.

Lemma invert_subtype_top_variant : forall v E1 E2 T1,
    subtype v E1 E2 (typ_top knd_type) (typ_variant T1) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_unit true v E1 E2
                      typ_unit (typ_top knd_type))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_unit true v E1 E2
                      typ_unit (typ_variant T1))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_top_arrow : forall v E1 E2 T1 T2,
    subtype v E1 E2 (typ_top knd_type) (typ_arrow T1 T2) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_unit true v E1 E2
                      typ_unit (typ_top knd_type))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_unit true v E1 E2
                      typ_unit (typ_arrow T1 T2))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_top_ref : forall v E1 E2 T1,
    subtype v E1 E2 (typ_top knd_type) (typ_ref T1) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_unit true v E1 E2
                      typ_unit (typ_top knd_type))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_unit true v E1 E2
                      typ_unit (typ_ref T1))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_top_unit : forall v E1 E2,
    subtype v E1 E2 (typ_top knd_type) typ_unit knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_ref_co true v E1 E2
                      typ_unit (typ_top knd_type))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_ref_co true v E1 E2
                      typ_unit typ_unit)
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_top_prod : forall v E1 E2 T1 T2,
    subtype v E1 E2 (typ_top knd_type) (typ_prod T1 T2) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  assert (covariant_inv ctx_unit true v E1 E2
                      typ_unit (typ_top knd_type))
    by auto using subtype_refl with kinding wellformed.
  assert (covariant_inv ctx_unit true v E1 E2
                      typ_unit (typ_prod T1 T2))
    as Hi by eauto using subtype_covariant_inv with kinding.
  inversion Hi.
Qed.

Lemma invert_subtype_top_bot : forall v E1 E2 K,
    subtype v E1 E2 (typ_top K) (typ_bot K) K ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    False.
Proof.
  introv Hs He1 He2.
  destruct K as [| cs].
  - assert (covariant_inv ctx_unit true v E1 E2
                      typ_unit (typ_top knd_type))
      by auto using subtype_refl with kinding wellformed.
    assert (covariant_inv ctx_unit true v E1 E2
                      typ_unit (typ_bot knd_type))
      as Hi by eauto using subtype_covariant_inv with kinding.
    inversion Hi.
  - assert (kind (knd_row cs)) as Hknd by auto with wellformed.
    inversion Hknd; subst.
    assert (CSet.Nonempty cs) as Hne by assumption.
    destruct Hne as [c ?].
    assert (covariant_inv (ctx_constructor c cs) true v E1 E2
                      typ_unit (typ_top (knd_row cs)))
      by auto using subtype_refl with kinding wellformed.
    assert (covariant_inv (ctx_constructor c cs) true v E1 E2
                      typ_unit (typ_bot (knd_row cs)))
      as Hi by eauto using subtype_covariant_inv with kinding.
    inversion Hi.
Qed.

(* *************************************************************** *)
(** Contravariant subtyping inversions *)

(* Type representing contravariant (and invariant) contexts *)
Inductive contravariant_context : Type :=
  | ctx_arrow_left : contravariant_context
  | ctx_arrow_right_row : contravariant_context
  | ctx_ref_contra : contravariant_context
  | ctx_prod_left_row : contravariant_context
  | ctx_prod_right_row : contravariant_context
  | ctx_constructor_row : nat -> cset -> contravariant_context.
  
Definition con_input_kind z :=
  match z with
  | ctx_arrow_left => knd_type
  | ctx_arrow_right_row => knd_type
  | ctx_ref_contra => knd_type
  | ctx_prod_left_row => knd_type
  | ctx_prod_right_row => knd_type
  | ctx_constructor_row _ _ => knd_type
  end.

Definition con_output_kind z :=
  match z with
  | ctx_arrow_left => knd_type
  | ctx_arrow_right_row => knd_type
  | ctx_ref_contra => knd_type
  | ctx_prod_left_row => knd_type
  | ctx_prod_right_row => knd_type
  | ctx_constructor_row _ cs => knd_row cs
  end.

Inductive valid_contravariant_context : contravariant_context -> Prop :=
  | valid_ctx_arrow_left :
      valid_contravariant_context ctx_arrow_left
  | valid_ctx_arrow_right_row :
      valid_contravariant_context ctx_arrow_right_row
  | valid_ctx_ref_contra : valid_contravariant_context ctx_ref_contra
  | valid_ctx_prod_left_row :
      valid_contravariant_context ctx_prod_left_row
  | valid_ctx_prod_right_row :
      valid_contravariant_context ctx_prod_right_row
  | valid_ctx_constructor_row : forall c cs,
      CSet.In c cs ->
      valid_contravariant_context (ctx_constructor_row c cs).

Hint Constructors valid_contravariant_context.

Inductive contravariant_inv :
  contravariant_context -> bool -> version -> tenv -> tenv ->
  typ -> typ -> Prop :=
  | contravariant_inv_meet : forall z s v E1 E2 T1 T2 T3,
      contravariant_inv z s v E1 E2 T1 T2 ->
      contravariant_inv z s v E1 E2 T1 T3 ->
      contravariant_inv z s v E1 E2 T1 (typ_meet T2 T3)
  | contravariant_inv_join : forall z s1 s2 s3 v E1 E2 T1 T2 T3 T4 T5,
      contravariant_inv z s1 v E1 E2 T2 T4 ->
      contravariant_inv z s2 v E1 E2 T3 T5 ->
      type_equal v (E1 & E2) empty T1
                 (typ_meet T2 T3) (con_input_kind z) ->
      s3 = orb s1 s2 ->
      contravariant_inv z s3 v E1 E2 T1 (typ_join T4 T5)
  | contravariant_inv_top : forall z s v E1 E2 K2 T1,
      contravariant_inv z s v E1 E2 T1 (typ_top K2)
  | contravariant_inv_var : forall z s v E1 E2 X T1 T2 T3,
      binds X (Rng T2 T3 (con_output_kind z)) E1 ->
      contravariant_inv z s v E1 E2 T1 T2 ->
      contravariant_inv z s v E1 E2 T1 (typ_fvar X)
  | contravariant_inv_arrow_left : forall s v E1 E2 T1 T2 T3,
      subtype v (E1 & E2) empty T2 T1 knd_type ->
      contravariant_inv ctx_arrow_left s v
        E1 E2 T1 (typ_arrow T2 T3)
  | contravariant_inv_arrow_right : forall s E1 E2 T1 T2 T3,
      subtype version_row_subtyping (E1 & E2) empty T3 T1 knd_type ->
      contravariant_inv ctx_arrow_right_row s version_row_subtyping
        E1 E2 T1 (typ_arrow T2 T3)
  | contravariant_inv_ref : forall s v E1 E2 T1 T2,
      subtype v (E1 & E2) empty T2 T1 knd_type ->
      contravariant_inv ctx_ref_contra s v E1 E2 T1 (typ_ref T2)
  | contravariant_inv_prod_left : forall s E1 E2 T1 T2 T3,
      subtype version_row_subtyping (E1 & E2) empty T2 T1 knd_type ->
      contravariant_inv ctx_prod_left_row s version_row_subtyping
        E1 E2 T1 (typ_prod T2 T3)
  | contravariant_inv_prod_right : forall s E1 E2 T1 T2 T3,
      subtype version_row_subtyping (E1 & E2) empty T3 T1 knd_type ->
      contravariant_inv ctx_prod_right_row s version_row_subtyping
        E1 E2 T1 (typ_prod T2 T3)
  | contravariant_inv_or_l : forall c s v E1 E2 cs1 cs2 cs3 T1 T2 T3,
      contravariant_inv (ctx_constructor_row c cs1) s v E1 E2 T1 T2 ->
      CSet.In c cs1 ->
      contravariant_inv (ctx_constructor_row c cs3) s
        v E1 E2 T1 (typ_or cs1 cs2 T2 T3)
  | contravariant_inv_or_r : forall c s v E1 E2 cs1 cs2 cs3 T1 T2 T3,
      contravariant_inv (ctx_constructor_row c cs2) s v E1 E2 T1 T3 ->
      CSet.In c cs2 ->
      contravariant_inv (ctx_constructor_row c cs3) s
        v E1 E2 T1 (typ_or cs1 cs2 T2 T3)
  | contravariant_inv_proj : forall c s v E1 E2 cs1 cs2 T1 T2,
      contravariant_inv (ctx_constructor_row c cs1) s v E1 E2 T1 T2 ->
      contravariant_inv (ctx_constructor_row c cs2) s
        v E1 E2 T1 (typ_proj cs1 cs2 T2)
  | contravariant_inv_constructor : forall c cs s E1 E2 T1 T2,
      subtype version_row_subtyping (E1 & E2) empty T2 T1 knd_type ->
      contravariant_inv (ctx_constructor_row c cs) s
        version_row_subtyping E1 E2 T1 (typ_constructor c T2)
  | contravariant_inv_bot : forall z v E1 E2 T1 T2,
      type_equal v (E1 & E2) empty T1
        (typ_top (con_input_kind z)) (con_input_kind z) ->
      contravariant_inv z false v E1 E2 T1 T2.

Hint Constructors contravariant_inv.

Lemma contravariant_inv_meet_inv : forall z s v E1 E2 T1 T2 T3 (P : Prop),
    contravariant_inv z s v E1 E2 T1 (typ_meet T2 T3) ->
    (s = false ->
     type_equal v (E1 & E2) empty T1
       (typ_top (con_input_kind z)) (con_input_kind z) ->
     P) ->
    (contravariant_inv z s v E1 E2 T1 T2 ->
     contravariant_inv z s v E1 E2 T1 T3 ->
     P) ->
    P.
Proof.
  introv Hc Hp1 Hp2.
  inversion Hc; auto.
Qed.

Lemma contravariant_inv_join_inv :
  forall z s1 v E1 E2 T1 T2 T3 (P : Prop),
    contravariant_inv z s1 v E1 E2 T1 (typ_join T2 T3) ->
    (s1 = false ->
     type_equal v (E1 & E2) empty T1
       (typ_top (con_input_kind z)) (con_input_kind z) ->
     P) ->
    (forall s2 s3 T4 T5,
        contravariant_inv z s2 v E1 E2 T4 T2 ->
        contravariant_inv z s3 v E1 E2 T5 T3 ->
        type_equal v (E1 & E2) empty T1
                   (typ_meet T4 T5) (con_input_kind z) ->
        s1 = orb s2 s3 ->
        P) ->
    P.
Proof.
  introv Hc Hp1 Hp2.
  inversion Hc; eauto.
Qed.

Lemma contravariant_inv_var_inv : forall z s v E1 E2 X T1 (P : Prop),
    contravariant_inv z s v E1 E2 T1 (typ_fvar X) ->
    (s = false ->
     type_equal v (E1 & E2) empty T1
       (typ_top (con_input_kind z)) (con_input_kind z) ->
     P) ->
    (forall T2 T3,
        binds X (Rng T2 T3 (con_output_kind z)) E1 ->
        contravariant_inv z s v E1 E2 T1 T2 ->
        P) ->
    P.
Proof.
  introv Hc Hp1 Hp2.
  inversion Hc; eauto.
Qed.

Lemma contravariant_inv_variant_inv : forall z s v E1 E2 T1 T2 (P : Prop),
    contravariant_inv z s v E1 E2 T1 (typ_variant T2) ->
    (s = false ->
     type_equal v (E1 & E2) empty T1
       (typ_top (con_input_kind z)) (con_input_kind z) ->
     P) ->
    P.
Proof.
  introv Hc Hp.
  inversion Hc; auto.
Qed.

Lemma contravariant_inv_arrow_inv : forall z s v E1 E2 T1 T2 T3 (P : Prop),
    contravariant_inv z s v E1 E2 T1 (typ_arrow T2 T3) ->
    (s = false ->
     type_equal v (E1 & E2) empty T1
       (typ_top (con_input_kind z)) (con_input_kind z) ->
     P) ->
    (z = ctx_arrow_left ->
     subtype v (E1 & E2) empty T2 T1 knd_type ->
     P) ->
    (z = ctx_arrow_right_row ->
     v = version_row_subtyping ->
     subtype v (E1 & E2) empty T3 T1 knd_type ->
     P) ->
    P.
Proof.
  introv Hc Hp1 Hp2 Hp3.
  inversion Hc; subst; auto.
Qed.

Lemma contravariant_inv_ref_inv : forall z s v E1 E2 T1 T2 (P : Prop),
    contravariant_inv z s v E1 E2 T1 (typ_ref T2) ->
    (s = false ->
     type_equal v (E1 & E2) empty T1
       (typ_top (con_input_kind z)) (con_input_kind z) ->
     P) ->
    (z = ctx_ref_contra ->
     subtype v (E1 & E2) empty T2 T1 knd_type ->
     P) ->
    P.
Proof.
  introv Hc Hp1 Hp2.
  inversion Hc; auto.
Qed.

Lemma contravariant_inv_prod_inv : forall z s v E1 E2 T1 T2 T3 (P : Prop),
    contravariant_inv z s v E1 E2 T1 (typ_prod T2 T3) ->
    (s = false ->
     type_equal v (E1 & E2) empty T1
       (typ_top (con_input_kind z)) (con_input_kind z) ->
     P) ->
    (z = ctx_prod_left_row ->
     v = version_row_subtyping ->
     subtype v (E1 & E2) empty T2 T1 knd_type ->
     P) ->
    (z = ctx_prod_right_row ->
     v = version_row_subtyping ->
     subtype v (E1 & E2) empty T3 T1 knd_type ->
     P) ->
    P.
Proof.
  introv Hc Hp1 Hp2 Hp3.
  inversion Hc; subst; auto.
Qed.

Lemma contravariant_inv_or_inv :
  forall z s v E1 E2 cs1 cs2 T1 T2 T3 (P : Prop),
    contravariant_inv z s v E1 E2 T1 (typ_or cs1 cs2 T2 T3) ->
    (s = false ->
     type_equal v (E1 & E2) empty T1
       (typ_top (con_input_kind z)) (con_input_kind z) ->
     P) ->
    (forall c cs3,
        z = ctx_constructor_row c cs3 ->
        contravariant_inv (ctx_constructor_row c cs1) s v E1 E2 T1 T2 ->
        CSet.In c cs1 ->
        P) ->
    (forall c cs3,
        z = ctx_constructor_row c cs3 ->
        contravariant_inv (ctx_constructor_row c cs2) s v E1 E2 T1 T3 ->
        CSet.In c cs2 ->
        P) ->
    P.
Proof.
  introv Hc Hp1 Hp2 Hp3.
  inversion Hc; eauto.
Qed.

Lemma contravariant_inv_proj_inv :
  forall z s v E1 E2 cs1 cs2 T1 T2 (P : Prop),
    contravariant_inv z s v E1 E2 T1 (typ_proj cs1 cs2 T2) ->
    (s = false ->
     type_equal v (E1 & E2) empty T1
       (typ_top (con_input_kind z)) (con_input_kind z) ->
     P) ->
    (forall c,
        z = ctx_constructor_row c cs2 ->
        contravariant_inv (ctx_constructor_row c cs1) s v E1 E2 T1 T2 ->
        P) ->
    P.
Proof.
  introv Hc Hp1 Hp2.
  inversion Hc; subst; eauto.  
Qed.

Lemma contravariant_inv_constructor_inv :
  forall z s v E1 E2 c T1 T2 (P : Prop),
    contravariant_inv z s v E1 E2 T1 (typ_constructor c T2) ->
    (s = false ->
     type_equal v (E1 & E2) empty T1
       (typ_top (con_input_kind z)) (con_input_kind z) ->
     P) ->
    (forall cs,
        z = ctx_constructor_row c cs ->
        v = version_row_subtyping ->
        subtype v (E1 & E2) empty T2 T1 knd_type ->
        P) ->
    P.
Proof.
  introv Hc Hp1 Hp2.
  inversion Hc; subst; eauto.
Qed.

Lemma contravariant_inv_bot_inv :
  forall z s v E1 E2 T1 K (P : Prop),
    contravariant_inv z s v E1 E2 T1 (typ_bot K) ->
    (s = false ->
     type_equal v (E1 & E2) empty T1
       (typ_top (con_input_kind z)) (con_input_kind z) ->
     P) ->
    P.
Proof.
  introv Hc Hp1.
  inversion Hc; subst; eauto.
Qed.

Ltac invert_ctx_constructor_row_equalities :=
  repeat match goal with
  | Heq : ctx_constructor_row _ _ = ctx_constructor_row _ _ |- _ =>
    inversion Heq; clear Heq
  end.

Ltac discriminate_ctx_prod_row_mismatches :=
  try match goal with
  | Heq : ctx_prod_left_row = ctx_prod_right_row |- _ =>
    discriminate Heq
  | Heq : ctx_prod_right_row = ctx_prod_left_row |- _ =>
    discriminate Heq
  end.

Ltac discriminate_con_ctx_arrow_mismatches :=
  try match goal with
  | Heq : ctx_arrow_left = ctx_arrow_right_row |- _ =>
    discriminate Heq
  | Heq : ctx_arrow_right_row = ctx_arrow_left |- _ =>
    discriminate Heq
  end.

Ltac invert_contravariant_inv :=
  repeat match goal with
  | H : contravariant_inv _ _ _ _ _ _ (typ_constructor _ _) |- _ =>
    apply (contravariant_inv_constructor_inv H); clear H; intros;
    invert_ctx_constructor_row_equalities; subst;
    discriminate_version
  | H : contravariant_inv _ _ _ _ _ _ (typ_or _ _ _ _) |- _ =>
    apply (contravariant_inv_or_inv H); clear H; intros;
    invert_ctx_constructor_row_equalities; subst
  | H : contravariant_inv _ _ _ _ _ _ (typ_proj _ _ _) |- _ =>
    apply (contravariant_inv_proj_inv H); clear H; intros;
    invert_ctx_constructor_row_equalities; subst
  | H : contravariant_inv _ _ _ _ _ _ (typ_variant _) |- _ =>
    apply (contravariant_inv_variant_inv H); clear H; intros;
    subst; discriminate_version
  | H : contravariant_inv _ _ _ _ _ _ (typ_arrow _ _) |- _ =>
    apply (contravariant_inv_arrow_inv H); clear H; intros;
    subst; discriminate_con_ctx_arrow_mismatches;
    discriminate_version
  | H : contravariant_inv _ _ _ _ _ _ (typ_ref _) |- _ =>
    apply (contravariant_inv_ref_inv H); clear H; intros
  | H : contravariant_inv _ _ _ _ _ _ (typ_prod _ _) |- _ =>
    apply (contravariant_inv_prod_inv H); clear H; intros;
    subst; discriminate_ctx_prod_row_mismatches;
    discriminate_version
  | H : contravariant_inv _ _ _ _ _ _ (typ_fvar _) |- _ =>
    apply (contravariant_inv_var_inv H); clear H; intros;
    equate_multiple_bindings
  | H : contravariant_inv _ _ _ _ _ _ (typ_bot _) |- _ =>
    apply (contravariant_inv_bot_inv H); clear H; intros
  | H : contravariant_inv _ _ _ _ _ _ (typ_meet _ _) |- _ =>
    apply (contravariant_inv_meet_inv H); clear H; intros
  | H : contravariant_inv _ _ _ _ _ _ (typ_join _ _) |- _ =>
    apply (contravariant_inv_join_inv H); clear H; intros
  end.

Ltac choose_contravariant_inv_join_type z Td T :=
  match T with
  | typ_meet ?T1 ?T2 =>
    let T1' := choose_contravariant_inv_join_type z Td T1 in
    let T2' := choose_contravariant_inv_join_type z Td T2 in
    constr:(typ_join T1' T2')
  | typ_join ?T1 ?T2 =>
    let T1' := choose_contravariant_inv_join_type z Td T1 in
    let T2' := choose_contravariant_inv_join_type z Td T2 in
    constr:(typ_meet T1' T2')
  | typ_or ?cs1 ?cs2 ?T1 ?T2 =>
    match z with
    | ctx_constructor_row ?c _ =>
      match goal with
      | Hin : CSet.In c cs1 |- _ =>
        choose_contravariant_inv_join_type z Td T1
      | Hin : CSet.In c cs2 |- _ =>
        choose_contravariant_inv_join_type z Td T2
      end
    end
  | typ_proj _ _ ?T1 =>
    choose_contravariant_inv_join_type z Td T1
  | typ_variant ?T1 => constr:(typ_join Td T1)
  | typ_constructor _ ?T1 => constr:(typ_join Td T1)
  | typ_ref ?T1 => constr:(typ_join Td T1)
  | typ_arrow ?T1 ?T2 =>
    match z with
    | ctx_arrow_left => constr:(typ_join Td T1)
    | ctx_arrow_right_row => constr:(typ_join Td T2)
    end
  | typ_prod ?T1 ?T2 =>
    match z with
    | ctx_prod_left_row => constr:(typ_join Td T1)
    | ctx_prod_right_row => constr:(typ_join Td T2)
    end
  | typ_bot (con_output_kind ?z) => constr:(typ_top (con_input_kind z))
  | typ_fvar ?X =>
      match goal with
      | Hb : binds X (Rng _ ?Tu _) _,
        Hi : contravariant_inv _ _ _ _ _ ?Tt ?Tu
        |- _ => constr:(Tt)
      end
  | _ =>
    match goal with
    | H1 : contravariant_inv _ _ _ _ _ ?Tt1 T,
      H2 : contravariant_inv _ _ _ _ _ ?Tt2 T
      |- _ => constr:(typ_meet Tt1 Tt2)
    | H : contravariant_inv _ _ _ _ _ ?Tt T |- _ =>
      constr:(Tt)
    | Hte : type_equal _ _ _ ?Tb (typ_top _) _ |- _ =>
      constr:(Tb)
    end
  end.

Ltac choose_contravariant_inv_join_bool z sd T :=
  match T with
  | typ_meet ?T1 ?T2 =>
    let s1 := choose_contravariant_inv_join_bool z sd T1 in
    let s2 := choose_contravariant_inv_join_bool z sd T2 in
    constr:(andb s1 s2)
  | typ_join ?T1 ?T2 =>
    let s1 := choose_contravariant_inv_join_bool z sd T1 in
    let s2 := choose_contravariant_inv_join_bool z sd T2 in
    constr:(orb s1 s2)
  | typ_or ?cs1 ?cs2 ?T1 ?T2 =>
    match z with
    | ctx_constructor_row ?c _ =>
      match goal with
      | Hin : CSet.In c cs1 |- _ =>
        choose_contravariant_inv_join_bool z sd T1
      | Hin : CSet.In c cs2 |- _ =>
        choose_contravariant_inv_join_bool z sd T2
      end
    end
  | typ_proj _ _ ?T1 =>
    choose_contravariant_inv_join_bool z sd T1
  | typ_variant _ => constr:(sd)
  | typ_constructor _ _ => constr:(sd)
  | typ_ref _ => constr:(sd)
  | typ_arrow _ _ => constr:(sd)
  | typ_prod _ _ => constr:(sd)
  | typ_bot (con_output_kind ?z) => constr:(false)
  | typ_fvar ?X =>
      match goal with
      | Hb : binds X (Rng _ ?Tu _) _,
        Hi : contravariant_inv _ ?s _ _ _ _ ?Tu
        |- _ => constr:(s)
      end
  | _ =>
    match goal with
    | H1 : contravariant_inv _ ?s1 _ _ _ _ T,
      H2 : contravariant_inv _ ?s2 _ _ _ _ T
      |- _ => constr:(orb s1 s2)
    | H : contravariant_inv _ ?s _ _ _ _ T |- _ => constr:(s)
    | Hte : type_equal _ _ _ ?Tb (typ_top _) _ |- _ =>
      constr:(false)
    end
  end.

Ltac construct_contravariant_inv_bot :=
  try match goal with
  | |- contravariant_inv _ _ _ _ _ (typ_top _) _ =>
    apply contravariant_inv_bot;
    treflexivity
  | |- contravariant_inv _ (?s && false) _ _ _
         (typ_join _ (typ_top _)) _ =>
    try replace (andb s false) with false by ring;
    apply contravariant_inv_bot;
    rewrite type_equal_join_annihilation_r
      by auto with wellformed;
    treflexivity
  | |- contravariant_inv _ _ _ _ _ ?Tt _ =>
    match goal with
    | H : type_equal _ _ _ Tt (typ_top _) _ |- _ =>
      apply contravariant_inv_bot;
      apply H
    | H: type_equal _ _ _ Tt (typ_meet ?Ttl ?Ttr) _,
      Hl : type_equal _ _ _ ?Ttl (typ_top _) _,
      Hr : type_equal _ _ _ ?Ttr (typ_top _) _ |- _ =>
      apply contravariant_inv_bot;
      rewrite H;
      rewrite Hl;
      rewrite Hr;
      rewrite type_equal_meet_identity by auto with kinding;
      treflexivity
    end
  end.

Ltac construct_contravariant_inv :=
  construct_contravariant_inv_bot;
  repeat match goal with
  | |- contravariant_inv ?z _ _ _ _ ?Tt (typ_or ?csl ?csr ?Tl ?Tr) =>
    match goal with
    | H : contravariant_inv _ _ _ _ _ Tt ?Ts |- _ =>
      match Tl with
      | context[Ts] =>
        match Tr with
        | context[Ts] =>
          match z with
          | ctx_constructor_row ?c ?cs =>
            destruct (CSet.In_dec c csl);
            [> apply contravariant_inv_or_l
            | apply contravariant_inv_or_r]
          end
        | _ => apply contravariant_inv_or_l
        end
      | _ =>
        match Tr with
        | context[Ts] => apply contravariant_inv_or_r
        end
      end
    | _ =>
      match z with
      | ctx_constructor_row ?c ?cs =>
        destruct (CSet.In_dec c csl);
        [> apply contravariant_inv_or_l | apply contravariant_inv_or_r]
      end     
    end
  | |- contravariant_inv ?z ?s _ _ _ ?Tt (typ_join ?Ts1 ?Ts2) =>
    let s1' := choose_contravariant_inv_join_bool z s Ts1 in
    let s2' := choose_contravariant_inv_join_bool z s Ts2 in
    let T1' := choose_contravariant_inv_join_type z Tt Ts1 in
    let T2' := choose_contravariant_inv_join_type z Tt Ts2 in
    apply contravariant_inv_join
      with (s1 := s1') (s2 := s2') (T2 := T1') (T3 := T2')
  | |- contravariant_inv _ _ _ _ _ _ (typ_top _) =>
    apply contravariant_inv_top
  | |- contravariant_inv _ _ _ _ _ _ (typ_meet _ _) =>
    apply contravariant_inv_meet
  | |- contravariant_inv _ _ _ _ _ _ (typ_proj _ _ _) =>
    apply contravariant_inv_proj
  | |- contravariant_inv _ _ _ _ _ _ (typ_constructor _ _) =>
    apply contravariant_inv_constructor
  | |- contravariant_inv ctx_arrow_left _ _ _ _ _ (typ_arrow _ _) =>
    apply contravariant_inv_arrow_left
  | |- contravariant_inv ctx_arrow_right_row _ _ _ _ _ (typ_arrow _ _) =>
    apply contravariant_inv_arrow_right
  | |- contravariant_inv ctx_prod_left_row _ _ _ _ _ (typ_prod _ _) =>
    apply contravariant_inv_prod_left
  | |- contravariant_inv ctx_prod_right_row _ _ _ _ _ (typ_prod _ _) =>
    apply contravariant_inv_prod_right
  | |- contravariant_inv _ _ _ _ _ _ (typ_ref _) =>
    apply contravariant_inv_ref
  | Hb : binds ?X (Rng ?Tl ?Tu _) _
    |- contravariant_inv _ _ _ _ _ _ (typ_fvar ?X) =>
    apply contravariant_inv_var with (T2 := Tl) (T3 := Tu)
  end;
  try assumption;
  construct_contravariant_inv_bot.

Lemma contravariant_inv_sub : forall z s1 s2 v E1 E2 K1 T1 T2 T3,
    contravariant_inv z s1 v E1 E2 T1 T2 ->
    subtype v (E1 & E2) empty T1 T3 K1 ->
    leb s2 s1 ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    K1 = con_input_kind z ->
    contravariant_inv z s2 v E1 E2 T3 T2.
Proof.
  introv Hi Hs Hb He1 He2 Heq.
  generalize dependent T3.
  generalize dependent s2.
  subst.
  induction Hi; introv Hb Hs; subst; eauto.
  - apply contravariant_inv_join
      with (s1 := andb s0 s1) (s2 := andb s0 s2)
           (T2 := typ_join T0 T2) (T3 := typ_join T0 T3); auto.
    + eauto using subtype_upper_bound_r,
        type_environment_extend, leb_lower_bound_r
          with kinding wellformed.
    + eauto using subtype_upper_bound_r,
        type_environment_extend, leb_lower_bound_r
          with kinding wellformed.
    + rewrite subtype_dual in Hs by auto using valid_tenv_extend.
      rewrite Hs at 1.
      subst_equal T1.
      rewrite type_equal_join_distribution by auto with kinding.
      treflexivity.
    + unfold leb in Hb.
      rewrite Hb at 1.
      rewrite andb_orb_distribution.
      reflexivity.
  - apply contravariant_inv_arrow_left;
      eauto using subtype_transitive, valid_tenv_extend.
  - apply contravariant_inv_arrow_right;
      eauto using subtype_transitive, valid_tenv_extend.
  - apply contravariant_inv_ref;
      eauto using subtype_transitive, valid_tenv_extend.
  - apply contravariant_inv_prod_left;
      eauto using subtype_transitive, valid_tenv_extend.
  - apply contravariant_inv_prod_right;
      eauto using subtype_transitive, valid_tenv_extend.
  - apply contravariant_inv_constructor;
      eauto using subtype_transitive, valid_tenv_extend.
  - rewrite leb_false with (b := s2) by assumption.
    eauto using subtype_equal_top, valid_tenv_extend.
Qed.

Instance contravariant_inv_eq_morph_impl
  (z : contravariant_context) (s : bool) (v : version)
  (E1 : tenv) (E2 : tenv)
  `{ He1 : valid_tenv v E1 }
  `{ He2 : valid_tenv_extension v E1 E2 }
  : Morphisms.Proper
      (type_equal' v (E1 & E2) empty (con_input_kind z) ==>
       eq ==> Basics.impl)
      (contravariant_inv z s v E1 E2) | 3
  := { }.
  unfold Morphisms.respectful.
  intros T1 T1' Hte T2' T2 Heq Hi.
  rewrite <- Heq.
  apply contravariant_inv_sub
    with (s1 := s) (K1 := con_input_kind z) (T1 := T1);
    auto using leb_refl.
  rewrite Hte.
  sreflexivity.
Qed.

Instance contravariant_inv_eq_morph_flip_impl
  (z : contravariant_context) (s : bool) (v : version)
  (E1 : tenv) (E2 : tenv)
  `{ He1 : valid_tenv v E1 }
  `{ He2 : valid_tenv_extension v E1 E2 }
  : Morphisms.Proper
      (type_equal' v (E1 & E2) empty (con_input_kind z) ==>
       eq ==> Basics.flip Basics.impl)
      (contravariant_inv z s v E1 E2) | 3
  := { }.
  unfold Morphisms.respectful.
  intros T1 T1' Hte T2' T2 Heq Hi.
  rewrite Heq.
  apply contravariant_inv_sub
    with (s1 := s) (K1 := con_input_kind z) (T1 := T1');
    auto using leb_refl.
  rewrite Hte.
  sreflexivity.
Qed.

Instance contravariant_inv_sub_morph_impl
  (z : contravariant_context) (s : bool) (v : version)
  (E1 : tenv) (E2 : tenv)
  `{ He1 : valid_tenv v E1 }
  `{ He2 : valid_tenv_extension v E1 E2 }
  : Morphisms.Proper
      (subtype' v (E1 & E2) empty (con_input_kind z) ==>
       eq ==> Basics.impl)
      (contravariant_inv z s v E1 E2) | 3
  := { }.
  unfold Morphisms.respectful.
  intros T1 T1' Hte T2' T2 Heq Hi.
  rewrite <- Heq.
  apply contravariant_inv_sub
    with (s1 := s) (K1 := con_input_kind z) (T1 := T1);
    auto using leb_refl.
Qed.

Lemma contravariant_inv_lower_bound : forall z s1 s2 v E1 E2 T1 T2 T3,
    contravariant_inv z s1 v E1 E2 T1 T3 ->
    contravariant_inv z s2 v E1 E2 T2 T3 ->
    kinding (E1 & E2) empty T1 (con_input_kind z) ->
    kinding (E1 & E2) empty T2 (con_input_kind z) ->
    kinding E1 E2 T3 (con_output_kind z) ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    contravariant_inv z (orb s1 s2) v E1 E2 (typ_meet T1 T2) T3.
Proof.
  introv Hi1 Hi2 Hk1 Hk2 Hk3 He1 He2.
  generalize dependent T2.
  generalize dependent s2.
  induction Hi1; introv Hi2 Hk2; invert_contravariant_inv; subst;
    auto using subtype_greatest_lower_bound, subtype_meet_top_r,
      valid_tenv_extend with kinding.
  - apply contravariant_inv_join
      with (s1 := s1) (s2 := s2) (T2 := T2) (T3 := T3);
      try ring_simplify; auto.
    subst_equal T0.
    rewrite type_equal_meet_identity by auto with kinding.
    assumption.
  - apply contravariant_inv_join
      with (s1 := orb s1 s4) (s2 := orb s2 s5)
        (T2 := typ_meet T2 T6) (T3 := typ_meet T3 T7);
          try ring_simplify; auto with kinding.
    subst_equal T1.
    subst_equal T0.
    rewrite <- type_equal_meet_associative by auto with kinding.
    rewrite type_equal_meet_associative
      with (T1 := T3) by auto with kinding.
    rewrite type_equal_meet_commutative
      with (T1 := T3) by auto with kinding.
    rewrite <- type_equal_meet_associative by auto with kinding.
    rewrite type_equal_meet_associative by auto with kinding.
    treflexivity.
  - eauto using kinding_from_valid_tenv_lower with wellformed.
  - eauto using kinding_from_valid_tenv_lower with wellformed.
  - inversion Hk3; subst.
    assert (not (CSet.In c0 cs1)) by csetdec.
    contradiction.
  - inversion Hk3; subst.
    assert (not (CSet.In c0 cs1)) by csetdec.
    contradiction.
  - subst_equal T1.
    rewrite type_equal_meet_commutative by auto with kinding.
    rewrite type_equal_meet_identity by auto with kinding.
    assumption.
Qed.

Ltac invert_con_output_kind_equality Heq :=
  match type of Heq with
  | knd_row ?cs1 = con_output_kind (ctx_constructor_row ?c ?cs2) =>
    inversion Heq; subst
  | knd_row ?cs1 = con_output_kind ?z =>
    destruct z; try discriminate;
    inversion HeqK; subst
  | _ => idtac
  end.

Ltac invert_kindings_con :=
  repeat
    match goal with
    | Hz : valid_contravariant_context (ctx_constructor_row _ _) |- _ =>
      inversion Hz; subst; clear Hz
    | H : kinding _ _ (typ_or _ _ _ _) _ |- _ =>
      inversion H; subst; clear H
    | H : kinding _ _ (typ_proj _ _ _) _ |- _ =>
      inversion H; subst; clear H
    end.

Ltac solve_contravariant_inv_side_conditions :=
  try match goal with
  | |- type_equal _ _ _ ?T ?T _ =>
    treflexivity
  | |- subtype _ _ _ ?T1 (typ_join ?T1 ?T2) _ =>
    auto using subtype_upper_bound_l with kinding wellformed
  | |- subtype _ _ _ ?T2 (typ_join ?T1 ?T2) _ =>
    auto using subtype_upper_bound_r with kinding wellformed
  | Hs1 : subtype _ _ _ ?T1 ?T3 _,
    Hs2 : subtype _ _ _ ?T2 ?T3 _
    |- subtype _ _ _ (typ_join ?T1 ?T2) ?T3 _ =>
    apply subtype_least_upper_bound;
    auto using valid_tenv_extend
  | |- @eq bool ?s1 ?s2 =>
    try ring;
    repeat match goal with
    | s : bool |- _ => destruct s
    end; solve [auto]
  | Hs : subtype _ _ _ (typ_join ?T1 ?T2) ?T3 _
    |- subtype _ _ _ ?T1 ?T3 _ =>
    rewrite <- Hs;
    apply subtype_upper_bound_l;
    auto with kinding wellformed
  | Hs : subtype _ _ _ (typ_join ?T1 ?T2) ?T3 _
    |- subtype _ _ _ ?T2 ?T3 _ =>
    rewrite <- Hs;
    apply subtype_upper_bound_r;
    auto with kinding wellformed
  | Hs : subtype _ _ _ (typ_meet ?T2 ?T3) ?T1 _ |-
    type_equal _ _ _ ?T1
      (typ_meet (typ_join ?T1 ?T2) (typ_join ?T1 ?T3)) _ =>
    rewrite <- type_equal_join_distribution
      by auto with kinding;
    rewrite subtype_dual in Hs;
    auto using valid_tenv_extend
  | Hte1 : type_equal _ _ _ ?T1 (typ_meet ?T2 ?T3) _,
    Hte2 : type_equal _ _ _ ?T3 (typ_top _) _,
    Hs : subtype _ _ _ ?T4 ?T2 _
    |- subtype _ _ _ (typ_meet ?T4 _) ?T1 _ =>
    rewrite Hte1;
    rewrite Hte2;
    rewrite type_equal_meet_identity
      by auto with kinding;
    rewrite <- Hs;
    rewrite subtype_lower_bound_l
      by auto with kinding wellformed;
    sreflexivity
  | Hte1 : type_equal _ _ _ ?T1 (typ_meet ?T2 ?T3) _,
    Hte2 : type_equal _ _ _ ?T2 (typ_top ?K) _,
    Hs : subtype _ _ _ ?T4 ?T3 _
    |- subtype _ _ _ (typ_meet _ ?T4) ?T1 _ =>
    rewrite Hte1;
    rewrite Hte2;
    rewrite type_equal_meet_commutative
      with (T1 := typ_top K) by auto with kinding;
    rewrite type_equal_meet_identity
      by auto with kinding;
    rewrite <- Hs;
    rewrite subtype_lower_bound_r
      by auto with kinding wellformed;
    sreflexivity
  | Hte : type_equal _ _ _ ?T1 (typ_meet ?T2 ?T3) _,
    Hs1 : subtype _ _ _ ?T4 ?T2 _,
    Hs2 : subtype _ _ _ ?T5 ?T3 _
    |- subtype _ _ _ (typ_meet ?T4 ?T5) ?T1 _ =>
    rewrite Hte;
    apply subtype_greatest_lower_bound;
      try rewrite <- Hs1; try rewrite <- Hs2;
      auto using valid_tenv_extend,
        subtype_lower_bound_l, subtype_lower_bound_r
          with kinding wellformed
  | Hte : type_equal _ _ _ ?T1 ?T2 _,
    Hs : subtype _ _ _ ?T1 ?T3 _
    |- subtype _ _ _ ?T2 ?T3 _ =>
    rewrite <- Hs;
    rewrite Hte;
    sreflexivity
  | Hte : type_equal _ _ _ ?T1 ?T2 _,
    Hs : subtype _ _ _ ?T2 ?T3 _
    |- subtype _ _ _ ?T1 ?T3 _ =>
    rewrite <- Hs;
    rewrite Hte;
    sreflexivity
  | Hi : contravariant_inv ?z ?s _ _ _ ?Tsl ?Tt |-
    contravariant_inv _ _ _ _ _ (typ_join ?Tsl _) ?Tt =>
    apply contravariant_inv_sub
      with (s1 := s) (K1 := con_input_kind z) (T1 := Tsl);
      auto using subtype_upper_bound_l, leb_lower_bound_l
        with kinding wellformed
  | Hi : contravariant_inv ?z ?s _ _ _ ?Tsr ?Tt |-
    contravariant_inv _ _ _ _ _ (typ_join _ ?Tsr) ?Tt =>
    apply contravariant_inv_sub
      with (s1 := s) (K1 := con_input_kind z) (T1 := Tsr);
      auto using subtype_upper_bound_r, leb_lower_bound_r
        with kinding wellformed
  | Hi : contravariant_inv _ ?s1 _ _ _ ?Tsl ?Tt,
    Hte1 : type_equal _ _ _ ?Ts (typ_meet ?Tsl ?Tsr) _,
    Hte2 : type_equal _ _ _ ?Tsr (typ_top _) _ |-
    contravariant_inv _ ?s2  _ _ _ ?Ts ?Tt =>
    rewrite Hte1;
    rewrite Hte2;
    rewrite type_equal_meet_identity by auto with kinding;
    replace s2 with s1 by ring;
    assumption
  | Hi : contravariant_inv _ ?s1 _ _ _ ?Tsr ?Tt,
    Hte1 : type_equal _ _ _ ?Ts (typ_meet ?Tsl ?Tsr) _,
    Hte2 : type_equal _ _ _ ?Tsl (typ_top _) _ |-
    contravariant_inv _ ?s2  _ _ _ ?Ts ?Tt =>
    rewrite Hte1;
    rewrite Hte2;
    rewrite type_equal_meet_commutative by auto with kinding;
    rewrite type_equal_meet_identity by auto with kinding;
    replace s2 with s1 by ring;
    assumption
  | Hil : contravariant_inv _ ?s1 _ _ _ ?Tsl ?Tt,
    Hir : contravariant_inv _ ?s2 _ _ _ ?Tsr ?Tt,
    Hte : type_equal _ _ _ ?Ts (typ_meet ?Tsl ?Tsr) _ |-
    contravariant_inv _ (orb ?s1 ?s2) _ _ _ ?Ts ?Tt =>
    rewrite Hte;
    apply contravariant_inv_lower_bound;
    auto with kinding wellformed
  | Hil : contravariant_inv _ ?s1 _ _ _ ?Tsl ?Tt,
    Hir : contravariant_inv _ ?s2 _ _ _ ?Tsr ?Tt
    |- contravariant_inv _ (orb ?s1 ?s2) _ _ _
                     (typ_meet ?Tsl ?Tsr) ?Tt =>
    apply contravariant_inv_lower_bound;
    auto with kinding wellformed
  | H1 : CSet.In ?c ?cs1,
    H2 : ~ CSet.In ?c ?cs1 |- _ =>
    contradiction
  | Hk : kinding _ _ (typ_or ?cs1 ?cs2 _ _) _,
    H1 : CSet.In ?c ?cs1,
    H2 : CSet.In ?c ?cs2 |- _ =>
    inversion Hk; subst;
    assert (~ CSet.In c cs1) by csetdec;
    contradiction
  | Hk : kinding _ _ (typ_or ?cs _ (typ_or _ _ _ _) _) _
    |- CSet.In _ ?cs =>
    inversion Hk; subst;
    match goal with
    | Hk' : kinding _ _ (typ_or _ _ _ _) (knd_row cs) |- _ =>
      inversion Hk'; subst;
      csetdec
    end
  | |- CSet.In _ _ =>
    invert_kindings_con;
    csetdec
  end.

Lemma type_equal_core_contravariant_inv_l :
  forall z s v E1 E2 T1 T2 T3,
    contravariant_inv z s v E1 E2 T1 T2 ->
    type_equal_core v T2 T3 (con_output_kind z) ->
    valid_contravariant_context z ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    kinding (E1 & E2) empty T1 (con_input_kind z) ->
    kinding E1 E2 T2 (con_output_kind z) ->
    kinding E1 E2 T3 (con_output_kind z) ->
    contravariant_inv z s v E1 E2 T1 T3.
Proof.
  introv Hi Hte Hz He1 He2 Hk1 Hk2 Hk3.
  remember (con_output_kind z) as K.
  destruct Hte; invert_contravariant_inv;
    invert_con_output_kind_equality HeqK; subst;
    construct_contravariant_inv; solve_contravariant_inv_side_conditions.
  - invert_kindings_con.
    assert (not (CSet.In c0 cs2)) by csetdec.
    contradiction.
  - invert_kindings_con.
    assert (not (CSet.In c0 cs1)) by csetdec.
    contradiction.
  - rewrite <- type_equal_join_distribution by auto with kinding.
    subst_equal T1 at 2.
    rewrite <- type_equal_join_idempotent
      by auto with kinding wellformed.
    subst_equal T1.
    treflexivity.
  - subst_equal T1.
    rewrite type_equal_meet_commutative by auto with kinding.
    treflexivity.
  - rewrite <- type_equal_meet_associative at 1
      by auto with kinding.
    rewrite <- type_equal_meet_idempotent
      by auto with kinding wellformed.
    subst_equal T1.
    treflexivity.
  - subst_equal T1.
    subst_equal T5.
    rewrite type_equal_meet_associative by auto with kinding.
    treflexivity.
Qed.

Lemma type_equal_core_contravariant_inv_r :
  forall z s v E1 E2 T1 T2 T3,
    contravariant_inv z s v E1 E2 T1 T2 ->
    type_equal_core v T3 T2 (con_output_kind z) ->
    valid_contravariant_context z ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    kinding (E1 & E2) empty T1 (con_input_kind z) ->
    kinding E1 E2 T2 (con_output_kind z) ->
    kinding E1 E2 T3 (con_output_kind z) ->
    contravariant_inv z s v E1 E2 T1 T3.
Proof.
  introv Hi Hte Hz He1 He2 Hk1 Hk2 Hk3.
  remember (con_output_kind z) as K.
  destruct Hte; invert_contravariant_inv;
    invert_con_output_kind_equality HeqK; subst;
    construct_contravariant_inv; solve_contravariant_inv_side_conditions.
  - apply contravariant_inv_join
      with (s1 := s) (s2 := false)
           (T2 := T1) (T3 := typ_top (con_input_kind z));
      construct_contravariant_inv;
      solve_contravariant_inv_side_conditions.
    rewrite type_equal_meet_identity
      by auto with kinding wellformed.
    treflexivity.
  - subst_equal T1.
    rewrite type_equal_meet_commutative by auto with kinding.
    treflexivity.
  - subst_equal T4.
    rewrite type_equal_meet_commutative by auto with kinding.
    rewrite type_equal_meet_identity by auto with kinding.
    subst_equal T1.
    subst_equal T4.
    treflexivity.
  - subst_equal T1.
    subst_equal T4.
    rewrite type_equal_meet_associative by auto with kinding.
    treflexivity.
  - rewrite type_equal_meet_identity
      by auto with kinding wellformed.
    treflexivity.
  - apply contravariant_inv_join
      with (s1 := s) (s2 := false)
           (T2 := T1) (T3 := typ_top (con_input_kind z));
      construct_contravariant_inv;
      solve_contravariant_inv_side_conditions.
    rewrite type_equal_meet_identity
      by auto with kinding wellformed.
    treflexivity.
  - apply contravariant_inv_bot.
    subst_equal T1.
    rewrite type_equal_join_annihilation_l
      by auto with kinding wellformed.
    treflexivity.
  - rewrite type_equal_meet_distribution
      by auto with kinding.
    subst_equal <- T1.
    subst_equal T1 at 3.
    rewrite type_equal_join_annihilation_r
      by auto with kinding wellformed.
    subst_equal T1.
    treflexivity.
  - rewrite <- type_equal_meet_associative
      by auto with kinding.
    rewrite type_equal_meet_distribution
      by auto with kinding.
    subst_equal <- T1.
    rewrite type_equal_meet_distribution
      by auto with kinding.
    rewrite type_equal_meet_commutative
      with (T1 := T6) (T2 := T5)
      by auto with kinding.
    rewrite type_equal_meet_associative
      by auto with kinding.
    subst_equal <- T1.
    rewrite H2 at 2.
    rewrite type_equal_meet_associative
      by auto with kinding.
    rewrite <- type_equal_meet_idempotent
      by auto with kinding wellformed.
    subst_equal <- T1.
    rewrite type_equal_join_absorption
      by auto with kinding.
    treflexivity.
Qed.

Lemma type_equal_contravariant_inv' :
  forall z s v E1 E2 E3 T1 T2 T3,
    type_equal v E1 (E2 & E3) T2 T3 (con_output_kind z) ->
    kinding (E1 & E2 & E3) empty T1 (con_input_kind z) ->
    kinding (E1 & E2) E3 T2 (con_output_kind z) ->
    kinding (E1 & E2) E3 T3 (con_output_kind z) ->
    valid_contravariant_context z ->
    valid_tenv v (E1 & E2) ->
    valid_tenv_extension v (E1 & E2) E3 ->
    (forall z s X T4 T5 T6,
        binds X (Rng T5 T6 (con_output_kind z)) E1 ->
        valid_contravariant_context z ->
        kinding (E1 & E2 & E3) empty T4 (con_input_kind z) ->
        contravariant_inv z s v (E1 & E2) E3 T4 T5 ->
        contravariant_inv z s v (E1 & E2) E3 T4 T6) ->
    contravariant_inv z s v (E1 & E2) E3 T1 T2 <->
    contravariant_inv z s v (E1 & E2) E3 T1 T3.
Proof.
  introv Hte Hk1 Hk2 Hk3 Hz He1 He2 Hb.
  pose (From := T2).
  pose (To := T3).
  remember (con_output_kind z) as K.
  remember (E2 & E3) as E23.
  generalize dependent z.
  generalize dependent s.
  generalize dependent T1.
  induction Hte; introv Heq Hk1 Hz; subst;
    autorewrite with rew_env_concat in *;
    split; introv Hi; invert_contravariant_inv; subst;
      construct_contravariant_inv;
      solve_contravariant_inv_side_conditions.
  - apply binds_tenv_weakening_l; auto with wellformed.
  - apply binds_tenv_weakening_l; auto with wellformed.
  - eauto.
  - apply binds_tenv_weakening_l; auto with wellformed.
  - rewrite <- IHHte1 by auto with kinding; auto.
  - rewrite <- IHHte2 by auto with kinding; auto.
  - rewrite IHHte1 by auto with kinding; auto.
  - rewrite IHHte2 by auto with kinding; auto.
  - rewrite <- IHHte
      by (invert_kindings_con; auto with kinding); auto.
  - rewrite IHHte
      by (invert_kindings_con; auto with kinding); auto.
  - rewrite <- IHHte1 by auto with kinding; auto.
  - rewrite <- IHHte2 by auto with kinding; auto.
  - rewrite IHHte1 by auto with kinding; auto.
  - rewrite IHHte2 by auto with kinding; auto.
  - apply contravariant_inv_join
      with (s1 := s2) (s2 := s3) (T2 := T4) (T3 := T5);
      solve_contravariant_inv_side_conditions; auto.
    + rewrite <- IHHte1 by auto with kinding; auto.
    + rewrite <- IHHte2 by auto with kinding; auto.
  - apply contravariant_inv_join
      with (s1 := s2) (s2 := s3) (T2 := T4) (T3 := T5);
      solve_contravariant_inv_side_conditions; auto.
    + rewrite IHHte1 by auto with kinding; auto.
    + rewrite IHHte2 by auto with kinding; auto.
  - apply type_equal_core_contravariant_inv_l with T1; auto.
  - apply type_equal_core_contravariant_inv_r with T1'; auto.
  - rewrite IHHte by auto; auto.
  - rewrite <- IHHte by auto; auto.
  - apply type_equal_extend in Hte1;
      auto using type_environment_extend_inv with wellformed.
    rewrite <- IHHte2 by auto with kinding.
    rewrite <- IHHte1 by auto with kinding; auto.
  - apply type_equal_extend in Hte1;
      auto using type_environment_extend_inv with wellformed.
    rewrite IHHte1 by auto with kinding.
    rewrite IHHte2 by auto with kinding; auto.
Qed.

Lemma subtype_contravariant_inv' : forall z s v E1 E2 E3 T1 T2 T3,
    subtype v E1 (E2 & E3) T2 T3 (con_output_kind z) ->
    kinding (E1 & E2 & E3) empty T1 (con_input_kind z) ->
    kinding (E1 & E2) E3 T2 (con_output_kind z) ->
    kinding (E1 & E2) E3 T3 (con_output_kind z) ->
    valid_contravariant_context z ->
    valid_tenv v (E1 & E2)->
    valid_tenv_extension v (E1 & E2) E3 ->
    (forall z s X T4 T5 T6,
        binds X (Rng T5 T6 (con_output_kind z)) E1 ->
        valid_contravariant_context z ->
        kinding (E1 & E2 & E3) empty T4 (con_input_kind z) ->
        contravariant_inv z s v (E1 & E2) E3 T4 T5 ->
        contravariant_inv z s v (E1 & E2) E3 T4 T6) ->
    contravariant_inv z s v (E1 & E2) E3 T1 T2 ->
    contravariant_inv z s v (E1 & E2) E3 T1 T3.
Proof.
  introv Hs Hk1 Hk2 Hk3 Hz He1 He2 Hb Hi.
  unfold subtype in Hs.
  assert (contravariant_inv z s v (E1 & E2) E3
            T1 (typ_meet T2 T3)) as Hi2
    by (rewrite type_equal_contravariant_inv' with (T3 := T2); auto).
  inversion Hi2; subst; auto.
Qed.

Lemma valid_tenv_rec_contravariant_inv : forall v E1 E2 E3,
    valid_tenv_rec v empty E1 (E2 & E3) ->
    valid_tenv v (E1 & E2) ->
    valid_tenv_extension v (E1 & E2) E3 ->
    (forall z s X T1 T2 T3,
        binds X (Rng T2 T3 (con_output_kind z)) E1 ->
        valid_contravariant_context z ->
        kinding (E1 & E2 & E3) empty T1 (con_input_kind z) ->
        contravariant_inv z s v (E1 & E2) E3 T1 T2 ->
        contravariant_inv z s v (E1 & E2) E3 T1 T3).
Proof.
  introv He1 He2 He3.
  remember empty as E0.
  remember (E2 & E3) as E23.
  generalize dependent E2.
  induction He1; introv Heq He2 He3 Hb Hz Hk Hi; subst.
  - exfalso; eauto using binds_empty_inv.
  - destruct (binds_push_inv Hb) as [[? ?]|[Hx Hbnd2]]; subst;
      autorewrite with rew_env_concat in *.
    + assert (valid_range v E2
                (X ~ Rng T2 T3 (con_output_kind z) & E4 & E3)
                (Rng T2 T3 (con_output_kind z))) as Hr by auto.
      inversion Hr; subst.
      rewrite <- concat_assoc with (E := E2).
      apply subtype_contravariant_inv' with T2;
        try solve [autorewrite with rew_env_concat; eauto];
        try solve
            [apply kinding_extend; auto;
             apply type_environment_extend_inv;
               autorewrite with rew_env_concat;
               auto with wellformed].
      apply IHHe1; autorewrite with rew_env_concat; auto.
    + rewrite <- concat_assoc with (E := E2).
      eapply IHHe1; autorewrite with rew_env_concat; eauto.
Qed.

Lemma type_equal_contravariant_inv :
  forall z s v E1 E2 T1 T2 T3,
    type_equal v E1 E2 T2 T3 (con_output_kind z) ->
    kinding (E1 & E2) empty T1 (con_input_kind z) ->
    valid_contravariant_context z ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    contravariant_inv z s v E1 E2 T1 T2 <->
    contravariant_inv z s v E1 E2 T1 T3.
Proof.
  introv Hte Hk Hz He1 He2.
  replace E1 with (E1 & empty) by apply concat_empty_r.
  apply type_equal_contravariant_inv';
    autorewrite with rew_env_concat; auto with kinding.
  introv Hb' Hz' Hk' Hi'.
  rewrite <- concat_empty_r with (E := E1).
  eapply valid_tenv_rec_contravariant_inv;
    autorewrite with rew_env_concat; eauto.
  rewrite <- concat_empty_r with (E := E2).
  apply valid_tenv_rec_weakening_rec_r;
    autorewrite with rew_env_concat;
    try fold (type_environment E1);
    auto with wellformed.
Qed.

Lemma subtype_contravariant_inv :
  forall z s v E1 E2 T1 T2 T3,
    subtype v E1 E2 T2 T3 (con_output_kind z) ->
    kinding (E1 & E2) empty T1 (con_input_kind z) ->
    valid_contravariant_context z ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    contravariant_inv z s v E1 E2 T1 T2 ->
    contravariant_inv z s v E1 E2 T1 T3.
Proof.
  introv Hs Hk Hz He1 He2 Hi.
  unfold subtype in Hs.
  assert (contravariant_inv z s v E1 E2
            T1 (typ_meet T2 T3)) as Hi2
    by (rewrite type_equal_contravariant_inv with (T3 := T2); auto).
  inversion Hi2; subst; auto.
Qed.

Lemma invert_subtype_arrow_left : forall v E1 E2 T1 T2 T3 T4,
    subtype v E1 E2 (typ_arrow T1 T2) (typ_arrow T3 T4) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    subtype v (E1 & E2) empty T3 T1 knd_type.
Proof.
  introv Hs He1 He2.
  assert (contravariant_inv ctx_arrow_left true v E1 E2
                      T1 (typ_arrow T1 T2))
    by auto using subtype_refl with kinding wellformed.
  assert (contravariant_inv ctx_arrow_left true v E1 E2
                      T1 (typ_arrow T3 T4))
    as Hi by eauto using subtype_contravariant_inv with kinding.
  inversion Hi; subst; auto.
Qed.

Lemma invert_subtype_arrow_right_row_contravariant :
  forall E1 E2 T1 T2 T3 T4,
    subtype version_row_subtyping E1 E2
      (typ_arrow T1 T2) (typ_arrow T3 T4) knd_type ->
    valid_tenv version_row_subtyping E1 ->
    valid_tenv_extension version_row_subtyping E1 E2 ->
    subtype version_row_subtyping (E1 & E2) empty T4 T2 knd_type.
Proof.
  introv Hs He1 He2.
  assert (contravariant_inv ctx_arrow_right_row true
            version_row_subtyping E1 E2 T2 (typ_arrow T1 T2))
    by auto using subtype_refl with kinding wellformed.
  assert (contravariant_inv ctx_arrow_right_row true
            version_row_subtyping E1 E2 T2 (typ_arrow T3 T4))
    as Hi by eauto using subtype_contravariant_inv with kinding.
  inversion Hi; subst; auto.
Qed.

Lemma invert_subtype_ref_contravariant : forall v E1 E2 T1 T2,
    subtype v E1 E2 (typ_ref T1) (typ_ref T2) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    subtype v (E1 & E2) empty T2 T1 knd_type.
Proof.
  introv Hs He1 He2.
  assert (contravariant_inv ctx_ref_contra true v E1 E2 T1 (typ_ref T1))
    by auto using subtype_refl with kinding wellformed.
  assert (contravariant_inv ctx_ref_contra true v E1 E2 T1 (typ_ref T2))
    as Hi by eauto using subtype_contravariant_inv with kinding.
  inversion Hi; subst; auto.
Qed.

Lemma invert_subtype_prod_left_row_contravariant :
  forall E1 E2 T1 T2 T3 T4,
    subtype version_row_subtyping E1 E2
      (typ_prod T1 T2) (typ_prod T3 T4) knd_type ->
    valid_tenv version_row_subtyping E1 ->
    valid_tenv_extension version_row_subtyping E1 E2 ->
    subtype version_row_subtyping (E1 & E2) empty T3 T1 knd_type.
Proof.
  introv Hs He1 He2.
  assert (contravariant_inv ctx_prod_left_row true
            version_row_subtyping E1 E2 T1 (typ_prod T1 T2))
    by auto using subtype_refl with kinding wellformed.
  assert (contravariant_inv ctx_prod_left_row true
            version_row_subtyping E1 E2 T1 (typ_prod T3 T4))
    as Hi by eauto using subtype_contravariant_inv with kinding.
  inversion Hi; subst; auto.
Qed.

Lemma invert_subtype_prod_right_row_contravariant :
  forall E1 E2 T1 T2 T3 T4,
    subtype version_row_subtyping E1 E2
      (typ_prod T1 T2) (typ_prod T3 T4) knd_type ->
    valid_tenv version_row_subtyping E1 ->
    valid_tenv_extension version_row_subtyping E1 E2 ->
    subtype version_row_subtyping (E1 & E2) empty T4 T2 knd_type.
Proof.
  introv Hs He1 He2.
  assert (contravariant_inv ctx_prod_right_row true
            version_row_subtyping E1 E2 T2 (typ_prod T1 T2))
    by auto using subtype_refl with kinding wellformed.
  assert (contravariant_inv ctx_prod_right_row true
            version_row_subtyping E1 E2 T2 (typ_prod T3 T4))
    as Hi by eauto using subtype_contravariant_inv with kinding.
  inversion Hi; subst; auto.
Qed.

Lemma invert_subtype_constructor_row_contravariant :
  forall c cs E1 E2 T1 T2,
    subtype version_row_subtyping E1 E2
      (typ_constructor c T1) (typ_constructor c T2) (knd_row cs)->
    valid_tenv version_row_subtyping E1 ->
    valid_tenv_extension version_row_subtyping E1 E2 ->
    subtype version_row_subtyping (E1 & E2) empty T2 T1 knd_type.
Proof.
  introv Hs He1 He2.
  assert (contravariant_inv (ctx_constructor_row c cs) true
           version_row_subtyping E1 E2 T1 (typ_constructor c T1))
    by auto using subtype_refl with kinding wellformed.
  assert (kinding E1 E2 (typ_constructor c T1) (knd_row cs)) as Hk
      by auto with kinding.
  inversion Hk; subst.
  assert (contravariant_inv (ctx_constructor_row c (CSet.singleton c))
            true version_row_subtyping E1 E2 T1 (typ_constructor c T2))
    as Hi by eauto using subtype_contravariant_inv with kinding csetdec.
  inversion Hi; subst; auto.
Qed.

(* *************************************************************** *)
(** Invariant subtyping inversions *)

Lemma invert_subtype_arrow_left_row : forall E1 E2 T1 T2 T3 T4,
    subtype version_row_subtyping E1 E2
      (typ_arrow T1 T2) (typ_arrow T3 T4) knd_type ->
    valid_tenv version_row_subtyping E1 ->
    valid_tenv_extension version_row_subtyping E1 E2 ->
    type_equal version_row_subtyping (E1 & E2) empty T1 T3 knd_type.
Proof.
  introv Hs He1 He2.
  apply subtype_antisymmetric;
    eauto using valid_tenv_extend,
      invert_subtype_arrow_left_row_covariant,
      invert_subtype_arrow_left.
Qed.

Lemma invert_subtype_arrow_right_row :
  forall E1 E2 T1 T2 T3 T4,
    subtype version_row_subtyping E1 E2
      (typ_arrow T1 T2) (typ_arrow T3 T4) knd_type ->
    valid_tenv version_row_subtyping E1 ->
    valid_tenv_extension version_row_subtyping E1 E2 ->
    type_equal version_row_subtyping (E1 & E2) empty T2 T4 knd_type.
Proof.
  introv Hs He1 He2.
  apply subtype_antisymmetric;
    eauto using valid_tenv_extend,
      invert_subtype_arrow_right,
      invert_subtype_arrow_right_row_contravariant.
Qed.

Lemma invert_subtype_ref : forall v E1 E2 T1 T2,
    subtype v E1 E2 (typ_ref T1) (typ_ref T2) knd_type ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    type_equal v (E1 & E2) empty T1 T2 knd_type.
Proof.
  introv Hs He1 He2.
  apply subtype_antisymmetric;
    eauto using valid_tenv_extend,
      invert_subtype_ref_covariant,
      invert_subtype_ref_contravariant.
Qed.

Lemma invert_subtype_prod_left_row :
  forall E1 E2 T1 T2 T3 T4,
    subtype version_row_subtyping E1 E2
      (typ_prod T1 T2) (typ_prod T3 T4) knd_type ->
    valid_tenv version_row_subtyping E1 ->
    valid_tenv_extension version_row_subtyping E1 E2 ->
    type_equal version_row_subtyping (E1 & E2) empty T1 T3 knd_type.
Proof.
  introv Hs He1 He2.
  apply subtype_antisymmetric;
    eauto using valid_tenv_extend,
      invert_subtype_prod_left,
      invert_subtype_prod_left_row_contravariant.
Qed.

Lemma invert_subtype_prod_right_row :
  forall E1 E2 T1 T2 T3 T4,
    subtype version_row_subtyping E1 E2
      (typ_prod T1 T2) (typ_prod T3 T4) knd_type ->
    valid_tenv version_row_subtyping E1 ->
    valid_tenv_extension version_row_subtyping E1 E2 ->
    type_equal version_row_subtyping (E1 & E2) empty T2 T4 knd_type.
Proof.
  introv Hs He1 He2.
  apply subtype_antisymmetric;
    eauto using valid_tenv_extend,
      invert_subtype_prod_right,
      invert_subtype_prod_right_row_contravariant.
Qed.

Lemma invert_subtype_constructor_row :
  forall c cs E1 E2 T1 T2,
    subtype version_row_subtyping E1 E2
      (typ_constructor c T1) (typ_constructor c T2) (knd_row cs)->
    valid_tenv version_row_subtyping E1 ->
    valid_tenv_extension version_row_subtyping E1 E2 ->
    type_equal version_row_subtyping (E1 & E2) empty T1 T2 knd_type.
Proof.
  introv Hs He1 He2.
  apply subtype_antisymmetric;
    eauto using valid_tenv_extend,
      invert_subtype_constructor,
      invert_subtype_constructor_row_contravariant.
Qed.
