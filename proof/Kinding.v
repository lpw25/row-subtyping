(************************************************
 *          Row Subtyping - Kinding             *
 *                 Leo White                    *
 ************************************************)

(* Lemmas and automation for kinding proofs *) 

Set Implicit Arguments.
Require Import LibLN Utilities Cofinite Disjoint Definitions
        Opening FreeVars Environments Subst Wellformedness
        Weakening Substitution.

(* *************************************************************** *)
(** Kinding inversions *)

Lemma kinding_constructor_inv : forall E1 E2 c T K,
    kinding E1 E2 (typ_constructor c T) K ->
    kinding (E1 & E2) empty T knd_type.
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_or_inv_l : forall E1 E2 T1 T2 cs1 cs2 cs3,
    kinding E1 E2 (typ_or cs1 cs2 T1 T2) (knd_row cs3) ->
    kinding E1 E2 T1 (knd_row cs1).
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_or_inv_r : forall E1 E2 T1 T2 cs1 cs2 cs3,
    kinding E1 E2 (typ_or cs1 cs2 T1 T2) (knd_row cs3) ->
    kinding E1 E2 T2 (knd_row cs2).
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_proj_inv : forall E1 E2 T cs1 cs2 cs3,
    kinding E1 E2 (typ_proj cs1 cs2 T) (knd_row cs3) ->
    kinding E1 E2 T (knd_row cs1).
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_variant_inv : forall E1 E2 T,
    kinding E1 E2 (typ_variant T) knd_type ->
    kinding (E1 & E2) empty T knd_row_all.
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_arrow_inv_l : forall E1 E2 T1 T2,
    kinding E1 E2 (typ_arrow T1 T2) knd_type ->
    kinding (E1 & E2) empty T1 knd_type.
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_arrow_inv_r : forall E1 E2 T1 T2,
    kinding E1 E2 (typ_arrow T1 T2) knd_type ->
    kinding (E1 & E2) empty T2 knd_type.
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_ref_inv : forall E1 E2 T,
    kinding E1 E2 (typ_ref T) knd_type ->
    kinding (E1 & E2) empty T knd_type.
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_prod_inv_l : forall E1 E2 T1 T2,
    kinding E1 E2 (typ_prod T1 T2) knd_type ->
    kinding (E1 & E2) empty T1 knd_type.
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_prod_inv_r : forall E1 E2 T1 T2,
    kinding E1 E2 (typ_prod T1 T2) knd_type ->
    kinding (E1 & E2) empty T2 knd_type.
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_meet_inv_l : forall E1 E2 T1 T2 K,
    kinding E1 E2 (typ_meet T1 T2) K ->
    kinding E1 E2 T1 K.
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_meet_inv_r : forall E1 E2 T1 T2 K,
    kinding E1 E2 (typ_meet T1 T2) K ->
    kinding E1 E2 T2 K.
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_join_inv_l : forall E1 E2 T1 T2 K,
    kinding E1 E2 (typ_join T1 T2) K ->
    kinding E1 E2 T1 K.
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_join_inv_r : forall E1 E2 T1 T2 K,
    kinding E1 E2 (typ_join T1 T2) K ->
    kinding E1 E2 T2 K.
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

(* *************************************************************** *)
(** Kinding from valid type environments *)

Lemma valid_range_from_valid_tenv_rec : forall X v E1 E2 E3 R,
    valid_tenv_rec v E1 E2 E3 ->
    binds X R E2 ->
    valid_range v (E1 & E2) E3 R.
Proof.
  introv He Hb.
  induction He.
  - apply binds_empty_inv in Hb; contradiction.
  - destruct (binds_push_inv Hb) as [[Hx Hbnd]|[Hx Hbnd]]; subst.
    + rewrite concat_assoc.
      apply valid_range_extend; auto.
      rewrite <- concat_empty_l.
      auto with wellformed.
    + rewrite concat_assoc.
      apply valid_range_extend; auto.
      rewrite <- concat_empty_l.
      auto with wellformed.
Qed.

Lemma valid_range_empty_from_valid_tenv_extension :
  forall X v E1 E2 R,
    valid_tenv_extension v E1 E2 ->
    binds X R E2 ->
    valid_range v (E1 & E2) empty R.
Proof.
  introv He Hb.
  eauto using valid_range_from_valid_tenv_rec.
Qed.

Lemma valid_range_empty_from_valid_tenv : forall X v E R,
    valid_tenv v E ->
    binds X R E ->
    valid_range v E empty R.
Proof.
  introv He Hb.
  rewrite <- concat_empty_l with (E := E).
  eauto using valid_range_empty_from_valid_tenv_extension.
Qed.

Lemma kinding_empty_from_valid_tenv_lower : forall X v E T1 T2 K,
    valid_tenv v E ->
    binds X (Rng T1 T2 K) E ->
    kinding E empty T1 K.
Proof.
  introv He Hb.
  assert (valid_range v E empty (Rng T1 T2 K)) as Hr
    by eauto using valid_range_empty_from_valid_tenv.
  inversion Hr; subst.
  assumption.
Qed.

Lemma kinding_empty_from_valid_tenv_upper : forall X v E T1 T2 K,
    valid_tenv v E ->
    binds X (Rng T1 T2 K) E ->
    kinding E empty T2 K.
Proof.
  introv He Hb.
  assert (valid_range v E empty (Rng T1 T2 K)) as Hr
    by eauto using valid_range_empty_from_valid_tenv.
  inversion Hr; subst.
  assumption.
Qed.

Lemma valid_range_from_valid_tenv : forall X v E1 E2 R,
    valid_tenv v E1 ->
    type_environment_extension E1 E2 ->
    binds X R E1 ->
    valid_range v E1 E2 R.
Proof.
  introv He1 He2 Hb.
  rewrite <- concat_empty_r with (E := E2).
  rewrite <- concat_empty_l with (E := E2).
  apply valid_range_weakening_rec;
    autorewrite with rew_env_concat; auto with wellformed.
  eauto using valid_range_empty_from_valid_tenv.
Qed.

Lemma kinding_from_valid_tenv_lower : forall X v E1 E2 T1 T2 K,
    valid_tenv v E1 ->
    type_environment_extension E1 E2 ->
    binds X (Rng T1 T2 K) E1 ->
    kinding E1 E2 T1 K.
Proof.
  introv He1 He2 Hb.
  assert (valid_range v E1 E2 (Rng T1 T2 K)) as Hr
    by eauto using valid_range_from_valid_tenv.
  inversion Hr; subst.
  assumption.
Qed.

Lemma kinding_from_valid_tenv_upper : forall X v E1 E2 T1 T2 K,
    valid_tenv v E1 ->
    type_environment_extension E1 E2 ->
    binds X (Rng T1 T2 K) E1 ->
    kinding E1 E2 T2 K.
Proof.
  introv He1 He2 Hb.
  assert (valid_range v E1 E2 (Rng T1 T2 K)) as Hr
    by eauto using valid_range_from_valid_tenv.
  inversion Hr; subst.
  assumption.
Qed.

(* *************************************************************** *)
(** Extending valid type environments *)

Lemma valid_tenv_rec_extend : forall v E1 E2 E3 E4,
  valid_tenv_rec v E1 E2 E3 ->
  valid_tenv_rec v (E1 & E2) E4 E3 ->
  type_environment E1 ->
  type_environment_extension (E1 & E2) E3 ->
  valid_tenv_rec v E1 (E2 & E4) E3.
Proof.
  introv He1 He2 He3 He4.
  remember (E1 & E2) as E12.
  induction He2; subst; autorewrite with rew_env_concat; auto.
  apply valid_tenv_rec_push; autorewrite with rew_env_concat; auto.
  auto using valid_tenv_rec_weakening_rec_r,
    type_environment_extension_rev_push with wellformed.
Qed.

Lemma valid_tenv_extend : forall v E1 E2,
  valid_tenv v E1 ->
  valid_tenv_extension v E1 E2 ->
  valid_tenv v (E1 & E2).
Proof.
  unfold valid_tenv in *.
  unfold valid_tenv_extension in *.
  introv He1 He2.
  apply valid_tenv_rec_extend;
    autorewrite with rew_env_concat; auto.
Qed.

Lemma valid_tenv_extension_empty : forall v E,
  valid_tenv_extension v E empty.
Proof.
  auto.
Qed.

(* *************************************************************** *)
(** Kinding from valid store types *)

Lemma kinding_from_valid_store_type : forall l E T P,
    valid_store_type E P ->
    binds l T P ->
    kinding E empty T knd_type.
Proof.
  introv Hp Hb.
  induction Hp.
  - apply binds_empty_inv in Hb; contradiction.
  - destruct (binds_push_inv Hb) as [[Hx Hbnd]|[Hx Hbnd]];
      subst; auto.
Qed.

(* *************************************************************** *)
(** Kinding from type equality *)

Lemma type_equal_kinding_both : forall v E1 E2 Q1 Q2 T1 T2 K,
    type_equal v E1 E2 Q1 Q2 T1 T2 K ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    kinding E1 E2 T1 K /\ kinding E1 E2 T2 K.
Proof.
  introv Hte He1 He2.
  induction Hte;
    repeat match goal with
    | IH : valid_tenv v (E1 & E2) ->
           valid_tenv_extension v (E1 & E2) empty ->
           kinding (E1 & E2) empty _ _ /\
           kinding (E1 & E2) empty _ _ |- _ =>
      destruct IH; auto using valid_tenv_extend
    | IH : valid_tenv v E1 ->
           valid_tenv_extension v E1 E2 ->
           kinding E1 E2 _ _ /\
           kinding E1 E2 _ _ |- _ =>
      destruct IH; auto
    | _ => auto
    end.
  - split; eauto using kinding_weakening_rec_empty,
      kinding_from_valid_tenv_lower with wellformed.
  - split; eauto using kinding_weakening_rec_empty,
      kinding_from_valid_tenv_upper with wellformed.
Qed.

Lemma type_equal_kinding_1 : forall v E1 E2 Q1 Q2 T1 T2 K,
    type_equal v E1 E2 Q1 Q2 T1 T2 K ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    kinding E1 E2 T1 K.
Proof.
  introv Hte He1 He2.
  destruct (type_equal_kinding_both Hte He1 He2).
  assumption.
Qed.

Lemma type_equal_kinding_2 : forall v E1 E2 Q1 Q2 T1 T2 K,
    type_equal v E1 E2 Q1 Q2 T1 T2 K ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    kinding E1 E2 T2 K.
Proof.
  introv Hte He1 He2.
  destruct (type_equal_kinding_both Hte He1 He2).
  assumption.
Qed.

Lemma subtype_kinding_1 : forall v E1 E2 Q1 Q2 T1 T2 K,
    subtype v E1 E2 Q1 Q2 T1 T2 K ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    kinding E1 E2 T1 K.
Proof.
  introv Hs He1 He2.
  unfold subtype in Hs.
  eauto using type_equal_kinding_1.
Qed.

Lemma subtype_kinding_2 : forall v E1 E2 Q1 Q2 T1 T2 K,
    subtype v E1 E2 Q1 Q2 T1 T2 K ->
    valid_tenv v E1 ->
    valid_tenv_extension v E1 E2 ->
    kinding E1 E2 T2 K.
Proof.
  introv Hs He1 He2.
  unfold subtype in Hs.
  assert (kinding E1 E2 (typ_meet T1 T2) K) as Hk
    by eauto using type_equal_kinding_2.
  inversion Hk; subst.
  auto.
Qed.

(* *************************************************************** *)
(** Valid empty schemes *)

Lemma valid_scheme_aux_empty : forall v L E T,
  kinding E empty T knd_type
  <-> valid_scheme_aux v L E (sch_empty T).
Proof.
  split.
  - introv Hk.
    constructor.
    introv Hf.
    apply fresh_zero in Hf.
    unfold bind_sch_ranges; subst; simpl;
      rewrite instance_vars_empty_nil, singles_nil.
    constructor; autorewrite with rew_env_concat; auto.
  - introv Hv.
    inversion Hv; subst.
    assert
      (valid_tenv_extension_and_type v E
        (nil ~: sch_empty T)
        (instance_vars (sch_empty T) nil))
      as Het by auto.
    inversion Het;
      unfold bind_sch_ranges in *; subst; simpl in *;
      rewrite instance_vars_empty_nil, singles_nil in *;
        autorewrite with rew_env_concat in *; auto.
Qed.

Lemma valid_scheme_empty : forall v E T,
  kinding E empty T knd_type
  <-> valid_scheme v E (sch_empty T).
Proof.
  split.
  - introv Hk.
    rewrite valid_scheme_aux_empty
      with (v := v) (L := \{}) (E := E) in Hk.
    eauto.
  - introv Hv.
    inversion Hv; subst.
    rewrite valid_scheme_aux_empty
      with (v := v) (L := L) (E := E).
    auto.
Qed.

(* Direct versions for using with auto. *)

Lemma valid_scheme_empty_of_kinding : forall v E T,
  kinding E empty T knd_type ->
  valid_scheme v E (sch_empty T).
Proof.
  introv Hk.
  rewrite <- valid_scheme_empty.
  assumption.
Qed.

Lemma kinding_of_valid_scheme_empty : forall v E T,
  valid_scheme v E (sch_empty T) ->
  kinding E empty T knd_type.
Proof.
  introv Hs.
  rewrite valid_scheme_empty with (v := v).
  assumption.
Qed.

(* *************************************************************** *)
(** Useful lemma to avoid needing rewrite *)

Lemma kinding_concat_empty : forall E1 E2 T K,
    kinding E1 E2 T K ->
    kinding (E1 & empty) E2 T K.
Proof.
  introv Hk.
  rewrite concat_empty_r.
  assumption.
Qed.

(* *************************************************************** *)
(** Kinding automation *)

Ltac extract_kinding E H T :=
  match type of H with
  | kinding ?E3 ?E4 T _ =>
    match E with
    | E3 & E4 =>
      match goal with
      | He : type_environment_extension E3 E4 |- _ =>
        exact (kinding_extend_empty H He)
      | He : valid_tenv_extension _ E3 E4 |- _ =>
        exact (kinding_extend_empty H
                 (wellformed_valid_tenv_extension He))
      end
    | _ =>
      match E3 with
      | E & empty =>
        rewrite <- concat_empty_r with (E := E); exact H
      | _ => exact H
      end
    end
  | kinding _ _ (typ_constructor _ _) _ =>
      extract_kinding E (kinding_constructor_inv H) T
  | kinding _ _ (typ_or _ _ ?T1 _) _ =>
      match T1 with
      | context[T] => extract_kinding E (kinding_or_inv_l H) T
      | _ => extract_kinding E (kinding_or_inv_r H) T
      end
  | kinding _ _ (typ_proj _ _ _) _ =>
      extract_kinding E (kinding_proj_inv H) T
  | kinding _ _ (typ_variant _) _ =>
      extract_kinding E (kinding_variant_inv H) T
  | kinding _ _ (typ_arrow ?T1 _) _ =>
      match T1 with
      | context[T] => extract_kinding E (kinding_arrow_inv_l H) T
      | _ => extract_kinding E (kinding_arrow_inv_r H) T
      end
  | kinding _ _ (typ_ref _) _ =>
      extract_kinding E (kinding_ref_inv H) T
  | kinding _ _ (typ_prod ?T1 _) _ =>
      match T1 with
      | context[T] => extract_kinding E (kinding_prod_inv_l H) T
      | _ => extract_kinding E (kinding_prod_inv_r H) T
      end
  | kinding _ _ (typ_meet ?T1 _) _ =>
      match T1 with
      | context[T1] => extract_kinding E (kinding_meet_inv_l H) T
      | _ => extract_kinding E (kinding_meet_inv_r H) T
      end
  | kinding _ _ (typ_join ?T1 _) _ =>
      match T1 with
      | context[T] => extract_kinding E (kinding_join_inv_l H) T
      | _ => extract_kinding E (kinding_join_inv_r H) T
      end
  end.

Ltac kinding :=
  match goal with
  | |- kinding ?E _ ?T _ =>
    match goal with
    | H : kinding _ _ ?Th _ |- _ =>
      match Th with
      | context[T] => extract_kinding E H T
      end
    | H : ?Pre -> kinding _ _ ?Th _, Hpre : ?Pre |- _ =>
      match Th with
      | context[T] => extract_kinding E (H Hpre) T
      end
    | H : ?Pre1 -> ?Pre2 -> kinding _ _ ?Th _,
      Hpre1 : ?Pre1, Hpre2 : ?Pre2 |- _ =>
      match Th with
      | context[T] => extract_kinding E (H Hpre1 Hpre2) T
      end
    | He1 : valid_tenv ?v ?E1,
      He2 : valid_tenv_extension ?v ?E1 ?E2,
      H : type_equal ?v ?E1 ?E2 _ _ ?Th _ _ |- _ =>
      match Th with
      | context[T] =>
          extract_kinding E (type_equal_kinding_1 H He1 He2) T
      end
    | He1 : valid_tenv ?v ?E1,
      He2 : valid_tenv_extension ?v ?E1 ?E2,
      H : type_equal ?v ?E1 ?E2 _ _ _ ?Th _ |- _ =>
      match Th with
      | context[T] =>
          extract_kinding E (type_equal_kinding_2 H He1 He2) T
      end
    | He1 : valid_tenv ?v ?E1,
      He2 : valid_tenv_extension ?v ?E1 ?E2,
      H : type_equal ?v (?E1 & ?E2) empty _ _ ?Th _ _ |- _ =>
      match Th with
      | context[T] =>
          extract_kinding E
            (type_equal_kinding_1 H (valid_tenv_extend He1 He2)
               (@valid_tenv_rec_empty v (E1 & E2) empty)) T
      end
    | He1 : valid_tenv ?v ?E1,
      He2 : valid_tenv_extension ?v ?E1 ?E2,
      H : type_equal ?v (?E1 & ?E2) empty _ _ _ ?Th _ |- _ =>
      match Th with
      | context[T] =>
          extract_kinding E
            (type_equal_kinding_2 H (valid_tenv_extend He1 He2)
               (@valid_tenv_rec_empty v (E1 & E2) empty)) T
      end
    | He1 : valid_tenv ?v ?E1,
      He2 : valid_tenv_extension ?v ?E1 ?E2,
      H : subtype ?v ?E1 ?E2 _ _ ?Th _ _ |- _ =>
      match Th with
      | context[T] =>
          extract_kinding E (subtype_kinding_1 H He1 He2) T
      end
    | He1 : valid_tenv ?v ?E1,
      He2 : valid_tenv_extension ?v ?E1 ?E2,
      H : subtype ?v ?E1 ?E2 _ _ _ ?Th _ |- _ =>
      match Th with
      | context[T] =>
          extract_kinding E (subtype_kinding_2 H He1 He2) T
      end
    | He1 : valid_tenv ?v ?E1,
      He2 : valid_tenv_extension ?v ?E1 ?E2,
      H : subtype ?v (?E1 & ?E2) empty _ _ ?Th _ _ |- _ =>
      match Th with
      | context[T] =>
          extract_kinding E
            (subtype_kinding_1 H (valid_tenv_extend He1 He2)
               (@valid_tenv_rec_empty v (E1 & E2) empty)) T
      end
    | He1 : valid_tenv ?v ?E1,
      He2 : valid_tenv_extension ?v ?E1 ?E2,
      H : subtype ?v (?E1 & ?E2) empty _ _ _ ?Th _ |- _ =>
      match Th with
      | context[T] =>
          extract_kinding E
            (subtype_kinding_2 H (valid_tenv_extend He1 He2)
               (@valid_tenv_rec_empty v (E1 & E2) empty)) T
      end
    end
  end.

Hint Extern 1 (kinding _ _ _ _) => kinding : kinding.
