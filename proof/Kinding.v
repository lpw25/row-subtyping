(************************************************
 *          Row Subtyping - Kinding             *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import LibLN Cofinite Disjoint Definitions Substitution Wellformedness.

Hint Constructors
     valid_kind kinding valid_kinds valid_kinds_and_type
     valid_scheme valid_env_aux valid_env
     type_equal_core type_equal_symm type_equal_cong type_equal
     subtype kindings valid_schemes valid_instance valid_store_type.

(* *************************************************************** *)
(** Convenient inversions of valid_kinds_and_types *)

Lemma valid_kinds_and_type_inv : forall chk E Ks T,
    valid_kinds_and_type chk E Ks T ->
    valid_kinds chk E Ks /\ kinding chk E T knd_type.
Proof.
  introv Hks.
  destruct Hks.
  split; auto.
Qed.

Lemma valid_kinds_and_type_inv_kinds : forall chk E Ks T,
    valid_kinds_and_type chk E Ks T ->
    valid_kinds chk E Ks.
Proof.
  introv Hks.
  apply valid_kinds_and_type_inv in Hks.
  intuition auto.
Qed.

Lemma valid_kinds_and_type_inv_type : forall chk E Ks T,
    valid_kinds_and_type chk E Ks T ->
    kinding chk E T knd_type.
Proof.
  introv Hks.
  apply valid_kinds_and_type_inv in Hks.
  intuition auto.
Qed.

(* *************************************************************** *)
(** Convenient constructors and destructors for valid_env_aux *)

(* Constructor for concatenations *)

Lemma valid_env_aux_concat : forall E F G,
    valid_env_aux E F ->
    valid_env_aux E G ->
    environment (F & G) ->
    valid_env_aux E (F & G).
Proof.
  introv He1 He2 Henv.
  induction G using env_ind;
    autorewrite with rew_env_concat in *; auto.
  remember (G & x ~ v) as Gx.
  destruct He2; subst.
  - exfalso; eapply empty_push_inv; eassumption.
  - destruct (eq_push_inv HeqGx) as [? [? ?]]; subst; auto.
    destruct (environment_knd_inv Henv) as [? [? ?]].
    eauto using environment_concat_inv_l.
  - destruct (eq_push_inv HeqGx) as [? [? ?]]; subst; auto.
    destruct (environment_typ_inv Henv) as [? [? ?]].
    eauto using environment_concat_inv_l.
Qed.

(* Constructors for bind_knds *)

Lemma valid_env_aux_bind_knds : forall E F Xs Ks,
    valid_env_aux E F ->
    fresh (dom F) (length Ks) Xs ->
    valid_kinds false E Ks ->
    valid_env_aux E (F & bind_knds Xs Ks).
Proof.
  introv He Hf Hks.
  generalize dependent Ks.
  generalize dependent F.
  induction Xs; introv He Hf Hks; simpl.
  - autorewrite with rew_env_concat; auto.
  - induction Ks; simpl.
    + autorewrite with rew_env_concat; auto.
    + destruct Hf.
      inversion Hks; subst.
      rewrite concat_assoc.
      apply IHXs; auto.
      autorewrite with rew_env_dom in *.
      auto.
Qed.

Lemma valid_env_aux_bind_typs : forall E F xs Ms,
    valid_env_aux E F ->
    fresh (dom F) (length Ms) xs ->
    valid_schemes false E Ms ->
    valid_env_aux E (F & bind_typs xs Ms).
Proof.
  introv He Hf Hss.
  generalize dependent Ms.
  generalize dependent F.
  induction xs; introv He Hf Hss; simpl.
  - autorewrite with rew_env_concat; auto.
  - induction Ms; simpl.
    + autorewrite with rew_env_concat; auto.
    + destruct Hf.
      inversion Hss; subst.
      rewrite concat_assoc.
      apply IHxs; auto.
      autorewrite with rew_env_dom in *.
      auto.
Qed.

(* Inversions for various constructors *)

Lemma valid_env_aux_typ_inv : forall E F x M,
    valid_env_aux E (F & x ~: M) ->
    valid_env_aux E F /\ x # F /\ valid_scheme false E M.
Proof.
  introv He.
  remember (F & x ~: M) as Fx.
  destruct He.
  - apply empty_push_inv in HeqFx; contradiction.
  - destruct (eq_push_inv HeqFx) as [? [? ?]].
    discriminate.
  - destruct (eq_push_inv HeqFx) as [? [Hb ?]].
    inversion Hb; subst.
    splits; auto.
Qed.

Lemma valid_env_aux_knd_inv : forall E F X K,
    valid_env_aux E (F & X ~:: K) ->
    valid_env_aux E F /\ X # F /\ valid_kind false E K.
Proof.
  introv He.
  remember (F & X ~:: K) as Fx.
  destruct He.
  - apply empty_push_inv in HeqFx; contradiction.
  - destruct (eq_push_inv HeqFx) as [? [Hb ?]].
    inversion Hb; subst.
    splits; auto.
  - destruct (eq_push_inv HeqFx) as [? [? ?]].
    discriminate.
Qed.

Lemma valid_env_aux_concat_inv : forall E F G,
    valid_env_aux E (F & G) ->
    valid_env_aux E F /\ valid_env_aux E G.
Proof.
  introv He.
  induction G using env_ind;
    autorewrite with rew_env_concat in *; auto.
  - split; auto with valid_env_aux_regular.
  - remember (F & G & x ~ v) as FGx.
    destruct He; subst.
    + exfalso; eapply empty_push_inv; eassumption.
    + destruct (eq_push_inv HeqFGx) as [? [? ?]]; subst;
        intuition auto.
    + destruct (eq_push_inv HeqFGx) as [? [? ?]]; subst;
        intuition auto.
Qed.

Lemma valid_env_aux_bind_knds_inv : forall E F Xs Ks,
    valid_env_aux E (F & bind_knds Xs Ks) ->
    length Ks = length Xs ->
    valid_env_aux E F /\ fresh (dom F) (length Ks) Xs
    /\ valid_kinds false E Ks.
Proof.
  introv He Hl.
  generalize dependent Ks.
  induction Xs; introv He Hl; induction Ks; try discriminate;
    simpl in *; autorewrite with rew_env_concat in *.
  - splits; auto with valid_env_aux_regular.
  - destruct (valid_env_aux_concat_inv He) as [He2 ?].
    destruct (valid_env_aux_knd_inv He2) as [? [? ?]].
    assert (environment (F & a ~:: a0 & bind_knds Xs Ks)) as He3
      by auto with valid_env_aux_regular.
    destruct (environment_middle_knd_inv He3) as [? [? ?]].
    inversion Hl.
    destruct IHXs with (Ks := Ks) as [? [? ?]];
      auto using valid_env_aux_concat.
    autorewrite with rew_env_dom in *; auto.
    splits; auto using fresh_from_notin.
Qed.

Lemma valid_env_aux_bind_typs_inv : forall E F xs Ms,
    valid_env_aux E (F & bind_typs xs Ms) ->
    length Ms = length xs ->
    valid_env_aux E F /\ fresh (dom F) (length Ms) xs
    /\ valid_schemes false E Ms.
Proof.
  introv He Hl.
  generalize dependent Ms.
  induction xs; introv He Hl; induction Ms; try discriminate;
    simpl in *; autorewrite with rew_env_concat in *.
  - splits; auto with valid_env_aux_regular.
  - destruct (valid_env_aux_concat_inv He) as [He2 ?].
    destruct (valid_env_aux_typ_inv He2) as [? [? ?]].
    assert (environment (F & a ~: a0 & bind_typs xs Ms)) as He3
      by auto with valid_env_aux_regular.
    destruct (environment_middle_typ_inv He3) as [? [? ?]].
    inversion Hl.
    destruct IHxs with (Ms := Ms) as [? [? ?]];
      auto using valid_env_aux_concat.
    autorewrite with rew_env_dom in *; auto.
    splits; auto using fresh_from_notin.
Qed.
    
(* Middle constructors and inversions *)

Lemma valid_env_aux_middle_typ : forall E F G x M,
    valid_env_aux E (F & G) ->
    valid_scheme false E M ->
    x # F & G ->
    valid_env_aux E (F & x ~: M & G).
Proof.
  introv He Hs Hn.
  destruct (valid_env_aux_concat_inv He) as [? ?].
  auto using valid_env_aux_concat, environment_middle_typ
    with valid_scheme_regular valid_env_aux_regular.
Qed.

Lemma valid_env_aux_middle_typ_inv : forall E F G x M,
    valid_env_aux E (F & x ~: M & G) ->
    valid_env_aux E (F & G) /\ valid_scheme false E M /\ x # F & G.
Proof.
  introv He.
  assert (environment (F & x ~: M & G)) as Henv
    by auto with valid_env_aux_regular.
  destruct (environment_middle_typ_inv Henv) as [? [? ?]].
  destruct (valid_env_aux_concat_inv He) as [He2 ?].
  destruct (valid_env_aux_typ_inv He2) as [? [? ?]].
  split; auto using valid_env_aux_concat.
Qed.

Lemma valid_env_aux_middle_knd : forall E F G X K,
    valid_env_aux E (F & G) ->
    valid_kind false E K ->
    X # F & G ->
    valid_env_aux E (F & X ~:: K & G).
Proof.
  introv He Hs Hn.
  destruct (valid_env_aux_concat_inv He) as [? ?].
  auto using valid_env_aux_concat, environment_middle_knd
    with valid_kind_regular valid_env_aux_regular.
Qed.

Lemma valid_env_aux_middle_knd_inv : forall E F G X K,
    valid_env_aux E (F & X ~:: K & G) ->
    valid_env_aux E (F & G) /\ valid_kind false E K /\ X # F & G.
Proof.
  introv He.
  assert (environment (F & X ~:: K & G)) as Henv
    by auto with valid_env_aux_regular.
  destruct (environment_middle_knd_inv Henv) as [? [? ?]].
  destruct (valid_env_aux_concat_inv He) as [He2 ?].
  destruct (valid_env_aux_knd_inv He2) as [? [? ?]].
  split; auto using valid_env_aux_concat.
Qed.

(* Various parital inversions *)

Lemma valid_env_aux_concat_inv_l : forall E F G,
    valid_env_aux E (F & G) ->
    valid_env_aux E F.
Proof.
  introv He.
  destruct (valid_env_aux_concat_inv He).
  assumption.
Qed.

Lemma valid_env_aux_concat_inv_r : forall E F G,
    valid_env_aux E (F & G) ->
    valid_env_aux E G.
Proof.
  introv He.
  destruct (valid_env_aux_concat_inv He).
  assumption.
Qed.

Lemma valid_env_aux_middle_inv_fresh : forall E F G x b,
    valid_env_aux E (F & x ~ b & G) ->
    x # (F & G).
Proof.
  introv He.
  eauto using environment_middle_inv_fresh
    with valid_env_aux_regular.
Qed.

Lemma valid_env_aux_push_inv_fresh : forall E F x b,
    valid_env_aux E (F & x ~ b) ->
    x # F.
Proof.
  introv He.
  rewrite <- concat_empty_r in He.
  rewrite <- (concat_empty_r F).
  eauto using valid_env_aux_middle_inv_fresh.
Qed.

Lemma valid_env_aux_typ_inv_scheme : forall E F x M,
    valid_env_aux E (F & x ~: M) ->
    valid_scheme false E M.
Proof.
  introv He.
  destruct (valid_env_aux_typ_inv He) as [? [? ?]].
  assumption.
Qed.

Lemma valid_env_aux_knd_inv_kind : forall E F X K,
    valid_env_aux E (F & X ~:: K) ->
    valid_kind false E K.
Proof.
  introv He.
  destruct (valid_env_aux_knd_inv He) as [? [? ?]].
  assumption.
Qed.

Lemma valid_env_aux_middle_inv_env : forall E F G x v,
    valid_env_aux E (F & x ~ v & G) ->
    valid_env_aux E (F & G).
Proof.
  introv He.
  destruct (valid_env_aux_concat_inv He) as [He2 ?].
  destruct (valid_env_aux_concat_inv He2) as [? ?].
  eauto using valid_env_aux_concat,
    environment_middle_inv_env
      with valid_env_aux_regular.
Qed.

Lemma valid_env_aux_typ_middle_inv_scheme : forall E F G x M,
    valid_env_aux E (F & x ~: M & G) ->
    valid_scheme false E M.
Proof.
  introv He.
  destruct (valid_env_aux_concat_inv He) as [He2 ?].
  eauto using valid_env_aux_typ_inv_scheme.
Qed.

Lemma valid_env_aux_knd_middle_inv_kind : forall E F G X K,
    valid_env_aux E (F & X ~:: K & G) ->
    valid_kind false E K.
Proof.
  introv He.
  destruct (valid_env_aux_concat_inv He) as [He2 ?].
  eauto using valid_env_aux_knd_inv_kind.
Qed.

(* *************************************************************** *)
(** Unchecked kindings from any kindings *)

Lemma combined_kinding_to_unchecked :
     (forall chk E K,
      valid_kind chk E K ->
      valid_kind false E K)
  /\ (forall chk E T K,
      kinding chk E T K ->
      kinding false E T K)
  /\ (forall chk E Ks,
      valid_kinds chk E Ks ->
      valid_kinds false E Ks)
  /\ (forall chk E Ks T,
      valid_kinds_and_type chk E Ks T ->
      valid_kinds_and_type false E Ks T)
  /\ (forall chk E Ms,
      valid_scheme chk E Ms ->
      valid_scheme false E Ms)
  /\ (forall E G,
      valid_env_aux E G ->
      valid_env_aux E G)
  /\ (forall chk E,
      valid_env chk E ->
      valid_env false E)
  /\ (forall chk E T1 T2 K,
      type_equal_core chk E T1 T2 K ->
      type_equal_core false E T1 T2 K)
  /\ (forall chk E T1 T2 K,
      type_equal_symm chk E T1 T2 K ->
      type_equal_symm false E T1 T2 K)
  /\ (forall chk E T1 T2 K,
      type_equal_cong chk E T1 T2 K ->
      type_equal_cong false E T1 T2 K)
  /\ (forall chk E T1 T2 K,
      type_equal chk E T1 T2 K ->
      type_equal false E T1 T2 K)
  /\ (forall chk E T1 T2 cs,
      subtype chk E T1 T2 cs ->
      subtype false E T1 T2 cs).
Proof.
  apply combined_kinding_mutind; intros;
    econstr eauto with valid_env_aux_regular.
Qed.

Lemma valid_kind_to_unchecked : forall chk E K,
    valid_kind chk E K ->
    valid_kind false E K.
Proof.
  introv Hv.
  pose combined_kinding_to_unchecked.
  intuition eauto.
Qed.

Lemma kinding_to_unchecked : forall chk E T K,
    kinding chk E T K ->
    kinding false E T K.
Proof.
  introv Hk.
  pose combined_kinding_to_unchecked.
  intuition eauto.
Qed.

Lemma valid_kinds_to_unchecked : forall chk E Ks,
    valid_kinds chk E Ks ->
    valid_kinds false E Ks.
Proof.
  introv Hv.
  pose combined_kinding_to_unchecked.
  intuition eauto.
Qed.

Lemma valid_kinds_and_type_to_unchecked : forall chk E Ks T,
    valid_kinds_and_type chk E Ks T ->
    valid_kinds_and_type false E Ks T.
Proof.
  introv Hv.
  pose combined_kinding_to_unchecked.
  intuition eauto.
Qed.

Lemma valid_scheme_to_unchecked : forall chk E Ms,
    valid_scheme chk E Ms ->
    valid_scheme false E Ms.
Proof.
  introv Hv.
  pose combined_kinding_to_unchecked.
  intuition eauto.
Qed.

Lemma valid_env_to_unchecked : forall chk E,
    valid_env chk E ->
    valid_env false E.
Proof.
  introv Hv.
  pose combined_kinding_to_unchecked.
  intuition eauto.
Qed.

Lemma type_equal_core_to_unchecked : forall chk E T1 T2 K,
    type_equal_core chk E T1 T2 K ->
    type_equal_core false E T1 T2 K.
Proof.
  introv Hte.
  pose combined_kinding_to_unchecked.
  intuition eauto.
Qed.

Lemma type_equal_symm_to_unchecked : forall chk E T1 T2 K,
    type_equal_symm chk E T1 T2 K ->
    type_equal_symm false E T1 T2 K.
Proof.
  introv Hte.
  pose combined_kinding_to_unchecked.
  intuition eauto.
Qed.

Lemma type_equal_cong_to_unchecked : forall chk E T1 T2 K,
    type_equal_cong chk E T1 T2 K ->
    type_equal_cong false E T1 T2 K.
Proof.
  introv Hte.
  pose combined_kinding_to_unchecked.
  intuition eauto.
Qed.

Lemma type_equal_to_unchecked : forall chk E T1 T2 K,
    type_equal chk E T1 T2 K ->
    type_equal false E T1 T2 K.
Proof.
  introv Hte.
  pose combined_kinding_to_unchecked.
  intuition eauto.
Qed.

Lemma subtype_to_unchecked : forall chk E T1 T2 cs,
    subtype chk E T1 T2 cs ->
    subtype false E T1 T2 cs.
Proof.
  introv Hs.
  pose combined_kinding_to_unchecked.
  intuition eauto.
Qed.

Lemma kindings_to_unchecked : forall chk E Ts Ks,
    kindings chk E Ts Ks ->
    kindings false E Ts Ks.
Proof.
  introv Hks.
  induction Hks;
    eauto using valid_env_to_unchecked, kinding_to_unchecked.
Qed.

Lemma valid_schemes_to_unchecked : forall chk E Ms,
    valid_schemes chk E Ms ->
    valid_schemes false E Ms.
Proof.
  introv Hss.
  induction Hss;
    eauto using valid_env_to_unchecked, valid_scheme_to_unchecked.
Qed.

(* *************************************************************** *)
(** Any kindings from checked kindings *)

Lemma combined_kinding_from_checked :
     (forall chk E K,
      valid_kind chk E K ->
      (forall chk',
        chk = true ->
        valid_kind chk' E K))
  /\ (forall chk E T K,
      kinding chk E T K ->
      (forall chk',
        chk = true ->
        kinding chk' E T K))
  /\ (forall chk E Ks,
      valid_kinds chk E Ks ->
      (forall chk',
        chk = true ->
        valid_kinds chk' E Ks))
  /\ (forall chk E Ks T,
      valid_kinds_and_type chk E Ks T ->
      (forall chk',
        chk = true ->
        valid_kinds_and_type chk' E Ks T))
  /\ (forall chk E Ms,
      valid_scheme chk E Ms ->
      (forall chk',
        chk = true ->
        valid_scheme chk' E Ms))
  /\ (forall E G,
      valid_env_aux E G ->
      valid_env_aux E G)
  /\ (forall chk E,
      valid_env chk E ->
      (forall chk',
        chk = true ->
        valid_env chk' E))
  /\ (forall chk E T1 T2 K,
      type_equal_core chk E T1 T2 K ->
      (forall chk',
        chk = true ->
        type_equal_core chk' E T1 T2 K))
  /\ (forall chk E T1 T2 K,
      type_equal_symm chk E T1 T2 K ->
      (forall chk',
        chk = true ->
        type_equal_symm chk' E T1 T2 K))
  /\ (forall chk E T1 T2 K,
      type_equal_cong chk E T1 T2 K ->
      (forall chk',
        chk = true ->
        type_equal_cong chk' E T1 T2 K))
  /\ (forall chk E T1 T2 K,
      type_equal chk E T1 T2 K ->
      (forall chk',
        chk = true ->
        type_equal chk' E T1 T2 K))
  /\ (forall chk E T1 T2 cs,
      subtype chk E T1 T2 cs ->
      (forall chk',
        chk = true ->
        subtype chk' E T1 T2 cs)).
Proof.
  apply combined_kinding_mutind; intros;
    econstr eauto with valid_env_aux_regular.
  - destruct chk'; auto with valid_env_aux_regular.
  - discriminate.
Qed.

Lemma valid_kind_from_checked : forall chk E K,
    valid_kind true E K ->
    valid_kind chk E K.
Proof.
  introv Hv.
  pose combined_kinding_from_checked.
  intuition eauto.
Qed.

Lemma kinding_from_checked : forall chk E T K,
    kinding true E T K ->
    kinding chk E T K.
Proof.
  introv Hk.
  pose combined_kinding_from_checked.
  intuition eauto.
Qed.

Lemma valid_kinds_from_checked : forall chk E Ks,
    valid_kinds true E Ks ->
    valid_kinds chk E Ks.
Proof.
  introv Hv.
  pose combined_kinding_from_checked.
  intuition eauto.
Qed.

Lemma valid_kinds_and_type_from_checked : forall chk E Ks T,
    valid_kinds_and_type true E Ks T ->
    valid_kinds_and_type chk E Ks T.
Proof.
  introv Hv.
  pose combined_kinding_from_checked.
  intuition eauto.
Qed.

Lemma valid_scheme_from_checked : forall chk E Ms,
    valid_scheme true E Ms ->
    valid_scheme chk E Ms.
Proof.
  introv Hv.
  pose combined_kinding_from_checked.
  intuition eauto.
Qed.

Lemma valid_env_from_checked : forall chk E,
    valid_env true E ->
    valid_env chk E.
Proof.
  introv Hv.
  pose combined_kinding_from_checked.
  intuition eauto.
Qed.

Lemma type_equal_core_from_checked : forall chk E T1 T2 K,
    type_equal_core true E T1 T2 K ->
    type_equal_core chk E T1 T2 K.
Proof.
  introv Hte.
  pose combined_kinding_from_checked.
  intuition eauto.
Qed.

Lemma type_equal_symm_from_checked : forall chk E T1 T2 K,
    type_equal_symm true E T1 T2 K ->
    type_equal_symm chk E T1 T2 K.
Proof.
  introv Hte.
  pose combined_kinding_from_checked.
  intuition eauto.
Qed.

Lemma type_equal_cong_from_checked : forall chk E T1 T2 K,
    type_equal_cong true E T1 T2 K ->
    type_equal_cong chk E T1 T2 K.
Proof.
  introv Hte.
  pose combined_kinding_from_checked.
  intuition eauto.
Qed.

Lemma type_equal_from_checked : forall chk E T1 T2 K,
    type_equal true E T1 T2 K ->
    type_equal chk E T1 T2 K.
Proof.
  introv Hte.
  pose combined_kinding_from_checked.
  intuition eauto.
Qed.

Lemma subtype_from_checked : forall chk E T1 T2 cs,
    subtype true E T1 T2 cs ->
    subtype chk E T1 T2 cs.
Proof.
  introv Hs.
  pose combined_kinding_from_checked.
  intuition eauto.
Qed.

Lemma kindings_from_checked : forall chk E Ts Ks,
    kindings true E Ts Ks ->
    kindings chk E Ts Ks.
Proof.
  introv Hks.
  remember true as chk'.
  induction Hks; subst;
    eauto using valid_env_from_checked, kinding_from_checked.
Qed.

Lemma valid_schemes_from_checked : forall chk E Ms,
    valid_schemes true E Ms ->
    valid_schemes chk E Ms.
Proof.
  introv Hss.
  remember true as chk'.
  induction Hss; subst;
    eauto using valid_env_from_checked, valid_scheme_from_checked.
Qed.

(* *************************************************************** *)
(** Weakening *)

Lemma combined_kinding_unchecked_weakening :
     (forall chk EG K,
      valid_kind_regular chk EG K ->
      (forall E F G,
          EG = E & G ->
          valid_env false (E & F & G) ->
          valid_kind false (E & F & G) K))
  /\ (forall chk EG T K,
      kinding_regular chk EG T K ->
      (forall E F G,
          EG = E & G ->
          valid_env false (E & F & G) ->
          kinding false (E & F & G) T K))
  /\ (forall chk EG Ks,
      valid_kinds_regular chk EG Ks ->
      (forall E F G,
          EG = E & G ->
          valid_env false (E & F & G) ->
          valid_kinds false (E & F & G) Ks))
  /\ (forall chk EG Ks T,
      valid_kinds_and_type_regular chk EG Ks T ->
      (forall E F G,
          EG = E & G ->
          valid_env false (E & F & G) ->
          valid_kinds_and_type false (E & F & G) Ks T))
  /\ (forall chk EG M,
      valid_scheme_regular chk EG M ->
      (forall E F G,
          EG = E & G ->
          valid_env false (E & F & G) ->
          valid_scheme false (E & F & G) M))
  /\ (forall EG H,
      valid_env_aux_regular EG H ->
      (forall E F G,
          EG = E & G ->
          valid_env false (E & F & G) ->
          valid_env_aux (E & F & G) H))
  /\ (forall chk E,
      valid_env_regular chk E -> valid_env false E)
  /\ (forall chk EG T1 T2 K,
      type_equal_core_regular chk EG T1 T2 K ->
      (forall E F G,
          EG = E & G ->
          valid_env false (E & F & G) ->
          type_equal_core false (E & F & G) T1 T2 K))
  /\ (forall chk EG T1 T2 K,
      type_equal_symm_regular chk EG T1 T2 K ->
      (forall E F G,
          EG = E & G ->
          valid_env false (E & F & G) ->
          type_equal_symm false (E & F & G) T1 T2 K))
  /\ (forall chk EG T1 T2 K,
      type_equal_cong_regular chk EG T1 T2 K ->
      (forall E F G,
          EG = E & G ->
          valid_env false (E & F & G) ->
          type_equal_cong false (E & F & G) T1 T2 K))
  /\ (forall chk EG T1 T2 K,
      type_equal_regular chk EG T1 T2 K ->
      (forall E F G,
          EG = E & G ->
          valid_env false (E & F & G) ->
          type_equal false (E & F & G) T1 T2 K))
  /\ (forall chk EG T1 T2 cs,
      subtype_regular chk EG T1 T2 cs ->
      (forall E F G,
          EG = E & G ->
          valid_env false (E & F & G) ->
          subtype false (E & F & G) T1 T2 cs)).
Proof.
  apply combined_kinding_regular_mutind; intros; subst; econstr auto.
  - auto using binds_weakening with valid_env_regular.
  - apply_fresh valid_scheme_c as Xs; auto.
    assert (environment (E0 & F & G & Xs ~::* M))
      by (apply environment_kinds;
          autorewrite with rew_env_dom;
          auto with valid_env_regular).   
    assert (valid_env false (E0 & F & G & Xs ~::* M)) as He by auto.
    rewrite <- concat_assoc.
    apply H0; autorewrite with rew_env_concat; auto.
  - auto with valid_env_regular.
Qed.

Lemma valid_env_aux_weakening : forall chk E F G H,
   valid_env_aux (E & G) H -> 
   valid_env chk (E & F & G) ->
   valid_env_aux (E & F & G) H.
Proof.
  introv Hea He.
  apply valid_env_to_unchecked in He.
  apply regular_valid_env_aux in Hea.
  pose combined_kinding_unchecked_weakening.
  intuition eauto.
Qed.

Lemma valid_env_aux_weakening_l : forall chk E F H,
   valid_env_aux E H -> 
   valid_env chk (E & F) ->
   valid_env_aux (E & F) H.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  eapply valid_env_aux_weakening; rewrite concat_empty_r; eassumption.
Qed.

Lemma valid_env_aux_bind_knds_both : forall E Xs Ks,
  valid_env_aux E E ->
  fresh (dom E) (length Ks) Xs ->
  valid_kinds false (E & bind_knds Xs Ks) Ks ->
  valid_env_aux (E & bind_knds Xs Ks) (E & bind_knds Xs Ks).
Proof.
  introv He Hf Hks.
  fresh_length Hf as Hl.
  apply valid_env_aux_weakening_l
    with (chk := false) (F := bind_knds Xs Ks) in He;
    auto with valid_kinds_regular.
  auto using valid_env_aux_bind_knds.
Qed.

Lemma valid_env_bind_knds : forall chk chk' E Xs Ks,
    valid_env chk E ->
    fresh (dom E) (length Ks) Xs ->
    valid_kinds chk' (E & bind_knds Xs Ks) Ks ->
    valid_env chk (E & bind_knds Xs Ks).
Proof.
  introv He Hf Hks.
  apply valid_kinds_to_unchecked in Hks.
  fresh_length Hf as Hl.
  destruct He.
  - auto using valid_env_aux_bind_knds_both.
  - rewrite Hl in Hf.
    auto using environment_bind_knds with valid_kinds_regular.
Qed.

Lemma valid_env_unchecked_kinds : forall chk E Xs M,
    valid_env chk E ->
    fresh (dom E) (sch_arity M) Xs ->
    scheme M ->
    valid_env false (E & Xs ~::* M).
Proof.
  introv He Hf Hs.
  apply valid_env_no_check.
  apply environment_kinds; auto with valid_env_regular.
Qed.

Lemma valid_env_bind_sch_kinds : forall chk chk' E Xs M,
    valid_env chk E ->
    fresh (dom E) (sch_arity M) Xs ->
    valid_kinds chk' (E & Xs ~::* M)
      (knd_open_vars_list (sch_kinds M) Xs) ->
    valid_env chk (E & Xs ~::* M).
Proof.
  introv He Hf Hks.
  eapply valid_env_bind_knds; eauto.
  rewrite knd_open_vars_list_length.
  rewrite sch_arity_length in Hf.
  auto.
Qed.

Lemma combined_kinding_weakening :
     (forall chk EG K,
      valid_kind_regular chk EG K ->
      (forall chk' E F G,
          EG = E & G ->
          valid_env chk' (E & F & G) ->
          valid_kind (chk' && chk) (E & F & G) K))
  /\ (forall chk EG T K,
      kinding_regular chk EG T K ->
      (forall chk' E F G,
          EG = E & G ->
          valid_env chk' (E & F & G) ->
          kinding (chk' && chk) (E & F & G) T K))
  /\ (forall chk EG Ks,
      valid_kinds_regular chk EG Ks ->
      (forall chk' E F G,
          EG = E & G ->
          valid_env chk' (E & F & G) ->
          valid_kinds (chk' && chk) (E & F & G) Ks))
  /\ (forall chk EG Ks T,
      valid_kinds_and_type_regular chk EG Ks T ->
      (forall chk' E F G,
          EG = E & G ->
          valid_env chk' (E & F & G) ->
          valid_kinds_and_type (chk' && chk) (E & F & G) Ks T))
  /\ (forall chk EG M,
      valid_scheme_regular chk EG M ->
      (forall chk' E F G,
          EG = E & G ->
          valid_env chk' (E & F & G) ->
          valid_scheme (chk' && chk) (E & F & G) M))
  /\ (forall EG H,
      valid_env_aux_regular EG H ->
      (forall chk' E F G,
          EG = E & G ->
          valid_env chk' (E & F & G) ->
          valid_env_aux (E & F & G) H))
  /\ (forall chk EG,
      valid_env_regular chk EG ->
      (forall chk' E F G,
          EG = E & G ->
          valid_env chk' (E & F & G) ->
          valid_env (chk' && chk) (E & F & G)))
  /\ (forall chk EG T1 T2 K,
      type_equal_core_regular chk EG T1 T2 K ->
      (forall chk' E F G,
          EG = E & G ->
          valid_env chk' (E & F & G) ->
          type_equal_core (chk' && chk) (E & F & G) T1 T2 K))
  /\ (forall chk EG T1 T2 K,
      type_equal_symm_regular chk EG T1 T2 K ->
      (forall chk' E F G,
          EG = E & G ->
          valid_env chk' (E & F & G) ->
          type_equal_symm (chk' && chk) (E & F & G) T1 T2 K))
  /\ (forall chk EG T1 T2 K,
      type_equal_cong_regular chk EG T1 T2 K ->
      (forall chk' E F G,
          EG = E & G ->
          valid_env chk' (E & F & G) ->
          type_equal_cong (chk' && chk) (E & F & G) T1 T2 K))
  /\ (forall chk EG T1 T2 K,
      type_equal_regular chk EG T1 T2 K ->
      (forall chk' E F G,
          EG = E & G ->
          valid_env chk' (E & F & G) ->
          type_equal (chk' && chk) (E & F & G) T1 T2 K))
  /\ (forall chk EG T1 T2 cs,
      subtype_regular chk EG T1 T2 cs ->
      (forall chk' E F G,
          EG = E & G ->
          valid_env chk' (E & F & G) ->
          subtype (chk' && chk) (E & F & G) T1 T2 cs)).
Proof.
  apply combined_kinding_regular_mutind; intros; subst; econstr auto.
  - auto using binds_weakening with valid_env_regular.
  - apply_fresh valid_scheme_c as Xs; auto.
    rewrite <- concat_assoc.
    apply H0; autorewrite with rew_env_concat; auto.
    eapply valid_env_bind_sch_kinds;
      autorewrite with rew_env_dom; auto.
    apply valid_kinds_and_type_inv_kinds
      with (T := typ_open_vars (sch_body M) Xs).
    rewrite <- concat_assoc.
    replace false with (andb false chk) by (simpl; reflexivity).
    apply H0; autorewrite with rew_env_concat; auto.
    apply valid_env_unchecked_kinds with (chk := chk');
      autorewrite with rew_env_dom; auto.
  - auto with valid_env_regular.
  - eauto using valid_kind_to_unchecked.
  - eauto using valid_scheme_to_unchecked.
  - destruct chk'; auto.
  - destruct chk'; simpl; auto with valid_env_regular.
Qed.

Lemma and_same : forall b,
    b = (andb b b).
Proof.
  destruct b; simpl; reflexivity.
Qed.  

Lemma valid_kind_weakening : forall chk E F G K,
    valid_kind chk (E & G) K ->
    valid_env chk (E & F & G) ->
    valid_kind chk (E & F & G) K.
Proof.
  introv Hv He.
  apply regular_valid_kind in Hv.
  rewrite (and_same chk).
  pose combined_kinding_weakening.
  intuition eauto.
Qed.

Lemma valid_kind_weakening_l : forall chk E F K,
    valid_kind chk E K ->
    valid_env chk (E & F) ->
    valid_kind chk (E & F) K.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply valid_kind_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma kinding_weakening : forall chk E F G T K,
   kinding chk (E & G) T K -> 
   valid_env chk (E & F & G) ->
   kinding chk (E & F & G) T K.
Proof.
  introv Hk He.
  apply regular_kinding in Hk.
  rewrite (and_same chk).
  pose combined_kinding_weakening.
  intuition eauto.
Qed.

Lemma kinding_weakening_l : forall chk E F T K,
   kinding chk E T K -> 
   valid_env chk (E & F) ->
   kinding chk (E & F) T K.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply kinding_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma valid_kinds_weakening : forall chk E F G Ks,
    valid_kinds chk (E & G) Ks ->
    valid_env chk (E & F & G) ->
    valid_kinds chk (E & F & G) Ks.
Proof.
  introv Hks He.
  apply regular_valid_kinds in Hks.
  rewrite (and_same chk).
  pose combined_kinding_weakening.
  intuition eauto.
Qed.

Lemma valid_kinds_weakening_l : forall chk E F Ks,
    valid_kinds chk E Ks ->
    valid_env chk (E & F) ->
    valid_kinds chk (E & F) Ks.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply valid_kinds_weakening;
    rewrite? concat_empty_r; assumption.
Qed.

Lemma valid_kinds_and_type_weakening : forall chk E F G Ks T,
    valid_kinds_and_type chk (E & G) Ks T ->
    valid_env chk (E & F & G) ->
    valid_kinds_and_type chk (E & F & G) Ks T.
Proof.
  introv Hks He.
  apply regular_valid_kinds_and_type in Hks.
  rewrite (and_same chk).
  pose combined_kinding_weakening.
  intuition eauto.
Qed.

Lemma valid_kinds_and_type_weakening_l : forall chk E F Ks T,
    valid_kinds_and_type chk E Ks T ->
    valid_env chk (E & F) ->
    valid_kinds_and_type chk (E & F) Ks T.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply valid_kinds_and_type_weakening;
    rewrite? concat_empty_r; assumption.
Qed.

Lemma valid_scheme_weakening : forall chk E F G M,
    valid_scheme chk (E & G) M ->
    valid_env chk (E & F & G) ->
    valid_scheme chk (E & F & G) M.
Proof.
  introv Hs He.
  apply regular_valid_scheme in Hs.
  rewrite (and_same chk).
  pose combined_kinding_weakening.
  intuition eauto.
Qed.

Lemma valid_scheme_weakening_l : forall chk E F M,
    valid_scheme chk E M ->
    valid_env chk (E & F) ->
    valid_scheme chk (E & F) M.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply valid_scheme_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma type_equal_core_weakening : forall chk E F G T1 T2 K,
   type_equal_core chk (E & G) T1 T2 K -> 
   valid_env chk (E & F & G) ->
   type_equal_core chk (E & F & G) T1 T2 K.
Proof.
  introv Hte He.
  apply regular_type_equal_core in Hte.
  rewrite (and_same chk).
  pose combined_kinding_weakening.
  intuition eauto.
Qed.

Lemma type_equal_core_weakening_l : forall chk E F T1 T2 K,
   type_equal_core chk E T1 T2 K -> 
   valid_env chk (E & F) ->
   type_equal_core chk (E & F) T1 T2 K.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply type_equal_core_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma type_equal_symm_weakening : forall chk E F G T1 T2 K,
   type_equal_symm chk (E & G) T1 T2 K -> 
   valid_env chk (E & F & G) ->
   type_equal_symm chk (E & F & G) T1 T2 K.
Proof.
  introv Hte He.
  apply regular_type_equal_symm in Hte.
  rewrite (and_same chk).
  pose combined_kinding_weakening.
  intuition eauto.
Qed.

Lemma type_equal_symm_weakening_l : forall chk E F T1 T2 K,
   type_equal_symm chk E T1 T2 K -> 
   valid_env chk (E & F) ->
   type_equal_symm chk (E & F) T1 T2 K.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply type_equal_symm_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma type_equal_cong_weakening : forall chk E F G T1 T2 K,
   type_equal_cong chk (E & G) T1 T2 K -> 
   valid_env chk (E & F & G) ->
   type_equal_cong chk (E & F & G) T1 T2 K.
Proof.
  introv Hte He.
  apply regular_type_equal_cong in Hte.
  rewrite (and_same chk).
  pose combined_kinding_weakening.
  intuition eauto.
Qed.

Lemma type_equal_cong_weakening_l : forall chk E F T1 T2 K,
   type_equal_cong chk E T1 T2 K -> 
   valid_env chk (E & F) ->
   type_equal_cong chk (E & F) T1 T2 K.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply type_equal_cong_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma type_equal_weakening : forall chk E F G T1 T2 K,
   type_equal chk (E & G) T1 T2 K -> 
   valid_env chk (E & F & G) ->
   type_equal chk (E & F & G) T1 T2 K.
Proof.
  introv Hte He.
  apply regular_type_equal in Hte.
  rewrite (and_same chk).
  pose combined_kinding_weakening.
  intuition eauto.
Qed.

Lemma type_equal_weakening_l : forall chk E F T1 T2 K,
   type_equal chk E T1 T2 K -> 
   valid_env chk (E & F) ->
   type_equal chk (E & F) T1 T2 K.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply type_equal_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma subtype_weakening : forall chk E F G T1 T2 cs,
    subtype chk (E & G) T1 T2 cs ->
    valid_env chk (E & F & G) ->
    subtype chk (E & F & G) T1 T2 cs.
Proof.
  introv Hs He.
  apply regular_subtype in Hs.
  rewrite (and_same chk).
  pose combined_kinding_weakening.
  intuition eauto.
Qed.

Lemma subtype_weakening_l : forall chk E F T1 T2 cs,
    subtype chk E T1 T2 cs ->
    valid_env chk (E & F) ->
    subtype chk (E & F) T1 T2 cs.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply subtype_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma kindings_weakening : forall chk E F G Ts Ks,
   kindings chk (E & G) Ts Ks -> 
   valid_env chk (E & F & G) ->
   kindings chk (E & F & G) Ts Ks.
Proof.
  introv Hks He.
  remember (E & G) as EG.
  induction Hks; subst; eauto using kinding_weakening.
Qed.  

Lemma kindings_weakening_l : forall chk E F Ts Ks,
   kindings chk E Ts Ks -> 
   valid_env chk (E & F) ->
   kindings chk (E & F) Ts Ks.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply kindings_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma valid_schemes_weakening : forall chk E F G Ms,
   valid_schemes chk (E & G) Ms -> 
   valid_env chk (E & F & G) ->
   valid_schemes chk (E & F & G) Ms.
Proof.
  introv Hss He.
  remember (E & G) as EG.
  induction Hss; subst; eauto using valid_scheme_weakening.
Qed.  

Lemma valid_schemes_weakening_l : forall chk E F Ms,
   valid_schemes chk E Ms -> 
   valid_env chk (E & F) ->
   valid_schemes chk (E & F) Ms.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply valid_schemes_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma valid_instance_weakening : forall E F G Ts M,
  valid_instance (E & G) Ts M ->
  valid_env true (E & F & G) ->
  valid_instance (E & F & G) Ts M.
Proof.
  introv Hi He.
  remember (E & G) as EG.
  destruct Hi; subst;
    auto using kindings_weakening, kinding_weakening.
Qed.

Lemma valid_instance_weakening_l : forall E F Ts M,
  valid_instance E Ts M ->
  valid_env true (E & F) ->
  valid_instance (E & F) Ts M.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply valid_instance_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma valid_store_type_weakening : forall E F G P,
  valid_store_type (E & G) P ->
  valid_env true (E & F & G) ->
  valid_store_type (E & F & G) P.
Proof.
  introv Hs He.
  remember (E & G) as EG.
  induction Hs; subst; auto using kinding_weakening.
Qed.

Lemma valid_store_type_weakening_l : forall E F P,
  valid_store_type E P ->
  valid_env true (E & F) ->
  valid_store_type (E & F) P.
Proof.
  introv Hs He.
  rewrite <- concat_empty_r with (E := E & F).
  apply valid_store_type_weakening;
    rewrite concat_empty_r; assumption.
Qed.

Lemma valid_env_aux_type_weakening : forall E F G x M,
    x # F ->
    valid_env_aux (E & G & x ~: M) (E & G & x ~: M) ->
    valid_env true (E & F & G) ->
    valid_env_aux (E & F & G & x ~: M) (E & F & G & x ~: M).
Proof.
  introv Hin He1 He2.
  assert (valid_env false (E & F & G & x ~: M)) as He3
    by auto using environment_typ_weakening
         with valid_env_regular valid_env_aux_regular.
  rewrite <- concat_assoc in He1. 
  apply valid_env_aux_weakening with (chk := false) (F := F) in He1;
    autorewrite with rew_env_concat;
    auto.
  rewrite! concat_assoc in He1.
  remember true as chk.
  remember (E & F & G) as EFG.
  destruct He2 as [? He4|]; subst; try discriminate.
  apply valid_env_aux_weakening_l
    with (chk := false) (F := x ~: M) in He4; auto.
  destruct (valid_env_aux_concat_inv He1).
  auto using valid_env_aux_concat, ok_from_environment
    with valid_env_aux_regular.
Qed.

Lemma valid_env_type_weakening : forall chk E F G x M,
    x # F ->
    valid_env chk (E & G & x ~: M) ->
    valid_env chk (E & F & G) ->
    valid_env chk (E & F & G & x ~: M).
Proof.
  introv Hin He1 He2.
  destruct chk.
  - inversion He1; subst.
    inversion He2; subst.
    auto using valid_env_aux_type_weakening.
  - auto using environment_typ_weakening with valid_env_regular.
Qed.

Lemma valid_env_type_weakening_l : forall chk E F x M,
    x # F ->
    valid_env chk (E & x ~: M) ->
    valid_env chk (E & F) ->
    valid_env chk (E & F & x ~: M).
Proof.
  introv Hn He1 He2.
  rewrite <- concat_empty_r with (E := E & F).
  apply valid_env_type_weakening; rewrite? concat_empty_r; assumption.
Qed.

Lemma valid_env_aux_kinds_weakening : forall E F G Xs M,
    fresh (dom F) (sch_arity M) Xs ->
    valid_env_aux (E & G & Xs ~::* M) (E & G & Xs ~::* M) ->
    valid_env true (E & F & G) ->
    valid_env_aux (E & F & G & Xs ~::* M) (E & F & G & Xs ~::* M).
Proof.
  introv Hf He1 He2.
  assert (valid_env false (E & F & G & Xs ~::* M)) as He3
    by auto using environment_kinds_weakening
         with valid_env_regular valid_env_aux_regular.
  rewrite <- concat_assoc in He1. 
  apply valid_env_aux_weakening with (chk := false) (F := F) in He1;
    autorewrite with rew_env_concat;
    auto.
  rewrite! concat_assoc in He1.
  remember true as chk.
  remember (E & F & G) as EFG.
  destruct He2 as [? He4|]; subst; try discriminate.
  apply valid_env_aux_weakening_l
    with (chk := false) (F := Xs ~::* M) in He4; auto.
  destruct (valid_env_aux_concat_inv He1).
  auto using valid_env_aux_concat, ok_from_environment
    with valid_env_aux_regular.
Qed.

Lemma valid_env_kinds_weakening : forall chk E F G Xs M,
    fresh (dom F) (sch_arity M) Xs ->
    valid_env chk (E & G & Xs ~::* M) ->
    valid_env chk (E & F & G) ->
    valid_env chk (E & F & G & Xs ~::* M).
Proof.
  introv Hf He1 He2.
  destruct chk.
  - inversion He1; subst.
    inversion He2; subst.
    auto using valid_env_aux_kinds_weakening.
  - auto using environment_kinds_weakening with valid_env_regular.
Qed.

Lemma valid_env_kinds_weakening_l : forall chk E F Xs M,
    fresh (dom F) (sch_arity M) Xs ->
    valid_env chk (E & Xs ~::* M) ->
    valid_env chk (E & F) ->
    valid_env chk (E & F & Xs ~::* M).
Proof.
  introv Hf He1 He2.
  rewrite <- concat_empty_r with (E := E & F).
  apply valid_env_kinds_weakening;
    rewrite? concat_empty_r; assumption.
Qed.

Lemma valid_env_aux_bind_typs_both : forall E xs Ms,
  valid_env_aux E E ->
  fresh (dom E) (length Ms) xs ->
  valid_schemes false E Ms ->
  valid_env_aux (E & bind_typs xs Ms) (E & bind_typs xs Ms).
Proof.
  introv He Hf Hss.
  fresh_length Hf as Hl.
  assert (valid_env false (E & bind_typs xs Ms))
    by auto using environment_bind_typs with valid_schemes_regular.
  apply valid_schemes_weakening_l
    with (chk := false) (F := bind_typs xs Ms) in Hss;
    auto.
  apply valid_env_aux_weakening_l
    with (chk := false) (F := bind_typs xs Ms) in He;
    auto.
  auto using valid_env_aux_bind_typs.
Qed.

Lemma valid_env_bind_typs : forall chk chk' E xs Ms,
    valid_env chk E ->
    fresh (dom E) (length Ms) xs ->
    valid_schemes chk' E Ms ->
    valid_env chk (E & bind_typs xs Ms).
Proof.
  introv He Hf Hss.
  apply valid_schemes_to_unchecked in Hss.
  fresh_length Hf as Hl.
  destruct He.
  - auto using valid_env_aux_bind_typs_both.
  - rewrite Hl in Hf.
    auto using environment_bind_typs with valid_schemes_regular.
Qed.

(* *************************************************************** *)
(** Checked kindings from any kindings and a checked environment *)

Lemma combined_kinding_to_checked :
     (forall chk E K,
      valid_kind chk E K ->
      chk = false ->
      valid_env true E ->
      valid_kind true E K)
  /\ (forall chk E T K,
      kinding chk E T K ->
      chk = false ->
      valid_env true E ->
      kinding true E T K)
  /\ (forall chk E Ks,
      valid_kinds chk E Ks ->
      chk = false ->
      valid_env true E ->
      valid_kinds true E Ks)
  /\ (forall chk E Ks T,
      valid_kinds_and_type chk E Ks T ->
      chk = false ->
      valid_env true E ->
      valid_kinds_and_type true E Ks T)
  /\ (forall chk E Ms,
      valid_scheme chk E Ms ->
      chk = false ->
      valid_env true E ->
      valid_scheme true E Ms)
  /\ (forall E G,
      valid_env_aux E G ->
      valid_env_aux E G)
  /\ (forall chk E,
      valid_env chk E ->
      chk = false ->
      valid_env true E ->
      valid_env true E)
  /\ (forall chk E T1 T2 K,
      type_equal_core chk E T1 T2 K ->
      chk = false ->
      valid_env true E ->
      type_equal_core true E T1 T2 K)
  /\ (forall chk E T1 T2 K,
      type_equal_symm chk E T1 T2 K ->
      chk = false ->
      valid_env true E ->
      type_equal_symm true E T1 T2 K)
  /\ (forall chk E T1 T2 K,
      type_equal_cong chk E T1 T2 K ->
      chk = false ->
      valid_env true E ->
      type_equal_cong true E T1 T2 K)
  /\ (forall chk E T1 T2 K,
      type_equal chk E T1 T2 K ->
      chk = false ->
      valid_env true E ->
      type_equal true E T1 T2 K)
  /\ (forall chk E T1 T2 cs,
      subtype chk E T1 T2 cs ->
      chk = false ->
      valid_env true E ->
      subtype true E T1 T2 cs).
Proof.
  apply combined_kinding_mutind; intros;
    econstr eauto with valid_env_aux_regular.
  - apply_fresh valid_scheme_c as Xs; auto.
    assert (valid_kinds chk (E & Xs ~::* M)
             (knd_open_vars_list (sch_kinds M) Xs)) as Hks
      by eauto using valid_kinds_and_type_inv_kinds.
    replace chk with false in Hks.
    eauto using valid_env_bind_sch_kinds.
  - auto.
Qed.

Lemma valid_kind_to_checked : forall chk E K,
    valid_kind chk E K ->
    valid_env true E ->
    valid_kind true E K.
Proof.
  introv Hv He.
  apply valid_kind_to_unchecked in Hv.
  pose combined_kinding_to_checked.
  intuition eauto.
Qed.

Lemma kinding_to_checked : forall chk E T K,
    kinding chk E T K ->
    valid_env true E ->
    kinding true E T K.
Proof.
  introv Hk He.
  apply kinding_to_unchecked in Hk.
  pose combined_kinding_to_checked.
  intuition eauto.
Qed.

Lemma valid_kinds_to_checked : forall chk E Ks,
    valid_kinds chk E Ks ->
    valid_env true E ->
    valid_kinds true E Ks.
Proof.
  introv Hv He.
  apply valid_kinds_to_unchecked in Hv.
  pose combined_kinding_to_checked.
  intuition eauto.
Qed.

Lemma valid_kinds_and_type_to_checked : forall chk E Ks T,
    valid_kinds_and_type chk E Ks T ->
    valid_env true E ->
    valid_kinds_and_type true E Ks T.
Proof.
  introv Hv He.
  apply valid_kinds_and_type_to_unchecked in Hv.
  pose combined_kinding_to_checked.
  intuition eauto.
Qed.

Lemma valid_scheme_to_checked : forall chk E Ms,
    valid_scheme chk E Ms ->
    valid_env true E ->
    valid_scheme true E Ms.
Proof.
  introv Hv He.
  apply valid_scheme_to_unchecked in Hv.
  pose combined_kinding_to_checked.
  intuition eauto.
Qed.

Lemma type_equal_core_to_checked : forall chk E T1 T2 K,
    type_equal_core chk E T1 T2 K ->
    valid_env true E ->
    type_equal_core true E T1 T2 K.
Proof.
  introv Hte He.
  apply type_equal_core_to_unchecked in Hte.
  pose combined_kinding_to_checked.
  intuition eauto.
Qed.

Lemma type_equal_symm_to_checked : forall chk E T1 T2 K,
    type_equal_symm chk E T1 T2 K ->
    valid_env true E ->
    type_equal_symm true E T1 T2 K.
Proof.
  introv Hte He.
  apply type_equal_symm_to_unchecked in Hte.
  pose combined_kinding_to_checked.
  intuition eauto.
Qed.

Lemma type_equal_cong_to_checked : forall chk E T1 T2 K,
    type_equal_cong chk E T1 T2 K ->
    valid_env true E ->
    type_equal_cong true E T1 T2 K.
Proof.
  introv Hte He.
  apply type_equal_cong_to_unchecked in Hte.
  pose combined_kinding_to_checked.
  intuition eauto.
Qed.

Lemma type_equal_to_checked : forall chk E T1 T2 K,
    type_equal chk E T1 T2 K ->
    valid_env true E ->
    type_equal true E T1 T2 K.
Proof.
  introv Hte He.
  apply type_equal_to_unchecked in Hte.
  pose combined_kinding_to_checked.
  intuition eauto.
Qed.

Lemma subtype_to_checked : forall chk E T1 T2 cs,
    subtype chk E T1 T2 cs ->
    valid_env true E ->
    subtype true E T1 T2 cs.
Proof.
  introv Hs He.
  apply subtype_to_unchecked in Hs.
  pose combined_kinding_to_checked.
  intuition eauto.
Qed.

Lemma kindings_to_checked : forall chk E Ts Ks,
    kindings chk E Ts Ks ->
    valid_env true E ->
    kindings true E Ts Ks.
Proof.
  introv Hks.
  induction Hks; subst;
    eauto using kinding_to_checked.
Qed.

Lemma valid_schemes_to_checked : forall chk E Ms,
    valid_schemes chk E Ms ->
    valid_env true E ->
    valid_schemes true E Ms.
Proof.
  introv Hss.
  induction Hss; subst;
    eauto using valid_scheme_to_checked.
Qed.

(* *************************************************************** *)
(** * Valid bindings *)

Lemma valid_scheme_unchecked_from_env : forall E x M,
    valid_env true E ->
    binds x (bind_typ M) E ->
    valid_scheme false E M.
Proof.
  introv He Hb.
  remember true as chk.
  remember E as F.
  destruct He as [F He|]; try discriminate.
  rewrite HeqF in He at 1.
  rewrite HeqF.
  apply regular_valid_env_aux in He.
  clear HeqF Heqchk.
  induction He.
  - apply binds_empty_inv in Hb; contradiction.
  - destruct (binds_push_inv Hb) as [[? ?]|[Hx Hbnd]];
      try discriminate; auto.
  - destruct (binds_push_inv Hb) as [[Hx Hbnd]|[Hx Hbnd]];
      inversion Hbnd; subst; auto.
Qed.

Lemma valid_scheme_from_env : forall E x M,
    valid_env true E ->
    binds x (bind_typ M) E ->
    valid_scheme true E M.
Proof.
  introv Hv Hb.
  eauto using valid_scheme_to_checked,
    valid_scheme_unchecked_from_env.
Qed.

Lemma valid_kind_unchecked_from_env : forall E X K,
    valid_env true E ->
    binds X (bind_knd K) E ->
    valid_kind false E K.
Proof.
  introv He Hb.
  remember true as chk.
  remember E as F.
  destruct He as [F He|]; try discriminate.
  rewrite HeqF in He at 1.
  rewrite HeqF.
  apply regular_valid_env_aux in He.
  clear HeqF Heqchk.
  induction He.
  - apply binds_empty_inv in Hb; contradiction.
  - destruct (binds_push_inv Hb) as [[Hx Hbnd]|[Hx Hbnd]];
      inversion Hbnd; subst; auto.
  - destruct (binds_push_inv Hb) as [[? ?]|[Hx Hbnd]];
      try discriminate; auto.
Qed.

Lemma valid_kind_from_env : forall E X K,
    valid_env true E ->
    binds X (bind_knd K) E ->
    valid_kind true E K.
Proof.
  introv Hv Hb.
  eauto using valid_kind_to_checked,
    valid_kind_unchecked_from_env.
Qed.

Lemma kinding_from_store_type : forall E l T P,
    valid_store_type E P ->
    binds l T P ->
    kinding true E T knd_type.
Proof.
  introv Hs Hb.
  induction Hs.
  - apply binds_empty_inv in Hb; contradiction.
  - destruct (binds_push_inv Hb) as [[Hx Hbnd]|[Hx Hbnd]];
      subst; auto.
Qed.    

(* *************************************************************** *)
(** Can remove type bindings *)

Lemma combined_kinding_remove_typ_bind :
     (forall chk EXF K,
      valid_kind chk EXF K ->
      (forall E F x M,
          EXF = E & x ~: M & F ->
          valid_kind chk (E & F) K))
  /\ (forall chk EXF T K,
      kinding chk EXF T K ->
      (forall E F x M,
          EXF = E & x ~: M & F ->
          kinding chk (E & F) T K))
  /\ (forall chk EXF Ks,
      valid_kinds chk EXF Ks ->
      (forall E F x M,
          EXF = E & x ~: M & F ->
          valid_kinds chk (E & F) Ks))
  /\ (forall chk EXF Ks T,
      valid_kinds_and_type chk EXF Ks T ->
      (forall E F x M,
          EXF = E & x ~: M & F ->
          valid_kinds_and_type chk (E & F) Ks T))
  /\ (forall chk EXF Ms,
      valid_scheme chk EXF Ms ->
      (forall E F x M,
          EXF = E & x ~: M & F ->
          valid_scheme chk (E & F) Ms))
  /\ (forall EXF G,
      valid_env_aux EXF G ->
      (forall E F x M,
          EXF = E & x ~: M & F ->
          valid_env_aux (E & F) G))
  /\ (forall chk EXF,
      valid_env chk EXF ->
      (forall E F x M,
          EXF = E & x ~: M & F ->
          valid_env chk (E & F)))
  /\ (forall chk EXF T1 T2 K,
      type_equal_core chk EXF T1 T2 K ->
      (forall E F x M,
          EXF = E & x ~: M & F ->
          type_equal_core chk (E & F) T1 T2 K))
  /\ (forall chk EXF T1 T2 K,
      type_equal_symm chk EXF T1 T2 K ->
      (forall E F x M,
          EXF = E & x ~: M & F ->
          type_equal_symm chk (E & F) T1 T2 K))
  /\ (forall chk EXF T1 T2 K,
      type_equal_cong chk EXF T1 T2 K ->
      (forall E F x M,
          EXF = E & x ~: M & F ->
          type_equal_cong chk (E & F) T1 T2 K))
  /\ (forall chk EXF T1 T2 K,
      type_equal chk EXF T1 T2 K ->
      (forall E F x M,
          EXF = E & x ~: M & F ->
          type_equal chk (E & F) T1 T2 K))
  /\ (forall chk EXF T1 T2 cs,
      subtype chk EXF T1 T2 cs ->
      (forall E F x M,
          EXF = E & x ~: M & F ->
          subtype chk (E & F) T1 T2 cs)).
Proof.
  apply combined_kinding_mutind; intros; subst; simpl; econstr eauto.
  - assert (binds X (bind_knd K) (E0 & x ~: M & F)) as Hb
      by assumption.
    destruct (binds_middle_inv Hb) as [? | [[? [? ?]] | [? [? ?]]]];
      try discriminate; eauto.
  - apply valid_scheme_c with (L := L); eauto.
    introv Hf.
    rewrite <- concat_assoc.
    eauto using concat_assoc.
  - eauto using environment_middle_inv_env.
  - eauto using valid_env_aux_middle_inv_env.
  - eauto using environment_middle_inv_env.
Qed.
    
Lemma valid_kind_remove_typ_bind : forall chk E F x M K,
    valid_kind chk (E & x ~: M & F) K ->
    valid_kind chk (E & F) K.
Proof.
  introv Hv.
  pose combined_kinding_remove_typ_bind.
  intuition eauto.
Qed.

Lemma valid_kind_remove_typ_bind_l : forall chk E x M K,
    valid_kind chk (E & x ~: M) K ->
    valid_kind chk E K.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using valid_kind_remove_typ_bind.
Qed.

Lemma kinding_remove_typ_bind : forall chk E F x M T K,
    kinding chk (E & x ~: M & F) T K ->
    kinding chk (E & F) T K.
Proof.
  introv Hk.
  pose combined_kinding_remove_typ_bind.
  intuition eauto.
Qed.

Lemma kinding_remove_typ_bind_l : forall chk E x M T K,
    kinding chk (E & x ~: M) T K ->
    kinding chk E T K.
Proof.
  introv Hk.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Hk.
  rewrite <- concat_empty_r with (E := E).
  eauto using kinding_remove_typ_bind.
Qed.

Lemma valid_kinds_remove_typ_bind : forall chk E F x M Ks,
    valid_kinds chk (E & x ~: M & F) Ks ->
    valid_kinds chk (E & F) Ks.
Proof.
  introv Hv.
  pose combined_kinding_remove_typ_bind.
  intuition eauto.
Qed.

Lemma valid_kinds_remove_typ_bind_l : forall chk E x M Ks,
    valid_kinds chk (E & x ~: M) Ks ->
    valid_kinds chk E Ks.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using valid_kinds_remove_typ_bind.
Qed.

Lemma valid_kinds_and_type_remove_typ_bind : forall chk E F x M Ks T,
    valid_kinds_and_type chk (E & x ~: M & F) Ks T ->
    valid_kinds_and_type chk (E & F) Ks T.
Proof.
  introv Hv.
  pose combined_kinding_remove_typ_bind.
  intuition eauto.
Qed.

Lemma valid_kinds_and_type_remove_typ_bind_l : forall chk E x M Ks T,
    valid_kinds_and_type chk (E & x ~: M) Ks T ->
    valid_kinds_and_type chk E Ks T.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using valid_kinds_and_type_remove_typ_bind.
Qed.

Lemma valid_scheme_remove_typ_bind : forall chk E F x M Ms,
    valid_scheme chk (E & x ~: M & F) Ms ->
    valid_scheme chk (E & F) Ms.
Proof.
  introv Hv.
  pose combined_kinding_remove_typ_bind.
  intuition eauto.
Qed.

Lemma valid_scheme_remove_typ_bind_l : forall chk E x M Ms,
    valid_scheme chk (E & x ~: M) Ms ->
    valid_scheme chk E Ms.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using valid_scheme_remove_typ_bind.
Qed.

Lemma valid_env_aux_remove_typ_bind : forall E F x M G,
    valid_env_aux (E & x ~: M & F) G ->
    valid_env_aux (E & F) G.
Proof.
  introv Hv.
  pose combined_kinding_remove_typ_bind.
  intuition eauto.
Qed.

Lemma valid_env_aux_remove_typ_bind_l : forall E x M G,
    valid_env_aux (E & x ~: M) G ->
    valid_env_aux E G.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using valid_env_aux_remove_typ_bind.
Qed.

Lemma valid_env_remove_typ_bind : forall chk E F x M,
    valid_env chk (E & x ~: M & F) ->
    valid_env chk (E & F).
Proof.
  introv Hv.
  pose combined_kinding_remove_typ_bind.
  intuition eauto.
Qed.

Lemma valid_env_remove_typ_bind_l : forall chk E x M,
    valid_env chk (E & x ~: M) ->
    valid_env chk E.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using valid_env_remove_typ_bind.
Qed.

Lemma type_equal_core_remove_typ_bind : forall chk E F x M T1 T2 K,
    type_equal_core chk (E & x ~: M & F) T1 T2 K ->
    type_equal_core chk (E & F) T1 T2 K.
Proof.
  introv Hte.
  pose combined_kinding_remove_typ_bind.
  intuition eauto.
Qed.

Lemma type_equal_core_remove_typ_bind_l : forall chk E x M T1 T2 K,
    type_equal_core chk (E & x ~: M) T1 T2 K ->
    type_equal_core chk E T1 T2 K.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using type_equal_core_remove_typ_bind.
Qed.

Lemma type_equal_symm_remove_typ_bind : forall chk E F x M T1 T2 K,
    type_equal_symm chk (E & x ~: M & F) T1 T2 K ->
    type_equal_symm chk (E & F) T1 T2 K.
Proof.
  introv Hte.
  pose combined_kinding_remove_typ_bind.
  intuition eauto.
Qed.

Lemma type_equal_symm_remove_typ_bind_l : forall chk E x M T1 T2 K,
    type_equal_symm chk (E & x ~: M) T1 T2 K ->
    type_equal_symm chk E T1 T2 K.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using type_equal_symm_remove_typ_bind.
Qed.

Lemma type_equal_cong_remove_typ_bind : forall chk E F x M T1 T2 K,
    type_equal_cong chk (E & x ~: M & F) T1 T2 K ->
    type_equal_cong chk (E & F) T1 T2 K.
Proof.
  introv Hte.
  pose combined_kinding_remove_typ_bind.
  intuition eauto.
Qed.

Lemma type_equal_cong_remove_typ_bind_l : forall chk E x M T1 T2 K,
    type_equal_cong chk (E & x ~: M) T1 T2 K ->
    type_equal_cong chk E T1 T2 K.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using type_equal_cong_remove_typ_bind.
Qed.

Lemma type_equal_remove_typ_bind : forall chk E F x M T1 T2 K,
    type_equal chk (E & x ~: M & F) T1 T2 K ->
    type_equal chk (E & F) T1 T2 K.
Proof.
  introv Hte.
  pose combined_kinding_remove_typ_bind.
  intuition eauto.
Qed.

Lemma type_equal_remove_typ_bind_l : forall chk E x M T1 T2 K,
    type_equal chk (E & x ~: M) T1 T2 K ->
    type_equal chk E T1 T2 K.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using type_equal_remove_typ_bind.
Qed.

Lemma subtype_remove_typ_bind : forall chk E F x M T1 T2 cs,
    subtype chk (E & x ~: M & F) T1 T2 cs ->
    subtype chk (E & F) T1 T2 cs.
Proof.
  introv Hs.
  pose combined_kinding_remove_typ_bind.
  intuition eauto.
Qed.

Lemma subtype_remove_typ_bind_l : forall chk E x M T1 T2 cs,
    subtype chk (E & x ~: M) T1 T2 cs ->
    subtype chk E T1 T2 cs.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using subtype_remove_typ_bind.
Qed.

Lemma kindings_remove_typ_bind : forall chk E F x M Ts Ks,
    kindings chk (E & x ~: M & F) Ts Ks ->
    kindings chk (E & F) Ts Ks.
Proof.
  introv Hks.
  remember (E & x ~: M & F) as ExF.
  induction Hks; subst;
    eauto using valid_env_remove_typ_bind, kinding_remove_typ_bind.
Qed.

Lemma kindings_remove_typ_bind_l : forall chk E x M Ts Ks,
    kindings chk (E & x ~: M) Ts Ks ->
    kindings chk E Ts Ks.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using kindings_remove_typ_bind.
Qed.

Lemma valid_schemes_remove_typ_bind : forall chk E F x M Ms,
    valid_schemes chk (E & x ~: M & F) Ms ->
    valid_schemes chk (E & F) Ms.
Proof.
  introv Hss.
  remember (E & x ~: M & F) as ExF.
  induction Hss; subst;
    eauto using valid_env_remove_typ_bind,
      valid_scheme_remove_typ_bind.
Qed.

Lemma valid_schemes_remove_typ_bind_l : forall chk E x M Ms,
    valid_schemes chk (E & x ~: M) Ms ->
    valid_schemes chk E Ms.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using valid_schemes_remove_typ_bind.
Qed.

Lemma valid_instance_remove_typ_bind : forall E F x M1 Ts M2,
    valid_instance (E & x ~: M1 & F) Ts M2 ->
    valid_instance (E & F) Ts M2.
Proof.
  introv Hv.
  remember (E & x ~: M1 & F) as ExF.
  remember (E & F) as EF.
  destruct Hv; subst;
    eauto using kinding_remove_typ_bind, kindings_remove_typ_bind.
Qed.

Lemma valid_instance_remove_typ_bind_l : forall E x M1 Ts M2,
    valid_instance (E & x ~: M1) Ts M2 ->
    valid_instance E Ts M2.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & x ~: M1) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using valid_instance_remove_typ_bind.
Qed.

Lemma valid_store_type_remove_typ_bind : forall E F x M P,
    valid_store_type (E & x ~: M & F) P ->
    valid_store_type (E & F) P.
Proof.
  introv Hs.
  remember (E & x ~: M & F) as ExF.
  remember (E & F) as EF.
  induction Hs; subst;
    eauto using valid_env_remove_typ_bind, kinding_remove_typ_bind.
Qed.

Lemma valid_store_type_remove_typ_bind_l : forall E x M P,
    valid_store_type (E & x ~: M) P ->
    valid_store_type E P.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using valid_store_type_remove_typ_bind.
Qed.

(* *************************************************************** *)
(** Can add type bindings *)

Lemma combined_kinding_add_typ_bind :
     (forall chk EF K,
      valid_kind chk EF K ->
      (forall chk' E F x M,
          EF = E & F ->
          valid_scheme chk' E M ->
          x # E & F ->
          valid_kind chk (E & x ~: M & F) K))
  /\ (forall chk EF T K,
      kinding chk EF T K ->
      (forall chk' E F x M,
          EF = E & F ->
          valid_scheme chk' E M ->
          x # E & F ->
          kinding chk (E & x ~: M & F) T K))
  /\ (forall chk EF Ks,
      valid_kinds chk EF Ks ->
      (forall chk' E F x M,
          EF = E & F ->
          valid_scheme chk' E M ->
          x # E & F ->
          valid_kinds chk (E & x ~: M & F) Ks))
  /\ (forall chk EF Ks T,
      valid_kinds_and_type chk EF Ks T ->
      (forall chk' E F x M,
          EF = E & F ->
          valid_scheme chk' E M ->
          x # E & F ->
          valid_kinds_and_type chk (E & x ~: M & F) Ks T))
  /\ (forall chk EF Ms,
      valid_scheme chk EF Ms ->
      (forall chk' E F x M,
          EF = E & F ->
          valid_scheme chk' E M ->
          x # E & F ->
          valid_scheme chk (E & x ~: M & F) Ms))
  /\ (forall EF G,
      valid_env_aux EF G ->
      (forall chk' E F x M,
          EF = E & F ->
          valid_scheme chk' E M ->
          x # E & F ->
          valid_env_aux (E & x ~: M & F) G))
  /\ (forall chk EF,
      valid_env chk EF ->
      (forall chk' E F x M,
          EF = E & F ->
          valid_scheme chk' E M ->
          x # E & F ->
          valid_env chk (E & x ~: M & F)))
  /\ (forall chk EF T1 T2 K,
      type_equal_core chk EF T1 T2 K ->
      (forall chk' E F x M,
          EF = E & F ->
          valid_scheme chk' E M ->
          x # E & F ->
          type_equal_core chk (E & x ~: M & F) T1 T2 K))
  /\ (forall chk EF T1 T2 K,
      type_equal_symm chk EF T1 T2 K ->
      (forall chk' E F x M,
          EF = E & F ->
          valid_scheme chk' E M ->
          x # E & F ->
          type_equal_symm chk (E & x ~: M & F) T1 T2 K))
  /\ (forall chk EF T1 T2 K,
      type_equal_cong chk EF T1 T2 K ->
      (forall chk' E F x M,
          EF = E & F ->
          valid_scheme chk' E M ->
          x # E & F ->
          type_equal_cong chk (E & x ~: M & F) T1 T2 K))
  /\ (forall chk EF T1 T2 K,
      type_equal chk EF T1 T2 K ->
      (forall chk' E F x M,
          EF = E & F ->
          valid_scheme chk' E M ->
          x # E & F ->
          type_equal chk (E & x ~: M & F) T1 T2 K))
  /\ (forall chk EF T1 T2 cs,
      subtype chk EF T1 T2 cs ->
      (forall chk' E F x M,
          EF = E & F ->
          valid_scheme chk' E M ->
          x # E & F ->
          subtype chk (E & x ~: M & F) T1 T2 cs)).
Proof.
  apply combined_kinding_mutind; intros; subst; simpl;
    econstr eauto.
  - assert (valid_env chk (E0 & x ~: M & F)) by eauto.
    auto using binds_weakening with valid_env_regular.
  - apply valid_scheme_c with (L := L \u \{x}); eauto.
    introv Hf.
    fresh_length Hf as Hl.
    rewrite <- concat_assoc.
    assert (x # E0 & (F & Xs ~::* M)) by
      (autorewrite with rew_env_dom in *;
       eauto using fresh_single_notin).
    eauto using concat_assoc.
  - auto using environment_middle_typ with valid_scheme_regular.
  - assert (valid_scheme false E0 M) as Hs
      by eauto using valid_scheme_to_unchecked.
    apply valid_scheme_weakening_l
      with (F := x ~: M & F) in Hs;
      autorewrite with rew_env_concat;
      auto using environment_middle_typ
        with valid_scheme_regular valid_env_aux_regular.
    rewrite concat_assoc in Hs.
    eauto using valid_env_aux_middle_typ.
  - auto using environment_middle_typ with valid_scheme_regular.
Qed.      

Lemma valid_kind_add_typ_bind : forall chk E F x M K,
    valid_kind chk (E & F) K ->
    valid_scheme chk E M ->
    x # E & F ->
    valid_kind chk (E & x ~: M & F) K.
Proof.
  introv Hv Hs Hn.
  pose combined_kinding_add_typ_bind.
  intuition eauto.
Qed.

Lemma valid_kind_add_typ_bind_l : forall chk E x M K,
    valid_kind chk E K ->
    valid_scheme chk E M ->
    x # E ->
    valid_kind chk (E & x ~: M) K.
Proof.
  introv Hv Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M).
  rewrite <- concat_empty_r with (E := E) in Hv.
  eauto using valid_kind_add_typ_bind.
Qed.

Lemma kinding_add_typ_bind : forall chk E F x M T K,
    kinding chk (E & F) T K ->
    valid_scheme chk E M ->
    x # E & F ->
    kinding chk (E & x ~: M & F) T K.
Proof.
  introv Hk Hs Hn.
  pose combined_kinding_add_typ_bind.
  intuition eauto.
Qed.

Lemma kinding_add_typ_bind_l : forall chk E x M T K,
    kinding chk E T K ->
    valid_scheme chk E M ->
    x # E ->
    kinding chk (E & x ~: M) T K.
Proof.
  introv Hk Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M).
  rewrite <- concat_empty_r with (E := E) in Hk.
  eauto using kinding_add_typ_bind.
Qed.

Lemma valid_kinds_add_typ_bind : forall chk E F x M Ks,
    valid_kinds chk (E & F) Ks ->
    valid_scheme chk E M ->
    x # E & F ->
    valid_kinds chk (E & x ~: M & F) Ks.
Proof.
  introv Hks Hs Hn.
  pose combined_kinding_add_typ_bind.
  intuition eauto.
Qed.

Lemma valid_kinds_add_typ_bind_l : forall chk E x M Ks,
    valid_kinds chk E Ks ->
    valid_scheme chk E M ->
    x # E ->
    valid_kinds chk (E & x ~: M) Ks.
Proof.
  introv Hks Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M).
  rewrite <- concat_empty_r with (E := E) in Hks.
  eauto using valid_kinds_add_typ_bind.
Qed.

Lemma valid_kinds_and_type_add_typ_bind : forall chk E F x M Ks T,
    valid_kinds_and_type chk (E & F) Ks T ->
    valid_scheme chk E M ->
    x # E & F ->
    valid_kinds_and_type chk (E & x ~: M & F) Ks T.
Proof.
  introv Hks Hs Hn.
  pose combined_kinding_add_typ_bind.
  intuition eauto.
Qed.

Lemma valid_kinds_and_type_add_typ_bind_l : forall chk E x M Ks T,
    valid_kinds_and_type chk E Ks T ->
    valid_scheme chk E M ->
    x # E ->
    valid_kinds_and_type chk (E & x ~: M) Ks T.
Proof.
  introv Hks Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M).
  rewrite <- concat_empty_r with (E := E) in Hks.
  eauto using valid_kinds_and_type_add_typ_bind.
Qed.

Lemma valid_scheme_add_typ_bind : forall chk E F x M Ms,
    valid_scheme chk (E & F) Ms ->
    valid_scheme chk E M ->
    x # E & F ->
    valid_scheme chk (E & x ~: M & F) Ms.
Proof.
  introv Hk Hs Hn.
  pose combined_kinding_add_typ_bind.
  intuition eauto.
Qed.

Lemma valid_scheme_add_typ_bind_l : forall chk E x M Ms,
    valid_scheme chk E Ms ->
    valid_scheme chk E M ->
    x # E ->
    valid_scheme chk (E & x ~: M) Ms.
Proof.
  introv Hv Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M).
  rewrite <- concat_empty_r with (E := E) in Hv.
  eauto using valid_scheme_add_typ_bind.
Qed.

Lemma valid_env_aux_add_typ_bind : forall chk E F G x M,
    valid_env_aux (E & F) G ->
    valid_scheme chk E M ->
    x # E & F ->
    valid_env_aux (E & x ~: M & F) G.
Proof.
  introv Hk Hs Hn.
  pose combined_kinding_add_typ_bind.
  intuition eauto.
Qed.

Lemma valid_env_aux_add_typ_bind_l : forall chk E F x M,
    valid_env_aux E F ->
    valid_scheme chk E M ->
    x # E ->
    valid_env_aux (E & x ~: M) F.
Proof.
  introv Hv Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M).
  rewrite <- concat_empty_r with (E := E) in Hv.
  eauto using valid_env_aux_add_typ_bind.
Qed.

Lemma valid_env_add_typ_bind : forall chk E F x M,
    valid_env chk (E & F) ->
    valid_scheme chk E M ->
    x # E & F ->
    valid_env chk (E & x ~: M & F).
Proof.
  introv Hk Hs Hn.
  pose combined_kinding_add_typ_bind.
  intuition eauto.
Qed.

Lemma valid_env_add_typ_bind_l : forall chk E x M,
    valid_env chk E ->
    valid_scheme chk E M ->
    x # E ->
    valid_env chk (E & x ~: M).
Proof.
  introv Hv Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M).
  rewrite <- concat_empty_r with (E := E) in Hv.
  eauto using valid_env_add_typ_bind.
Qed.

Lemma type_equal_core_add_typ_bind : forall chk E F x M T1 T2 K,
    type_equal_core chk (E & F) T1 T2 K ->
    valid_scheme chk E M ->
    x # E & F ->
    type_equal_core chk (E & x ~: M & F) T1 T2 K.
Proof.
  introv Hte Hs Hn.
  pose combined_kinding_add_typ_bind.
  intuition eauto.
Qed.

Lemma type_equal_core_add_typ_bind_l : forall chk E x M T1 T2 K,
    type_equal_core chk E T1 T2 K ->
    valid_scheme chk E M ->
    x # E ->
    type_equal_core chk (E & x ~: M) T1 T2 K.
Proof.
  introv Hv Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M).
  rewrite <- concat_empty_r with (E := E) in Hv.
  eauto using type_equal_core_add_typ_bind.
Qed.

Lemma type_equal_symm_add_typ_bind : forall chk E F x M T1 T2 K,
    type_equal_symm chk (E & F) T1 T2 K ->
    valid_scheme chk E M ->
    x # E & F ->
    type_equal_symm chk (E & x ~: M & F) T1 T2 K.
Proof.
  introv Hte Hs Hn.
  pose combined_kinding_add_typ_bind.
  intuition eauto.
Qed.

Lemma type_equal_symm_add_typ_bind_l : forall chk E x M T1 T2 K,
    type_equal_symm chk E T1 T2 K ->
    valid_scheme chk E M ->
    x # E ->
    type_equal_symm chk (E & x ~: M) T1 T2 K.
Proof.
  introv Hv Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M).
  rewrite <- concat_empty_r with (E := E) in Hv.
  eauto using type_equal_symm_add_typ_bind.
Qed.

Lemma type_equal_cong_add_typ_bind : forall chk E F x M T1 T2 K,
    type_equal_cong chk (E & F) T1 T2 K ->
    valid_scheme chk E M ->
    x # E & F ->
    type_equal_cong chk (E & x ~: M & F) T1 T2 K.
Proof.
  introv Hte Hs Hn.
  pose combined_kinding_add_typ_bind.
  intuition eauto.
Qed.

Lemma type_equal_cong_add_typ_bind_l : forall chk E x M T1 T2 K,
    type_equal_cong chk E T1 T2 K ->
    valid_scheme chk E M ->
    x # E ->
    type_equal_cong chk (E & x ~: M) T1 T2 K.
Proof.
  introv Hv Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M).
  rewrite <- concat_empty_r with (E := E) in Hv.
  eauto using type_equal_cong_add_typ_bind.
Qed.

Lemma type_equal_add_typ_bind : forall chk E F x M T1 T2 K,
    type_equal chk (E & F) T1 T2 K ->
    valid_scheme chk E M ->
    x # E & F ->
    type_equal chk (E & x ~: M & F) T1 T2 K.
Proof.
  introv Hte Hs Hn.
  pose combined_kinding_add_typ_bind.
  intuition eauto.
Qed.

Lemma type_equal_add_typ_bind_l : forall chk E x M T1 T2 K,
    type_equal chk E T1 T2 K ->
    valid_scheme chk E M ->
    x # E ->
    type_equal chk (E & x ~: M) T1 T2 K.
Proof.
  introv Hv Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M).
  rewrite <- concat_empty_r with (E := E) in Hv.
  eauto using type_equal_add_typ_bind.
Qed.

Lemma subtype_add_typ_bind : forall chk E F x M T1 T2 cs,
    subtype chk (E & F) T1 T2 cs ->
    valid_scheme chk E M ->
    x # E & F ->
    subtype chk (E & x ~: M & F) T1 T2 cs.
Proof.
  introv Hs Hsc Hn.
  pose combined_kinding_add_typ_bind.
  intuition eauto.
Qed.

Lemma subtype_add_typ_bind_l : forall chk E x M T1 T2 cs,
    subtype chk E T1 T2 cs ->
    valid_scheme chk E M ->
    x # E ->
    subtype chk (E & x ~: M) T1 T2 cs.
Proof.
  introv Hv Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M).
  rewrite <- concat_empty_r with (E := E) in Hv.
  eauto using subtype_add_typ_bind.
Qed.

Lemma kindings_add_typ_bind : forall chk E F x M Ts Ks,
    kindings chk (E & F) Ts Ks ->
    valid_scheme chk E M ->
    x # E & F ->
    kindings chk (E & x ~: M & F) Ts Ks.
Proof.
  introv Hks Hs Hn.
  remember (E & F) as EF.
  induction Hks; subst;
    auto using valid_env_add_typ_bind, kinding_add_typ_bind.
Qed.

Lemma kindings_add_typ_bind_l : forall chk E x M Ts Ks,
    kindings chk E Ts Ks ->
    valid_scheme chk E M ->
    x # E ->
    kindings chk (E & x ~: M) Ts Ks.
Proof.
  introv Hk Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M).
  rewrite <- concat_empty_r with (E := E) in Hk.
  eauto using kindings_add_typ_bind.
Qed.

Lemma valid_schemes_add_typ_bind : forall chk E F x M Ms,
    valid_schemes chk (E & F) Ms ->
    valid_scheme chk E M ->
    x # E & F ->
    valid_schemes chk (E & x ~: M & F) Ms.
Proof.
  introv Hss Hs Hn.
  remember (E & F) as EF.
  induction Hss; subst;
    auto using valid_env_add_typ_bind, valid_scheme_add_typ_bind.
Qed.

Lemma valid_schemes_add_typ_bind_l : forall chk E x M Ms,
    valid_schemes chk E Ms ->
    valid_scheme chk E M ->
    x # E ->
    valid_schemes chk (E & x ~: M) Ms.
Proof.
  introv Hss Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M).
  rewrite <- concat_empty_r with (E := E) in Hss.
  eauto using valid_schemes_add_typ_bind.
Qed.

Lemma valid_instance_add_typ_bind : forall E F x M1 Ts M2,
    valid_instance (E & F) Ts M2 ->
    valid_scheme true E M1 ->
    x # E & F ->
    valid_instance (E & x ~: M1 & F) Ts M2.
Proof.
  introv Hv Hs Hn.
  remember (E & F) as EF.
  destruct Hv; subst;
    auto using kinding_add_typ_bind, kindings_add_typ_bind.
Qed.

Lemma valid_instance_add_typ_bind_l : forall E x M1 Ts M2,
    valid_instance E Ts M2 ->
    valid_scheme true E M1 ->
    x # E ->
    valid_instance (E & x ~: M1) Ts M2.
Proof.
  introv Hv Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M1).
  rewrite <- concat_empty_r with (E := E) in Hv.
  eauto using valid_instance_add_typ_bind.
Qed.

Lemma valid_store_type_add_typ_bind : forall E F x M P,
    valid_store_type (E & F) P ->
    valid_scheme true E M ->
    x # E & F ->
    valid_store_type (E & x ~: M & F) P.
Proof.
  introv Hv Hs Hn.
  remember (E & x ~: M & F) as ExF.
  remember (E & F) as EF.
  induction Hv; subst;
    eauto using valid_env_add_typ_bind, kinding_add_typ_bind.
Qed.

Lemma valid_store_type_add_typ_bind_l : forall E x M P,
    valid_store_type E P ->
    valid_scheme true E M ->
    x # E ->
    valid_store_type (E & x ~: M) P.
Proof.
  introv Hv Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M).
  rewrite <- concat_empty_r with (E := E) in Hv.
  eauto using valid_store_type_add_typ_bind.
Qed.

(* *************************************************************** *)
(** Can swap type bindings *)

Lemma valid_kind_swap_typ_bind : forall chk E F x M1 M2 K,
    valid_kind chk (E & x ~: M1 & F) K ->
    valid_scheme chk E M2 ->
    valid_kind chk (E & x ~: M2 & F) K.
Proof.
  introv Hk Hs.
  apply valid_kind_add_typ_bind;
    eauto
      using valid_kind_remove_typ_bind, environment_middle_inv_fresh
       with valid_kind_regular.
Qed.

Lemma kinding_swap_typ_bind : forall chk E F x M1 M2 T K,
    kinding chk (E & x ~: M1 & F) T K ->
    valid_scheme chk E M2 ->
    kinding chk (E & x ~: M2 & F) T K.
Proof.
  introv Hk Hs.
  apply kinding_add_typ_bind;
    eauto
      using kinding_remove_typ_bind, environment_middle_inv_fresh
      with kinding_regular.
Qed.

Lemma valid_scheme_swap_typ_bind : forall chk E F x M1 M2 Ms,
    valid_scheme chk (E & x ~: M1 & F) Ms ->
    valid_scheme chk E M2 ->
    valid_scheme chk (E & x ~: M2 & F) Ms.
Proof.
  introv Hs1 Hs2.
  apply valid_scheme_add_typ_bind;
    eauto
      using valid_scheme_remove_typ_bind, environment_middle_inv_fresh
      with valid_scheme_regular.
Qed.

Lemma valid_env_swap_typ_bind : forall chk E F x M1 M2,
    valid_env chk (E & x ~: M1 & F) ->
    valid_scheme chk E M2 ->
    valid_env chk (E & x ~: M2 & F).
Proof.
  introv He Hs.
  apply valid_env_add_typ_bind;
    eauto
      using valid_env_remove_typ_bind, environment_middle_inv_fresh
      with valid_env_regular.
Qed.  

Lemma type_equal_swap_typ_bind : forall chk E F x M1 M2 T1 T2 K,
    type_equal chk (E & x ~: M1 & F) T1 T2 K ->
    valid_scheme chk E M2 ->
    type_equal chk (E & x ~: M2 & F) T1 T2 K.
Proof.
  introv Hte Hs.
  apply type_equal_add_typ_bind;
    eauto
      using type_equal_remove_typ_bind, environment_middle_inv_fresh
      with type_equal_regular.
Qed.

Lemma subtype_swap_typ_bind : forall chk E F x M1 M2 T1 T2 cs,
    subtype chk (E & x ~: M1 & F) T1 T2 cs ->
    valid_scheme chk E M2 ->
    subtype chk (E & x ~: M2 & F) T1 T2 cs.
Proof.
  introv Hs Hsc.
  apply subtype_add_typ_bind;
    eauto
      using subtype_remove_typ_bind, environment_middle_inv_fresh
      with subtype_regular.
Qed.

Lemma valid_instance_swap_typ_bind : forall E F x M1 M2 Ts M3,
    valid_instance (E & x ~: M1 & F) Ts M3 ->
    valid_scheme true E M2 ->
    valid_instance (E & x ~: M2 & F) Ts M3.
Proof.
  introv Hs Hsc.
  apply valid_instance_add_typ_bind;
    eauto
      using valid_instance_remove_typ_bind,
        environment_middle_inv_fresh
      with valid_instance_regular.
Qed.

Lemma valid_store_type_swap_typ_bind : forall E F x M1 M2 P,
    valid_store_type (E & x ~: M1 & F) P ->
    valid_scheme true E M2 ->
    valid_store_type (E & x ~: M2 & F) P.
Proof.
  introv Hs Hsc.
  apply valid_store_type_add_typ_bind;
    eauto
      using valid_store_type_remove_typ_bind,
        environment_middle_inv_fresh
      with valid_store_type_regular.
Qed.

(* *************************************************************** *)
(** Can remove multiple type bindings *)

Lemma valid_kind_remove_bind_typs : forall chk E F xs Ms K,
    valid_kind chk (E & bind_typs xs Ms & F) K ->
    valid_kind chk (E & F) K.
Proof.
  introv Hv.
  generalize dependent Ms.
  induction xs; introv Hv; destruct Ms; simpl in *;
    autorewrite with rew_env_concat in *; auto.
  apply IHxs with (Ms := Ms).
  rewrite <- concat_assoc.
  apply valid_kind_remove_typ_bind with (x := a) (M := s).
  rewrite concat_assoc.
  auto.
Qed.

Lemma valid_kind_remove_bind_typs_l : forall chk E xs Ms K,
    valid_kind chk (E & bind_typs xs Ms) K ->
    valid_kind chk E K.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & bind_typs xs Ms) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using valid_kind_remove_bind_typs.
Qed.

Lemma kinding_remove_bind_typs : forall chk E F xs Ms T K,
    kinding chk (E & bind_typs xs Ms & F) T K ->
    kinding chk (E & F) T K.
Proof.
  introv Hk.
  generalize dependent Ms.
  induction xs; introv Hk; destruct Ms; simpl in *;
    autorewrite with rew_env_concat in *; auto.
  apply IHxs with (Ms := Ms).
  rewrite <- concat_assoc.
  apply kinding_remove_typ_bind with (x := a) (M := s).
  rewrite concat_assoc.
  auto.
Qed.

Lemma kinding_remove_bind_typs_l : forall chk E xs Ms T K,
    kinding chk (E & bind_typs xs Ms) T K ->
    kinding chk E T K.
Proof.
  introv Hk.
  rewrite <- concat_empty_r with (E := E & bind_typs xs Ms) in Hk.
  rewrite <- concat_empty_r with (E := E).
  eauto using kinding_remove_bind_typs.
Qed.

Lemma valid_kinds_remove_bind_typs : forall chk E F xs Ms Ks,
    valid_kinds chk (E & bind_typs xs Ms & F) Ks ->
    valid_kinds chk (E & F) Ks.
Proof.
  introv Hv.
  generalize dependent Ms.
  induction xs; introv Hv; destruct Ms; simpl in *;
    autorewrite with rew_env_concat in *; auto.
  apply IHxs with (Ms := Ms).
  rewrite <- concat_assoc.
  apply valid_kinds_remove_typ_bind with (x := a) (M := s).
  rewrite concat_assoc.
  auto.
Qed.

Lemma valid_kinds_remove_bind_typs_l : forall chk E xs Ms Ks,
    valid_kinds chk (E & bind_typs xs Ms) Ks ->
    valid_kinds chk E Ks.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & bind_typs xs Ms) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using valid_kinds_remove_bind_typs.
Qed.

Lemma valid_kinds_and_type_remove_bind_typs :
  forall chk E F xs Ms Ks T,
    valid_kinds_and_type chk (E & bind_typs xs Ms & F) Ks T ->
    valid_kinds_and_type chk (E & F) Ks T.
Proof.
  introv Hv.
  generalize dependent Ms.
  induction xs; introv Hv; destruct Ms; simpl in *;
    autorewrite with rew_env_concat in *; auto.
  apply IHxs with (Ms := Ms).
  rewrite <- concat_assoc.
  apply valid_kinds_and_type_remove_typ_bind with (x := a) (M := s).
  rewrite concat_assoc.
  auto.
Qed.

Lemma valid_kinds_and_type_remove_bind_typs_l :
  forall chk E xs Ms Ks T,
    valid_kinds_and_type chk (E & bind_typs xs Ms) Ks T ->
    valid_kinds_and_type chk E Ks T.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & bind_typs xs Ms) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using valid_kinds_and_type_remove_bind_typs.
Qed.

Lemma valid_scheme_remove_bind_typs : forall chk E F xs Ms M,
    valid_scheme chk (E & bind_typs xs Ms & F) M ->
    valid_scheme chk (E & F) M.
Proof.
  introv Hv.
  generalize dependent Ms.
  induction xs; introv Hv; destruct Ms; simpl in *;
    autorewrite with rew_env_concat in *; auto.
  apply IHxs with (Ms := Ms).
  rewrite <- concat_assoc.
  apply valid_scheme_remove_typ_bind with (x := a) (M := s).
  rewrite concat_assoc.
  auto.
Qed.

Lemma valid_scheme_remove_bind_typs_l : forall chk E xs Ms M,
    valid_scheme chk (E & bind_typs xs Ms) M ->
    valid_scheme chk E M.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & bind_typs xs Ms) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using valid_scheme_remove_bind_typs.
Qed.

Lemma valid_env_aux_remove_bind_typs : forall E F xs Ms G,
    valid_env_aux (E & bind_typs xs Ms & F) G ->
    valid_env_aux (E & F) G.
Proof.
  introv Hv.
  generalize dependent Ms.
  induction xs; introv Hv; destruct Ms; simpl in *;
    autorewrite with rew_env_concat in *; auto.
  apply IHxs with (Ms := Ms).
  rewrite <- concat_assoc.
  apply valid_env_aux_remove_typ_bind with (x := a) (M := s).
  rewrite concat_assoc.
  auto.
Qed.

Lemma valid_env_aux_remove_bind_typs_l : forall E xs Ms G,
    valid_env_aux (E & bind_typs xs Ms) G ->
    valid_env_aux E G.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & bind_typs xs Ms) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using valid_env_aux_remove_bind_typs.
Qed.

Lemma valid_env_remove_bind_typs : forall chk E F xs Ms,
    valid_env chk (E & bind_typs xs Ms & F) ->
    valid_env chk (E & F).
Proof.
  introv Hv.
  generalize dependent Ms.
  induction xs; introv Hv; destruct Ms; simpl in *;
    autorewrite with rew_env_concat in *; auto.
  apply IHxs with (Ms := Ms).
  rewrite <- concat_assoc.
  apply valid_env_remove_typ_bind with (x := a) (M := s).
  rewrite concat_assoc.
  auto.
Qed.

Lemma valid_env_remove_bind_typs_l : forall chk E xs Ms,
    valid_env chk (E & bind_typs xs Ms) ->
    valid_env chk E.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & bind_typs xs Ms) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using valid_env_remove_bind_typs.
Qed.

Lemma type_equal_core_remove_bind_typs : forall chk E F xs Ms T1 T2 K,
    type_equal_core chk (E & bind_typs xs Ms & F) T1 T2 K ->
    type_equal_core chk (E & F) T1 T2 K.
Proof.
  introv Hv.
  generalize dependent Ms.
  induction xs; introv Hv; destruct Ms; simpl in *;
    autorewrite with rew_env_concat in *; auto.
  apply IHxs with (Ms := Ms).
  rewrite <- concat_assoc.
  apply type_equal_core_remove_typ_bind with (x := a) (M := s).
  rewrite concat_assoc.
  auto.
Qed.

Lemma type_equal_core_remove_bind_typs_l : forall chk E xs Ms T1 T2 K,
    type_equal_core chk (E & bind_typs xs Ms) T1 T2 K ->
    type_equal_core chk E T1 T2 K.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & bind_typs xs Ms) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using type_equal_core_remove_bind_typs.
Qed.

Lemma type_equal_symm_remove_bind_typs : forall chk E F xs Ms T1 T2 K,
    type_equal_symm chk (E & bind_typs xs Ms & F) T1 T2 K ->
    type_equal_symm chk (E & F) T1 T2 K.
Proof.
  introv Hv.
  generalize dependent Ms.
  induction xs; introv Hv; destruct Ms; simpl in *;
    autorewrite with rew_env_concat in *; auto.
  apply IHxs with (Ms := Ms).
  rewrite <- concat_assoc.
  apply type_equal_symm_remove_typ_bind with (x := a) (M := s).
  rewrite concat_assoc.
  auto.
Qed.

Lemma type_equal_symm_remove_bind_typs_l : forall chk E xs Ms T1 T2 K,
    type_equal_symm chk (E & bind_typs xs Ms) T1 T2 K ->
    type_equal_symm chk E T1 T2 K.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & bind_typs xs Ms) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using type_equal_symm_remove_bind_typs.
Qed.

Lemma type_equal_cong_remove_bind_typs : forall chk E F xs Ms T1 T2 K,
    type_equal_cong chk (E & bind_typs xs Ms & F) T1 T2 K ->
    type_equal_cong chk (E & F) T1 T2 K.
Proof.
  introv Hv.
  generalize dependent Ms.
  induction xs; introv Hv; destruct Ms; simpl in *;
    autorewrite with rew_env_concat in *; auto.
  apply IHxs with (Ms := Ms).
  rewrite <- concat_assoc.
  apply type_equal_cong_remove_typ_bind with (x := a) (M := s).
  rewrite concat_assoc.
  auto.
Qed.

Lemma type_equal_cong_remove_bind_typs_l : forall chk E xs Ms T1 T2 K,
    type_equal_cong chk (E & bind_typs xs Ms) T1 T2 K ->
    type_equal_cong chk E T1 T2 K.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & bind_typs xs Ms) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using type_equal_cong_remove_bind_typs.
Qed.

Lemma type_equal_remove_bind_typs : forall chk E F xs Ms T1 T2 K,
    type_equal chk (E & bind_typs xs Ms & F) T1 T2 K ->
    type_equal chk (E & F) T1 T2 K.
Proof.
  introv Hv.
  generalize dependent Ms.
  induction xs; introv Hv; destruct Ms; simpl in *;
    autorewrite with rew_env_concat in *; auto.
  apply IHxs with (Ms := Ms).
  rewrite <- concat_assoc.
  apply type_equal_remove_typ_bind with (x := a) (M := s).
  rewrite concat_assoc.
  auto.
Qed.

Lemma type_equal_remove_bind_typs_l : forall chk E xs Ms T1 T2 K,
    type_equal chk (E & bind_typs xs Ms) T1 T2 K ->
    type_equal chk E T1 T2 K.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & bind_typs xs Ms) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using type_equal_remove_bind_typs.
Qed.

Lemma subtype_remove_bind_typs : forall chk E F xs Ms T1 T2 cs,
    subtype chk (E & bind_typs xs Ms & F) T1 T2 cs ->
    subtype chk (E & F) T1 T2 cs.
Proof.
  introv Hv.
  generalize dependent Ms.
  induction xs; introv Hv; destruct Ms; simpl in *;
    autorewrite with rew_env_concat in *; auto.
  apply IHxs with (Ms := Ms).
  rewrite <- concat_assoc.
  apply subtype_remove_typ_bind with (x := a) (M := s).
  rewrite concat_assoc.
  auto.
Qed.

Lemma subtype_remove_bind_typs_l : forall chk E xs Ms T1 T2 cs,
    subtype chk (E & bind_typs xs Ms) T1 T2 cs ->
    subtype chk E T1 T2 cs.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & bind_typs xs Ms) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using subtype_remove_bind_typs.
Qed.

Lemma kindings_remove_bind_typs : forall chk E F xs Ms Ts Ks,
    kindings chk (E & bind_typs xs Ms & F) Ts Ks ->
    kindings chk (E & F) Ts Ks.
Proof.
  introv Hks.
  remember (E & bind_typs xs Ms & F) as ExF.
  induction Hks; subst;
    eauto using valid_env_remove_bind_typs, kinding_remove_bind_typs.
Qed.

Lemma kindings_remove_bind_typs_l : forall chk E xs Ms Ts Ks,
    kindings chk (E & bind_typs xs Ms) Ts Ks ->
    kindings chk E Ts Ks.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & bind_typs xs Ms) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using kindings_remove_bind_typs.
Qed.

Lemma valid_schemes_remove_bind_typs : forall chk E F xs Ms Ns,
    valid_schemes chk (E & bind_typs xs Ms & F) Ns ->
    valid_schemes chk (E & F) Ns.
Proof.
  introv Hss.
  remember (E & bind_typs xs Ms & F) as ExF.
  induction Hss; subst;
    eauto using valid_env_remove_bind_typs,
      valid_scheme_remove_bind_typs.
Qed.

Lemma valid_schemes_remove_bind_typs_l : forall chk E xs Ms Ns,
    valid_schemes chk (E & bind_typs xs Ms) Ns ->
    valid_schemes chk E Ns.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & bind_typs xs Ms) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using valid_schemes_remove_bind_typs.
Qed.

Lemma valid_instance_remove_bind_typs : forall E F xs Ms Ts M,
    valid_instance (E & bind_typs xs Ms & F) Ts M ->
    valid_instance (E & F) Ts M.
Proof.
  introv Hv.
  remember (E & bind_typs xs Ms & F) as ExF.
  remember (E & F) as EF.
  destruct Hv; subst;
    eauto using kinding_remove_bind_typs, kindings_remove_bind_typs.
Qed.

Lemma valid_instance_remove_bind_typs_l : forall E xs Ms Ts M,
    valid_instance (E & bind_typs xs Ms) Ts M ->
    valid_instance E Ts M.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & bind_typs xs Ms) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using valid_instance_remove_bind_typs.
Qed.

Lemma valid_store_type_remove_bind_typs : forall E F xs Ms P,
    valid_store_type (E & bind_typs xs Ms & F) P ->
    valid_store_type (E & F) P.
Proof.
  introv Hs.
  remember (E & bind_typs xs Ms & F) as ExF.
  remember (E & F) as EF.
  induction Hs; subst;
    eauto using valid_env_remove_bind_typs, kinding_remove_bind_typs.
Qed.

Lemma valid_store_type_remove_bind_typs_l : forall E xs Ms P,
    valid_store_type (E & bind_typs xs Ms) P ->
    valid_store_type E P.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & bind_typs xs Ms) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using valid_store_type_remove_bind_typs.
Qed.

(* *************************************************************** *)
(** Judegments are closed *)

Lemma combined_kinding_closed :
     (forall chk E K,
      valid_kind_regular chk E K ->
      (forall X,
          X # E ->
          X \notin (knd_fv K)))
  /\ (forall chk E T K,
      kinding_regular chk E T K ->
         (forall X,
          X # E ->
          X \notin (typ_fv T))
      /\ (forall X,
          chk = true ->
          X # E ->
          X \notin (knd_fv K)))
  /\ (forall chk E Ks,
      valid_kinds_regular chk E Ks ->
      (forall X,
          X # E ->
          X \notin (knd_fv_list Ks)))
  /\ (forall chk E Ks T,
      valid_kinds_and_type_regular chk E Ks T ->
         (forall X,
          X # E ->
          X \notin (knd_fv_list Ks))
      /\ (forall X,
          X # E ->
          X \notin (typ_fv T)))
  /\ (forall chk E M,
      valid_scheme_regular chk E M ->
      (forall X,
          X # E ->
          X \notin (sch_fv M)))
  /\ (forall E F,
      valid_env_aux_regular E F ->
      (forall X,
          X # E ->
          X \notin (env_fv F)))
  /\ (forall chk E,
      valid_env_regular chk E ->
      (forall X Y K,
          chk = true ->
          X # E ->
          binds Y (bind_knd K) E ->
          X \notin (knd_fv K)))
  /\ (forall chk E T1 T2 K,
      type_equal_core_regular chk E T1 T2 K ->
         (forall X,
          X # E ->
          X \notin (typ_fv T1))
      /\ (forall X,
          X # E ->
          X \notin (typ_fv T2))
      /\ (forall X,
          chk = true ->
          X # E ->
          X \notin (knd_fv K)))
  /\ (forall chk E T1 T2 K,
      type_equal_symm_regular chk E T1 T2 K ->
         (forall X,
          X # E ->
          X \notin (typ_fv T1))
      /\ (forall X,
          X # E ->
          X \notin (typ_fv T2))
      /\ (forall X,
          chk = true ->
          X # E ->
          X \notin (knd_fv K)))
  /\ (forall chk E T1 T2 K,
      type_equal_cong_regular chk E T1 T2 K ->
         (forall X,
          X # E ->
          X \notin (typ_fv T1))
      /\ (forall X,
          X # E ->
          X \notin (typ_fv T2))
      /\ (forall X,
          chk = true ->
          X # E ->
          X \notin (knd_fv K)))
  /\ (forall chk E T1 T2 K,
      type_equal_regular chk E T1 T2 K ->
         (forall X,
          X # E ->
          X \notin (typ_fv T1))
      /\ (forall X,
          X # E ->
          X \notin (typ_fv T2))
      /\ (forall X,
          chk = true ->
          X # E ->
          X \notin (knd_fv K)))
  /\ (forall chk E T1 T2 cs,
      subtype_regular chk E T1 T2 cs ->
         (forall X,
          X # E ->
          X \notin (typ_fv T1))
      /\ (forall X,
          X # E ->
          X \notin (typ_fv T2))).
Proof.      
  apply combined_kinding_regular_mutind; jauto_set; intros; subst;
    simpl; auto.
  - apply notin_singleton_l.
    intro; subst.
    eauto using get_some_inv, binds_get.
  - eauto.
  - destruct M; unfold bind_sch_kinds in *; simpl in *.
    pick_freshes (length sch_kinds) Xs.
    fresh_length Fr as Hl.
    assert (X # E & bind_knds Xs (knd_open_vars_list sch_kinds Xs))
      by (autorewrite with rew_env_dom;
          try rewrite <- length_knd_open_vars_list; auto).
    assert
      (X \notin knd_fv_list (knd_open_vars_list sch_kinds Xs)) as Hn1
      by (apply H0; auto).
    assert (X \notin typ_fv (typ_open_vars sch_body Xs)) as Hn2
      by (apply H0; auto).
    apply notin_subset with (P := knd_fv_list sch_kinds) in Hn1;
      auto using knd_open_vars_list_fv_inv.
    apply notin_subset with (P := typ_fv sch_body) in Hn2;
      auto using typ_open_vars_fv_inv.
  - autorewrite with rew_env_fv; auto.
  - autorewrite with rew_env_fv; auto.
  - autorewrite with rew_env_fv; auto.
  - replace (knd_fv K) with (bind_fv (bind_knd K)) by auto.
    apply fv_in_values_binds with (x := Y) (E := E); auto.
  - discriminate.
  - assert (X \notin typ_fv (typ_meet T1 T2)) as Hn by auto.
    simpl in Hn.
    auto.
Qed.

Lemma valid_kind_closed : forall chk E K X,
    valid_kind chk E K ->
    X # E ->
    X \notin (knd_fv K).
Proof.
  introv Hk Hn.
  apply regular_valid_kind in Hk.
  pose combined_kinding_closed.
  intuition eauto.
Qed.

Lemma kinding_closed : forall chk E T K X,
    kinding chk E T K ->
    X # E ->
    X \notin (typ_fv T).
Proof.
  introv Hk Hn.
  apply regular_kinding in Hk.
  pose combined_kinding_closed.
  jauto_set.
  assert
    ((forall X : var, X # E -> X \notin typ_fv T)
     /\ (forall X : var, chk = true -> X # E -> X \notin knd_fv K))
    by auto.
  intuition auto.
Qed.

Lemma kinding_checked_closed : forall E T K X,
    kinding true E T K ->
    X # E ->
    X \notin (typ_fv T \u knd_fv K).
Proof.
  introv Hk Hn.
  apply regular_kinding in Hk.
  pose combined_kinding_closed.
  jauto_set.
  assert
    ((forall X : var, X # E -> X \notin typ_fv T)
     /\ (forall X : var, true = true -> X # E -> X \notin knd_fv K))
    by auto.
  intuition auto.
Qed.

Lemma valid_kinds_closed : forall chk E X Ks,
    valid_kinds chk E Ks ->
    X # E ->
    X \notin (knd_fv_list Ks).
Proof.
  introv Hks Hn.
  apply regular_valid_kinds in Hks.
  pose combined_kinding_closed.
  intuition eauto.
Qed.

Lemma valid_kinds_and_type_closed : forall chk E X Ks T,
    valid_kinds_and_type chk E Ks T ->
    X # E ->
    X \notin (knd_fv_list Ks \u typ_fv T).
Proof.
  introv Hks Hn.
  apply regular_valid_kinds_and_type in Hks.
  pose combined_kinding_closed.
  jauto_set.
  assert
    ((forall X : var, X # E -> X \notin knd_fv_list Ks)
     /\ (forall X : var, X # E -> X \notin typ_fv T))
    by eauto.
  intuition eauto.
Qed.

Lemma valid_scheme_closed : forall chk E M X,
    valid_scheme chk E M ->
    X # E ->
    X \notin (sch_fv M).
Proof.
  introv Hs Hn.
  apply regular_valid_scheme in Hs.
  pose combined_kinding_closed.
  intuition eauto.
Qed.

Lemma valid_scheme_closed_list : forall E M Xs,
    valid_scheme true E M ->
    disjoint (from_list Xs) (dom E) ->
    disjoint (from_list Xs) (sch_fv M).
Proof.
  introv Hv Hd.
  induction Xs.
  - rewrite from_list_nil; auto.
  - rewrite from_list_cons in *.
    rewrite disjoint_union_l; split; auto.
    rewrite disjoint_all_in_notin.
    introv Hin.
    rewrite in_singleton in Hin; subst.
    eauto using valid_scheme_closed.
Qed.

Lemma valid_env_aux_closed : forall E X F,
    valid_env_aux E F ->
    X # E ->
    X \notin (env_fv F).
Proof.
  introv He Hn.
  apply regular_valid_env_aux in He.
  pose combined_kinding_closed.
  intuition eauto.
Qed.

Lemma valid_env_closed : forall E X,
    valid_env true E ->
    X # E ->
    X \notin (env_fv E).
Proof.
  introv Hv Hn.
  inversion Hv; subst.
  eauto using valid_env_aux_closed.
Qed.  

Lemma valid_env_closed_list : forall E Xs,
    valid_env true E ->
    disjoint (from_list Xs) (dom E) ->
    disjoint (from_list Xs) (env_fv E).
Proof.
  introv Hv Hd.
  induction Xs.
  - rewrite from_list_nil; auto.
  - rewrite from_list_cons in *.
    rewrite disjoint_union_l; split; auto.
    rewrite disjoint_all_in_notin.
    introv Hin.
    rewrite in_singleton in Hin; subst.
    auto using valid_env_closed.
Qed.
    
Lemma valid_env_binds_knd_closed : forall E X Y K,
    valid_env true E ->
    X # E ->
    binds Y (bind_knd K) E ->
    X \notin (knd_fv K).
Proof.
  introv He Hn.
  apply regular_valid_env in He.
  pose combined_kinding_closed.
  intuition eauto.
Qed.

Lemma valid_env_binds_typ_closed : forall E X x M,
    valid_env true E ->
    X # E ->
    binds x (bind_typ M) E ->
    X \notin (sch_fv M).
Proof.
  introv He Hn Hb.
  remember true as chk.
  destruct He; subst; try discriminate.
  assert (X \notin env_fv E)
    by eauto using valid_env_aux_closed.
  replace (sch_fv M) with (bind_fv (bind_typ M)) by auto.
  apply fv_in_values_binds with (x := x) (E := E); auto.
Qed.

Lemma type_equal_core_closed : forall chk E T1 T2 K X,
    type_equal_core chk E T1 T2 K ->
    X # E ->
    X \notin ((typ_fv T1) \u (typ_fv T2)).
Proof.
  introv Hte Hn.
  apply regular_type_equal_core in Hte.
  pose combined_kinding_closed.
  jauto_set.
  assert
    ((forall X : var, X # E -> X \notin typ_fv T1)
  /\ (forall X : var, X # E -> X \notin typ_fv T2)
  /\ (forall X : var, chk = true -> X # E -> X \notin knd_fv K))
    by auto.
  intuition auto.
Qed.

Lemma type_equal_core_checked_closed : forall E T1 T2 K X,
    type_equal_core true E T1 T2 K ->
    X # E ->
    X \notin ((typ_fv T1) \u (typ_fv T2) \u (knd_fv K)).
Proof.
  introv Hte Hn.
  apply regular_type_equal_core in Hte.
  pose combined_kinding_closed.
  jauto_set.
  assert
    ((forall X : var, X # E -> X \notin typ_fv T1)
  /\ (forall X : var, X # E -> X \notin typ_fv T2)
  /\ (forall X : var, true = true -> X # E -> X \notin knd_fv K))
    by auto.
  intuition auto.
Qed.

Lemma type_equal_symm_closed : forall chk E T1 T2 K X,
    type_equal_symm chk E T1 T2 K ->
    X # E ->
    X \notin ((typ_fv T1) \u (typ_fv T2)).
Proof.
  introv Hte Hn.
  apply regular_type_equal_symm in Hte.
  pose combined_kinding_closed.
  jauto_set.
  assert
    ((forall X : var, X # E -> X \notin typ_fv T1)
  /\ (forall X : var, X # E -> X \notin typ_fv T2)
  /\ (forall X : var, chk = true -> X # E -> X \notin knd_fv K))
    by auto.
  intuition auto.
Qed.

Lemma type_equal_symm_checked_closed : forall E T1 T2 K X,
    type_equal_symm true E T1 T2 K ->
    X # E ->
    X \notin ((typ_fv T1) \u (typ_fv T2) \u (knd_fv K)).
Proof.
  introv Hte Hn.
  apply regular_type_equal_symm in Hte.
  pose combined_kinding_closed.
  jauto_set.
  assert
    ((forall X : var, X # E -> X \notin typ_fv T1)
  /\ (forall X : var, X # E -> X \notin typ_fv T2)
  /\ (forall X : var, true = true -> X # E -> X \notin knd_fv K))
    by auto.
  intuition auto.
Qed.

Lemma type_equal_cong_closed : forall chk E T1 T2 K X,
    type_equal_cong chk E T1 T2 K ->
    X # E ->
    X \notin ((typ_fv T1) \u (typ_fv T2)).
Proof.
  introv Hte Hn.
  apply regular_type_equal_cong in Hte.
  pose combined_kinding_closed.
  jauto_set.
  assert
    ((forall X : var, X # E -> X \notin typ_fv T1)
  /\ (forall X : var, X # E -> X \notin typ_fv T2)
  /\ (forall X : var, chk = true -> X # E -> X \notin knd_fv K))
    by auto.
  intuition auto.
Qed.

Lemma type_equal_cong_checked_closed : forall E T1 T2 K X,
    type_equal_cong true E T1 T2 K ->
    X # E ->
    X \notin ((typ_fv T1) \u (typ_fv T2) \u (knd_fv K)).
Proof.
  introv Hte Hn.
  apply regular_type_equal_cong in Hte.
  pose combined_kinding_closed.
  jauto_set.
  assert
    ((forall X : var, X # E -> X \notin typ_fv T1)
  /\ (forall X : var, X # E -> X \notin typ_fv T2)
  /\ (forall X : var, true = true -> X # E -> X \notin knd_fv K))
    by auto.
  intuition auto.
Qed.

Lemma type_equal_closed : forall chk E T1 T2 K X,
    type_equal chk E T1 T2 K ->
    X # E ->
    X \notin ((typ_fv T1) \u (typ_fv T2)).
Proof.
  introv Hte Hn.
  apply regular_type_equal in Hte.
  pose combined_kinding_closed.
  jauto_set.
  assert
    ((forall X : var, X # E -> X \notin typ_fv T1)
  /\ (forall X : var, X # E -> X \notin typ_fv T2)
  /\ (forall X : var, chk = true -> X # E -> X \notin knd_fv K))
    by auto.
  intuition auto.
Qed.

Lemma type_equal_checked_closed : forall E T1 T2 K X,
    type_equal true E T1 T2 K ->
    X # E ->
    X \notin ((typ_fv T1) \u (typ_fv T2) \u (knd_fv K)).
Proof.
  introv Hte Hn.
  apply regular_type_equal in Hte.
  pose combined_kinding_closed.
  jauto_set.
  assert
    ((forall X : var, X # E -> X \notin typ_fv T1)
  /\ (forall X : var, X # E -> X \notin typ_fv T2)
  /\ (forall X : var, true = true -> X # E -> X \notin knd_fv K))
    by auto.
  intuition auto.
Qed.

Lemma subtype_closed : forall chk E T1 T2 cs X,
    subtype chk E T1 T2 cs ->
    X # E ->
    X \notin ((typ_fv T1) \u (typ_fv T2)).
Proof.
  introv Hs Hn.
  apply regular_subtype in Hs.
  pose combined_kinding_closed.
  jauto_set.
  assert
    ((forall X : var, X # E -> X \notin typ_fv T1)
  /\ (forall X : var, X # E -> X \notin typ_fv T2)) as Hc by eauto.
  intuition auto.
Qed.

Lemma kindings_closed : forall chk E Ts Ks X,
    kindings chk E Ts Ks ->
    X # E ->
    X \notin (typ_fv_list Ts).
Proof.
  introv Hks Hn.
  induction Hks; simpl; auto.
  eauto using kinding_closed.
Qed.

Lemma kindings_checked_closed : forall E Ts Ks X,
    kindings true E Ts Ks ->
    X # E ->
    X \notin (typ_fv_list Ts \u knd_fv_list Ks).
Proof.
  introv Hks Hn.
  remember true as chk.
  induction Hks; subst; simpl; auto.
  assert (X \notin typ_fv_list Ts \u knd_fv_list Ks) by auto.
  assert (X \notin typ_fv T \u knd_fv K)
    by eauto using kinding_checked_closed.
  auto.
Qed.

Lemma valid_schemes_closed : forall chk E Ms X,
    valid_schemes chk E Ms ->
    X # E ->
    X \notin (sch_fv_list Ms).
Proof.
  introv Hss Hn.
  induction Hss; simpl; auto.
  eauto using valid_scheme_closed.
Qed.

Lemma valid_instance_closed : forall E Ts M X,
  valid_instance E Ts M ->
  X # E ->
  X \notin ((typ_fv_list Ts) \u (sch_fv M)).
Proof.
  introv Hi Hn.
  destruct Hi as [E Ts M Hks Hk].
  destruct M; simpl in *.
  apply kindings_checked_closed with (X := X) in Hks; auto.
  apply kinding_checked_closed with (X := X) in Hk; auto.
  assert (X \notin knd_fv_list sch_kinds)
    by (apply notin_subset
         with (Q := knd_fv_list (knd_open_list sch_kinds Ts));
         auto using knd_open_list_fv_inv).
  assert (X \notin typ_fv sch_body)
    by (apply notin_subset
         with (Q := typ_fv (typ_open sch_body Ts));
         auto using typ_open_fv_inv).
  auto.
Qed.

Lemma valid_store_type_closed : forall E P X,
  valid_store_type E P ->
  X # E ->
  X \notin (styp_fv P).
Proof.
  introv Hs Hn.
  induction Hs; autorewrite with rew_styp_fv; auto.
  assert (kinding true E T knd_type) as Hk by assumption.
  apply kinding_closed with (X := X) in Hk; auto.
Qed.

(* *************************************************************** *)
(** Preserved by type substitution *)

Lemma binds_var_trm_subst : forall E F G Xs Ks Ts X Ys Us K,
    environment (E & bind_knds Xs Ks & F) ->
    binds X (bind_knd K) (E & bind_knds Xs Ks & F) ->
    kindings false G Ts (knd_subst_list Ys Us Ks) ->
    kinding false G (typ_var_subst Xs Ts X)
            (knd_subst Ys Us K)
    \/ (binds X (bind_knd K) (E & F)
        /\ typ_var_subst Xs Ts X = typ_fvar X).
Proof.
  introv He Hb Hks.
  assert (length Ts = length (knd_subst_list Ys Us Ks)) as Hl2
    by eauto using kindings_length.
  generalize dependent Ks.
  generalize dependent Ts.
  induction Xs; introv He Hb Hks Hl; destruct Ks; destruct Ts;
    try discriminate; simpl in *;
    autorewrite with rew_env_concat in *; auto.
  inversion Hks; subst.
  case_var.
  - rewrite <- concat_assoc in Hb, He.
    apply binds_middle_eq_inv in Hb; auto using ok_from_environment.
    inversion Hb; subst.
    auto.
  - rewrite <- concat_assoc in Hb, He.    
    apply IHXs with (Ks := Ks) (Ts := Ts); auto.
    + rewrite <- concat_assoc.
      eauto using environment_remove.
    + rewrite <- concat_assoc.
      destruct (binds_middle_inv Hb) as [?|[[? [? ?]]|[? [? ?]]]];
        try contradiction; auto.
Qed.

Lemma combined_kinding_typ_subst :
     (forall chk EXF K,
      valid_kind_regular chk EXF K ->
      (forall E F Xs Js Us,
          EXF = E & bind_knds Xs Js & F ->
          kindings false (env_subst Xs Us (E & F)) Us
            (knd_subst_list Xs Us Js) ->
          valid_kind false (env_subst Xs Us (E & F))
            (knd_subst Xs Us K)))
  /\ (forall chk EXF T K,
      kinding_regular chk EXF T K ->
      (forall E F Xs Js Us,
          EXF = E & bind_knds Xs Js & F ->
          kindings false (env_subst Xs Us (E & F)) Us
            (knd_subst_list Xs Us Js) ->
          kinding false (env_subst Xs Us (E & F))
            (typ_subst Xs Us T) (knd_subst Xs Us K)))
  /\ (forall chk EXF Ks,
      valid_kinds_regular chk EXF Ks ->
      (forall E F Xs Js Us,
          EXF = E & bind_knds Xs Js & F ->
          kindings false (env_subst Xs Us (E & F)) Us
            (knd_subst_list Xs Us Js) ->
          valid_kinds false (env_subst Xs Us (E & F))
            (knd_subst_list Xs Us Ks)))
  /\ (forall chk EXF Ks T,
      valid_kinds_and_type_regular chk EXF Ks T ->
      (forall E F Xs Js Us,
          EXF = E & bind_knds Xs Js & F ->
          kindings false (env_subst Xs Us (E & F)) Us
            (knd_subst_list Xs Us Js) ->
          valid_kinds_and_type false (env_subst Xs Us (E & F))
            (knd_subst_list Xs Us Ks) (typ_subst Xs Us T)))
  /\ (forall chk EXF M,
      valid_scheme_regular chk EXF M ->
      (forall E F Xs Js Us,
          EXF = E & bind_knds Xs Js & F ->
          kindings false (env_subst Xs Us (E & F)) Us
            (knd_subst_list Xs Us Js) ->
          valid_scheme false (env_subst Xs Us (E & F))
            (sch_subst Xs Us M)))
  /\ (forall EXF G,
      valid_env_aux_regular EXF G ->
      (forall E F Xs Js Us,
          EXF = E & bind_knds Xs Js & F ->
          kindings false (env_subst Xs Us (E & F)) Us
            (knd_subst_list Xs Us Js) ->
          valid_env_aux (env_subst Xs Us (E & F))
            (env_subst Xs Us G)))
  /\ (forall chk EXF,
      valid_env_regular chk EXF ->
      (forall E F Xs Js Us,
          EXF = E & bind_knds Xs Js & F ->
          kindings false (env_subst Xs Us (E & F)) Us
            (knd_subst_list Xs Us Js) ->
          valid_env false (env_subst Xs Us (E & F))))
  /\ (forall chk EXF T1 T2 K,
      type_equal_core_regular chk EXF T1 T2 K ->
      (forall E F Xs Js Us,
          EXF = E & bind_knds Xs Js & F ->
          kindings false (env_subst Xs Us (E & F)) Us
            (knd_subst_list Xs Us Js) ->
          type_equal_core false (env_subst Xs Us (E & F))
            (typ_subst Xs Us T1) (typ_subst Xs Us T2)
            (knd_subst Xs Us K)))
  /\ (forall chk EXF T1 T2 K,
      type_equal_symm_regular chk EXF T1 T2 K ->
      (forall E F Xs Js Us,
          EXF = E & bind_knds Xs Js & F ->
          kindings false (env_subst Xs Us (E & F)) Us
            (knd_subst_list Xs Us Js) ->
          type_equal_symm false (env_subst Xs Us (E & F))
            (typ_subst Xs Us T1) (typ_subst Xs Us T2)
            (knd_subst Xs Us K)))
  /\ (forall chk EXF T1 T2 K,
      type_equal_cong_regular chk EXF T1 T2 K ->
      (forall E F Xs Js Us,
          EXF = E & bind_knds Xs Js & F ->
          kindings false (env_subst Xs Us (E & F)) Us
            (knd_subst_list Xs Us Js) ->
          type_equal_cong false (env_subst Xs Us (E & F))
            (typ_subst Xs Us T1) (typ_subst Xs Us T2)
            (knd_subst Xs Us K)))
  /\ (forall chk EXF T1 T2 K,
      type_equal_regular chk EXF T1 T2 K ->
      (forall E F Xs Js Us,
          EXF = E & bind_knds Xs Js & F ->
          kindings false (env_subst Xs Us (E & F)) Us
            (knd_subst_list Xs Us Js) ->
          type_equal false (env_subst Xs Us (E & F))
            (typ_subst Xs Us T1) (typ_subst Xs Us T2)
            (knd_subst Xs Us K)))
  /\ (forall chk EXF T1 T2 cs,
      subtype_regular chk EXF T1 T2 cs ->
      (forall E F Xs Js Us,
          EXF = E & bind_knds Xs Js & F ->
          kindings false (env_subst Xs Us (E & F)) Us
            (knd_subst_list Xs Us Js) ->
          subtype false (env_subst Xs Us (E & F))
            (typ_subst Xs Us T1) (typ_subst Xs Us T2) cs)).
Proof.
  apply combined_kinding_regular_mutind; intros; subst; simpl;
    econstr eauto with kindings_regular.
  - destruct binds_var_trm_subst
      with (E := E0) (F := F) (G := env_subst Xs Us (E0 & F))
           (Xs := Xs) (Ks := Js) (Ts := Us) (X := X) (K := K)
           (Ys := Xs) (Us := Us)
      as [?|[Hb Heq]]; auto.
    rewrite Heq.
    apply kinding_var; eauto using env_subst_binds_knd.
  - apply kinding_range_subsumption
      with (T1 := typ_subst Xs Us T1) (T2 := typ_subst Xs Us T2);
      eauto.
  - apply_fresh valid_scheme_c as Ys; eauto.
    assert (types Us) by auto with kindings_regular.
    assert (fresh L (sch_arity (sch_subst Xs Us M)) Ys) as Hf by auto.
    rewrite sch_subst_arity in Hf.
    assert (valid_kinds_and_type_regular chk
              (E0 & bind_knds Xs Js & F & Ys ~::* M)
              (knd_open_vars_list (sch_kinds M) Ys)
              (typ_open_vars (sch_body M) Ys)) by auto.
    assert (kinds (knd_open_vars_list (sch_kinds M) Ys))
      by eauto with valid_kinds_and_type_regular.
    rewrite <- env_subst_bind_sch_kinds; auto.
    rewrite <- env_subst_concat.
    rewrite <- concat_assoc.
    destruct M; unfold bind_sch_kinds in *; simpl in *.
    rewrite <- knd_subst_list_open_vars; auto.
    rewrite typ_subst_open_vars; auto.
    rewrite <- length_knd_subst_list in FrYs.
    assert
      (environment
         (env_subst Xs Us (E0 & F) &
          bind_knds Ys (knd_subst_list Xs Us
                          (knd_open_vars_list sch_kinds Ys)))) as He
        by (apply environment_bind_knds;
              auto with kindings_regular;
              autorewrite with rew_env_subst rew_env_dom;
              rewrite <- ? length_knd_subst_list;
              rewrite <- ? length_knd_open_vars_list;
              rewrite ? knd_subst_kind_list; auto).
    rewrite <- env_subst_bind_knds in He; auto.
    assert (kindings false (env_subst Xs Us (E0 & F)) Us
              (knd_subst_list Xs Us Js)) as Hks by assumption.
    apply kindings_weakening_l
      with (F := env_subst Xs Us
        (bind_knds Ys (knd_open_vars_list sch_kinds Ys)))
          in Hks; auto.
    rewrite <- env_subst_concat in Hks.
    rewrite <- concat_assoc in Hks.
    eauto using concat_assoc.
  - rewrite env_subst_empty.
    auto with kindings_regular.
  - rewrite env_subst_knd.
    apply valid_env_aux_kind; autorewrite with rew_env_dom; eauto.
  - rewrite env_subst_typ.
    apply valid_env_aux_type; autorewrite with rew_env_dom; eauto.
Qed.

Lemma kindings_valid_env : forall chk E Ts Ks,
    kindings chk E Ts Ks ->
    valid_env chk E.
Proof.
  introv Hks.
  induction Hks; auto.
Qed.

Lemma valid_kind_unchecked_typ_subst : forall chk E F Xs Js Us K,
    valid_kind chk (E & bind_knds Xs Js & F) K ->
    kindings false (env_subst Xs Us (E & F)) Us
      (knd_subst_list Xs Us Js) ->
    valid_kind false (env_subst Xs Us (E & F)) (knd_subst Xs Us K).
Proof.
  introv Hv Hks.
  apply regular_valid_kind in Hv.
  pose combined_kinding_typ_subst.
  intuition eauto.
Qed.

Lemma valid_kind_typ_subst : forall chk E F Xs Js Us K,
    valid_kind chk (E & bind_knds Xs Js & F) K ->
    kindings chk (env_subst Xs Us (E & F)) Us
      (knd_subst_list Xs Us Js) ->
    valid_kind chk (env_subst Xs Us (E & F)) (knd_subst Xs Us K).
Proof.
  introv Hv Hks.
  destruct chk;
    eauto using valid_kind_to_checked, kindings_valid_env,
      kindings_to_unchecked, valid_kind_unchecked_typ_subst.
Qed.
  
Lemma valid_kind_typ_subst_l : forall chk E Xs Js Us K,
    valid_kind chk (E & bind_knds Xs Js) K ->
    kindings chk (env_subst Xs Us E) Us
      (knd_subst_list Xs Us Js) ->
    valid_kind chk (env_subst Xs Us E) (knd_subst Xs Us K).
Proof.
  introv Hv Hks.
  rewrite <- concat_empty_r with (E := E & bind_knds Xs Js) in Hv.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r with (E := E) in Hks.
  eauto using valid_kind_typ_subst.
Qed.

Lemma kinding_unchecked_typ_subst : forall chk E F Xs Js Us T K,
    kinding chk (E & bind_knds Xs Js & F) T K ->
    kindings false (env_subst Xs Us (E & F)) Us
      (knd_subst_list Xs Us Js) ->
    kinding false (env_subst Xs Us (E & F))
      (typ_subst Xs Us T) (knd_subst Xs Us K).
Proof.
  introv Hk Hks.
  apply regular_kinding in Hk.
  pose combined_kinding_typ_subst.
  intuition eauto.
Qed.

Lemma kinding_typ_subst : forall chk E F Xs Js Us T K,
    kinding chk (E & bind_knds Xs Js & F) T K ->
    kindings chk (env_subst Xs Us (E & F)) Us
      (knd_subst_list Xs Us Js) ->
    kinding chk (env_subst Xs Us (E & F))
      (typ_subst Xs Us T) (knd_subst Xs Us K).
Proof.
  introv Hk Hks.
  destruct chk;
    eauto using kinding_to_checked, kindings_valid_env,
      kindings_to_unchecked, kinding_unchecked_typ_subst.
Qed.

Lemma kinding_typ_subst_l : forall chk E Xs Js Us T K,
    kinding chk (E & bind_knds Xs Js) T K ->
    kindings chk (env_subst Xs Us E) Us
      (knd_subst_list Xs Us Js) ->
    kinding chk (env_subst Xs Us E) (typ_subst Xs Us T)
      (knd_subst Xs Us K).
Proof. 
  introv Hk Hks.
  rewrite <- concat_empty_r with (E := E & bind_knds Xs Js) in Hk.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r with (E := E) in Hks.
  eauto using kinding_typ_subst.
Qed.

Lemma valid_kinds_unchecked_typ_subst : forall chk E F Xs Js Us Ks,
    valid_kinds chk (E & bind_knds Xs Js & F) Ks ->
    kindings false (env_subst Xs Us (E & F)) Us
      (knd_subst_list Xs Us Js) ->
    valid_kinds false (env_subst Xs Us (E & F))
      (knd_subst_list Xs Us Ks).
Proof.
  introv Hv Hks.
  apply regular_valid_kinds in Hv.
  pose combined_kinding_typ_subst.
  intuition eauto.
Qed.

Lemma valid_kinds_typ_subst : forall chk E F Xs Js Us Ks,
    valid_kinds chk (E & bind_knds Xs Js & F) Ks ->
    kindings chk (env_subst Xs Us (E & F)) Us
      (knd_subst_list Xs Us Js) ->
    valid_kinds chk (env_subst Xs Us (E & F))
      (knd_subst_list Xs Us Ks).
Proof.
  introv Hv Hks.
  destruct chk;
    eauto using valid_kinds_to_checked, kindings_valid_env,
      kindings_to_unchecked, valid_kinds_unchecked_typ_subst.
Qed.

Lemma valid_kinds_typ_subst_l : forall chk E Xs Js Us Ks,
    valid_kinds chk (E & bind_knds Xs Js) Ks ->
    kindings chk (env_subst Xs Us E) Us
      (knd_subst_list Xs Us Js) ->
    valid_kinds chk (env_subst Xs Us E)
      (knd_subst_list Xs Us Ks).
Proof.
  introv Hv Hks.
  rewrite <- concat_empty_r with (E := E & bind_knds Xs Js) in Hv.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r with (E := E) in Hks.
  eauto using valid_kinds_typ_subst.
Qed.

Lemma valid_kinds_and_type_unchecked_typ_subst :
  forall chk E F Xs Js Us Ks T,
    valid_kinds_and_type chk (E & bind_knds Xs Js & F) Ks T ->
    kindings false (env_subst Xs Us (E & F)) Us
      (knd_subst_list Xs Us Js) ->
    valid_kinds_and_type false (env_subst Xs Us (E & F))
      (knd_subst_list Xs Us Ks) (typ_subst Xs Us T).
Proof.
  introv Hv Hks.
  apply regular_valid_kinds_and_type in Hv.
  pose combined_kinding_typ_subst.
  intuition eauto.
Qed.

Lemma valid_kinds_and_type_typ_subst : forall chk E F Xs Js Us Ks T,
    valid_kinds_and_type chk (E & bind_knds Xs Js & F) Ks T ->
    kindings chk (env_subst Xs Us (E & F)) Us
      (knd_subst_list Xs Us Js) ->
    valid_kinds_and_type chk (env_subst Xs Us (E & F))
      (knd_subst_list Xs Us Ks) (typ_subst Xs Us T).
Proof.
  introv Hv Hks.
  destruct chk;
    eauto using valid_kinds_and_type_to_checked, kindings_valid_env,
      kindings_to_unchecked, valid_kinds_and_type_unchecked_typ_subst.
Qed.

Lemma valid_kinds_and_type_typ_subst_l : forall chk E Xs Js Us Ks T,
    valid_kinds_and_type chk (E & bind_knds Xs Js) Ks T ->
    kindings chk (env_subst Xs Us E) Us
      (knd_subst_list Xs Us Js) ->
    valid_kinds_and_type chk (env_subst Xs Us E)
      (knd_subst_list Xs Us Ks) (typ_subst Xs Us T).
Proof.
  introv Hv Hks.
  rewrite <- concat_empty_r with (E := E & bind_knds Xs Js) in Hv.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r with (E := E) in Hks.
  eauto using valid_kinds_and_type_typ_subst.
Qed.

Lemma valid_scheme_unchecked_typ_subst : forall chk E F Xs Js Us M,
    valid_scheme chk (E & bind_knds Xs Js & F) M ->
    kindings false (env_subst Xs Us (E & F)) Us
      (knd_subst_list Xs Us Js) ->
    valid_scheme false (env_subst Xs Us (E & F)) (sch_subst Xs Us M).
Proof.
  introv Hv Hks.
  apply regular_valid_scheme in Hv.
  pose combined_kinding_typ_subst.
  intuition eauto.
Qed.

Lemma valid_scheme_typ_subst : forall chk E F Xs Js Us M,
    valid_scheme chk (E & bind_knds Xs Js & F) M ->
    kindings chk (env_subst Xs Us (E & F)) Us
      (knd_subst_list Xs Us Js) ->
    valid_scheme chk (env_subst Xs Us (E & F)) (sch_subst Xs Us M).
Proof.
  introv Hv Hks.
  destruct chk;
    eauto using valid_scheme_to_checked, kindings_valid_env,
      kindings_to_unchecked, valid_scheme_unchecked_typ_subst.
Qed.

Lemma valid_scheme_typ_subst_l : forall chk E Xs Js Us M,
    valid_scheme chk (E & bind_knds Xs Js) M ->
    kindings chk (env_subst Xs Us E) Us
      (knd_subst_list Xs Us Js) ->
    valid_scheme chk (env_subst Xs Us E) (sch_subst Xs Us M).
Proof.
  introv Hv Hks.
  rewrite <- concat_empty_r with (E := E & bind_knds Xs Js) in Hv.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r with (E := E) in Hks.
  eauto using valid_scheme_typ_subst.
Qed.

Lemma type_equal_core_unchecked_typ_subst :
  forall chk E F Xs Js Us T1 T2 K,
    type_equal_core chk (E & bind_knds Xs Js & F) T1 T2 K ->
    kindings false (env_subst Xs Us (E & F)) Us
      (knd_subst_list Xs Us Js) ->
    type_equal_core false (env_subst Xs Us (E & F))
      (typ_subst Xs Us T1) (typ_subst Xs Us T2) (knd_subst Xs Us K).
Proof.
  introv Hte Hks.
  apply regular_type_equal_core in Hte.
  pose combined_kinding_typ_subst.
  intuition eauto.
Qed.

Lemma type_equal_core_typ_subst : forall chk E F Xs Js Us T1 T2 K,
    type_equal_core chk (E & bind_knds Xs Js & F) T1 T2 K ->
    kindings chk (env_subst Xs Us (E & F)) Us
      (knd_subst_list Xs Us Js) ->
    type_equal_core chk (env_subst Xs Us (E & F))
      (typ_subst Xs Us T1) (typ_subst Xs Us T2) (knd_subst Xs Us K).
Proof.
  introv Hte Hks.
  destruct chk;
    eauto using type_equal_core_to_checked, kindings_valid_env,
      kindings_to_unchecked, type_equal_core_unchecked_typ_subst.
Qed.

Lemma type_equal_core_typ_subst_l : forall chk E Xs Js Us T1 T2 K,
    type_equal_core chk (E & bind_knds Xs Js) T1 T2 K ->
    kindings chk (env_subst Xs Us E) Us
      (knd_subst_list Xs Us Js) ->
    type_equal_core chk (env_subst Xs Us E)
      (typ_subst Xs Us T1) (typ_subst Xs Us T2) (knd_subst Xs Us K).
Proof.
  introv Hte Hks.
  rewrite <- concat_empty_r with (E := E & bind_knds Xs Js) in Hte.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r with (E := E) in Hks.
  eauto using type_equal_core_typ_subst.
Qed.

Lemma type_equal_symm_unchecked_typ_subst :
  forall chk E F Xs Js Us T1 T2 K,
    type_equal_symm chk (E & bind_knds Xs Js & F) T1 T2 K ->
    kindings false (env_subst Xs Us (E & F)) Us
      (knd_subst_list Xs Us Js) ->
    type_equal_symm false (env_subst Xs Us (E & F))
      (typ_subst Xs Us T1) (typ_subst Xs Us T2) (knd_subst Xs Us K).
Proof.
  introv Hte Hks.
  apply regular_type_equal_symm in Hte.
  pose combined_kinding_typ_subst.
  intuition eauto.
Qed.

Lemma type_equal_symm_typ_subst : forall chk E F Xs Js Us T1 T2 K,
    type_equal_symm chk (E & bind_knds Xs Js & F) T1 T2 K ->
    kindings chk (env_subst Xs Us (E & F)) Us
      (knd_subst_list Xs Us Js) ->
    type_equal_symm chk (env_subst Xs Us (E & F))
      (typ_subst Xs Us T1) (typ_subst Xs Us T2) (knd_subst Xs Us K).
Proof.
  introv Hte Hks.
  destruct chk;
    eauto using type_equal_symm_to_checked, kindings_valid_env,
      kindings_to_unchecked, type_equal_symm_unchecked_typ_subst.
Qed.

Lemma type_equal_symm_typ_subst_l : forall chk E Xs Js Us T1 T2 K,
    type_equal_symm chk (E & bind_knds Xs Js) T1 T2 K ->
    kindings chk (env_subst Xs Us E) Us
      (knd_subst_list Xs Us Js) ->
    type_equal_symm chk (env_subst Xs Us E)
      (typ_subst Xs Us T1) (typ_subst Xs Us T2) (knd_subst Xs Us K).
Proof.
  introv Hte Hks.
  rewrite <- concat_empty_r with (E := E & bind_knds Xs Js) in Hte.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r with (E := E) in Hks.
  eauto using type_equal_symm_typ_subst.
Qed.

Lemma type_equal_cong_unchecked_typ_subst :
  forall chk E F Xs Js Us T1 T2 K,
    type_equal_cong chk (E & bind_knds Xs Js & F) T1 T2 K ->
    kindings false (env_subst Xs Us (E & F)) Us
      (knd_subst_list Xs Us Js) ->
    type_equal_cong false (env_subst Xs Us (E & F))
      (typ_subst Xs Us T1) (typ_subst Xs Us T2) (knd_subst Xs Us K).
Proof.
  introv Hte Hks.
  apply regular_type_equal_cong in Hte.
  pose combined_kinding_typ_subst.
  intuition eauto.
Qed.

Lemma type_equal_cong_typ_subst : forall chk E F Xs Js Us T1 T2 K,
    type_equal_cong chk (E & bind_knds Xs Js & F) T1 T2 K ->
    kindings chk (env_subst Xs Us (E & F)) Us
      (knd_subst_list Xs Us Js) ->
    type_equal_cong chk (env_subst Xs Us (E & F))
      (typ_subst Xs Us T1) (typ_subst Xs Us T2) (knd_subst Xs Us K).
Proof.
  introv Hte Hks.
  destruct chk;
    eauto using type_equal_cong_to_checked, kindings_valid_env,
      kindings_to_unchecked, type_equal_cong_unchecked_typ_subst.
Qed.

Lemma type_equal_cong_typ_subst_l : forall chk E Xs Js Us T1 T2 K,
    type_equal_cong chk (E & bind_knds Xs Js) T1 T2 K ->
    kindings chk (env_subst Xs Us E) Us
      (knd_subst_list Xs Us Js) ->
    type_equal_cong chk (env_subst Xs Us E)
      (typ_subst Xs Us T1) (typ_subst Xs Us T2) (knd_subst Xs Us K).
Proof.
  introv Hte Hks.
  rewrite <- concat_empty_r with (E := E & bind_knds Xs Js) in Hte.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r with (E := E) in Hks.
  eauto using type_equal_cong_typ_subst.
Qed.

Lemma type_equal_unchecked_typ_subst :
  forall chk E F Xs Js Us T1 T2 K,
    type_equal chk (E & bind_knds Xs Js & F) T1 T2 K ->
    kindings false (env_subst Xs Us (E & F)) Us
      (knd_subst_list Xs Us Js) ->
    type_equal false (env_subst Xs Us (E & F))
      (typ_subst Xs Us T1) (typ_subst Xs Us T2) (knd_subst Xs Us K).
Proof.
  introv Hte Hks.
  apply regular_type_equal in Hte.
  pose combined_kinding_typ_subst.
  intuition eauto.
Qed.

Lemma type_equal_typ_subst : forall chk E F Xs Js Us T1 T2 K,
    type_equal chk (E & bind_knds Xs Js & F) T1 T2 K ->
    kindings chk (env_subst Xs Us (E & F)) Us
      (knd_subst_list Xs Us Js) ->
    type_equal chk (env_subst Xs Us (E & F))
      (typ_subst Xs Us T1) (typ_subst Xs Us T2) (knd_subst Xs Us K).
Proof.
  introv Hte Hks.
  destruct chk;
    eauto using type_equal_to_checked, kindings_valid_env,
      kindings_to_unchecked, type_equal_unchecked_typ_subst.
Qed.

Lemma type_equal_typ_subst_l : forall chk E Xs Js Us T1 T2 K,
    type_equal chk (E & bind_knds Xs Js) T1 T2 K ->
    kindings chk (env_subst Xs Us E) Us
      (knd_subst_list Xs Us Js) ->
    type_equal chk (env_subst Xs Us E)
      (typ_subst Xs Us T1) (typ_subst Xs Us T2) (knd_subst Xs Us K).
Proof.
  introv Hte Hks.
  rewrite <- concat_empty_r with (E := E & bind_knds Xs Js) in Hte.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r with (E := E) in Hks.
  eauto using type_equal_typ_subst.
Qed.

Lemma subtype_unchecked_typ_subst : forall chk E F Xs Js Us T1 T2 cs,
    subtype chk (E & bind_knds Xs Js & F) T1 T2 cs ->
    kindings false (env_subst Xs Us (E & F)) Us
      (knd_subst_list Xs Us Js) ->
    subtype false (env_subst Xs Us (E & F))
      (typ_subst Xs Us T1) (typ_subst Xs Us T2) cs.
Proof.
  introv Hs Hks.
  apply regular_subtype in Hs.
  pose combined_kinding_typ_subst.
  intuition eauto.
Qed.

Lemma subtype_typ_subst : forall chk E F Xs Js Us T1 T2 cs,
    subtype chk (E & bind_knds Xs Js & F) T1 T2 cs ->
    kindings chk (env_subst Xs Us (E & F)) Us
      (knd_subst_list Xs Us Js) ->
    subtype chk (env_subst Xs Us (E & F))
      (typ_subst Xs Us T1) (typ_subst Xs Us T2) cs.
Proof.
  introv Hs Hks.
  destruct chk;
    eauto using subtype_to_checked, kindings_valid_env,
      kindings_to_unchecked, subtype_unchecked_typ_subst.
Qed.

Lemma subtype_typ_subst_l : forall chk E Xs Js Us T1 T2 cs,
    subtype chk (E & bind_knds Xs Js) T1 T2 cs ->
    kindings chk (env_subst Xs Us E) Us
      (knd_subst_list Xs Us Js) ->
    subtype chk (env_subst Xs Us E) (typ_subst Xs Us T1) (typ_subst Xs Us T2) cs.
Proof.
  introv Hte Hks.
  rewrite <- concat_empty_r with (E := E & bind_knds Xs Js) in Hte.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r with (E := E) in Hks.
  eauto using subtype_typ_subst.
Qed.

Lemma kindings_typ_subst : forall chk E F Xs Js Us Ts Ks,
    kindings chk (E & bind_knds Xs Js & F) Ts Ks ->
    kindings chk (env_subst Xs Us (E & F)) Us
      (knd_subst_list Xs Us Js) ->
    kindings chk (env_subst Xs Us (E & F))
      (typ_subst_list Xs Us Ts) (knd_subst_list Xs Us Ks).
Proof.
  introv Hks1 Hks2.
  remember (E & bind_knds Xs Js & F) as EXF.
  induction Hks1; subst; simpl;
    eauto using kindings_valid_env, kinding_typ_subst.    
Qed.

Lemma kindings_typ_subst_l : forall chk E Xs Js Us Ts Ks,
    kindings chk (E & bind_knds Xs Js) Ts Ks ->
    kindings chk (env_subst Xs Us E) Us
      (knd_subst_list Xs Us Js) ->
    kindings chk (env_subst Xs Us E) (typ_subst_list Xs Us Ts)
      (knd_subst_list Xs Us Ks).
Proof.
  introv Hk Hks.
  rewrite <- concat_empty_r with (E := E & bind_knds Xs Js) in Hk.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r with (E := E) in Hks.
  eauto using kindings_typ_subst.
Qed.

Lemma valid_schemes_typ_subst : forall chk E F Xs Js Us Ms,
    valid_schemes chk (E & bind_knds Xs Js & F) Ms ->
    kindings chk (env_subst Xs Us (E & F)) Us
      (knd_subst_list Xs Us Js) ->
    valid_schemes chk (env_subst Xs Us (E & F))
      (sch_subst_list Xs Us Ms).
Proof.
  introv Hss Hks.
  remember (E & bind_knds Xs Js & F) as EXF.
  induction Hss; subst; simpl;
    eauto using kindings_valid_env, valid_scheme_typ_subst.
Qed.

Lemma valid_schemes_typ_subst_l : forall chk E Xs Js Us Ms,
    valid_schemes chk (E & bind_knds Xs Js) Ms ->
    kindings chk (env_subst Xs Us E) Us
      (knd_subst_list Xs Us Js) ->
    valid_schemes chk (env_subst Xs Us E) (sch_subst_list Xs Us Ms).
Proof.
  introv Hss Hks.
  rewrite <- concat_empty_r with (E := E & bind_knds Xs Js) in Hss.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r with (E := E) in Hks.
  eauto using valid_schemes_typ_subst.
Qed.

Lemma valid_instance_typ_subst : forall E F Xs Js Us Ts M,
    valid_instance (E & bind_knds Xs Js & F) Ts M ->
    kindings true (env_subst Xs Us (E & F)) Us
      (knd_subst_list Xs Us Js) ->
    valid_instance (env_subst Xs Us (E & F))
      (typ_subst_list Xs Us Ts) (sch_subst Xs Us M).
Proof.
  introv Hv Hks.
  remember (E & bind_knds Xs Js & F) as EXF.
  destruct Hv; subst.
  destruct M; unfold sch_subst; simpl in *.
  apply valid_instance_c; simpl.
  - rewrite <- knd_subst_list_open;
      eauto using kindings_typ_subst with kindings_regular.
  - replace knd_type with (knd_subst Xs Us knd_type) by auto.
    rewrite <- typ_subst_open;
      eauto using kinding_typ_subst with kindings_regular.
Qed.

Lemma valid_instance_typ_subst_l : forall E Xs Js Us Ts M,
    valid_instance (E & bind_knds Xs Js) Ts M ->
    kindings true (env_subst Xs Us E) Us
      (knd_subst_list Xs Us Js) ->
    valid_instance (env_subst Xs Us E)
      (typ_subst_list Xs Us Ts) (sch_subst Xs Us M).
Proof.
  introv Hv Hks.
  rewrite <- concat_empty_r with (E := E & bind_knds Xs Js) in Hv.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r with (E := E) in Hks.
  eauto using valid_instance_typ_subst.
Qed.

Lemma valid_store_type_typ_subst : forall E F Xs Js Us P,
  valid_store_type (E & bind_knds Xs Js & F) P ->
  kindings true (env_subst Xs Us (E & F)) Us
    (knd_subst_list Xs Us Js) ->
  valid_store_type (env_subst Xs Us (E & F)) (styp_subst Xs Us P).
Proof.
  introv Hs He.
  remember (E & bind_knds Xs Js & F) as EXF.
  induction Hs; autorewrite with rew_styp_subst in *; subst.
  - apply valid_store_type_empty.
    eauto using kindings_valid_env.
  - apply valid_store_type_push; autorewrite with rew_styp_dom; auto.
    replace knd_type with (knd_subst Xs Us knd_type) by auto.
    eauto using kinding_typ_subst.
Qed.

Lemma valid_store_type_typ_subst_l : forall E Xs Js Us P,
  valid_store_type (E & bind_knds Xs Js) P ->
  kindings true (env_subst Xs Us E) Us
    (knd_subst_list Xs Us Js) ->
  valid_store_type (env_subst Xs Us E) (styp_subst Xs Us P).
Proof.
  introv Hs Hks.
  rewrite <- concat_empty_r with (E := E & bind_knds Xs Js) in Hs.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r with (E := E) in Hks.
  eauto using valid_store_type_typ_subst.
Qed.

(* *************************************************************** *)
(** Some subtyping theorems useful for proving validity.

    Since these are needed for proving validity they can't assume
    it, so some of them require additional parameters showing that
    the types involved are valid. Versions of these properties
    without the additional parameters are in the subtyping file. *)

(* Type equality is a preorder *)

Lemma type_equal_reflexive : forall chk E T K,
    kinding chk E T K ->
    type_equal chk E T T K.
Proof.
  intros.
  apply type_equal_refl;
    destruct chk; try discriminate;
    auto with kinding_regular. 
Qed.

Lemma type_equal_transitive : forall chk E T1 T2 T3 K,
    type_equal chk E T1 T2 K ->
    type_equal chk E T2 T3 K ->
    type_equal chk E T1 T3 K.
Proof.
  introv Hte1 Hte2.
  induction Hte1;
    eauto using type_equal
      with type_equal_regular.
Qed.

(* Useful properties of type equality on meets *)

Lemma type_equal_unvalidated_meet_idempotent : forall chk E T cs,
    valid_env chk E ->
    kinding chk E T (knd_row cs) ->
    type_equal chk E T (typ_meet T T) (knd_row cs).
Proof.
  introv He Hk.
  apply type_equal_step
    with (T2 := typ_meet T (typ_join T (typ_bot cs)));
    auto with kinding_regular.
  apply type_equal_step
    with (T2 := typ_meet T T);
    auto with kinding_regular.
Qed.

Lemma type_equal_meet_r : forall chk E T1 T2 T2' cs,
    kinding chk E T1 (knd_row cs) ->
    type_equal chk E T2 T2' (knd_row cs) ->
    type_equal chk E
      (typ_meet T1 T2) (typ_meet T1 T2') (knd_row cs).
Proof.
  introv Hk Hte.
  remember (knd_row cs).
  induction Hte; subst.
  - apply type_equal_refl;
      auto with kinding_regular.
  - apply type_equal_step
      with (T2 := typ_meet T1 T2);
      auto with kinding_regular.
Qed.

Lemma type_equal_meet_l : forall chk E T1 T1' T2 cs,
    kinding chk E T2 (knd_row cs) ->
    type_equal chk E T1 T1' (knd_row cs) ->
    type_equal chk E
      (typ_meet T1 T2) (typ_meet T1' T2) (knd_row cs).
Proof.
  introv Hk Hte.
  remember (knd_row cs).
  induction Hte; subst.
  - apply type_equal_refl;
      auto with kinding_regular.
  - apply type_equal_step
      with (T2 := typ_meet T0 T2);
      auto with kinding_regular.
Qed.

(* Subtyping is reflexive *)

Lemma subtype_unvalidated_refl : forall chk E T cs,
    valid_env chk E ->
    kinding chk E T (knd_row cs) ->
    subtype chk E T T cs.
Proof.
  introv He Hk.
  apply subtype_c;
    auto with kinding_regular.
  apply type_equal_step
    with (T2 := (typ_meet T (typ_join T (typ_bot cs))));
    auto with kinding_regular.
  apply type_equal_step
    with (T2 := (typ_meet T T));
    auto with kinding_regular.
Qed.

Lemma subtype_unvalidated_reflexive : forall chk E T1 T2 cs,
    valid_env chk E ->
    kinding chk E T1 (knd_row cs) ->
    type_equal chk E T1 T2 (knd_row cs) ->
    subtype chk E T1 T2 cs.
Proof.
  introv He Hk HHte.
  apply subtype_c; auto with type_equal_regular.
  apply type_equal_transitive with (T2 := typ_meet T1 T1);
    auto using type_equal_unvalidated_meet_idempotent.
  auto using type_equal_meet_r.
Qed.

(* Type equality is symmetric (and thus an equivalence) *)
    
Lemma type_equal_symm_symmetric : forall chk E T1 T2 K,
    type_equal_symm chk E T1 T2 K ->
    type_equal_symm chk E T2 T1 K.
Proof.
  introv Hte.
  induction Hte; auto.
Qed.

Lemma type_equal_cong_symmetric : forall chk E T1 T2 K,
    type_equal_cong chk E T1 T2 K ->
    type_equal_cong chk E T2 T1 K.
Proof.
  introv Hte. 
  induction Hte;
    auto using type_equal_symm_symmetric.
Qed.

Lemma type_equal_unvalidated_symmetric_ind : forall chk E T1 T2 T3 K,
    type_equal chk E T2 T1 K ->
    type_equal chk E T2 T3 K ->
    type_equal chk E T3 T1 K.
Proof.
  introv Hacc Hte.
  induction Hte;
    eauto using type_equal_cong_symmetric
      with type_equal_regular.
Qed.

Lemma type_equal_unvalidated_symmetric : forall chk E T1 T2 K,
    kinding chk E T1 K ->
    type_equal chk E T1 T2 K ->
    type_equal chk E T2 T1 K.
Proof.
  introv Hte.
  apply type_equal_unvalidated_symmetric_ind with (T2 := T1);
    try assumption.
  apply type_equal_refl;
    auto with type_equal_regular.
Qed.

(* Subtyping is transitive and antisymmetric (and
   thus a partial order) *)

Lemma subtype_unvalidated_transitive : forall chk E T1 T2 T3 cs,
    kinding chk E T1 (knd_row cs) ->
    kinding chk E T2 (knd_row cs) ->
    kinding chk E T3 (knd_row cs) ->
    subtype chk E T1 T2 cs ->
    subtype chk E T2 T3 cs ->
    subtype chk E T1 T3 cs.
Proof.
  introv Hk1 Hk2 Hk3 Hs1 Hs2.
  apply subtype_c; auto with subtype_regular.
  destruct Hs1; destruct Hs2.
  apply type_equal_transitive
    with (T2 := typ_meet T1 T0); auto.
  apply type_equal_transitive
    with (T2 := typ_meet T1 (typ_meet T0 T2));
    auto using type_equal_meet_r.
  apply type_equal_step
    with (T2 := typ_meet (typ_meet T1 T0) T2);
    auto with kinding_regular.
  apply type_equal_transitive with (T2 := typ_meet T1 T2);
    auto using type_equal_meet_l,
      type_equal_reflexive,
      type_equal_unvalidated_symmetric.
Qed.

Lemma subtype_unvalidated_antisymmetric : forall chk E T1 T2 cs,
    kinding chk E T1 (knd_row cs) ->
    kinding chk E T2 (knd_row cs) ->
    subtype chk E T1 T2 cs ->
    subtype chk E T2 T1 cs ->
    type_equal chk E T1 T2 (knd_row cs).
Proof.
  introv Hk1 Hk2 Hs1 Hs2.
  destruct Hs1; destruct Hs2.
  apply type_equal_transitive
    with (T2 := typ_meet T2 T1); auto.
  apply type_equal_step
    with (T2 := typ_meet T1 T2);
    auto with kinding_regular.
  apply type_equal_unvalidated_symmetric; auto.
Qed.

(* Typing lattice is bounded *)

Lemma subtype_unvalidated_top : forall chk E T cs,
    valid_env chk E ->
    kinding chk E T (knd_row cs) ->
    subtype chk E T (typ_top cs) cs.
Proof.
  introv He Hk.
  apply subtype_c; auto with kinding_regular.
  apply type_equal_step with (typ_meet T (typ_top cs));
    auto using type_equal_reflexive with kinding_regular.
Qed.

Lemma subtype_unvalidated_bot : forall chk E T cs,
    valid_env chk E ->
    kinding chk E T (knd_row cs) ->
    subtype chk E (typ_bot cs) T cs.
Proof.
  introv He Hk.
  apply subtype_c; auto with kinding_regular.
  apply type_equal_step
    with (typ_meet (typ_bot cs) (typ_join (typ_bot cs) T));
    auto with kinding_regular.
  apply type_equal_step
    with (typ_meet (typ_bot cs) (typ_join T (typ_bot cs)));
    auto 6 with kinding_regular.
  apply type_equal_step with (typ_meet (typ_bot cs) T);
    auto using type_equal_reflexive
      with kinding_regular.
Qed.

Lemma kinding_unvalidated_range_top_bot : forall chk E T1 T2 T3,
    valid_env chk E ->
    kinding chk E T1 (knd_range T2 T3) ->
    kinding chk E T2 (knd_row CSet.universe) ->
    kinding chk E T3 (knd_row CSet.universe) ->
    subtype chk E T3 T2 CSet.universe ->
    kinding chk E T1
      (knd_range (typ_top CSet.universe) (typ_bot CSet.universe)).
Proof.
  introv He Hk1 Hk2 Hk3 Hs.
  apply kinding_range_subsumption
    with (T1 := T2) (T2 := T3);
      auto using subtype_unvalidated_top, subtype_unvalidated_bot
        with kinding_regular.
Qed.

Lemma kinding_unvalidated_range_top : forall chk E T1 T2,
    valid_env chk E ->
    kinding chk E T1 (knd_range T2 (typ_bot CSet.universe)) ->
    kinding chk E T2 (knd_row CSet.universe) ->
    kinding chk E T1
      (knd_range (typ_top CSet.universe) (typ_bot CSet.universe)).
Proof.
  introv He Hk1 Hk2.
  eauto using kinding_unvalidated_range_top_bot,
   subtype_unvalidated_bot with csetdec.
Qed.

Lemma kinding_unvalidated_range_bot : forall chk E T1 T2,
    valid_env chk E ->
    kinding chk E T1 (knd_range (typ_top CSet.universe) T2) ->
    kinding chk E T2 (knd_row CSet.universe) ->
    kinding chk E T1
      (knd_range (typ_top CSet.universe) (typ_bot CSet.universe)).
Proof.
  introv He Hk1 Hk2.
  eauto using kinding_unvalidated_range_top_bot,
   subtype_unvalidated_top with csetdec.
Qed.

(* *************************************************************** *)
(** * "Validated" versions of kinding judgements *)

Inductive valid_kind_validated : bool -> env -> knd -> Prop :=
  | valid_kind_validated_type : forall chk E,
      valid_env_validated chk E ->
      environment E ->
      valid_kind_validated chk E knd_type
  | valid_kind_validated_row :  forall chk E cs,
      valid_env_validated chk E ->
      CSet.Nonempty cs ->
      environment E ->
      valid_kind_validated chk E (knd_row cs)
  | valid_kind_validated_range : forall chk E T1 T2,
      subtype_validated chk E T2 T1 CSet.universe ->
      environment E ->
      type T1 ->
      type T2 ->
      valid_env_validated chk E ->
      kinding_validated chk E T1 (knd_row CSet.universe) ->
      kinding_validated chk E T2 (knd_row CSet.universe) ->
      valid_kind_validated chk E (knd_range T1 T2)

with kinding_validated : bool -> env -> typ -> knd -> Prop :=
  | kinding_validated_var : forall chk E X K,
      valid_env_validated chk E ->
      binds X (bind_knd K) E ->
      environment E ->
      kind K ->
      (chk = true -> valid_kind chk E K) ->
      kinding_validated chk E (typ_fvar X) K
  | kinding_validated_constructor : forall chk E c T cs,
      kinding_validated chk E T knd_type ->
      cs = CSet.singleton c ->
      environment E ->
      type T ->
      valid_env_validated chk E ->
      kinding_validated chk E (typ_constructor c T) (knd_row cs)
  | kinding_validated_or : forall chk E T1 T2 cs1 cs2 cs12,
      kinding_validated chk E T1 (knd_row cs1) ->
      kinding_validated chk E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      valid_env_validated chk E ->
      kinding_validated chk E (typ_or cs1 T1 cs2 T2) (knd_row cs12)
  | kinding_validated_proj : forall chk E T cs cs',
      kinding_validated chk E T (knd_row cs) ->
      CSet.Subset cs' cs ->
      CSet.Nonempty cs' ->
      environment E ->
      type T ->
      CSet.Nonempty cs ->
      valid_env_validated chk E ->
      kinding_validated chk E (typ_proj cs T cs') (knd_row cs')
  | kinding_validated_variant : forall chk E T,
      kinding_validated chk E T
        (knd_range (typ_top CSet.universe) (typ_bot CSet.universe)) ->
      environment E ->
      type T ->
      valid_env_validated chk E ->
      kinding_validated chk E (typ_variant T) knd_type
  | kinding_validated_arrow : forall chk E T1 T2,
      kinding_validated chk E T1 knd_type -> 
      kinding_validated chk E T2 knd_type -> 
      environment E ->
      type T1 ->
      type T2 ->
      valid_env_validated chk E ->
      kinding_validated chk E (typ_arrow T1 T2) knd_type
  | kinding_validated_ref : forall chk E T,
      kinding_validated chk E T knd_type ->
      environment E ->
      type T ->
      valid_env_validated chk E ->
      kinding_validated chk E (typ_ref T) knd_type
  | kinding_validated_unit : forall chk E,
      valid_env_validated chk E ->
      environment E ->
      kinding_validated chk E typ_unit knd_type
  | kinding_validated_prod : forall chk E T1 T2,
      kinding_validated chk E T1 knd_type -> 
      kinding_validated chk E T2 knd_type -> 
      environment E ->
      type T1 ->
      type T2 ->
      valid_env_validated chk E ->
      kinding_validated chk E (typ_prod T1 T2) knd_type
  | kinding_validated_top : forall chk E cs,
      valid_env_validated chk E ->
      CSet.Nonempty cs ->
      environment E ->
      kinding_validated chk E (typ_top cs) (knd_row cs)
  | kinding_validated_bot : forall chk E cs,
      valid_env_validated chk E ->
      CSet.Nonempty cs ->
      environment E ->
      kinding_validated chk E (typ_bot cs) (knd_row cs)
  | kinding_validated_meet : forall chk E T1 T2 cs,
      kinding_validated chk E T1 (knd_row cs) ->
      kinding_validated chk E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env_validated chk E ->
      kinding_validated chk E (typ_meet T1 T2) (knd_row cs)
  | kinding_validated_join : forall chk E T1 T2 cs,
      kinding_validated chk E T1 (knd_row cs) ->
      kinding_validated chk E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env_validated chk E ->
      kinding_validated chk E (typ_join T1 T2) (knd_row cs)
  | kinding_validated_range_subsumption :
      forall chk E T T1 T2 T1' T2',
      kinding_validated chk E T (knd_range T1 T2) ->
      subtype_validated chk E T1 T1' CSet.universe ->
      subtype_validated chk E T2' T2 CSet.universe ->
      environment E ->
      type T ->
      type T1 ->
      type T2 ->
      type T1' ->
      type T2' ->
      valid_env_validated chk E ->
      kinding_validated chk E T1 (knd_row CSet.universe) ->
      kinding_validated chk E T1' (knd_row CSet.universe) ->
      kinding_validated chk E T2 (knd_row CSet.universe) ->
      kinding_validated chk E T2' (knd_row CSet.universe) ->
      (chk = true -> subtype chk E T2 T1 CSet.universe) ->
      (chk = true -> subtype chk E T2' T1' CSet.universe) ->
      (chk = true -> valid_kind chk E (knd_range T1 T2)) ->
      (chk = true -> valid_kind chk E (knd_range T1' T2')) ->
      kinding_validated chk E T (knd_range T1' T2')

with valid_kinds_validated : bool -> env -> list knd -> Prop :=
  | valid_kinds_validated_nil : forall chk E,
      valid_env_validated chk E ->
      environment E ->
      valid_kinds_validated chk E nil
  | valid_kinds_validated_cons : forall chk E K Ks,
      valid_kind_validated chk E K ->
      valid_kinds_validated chk E Ks ->
      environment E ->
      kind K ->
      kinds Ks ->
      valid_env_validated chk E ->
      valid_kinds_validated chk E (K :: Ks)

with valid_kinds_and_type_validated
     : bool -> env -> list knd -> typ -> Prop :=
  | valid_kinds_and_type_validated_c : forall chk E Ks T,
      valid_kinds_validated chk E Ks ->
      kinding_validated chk E T knd_type ->
      environment E ->
      kinds Ks ->
      type T ->
      valid_env_validated chk E ->
      valid_kinds_and_type_validated chk E Ks T

with valid_scheme_validated : bool -> env -> sch -> Prop :=
  | valid_scheme_validated_c : forall L chk E M,
      valid_env_validated chk E ->
      (forall Xs,
          fresh L (sch_arity M) Xs ->
          valid_kinds_and_type_validated chk (E & Xs ~::* M)
            (knd_open_vars_list (sch_kinds M) Xs)
            (typ_open_vars (sch_body M) Xs)) ->
      environment E ->
      scheme M ->
      valid_scheme_validated chk E M

with valid_env_aux_validated : env -> env -> Prop :=
  | valid_env_aux_validated_empty : forall E,
      environment E ->
      valid_env_aux_validated E empty
  | valid_env_aux_validated_kind : forall E F X K,
      valid_env_aux_validated E F ->
      valid_kind_validated false E K ->
      X # F ->
      environment E ->
      environment F ->
      environment (F & X ~:: K) ->
      kind K ->
      valid_env_aux_validated E (F & X ~:: K)
  | valid_env_aux_validated_type : forall E F x M,
      valid_env_aux_validated E F ->
      valid_scheme_validated false E M ->
      x # F ->
      environment E ->
      environment F ->
      environment (F & x ~: M) ->
      scheme M ->
      valid_env_aux_validated E (F & x ~: M)

with valid_env_validated : bool -> env -> Prop :=
  | valid_env_validated_check : forall E,
      valid_env_aux_validated E E ->
      environment E ->
      valid_env_validated true E
  | valid_env_validated_no_check : forall E,
      environment E ->
      valid_env_validated false E

with type_equal_core_validated :
       bool -> env -> typ -> typ -> knd -> Prop :=
  | type_equal_core_validated_or_commutative :
      forall chk E T1 T2 cs1 cs2 cs12,
      kinding_validated chk E T1 (knd_row cs1) ->
      kinding_validated chk E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      valid_env_validated chk E ->
      type_equal_core_validated chk E
        (typ_or cs1 T1 cs2 T2) (typ_or cs2 T2 cs1 T1) (knd_row cs12)
  | type_equal_core_validated_or_associative :
      forall chk E T1 cs1 T2 cs2 T3 cs3 cs12 cs23 cs123,
      kinding_validated chk E T1 (knd_row cs1) ->
      kinding_validated chk E T2 (knd_row cs2) ->
      kinding_validated chk E T3 (knd_row cs3) ->
      CSet.Disjoint cs1 cs2 ->
      CSet.Disjoint cs1 cs3 ->
      CSet.Disjoint cs2 cs3 ->
      cs12 = CSet.union cs1 cs2 ->
      cs23 = CSet.union cs2 cs3 ->
      cs123 = CSet.union cs1 cs23 ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      CSet.Nonempty cs3 ->
      valid_env_validated chk E ->
      type_equal_core_validated chk E
        (typ_or cs1 T1 cs23 (typ_or cs2 T2 cs3 T3))
        (typ_or cs12 (typ_or cs1 T1 cs2 T2) cs3 T3)
        (knd_row cs123)
  | type_equal_core_validated_or_bot : forall chk E cs1 cs2 cs12,
      valid_env_validated chk E ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type_equal_core_validated chk E
        (typ_or cs1 (typ_bot cs1) cs2 (typ_bot cs2)) (typ_bot cs12)
        (knd_row cs12)
  | type_equal_core_validated_or_top : forall chk E cs1 cs2 cs12,
      valid_env_validated chk E ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type_equal_core_validated chk E
        (typ_or cs1 (typ_top cs1) cs2 (typ_top cs2)) (typ_top cs12)
        (knd_row cs12)
  | type_equal_core_validated_or_meet_distribution :
      forall chk E T1 T2 T3 T4 cs1 cs2 cs12,
      kinding_validated chk E T1 (knd_row cs1) ->
      kinding_validated chk E T2 (knd_row cs2) ->
      kinding_validated chk E T3 (knd_row cs1) ->
      kinding_validated chk E T4 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      type T4 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      valid_env_validated chk E ->
      type_equal_core_validated chk E
        (typ_or cs1 (typ_meet T1 T3) cs2 (typ_meet T2 T4))
        (typ_meet (typ_or cs1 T1 cs2 T2) (typ_or cs1 T3 cs2 T4))
        (knd_row cs12)
  | type_equal_core_validated_or_join_distribution :
      forall chk E T1 T2 T3 T4 cs1 cs2 cs12,
      kinding_validated chk E T1 (knd_row cs1) ->
      kinding_validated chk E T2 (knd_row cs2) ->
      kinding_validated chk E T3 (knd_row cs1) ->
      kinding_validated chk E T4 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      type T4 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      valid_env_validated chk E ->
      type_equal_core_validated chk E
        (typ_or cs1 (typ_join T1 T3) cs2 (typ_join T2 T4))
        (typ_join (typ_or cs1 T1 cs2 T2) (typ_or cs1 T3 cs2 T4))
        (knd_row cs12)
  | type_equal_core_validated_or_proj :
      forall chk E T cs1 cs2 cs3 cs23,
      kinding_validated chk E T (knd_row cs1) ->
      CSet.Disjoint cs2 cs3 ->
      CSet.Subset cs2 cs1 ->
      CSet.Nonempty cs2 ->
      CSet.Subset cs3 cs1 ->
      CSet.Nonempty cs3 ->
      cs23 = CSet.union cs2 cs3 ->
      environment E ->
      type T ->
      CSet.Nonempty cs1 ->
      valid_env_validated chk E ->
      type_equal_core_validated chk E
        (typ_or cs2 (typ_proj cs1 T cs2) cs3 (typ_proj cs1 T cs3))
        (typ_proj cs1 T cs23)
        (knd_row cs23)
  | type_equal_core_validated_proj_id :
      forall chk E T cs,
      kinding_validated chk E T (knd_row cs) ->
      environment E ->
      type T ->
      CSet.Nonempty cs ->
      valid_env_validated chk E ->
      type_equal_core_validated chk E
        (typ_proj cs T cs) T (knd_row cs)
  | type_equal_core_validated_proj_compose :
      forall chk E T cs1 cs2 cs3,
      kinding_validated chk E T (knd_row cs1) ->
      CSet.Subset cs2 cs1 ->
      CSet.Subset cs3 cs2 ->
      CSet.Nonempty cs3 ->
      environment E ->
      type T ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      valid_env_validated chk E ->
      type_equal_core_validated chk E
        (typ_proj cs2 (typ_proj cs1 T cs2) cs3)
        (typ_proj cs1 T cs3)
        (knd_row cs3)
  | type_equal_core_validated_proj_or_l :
      forall chk E T1 T2 cs1 cs1' cs2 cs12,
      kinding_validated chk E T1 (knd_row cs1) ->
      kinding_validated chk E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      CSet.Subset cs1' cs1 ->
      CSet.Nonempty cs1' ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      valid_env_validated chk E ->
      type_equal_core_validated chk E
        (typ_proj cs12 (typ_or cs1 T1 cs2 T2) cs1')
        (typ_proj cs1 T1 cs1')
        (knd_row cs1')
  | type_equal_core_validated_proj_or_r :
      forall chk E T1 T2 cs1 cs2 cs2' cs12,
      kinding_validated chk E T1 (knd_row cs1) ->
      kinding_validated chk E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      CSet.Subset cs2' cs2 ->
      CSet.Nonempty cs2' ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      valid_env_validated chk E ->
      type_equal_core_validated chk E
        (typ_proj cs12 (typ_or cs1 T1 cs2 T2) cs2')
        (typ_proj cs2 T2 cs2')
        (knd_row cs2')
  | type_equal_core_validated_proj_or_both :
      forall chk E T1 T2 cs1 cs2 cs1' cs2' cs12 cs12',
      kinding_validated chk E T1 (knd_row cs1) ->
      kinding_validated chk E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      CSet.Subset cs1' cs1 ->
      CSet.Nonempty cs1' ->
      CSet.Subset cs2' cs2 ->
      CSet.Nonempty cs2' ->
      cs12 = CSet.union cs1 cs2 ->
      cs12' = CSet.union cs1' cs2' ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      valid_env_validated chk E ->
      type_equal_core_validated chk E
        (typ_proj cs12 (typ_or cs1 T1 cs2 T2) cs12')
        (typ_or cs1' (typ_proj cs1 T1 cs1')
                cs2' (typ_proj cs2 T2 cs2'))
        (knd_row cs12')
  | type_equal_core_validated_proj_meet : forall chk E T1 T2 cs cs',
      kinding_validated chk E T1 (knd_row cs) ->
      kinding_validated chk E T2 (knd_row cs) ->
      CSet.Subset cs' cs ->
      CSet.Nonempty cs' ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env_validated chk E ->
      type_equal_core_validated chk E
        (typ_proj cs (typ_meet T1 T2) cs')
        (typ_meet (typ_proj cs T1 cs') (typ_proj cs T2 cs'))
        (knd_row cs')
  | type_equal_core_validated_proj_join : forall chk E T1 T2 cs cs',
      kinding_validated chk E T1 (knd_row cs) ->
      kinding_validated chk E T2 (knd_row cs) ->
      CSet.Subset cs' cs ->
      CSet.Nonempty cs' ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env_validated chk E ->
      type_equal_core_validated chk E
        (typ_proj cs (typ_join T1 T2) cs')
        (typ_join (typ_proj cs T1 cs') (typ_proj cs T2 cs'))
        (knd_row cs')
  | type_equal_core_validated_meet_commutative :
      forall chk E T1 T2 cs,
      kinding_validated chk E T1 (knd_row cs) ->
      kinding_validated chk E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env_validated chk E ->
      type_equal_core_validated chk E
        (typ_meet T1 T2) (typ_meet T2 T1) (knd_row cs)
  | type_equal_core_validated_meet_associative :
      forall chk E T1 T2 T3 cs,
      kinding_validated chk E T1 (knd_row cs) ->
      kinding_validated chk E T2 (knd_row cs) ->
      kinding_validated chk E T3 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      CSet.Nonempty cs ->
      valid_env_validated chk E ->
      type_equal_core_validated chk E
        (typ_meet T1 (typ_meet T2 T3))
        (typ_meet (typ_meet T1 T2) T3)
        (knd_row cs)
  | type_equal_core_validated_meet_identity : forall chk E T1 cs,
      kinding_validated chk E T1 (knd_row cs) ->
      environment E ->
      type T1 ->
      CSet.Nonempty cs ->
      valid_env_validated chk E ->
      type_equal_core_validated chk E
        (typ_meet T1 (typ_top cs)) T1 (knd_row cs)
  | type_equal_core_validated_meet_absorption : forall chk E T1 T2 cs,
      kinding_validated chk E T1 (knd_row cs) ->
      kinding_validated chk E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env_validated chk E ->
      type_equal_core_validated chk E
        (typ_meet T1 (typ_join T1 T2)) T1 (knd_row cs)
  | type_equal_core_validated_meet_distribution :
      forall chk E T1 T2 T3 cs,
      kinding_validated chk E T1 (knd_row cs) ->
      kinding_validated chk E T2 (knd_row cs) ->
      kinding_validated chk E T3 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      CSet.Nonempty cs ->
      valid_env_validated chk E ->
      type_equal_core_validated chk E
        (typ_meet T1 (typ_join T2 T3))
        (typ_join (typ_meet T1 T2) (typ_meet T1 T3))
        (knd_row cs)
  | type_equal_core_validated_join_commutative :
      forall chk E T1 T2 cs,
      kinding_validated chk E T1 (knd_row cs) ->
      kinding_validated chk E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env_validated chk E ->
      type_equal_core_validated chk E
        (typ_join T1 T2) (typ_join T2 T1) (knd_row cs)
  | type_equal_core_validated_join_associative :
      forall chk E T1 T2 T3 cs,
      kinding_validated chk E T1 (knd_row cs) ->
      kinding_validated chk E T2 (knd_row cs) ->
      kinding_validated chk E T3 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      CSet.Nonempty cs ->
      valid_env_validated chk E ->
      type_equal_core_validated chk E
        (typ_join T1 (typ_join T2 T3))
        (typ_join (typ_join T1 T2) T3)
        (knd_row cs)
  | type_equal_core_validated_join_identity : forall chk E T1 cs,
      kinding_validated chk E T1 (knd_row cs) ->
      environment E ->
      type T1 ->
      CSet.Nonempty cs ->
      valid_env_validated chk E ->
      type_equal_core_validated chk E
        (typ_join T1 (typ_bot cs)) T1 (knd_row cs)
  | type_equal_core_validated_join_absorption : forall chk E T1 T2 cs,
      kinding_validated chk E T1 (knd_row cs) ->
      kinding_validated chk E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env_validated chk E ->
      type_equal_core_validated chk E
        (typ_join T1 (typ_meet T1 T2)) T1 (knd_row cs)
  | type_equal_core_validated_join_distribution :
      forall chk E T1 T2 T3 cs,
      kinding_validated chk E T1 (knd_row cs) ->
      kinding_validated chk E T2 (knd_row cs) ->
      kinding_validated chk E T3 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      CSet.Nonempty cs ->
      valid_env_validated chk E ->
      type_equal_core_validated chk E
        (typ_join T1 (typ_meet T2 T3))
        (typ_meet (typ_join T1 T2) (typ_join T1 T3))
        (knd_row cs)

with type_equal_symm_validated :
       bool -> env -> typ -> typ -> knd -> Prop :=
  | type_equal_symm_validated_l : forall chk E T1 T2 K,
      type_equal_core_validated chk E T1 T2 K ->
      environment E ->
      type T1 ->
      type T2 ->
      kind K ->
      valid_env_validated chk E ->
      kinding_validated chk E T1 K ->
      kinding_validated chk E T2 K ->
      (chk = true -> valid_kind chk E K) ->
      type_equal_symm_validated chk E T1 T2 K
  | type_equal_symm_validated_r : forall chk E T1 T2 K,
      type_equal_core_validated chk E T1 T2 K ->
      environment E ->
      type T1 ->
      type T2 ->
      kind K ->
      valid_env_validated chk E ->
      kinding_validated chk E T1 K ->
      kinding_validated chk E T2 K ->
      (chk = true -> valid_kind chk E K) ->
      type_equal_symm_validated chk E T2 T1 K

with type_equal_cong_validated :
       bool -> env -> typ -> typ -> knd -> Prop :=
  | type_equal_cong_validated_constructor : forall chk E c T1 T1' cs,
      type_equal_cong_validated chk E T1 T1' knd_type ->
      cs = CSet.singleton c ->
      environment E ->
      type T1 ->
      type T1' ->
      valid_env_validated chk E ->
      kinding_validated chk E T1 knd_type ->
      kinding_validated chk E T1' knd_type ->
      type_equal_cong_validated chk E
        (typ_constructor c T1) (typ_constructor c T1')
        (knd_row cs)
  | type_equal_cong_validated_or_l :
      forall chk E T1 T1' T2 cs1 cs2 cs12,
      kinding_validated chk E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_cong_validated chk E T1 T1' (knd_row cs1) ->
      environment E ->
      type T1 ->
      type T1' ->
      type T2 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      valid_env_validated chk E ->
      kinding_validated chk E T1 (knd_row cs1) ->
      kinding_validated chk E T1' (knd_row cs1) ->
      type_equal_cong_validated chk E
        (typ_or cs1 T1 cs2 T2) (typ_or cs1 T1' cs2 T2) (knd_row cs12)
  | type_equal_cong_validated_or_r :
      forall chk E T1 T2 T2' cs1 cs2 cs12,
      kinding_validated chk E T1 (knd_row cs1) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_cong_validated chk E T2 T2' (knd_row cs2) ->
      environment E ->
      type T1 ->
      type T2 ->
      type T2' ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      valid_env_validated chk E ->
      kinding_validated chk E T2 (knd_row cs2) ->
      kinding_validated chk E T2' (knd_row cs2) ->
      type_equal_cong_validated chk E
        (typ_or cs1 T1 cs2 T2) (typ_or cs1 T1 cs2 T2') (knd_row cs12)
  | type_equal_cong_validated_proj : forall chk E T1 T1' cs1 cs2,
      CSet.Subset cs2 cs1 ->
      CSet.Nonempty cs2 ->
      type_equal_cong_validated chk E T1 T1' (knd_row cs1) ->
      environment E ->
      type T1 ->
      type T1' ->
      CSet.Nonempty cs1 ->
      valid_env_validated chk E ->
      kinding_validated chk E T1 (knd_row cs1) ->
      kinding_validated chk E T1' (knd_row cs1) ->
      type_equal_cong_validated chk E
        (typ_proj cs1 T1 cs2) (typ_proj cs1 T1' cs2) (knd_row cs2)
  | type_equal_cong_validated_arrow_l : forall chk E T1 T1' T2,
      kinding_validated chk E T2 knd_type ->
      type_equal_cong_validated chk E T1 T1' knd_type ->
      environment E ->
      type T1 ->
      type T1' ->
      type T2 ->
      valid_env_validated chk E ->
      kinding_validated chk E T1 knd_type ->
      kinding_validated chk E T1' knd_type ->
      type_equal_cong_validated chk E
        (typ_arrow T1 T2) (typ_arrow T1' T2) knd_type
  | type_equal_cong_validated_arrow_r : forall chk E T1 T2 T2',
      kinding_validated chk E T1 knd_type ->
      type_equal_cong_validated chk E T2 T2' knd_type ->
      environment E ->
      type T1 ->
      type T2 ->
      type T2' ->
      valid_env_validated chk E ->
      kinding_validated chk E T2 knd_type ->
      kinding_validated chk E T2' knd_type ->
      type_equal_cong_validated chk E
        (typ_arrow T1 T2) (typ_arrow T1 T2') knd_type
  | type_equal_cong_validated_prod_l : forall chk E T1 T1' T2,
      kinding_validated chk E T2 knd_type ->
      type_equal_cong_validated chk E T1 T1' knd_type ->
      environment E ->
      type T1 ->
      type T1' ->
      type T2 ->
      valid_env_validated chk E ->
      kinding_validated chk E T1 knd_type ->
      kinding_validated chk E T1' knd_type ->
      type_equal_cong_validated chk E
        (typ_prod T1 T2) (typ_prod T1' T2) knd_type
  | type_equal_cong_validated_prod_r : forall chk E T1 T2 T2',
      kinding_validated chk E T1 knd_type ->
      type_equal_cong_validated chk E T2 T2' knd_type ->
      environment E ->
      type T1 ->
      type T2 ->
      type T2' ->
      valid_env_validated chk E ->
      kinding_validated chk E T2 knd_type ->
      kinding_validated chk E T2' knd_type ->
      type_equal_cong_validated chk E
        (typ_prod T1 T2) (typ_prod T1 T2') knd_type
  | type_equal_cong_validated_ref : forall chk E T1 T1',
      type_equal_cong_validated chk E T1 T1' knd_type ->
      environment E ->
      type T1 ->
      type T1' ->
      valid_env_validated chk E ->
      kinding_validated chk E T1 knd_type ->
      kinding_validated chk E T1' knd_type ->
      type_equal_cong_validated chk E
        (typ_ref T1) (typ_ref T1') knd_type
  | type_equal_cong_validated_meet_l : forall chk E T1 T1' T2 cs,
      kinding_validated chk E T2 (knd_row cs) ->
      type_equal_cong_validated chk E T1 T1' (knd_row cs) ->
      environment E ->
      type T1 ->
      type T1' ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env_validated chk E ->
      kinding_validated chk E T1 (knd_row cs) ->
      kinding_validated chk E T1' (knd_row cs) ->
      type_equal_cong_validated chk E
        (typ_meet T1 T2) (typ_meet T1' T2) (knd_row cs)
  | type_equal_cong_validated_meet_r : forall chk E T1 T2 T2' cs,
      kinding_validated chk E T1 (knd_row cs) ->
      type_equal_cong_validated chk E T2 T2' (knd_row cs) -> 
      environment E ->
      type T1 ->
      type T2 ->
      type T2' ->
      CSet.Nonempty cs ->
      valid_env_validated chk E ->
      kinding_validated chk E T2 (knd_row cs) ->
      kinding_validated chk E T2' (knd_row cs) ->
      type_equal_cong_validated chk E
        (typ_meet T1 T2) (typ_meet T1 T2') (knd_row cs)
  | type_equal_cong_validated_join_l : forall chk E T1 T1' T2 cs,
      kinding_validated chk E T2 (knd_row cs) ->
      type_equal_cong_validated chk E T1 T1' (knd_row cs) ->
      environment E ->
      type T1 ->
      type T1' ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env_validated chk E ->
      kinding_validated chk E T1 (knd_row cs) ->
      kinding_validated chk E T1' (knd_row cs) ->
      type_equal_cong_validated chk E
        (typ_join T1 T2) (typ_join T1' T2) (knd_row cs)
  | type_equal_cong_validated_join_r : forall chk E T1 T2 T2' cs,
      kinding_validated chk E T1 (knd_row cs) ->
      type_equal_cong_validated chk E T2 T2' (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      type T2' ->
      CSet.Nonempty cs ->
      valid_env_validated chk E ->
      kinding_validated chk E T2 (knd_row cs) ->
      kinding_validated chk E T2' (knd_row cs) ->
      type_equal_cong_validated chk E
        (typ_join T1 T2) (typ_join T1 T2') (knd_row cs)
  | type_equal_cong_validated_symm : forall chk E T1 T1' K,
      type_equal_symm_validated chk E T1 T1' K ->
      environment E ->
      type T1 ->
      type T1' ->
      kind K ->
      valid_env_validated chk E ->
      kinding_validated chk E T1 K ->
      kinding_validated chk E T1' K ->
      (chk = true -> valid_kind chk E K) ->
      type_equal_cong_validated chk E T1 T1' K

with type_equal_validated
     : bool -> env -> typ -> typ -> knd -> Prop :=
  | type_equal_validated_refl : forall chk E T K,
      kinding_validated chk E T K ->
      environment E ->
      type T ->
      kind K ->
      valid_env_validated chk E ->
      (chk = true -> valid_kind chk E K) ->
      type_equal_validated chk E T T K
  | type_equal_validated_step : forall chk E T1 T2 T3 K,
      type_equal_cong_validated chk E T1 T2 K ->
      type_equal_validated chk E T2 T3 K ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      kind K ->
      valid_env_validated chk E ->
      kinding_validated chk E T1 K ->
      kinding_validated chk E T2 K ->
      kinding_validated chk E T3 K ->
      (chk = true -> valid_kind chk E K) ->
      type_equal_validated chk E T1 T3 K

with subtype_validated : bool -> env -> typ -> typ -> cset -> Prop :=
  | subtype_validated_c : forall chk E T1 T2 cs,
      type_equal_validated chk E T1 (typ_meet T1 T2) (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env_validated chk E ->
      kinding_validated chk E T1 (knd_row cs) ->
      kinding_validated chk E T2 (knd_row cs) ->
      subtype_validated chk E T1 T2 cs.

Scheme valid_kind_validated_mutind :=
         Induction for valid_kind_validated Sort Prop
  with kinding_validated_mutind :=
         Induction for kinding_validated Sort Prop
  with valid_kinds_validated_mutind :=
         Induction for valid_kinds_validated Sort Prop
  with valid_kinds_and_type_validated_mutind :=
         Induction for valid_kinds_and_type_validated Sort Prop
  with valid_scheme_validated_mutind :=
         Induction for valid_scheme_validated Sort Prop
  with valid_env_aux_validated_mutind :=
         Induction for valid_env_aux_validated Sort Prop
  with valid_env_validated_mutind :=
         Induction for valid_env_validated Sort Prop
  with type_equal_core_validated_mutind :=
         Induction for type_equal_core_validated Sort Prop
  with type_equal_symm_validated_mutind :=
         Induction for type_equal_symm_validated Sort Prop
  with type_equal_cong_validated_mutind :=
         Induction for type_equal_cong_validated Sort Prop
  with type_equal_validated_mutind :=
         Induction for type_equal_validated Sort Prop
  with subtype_validated_mutind :=
         Induction for subtype_validated Sort Prop.

Combined Scheme combined_kinding_validated_mutind
  from valid_kind_validated_mutind, kinding_validated_mutind,
       valid_kinds_validated_mutind,
       valid_kinds_and_type_validated_mutind,
       valid_scheme_validated_mutind, valid_env_aux_validated_mutind,
       valid_env_validated_mutind, type_equal_core_validated_mutind,
       type_equal_symm_validated_mutind,
       type_equal_cong_validated_mutind,
       type_equal_validated_mutind, subtype_validated_mutind.

Lemma unvalidated_combined_kinding :
  (forall chk E K, valid_kind_validated chk E K -> valid_kind chk E K)
  /\ (forall chk E T K,
       kinding_validated chk E T K -> kinding chk E T K)
  /\ (forall chk E Ks,
       valid_kinds_validated chk E Ks -> valid_kinds chk E Ks)
  /\ (forall chk E Ks T,
       valid_kinds_and_type_validated chk E Ks T ->
       valid_kinds_and_type chk E Ks T)
  /\ (forall chk E M,
       valid_scheme_validated chk E M -> valid_scheme chk E M)
  /\ (forall E F, valid_env_aux_validated E F -> valid_env_aux E F)
  /\ (forall chk E, valid_env_validated chk E -> valid_env chk E)
  /\ (forall chk E T1 T2 K,
       type_equal_core_validated chk E T1 T2 K ->
       type_equal_core chk E T1 T2 K)
  /\ (forall chk E T1 T2 K,
       type_equal_symm_validated chk E T1 T2 K ->
       type_equal_symm chk E T1 T2 K)
  /\ (forall chk E T1 T2 K,
       type_equal_cong_validated chk E T1 T2 K ->
       type_equal_cong chk E T1 T2 K)
  /\ (forall chk E T1 T2 K,
       type_equal_validated chk E T1 T2 K -> type_equal chk E T1 T2 K)
  /\ (forall chk E T1 T2 cs,
       subtype_validated chk E T1 T2 cs -> subtype chk E T1 T2 cs).
Proof.
  apply combined_kinding_validated_mutind;
    intros; subst; econstr auto.
Qed.

Lemma unvalidated_valid_kind : forall chk E K,
    valid_kind_validated chk E K -> valid_kind chk E K.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_valid_kind.

Lemma unvalidated_kinding : forall chk E T K,
    kinding_validated chk E T K -> kinding chk E T K.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_kinding.

Lemma unvalidated_valid_kinds : forall chk E Ks,
    valid_kinds_validated chk E Ks ->
    valid_kinds chk E Ks.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_valid_kinds.

Lemma unvalidated_valid_kinds_and_type : forall chk E Ks T,
    valid_kinds_and_type_validated chk E Ks T ->
    valid_kinds_and_type chk E Ks T.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_valid_kinds_and_type.

Lemma unvalidated_valid_scheme : forall chk E M,
    valid_scheme_validated chk E M -> valid_scheme chk E M.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_valid_scheme.

Lemma unvalidated_valid_env_aux : forall E F,
    valid_env_aux_validated E F -> valid_env_aux E F.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_valid_env_aux.

Lemma unvalidated_valid_env : forall chk E,
    valid_env_validated chk E -> valid_env chk E.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_valid_env.

Lemma unvalidated_type_equal_core : forall chk E T1 T2 K,
    type_equal_core_validated chk E T1 T2 K ->
    type_equal_core chk E T1 T2 K.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_type_equal_core.

Lemma unvalidated_type_equal_symm : forall chk E T1 T2 K,
    type_equal_symm_validated chk E T1 T2 K ->
    type_equal_symm chk E T1 T2 K.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_type_equal_symm.

Lemma unvalidated_type_equal_cong : forall chk E T1 T2 K,
    type_equal_cong_validated chk E T1 T2 K ->
    type_equal_cong chk E T1 T2 K.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_type_equal_cong.

Lemma unvalidated_type_equal : forall chk E T1 T2 K,
    type_equal_validated chk E T1 T2 K -> type_equal chk E T1 T2 K.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_type_equal.

Lemma unvalidated_subtype : forall chk E T1 T2 K,
    subtype_validated chk E T1 T2 K -> subtype chk E T1 T2 K.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_subtype.

Lemma valid_kind_validated_inv : forall chk E K,
    valid_kind_validated chk E K ->
    valid_env_validated chk E.
Proof.
  introv Hv.
  induction Hv; auto.
Qed.

Hint Constructors valid_kind_validated : valid_kind_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_kind_validated _ E _ |- _ =>
      apply (proj1 (valid_kind_regular_inv
               (regular_valid_kind (unvalidated_valid_kind H))))
  end : valid_kind_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : valid_kind_validated _ _ K |- _ =>
      apply (proj2 (valid_kind_regular_inv
               (regular_valid_kind (unvalidated_valid_kind H))))
  end : valid_kind_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : valid_kind_validated _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj2 (valid_kind_regular_inv
                   (regular_valid_kind (unvalidated_valid_kind H))));
      inversion Hknd; assumption
  end : valid_kind_regular.

Hint Extern 1 (valid_env_validated ?chk ?E) =>
  match goal with
  | H : valid_kind_validated chk E _ |- _ =>
      apply (valid_kind_validated_inv H)
  end : valid_kind_validated.

Hint Extern 1 (valid_env ?chk ?E) =>
  match goal with
  | H : valid_kind_validated chk E _ |- _ =>
      apply (unvalidated_valid_env (valid_kind_validated_inv H))
  end : valid_kind_validated.

Lemma kinding_validated_inv : forall chk E T K,
    kinding_validated chk E T K ->
    valid_env_validated chk E.
Proof.
  introv Hk.
  destruct Hk; subst;
    auto with valid_kind_validated csetdec.
Qed.

Lemma kinding_validated_checked_inv : forall E T K,
    kinding_validated true E T K ->
    valid_env_validated true E /\ valid_kind true E K.
Proof.
  introv Hk.
  remember true as chk.
  split; destruct Hk; subst;
    auto with valid_kind_validated csetdec.
Qed.

Hint Constructors kinding_validated : kinding_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : kinding_validated _ E _ _ |- _ =>
      apply (proj31 (kinding_regular_inv
               (regular_kinding (unvalidated_kinding H))))
  end : kinding_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : kinding_validated _ _ T _ |- _ =>
      apply (proj32 (kinding_regular_inv
               (regular_kinding (unvalidated_kinding H))))
  end : kinding_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : kinding_validated _ _ _ K |- _ =>
      apply (proj33 (kinding_regular_inv 
               (regular_kinding (unvalidated_kinding H))))
  end : kinding_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : kinding_validated _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj33 (kinding_regular_inv 
                    (regular_kinding (unvalidated_kinding H))));
      inversion Hknd; assumption
  end : kinding_regular.

Hint Extern 1 (valid_env_validated ?chk ?E) =>
  match goal with
  | H : kinding_validated chk E _ _ |- _ =>
      apply (kinding_validated_inv H)
  end : kinding_validated.

Hint Extern 1 (valid_env ?chk ?E) =>
  match goal with
  | H : kinding_validated chk E _ _ |- _ =>
      apply (unvalidated_valid_env (kinding_validated_inv H))
  end : kinding_validated.

Hint Extern 1 (valid_kind true ?E ?K) =>
  match goal with
  | H : kinding_validated true E _ K |- _ =>
      apply (proj2 (kinding_validated_checked_inv H))
  end : kinding_validated.

Lemma valid_kinds_validated_inv : forall chk E Ks,
    valid_kinds_validated chk E Ks ->
    valid_env_validated chk E.
Proof.
  introv Hv.
  induction Hv; auto.
Qed.

Hint Constructors valid_kinds_validated : valid_kinds_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_kinds_validated _ E _ |- _ =>
      apply (proj1 (valid_kinds_regular_inv
               (regular_valid_kinds (unvalidated_valid_kinds H))))
  end : valid_kinds_regular.

Hint Extern 1 (kinds ?Ks) =>
  match goal with
  | H : valid_kinds_validated _ _ Ks |- _ =>
      apply (proj2 (valid_kinds_regular_inv
               (regular_valid_kinds (unvalidated_valid_kinds H))))
  end : valid_kinds_regular.

Hint Extern 1 (valid_env_validated ?chk ?E) =>
  match goal with
  | H : valid_kinds_validated chk E _ |- _ =>
      apply (valid_kinds_validated_inv H)
  end : valid_kinds_validated.

Hint Extern 1 (valid_env ?chk ?E) =>
  match goal with
  | H : valid_kinds_validated chk E _ |- _ =>
      apply (unvalidated_valid_env (valid_kinds_validated_inv H))
  end : valid_kinds_validated.

Lemma valid_kinds_and_type_validated_inv : forall chk E Ks T,
    valid_kinds_and_type_validated chk E Ks T ->
    valid_env_validated chk E.
Proof.
  introv Hv.
  induction Hv; auto.
Qed.

Hint Constructors valid_kinds_and_type_validated
  : valid_kinds_and_type_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_kinds_and_type_validated _ E _ _ |- _ =>
      apply (proj31 (valid_kinds_and_type_regular_inv
               (regular_valid_kinds_and_type
                  (unvalidated_valid_kinds_and_type H))))
  end : valid_kinds_and_type_regular.

Hint Extern 1 (kinds ?Ks) =>
  match goal with
  | H : valid_kinds_and_type_validated _ _ Ks _ |- _ =>
      apply (proj32 (valid_kinds_and_type_regular_inv
               (regular_valid_kinds_and_type
                  (unvalidated_valid_kinds_and_type H))))
  end : valid_kinds_and_type_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : valid_kinds_and_type_validated _ _ _ T |- _ =>
      apply (proj33 (valid_kinds_and_type_regular_inv
               (regular_valid_kinds_and_type
                  (unvalidated_valid_kinds_and_type H))))
  end : valid_kinds_and_type_regular.

Hint Extern 1 (valid_env_validated ?chk ?E) =>
  match goal with
  | H : valid_kinds_and_type_validated chk E _ _ |- _ =>
      apply (valid_kinds_and_type_validated_inv H)
  end : valid_kinds_and_type_validated.

Hint Extern 1 (valid_env ?chk ?E) =>
  match goal with
  | H : valid_kinds_and_type_validated chk E _ _ |- _ =>
      apply (unvalidated_valid_env
               (valid_kinds_and_type_validated_inv H))
  end : valid_kinds_and_type_validated.

Lemma valid_scheme_validated_inv : forall chk E M,
    valid_scheme_validated chk E M ->
    valid_env_validated chk E.
Proof.
  introv Hs.
  destruct Hs; auto.
Qed.

Hint Constructors valid_scheme_validated : valid_scheme_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_scheme_validated _ E _ |- _ =>
      apply (proj1 (valid_scheme_regular_inv
               (regular_valid_scheme (unvalidated_valid_scheme H))))
  end : valid_scheme_regular.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H : valid_scheme_validated _ _ M |- _ =>
      apply (proj2 (valid_scheme_regular_inv
               (regular_valid_scheme (unvalidated_valid_scheme H))))
  end : valid_scheme_regular.

Hint Extern 1 (valid_env_validated ?chk ?E) =>
  match goal with
  | H : valid_scheme_validated chk E _ |- _ =>
      apply (valid_scheme_validated_inv H)
  end : valid_scheme_validated.

Hint Extern 1 (valid_env ?chk ?E) =>
  match goal with
  | H : valid_scheme_validated chk E _ |- _ =>
      apply (unvalidated_valid_env (valid_scheme_validated_inv H))
  end : valid_scheme_validated.

Hint Constructors valid_env_aux_validated : valid_env_aux_validated.

Hint Constructors valid_env_validated : valid_env_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_env_validated _ E |- _ =>
      apply (valid_env_regular_inv
               (regular_valid_env (unvalidated_valid_env H)))
  end : valid_env_regular.

Lemma type_equal_core_validated_inv : forall chk E T1 T2 K,
    type_equal_core_validated chk E T1 T2 K ->
    valid_env_validated chk E
    /\ kinding_validated chk E T1 K
    /\ kinding_validated chk E T2 K.
Proof.
  introv Hte.
  destruct Hte; subst; splits;
    auto;
    econstr solve
     [ auto with kinding_validated
     | csetdec
     | eauto with kinding_validated ].
Qed.

Lemma type_equal_core_validated_checked_inv : forall E T1 T2 K,
    type_equal_core_validated true E T1 T2 K ->
    valid_env_validated true E
    /\ kinding_validated true E T1 K
    /\ kinding_validated true E T2 K
    /\ valid_kind true E K.
Proof.
  introv Hte.
  destruct (type_equal_core_validated_inv Hte) as [? [? ?]].
  remember true as chk.
  destruct Hte; subst; splits; auto with csetdec.
Qed.

Hint Constructors type_equal_core_validated
  : type_equal_core_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_core_validated _ E _ _ _ |- _ =>
      apply (proj41 (type_equal_core_regular_inv
        (regular_type_equal_core (unvalidated_type_equal_core H))))
  end : type_equal_core_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_core_validated _ _ T _ _ |- _ =>
      apply (proj42 (type_equal_core_regular_inv
        (regular_type_equal_core (unvalidated_type_equal_core H))))
  | H : type_equal_core_validated _ _ _ T _ |- _ =>
      apply (proj43 (type_equal_core_regular_inv
        (regular_type_equal_core (unvalidated_type_equal_core H))))
  end : type_equal_core_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_core_validated _ _ _ _ K |- _ =>
      apply (proj44 (type_equal_core_regular_inv
        (regular_type_equal_core (unvalidated_type_equal_core H))))
  end : type_equal_core_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_core_validated _ _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_core_regular_inv
         (regular_type_equal_core (unvalidated_type_equal_core H))));
      inversion Hknd; assumption
  end : type_equal_core_regular.

Hint Extern 1 (valid_env_validated ?chk ?E) =>
  match goal with
  | H : type_equal_core_validated chk E _ _ _ |- _ =>
      apply (proj31 (type_equal_core_validated_inv H))
  end : type_equal_core_validated.

Hint Extern 1 (kinding_validated ?chk ?E ?T ?K) =>
  match goal with
  | H : type_equal_core_validated chk E T _ K |- _ =>
      apply (proj32 (type_equal_core_validated_inv H))
  | H : type_equal_core_validated chk E _ T K |- _ =>
      apply (proj33 (type_equal_core_validated_inv H))
  end : type_equal_core_validated.

Hint Extern 1 (valid_env ?chk ?E) =>
  match goal with
  | H : type_equal_core_validated chk E _ _ _ |- _ =>
      apply (unvalidated_valid_env
               (proj31 (type_equal_core_validated_inv H)))
  end : type_equal_core_regular.

Hint Extern 1 (kinding ?chk ?E ?T ?K) =>
  match goal with
  | H : type_equal_core_validated chk E T _ K |- _ =>
      apply (unvalidated_kinding
               (proj32 (type_equal_core_validated_inv H)))
  | H : type_equal_core_validated chk E _ T K |- _ =>
      apply (unvalidated_kinding
               (proj33 (type_equal_core_validated_inv H)))
  end : type_equal_core_validated.

Hint Extern 1 (valid_kind true ?E ?K) =>
  match goal with
  | H : type_equal_core_validated true E _ _ K |- _ =>
      apply (proj44 (type_equal_core_validated_checked_inv H))
  end : type_equal_core_validated.

Lemma type_equal_symm_validated_inv : forall chk E T1 T2 K,
    type_equal_symm_validated chk E T1 T2 K ->
    valid_env_validated chk E
    /\ kinding_validated chk E T1 K
    /\ kinding_validated chk E T2 K.
Proof.
  introv Hte.
  destruct Hte; auto.
Qed.

Lemma type_equal_symm_validated_checked_inv : forall E T1 T2 K,
    type_equal_symm_validated true E T1 T2 K ->
    valid_env_validated true E
    /\ kinding_validated true E T1 K
    /\ kinding_validated true E T2 K
    /\ valid_kind true E K.
Proof.
  introv Hte.
  remember true as chk.
  destruct Hte; subst; auto.
Qed.

Hint Constructors type_equal_symm_validated
  : type_equal_symm_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_symm_validated _ E _ _ _ |- _ =>
      apply (proj41 (type_equal_symm_regular_inv
        (regular_type_equal_symm (unvalidated_type_equal_symm H))))
  end : type_equal_symm_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_symm_validated _ _ T _ _ |- _ =>
      apply (proj42 (type_equal_symm_regular_inv
        (regular_type_equal_symm (unvalidated_type_equal_symm H))))
  | H : type_equal_symm_validated _ _ _ T _ |- _ =>
      apply (proj43 (type_equal_symm_regular_inv
        (regular_type_equal_symm (unvalidated_type_equal_symm H))))
  end : type_equal_symm_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_symm_validated _ _ _ _ K |- _ =>
      apply (proj44 (type_equal_symm_regular_inv
        (regular_type_equal_symm (unvalidated_type_equal_symm H))))
  end : type_equal_symm_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_symm_validated _ _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_symm_regular_inv
         (regular_type_equal_symm (unvalidated_type_equal_symm H))));
      inversion Hknd; assumption
  end : type_equal_symm_regular.

Hint Extern 1 (valid_env_validated ?chk ?E) =>
  match goal with
  | H : type_equal_symm_validated chk E _ _ _ |- _ =>
      apply (proj31 (type_equal_symm_validated_inv H))
  end : type_equal_symm_validated.

Hint Extern 1 (kinding_validated ?chk ?E ?T ?K) =>
  match goal with
  | H : type_equal_symm_validated chk E T _ K |- _ =>
      apply (proj32 (type_equal_symm_validated_inv H))
  | H : type_equal_symm_validated chk E _ T K |- _ =>
      apply (proj33 (type_equal_symm_validated_inv H))
  end : type_equal_symm_validated.

Hint Extern 1 (valid_env ?chk ?E) =>
  match goal with
  | H : type_equal_symm_validated chk E _ _ _ |- _ =>
      apply (unvalidated_valid_env
               (proj31 (type_equal_symm_validated_inv H)))
  end : type_equal_symm_regular.

Hint Extern 1 (kinding ?chk ?E ?T ?K) =>
  match goal with
  | H : type_equal_symm_validated chk E T _ K |- _ =>
      apply (unvalidated_kinding
               (proj32 (type_equal_symm_validated_inv H)))
  | H : type_equal_symm_validated chk E _ T K |- _ =>
      apply (unvalidated_kinding
               (proj33 (type_equal_symm_validated_inv H)))
  end : type_equal_symm_validated.

Hint Extern 1 (valid_kind true ?E ?K) =>
  match goal with
  | H : type_equal_symm_validated true E _ _ K |- _ =>
      apply (proj44 (type_equal_symm_validated_checked_inv H))
  end : type_equal_symm_validated.

Lemma type_equal_cong_validated_inv : forall chk E T1 T2 K,
    type_equal_cong_validated chk E T1 T2 K ->
    valid_env_validated chk E
    /\ kinding_validated chk E T1 K
    /\ kinding_validated chk E T2 K.
Proof.
  introv Hte.
  destruct Hte; splits;
    eauto with kinding_validated.
Qed.

Lemma type_equal_cong_validated_checked_inv : forall E T1 T2 K,
    type_equal_cong_validated true E T1 T2 K ->
    valid_env_validated true E
    /\ kinding_validated true E T1 K
    /\ kinding_validated true E T2 K
    /\ valid_kind true E K.
Proof.
  introv Hte.
  remember true as chk.
  destruct Hte; subst; splits;
    auto with csetdec;
    eauto with kinding_validated.
Qed.

Hint Constructors type_equal_cong_validated
  : type_equal_cong_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_cong_validated _ E _ _ _ |- _ =>
      apply (proj41 (type_equal_cong_regular_inv
        (regular_type_equal_cong (unvalidated_type_equal_cong H))))
  end : type_equal_cong_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_cong_validated _ _ T _ _ |- _ =>
      apply (proj42 (type_equal_cong_regular_inv
        (regular_type_equal_cong (unvalidated_type_equal_cong H))))
  | H : type_equal_cong_validated _ _ _ T _ |- _ =>
      apply (proj43 (type_equal_cong_regular_inv
        (regular_type_equal_cong (unvalidated_type_equal_cong H))))
  end : type_equal_cong_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_cong_validated _ _ _ _ K |- _ =>
      apply (proj44 (type_equal_cong_regular_inv
        (regular_type_equal_cong (unvalidated_type_equal_cong H))))
  end : type_equal_cong_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_cong_validated _ _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_cong_regular_inv
         (regular_type_equal_cong (unvalidated_type_equal_cong H))));
      inversion Hknd; assumption
  end : type_equal_cong_regular.

Hint Extern 1 (valid_env_validated ?chk ?E) =>
  match goal with
  | H : type_equal_cong_validated chk E _ _ _ |- _ =>
      apply (proj31 (type_equal_cong_validated_inv H))
  end : type_equal_cong_validated.

Hint Extern 1 (kinding_validated ?chk ?E ?T ?K) =>
  match goal with
  | H : type_equal_cong_validated chk E T _ K |- _ =>
      apply (proj32 (type_equal_cong_validated_inv H))
  | H : type_equal_cong_validated chk E _ T K |- _ =>
      apply (proj33 (type_equal_cong_validated_inv H))
  end : type_equal_cong_validated.

Hint Extern 1 (valid_env ?chk ?E) =>
  match goal with
  | H : type_equal_cong_validated chk E _ _ _ |- _ =>
      apply (unvalidated_valid_env
               (proj31 (type_equal_cong_validated_inv H)))
  end : type_equal_cong_regular.

Hint Extern 1 (kinding ?chk ?E ?T ?K) =>
  match goal with
  | H : type_equal_cong_validated chk E T _ K |- _ =>
      apply (unvalidated_kinding
               (proj32 (type_equal_cong_validated_inv H)))
  | H : type_equal_cong_validated chk E _ T K |- _ =>
      apply (unvalidated_kinding
               (proj33 (type_equal_cong_validated_inv H)))
  end : type_equal_cong_validated.

Hint Extern 1 (valid_kind true ?E ?K) =>
  match goal with
  | H : type_equal_cong_validated true E _ _ K |- _ =>
      apply (proj44 (type_equal_cong_validated_checked_inv H))
  end : type_equal_cong_validated.

Lemma type_equal_validated_inv : forall chk E T1 T2 K,
    type_equal_validated chk E T1 T2 K ->
    valid_env_validated chk E
    /\ kinding_validated chk E T1 K
    /\ kinding_validated chk E T2 K.
Proof.
  introv Hk.
  destruct Hk; auto.
Qed.

Lemma type_equal_validated_checked_inv : forall E T1 T2 K,
    type_equal_validated true E T1 T2 K ->
    valid_env_validated true E
    /\ kinding_validated true E T1 K
    /\ kinding_validated true E T2 K
    /\ valid_kind true E K.
Proof.
  introv Hk.
  remember true as chk.
  destruct Hk; subst; auto.
Qed.

Hint Constructors type_equal_validated : type_equal_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_validated _ E _ _ _ |- _ =>
      apply (proj41 (type_equal_regular_inv
        (regular_type_equal (unvalidated_type_equal H))))
  end : type_equal_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_validated _ _ T _ _ |- _ =>
      apply (proj42 (type_equal_regular_inv
        (regular_type_equal (unvalidated_type_equal H))))
  | H : type_equal_validated _ _ _ T _ |- _ =>
      apply (proj43 (type_equal_regular_inv
        (regular_type_equal (unvalidated_type_equal H))))
  end : type_equal_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_validated _ _ _ _ K |- _ =>
      apply (proj44 (type_equal_regular_inv
        (regular_type_equal (unvalidated_type_equal H))))
  end : type_equal_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_validated _ _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_regular_inv
         (regular_type_equal (unvalidated_type_equal H))));
      inversion Hknd; assumption
  end : type_equal_regular.

Hint Extern 1 (valid_env_validated ?chk ?E) =>
  match goal with
  | H : type_equal_validated chk E _ _ _ |- _ =>
      apply (proj31 (type_equal_validated_inv H))
  end : type_equal_validated.

Hint Extern 1 (kinding_validated ?chk ?E ?T ?K) =>
  match goal with
  | H : type_equal_validated chk E T _ K |- _ =>
      apply (proj32 (type_equal_validated_inv H))
  | H : type_equal_validated chk E _ T K |- _ =>
      apply (proj33 (type_equal_validated_inv H))
  end : type_equal_validated.

Hint Extern 1 (valid_env ?chk ?E) =>
  match goal with
  | H : type_equal_validated chk E _ _ _ |- _ =>
      apply (unvalidated_valid_env
               (proj31 (type_equal_validated_inv H)))
  end : type_equal_validated.

Hint Extern 1 (kinding ?chk ?E ?T ?K) =>
  match goal with
  | H : type_equal_validated chk E T _ K |- _ =>
      apply (unvalidated_kinding
               (proj32 (type_equal_validated_inv H)))
  | H : type_equal_validated chk E _ T K |- _ =>
      apply (unvalidated_kinding
               (proj33 (type_equal_validated_inv H)))
  end : type_equal_validated.

Hint Extern 1 (valid_kind true ?E ?K) =>
  match goal with
  | H : type_equal_validated true E _ _ K |- _ =>
      apply (proj44 (type_equal_validated_checked_inv H))
  end : type_equal_validated.

Lemma subtype_validated_inv : forall chk E T1 T2 cs,
    subtype_validated chk E T1 T2 cs ->
    valid_env_validated chk E
    /\ kinding_validated chk E T1 (knd_row cs)
    /\ kinding_validated chk E T2 (knd_row cs).
Proof.
  introv Hk.
  destruct Hk; auto.
Qed.

Hint Constructors subtype_validated : subtype_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : subtype_validated _ E _ _ _ |- _ =>
      apply (proj41 (subtype_regular_inv
        (regular_subtype (unvalidated_subtype H))))
  end : subtype_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : subtype_validated _ _ T _ _ |- _ =>
      apply (proj42 (subtype_regular_inv
        (regular_subtype (unvalidated_subtype H))))
  | H : subtype_validated _ _ _ T _ |- _ =>
      apply (proj43 (subtype_regular_inv
        (regular_subtype (unvalidated_subtype H))))
  end : subtype_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : subtype_validated _ _ _ _ cs |- _ =>
      apply (proj44 (subtype_regular_inv
        (regular_subtype (unvalidated_subtype H))))
  end : subtype_regular.

Hint Extern 1 (valid_env_validated ?chk ?E) =>
  match goal with
  | H : subtype_validated chk E _ _ _ |- _ =>
      apply (proj31 (subtype_validated_inv H))
  end : subtype_validated.

Hint Extern 1 (kinding_validated ?chk ?E ?T (knd_row ?cs)) =>
  match goal with
  | H : subtype_validated chk E T _ cs |- _ =>
      apply (proj32 (subtype_validated_inv H))
  | H : subtype_validated chk E _ T cs |- _ =>
      apply (proj33 (subtype_validated_inv H))
  end : subtype_validated.

Hint Extern 1 (valid_env ?chk ?E) =>
  match goal with
  | H : subtype_validated chk E _ _ _ |- _ =>
      apply (unvalidated_valid_env (proj31 (subtype_validated_inv H)))
  end : subtype_validated.

Hint Extern 1 (kinding ?chk ?E ?T (knd_row ?cs)) =>
  match goal with
  | H : subtype_validated chk E T _ cs |- _ =>
      apply (unvalidated_kinding (proj32 (subtype_validated_inv H)))
  | H : subtype_validated chk E _ T cs |- _ =>
      apply (unvalidated_kinding (proj33 (subtype_validated_inv H)))
  end : subtype_validated.

Lemma validated_combined_kinding_regular :
     (forall chk E K,
       valid_kind_regular chk E K -> valid_kind_validated chk E K)
  /\ (forall chk E T K,
       kinding_regular chk E T K -> kinding_validated chk E T K)
  /\ (forall chk E Ks,
       valid_kinds_regular chk E Ks -> valid_kinds_validated chk E Ks)
  /\ (forall chk E Ks T,
       valid_kinds_and_type_regular chk E Ks T ->
       valid_kinds_and_type_validated chk E Ks T)
  /\ (forall chk E M,
       valid_scheme_regular chk E M ->
       valid_scheme_validated chk E M)
  /\ (forall E F,
       valid_env_aux_regular E F -> valid_env_aux_validated E F)
  /\ (forall chk E,
       valid_env_regular chk E -> valid_env_validated chk E)
  /\ (forall chk E T1 T2 K,
       type_equal_core_regular chk E T1 T2 K ->
       type_equal_core_validated chk E T1 T2 K)
  /\ (forall chk E T1 T2 K,
       type_equal_symm_regular chk E T1 T2 K ->
       type_equal_symm_validated chk E T1 T2 K)
  /\ (forall chk E T1 T2 K,
       type_equal_cong_regular chk E T1 T2 K ->
       type_equal_cong_validated chk E T1 T2 K)
  /\ (forall chk E T1 T2 K,
       type_equal_regular chk E T1 T2 K ->
       type_equal_validated chk E T1 T2 K)
  /\ (forall chk E T1 T2 cs,
       subtype_regular chk E T1 T2 cs ->
       subtype_validated chk E T1 T2 cs).
Proof.
  apply combined_kinding_regular_mutind; intros; auto;
    econstr auto with valid_kind_validated kinding_validated
           valid_kinds_validated valid_kinds_and_type_validated
           valid_scheme_validated
           valid_env_validated type_equal_core_validated
           type_equal_symm_validated type_equal_cong_validated
           type_equal_validated subtype_validated.
  - apply kinding_validated_var; auto.
    destruct chk; try discriminate.
    eauto using valid_kind_from_env.
  - destruct chk.
    + assert (valid_kind true E (knd_range T1 T2)) as Hknd
        by auto with kinding_validated.
      inversion Hknd; subst.
      assert (subtype true E T2' T1' CSet.universe)
        by (apply subtype_unvalidated_transitive with (T2 := T2);
              auto with subtype_validated;
            apply subtype_unvalidated_transitive with (T2 := T1);
             auto with subtype_validated).
      apply kinding_validated_range_subsumption
        with (T1 := T1) (T2 := T2);
        auto with subtype_validated.
    + apply kinding_validated_range_subsumption
        with (T1 := T1) (T2 := T2);
        try discriminate; auto with subtype_validated.
  - apply type_equal_symm_validated_l;
      destruct chk; try discriminate;
      auto with type_equal_core_validated.
  - apply type_equal_symm_validated_r;
      destruct chk; try discriminate;
      auto with type_equal_core_validated.
  - apply type_equal_cong_validated_symm;
      destruct chk; try discriminate;
      auto with type_equal_symm_validated.
  - apply type_equal_validated_refl;
      destruct chk; try discriminate;
      auto with kinding_validated.
  - apply type_equal_validated_step with (T2 := T2);
      destruct chk; try discriminate;
      auto with type_equal_validated type_equal_cong_validated.
  - assert (kinding_validated chk E (typ_meet T1 T2) (knd_row cs))
      as Hk by auto with type_equal_validated.
    inversion Hk; subst.
    auto with subtype_validated type_equal_validated.
Qed.

Lemma validated_valid_kind : forall chk E K,
    valid_kind chk E K -> valid_kind_validated chk E K.
Proof.
  introv Hv.
  apply regular_valid_kind in Hv.
  pose validated_combined_kinding_regular.
  intuition auto.
Qed.

Hint Extern 1 (valid_env ?chk ?E) =>
  match goal with
  | H : valid_kind chk E _ |- _ =>
      apply (unvalidated_valid_env
               (valid_kind_validated_inv (validated_valid_kind H)))
  end : valid_kind_validated.

Lemma validated_kinding : forall chk E T K,
    kinding chk E T K -> kinding_validated chk E T K.
Proof.
  introv Hk.
  apply regular_kinding in Hk.
  pose validated_combined_kinding_regular.
  intuition auto.
Qed.

Hint Extern 1 (valid_env ?chk ?E) =>
  match goal with
  | H : kinding chk E _ _ |- _ =>
      apply (unvalidated_valid_env
               (kinding_validated_inv (validated_kinding H)))
  end : kinding_validated.

Hint Extern 1 (valid_kind true ?E ?K) =>
  match goal with
  | H : kinding true E _ K |- _ =>
      apply (proj2 (kinding_validated_checked_inv
                      (validated_kinding H)))
  end : kinding_validated.

Lemma validated_valid_kinds : forall chk E Ks,
    valid_kinds chk E Ks -> valid_kinds_validated chk E Ks.
Proof.
  introv Hv.
  apply regular_valid_kinds in Hv.
  pose validated_combined_kinding_regular.
  intuition auto.
Qed.

Hint Extern 1 (valid_env ?chk ?E) =>
  match goal with
  | H : valid_kinds chk E _ |- _ =>
      apply (unvalidated_valid_env
               (valid_kinds_validated_inv (validated_valid_kinds H)))
  end : valid_kinds_validated.

Lemma validated_valid_kinds_and_type : forall chk E Ks T,
    valid_kinds_and_type chk E Ks T ->
    valid_kinds_and_type_validated chk E Ks T.
Proof.
  introv Hv.
  apply regular_valid_kinds_and_type in Hv.
  pose validated_combined_kinding_regular.
  intuition auto.
Qed.

Hint Extern 1 (valid_env ?chk ?E) =>
  match goal with
  | H : valid_kinds_and_type chk E _ |- _ =>
      apply (unvalidated_valid_env
               (valid_kinds_and_type_validated_inv
                  (validated_valid_kinds_and_type H)))
  end : valid_kinds_and_type_validated.

Lemma validated_valid_scheme : forall chk E M,
    valid_scheme chk E M -> valid_scheme_validated chk E M.
Proof.
  introv Hv.
  apply regular_valid_scheme in Hv.
  pose validated_combined_kinding_regular.
  intuition auto.
Qed.

Hint Extern 1 (valid_env ?chk ?E) =>
  match goal with
  | H : valid_scheme chk E _ |- _ =>
      apply (unvalidated_valid_env
               (valid_scheme_validated_inv
                  (validated_valid_scheme H)))
  end : valid_scheme_validated.

Lemma validated_valid_env_aux : forall E F,
    valid_env_aux E F -> valid_env_aux_validated E F.
Proof.
  introv Hv.
  apply regular_valid_env_aux in Hv.
  pose validated_combined_kinding_regular.
  intuition auto.
Qed.

Lemma validated_valid_env : forall chk E,
    valid_env chk E -> valid_env_validated chk E.
Proof.
  introv Hv.
  apply regular_valid_env in Hv.
  pose validated_combined_kinding_regular.
  intuition auto.
Qed.

Lemma validated_type_equal_core : forall chk E T1 T2 K,
    type_equal_core chk E T1 T2 K ->
    type_equal_core_validated chk E T1 T2 K.
Proof.
  introv He.
  apply regular_type_equal_core in He.
  pose validated_combined_kinding_regular.
  intuition auto.
Qed.

Hint Extern 1 (valid_env ?chk ?E) =>
  match goal with
  | H : type_equal_core chk E _ _ _ |- _ =>
      apply (unvalidated_valid_env
               (proj31 (type_equal_core_validated_inv
                          (validated_type_equal_core H))))
  end : type_equal_core_regular.

Hint Extern 1 (kinding ?chk ?E ?T ?K) =>
  match goal with
  | H : type_equal_core chk E T _ K |- _ =>
      apply (unvalidated_kinding
               (proj32 (type_equal_core_validated_inv
                          (validated_type_equal_core H))))
  | H : type_equal_core chk E _ T K |- _ =>
      apply (unvalidated_kinding
               (proj33 (type_equal_core_validated_inv
                          (validated_type_equal_core H))))
  end : type_equal_core_validated.

Hint Extern 1 (valid_kind true ?E ?K) =>
  match goal with
  | H : type_equal_core true E _ _ K |- _ =>
      apply (proj44 (type_equal_core_validated_checked_inv
                          (validated_type_equal_core H)))
  end : type_equal_core_validated.

Lemma validated_type_equal_symm : forall chk E T1 T2 K,
    type_equal_symm chk E T1 T2 K ->
    type_equal_symm_validated chk E T1 T2 K.
Proof.
  introv He.
  apply regular_type_equal_symm in He.
  pose validated_combined_kinding_regular.
  intuition auto.
Qed.

Hint Extern 1 (valid_env ?chk ?E) =>
  match goal with
  | H : type_equal_symm chk E _ _ _ |- _ =>
      apply (unvalidated_valid_env
               (proj31 (type_equal_symm_validated_inv
                          (validated_type_equal_symm H))))
  end : type_equal_symm_regular.

Hint Extern 1 (kinding ?chk ?E ?T ?K) =>
  match goal with
  | H : type_equal_symm chk E T _ K |- _ =>
      apply (unvalidated_kinding
               (proj32 (type_equal_symm_validated_inv
                          (validated_type_equal_symm H))))
  | H : type_equal_symm chk E _ T K |- _ =>
      apply (unvalidated_kinding
               (proj33 (type_equal_symm_validated_inv
                          (validated_type_equal_symm H))))
  end : type_equal_symm_validated.

Hint Extern 1 (valid_kind true ?E ?K) =>
  match goal with
  | H : type_equal_symm true E _ _ K |- _ =>
      apply (proj44 (type_equal_symm_validated_checked_inv
                          (validated_type_equal_symm H)))
  end : type_equal_symm_validated.

Lemma validated_type_equal_cong : forall chk E T1 T2 K,
    type_equal_cong chk E T1 T2 K ->
    type_equal_cong_validated chk E T1 T2 K.
Proof.
  introv He.
  apply regular_type_equal_cong in He.
  pose validated_combined_kinding_regular.
  intuition auto.
Qed.

Hint Extern 1 (valid_env ?chk ?E) =>
  match goal with
  | H : type_equal_cong chk E _ _ _ |- _ =>
      apply (unvalidated_valid_env
               (proj31 (type_equal_cong_validated_inv
                          (validated_type_equal_cong H))))
  end : type_equal_cong_regular.

Hint Extern 1 (kinding ?chk ?E ?T ?K) =>
  match goal with
  | H : type_equal_cong chk E T _ K |- _ =>
      apply (unvalidated_kinding
               (proj32 (type_equal_cong_validated_inv
                          (validated_type_equal_cong H))))
  | H : type_equal_cong chk E _ T K |- _ =>
      apply (unvalidated_kinding
               (proj33 (type_equal_cong_validated_inv
                          (validated_type_equal_cong H))))
  end : type_equal_cong_validated.

Hint Extern 1 (valid_kind true ?E ?K) =>
  match goal with
  | H : type_equal_cong true E _ _ K |- _ =>
      apply (proj44 (type_equal_cong_validated_checked_inv
                          (validated_type_equal_cong H)))
  end : type_equal_cong_validated.

Lemma validated_type_equal : forall chk E T1 T2 K,
    type_equal chk E T1 T2 K ->
    type_equal_validated chk E T1 T2 K.
Proof.
  introv He.
  apply regular_type_equal in He.
  pose validated_combined_kinding_regular.
  intuition auto.
Qed.

Hint Extern 1 (valid_env ?chk ?E) =>
  match goal with
  | H : type_equal chk E _ _ _ |- _ =>
      apply (unvalidated_valid_env
               (proj31 (type_equal_validated_inv
                          (validated_type_equal H))))
  end : type_equal_validated.

Hint Extern 1 (kinding ?chk ?E ?T ?K) =>
  match goal with
  | H : type_equal chk E T _ K |- _ =>
      apply (unvalidated_kinding
               (proj32 (type_equal_validated_inv
                          (validated_type_equal H))))
  | H : type_equal chk E _ T K |- _ =>
      apply (unvalidated_kinding
               (proj33 (type_equal_validated_inv
                          (validated_type_equal H))))
  end : type_equal_validated.

Hint Extern 1 (valid_kind true ?E ?K) =>
  match goal with
  | H : type_equal true E _ _ K |- _ =>
      apply (proj44 (type_equal_validated_checked_inv
                       (validated_type_equal H)))
  end : type_equal_validated.

Lemma validated_subtype : forall chk E T1 T2 K,
    subtype chk E T1 T2 K -> subtype_validated chk E T1 T2 K.
Proof.
  introv Hs.
  apply regular_subtype in Hs.
  pose validated_combined_kinding_regular.
  intuition auto.
Qed.

Hint Extern 1 (valid_env ?chk ?E) =>
  match goal with
  | H : subtype chk E _ _ _ |- _ =>
      apply (unvalidated_valid_env
               (proj31 (subtype_validated_inv (validated_subtype H))))
  end : subtype_validated.

Hint Extern 1 (kinding ?chk ?E ?T (knd_row ?cs)) =>
  match goal with
  | H : subtype chk E T _ cs |- _ =>
      apply (unvalidated_kinding
               (proj32 (subtype_validated_inv (validated_subtype H))))
  | H : subtype chk E _ T cs |- _ =>
      apply (unvalidated_kinding
               (proj33 (subtype_validated_inv (validated_subtype H))))
  end : subtype_validated.

Inductive kindings_validated
  : bool -> env -> list typ -> list knd -> Prop :=
  | kindings_validated_nil : forall chk E,
      valid_env chk E ->
      environment E ->
      kindings_validated chk E nil nil
  | kindings_validated_cons : forall chk E T Ts K Ks,
      kinding chk E T K ->
      kindings_validated chk E Ts Ks ->
      environment E ->
      type T ->
      types Ts ->
      kind K ->
      kinds Ks ->
      valid_env chk E ->
      (chk = true -> valid_kind chk E K) ->
      (chk = true -> valid_kinds chk E Ks) ->
      kindings_validated chk E (T :: Ts) (K :: Ks).

Lemma unvalidated_kindings : forall chk E Ts Ks,
    kindings_validated chk E Ts Ks -> kindings chk E Ts Ks.
Proof.
  introv Hv.
  induction Hv; auto.
Qed.

Hint Constructors kindings_validated : kindings_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : kindings_validated _ E _ _ |- _ =>
      apply (proj31 (kindings_regular_inv
               (regular_kindings
                  (unvalidated_kindings H))))
  end : kindings_regular.

Hint Extern 1 (types ?Ts) =>
  match goal with
  | H : kindings_validated _ _ Ts _ |- _ =>
      apply (proj32 (kindings_regular_inv
               (regular_kindings
                  (unvalidated_kindings H))))
  end : kindings_regular.

Hint Extern 1 (kinds ?Ks) =>
  match goal with
  | H : kindings_validated _ _ _ Ks |- _ =>
      apply (proj33 (kindings_regular_inv
               (regular_kindings
                  (unvalidated_kindings H))))
  end : kindings_regular.

Lemma kindings_validated_inv : forall chk E Ts Ks,
    kindings_validated chk E Ts Ks ->
    valid_env chk E.
Proof.
  introv Hv.
  destruct Hv; auto.
Qed.

Lemma kindings_validated_checked_inv : forall E Ts Ks,
    kindings_validated true E Ts Ks ->
    valid_env true E /\ valid_kinds true E Ks.
Proof.
  introv Hv.
  remember true as chk.
  destruct Hv; subst; auto.
Qed.

Hint Extern 1 (valid_env ?chk ?E) =>
  match goal with
  | H : kindings_validated chk E _ _ |- _ =>
      apply (kindings_validated_inv H)
  end : kindings_validated.

Hint Extern 1 (valid_kinds true ?E ?Ks) =>
  match goal with
  | H : kindings_validated true E _ Ks |- _ =>
      apply (proj2 (kindings_validated_checked_inv H))
  end : kindings_validated.

Lemma validated_kindings_regular : forall chk E Ts M,
    kindings_regular chk E Ts M -> kindings_validated chk E Ts M.
Proof.
  introv Hv.
  induction Hv; auto with kindings_validated.
  apply kindings_validated_cons;
    destruct chk; try discriminate;
    auto with kinding_validated kindings_validated.
Qed.

Lemma validated_kindings : forall chk E Ts M,
    kindings chk E Ts M -> kindings_validated chk E Ts M.
Proof.
  introv Hv.
  auto using
    regular_kindings, validated_kindings_regular.
Qed.

Hint Extern 1 (valid_env ?chk ?E) =>
  match goal with
  | H : kindings chk E _ _ |- _ =>
      apply (kindings_validated_inv
               (validated_kindings H))
  end : kindings_validated.

Hint Extern 1 (valid_kinds true ?E ?Ks) =>
  match goal with
  | H : kindings true E _ Ks |- _ =>
      apply (proj2 (kindings_validated_checked_inv
                      (validated_kindings H)))
  end : kindings_validated.

Inductive valid_schemes_validated : bool -> env -> list sch -> Prop :=
  | valid_schemes_validated_nil : forall chk E,
      valid_env chk E ->
      environment E ->
      valid_schemes_validated chk E nil
  | valid_schemes_validated_cons : forall chk E M Ms,
      valid_scheme chk E M ->
      valid_schemes_validated chk E Ms ->
      environment E ->
      scheme M ->
      schemes Ms ->
      valid_env chk E ->
      valid_schemes_validated chk E (M :: Ms).

Lemma unvalidated_valid_schemes : forall chk E Ms,
    valid_schemes_validated chk E Ms -> valid_schemes chk E Ms.
Proof.
  introv Hv.
  induction Hv; auto.
Qed.

Hint Constructors valid_schemes_validated : valid_schemes_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_schemes_validated _ E _ |- _ =>
      apply (proj1 (valid_schemes_regular_inv
               (regular_valid_schemes
                  (unvalidated_valid_schemes H))))
  end : valid_schemes_regular.

Hint Extern 1 (schemes ?Ms) =>
  match goal with
  | H : valid_schemes_validated _ _ Ms |- _ =>
      apply (proj2 (valid_schemes_regular_inv
               (regular_valid_schemes
                  (unvalidated_valid_schemes H))))
  end : valid_schemes_regular.

Lemma valid_schemes_validated_inv : forall chk E Ms,
    valid_schemes_validated chk E Ms ->
    valid_env chk E.
Proof.
  introv Hv.
  destruct Hv; auto.
Qed.

Hint Extern 1 (valid_env ?chk ?E) =>
  match goal with
  | H : valid_schemes_validated chk E _ |- _ =>
      apply (valid_schemes_validated_inv H)
  end : valid_schemes_validated.

Lemma validated_valid_schemes_regular : forall chk E Ms,
    valid_schemes_regular chk E Ms ->
    valid_schemes_validated chk E Ms.
Proof.
  introv Hv.
  induction Hv; auto with valid_schemes_validated.
Qed.

Lemma validated_valid_schemes : forall chk E Ms,
    valid_schemes chk E Ms -> valid_schemes_validated chk E Ms.
Proof.
  introv Hv.
  auto using
    regular_valid_schemes, validated_valid_schemes_regular.
Qed.

Hint Extern 1 (valid_env ?chk ?E) =>
  match goal with
  | H : valid_schemes chk E _ |- _ =>
      apply (valid_schemes_validated_inv
               (validated_valid_schemes H))
  end : valid_schemes_validated.

Inductive valid_instance_validated : env -> list typ -> sch -> Prop :=
  | valid_instance_validated_c : forall E Ts M,
      kindings true E Ts (knd_open_list (sch_kinds M) Ts) ->
      kinding true E (typ_open (sch_body M) Ts) knd_type ->
      environment E ->
      types Ts ->
      scheme M ->
      kinds (knd_open_list (sch_kinds M) Ts) ->
      type (typ_open (sch_body M) Ts) ->
      valid_env true E ->
      valid_instance_validated E Ts M.

Lemma unvalidated_valid_instance : forall E Ts M,
    valid_instance_validated E Ts M -> valid_instance E Ts M.
Proof.
  introv Hv.
  induction Hv; auto.
Qed.

Hint Constructors valid_instance_validated : valid_instance_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_instance_validated E _ _ |- _ =>
      apply (proj31 (valid_instance_regular_inv
               (regular_valid_instance
                  (unvalidated_valid_instance H))))
  end : valid_instance_regular.

Hint Extern 1 (types ?Ts) =>
  match goal with
  | H : valid_instance_validated _ Ts _ |- _ =>
      apply (proj32 (valid_instance_regular_inv
               (regular_valid_instance
                  (unvalidated_valid_instance H))))
  end : valid_instance_regular.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H : valid_instance_validated _ _ M |- _ =>
      apply (proj33 (valid_instance_regular_inv
               (regular_valid_instance
                  (unvalidated_valid_instance H))))
  end : valid_instance_regular.

Lemma valid_instance_validated_inv : forall E Ts M,
    valid_instance_validated E Ts M ->
    valid_env true E.
Proof.
  introv Hv.
  destruct Hv; auto.
Qed.

Hint Extern 1 (valid_env true ?E) =>
  match goal with
  | H : valid_instance_validated E _ _ |- _ =>
      apply (valid_instance_validated_inv H)
  end : valid_instance_validated.

Lemma validated_valid_instance_regular : forall E Ts M,
    valid_instance_regular E Ts M -> valid_instance_validated E Ts M.
Proof.
  introv Hv.
  destruct Hv; auto with valid_instance_validated kindings_validated.
Qed.

Lemma validated_valid_instance : forall E Ts M,
    valid_instance E Ts M -> valid_instance_validated E Ts M.
Proof.
  introv Hv.
  auto using
    regular_valid_instance, validated_valid_instance_regular.
Qed.

Hint Extern 1 (valid_env true ?E) =>
  match goal with
  | H : valid_instance E _ _ |- _ =>
      apply (valid_instance_validated_inv
               (validated_valid_instance H))
  end : valid_instance_validated.

Inductive valid_store_type_validated : env -> styp -> Prop :=
  | valid_store_type_validated_empty : forall E,
      valid_env true E ->
      environment E ->
      valid_store_type_validated E empty
  | valid_store_type_validated_push : forall E P l T,
      valid_store_type_validated E P ->
      kinding true E T knd_type ->
      l # P ->
      environment E ->
      type T ->
      valid_env true E ->
      valid_store_type_validated E (P & l ~ T).

Lemma unvalidated_valid_store_type : forall E P,
    valid_store_type_validated E P -> valid_store_type E P.
Proof.
  introv Hv.
  induction Hv; auto.
Qed.

Hint Constructors valid_store_type_validated
  : valid_store_type_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_store_type_validated E _ |- _ =>
      apply (proj1 (valid_store_type_regular_inv
               (regular_valid_store_type
                  (unvalidated_valid_store_type H))))
  end : valid_store_type_regular.

Hint Extern 1 (store_type ?P) =>
  match goal with
  | H : valid_store_type_validated _ P |- _ =>
      apply (proj2 (valid_store_type_regular_inv
               (regular_valid_store_type
                  (unvalidated_valid_store_type H))))
  end : valid_store_type_regular.

Lemma valid_store_type_validated_inv : forall E P,
    valid_store_type_validated E P ->
    valid_env true E.
Proof.
  introv Hv.
  destruct Hv; auto.
Qed.    

Hint Extern 1 (valid_env true ?E) =>
  match goal with
  | H : valid_store_type_validated E _ |- _ =>
      apply (valid_store_type_validated_inv H)
  end : valid_store_type_validated.

Lemma validated_valid_store_type_regular : forall E P,
    valid_store_type_regular E P ->
    valid_store_type_validated E P.
Proof.
  introv Hv.
  induction Hv;
    auto with valid_store_type_validated kinding_validated.
Qed.

Lemma validated_valid_store_type : forall E P,
    valid_store_type E P -> valid_store_type_validated E P.
Proof.
  introv Hv.
  auto using
    regular_valid_store_type, validated_valid_store_type_regular.
Qed.

Hint Extern 1 (valid_env true ?E) =>
  match goal with
  | H : valid_store_type E _ |- _ =>
      apply (valid_store_type_validated_inv
               (validated_valid_store_type H))
  end : valid_store_type_validated.

(* *************************************************************** *)
(** * Constructor of valid "kinds" bindings  *)

Lemma disjoint_env_fv_kinds : forall Xs M L,
    length Xs = sch_arity M ->
    disjoint (sch_fv M \u from_list Xs) L ->
    disjoint (env_fv (Xs ~::* M)) L.
Proof.
  introv Hl Hd.
  apply disjoint_subset_l
    with (B := knd_fv_list (sch_kinds M) \u from_list Xs);
    auto using env_fv_kinds.
  apply disjoint_union_l; split; auto.
  apply disjoint_subset_l with (B := sch_fv M);
    auto using sch_fv_kinds.
Qed.

Lemma kindings_bind_knds_fvars : forall E Xs Ks,
  environment E ->
  kinds Ks ->
  fresh (dom E) (length Ks) Xs ->
  kindings false (E & bind_knds Xs Ks) (typ_fvars Xs) Ks.
Proof.
  introv He Hks Hf.
  fresh_length Hf as Hl.
  generalize dependent E.  
  generalize dependent Ks.
  induction Xs; introv Hks Hl He Hf; destruct Ks; simpl in *;
    try discriminate; autorewrite with rew_env_concat in *; auto.
  inversion Hl; inversion Hks; destruct Hf; subst.
  apply kindings_cons.
  - apply kinding_var.
    + apply valid_env_no_check.
      apply environment_bind_knds;
        autorewrite with rew_env_dom; auto.
    + apply binds_middle_eq.
      autorewrite with rew_env_dom; auto.
  - apply IHXs; autorewrite with rew_env_dom; auto.
Qed.

Lemma scheme_kinds : forall Xs M,
  scheme M ->
  fresh \{} (sch_arity M) Xs ->
  kinds (knd_open_vars_list (sch_kinds M) Xs).
Proof.
  introv Hs Hf.
  fresh_length Hf as Hl.
  destruct Hs as [L M Hks].
  pick_freshes (sch_arity M) Ys.
  assert (fresh L (sch_arity M) Ys) as Hf2 by auto.
  assert (fresh (knd_fv_list (sch_kinds M)) (length Xs) Ys)
    by (apply fresh_subset with (L := sch_fv M);
          auto using sch_fv_kinds).
  specialize (Hks Ys Hf2).
  inversion Hks; subst.
  unfold knd_open_vars_list.
  rewrite knd_subst_list_intro with (Xs := Ys);
    try rewrite length_typ_fvars; auto.
  rewrite knd_subst_kind_list; auto.
Qed.  

Lemma kindings_fvars : forall E Xs M,
  environment E ->
  scheme M ->
  fresh (dom E) (sch_arity M) Xs ->
  kindings false (E & Xs ~::* M) (typ_fvars Xs)
    (knd_open_vars_list (sch_kinds M) Xs).
Proof.
  introv He Hs Hf.
  fresh_length Hf as Hl.
  assert (kinds (knd_open_vars_list (sch_kinds M) Xs))
    by auto using scheme_kinds.
  destruct M; unfold bind_sch_kinds; simpl in *.
  inversion Hs.
  apply kindings_bind_knds_fvars;
    try rewrite <- length_knd_open_vars_list; auto.
Qed.

Lemma valid_kinds_change_vars : forall E M Xs Ys Ks,
    fresh (dom E \u env_fv E \u sch_fv M) (sch_arity M) Xs ->
    fresh (dom E \u env_fv E \u sch_fv M \u from_list Xs \u knd_fv_list Ks)
      (sch_arity M) Ys ->
    scheme M ->
    environment E ->
    valid_kinds false (E & Xs ~::* M) Ks ->
    valid_kinds false (E & Ys ~::* M)
      (knd_subst_list Xs (typ_fvars Ys) Ks).
Proof.
  introv Hf1 Hf2 Hs He Hk.
  fresh_length Hf1 as Hl1.
  fresh_length Hf2 as Hl2.
  assert (valid_env false (E & Xs ~::* M & Ys ~::* M))
    by (eapply valid_env_unchecked_kinds; 
        autorewrite with rew_env_dom;
        eauto using valid_env_unchecked_kinds).
  apply valid_kinds_weakening_l with (F := Ys ~::* M) in Hk; auto.
  assert (disjoint (from_list Xs) (from_list Ys)) by auto.
  assert (disjoint (env_fv (Ys ~::* M)) (from_list Xs))
    by auto using disjoint_env_fv_kinds.
  assert (fresh (knd_fv_list (sch_kinds M)) (length Ys) Xs)
    by (apply fresh_subset with (L := sch_fv M);
          auto using sch_fv_kinds).
  apply valid_kinds_typ_subst
    with (Us := typ_fvars Ys) in Hk;
    try rewrite env_subst_fresh in Hk;
    autorewrite with rew_env_fv; auto.
  rewrite <- knd_subst_list_intro;
    try rewrite length_typ_fvars;
    auto.
  rewrite env_subst_fresh;
    autorewrite with rew_env_fv; auto.
  apply kindings_fvars;
    auto with valid_scheme_regular.
Qed.

Lemma valid_env_kinds : forall E Xs M,
    valid_env true E ->
    fresh (dom E) (sch_arity M) Xs ->
    valid_scheme true E M ->
    valid_env true (E & Xs ~::* M).
Proof.
  introv He Hf Hs.
  fresh_length Hf as Hl.
  assert (scheme M) by auto with valid_scheme_regular.
  assert (disjoint (from_list Xs) (sch_fv M))
   by eauto using valid_scheme_closed_list.
  apply valid_scheme_to_unchecked in Hs.
  remember false as chk''.
  destruct Hs; subst.
  apply valid_env_bind_sch_kinds with (chk' := false); auto.
  pick_freshes (sch_arity M) Ys.
  assert (fresh (knd_fv_list (sch_kinds M)) (length Xs) Ys)
    by (apply fresh_subset with (L := sch_fv M);
          auto using sch_fv_kinds).
  assert (disjoint (from_list Xs) (from_list Ys)) by auto.
  assert (disjoint (from_list Xs) (env_fv E))
   by auto using valid_env_closed_list.
  assert (fresh (knd_fv_list (sch_kinds M)) (sch_arity M) Xs)
    by (apply fresh_subset with (L := sch_fv M);
          auto using sch_fv_kinds, fresh_disjoint).
  assert
    (fresh (knd_fv_list (knd_open_vars_list (sch_kinds M) Ys))
      (sch_arity M) Xs)
    by (apply fresh_subset
          with (L := knd_fv_list (sch_kinds M) \u from_list Ys);
            auto using knd_open_vars_list_fv, fresh_disjoint).
  unfold knd_open_vars_list.
  rewrite knd_subst_list_intro with (Xs := Ys);
    try rewrite length_typ_fvars; auto.
  apply valid_kinds_change_vars with (Xs := Ys);
    eauto using fresh_disjoint, valid_kinds_and_type_inv_kinds
      with valid_env_regular.
Qed.

(* *************************************************************** *)
(* Valid empty schemes *)

Lemma valid_scheme_empty : forall chk E T,
    kinding chk E T knd_type <-> valid_scheme chk E (sch_empty T).
Proof.
  split.
  - introv Hk.
    apply valid_scheme_c with (L := typ_fv T);
      auto with kinding_validated.
    introv Hf.
    simpl in Hf.
    fresh_length Hf as Hl.
    destruct Xs; simpl in Hl; try discriminate.
    unfold bind_sch_kinds; simpl.
    rewrite concat_empty_r.
    rewrite typ_open_vars_nil.
    auto with kinding_validated.
  - intro Hv.
    remember (sch_empty T) as M.
    destruct Hv as [L chk E ? _ Hks]; subst.
    unfold bind_sch_kinds in Hks.
    specialize (Hks nil).
    apply valid_kinds_and_type_inv_type in Hks; auto.
    rewrite typ_open_vars_nil in Hks.
    simpl in *.
    rewrite concat_empty_r in Hks.
    assumption.
Qed.

(* directed versions for use with `auto` *)
Lemma valid_scheme_empty_of_kinding : forall chk E T,
    kinding chk E T knd_type ->
    valid_scheme chk E (sch_empty T).
Proof.
  introv Hv.
  rewrite <- valid_scheme_empty.
  assumption.
Qed.

Lemma kinding_of_valid_scheme_empty : forall chk E T,
    valid_scheme chk E (sch_empty T) ->
    kinding chk E T knd_type.
Proof.
  introv Hv.
  rewrite valid_scheme_empty.
  assumption.
Qed.

(* *************************************************************** *)
(** Somes lemmas about kindings useful for proving type subtitution
    on typings *)

Lemma kindings_add_subst_typ_bind : forall E F x M Xs Ts Ks,
  x \notin (dom E \u dom F) ->
  kindings true (env_subst Xs Ts (E & F))
    Ts (knd_subst_list Xs Ts Ks) ->
  valid_scheme true (E & bind_knds Xs Ks & F) M ->
  kindings true (env_subst Xs Ts (E & (F & x ~: M)))
    Ts (knd_subst_list Xs Ts Ks).
Proof.
  introv Hn Hks Hs.
  rewrite concat_assoc.
  rewrite env_subst_concat.
  rewrite env_subst_single.
  apply kindings_add_typ_bind_l;
    autorewrite with rew_env_dom;
    eauto using valid_scheme_typ_subst.
Qed.

Lemma kindings_add_subst_typ_bind_empty : forall E F x T Xs Ts Ks,
  x \notin (dom E \u dom F) ->
  kindings true (env_subst Xs Ts (E & F))
    Ts (knd_subst_list Xs Ts Ks) ->
  kinding true (E & bind_knds Xs Ks & F) T knd_type ->
  kindings true (env_subst Xs Ts (E & (F & x ~: sch_empty T))) Ts
    (knd_subst_list Xs Ts Ks).
Proof.
  introv Hn Hks Hk.
  rewrite concat_assoc.
  rewrite env_subst_concat.
  rewrite env_subst_single.
  apply kindings_add_typ_bind_l;
    autorewrite with rew_env_dom; auto.
  rewrite sch_subst_empty.
  rewrite <- valid_scheme_empty.
  replace knd_type with (knd_subst Xs Ts knd_type) by reflexivity.
  eauto using kinding_typ_subst.
Qed.

Lemma kindings_add_subst_typ_bind_empty2 :
  forall E F x T y U Xs Ts Ks,
  x \notin (dom E \u dom F) ->
  y \notin (dom E \u dom F \u \{x}) ->
  kindings true (env_subst Xs Ts (E & F))
    Ts (knd_subst_list Xs Ts Ks) ->
  kinding true (E & bind_knds Xs Ks & F) T knd_type ->
  kinding true (E & bind_knds Xs Ks & F) U knd_type ->
  kindings true
    (env_subst Xs Ts (E & (F & x ~: sch_empty T & y ~: sch_empty U)))
    Ts (knd_subst_list Xs Ts Ks).
Proof.
  introv Hn1 Hn2 Hks Hk1 Hk2.
  rewrite concat_assoc.
  rewrite concat_assoc.
  rewrite env_subst_concat.
  rewrite env_subst_concat.
  rewrite env_subst_single.
  rewrite env_subst_single.
  apply kindings_add_typ_bind_l;
    autorewrite with rew_env_dom; auto.
  apply kindings_add_typ_bind_l;
    autorewrite with rew_env_dom;
    try rewrite sch_subst_empty;
    try rewrite <- valid_scheme_empty;
    replace knd_type with (knd_subst Xs Ts knd_type) by reflexivity;
    eauto using kinding_typ_subst.
  apply valid_scheme_add_typ_bind_l;
    autorewrite with rew_env_dom;
    try rewrite sch_subst_empty;
    try rewrite <- valid_scheme_empty;
    replace knd_type with (knd_subst Xs Ts knd_type) by reflexivity;
    eauto using kinding_typ_subst.
Qed.

Lemma kindings_add_subst_kinds_bind : forall E F Zs Us Ks Xs M,
    fresh (dom E \u dom F \u from_list Zs) (sch_arity M) Xs ->
    kindings true (env_subst Zs Us (E & F)) Us
      (knd_subst_list Zs Us Ks) ->
    valid_scheme true (E & bind_knds Zs Ks & F) M ->
    kindings true (env_subst Zs Us (E & (F & Xs ~::* M))) Us
      (knd_subst_list Zs Us Ks).
Proof.
  introv Hf Hk Hs.
  rewrite concat_assoc.
  rewrite env_subst_concat.
  rewrite env_subst_bind_sch_kinds; auto with kindings_regular.
  apply kindings_weakening_l; auto.
  apply valid_env_kinds;
    try rewrite sch_subst_arity;
    autorewrite with rew_env_dom;
    auto with kindings_validated.
  eauto using valid_scheme_typ_subst.
Qed.

(* *************************************************************** *)
(** * "Validated" version of typing judgement *)

Inductive typing_validated : env -> styp -> trm -> typ -> Prop :=
  | typing_validated_var : forall E P x M T Us,
      valid_env true E ->
      valid_store_type E P ->
      binds x (bind_typ M) E -> 
      valid_instance E Us M ->
      type_equal true E T (instance M Us) knd_type ->
      environment E ->
      store_type P ->
      scheme M ->
      types Us ->
      type T ->
      valid_scheme true E M ->
      kinding true E T knd_type ->
      typing_validated E P (trm_fvar x) T
  | typing_validated_abs : forall L E P T1 T2 t1,
      kinding true E T1 knd_type ->
      (forall x, x \notin L -> 
        typing_validated
          (E & x ~ bind_typ (sch_empty T1)) P (t1 ^ x) T2) ->
      environment E ->
      (forall x, x \notin L ->
         environment (E & x ~ bind_typ (sch_empty T1))) ->
      store_type P ->
      type T1 ->
      type T2 ->
      term_body t1 ->
      valid_env true E ->
      (forall x, x \notin L -> 
        valid_env true (E & x ~ bind_typ (sch_empty T1))) ->
      valid_store_type E P ->
      kinding true E T2 knd_type ->
      (forall x, x \notin L -> 
        kinding true
          (E & x ~ bind_typ (sch_empty T1)) T2 knd_type) ->
      typing_validated E P (trm_abs t1) (typ_arrow T1 T2)
  | typing_validated_app : forall E P S T t1 t2, 
      typing_validated E P t1 (typ_arrow S T) ->
      typing_validated E P t2 S ->
      environment E ->
      store_type P ->
      type S ->
      type T ->
      term t1 ->
      term t2 ->
      valid_env true E ->
      valid_store_type E P ->
      kinding true E S knd_type ->
      kinding true E T knd_type ->
      typing_validated E P (trm_app t1 t2) T
  | typing_validated_let_val : forall M L E P T2 t1 t2,
      value t1 ->
      (forall Xs, fresh L (sch_arity M) Xs ->
         typing_validated
           (E & Xs ~::* M) P
           t1 (instance_vars M Xs)) ->
      (forall x, x \notin L ->
         typing_validated (E & x ~ (bind_typ M)) P (t2 ^ x) T2) ->
      environment E ->
      (forall Xs, fresh L (sch_arity M) Xs ->
         environment (E & Xs ~::* M)) ->
      (forall x, x \notin L ->
         environment (E & x ~ (bind_typ M))) ->
      store_type P ->
      type T2 ->
      (forall Xs, fresh L (sch_arity M) Xs ->
         type (instance_vars M Xs)) ->
      scheme M ->
      term t1 ->
      term_body t2 ->
      valid_env true E ->
      (forall Xs, fresh L (sch_arity M) Xs ->
         valid_env true (E & Xs ~::* M)) ->
      (forall x, x \notin L ->
         valid_env true (E & x ~ (bind_typ M))) ->
      valid_store_type E P ->
      (forall Xs, fresh L (sch_arity M) Xs ->
         kinding true (E & Xs ~::* M)
           (instance_vars M Xs) knd_type) ->
      valid_scheme true E M ->
      kinding true E T2 knd_type ->
      (forall x, x \notin L ->
         kinding true (E & x ~ (bind_typ M)) T2 knd_type) ->
      typing_validated E P (trm_let t1 t2) T2
  | typing_validated_let : forall L E P T1 T2 t1 t2, 
      typing_validated E P t1 T1 ->
      (forall x, x \notin L ->
         typing_validated (E & x ~: sch_empty T1) P (t2 ^ x) T2) ->
      environment E ->
      (forall x, x \notin L ->
         environment (E & x ~: sch_empty T1)) ->
      store_type P ->
      type T1 ->
      type T2 ->
      term t1 ->
      term_body t2 ->
      valid_env true E ->
      (forall x, x \notin L ->
         valid_env true (E & x ~: sch_empty T1)) ->
      valid_store_type E P ->
      kinding true E T1 knd_type ->
      kinding true E T2 knd_type ->
      typing_validated E P (trm_let t1 t2) T2
  | typing_validated_constructor : forall c E P T1 T2 T3 t,
      kinding true E T1 (knd_range (typ_top CSet.universe) T2) ->
      subtype true E
        (typ_constructor c T3)
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (CSet.singleton c) ->
      typing_validated E P t T3 ->
      environment E ->
      store_type P ->
      type T1 ->
      type T2 ->
      type T3 ->
      term t ->
      valid_env true E ->
      valid_store_type E P ->
      kinding true E T2 (knd_row CSet.universe) ->
      kinding true E T3 knd_type ->
      typing_validated E P (trm_constructor c t) (typ_variant T1)
  | typing_validated_match : forall c L E P T1 T2 T3 T4 T5
                          T6 T7 T8 t1 t2 t3,
      subtype true E
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (typ_constructor c T7)
        (CSet.singleton c) ->
      subtype true E
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (typ_proj CSet.universe T4 (CSet.singleton c))
        (CSet.singleton c) ->
      subtype true E
        (typ_proj CSet.universe T2 (CSet.cosingleton c))
        (typ_proj CSet.universe T6 (CSet.cosingleton c))
        (CSet.cosingleton c) ->
      kinding true E T1 (knd_range T2 (typ_bot CSet.universe)) ->
      kinding true E T3 (knd_range (typ_top CSet.universe) T4) ->
      kinding true E T5 (knd_range (typ_top CSet.universe) T6) ->
      typing_validated E P t1 (typ_variant T1) ->
      (forall x, x \notin L ->
         typing_validated (E & x ~: (sch_empty (typ_variant T3))) P
                (t2 ^ x) T8) ->
      (forall y, y \notin L -> 
         typing_validated (E & y ~: (sch_empty (typ_variant T5))) P
                (t3 ^ y) T8) ->
      environment E ->
      (forall x, x \notin L ->
         environment (E & x ~: (sch_empty (typ_variant T3)))) ->
      (forall y, y \notin L -> 
         environment (E & y ~: (sch_empty (typ_variant T5)))) ->
      store_type P ->
      type T1 ->
      type T2 ->
      type T3 ->
      type T4 ->
      type T5 ->
      type T6 ->
      type T7 ->
      type T8 ->
      term t1 ->
      term_body t2 ->
      term_body t3 ->
      valid_env true E ->
      (forall x, x \notin L ->
         valid_env true (E & x ~: (sch_empty (typ_variant T3)))) ->
      (forall y, y \notin L -> 
         valid_env true (E & y ~: (sch_empty (typ_variant T5)))) ->
      valid_store_type E P ->
      kinding true E T2 (knd_row CSet.universe) ->
      kinding true E T4 (knd_row CSet.universe) ->
      kinding true E T6 (knd_row CSet.universe) ->
      kinding true E T7 knd_type ->
      kinding true E T8 knd_type ->
      (forall x, x \notin L ->
         kinding true (E & x ~: (sch_empty (typ_variant T3)))
                 T8 knd_type) ->
      (forall y, y \notin L -> 
         kinding true (E & y ~: (sch_empty (typ_variant T5)))
                 T8 knd_type) ->
      typing_validated E P (trm_match t1 c t2 t3) T8
  | typing_validated_destruct : forall c L E P T1 T2 T3 T4 t1 t2,
      kinding true E T1 (knd_range T2 (typ_bot CSet.universe)) ->
      subtype true E
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (typ_constructor c T3)
        (CSet.singleton c) ->
      subtype true E
        (typ_proj CSet.universe T2 (CSet.cosingleton c))
        (typ_bot (CSet.cosingleton c))
        (CSet.cosingleton c) ->
      typing_validated E P t1 (typ_variant T1) ->
      (forall x, x \notin L ->
         typing_validated (E & x ~: (sch_empty T3)) P
                (t2 ^ x) T4) ->
      environment E ->
      (forall x, x \notin L ->
         environment (E & x ~: (sch_empty T3))) ->
      store_type P ->
      type T1 ->
      type T2 ->
      type T3 ->
      type T4 ->
      term t1 ->
      term_body t2 ->
      valid_env true E ->
      (forall x, x \notin L ->
         valid_env true (E & x ~: (sch_empty T3))) ->
      valid_store_type E P ->
      kinding true E T2 (knd_row CSet.universe) ->
      kinding true E T3 knd_type ->
      kinding true E T4 knd_type ->
      (forall x, x \notin L ->
          kinding true (E & x ~: (sch_empty T3))
                  T4 knd_type) ->
      typing_validated E P (trm_destruct t1 c t2) T4
  | typing_validated_absurd : forall E P T1 T2 t1,
      kinding true E T1 (knd_range (typ_bot CSet.universe)
                              (typ_bot CSet.universe)) ->
      kinding true E T2 knd_type ->
      typing_validated E P t1 (typ_variant T1) ->
      environment E ->
      store_type P ->
      type T1 ->
      type T2 ->
      term t1 ->
      valid_env true E ->
      valid_store_type E P ->
      typing_validated E P (trm_absurd t1) T2
  | typing_validated_fix : forall L E P T1 T2 t1,
      (forall x y,
          x \notin L -> y \notin (L \u \{x}) ->
          typing_validated
            (E & x ~: sch_empty (typ_arrow T1 T2) & y ~: sch_empty T1)
            P (t1 ^* (cons x (cons y nil))) T2) ->
      environment E ->
      (forall x y, x \notin L -> y \notin (L \u \{x}) ->
         environment
           (E & x ~: sch_empty (typ_arrow T1 T2)
              & y ~: sch_empty T1)) ->
      store_type P ->
      type T1 ->
      type T2 ->
      term_body2 t1 ->
      valid_env true E ->
      (forall x y, x \notin L -> y \notin (L \u \{x}) ->
         valid_env true
           (E & x ~: sch_empty (typ_arrow T1 T2)
              & y ~: sch_empty T1)) ->
      valid_store_type E P ->
      kinding true E T1 knd_type ->
      kinding true E T2 knd_type ->
      typing_validated E P (trm_fix t1) (typ_arrow T1 T2)
  | typing_validated_unit : forall E P,
      valid_env true E ->
      valid_store_type E P ->
      environment E ->
      store_type P ->
      typing_validated E P trm_unit typ_unit
  | typing_validated_prod : forall E P T1 T2 t1 t2,
      typing_validated E P t1 T1 ->
      typing_validated E P t2 T2 ->
      environment E ->
      store_type P ->
      type T1 ->
      type T2 ->
      term t1 ->
      term t2 ->
      valid_env true E ->
      valid_store_type E P ->
      kinding true E T1 knd_type ->
      kinding true E T2 knd_type ->
      typing_validated E P (trm_prod t1 t2) (typ_prod T1 T2)
  | typing_validated_fst : forall E P T1 T2 t1,
      typing_validated E P t1 (typ_prod T1 T2) ->
      environment E ->
      store_type P ->
      type T1 ->
      type T2 ->
      term t1 ->
      valid_env true E ->
      valid_store_type E P ->
      kinding true E T1 knd_type ->
      kinding true E T2 knd_type ->
      typing_validated E P (trm_fst t1) T1
  | typing_validated_snd : forall E P T1 T2 t1,
      typing_validated E P t1 (typ_prod T1 T2) ->
      environment E ->
      store_type P ->
      type T1 ->
      type T2 ->
      term t1 ->
      valid_env true E ->
      valid_store_type E P ->
      kinding true E T1 knd_type ->
      kinding true E T2 knd_type ->
      typing_validated E P (trm_snd t1) T2
  | typing_validated_loc : forall E P l T1 T2,
      valid_env true E ->
      valid_store_type E P ->
      binds l T1 P ->
      type_equal true E T1 T2 knd_type ->
      environment E ->
      store_type P ->
      type T1 ->
      type T2 ->
      kinding true E T1 knd_type ->
      kinding true E T2 knd_type ->
      typing_validated E P (trm_loc l) (typ_ref T2)
  | typing_validated_ref : forall E P t1 T,
      typing_validated E P t1 T ->
      environment E ->
      store_type P ->
      type T ->
      term t1 ->
      valid_env true E ->
      valid_store_type E P ->
      kinding true E T knd_type ->
      typing_validated E P (trm_ref t1) (typ_ref T)
  | typing_validated_get : forall E P t1 T,
      typing_validated E P t1 (typ_ref T) ->
      environment E ->
      store_type P ->
      type T ->
      term t1 ->
      valid_env true E ->
      valid_store_type E P ->
      kinding true E T knd_type ->
      typing_validated E P (trm_get t1) T
  | typing_validated_set : forall E P t1 t2 T,
      typing_validated E P t1 (typ_ref T) ->
      typing_validated E P t2 T ->
      environment E ->
      store_type P ->
      type T ->
      term t1 ->
      term t2 ->
      valid_env true E ->
      valid_store_type E P ->
      kinding true E T knd_type ->
      typing_validated E P (trm_set t1 t2) typ_unit.

Lemma unvalidated_typing : forall E P t T,
    typing_validated E P t T -> typing E P t T.
Proof.
  introv Ht.
  induction Ht; eauto using typing.
Qed.

Hint Resolve unvalidated_typing.

Lemma typing_validated_inv : forall E P t T,
    typing_validated E P t T ->
    valid_env true E /\ valid_store_type E P
    /\ kinding true E T knd_type.
Proof.
  introv Ht.
  induction Ht; splits;
  eauto using kinding_unvalidated_range_bot.
Qed.

Hint Constructors typing_validated : typing_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : typing_validated E _ _ _ |- _ =>
      apply (proj41 (typing_regular_inv
                       (regular_typing (unvalidated_typing H))))
  end : typing_regular.

Hint Extern 1 (store_type ?P) =>
  match goal with
  | H : typing_validated _ P _ _ |- _ =>
      apply (proj42 (typing_regular_inv
                       (regular_typing (unvalidated_typing H))))
  end : typing_regular.

Hint Extern 1 (term ?t) =>
  match goal with
  | H : typing_validated _ _ t _ |- _ =>
      apply (proj43 (typing_regular_inv
                       (regular_typing (unvalidated_typing H))))
  end : typing_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : typing_validated _ _ _ T |- _ =>
      apply (proj44 (typing_regular_inv 
                       (regular_typing (unvalidated_typing H))))
  end : typing_regular.

Hint Extern 1 (valid_env true ?E) =>
  match goal with
  | H : typing_validated E _ _ _ |- _ =>
      apply (proj31 (typing_validated_inv H))
  end : typing_validated.

Hint Extern 1 (valid_store_type ?E ?P) =>
  match goal with
  | H : typing_validated E P _ _ |- _ =>
      apply (proj32 (typing_validated_inv H))
  end : typing_validated.

Hint Extern 1 (kinding true ?E ?T knd_type) =>
  match goal with
  | H : typing_validated E _ _ T |- _ =>
      apply (proj33 (typing_validated_inv H))
  end : typing_validated.

Lemma validated_typing_regular : forall E P t T,
    typing_regular E P t T -> typing_validated E P t T.
Proof.
  introv Ht.
  induction Ht.
  - econstructor; try eassumption; auto.
    + apply valid_scheme_from_env with (x := x); assumption.
    + auto with type_equal_validated.
  - pick_fresh x.
    assert (typing_validated (E & x ~: sch_empty T1) P (t1 ^ x) T2)
      by auto.
    assert (valid_env true E)
      by eauto with kinding_validated.
    assert (valid_store_type E P)
      by eauto using valid_store_type_remove_typ_bind_l
           with typing_validated.
    assert (kinding true E T2 knd_type)
      by eauto using kinding_remove_typ_bind_l with typing_validated.
    econstructor; eauto with typing_validated;
      intros y Hn;
      assert (typing_validated (E & y ~: sch_empty T1) P (t1 ^ y) T2) 
        by auto;
      auto with typing_validated.
  - assert (kinding true E (typ_arrow S T) knd_type)
      as Hk by auto with typing_validated.
    inversion Hk; subst.
    econstr auto with typing_validated.
  - pick_fresh x.
    assert (typing_validated (E & x ~: M) P (t2 ^ x) T2) by auto.
    assert (valid_store_type E P)
      by eauto using valid_store_type_remove_typ_bind_l
           with typing_validated.
    assert (kinding true E T2 knd_type)
      by eauto using kinding_remove_typ_bind_l with typing_validated.
    assert (valid_env true (E & x ~: M))
      by auto with typing_validated.
    assert (valid_env true E) by eauto with kinding_validated.
    assert (valid_scheme true E M)
      by eauto using binds_push_eq,
         valid_scheme_from_env, valid_scheme_remove_typ_bind_l.
    econstructor; eauto;
      try
        (intros Ys Hf;
         assert
           (typing_validated (E & Ys ~::* M) P
              t1 (instance_vars M Ys))
           by auto;
         auto with typing_validated);
      try
        (intros y Hn;
         assert (typing_validated (E & y ~: M) P (t2 ^ y) T2)
           by auto;
         auto with typing_validated).
  - pick_fresh x.
    assert (typing_validated (E & x ~: sch_empty T1) P (t2 ^ x) T2)
      by auto.
    assert (kinding true E T2 knd_type)
      by eauto using kinding_remove_typ_bind_l with typing_validated.
    eapply typing_validated_let; eauto with typing_validated.
    intros y Hn.
    assert (typing_validated (E & y ~: sch_empty T1) P (t2 ^ y) T2)
      by auto.
    auto with typing_validated.
  - assert (valid_kind true E (knd_range (typ_top CSet.universe) T2))
      as Hk by auto with kinding_validated.
    inversion Hk; subst.
    assert (kinding true E T2 (knd_row CSet.universe))
      by auto with subtype_validated.
    econstr auto with typing_validated.
  - assert (valid_kind true E (knd_range T2 (typ_bot CSet.universe)))
      as Hk1 by auto with kinding_validated.
    inversion Hk1; subst.
    assert (kinding true E T2 (knd_row CSet.universe))
      by auto with subtype_validated.
    assert (valid_kind true E (knd_range (typ_top CSet.universe) T4))
      as Hk2 by auto with kinding_validated.
    inversion Hk2; subst.
    assert (kinding true E T4 (knd_row CSet.universe))
      by auto with subtype_validated.
    assert (valid_kind true E (knd_range (typ_top CSet.universe) T6))
      as Hk3 by auto with kinding_validated.
    inversion Hk3; subst.
    assert (kinding true E T6 (knd_row CSet.universe))
      by auto with subtype_validated.
    assert (kinding true E (typ_constructor c T7)
                    (knd_row (CSet.singleton c)))
      as Hk4 by auto with subtype_validated.
    inversion Hk4; subst.
    pick_fresh x.
    assert (typing_validated (E & x ~: sch_empty (typ_variant T5)) P
                             (t3 ^ x) T8)
      by auto.
    assert (kinding true E T8 knd_type)
      by eauto using kinding_remove_typ_bind_l with typing_validated.
    econstructor; eauto with typing_validated;
      intros y Hn;
      assert
        (typing_validated
           (E & y ~: sch_empty (typ_variant T3)) P (t2 ^ y) T8)
        by auto;
      assert (typing_validated
                (E & y ~: sch_empty (typ_variant T5)) P (t3 ^ y) T8)
        by auto;
      auto with typing_validated.
  - assert (valid_kind true E (knd_range T2 (typ_bot CSet.universe)))
      as Hk1 by auto with kinding_validated.
    inversion Hk1; subst.
    assert (kinding true E T2 (knd_row CSet.universe))
      by auto with subtype_validated.
    assert (kinding true E (typ_constructor c T3)
                    (knd_row (CSet.singleton c)))
      as Hk2 by auto with subtype_validated.
    inversion Hk2; subst.
    pick_fresh x.
    assert (typing_validated (E & x ~: sch_empty T3) P
                             (t2 ^ x) T4)
      by auto.
    assert (kinding true E T4 knd_type)
      by eauto using kinding_remove_typ_bind_l with typing_validated.
    econstructor; eauto with typing_validated;
      intros y Hn;
      assert (typing_validated
                (E & y ~: sch_empty T3) P (t2 ^ y) T4)
        by auto;
      auto with typing_validated.   
  - econstr auto with typing_validated.
  - pick_fresh x.
    pick_fresh y.
    assert
      (typing_validated
         (E & x ~: sch_empty (typ_arrow T1 T2) & y ~: sch_empty T1)
         P (t1 ^* (cons x (cons y nil))) T2)
      by auto.
    assert (valid_env true E)
      by eauto using valid_env_remove_typ_bind_l
           with typing_validated.
    assert (valid_store_type E P)
      by eauto using valid_store_type_remove_typ_bind_l
           with typing_validated.
    assert 
      (valid_env true (E & x ~: sch_empty (typ_arrow T1 T2)
                   & y ~: sch_empty T1)) as He
      by auto with typing_validated.
    apply valid_scheme_from_env
      with (x := y) (M := sch_empty T1) in He;
        auto using binds_push_eq.
    rewrite <- valid_scheme_empty in He.
    assert (kinding true E T2 knd_type)
        by eauto using kinding_remove_typ_bind_l
             with typing_validated.
    assert (kinding true E T1 knd_type)
        by eauto using kinding_remove_typ_bind_l.
    econstructor; eauto with typing_validated.
      intros x' y' Hn1 Hn2;
      assert
        (typing_validated
          (E & x' ~: sch_empty (typ_arrow T1 T2) & y' ~: sch_empty T1)
          P (t1 ^* (cons x' (cons y' nil))) T2)
        by auto;
      auto with typing_validated.    
  - econstr auto with typing_validated.
  - econstr auto with typing_validated.
  - assert (kinding true E (typ_prod T1 T2) knd_type)
      as Hk by auto with typing_validated.
    inversion Hk; subst.
    econstr auto with typing_validated.
  - assert (kinding true E (typ_prod T1 T2) knd_type)
      as Hk by auto with typing_validated.
    inversion Hk; subst.
    econstr auto with typing_validated.
  - econstr
      eauto using kinding_from_store_type
        with typing_validated type_equal_validated.  
  - econstr auto with typing_validated.
  - assert (kinding true E (typ_ref T) knd_type)
      as Hknd by auto with typing_validated.
    inversion Hknd; subst.
    econstr auto with typing_validated.
  - econstr auto with typing_validated.
Qed.

Lemma validated_typing : forall E P t T,
    typing E P t T -> typing_validated E P t T.
Proof.
  intros.
  apply validated_typing_regular.
  apply regular_typing.
  assumption.
Qed.

Hint Extern 1 (valid_env true ?E) =>
  match goal with
  | H : typing E _ _ _ |- _ =>
      apply (proj31 (typing_validated_inv (validated_typing H)))
  end : typing_validated.

Hint Extern 1 (valid_store_type ?E ?P) =>
  match goal with
  | H : typing E P _ _ |- _ =>
      apply (proj32 (typing_validated_inv (validated_typing H)))
  end : typing_validated.

Hint Extern 1 (kinding true ?E ?T knd_type) =>
  match goal with
  | H : typing E _ _ T |- _ =>
      apply (proj33 (typing_validated_inv (validated_typing H)))
  end : typing_validated.

Inductive typing_scheme_validated
  : env -> styp -> trm -> sch -> Prop :=
  | typing_scheme_validated_c : forall L E P t M,
      valid_scheme true E M ->
      valid_store_type E P ->
      (forall Xs,
         fresh L (sch_arity M) Xs ->
         typing (E & Xs ~::* M) P t (instance_vars M Xs)) ->     
      environment E ->
      (forall Xs, fresh L (sch_arity M) Xs ->
         environment (E & Xs ~::* M)) ->
      store_type P ->
      scheme M ->
      term t ->
      valid_env true E ->
      (forall Xs, fresh L (sch_arity M) Xs ->
         valid_env true (E & Xs ~::* M)) ->
      (forall Xs, fresh L (sch_arity M) Xs ->
         kinding true (E & Xs ~::* M)
           (instance_vars M Xs) knd_type) ->
      typing_scheme_validated E P t M.

Lemma unvalidated_typing_scheme : forall E P t M,
    typing_scheme_validated E P t M -> typing_scheme E P t M.
Proof.
  introv Ht.
  induction Ht; eauto using typing_scheme.
Qed.

Hint Resolve unvalidated_typing_scheme.

Lemma typing_scheme_validated_inv : forall E P t M,
    typing_scheme_validated E P t M ->
    valid_env true E /\ valid_store_type E P
    /\ valid_scheme true E M.
Proof.
  introv Ht.
  destruct Ht; auto.
Qed.

Hint Constructors typing_scheme_validated : typing_scheme_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : typing_scheme_validated E _ _ _ |- _ =>
      apply (proj41 (typing_scheme_regular_inv
                       (regular_typing_scheme
                          (unvalidated_typing_scheme H))))
  end : typing_scheme_regular.

Hint Extern 1 (store_type ?P) =>
  match goal with
  | H : typing_scheme_validated _ P _ _ |- _ =>
      apply (proj42 (typing_scheme_regular_inv
                       (regular_typing_scheme
                          (unvalidated_typing_scheme H))))
  end : typing_scheme_regular.

Hint Extern 1 (term ?t) =>
  match goal with
  | H : typing_scheme_validated _ _ t _ |- _ =>
      apply (proj43 (typing_scheme_regular_inv
                       (regular_typing_scheme
                          (unvalidated_typing_scheme H))))
  end : typing_scheme_regular.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H : typing_scheme_validated _ _ _ M |- _ =>
      apply (proj44 (typing_scheme_regular_inv 
                       (regular_typing_scheme
                          (unvalidated_typing_scheme H))))
  end : typing_scheme_regular.

Hint Extern 1 (valid_env true ?E) =>
  match goal with
  | H : typing_scheme_validated E _ _ _ |- _ =>
      apply (proj31 (typing_scheme_validated_inv H))
  end : typing_scheme_validated.

Hint Extern 1 (valid_store_type ?E ?P) =>
  match goal with
  | H : typing_scheme_validated E P _ _ |- _ =>
      apply (proj32 (typing_scheme_validated_inv H))
  end : typing_scheme_validated.

Hint Extern 1 (valid_scheme true ?E ?M) =>
  match goal with
  | H : typing_scheme_validated E _ _ M |- _ =>
      apply (proj33 (typing_scheme_validated_inv H))
  end : typing_scheme_validated.

Lemma validated_typing_scheme_regular : forall E P t M,
    typing_scheme_regular E P t M -> typing_scheme_validated E P t M.
Proof.
  introv Ht.
  destruct Ht.
  pick_freshes (sch_arity M) Xs.
  assert (typing (E & Xs ~::* M) P t (instance_vars M Xs)) by auto.
  apply typing_scheme_validated_c with (L := L);
    auto with valid_scheme_validated typing_validated;
    intros Ys Hf;
    assert (typing (E & Ys ~::* M) P t (instance_vars M Ys)) by auto;
    auto with typing_validated.
Qed.

Lemma validated_typing_scheme : forall E P t M,
    typing_scheme E P t M -> typing_scheme_validated E P t M.
Proof.
  intros.
  apply validated_typing_scheme_regular.
  apply regular_typing_scheme.
  assumption.
Qed.

Hint Extern 1 (valid_env true ?E) =>
  match goal with
  | H : typing_scheme E _ _ _ |- _ =>
      apply (proj31 (typing_scheme_validated_inv
                       (validated_typing_scheme H)))
  end : typing_scheme_validated.

Hint Extern 1 (valid_store_type ?E ?P) =>
  match goal with
  | H : typing_scheme E P _ _ |- _ =>
      apply (proj32 (typing_scheme_validated_inv
                       (validated_typing_scheme H)))
  end : typing_scheme_validated.

Hint Extern 1 (valid_scheme true ?E ?M) =>
  match goal with
  | H : typing_scheme E _ _ M |- _ =>
      apply (proj33 (typing_scheme_validated_inv
                       (validated_typing_scheme H)))
  end : typing_scheme_validated.

Inductive typing_schemes_validated
  : env -> styp -> list trm -> list sch -> Prop :=
  | typing_schemes_validated_nil : forall E P,
      valid_env true E ->
      valid_store_type E P ->
      environment E ->
      store_type P ->
      typing_schemes_validated E P nil nil
  | typing_schemes_validated_cons : forall E P t ts M Ms,
      typing_scheme E P t M ->
      typing_schemes_validated E P ts Ms ->
      environment E ->
      store_type P ->
      scheme M ->
      schemes Ms ->
      term t ->
      terms ts ->
      valid_env true E ->
      valid_store_type E P ->
      valid_scheme true E M ->
      valid_schemes true E Ms ->
      typing_schemes_validated E P (t :: ts) (M :: Ms).

Lemma unvalidated_typing_schemes : forall E P ts Ms,
    typing_schemes_validated E P ts Ms -> typing_schemes E P ts Ms.
Proof.
  introv Hts.
  induction Hts; eauto using typing_schemes.
Qed.

Hint Resolve unvalidated_typing_schemes.

Lemma typing_schemes_validated_inv : forall E P ts Ms,
    typing_schemes_validated E P ts Ms ->
    valid_env true E /\ valid_store_type E P
    /\ valid_schemes true E Ms.
Proof.
  introv Hts.
  destruct Hts; auto.
Qed.

Hint Constructors typing_schemes_validated : typing_schemes_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : typing_schemes_validated E _ _ _ |- _ =>
      apply (proj41 (typing_schemes_regular_inv
                       (regular_typing_schemes
                          (unvalidated_typing_schemes H))))
  end : typing_schemes_regular.

Hint Extern 1 (store_type ?P) =>
  match goal with
  | H : typing_schemes_validated _ P _ _ |- _ =>
      apply (proj42 (typing_schemes_regular_inv
                       (regular_typing_schemes
                          (unvalidated_typing_schemes H))))
  end : typing_schemes_regular.

Hint Extern 1 (terms ?ts) =>
  match goal with
  | H : typing_schemes_validated _ _ ts _ |- _ =>
      apply (proj43 (typing_schemes_regular_inv
                       (regular_typing_schemes
                          (unvalidated_typing_schemes H))))
  end : typing_schemes_regular.

Hint Extern 1 (schemes ?Ms) =>
  match goal with
  | H : typing_schemes_validated _ _ _ Ms |- _ =>
      apply (proj44 (typing_schemes_regular_inv 
                       (regular_typing_schemes
                          (unvalidated_typing_schemes H))))
  end : typing_schemes_regular.

Hint Extern 1 (valid_env true ?E) =>
  match goal with
  | H : typing_schemes_validated E _ _ _ |- _ =>
      apply (proj31 (typing_schemes_validated_inv H))
  end : typing_schemes_validated.

Hint Extern 1 (valid_store_type ?E ?P) =>
  match goal with
  | H : typing_schemes_validated E P _ _ |- _ =>
      apply (proj32 (typing_schemes_validated_inv H))
  end : typing_schemes_validated.

Hint Extern 1 (valid_schemes true ?E ?Ms) =>
  match goal with
  | H : typing_schemes_validated E _ _ Ms |- _ =>
      apply (proj33 (typing_schemes_validated_inv H))
  end : typing_schemes_validated.

Lemma validated_typing_schemes_regular : forall E P ts Ms,
    typing_schemes_regular E P ts Ms ->
    typing_schemes_validated E P ts Ms.
Proof.
  introv Hts.
  induction Hts; auto with typing_schemes_validated.
  apply typing_schemes_validated_cons;
    auto with typing_scheme_validated typing_schemes_validated.
Qed.

Lemma validated_typing_schemes : forall E P ts Ms,
    typing_schemes E P ts Ms -> typing_schemes_validated E P ts Ms.
Proof.
  intros.
  apply validated_typing_schemes_regular.
  apply regular_typing_schemes.
  assumption.
Qed.

Hint Extern 1 (valid_env true ?E) =>
  match goal with
  | H : typing_schemes E _ _ _ |- _ =>
      apply (proj31 (typing_schemes_validated_inv
                       (validated_typing_schemes H)))
  end : typing_schemes_validated.

Hint Extern 1 (valid_store_type ?E ?P) =>
  match goal with
  | H : typing_schemes E P _ _ |- _ =>
      apply (proj32 (typing_schemes_validated_inv
                       (validated_typing_schemes H)))
  end : typing_schemes_validated.

Hint Extern 1 (valid_schemes true ?E ?M) =>
  match goal with
  | H : typing_schemes E _ _ M |- _ =>
      apply (proj33 (typing_schemes_validated_inv
                       (validated_typing_schemes H)))
  end : typing_schemes_validated.

Lemma typing_store_validated_inv : forall E V P,
    typing_store E V P ->
    valid_env true E /\ valid_store_type E P.
Proof.
  introv Ht.
  destruct Ht as [_ [Hv _]].
  splits; auto with valid_store_type_validated.
Qed.

Hint Extern 1 (valid_env true ?E) =>
  match goal with
  | H : typing_store E _ _ |- _ =>
      apply (proj1 (typing_store_validated_inv H))
  end : typing_store_validated.

Hint Extern 1 (valid_store_type ?E ?P) =>
  match goal with
  | H : typing_store E _ P |- _ =>
      apply (proj2 (typing_store_validated_inv H))
  end : typing_store_validated.