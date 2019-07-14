(************************************************
 *       Row Subtyping - Substitution           *
 *                 Leo White                    *
 ************************************************)

(* Lemmas for preservation under substitution *)

Set Implicit Arguments.
Require Import LibLN Utilities Cofinite Disjoint Definitions
        Opening FreeVars Environments Subst Wellformedness
        Weakening.

(* *************************************************************** *)
(** Kinding preserved by type substitution *)

Lemma kinding_typ_subst_var : forall E1 E2 E3 E4 Xs Rs Us X R,
    binds X R (E1 & Xs ~* Rs & E2) ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    kindings E3 E4 Us (rngs_kinds Rs) ->
    kinding E3 E4 (typ_var_subst Xs Us X) (rng_kind R)
    \/ (binds X R (E1 & E2)
        /\ typ_var_subst Xs Us X = typ_fvar X).
Proof.
  introv Hb Hl1 He Hks.
  assert (length Us = length Rs) as Hl2
    by (rewrite length_rngs_kinds; eauto using kindings_length).
  generalize dependent Rs.
  generalize dependent Us.
  induction Xs; introv Hb Hl1 He Hks Hl2; destruct Rs; destruct Us;
    try discriminate; simpl in *;
    autorewrite with rew_env_concat in *; auto.
  inversion Hks; subst.
  case_var.
  - apply binds_middle_eq_inv in Hb; subst;
      auto using ok_from_type_environment.
  - eauto using binds_subst, type_environment_remove.     
Qed.

(* Lemma for applying the inductive hypothesis in
   the contractive recursive cases. *)

Lemma kinding_typ_subst_rec :
  forall E1 E2 E3 Xs Us Rs T K,
  (type_environment (E1 & Xs ~* Rs & E2 & E3) ->
   type_environment_extension
     (E1 & Xs ~* Rs & E2 & E3) empty ->
   forall E4 : LibEnv.env rng,
     E1 & Xs ~* Rs & E2 & E3 = E1 & Xs ~* Rs & E4 ->
     kindings (tenv_subst Xs Us (E1 & E4))
              (tenv_subst Xs Us empty) Us
              (rngs_kinds (rng_subst_list Xs Us Rs)) ->
     kinding (tenv_subst Xs Us (E1 & E4))
             (tenv_subst Xs Us empty)
             (typ_subst Xs Us T) K) ->
  type_environment (E1 & Xs ~* Rs & E2) ->
  type_environment_extension (E1 & Xs ~* Rs & E2) E3 ->
  kindings (tenv_subst Xs Us (E1 & E2))
           (tenv_subst Xs Us E3) Us
           (rngs_kinds (rng_subst_list Xs Us Rs)) ->
  kinding (tenv_subst Xs Us (E1 & E2) & tenv_subst Xs Us E3)
    empty (typ_subst Xs Us T) K.
Proof.
  introv IH He1 He2 Hks.
  rewrite <- tenv_subst_concat.
  rewrite <- tenv_subst_empty with (Xs := Xs) (Us := Us).
  rewrite <- concat_assoc.
  apply IH; auto using concat_assoc, type_environment_extend.
  rewrite tenv_subst_empty.
  rewrite concat_assoc.
  rewrite tenv_subst_concat.
  apply kindings_extend;
    autorewrite with rew_env_concat;
    eauto using tenv_subst_type_environment,
      tenv_subst_type_environment_extension with wellformed.
Qed.

Lemma kinding_typ_subst : forall E1 E2 E3 Xs Rs Us T K,
    kinding (E1 & Xs ~* Rs & E2) E3 T K ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    type_environment_extension (E1 & Xs ~* Rs & E2) E3 ->
    kindings (tenv_subst Xs Us (E1 & E2)) (tenv_subst Xs Us E3)
      Us (rngs_kinds (rng_subst_list Xs Us Rs)) ->
    kinding (tenv_subst Xs Us (E1 & E2)) (tenv_subst Xs Us E3)
            (typ_subst Xs Us T) K.
Proof.
  introv Hk Hl He1 He2 Hks.
  remember (E1 & Xs ~* Rs & E2) as E4.
  generalize dependent E2.
  induction Hk; introv Heq Hks; subst; simpl;
    eauto using kinding_typ_subst_rec.
  - rewrite <- rngs_kinds_subst_list in Hks.
    destruct kinding_typ_subst_var
      with (E1 := E1) (E2 := E3)
           (E3 := tenv_subst Xs Us (E1 & E3))
           (E4 := tenv_subst Xs Us E2)
           (Xs := Xs) (Rs := Rs) (Us := Us) (X := X)
           (R := Rng T1 T2 K)
      as [?|[Hb Heq]]; auto.
    rewrite Heq.
    eapply tenv_subst_binds in Hb.
    eauto.
Qed.

Lemma kinding_typ_subst_l : forall E1 E2 Xs Rs Us T K,
    kinding (E1 & Xs ~* Rs) E2 T K ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs) ->
    type_environment_extension (E1 & Xs ~* Rs) E2 ->
    kindings (tenv_subst Xs Us E1) (tenv_subst Xs Us E2)
      Us (rngs_kinds (rng_subst_list Xs Us Rs)) ->
    kinding (tenv_subst Xs Us E1) (tenv_subst Xs Us E2)
      (typ_subst Xs Us T) K.
Proof.
  introv Hk Hl He1 He2 Hks.
  rewrite <- (concat_empty_r E1).
  rewrite <- (concat_empty_r E1) in Hks.
  rewrite <- (concat_empty_r (E1 & Xs ~* Rs)) in Hk, He1, He2.
  eauto using kinding_typ_subst.
Qed.

Lemma kinding_typ_subst_empty : forall E1 E2 Xs Rs Us T K,
    kinding (E1 & Xs ~* Rs & E2) empty T K ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    kindings (tenv_subst Xs Us (E1 & E2)) empty
      Us (rngs_kinds (rng_subst_list Xs Us Rs)) ->
    kinding (tenv_subst Xs Us (E1 & E2)) empty
            (typ_subst Xs Us T) K.
Proof.
  introv Hk Hl He Hrs.
  rewrite <- tenv_subst_empty with (Xs := Xs) (Us := Us) in Hrs.
  rewrite <- tenv_subst_empty with (Xs := Xs) (Us := Us).
  apply kinding_typ_subst with Rs; auto.
Qed.

(* *************************************************************** *)
(** Kindings implied by rangings *)

Lemma ranging_kinding : forall v E1 E2 T R K,
  ranging v E1 E2 T R ->
  K = rng_kind R ->
  kinding E1 E2 T K.
Proof.
  introv Hr Heq.
  induction Hr; subst; simpl; eauto.
Qed.

Lemma rangings_kindings : forall v E1 E2 Ts Rs Ks,
  rangings v E1 E2 Ts Rs ->
  Ks = rngs_kinds Rs ->
  kindings E1 E2 Ts Ks.
Proof.
  introv Hrs Heq.
  generalize dependent Ks.
  induction Hrs; introv Heq; subst; simpl;
    eauto using ranging_kinding.
Qed.

(* *************************************************************** *)
(** Kinding of instances *)

Lemma kinding_instance : forall v E M Us,
  valid_scheme v E M ->
  valid_instance v E Us M ->
  type_environment E ->
  kinding E empty (instance M Us) knd_type.
Proof.
  introv Hs Hi He.
  destruct Hs as [? ? ? ? Hs].
  destruct Hs as [? ? ? ? Hs].
  pick_freshes (sch_arity M) Xs.
  assert (fresh L (sch_arity M) Xs) as Hf by auto.
  fresh_length Hf as Hl.
  specialize (Hs Xs Hf).
  inversion Hs; subst.
  destruct Hi as [? ? Us]; subst.
  assert (length Us = sch_arity M)
    by (erewrite rangings_length; eauto;
        rewrite rng_open_list_length;
        rewrite sch_arity_length;
        reflexivity).
  rewrite typ_subst_intro_instance with (Xs := Xs);
    auto with wellformed.
  replace empty with (tenv_subst Xs Us empty)
    by (rewrite tenv_subst_empty; reflexivity).
  replace E with (tenv_subst Xs Us E)
    by auto using tenv_subst_fresh.
  apply kinding_typ_subst_l
    with (Rs := rng_open_vars_list (sch_ranges M) Xs); auto.
  - rewrite rng_open_vars_list_length.
    rewrite <- sch_arity_length.
    auto.             
  - apply type_environment_extend; try fold (Xs ~: M);
      auto with wellformed.
  - apply rangings_kindings
      with (v := v) (Rs := rng_open_list (sch_ranges M) Us).
    + replace (tenv_subst Xs Us empty) with (empty : tenv)
        by (rewrite tenv_subst_empty; reflexivity).
      replace (tenv_subst Xs Us E) with E
        by (rewrite tenv_subst_fresh; auto).
      auto.
    + rewrite rng_subst_list_intro with (Xs := Xs);
        auto with wellformed.
      apply fresh_subset with (sch_fv M);
        auto using sch_fv_ranges.
Qed.

(* *************************************************************** *)
(** Type equality preserved by type substitution *)

(* Lemma for kinding judgements in contractive positions *)

Lemma kinding_typ_subst_assoc : forall E1 E2 E3 Xs Rs Us T K,
    kinding (E1 & Xs ~* Rs & E2 & E3) empty T K ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    type_environment_extension (E1 & Xs ~* Rs & E2) E3 ->
    kindings (tenv_subst Xs Us (E1 & E2)) (tenv_subst Xs Us E3)
      Us (rngs_kinds (rng_subst_list Xs Us Rs)) ->
    kinding (tenv_subst Xs Us (E1 & E2) & tenv_subst Xs Us E3)
      empty (typ_subst Xs Us T) K.
Proof.
  introv Hk Hl He1 He2 Hks.
  rewrite <- tenv_subst_concat.
  rewrite <- concat_assoc.
  rewrite <- tenv_subst_empty with (Xs := Xs) (Us := Us).
  eapply kinding_typ_subst; rewrite? concat_assoc;
    eauto using type_environment_extend.
  rewrite tenv_subst_concat.
  rewrite tenv_subst_empty.
  apply kindings_extend;
    autorewrite with rew_env_concat;
    eauto using tenv_subst_type_environment,
      tenv_subst_type_environment_extension with wellformed.
Qed.  

Lemma type_equal_core_typ_subst :
  forall v Xs Us T1 T2 K,
  type_equal_core v T1 T2 K ->
  type_equal_core v (typ_subst Xs Us T1) (typ_subst Xs Us T2) K.
Proof.
  introv Hte.
  destruct Hte; simpl; auto.
Qed.

Lemma ranging_typ_subst_var :
  forall v E1 E2 E3 E4 Xs Rs Us Ys Ts X R,
    binds X R (E1 & Xs ~* Rs & E2) ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    rangings v E3 E4 Us (rng_subst_list Ys Ts Rs) ->
    ranging v E3 E4 (typ_var_subst Xs Us X) (rng_subst Ys Ts R)
    \/ (binds X R (E1 & E2)
        /\ typ_var_subst Xs Us X = typ_fvar X).
Proof.
  introv Hb Hl1 He Hrs.
  assert (length Us = length Rs) as Hl2
    by (erewrite length_rng_subst_list; eauto using rangings_length).
  generalize dependent Rs.
  generalize dependent Us.
  induction Xs; introv Hb Hl1 He Hrs Hl2; destruct Rs; destruct Us;
    try discriminate; simpl in *;
    autorewrite with rew_env_concat in *; auto.
  inversion Hrs; subst.
  case_var.
  - apply binds_middle_eq_inv in Hb; subst;
      auto using ok_from_type_environment.
  - eauto using binds_subst, type_environment_remove.     
Qed.

Lemma type_equal_typ_subst_rec :
  forall v E1 E2 E3 Q1 Q2 Xs Rs Us T1 T2 K Tl Tr Klr,
  (type_environment (E1 & Xs ~* Rs & E2 & E3) ->
   type_environment_extension
     (E1 & Xs ~* Rs & E2 & E3) empty ->
   forall E4 : LibEnv.env rng,
     E1 & Xs ~* Rs & E2 & E3 = E1 & Xs ~* Rs & E4 ->
     rangings v (tenv_subst Xs Us (E1 & E4))
       (tenv_subst Xs Us empty) Us
       (rng_subst_list Xs Us Rs) ->
     type_equal v (tenv_subst Xs Us (E1 & E4))
       (tenv_subst Xs Us empty)
       ((Tl, Tr, Klr) :: qenv_subst Xs Us (Q2 ++ Q1))%list
       (qenv_subst Xs Us nil)
       (typ_subst Xs Us T1)
       (typ_subst Xs Us T2) K) ->
  type_environment_extension (E1 & Xs ~* Rs & E2) E3 ->
  type_environment (E1 & Xs ~* Rs & E2) ->
  rangings v (tenv_subst Xs Us (E1 & E2))
    (tenv_subst Xs Us E3) Us
    (rng_subst_list Xs Us Rs) ->
  type_equal v
    (tenv_subst Xs Us (E1 & E2) & tenv_subst Xs Us E3) empty
    ((Tl, Tr, Klr)
       :: (qenv_subst Xs Us Q2) ++ (qenv_subst Xs Us Q1))%list
    nil (typ_subst Xs Us T1) (typ_subst Xs Us T2) K.
Proof.
  introv IH He1 He2 Hrs.
  rewrite <- tenv_subst_empty with (Xs := Xs) (Us := Us).
  rewrite <- tenv_subst_concat.
  rewrite <- concat_assoc.
  rewrite <- qenv_subst_nil with (Xs := Xs) (Us := Us).
  rewrite <- qenv_subst_app.
  apply IH; rewrite? concat_assoc;
    auto using type_environment_extend.
  rewrite tenv_subst_concat.
  apply rangings_extend;
    eauto using tenv_subst_type_environment_extension
    with wellformed.
  rewrite tenv_subst_empty.
  rewrite concat_empty_r.
  assumption.
Qed.

Lemma type_equal_typ_subst : forall v E1 E2 E3 Q1 Q2 Xs Rs Us T1 T2 K,
  type_equal v (E1 & Xs ~* Rs & E2) E3 Q1 Q2 T1 T2 K ->
  length Xs = length Rs ->
  type_environment (E1 & Xs ~* Rs & E2) ->
  type_environment_extension (E1 & Xs ~* Rs & E2) E3 ->
  rangings v (tenv_subst Xs Us (E1 & E2)) (tenv_subst Xs Us E3)
    Us (rng_subst_list Xs Us Rs) ->
  type_equal v (tenv_subst Xs Us (E1 & E2)) (tenv_subst Xs Us E3)
    (qenv_subst Xs Us Q1) (qenv_subst Xs Us Q2)
    (typ_subst Xs Us T1) (typ_subst Xs Us T2) K.
Proof.
  introv Hte Hl He1 He2 Hrs.
  remember (E1 & Xs ~* Rs & E2) as E12.
  generalize dependent E2.
  induction Hte; introv Heq Hrs; subst; simpl in *; auto.
  - destruct ranging_typ_subst_var
      with (E1 := E1) (E2 := E3) (E3 := tenv_subst Xs Us (E1 & E3))
           (E4 := tenv_subst Xs Us E2)
           (Xs := Xs) (Rs := Rs) (Us := Us) (Ys := Xs) (Ts := Us)
           (X := X) (R := Rng T1 T2 K) (v := v)
      as [Hr|[Hb Heq]]; auto.
    + inversion Hr; subst.
      apply type_equal_weakening_eqn_nils; auto.
    + rewrite Heq in *.
      apply tenv_subst_binds with (Zs := Xs) (Us := Us) in Hb.
      unfold rng_subst in Hb; simpl in Hb.
      eauto.
  - destruct ranging_typ_subst_var
      with (E1 := E1) (E2 := E3) (E3 := tenv_subst Xs Us (E1 & E3))
           (E4 := tenv_subst Xs Us E2)
           (Xs := Xs) (Rs := Rs) (Us := Us) (Ys := Xs) (Ts := Us)
           (X := X) (R := Rng T1 T2 K) (v := v)
      as [Hr|[Hb Heq]]; auto.
    + inversion Hr; subst.
      apply type_equal_weakening_eqn_nils; auto.
    + rewrite Heq in *.
      apply tenv_subst_binds with (Zs := Xs) (Us := Us) in Hb.
      unfold rng_subst in Hb; simpl in Hb.
      eauto.
  - eauto using type_equal_typ_subst_rec.
  - eauto using type_equal_typ_subst_rec.
  - eauto using type_equal_typ_subst_rec.
  - eauto using type_equal_typ_subst_rec.
  - eauto using type_equal_typ_subst_rec.
  - apply type_equal_of_core; eauto using type_equal_core_typ_subst,
      kinding_typ_subst, rangings_kindings.
  - apply type_equal_rec; eauto using kinding_typ_subst,
      rangings_kindings, qenv_subst_in.
  - eauto using kinding_typ_subst, rangings_kindings.
  - eauto.
Qed.

Lemma type_equal_typ_subst_l : forall v E1 E2 Q1 Q2 Xs Rs Us T1 T2 K,
  type_equal v (E1 & Xs ~* Rs) E2 Q1 Q2 T1 T2 K ->
  length Xs = length Rs ->
  type_environment (E1 & Xs ~* Rs) ->
  type_environment_extension (E1 & Xs ~* Rs) E2 ->
  rangings v (tenv_subst Xs Us E1) (tenv_subst Xs Us E2)
    Us (rng_subst_list Xs Us Rs) ->
  type_equal v (tenv_subst Xs Us E1) (tenv_subst Xs Us E2)
    (qenv_subst Xs Us Q1) (qenv_subst Xs Us Q2)
    (typ_subst Xs Us T1) (typ_subst Xs Us T2) K.
Proof.
  introv Hte Hl He1 He2 Hrs.
  rewrite <- (concat_empty_r E1).
  rewrite <- (concat_empty_r E1) in Hrs.
  rewrite <- (concat_empty_r (E1 & Xs ~* Rs)) in Hte, He1, He2.
  eauto using type_equal_typ_subst.
Qed.

Lemma type_equal_typ_subst_empty : forall v E1 E2 Xs Rs Us T1 T2 K,
  type_equal v (E1 & Xs ~* Rs & E2) empty nil nil T1 T2 K ->
  length Xs = length Rs ->
  type_environment (E1 & Xs ~* Rs & E2) ->
  rangings v (tenv_subst Xs Us (E1 & E2)) empty
    Us (rng_subst_list Xs Us Rs) ->
  type_equal v (tenv_subst Xs Us (E1 & E2)) empty nil nil
    (typ_subst Xs Us T1) (typ_subst Xs Us T2) K.
Proof.
  introv Hte Hl He Hrs.
  rewrite <- tenv_subst_empty with (Xs := Xs) (Us := Us) in Hrs.
  rewrite <- tenv_subst_empty with (Xs := Xs) (Us := Us).
  rewrite <- qenv_subst_nil with (Xs := Xs) (Us := Us).
  apply type_equal_typ_subst with Rs; auto.
Qed.

Lemma subtype_typ_subst : forall v E1 E2 E3 Q1 Q2 Xs Rs Us T1 T2 K,
  subtype v (E1 & Xs ~* Rs & E2) E3 Q1 Q2 T1 T2 K ->
  length Xs = length Rs ->
  type_environment (E1 & Xs ~* Rs & E2) ->
  type_environment_extension (E1 & Xs ~* Rs & E2) E3 ->
  rangings v (tenv_subst Xs Us (E1 & E2)) (tenv_subst Xs Us E3)
    Us (rng_subst_list Xs Us Rs) ->
  subtype v (tenv_subst Xs Us (E1 & E2)) (tenv_subst Xs Us E3)
    (qenv_subst Xs Us Q1) (qenv_subst Xs Us Q2)
    (typ_subst Xs Us T1) (typ_subst Xs Us T2) K.
Proof.
  introv Hsb Hl He1 He2 Hrs.
  unfold subtype.
  replace (typ_meet (typ_subst Xs Us T1) (typ_subst Xs Us T2))
    with (typ_subst Xs Us (typ_meet T1 T2)) by auto.
  eauto using type_equal_typ_subst.
Qed.

Lemma subtype_typ_subst_l : forall v E1 E2 Q1 Q2 Xs Rs Us T1 T2 cs,
  subtype v (E1 & Xs ~* Rs) E2 Q1 Q2 T1 T2 cs ->
  length Xs = length Rs ->
  type_environment (E1 & Xs ~* Rs) ->
  type_environment_extension (E1 & Xs ~* Rs) E2 ->
  rangings v (tenv_subst Xs Us E1) (tenv_subst Xs Us E2)
    Us (rng_subst_list Xs Us Rs) ->
  subtype v (tenv_subst Xs Us E1) (tenv_subst Xs Us E2)
    (qenv_subst Xs Us Q1) (qenv_subst Xs Us Q2)
    (typ_subst Xs Us T1) (typ_subst Xs Us T2) cs.
Proof.
  introv Hsb Hl He1 He2 Hrs.
  rewrite <- (concat_empty_r E1).
  rewrite <- (concat_empty_r E1) in Hrs.
  rewrite <- (concat_empty_r (E1 & Xs ~* Rs)) in Hsb, He1, He2.
  eauto using subtype_typ_subst.
Qed.

Lemma subtype_typ_subst_empty : forall v E1 E2 Xs Rs Us T1 T2 K,
  subtype v (E1 & Xs ~* Rs & E2) empty nil nil T1 T2 K ->
  length Xs = length Rs ->
  type_environment (E1 & Xs ~* Rs & E2) ->
  rangings v (tenv_subst Xs Us (E1 & E2)) empty
    Us (rng_subst_list Xs Us Rs) ->
  subtype v (tenv_subst Xs Us (E1 & E2)) empty nil nil
    (typ_subst Xs Us T1) (typ_subst Xs Us T2) K.
Proof.
  introv Hs Hl He Hrs.
  rewrite <- tenv_subst_empty with (Xs := Xs) (Us := Us) in Hrs.
  rewrite <- tenv_subst_empty with (Xs := Xs) (Us := Us).
  rewrite <- qenv_subst_nil with (Xs := Xs) (Us := Us).
  apply subtype_typ_subst with Rs; auto.
Qed.

(* *************************************************************** *)
(** Valid environment extensions preserved by type substitution *)

Lemma valid_range_typ_subst : forall v E1 E2 E3 Xs Rs Us R,
    valid_range v (E1 & Xs ~* Rs & E2) E3 R ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    type_environment_extension (E1 & Xs ~* Rs & E2) E3 ->
    rangings v (tenv_subst Xs Us (E1 & E2)) (tenv_subst Xs Us E3)
      Us (rng_subst_list Xs Us Rs) ->
    valid_range v (tenv_subst Xs Us (E1 & E2)) (tenv_subst Xs Us E3)
      (rng_subst Xs Us R).
Proof.
  introv Hr Hl He1 He2 Hrs.
  remember (E1 & Xs ~* Rs & E2) as E12.
  destruct Hr; subst.
  constructor;
    try rewrite <- qenv_subst_nil with (Xs := Xs) (Us := Us);
    eauto using subtype_typ_subst,
      kinding_typ_subst, rangings_kindings.
Qed.

Lemma valid_tenv_rec_typ_subst : forall v E1 E2 E3 E4 Xs Rs Us,
    valid_tenv_rec v (E1 & Xs ~* Rs & E2) E3 E4 ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    type_environment_extension (E1 & Xs ~* Rs & E2) E3 ->
    type_environment_extension (E1 & Xs ~* Rs & E2 & E3) E4 ->
    rangings v (tenv_subst Xs Us (E1 & E2))
      (tenv_subst Xs Us (E3 & E4)) Us (rng_subst_list Xs Us Rs) ->
    valid_tenv_rec v (tenv_subst Xs Us (E1 & E2))
      (tenv_subst Xs Us E3) (tenv_subst Xs Us E4).
Proof.
  introv He Hl He1 He2 He3 Hrs.
  remember (E1 & Xs ~* Rs & E2) as E12.
  induction He; subst; autorewrite with rew_tenv_subst in *; auto.
  autorewrite with rew_env_concat in *.
  destruct (type_environment_push_inv He2) as [? [? [? ?]]].
  apply type_environment_extension_strengthen_l in He3.
  apply type_environment_extension_rev_push
    with (X := X) (R := R) in He3; auto.
  constructor; autorewrite with rew_tenv_dom; auto.
  rewrite <- concat_assoc.
  rewrite <- tenv_subst_single.
  rewrite <- tenv_subst_concat.
  rewrite <- tenv_subst_concat.
  rewrite <- tenv_subst_concat.
  eapply valid_range_typ_subst;
    rewrite? concat_assoc; eauto using type_environment_extend.
  autorewrite with rew_tenv_subst.
  apply rangings_extend; rewrite? concat_assoc; auto.
  rewrite <- tenv_subst_concat.
  eauto using tenv_subst_type_environment_extension with wellformed.
Qed.

Lemma valid_tenv_extension_typ_subst : forall v E1 E2 E3 Xs Rs Us,
    valid_tenv_extension v (E1 & Xs ~* Rs & E2) E3 ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    rangings v (tenv_subst Xs Us (E1 & E2)) (tenv_subst Xs Us E3)
      Us (rng_subst_list Xs Us Rs) ->
    valid_tenv_extension v (tenv_subst Xs Us (E1 & E2))
      (tenv_subst Xs Us E3).
Proof.
  introv Hx Hl He Hrs.
  unfold valid_tenv_extension.
  rewrite <- tenv_subst_empty with (Xs := Xs) (Us := Us).
  rewrite <- concat_empty_r with (E := E3) in Hrs.
  eauto using valid_tenv_rec_typ_subst with wellformed.
Qed.

(* *************************************************************** *)
(** Valid schemes preserved by type substitution *)

Lemma valid_tenv_extension_and_type_typ_subst :
  forall v E1 E2 E3 Xs Rs Us T,
    valid_tenv_extension_and_type v (E1 & Xs ~* Rs & E2) E3 T ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    rangings v (tenv_subst Xs Us (E1 & E2)) (tenv_subst Xs Us E3)
      Us (rng_subst_list Xs Us Rs) ->
    valid_tenv_extension_and_type v (tenv_subst Xs Us (E1 & E2))
      (tenv_subst Xs Us E3) (typ_subst Xs Us T).
Proof.
  introv Het Hl He Hrs.
  remember (E1 & Xs ~* Rs & E2) as E12.
  destruct Het; subst.
  eauto using valid_tenv_extension_typ_subst,
    kinding_typ_subst_assoc, rangings_kindings with wellformed.
Qed.

Lemma valid_scheme_aux_typ_subst : forall v E1 E2 Xs Rs Us L M,
    valid_scheme_aux v L (E1 & Xs ~* Rs & E2) M ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    rangings v (tenv_subst Xs Us (E1 & E2)) empty
      Us (rng_subst_list Xs Us Rs) ->
    valid_scheme_aux v (dom (E1 & Xs ~* Rs & E2) \u L)
      (tenv_subst Xs Us (E1 & E2)) (sch_subst Xs Us M).
Proof.
  introv Hs Hl He Hrs.
  assert (scheme_aux L M) by auto with wellformed.
  remember (E1 & Xs ~* Rs & E2) as E12.
  destruct Hs; subst.
  apply valid_scheme_aux_c.
  intros Ys Hf.
  fresh_length Hf as Hl2.
  autorewrite with rew_sch_arity in Hl2, Hf.
  assert (type_environment_extension
            (E1 & Xs ~* Rs & E2) (Ys ~: M))
    by (apply type_environment_extension_ranges with L; auto).
  autorewrite with rew_tenv_dom in Hf.
  rewrite <- tenv_subst_ranges; auto with wellformed.
  rewrite <- sch_subst_instance_vars; auto with wellformed.
  apply valid_tenv_extension_and_type_typ_subst with Rs;
    eauto using rangings_weakening_rec_empty,
      tenv_subst_type_environment,
        tenv_subst_type_environment_extension with wellformed.
Qed.

Lemma valid_scheme_typ_subst : forall v E1 E2 Xs Rs Us M,
    valid_scheme v (E1 & Xs ~* Rs & E2) M ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    rangings v (tenv_subst Xs Us (E1 & E2)) empty
      Us (rng_subst_list Xs Us Rs) ->
    valid_scheme v (tenv_subst Xs Us (E1 & E2)) (sch_subst Xs Us M).
Proof.
  introv Hs Hl He Hrs.
  remember (E1 & Xs ~* Rs & E2) as E12.
  destruct Hs as [L ? ? ? Hs]; subst.
  apply valid_scheme_c with (dom (E1 & Xs ~* Rs & E2) \u L).
  apply valid_scheme_aux_typ_subst; auto.
Qed.

Lemma valid_schemes_typ_subst : forall v E1 E2 Xs Rs Us Ms,
    valid_schemes v (E1 & Xs ~* Rs & E2) Ms ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    rangings v (tenv_subst Xs Us (E1 & E2)) empty
      Us (rng_subst_list Xs Us Rs) ->
    valid_schemes v (tenv_subst Xs Us (E1 & E2))
      (sch_subst_list Xs Us Ms).
Proof.
  introv Hss Hl He Hrs.
  remember (E1 & Xs ~* Rs & E2) as E12.
  induction Hss; subst; simpl; eauto using valid_scheme_typ_subst.
Qed.

(* *************************************************************** *)
(** Valid instances preserved by type substitution *)

Lemma ranging_typ_subst : forall v E1 E2 E3 Xs Rs Us T R,
    ranging v (E1 & Xs ~* Rs & E2) E3 T R ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    type_environment_extension (E1 & Xs ~* Rs & E2) E3 ->
    rangings v (tenv_subst Xs Us (E1 & E2)) (tenv_subst Xs Us E3)
      Us (rng_subst_list Xs Us Rs) ->
    ranging v (tenv_subst Xs Us (E1 & E2)) (tenv_subst Xs Us E3)
      (typ_subst Xs Us T) (rng_subst Xs Us R).
Proof.
  introv Hr Hl He1 He2 Hrs.
  remember (E1 & Xs ~* Rs & E2) as E12.
  destruct Hr; subst.
  constructor;
    try rewrite <- qenv_subst_nil with (Xs := Xs) (Us := Us);
    eauto using subtype_typ_subst, kinding_typ_subst,
      rangings_kindings.
Qed.

Lemma ranging_typ_subst_l : forall v E1 E2 Xs Rs Us T R,
    ranging v (E1 & Xs ~* Rs) E2 T R ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs) ->
    type_environment_extension (E1 & Xs ~* Rs) E2 ->
    rangings v (tenv_subst Xs Us E1) (tenv_subst Xs Us E2)
      Us (rng_subst_list Xs Us Rs) ->
    ranging v (tenv_subst Xs Us E1) (tenv_subst Xs Us E2)
      (typ_subst Xs Us T) (rng_subst Xs Us R).
Proof.
  introv Hr Hl He1 He2 Hrs.
  rewrite <- (concat_empty_r E1).
  rewrite <- (concat_empty_r E1) in Hrs.
  rewrite <- (concat_empty_r (E1 & Xs ~* Rs)) in Hr, He1, He2.
  eauto using ranging_typ_subst.
Qed.

Lemma rangings_typ_subst : forall v E1 E2 E3 Xs Rs1 Us Ts Rs2,
    rangings v (E1 & Xs ~* Rs1 & E2) E3 Ts Rs2 ->
    length Xs = length Rs1 ->
    type_environment (E1 & Xs ~* Rs1 & E2) ->
    type_environment_extension (E1 & Xs ~* Rs1 & E2) E3 ->
    rangings v (tenv_subst Xs Us (E1 & E2)) (tenv_subst Xs Us E3)
      Us (rng_subst_list Xs Us Rs1) ->
    rangings v (tenv_subst Xs Us (E1 & E2)) (tenv_subst Xs Us E3)
      (typ_subst_list Xs Us Ts) (rng_subst_list Xs Us Rs2).
Proof.
  introv Hrs1 Hl He1 He2 Hrs2.
  remember (E1 & Xs ~* Rs1 & E2) as E12.
  induction Hrs1; subst; simpl; eauto using ranging_typ_subst.
Qed.

Lemma rangings_typ_subst_empty : forall v E1 E2 Xs Rs1 Us Ts Rs2,
    rangings v (E1 & Xs ~* Rs1 & E2) empty Ts Rs2 ->
    length Xs = length Rs1 ->
    type_environment (E1 & Xs ~* Rs1 & E2) ->
    rangings v (tenv_subst Xs Us (E1 & E2)) empty
      Us (rng_subst_list Xs Us Rs1) ->
    rangings v (tenv_subst Xs Us (E1 & E2)) empty
      (typ_subst_list Xs Us Ts) (rng_subst_list Xs Us Rs2).
Proof.
  introv Hrs1 Hl He Hrs2.
  rewrite <- tenv_subst_empty with (Xs := Xs) (Us := Us) in Hrs2.
  rewrite <- tenv_subst_empty with (Xs := Xs) (Us := Us).
  apply rangings_typ_subst with Rs1; auto.
Qed.

Lemma valid_instance_typ_subst : forall v E1 E2 Xs Rs Us Ts M,
    valid_instance v (E1 & Xs ~* Rs & E2) Ts M ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    rangings v (tenv_subst Xs Us (E1 & E2)) empty
      Us (rng_subst_list Xs Us Rs) ->
    valid_instance v (tenv_subst Xs Us (E1 & E2))
      (typ_subst_list Xs Us Ts) (sch_subst Xs Us M).
Proof.
  introv Hv Hl He Hrs.
  remember (E1 & Xs ~* Rs & E2) as E12.
  destruct Hv; subst.
  apply valid_instance_c
    with (rng_subst_list Xs Us (rng_open_list (sch_ranges M) Ts));
    eauto using rangings_typ_subst_empty.
  apply rng_subst_list_open; auto with wellformed.
Qed.

(* ****************************************************** *)
(** ** Type substitution *)

Lemma rangings_add_subst_ranges : forall v E1 E2 Zs Us Rs Xs L M,
    scheme_aux L M ->
    fresh (dom E1 \u dom E2 \u from_list Zs \u L) (sch_arity M) Xs ->
    rangings v (tenv_subst Zs Us (E1 & E2)) empty Us
      (rng_subst_list Zs Us Rs) ->
    type_environment (E1 & Zs ~* Rs & E2) ->
    rangings v (tenv_subst Zs Us (E1 & (E2 & Xs ~: M))) empty Us
      (rng_subst_list Zs Us Rs).
Proof.
  introv Hs Hf Hrs He.
  fresh_length Hf as Hl.
  rewrite concat_assoc.
  rewrite tenv_subst_concat.
  rewrite tenv_subst_ranges; auto with wellformed.
  apply rangings_weakening_l; auto.
  apply scheme_aux_subset with (L2 := L \u from_list Zs) in Hs;
    auto using subset_union_weak_l.
  apply type_environment_push_ranges with (L \u from_list Zs);
    eauto using tenv_subst_type_environment,
      type_environment_remove with wellformed;
    autorewrite with rew_sch_arity;
    autorewrite with rew_tenv_subst;
    autorewrite with rew_tenv_dom;
   try apply sch_subst_scheme_aux;
   auto using subset_union_weak_r with wellformed.
Qed.

Lemma type_environment_push_subst_ranges : forall E1 E2 Xs Rs Ys L M,
    type_environment (E1 & Xs ~* Rs & E2) ->
    length Xs = length Rs ->
    scheme_aux L M ->
    fresh (dom E1 \u from_list Xs \u dom E2 \u L) (sch_arity M) Ys ->
    type_environment (E1 & Xs ~* Rs & (E2 & Ys ~: M)).
Proof.
  introv He Hl Hs Hf.
  rewrite concat_assoc.
  apply type_environment_push_ranges with L;
    autorewrite with rew_tenv_dom; auto.
Qed.

Lemma typing_typ_subst : forall v E1 E2 Xs Rs Us D P t T,
    typing v (E1 & Xs ~* Rs & E2) D P t T ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    rangings v (tenv_subst Xs Us (E1 & E2)) empty
      Us (rng_subst_list Xs Us Rs) ->
    typing v (tenv_subst Xs Us (E1 & E2))
      (env_subst Xs Us D) (styp_subst Xs Us P) t
           (typ_subst Xs Us T).
Proof.
  introv Ht Hl He Hrs.
  remember (E1 & Xs ~* Rs & E2) as E12 in Ht.
  generalize dependent E2.
  induction Ht; introv Heq He Hrs; subst;
    eauto using type_equal_typ_subst_empty, subtype_typ_subst_empty.
  - eapply typing_var;
      eauto using env_subst_binds, valid_instance_typ_subst.
    rewrite <- sch_subst_instance;
      eauto using type_equal_typ_subst with wellformed.
  - apply_fresh typing_abs as x;
      eauto using kinding_typ_subst_empty, rangings_kindings.
    fold typ_subst.
    replace (sch_empty (typ_subst Xs Us T1))
      with (sch_subst Xs Us (sch_empty T1)) by reflexivity.
    rewrite <- env_subst_push; auto.
  - apply typing_let_val
      with (L := dom (E1 & Xs ~* Rs & E2) \u L)
           (M := sch_subst Xs Us M);
      eauto using valid_scheme_aux_typ_subst.
    + introv Hf.
      autorewrite with rew_sch_arity in Hf.
      autorewrite with rew_tenv_dom in Hf.
      fresh_length Hf as Hl2.
      rewrite <- tenv_subst_ranges;
        autorewrite with rew_env_dom; auto with wellformed.
      rewrite <- tenv_subst_concat.
      rewrite <- concat_assoc.
      unfold instance_vars.
      rewrite <- typ_subst_fresh_typ_fvars
        with (Xs := Xs) (Us := Us); auto.
      rewrite <- sch_subst_instance; auto with wellformed.
      assert
        (scheme_aux (((dom E1 \u from_list Xs) \u dom E2) \u L) M)
        by (apply scheme_aux_subset with (L1 := L);
              auto using subset_union_weak_r with wellformed).
      eauto 6 using concat_assoc, rangings_add_subst_ranges,
        type_environment_push_subst_ranges
          with wellformed.
    + introv Hn.
      rewrite <- env_subst_push; auto.
  - apply typing_let
      with (L := L \u from_list Xs \u dom E1 \u dom E2)
             (T1 := typ_subst Xs Us T1);
      eauto using kinding_typ_subst_empty, rangings_kindings.
    introv Hn.
    replace (sch_empty (typ_subst Xs Us T1))
      with (sch_subst Xs Us (sch_empty T1)) by reflexivity.
    rewrite <- env_subst_push; auto.
  - apply typing_constructor with (T1 := typ_subst Xs Us T1); auto.
    fold typ_subst.
    replace (typ_constructor c (typ_subst Xs Us T1))
      with (typ_subst Xs Us (typ_constructor c T1))
      by reflexivity.
    replace (typ_proj CSet.universe (CSet.singleton c)
                      (typ_subst Xs Us T2))
      with (typ_subst Xs Us (typ_proj CSet.universe
                                      (CSet.singleton c) T2))
      by reflexivity.
    eauto using subtype_typ_subst_empty.
  - apply typing_match
      with (T1 := typ_subst Xs Us T1) (T2 := typ_subst Xs Us T2)
           (T3 := typ_subst Xs Us T3)
           (L := L \u dom E1 \u dom E2); auto.
    + replace
        (typ_proj CSet.universe (CSet.singleton c)
                  (typ_subst Xs Us T1))
        with (typ_subst Xs Us
                (typ_proj CSet.universe (CSet.singleton c) T1))
        by reflexivity.
      replace
        (typ_proj CSet.universe (CSet.singleton c)
                  (typ_subst Xs Us T2))
        with (typ_subst Xs Us
                (typ_proj CSet.universe (CSet.singleton c) T2))
        by reflexivity.
      eauto using subtype_typ_subst_empty.
    + replace
        (typ_proj CSet.universe (CSet.cosingleton c)
                  (typ_subst Xs Us T1))
        with (typ_subst Xs Us
                (typ_proj CSet.universe (CSet.cosingleton c) T1))
        by reflexivity.
      replace
        (typ_proj CSet.universe (CSet.cosingleton c)
                  (typ_subst Xs Us T3))
        with (typ_subst Xs Us
                (typ_proj CSet.universe (CSet.cosingleton c) T3))
        by reflexivity.
      eauto using subtype_typ_subst_empty.
    + replace (sch_empty (typ_variant (typ_subst Xs Us T2)))
        with (sch_subst Xs Us (sch_empty (typ_variant T2)))
        by reflexivity.
      introv Hn.
      rewrite <- env_subst_push.
      auto.
    + replace (sch_empty (typ_variant (typ_subst Xs Us T3)))
        with (sch_subst Xs Us (sch_empty (typ_variant T3)))
        by reflexivity.
      introv Hn.
      rewrite <- env_subst_push.
      auto.
  - apply typing_destruct
      with (T1 := typ_subst Xs Us T1) (T2 := typ_subst Xs Us T2)
           (L := L \u dom E1 \u dom E2); auto.
    + replace
        (typ_proj CSet.universe (CSet.singleton c)
                  (typ_subst Xs Us T1))
        with (typ_subst Xs Us
                (typ_proj CSet.universe (CSet.singleton c) T1))
        by reflexivity.
      replace (typ_constructor c (typ_subst Xs Us T2))
        with (typ_subst Xs Us (typ_constructor c T2)) by reflexivity.
      eauto using subtype_typ_subst_empty.
    + replace
        (typ_proj CSet.universe (CSet.cosingleton c)
                  (typ_subst Xs Us T1))
        with (typ_subst Xs Us
                (typ_proj CSet.universe (CSet.cosingleton c) T1))
        by reflexivity.
      replace (typ_bot (knd_row (CSet.cosingleton c)))
        with (typ_subst Xs Us
                (typ_bot (knd_row (CSet.cosingleton c))))
        by reflexivity.
      eauto using subtype_typ_subst_empty.
    + replace (sch_empty (typ_subst Xs Us T2))
        with (sch_subst Xs Us (sch_empty T2)) by reflexivity.
      introv Hn.
      rewrite <- env_subst_push.
      auto.
  - apply typing_absurd with (T1 := typ_subst Xs Us T1);
      eauto using kinding_typ_subst_empty, rangings_kindings.
    replace (typ_bot knd_row_all)
      with (typ_subst Xs Us (typ_bot knd_row_all)) by reflexivity.
    eauto using subtype_typ_subst_empty.
  - apply_fresh typing_fix as x;
      eauto using kinding_typ_subst_empty, rangings_kindings.
    introv Hn1 Hn2.
    fold typ_subst.
    replace (sch_empty (typ_arrow (typ_subst Xs Us T1)
                                  (typ_subst Xs Us T2)))
      with (sch_subst Xs Us (sch_empty (typ_arrow T1 T2)))
      by reflexivity.
    replace (sch_empty (typ_subst Xs Us T1))
      with (sch_subst Xs Us (sch_empty T1)) by reflexivity.
    rewrite <- env_subst_push.
    rewrite <- env_subst_push.
    auto.
  - apply typing_prod; auto.
  - apply typing_loc with (T1 := typ_subst Xs Us T1);
      eauto using styp_subst_binds.
  - apply typing_ref; auto.
Qed.

Lemma typing_typ_subst_l : forall v E Xs Rs Us D P t T,
    typing v (E & Xs ~* Rs) D P t T ->
    length Xs = length Rs ->
    type_environment (E & Xs ~* Rs) ->
    rangings v (tenv_subst Xs Us E) empty
      Us (rng_subst_list Xs Us Rs) ->
    typing v (tenv_subst Xs Us E)
      (env_subst Xs Us D) (styp_subst Xs Us P) t
           (typ_subst Xs Us T).
Proof.
  introv Ht Hl He Hrs.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- concat_empty_r with (E := E & Xs ~* Rs) in He, Ht.
  rewrite <- concat_empty_r with (E := E) in Hrs.
  eauto using typing_typ_subst.
Qed.

Lemma typing_instance : forall v E M D P t Us,
  typing_scheme v E D P t M ->
  valid_instance v E Us M ->
  type_environment E ->
  typing v E D P t (instance M Us). 
Proof.
  introv Hs Hv He.
  destruct Hs as [L ? ? ? ? ? ? Hs].
  pick_freshes (sch_arity M) Xs.
  fresh_length Fr as Hl.
  assert (fresh L (sch_arity M) Xs) as Hf2 by auto.
  specialize (Hs Xs Hf2).
  inversion Hs; subst.
  inversion Hv; subst; simpl in *.
  assert (length Us = sch_arity M)
    by (erewrite rangings_length,
          <- length_rng_open_list, sch_arity_length; eauto).
  rewrite typ_subst_intro_instance with (Xs := Xs);
    auto with wellformed.
  assert (type_environment_extension E (Xs ~: M))
    by auto with wellformed.
  unfold bind_sch_ranges, instance_vars, instance in *.
  destruct M; simpl in *.
  rewrite <- styp_subst_fresh with (Xs := Xs) (Us := Us) (P := P);
    auto.
  rewrite <- env_subst_fresh with (Xs := Xs) (Us := Us) (D := D);
    auto.
  rewrite <- tenv_subst_fresh with (Xs := Xs) (Us := Us) (E := E);
    auto.
  apply typing_typ_subst_l
    with (Rs := rng_open_vars_list sch_ranges Xs);
    rewrite <- ?length_rng_open_vars_list;
      auto using type_environment_extend. 
  rewrite tenv_subst_fresh with (Xs := Xs) (Us := Us) (E := E); auto.
  rewrite <- rng_subst_list_intro; auto with wellformed.
Qed.

(* *************************************************************** *)
(** Somes useful lemmas for proofs about term subtitution *)

Lemma typing_schemes_add_subst_typ_bind :
  forall v E D1 D2 P x M Ms ts,
    x \notin (dom D1 \u dom D2) ->
    typing_schemes v E (D1 & D2) P ts Ms ->
    scheme M ->
    type_environment E ->
    environment (D1 & D2) ->
    store_type P ->
    typing_schemes v E (D1 & (D2 & x ~ M)) P ts Ms.
Proof.
  introv Hn Hss Hs He Hd Hp.
  rewrite concat_assoc.
  apply typing_schemes_env_weakening_l; auto.
Qed.

Lemma typing_schemes_add_subst_typ_bind_empty :
  forall v E D1 D2 P x T Ms ts,
    x \notin (dom D1 \u dom D2) ->
    typing_schemes v E (D1 & D2) P ts Ms ->
    type T ->
    type_environment E ->
    environment (D1 & D2) ->
    store_type P ->
    typing_schemes v E (D1 & (D2 & x ~ sch_empty T)) P ts Ms.
Proof.
  introv Hn Hss Hk He Hd Hp.
  apply typing_schemes_add_subst_typ_bind; auto.
Qed.

Lemma typing_schemes_add_subst_typ_bind_empty2 :
  forall v E D1 D2 P x T y U Ms ts,
    x \notin (dom D1 \u dom D2) ->
    y \notin (dom D1 \u dom D2 \u \{x}) ->
    typing_schemes v E (D1 & D2) P ts Ms ->
    type T ->
    type U ->
    type_environment E ->
    environment (D1 & D2) ->
    store_type P ->
    typing_schemes
      v E (D1 & (D2 & x ~ sch_empty T & y ~ sch_empty U)) P ts Ms.
Proof.
  introv Hn1 Hn2 Hss Hk1 Hk2 He Hd Hp.
  rewrite concat_assoc2.
  apply typing_schemes_env_weakening_l;
    auto using environment_push2.
  apply typing_schemes_env_weakening_l; auto.
Qed.  

Lemma typing_schemes_add_subst_kinds_bind :
  forall v E D1 D2 P Xs L M Ms ts,
    scheme_aux L M ->
    fresh (dom E \u L) (sch_arity M) Xs ->
    typing_schemes v E (D1 & D2) P ts Ms ->
    type_environment E ->
    typing_schemes v (E & Xs ~: M) (D1 & D2) P ts Ms.
Proof.
  introv Hs Hf Hss He.
  apply typing_schemes_tenv_weakening_l;
    eauto using type_environment_push_ranges.
Qed.

Lemma type_environment_add_subst_typ_bind : forall D1 D2 xs Ms x M,
    environment (D1 & xs ~* Ms & D2) ->
    length xs = length Ms ->
    x \notin (dom D1 \u from_list xs \u dom D2) ->
    scheme M ->
    environment (D1 & xs ~* Ms & D2 & x ~ M).
Proof.
  introv He Hl Hn Hs.
  apply environment_push; autorewrite with rew_env_dom; auto.
Qed.

Lemma environment_add_subst_typ_bind :
    forall D1 D2 xs Ms x M,
    environment (D1 & xs ~* Ms & D2) ->
    length xs = length Ms ->
    x \notin (dom D1 \u from_list xs \u dom D2) ->
    scheme M ->
    environment (D1 & xs ~* Ms & D2 & x ~ M).
Proof.
  introv He Hl Hn Hk.
  apply environment_push; autorewrite with rew_env_dom; auto.
Qed.

Lemma environment_add_subst_typ_bind_empty :
    forall D1 D2 xs Ms x T,
    environment (D1 & xs ~* Ms & D2) ->
    length xs = length Ms ->
    x \notin (dom D1 \u from_list xs \u dom D2) ->
    type T ->
    environment (D1 & xs ~* Ms & D2 & x ~ sch_empty T).
Proof.
  introv He Hl Hn Hk.
  apply environment_push; autorewrite with rew_env_dom; auto.
Qed.

Lemma environment_add_subst_typ_bind_empty2 :
    forall D1 D2 xs Ms x T1 y T2,
    environment (D1 & xs ~* Ms & D2) ->
    length xs = length Ms ->
    x \notin (dom D1 \u from_list xs \u dom D2) ->
    y \notin (dom D1 \u from_list xs \u dom D2 \u \{x}) ->
    type T1 ->
    type T2 ->
    environment (D1 & xs ~* Ms & D2
                 & x ~ sch_empty T1 & y ~ sch_empty T2).
Proof.
  introv He Hl Hn1 Hn2 Hk1 Hk2.
  apply environment_push; autorewrite with rew_env_dom; auto.
  apply environment_push; autorewrite with rew_env_dom; auto.
Qed.

(* ****************************************************** *)
(** ** Term substitution *)

Lemma value_trm_subst : forall xs ss t,
    value t ->
    terms ss ->
    value (trm_subst xs ss t).
Proof.
  introv Hv Ht.
  induction Hv; simpl; auto.
  - apply value_abs.
    replace (trm_abs (trm_subst xs ss t))
      with (trm_subst xs ss (trm_abs t))
      by auto.
    auto using trm_subst_term.
  - apply value_fix.
    replace (trm_fix (trm_subst xs ss t))
      with (trm_subst xs ss (trm_fix t))
      by auto.
    auto using trm_subst_term.
Qed.

Lemma typing_trm_subst_var : forall v E D1 D2 P xs Ms ts x M,
    binds x M (D1 & xs ~* Ms & D2) ->
    length xs = length Ms ->
    environment (D1 & xs ~* Ms & D2) ->
    typing_schemes v E (D1 & D2) P ts Ms ->
    typing_scheme v E (D1 & D2) P (trm_var_subst xs ts x) M
    \/ (binds x M (D1 & D2)
        /\ trm_var_subst xs ts x = trm_fvar x).
Proof.
  introv Hb Hl He Hss.
  assert (length ts = length Ms) as Hl2
    by eauto using typing_schemes_length.
  generalize dependent Ms.
  generalize dependent ts.
  induction xs; introv Hb Hl1 He Hss Hl2; destruct Ms; destruct ts;
    try discriminate; simpl in *;
    autorewrite with rew_env_concat in *; auto.
  inversion Hss; subst.
  case_var.
  - apply binds_middle_eq_inv in Hb; subst;
      auto using ok_from_environment.
  - eauto using binds_subst, environment_remove.
Qed.

Lemma typing_trm_subst : forall v E D1 D2 P xs Ms ts t T,
    typing v E (D1 & xs ~* Ms & D2) P t T ->
    length xs = length Ms ->
    type_environment E ->
    environment (D1 & xs ~* Ms & D2) ->
    store_type P ->
    typing_schemes v E (D1 & D2) P ts Ms ->
    typing v E (D1 & D2) P (trm_subst xs ts t) T.
Proof.
  introv Ht Hl He Hd Hp Hss.
  assert (type_environment_extension E empty) as He2 by auto.
  remember (D1 & xs ~* Ms & D2) as D12.
  generalize dependent D2.
  induction Ht; introv Heq Hss; subst; simpl; eauto.
  - destruct typing_trm_subst_var
      with (v := v) (E := E) (D1 := D1) (D2 := D2) (P := P)
           (xs := xs) (Ms := Ms)
           (ts := ts) (x := x) (M := M) as [Hs | [Hb Heq]]; auto.
    + auto using typing_instance.
    + rewrite Heq.
      apply typing_var with (M := M) (Us := Us); auto.
  - apply typing_abs with (L := L \u from_list xs \u dom D1 \u dom D2);
      auto.
    intros x Hf.
    rewrite trm_subst_open_var; auto with wellformed.
    rewrite <- concat_assoc.
    eauto using concat_assoc, typing_schemes_add_subst_typ_bind_empty,
      environment_remove, environment_add_subst_typ_bind_empty
        with wellformed.
  - apply typing_let_val
      with (L := L \u from_list xs \u dom E \u dom D1 \u dom D2)
        (M := M);
      eauto using value_trm_subst, valid_scheme_aux_subset,
        subset_union_weak_l with wellformed.
    + introv Hf.
      assert (scheme_aux L M) by auto with wellformed.
      eauto using type_environment_push_ranges,
        typing_schemes_add_subst_kinds_bind with wellformed.
    + introv Hn.
      rewrite trm_subst_open_var; auto with wellformed.
      rewrite <- concat_assoc.
      eauto using concat_assoc, typing_schemes_add_subst_typ_bind,
        environment_remove, environment_add_subst_typ_bind
          with wellformed.
  - apply typing_let
      with (L := L \u from_list xs \u dom D1 \u dom D2) (T1 := T1);
      auto.
    introv Hn.
    rewrite trm_subst_open_var; auto with wellformed.
    rewrite <- concat_assoc.
    eauto using concat_assoc, typing_schemes_add_subst_typ_bind_empty,
      environment_remove, environment_add_subst_typ_bind_empty
        with wellformed.
  - apply typing_match
      with (L := L \u from_list xs \u dom D1 \u dom D2)
           (T1 := T1) (T2 := T2) (T3 := T3); auto.
    + introv Hn.
      rewrite trm_subst_open_var; auto with wellformed.
      rewrite <- concat_assoc.
      assert
        (type (typ_proj CSet.universe (CSet.singleton c) T2))
          as Hty by auto with wellformed.
      inversion Hty; subst.
      assert (type (typ_variant T2)) by auto.
      eauto using concat_assoc, typing_schemes_add_subst_typ_bind_empty,
        environment_remove, environment_add_subst_typ_bind_empty
          with wellformed.
    + introv Hn.
      rewrite trm_subst_open_var; auto with wellformed.
      rewrite <- concat_assoc.
      assert
        (type (typ_proj CSet.universe (CSet.cosingleton c) T3))
          as Hty by auto with wellformed.
      inversion Hty; subst.
      assert (type (typ_variant T3)) by auto.
      eauto using concat_assoc, typing_schemes_add_subst_typ_bind_empty,
        environment_remove, environment_add_subst_typ_bind_empty
          with wellformed.
  - apply typing_destruct
      with (L := L \u from_list xs \u dom D1 \u dom D2)
           (T1 := T1) (T2 := T2); auto.
    introv Hn.
    rewrite trm_subst_open_var; auto with wellformed.
    rewrite <- concat_assoc.
      assert (type (typ_constructor c T2))
          as Hty by auto with wellformed.
    inversion Hty; subst.
    eauto using concat_assoc, typing_schemes_add_subst_typ_bind_empty,
      environment_remove, environment_add_subst_typ_bind_empty
        with wellformed.
  - apply typing_fix
      with (L := L \u from_list xs \u dom D1 \u dom D2); auto.
    introv Hn1 Hn2.
    rewrite trm_subst_open_vars; auto with wellformed.
    rewrite <- concat_assoc2.
    assert (type (typ_arrow T1 T2)) by auto with wellformed.
    eauto using concat_assoc2, typing_schemes_add_subst_typ_bind_empty2,
      environment_remove, environment_add_subst_typ_bind_empty2
        with wellformed.
Qed.

Lemma typing_trm_subst_l : forall v E D xs Ms P ts t T,
    typing v E (D & xs ~* Ms) P t T ->
    length xs = length Ms ->
    type_environment E ->
    environment (D & xs ~* Ms) ->
    store_type P ->
    typing_schemes v E D P ts Ms ->
    typing v E D P (trm_subst xs ts t) T.
Proof.
  introv Ht Hl He Hd Hp Hts.
  rewrite <- concat_empty_r with (E := D).
  rewrite <- concat_empty_r with (E := D & xs ~* Ms) in Ht, Hd.
  rewrite <- concat_empty_r with (E := D) in Hts.
  eauto using typing_trm_subst.
Qed.

Lemma typing_trm_subst_single : forall v E D1 D2 x M P s t T,
    typing v E (D1 & x ~ M & D2) P t T ->
    type_environment E ->
    environment (D1 & x ~ M & D2) ->
    store_type P ->
    typing_scheme v E (D1 & D2) P s M ->
    typing v E (D1 & D2) P (trm_subst_single x s t) T.
Proof.
  introv Ht He Hd Hp Hs.
  apply typing_trm_subst with (Ms := cons M nil);
    simpl; autorewrite with rew_env_concat; auto.
Qed.

Lemma typing_trm_subst_single_l : forall v E D x M P s t T,
    typing v E (D & x ~ M) P t T ->
    type_environment E ->
    environment (D & x ~ M) ->
    store_type P ->
    typing_scheme v E D P s M ->
    typing v E D P (trm_subst_single x s t) T.
Proof.
  introv Ht He Hd Hp Hts.
  rewrite <- concat_empty_r with (E := D).
  rewrite <- concat_empty_r with (E := D & x ~ M) in Ht, Hd.
  rewrite <- concat_empty_r with (E := D) in Hts.
  eauto using typing_trm_subst_single.
Qed.
