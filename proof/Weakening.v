(************************************************
 *          Row Subtyping - Weakening           *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import LibLN Utilities Cofinite Disjoint Definitions
        Opening FreeVars Environments Subst Wellformedness.

(* *************************************************************** *)
(** Weakening kinding *)

Lemma kinding_weakening : forall E1 E2 E3 E4 T K,
   kinding (E1 & E3) E4 T K -> 
   type_environment (E1 & E2 & E3) ->
   type_environment_extension (E1 & E2 & E3) E4 ->
   kinding (E1 & E2 & E3) E4 T K.
Proof.
  introv Hk He1 He2.
  remember (E1 & E3) as E13.
  generalize dependent E3.
  induction Hk; introv Heq He1 He2; subst;
    eauto using binds_tenv_weakening,
      type_environment_concat_inv_l;
    constructor;
    match goal with
    | IH : forall E5 : LibEnv.env rng,
        E1 & E4 & ?E6 = E1 & E5 ->
        type_environment (E1 & E2 & E5) ->
        type_environment_extension 
          (E1 & E2 & E5) empty ->
        kinding (E1 & E2 & E5) empty ?T ?K
      |- kinding (E1 & E2 & E4 & ?E6) empty ?T ?K =>
        rewrite <- concat_assoc;
        apply IH; autorewrite with rew_env_concat;
          auto using type_environment_extend
    | _ => auto
    end.
Qed.

Lemma kinding_weakening_l : forall E1 E2 E3 T K,
   kinding E1 E3 T K -> 
   type_environment (E1 & E2) ->
   type_environment_extension (E1 & E2) E3 ->
   kinding (E1 & E2) E3 T K.
Proof.
  introv Hv He1 He2.
  rewrite <- concat_empty_r with (E := E1 & E2).
  apply kinding_weakening; rewrite? concat_empty_r;
    assumption.
Qed.

Lemma kindings_weakening : forall E1 E2 E3 E4 Ts Ks,
   kindings (E1 & E3) E4 Ts Ks -> 
   type_environment (E1 & E2 & E3) ->
   type_environment_extension (E1 & E2 & E3) E4 ->
   kindings (E1 & E2 & E3) E4 Ts Ks.
Proof.
  introv Hks He1 He2.
  remember (E1 & E3) as E13.
  induction Hks; subst; auto using kinding_weakening.  
Qed.

Lemma kindings_weakening_l : forall E1 E2 E3 Ts Ks,
   kindings E1 E3 Ts Ks -> 
   type_environment (E1 & E2) ->
   type_environment_extension (E1 & E2) E3 ->
   kindings (E1 & E2) E3 Ts Ks.
Proof.
  introv Hks He1 He2.
  rewrite <- concat_empty_r with (E := E1 & E2).
  apply kindings_weakening; rewrite concat_empty_r; assumption.
Qed.

(* *************************************************************** *)
(** Using weakening lemmas for other weakening proofs *)

Lemma kinding_weakening_3 : forall E1 E2 E3 E4 T K,
    kinding (E1 & E3 & E4) empty T K ->
    type_environment (E1 & E2 & E3) ->
    type_environment_extension (E1 & E2 & E3) E4 ->
    kinding (E1 & E2 & E3 & E4) empty T K.
Proof.
  introv Hk He1 He2.
  rewrite <- concat_assoc.
  apply kinding_weakening;
    rewrite concat_assoc;
    auto using type_environment_extend.
Qed.

Lemma kinding_weakening_assoc : forall E1 E2 E3 E4 T K,
    kinding (E1 & (E2 & E4)) empty T K ->
    type_environment E1 ->
    type_environment_extension E1 (E2 & E3 & E4) ->
    kinding (E1 & (E2 & E3 & E4)) empty T K.
Proof.
  introv Hk He1 He2.
  autorewrite with rew_env_concat in *.
  apply kinding_weakening; auto.
  rewrite <- concat_assoc.
  rewrite <- concat_assoc.
  apply type_environment_extend;
    autorewrite with rew_env_concat in *; auto.
Qed.

(* *************************************************************** *)
(** Weakening recursive environment of kinding *)

Lemma kinding_weakening_rec : forall E1 E2 E3 E4 T K,
   kinding E1 (E2 & E4) T K -> 
   type_environment E1 ->
   type_environment_extension E1 (E2 & E3 & E4) ->
   kinding E1 (E2 & E3 & E4) T K.
Proof.
  introv Hk He1 He2.
  remember (E2 & E4) as E24.
  induction Hk; subst;
    eauto using binds_tenv_weakening, kinding_weakening_assoc.
Qed.

Lemma kinding_weakening_rec_l : forall E1 E2 E3 T K,
   kinding E1 E2 T K -> 
   type_environment E1 ->
   type_environment_extension E1 (E2 & E3) ->
   kinding E1 (E2 & E3) T K.
Proof.
  introv Hv He1 He2.
  rewrite <- concat_empty_r with (E := E2 & E3).
  apply kinding_weakening_rec;
    rewrite? concat_empty_r; assumption.
Qed.

Lemma kinding_weakening_rec_empty : forall E1 E2 T K,
   kinding E1 empty T K -> 
   type_environment E1 ->
   type_environment_extension E1 E2 ->
   kinding E1 E2 T K.
Proof.
  introv Hr He1 He2.
  rewrite <- concat_empty_l with (E := E2).
  rewrite <- concat_empty_r with (E := empty & E2).
  apply kinding_weakening_rec;
    autorewrite with rew_env_concat; auto.
Qed.

Lemma kindings_weakening_rec : forall E1 E2 E3 E4 Ts Ks,
   kindings E1 (E2 & E4) Ts Ks -> 
   type_environment E1 ->
   type_environment_extension E1 (E2 & E3 & E4) ->
   kindings E1 (E2 & E3 & E4) Ts Ks.
Proof.
  introv Hks He1 He2.
  remember (E2 & E4) as E24.
  induction Hks; subst; auto using kinding_weakening_rec.  
Qed.

Lemma kindings_weakening_rec_l : forall E1 E2 E3 Ts Ks,
   kindings E1 E2 Ts Ks -> 
   type_environment E1 ->
   type_environment_extension E1 (E2 & E3) ->
   kindings E1 (E2 & E3) Ts Ks.
Proof.
  introv Hks He1 He2.
  rewrite <- concat_empty_r with (E := E2 & E3).
  apply kindings_weakening_rec; rewrite? concat_empty_r; assumption.
Qed.

(* *************************************************************** *)
(** Extending environment with recursive environment *)

Lemma kinding_extend : forall E1 E2 E3 T K,
   kinding E1 (E2 & E3) T K -> 
   type_environment_extension E1 E2 ->
   kinding (E1 & E2) E3 T K.
Proof.
  introv Hk He.
  remember (E2 & E3) as E23.
  generalize dependent E2.
  generalize dependent E3.
  induction Hk; introv Heq He; subst; eauto using binds_tenv_extend;
    constructor; autorewrite with rew_env_concat in *; auto.
Qed.

Lemma kinding_extend_empty : forall E1 E2 T K,
   kinding E1 E2 T K -> 
   type_environment_extension E1 E2 ->
   kinding (E1 & E2) empty T K.
Proof.
  introv Hk He.
  apply kinding_extend;
    autorewrite with rew_env_concat; auto.
Qed.

Lemma kindings_extend : forall E1 E2 E3 Ts Ks,
   kindings E1 (E2 & E3) Ts Ks -> 
   type_environment_extension E1 E2 ->
   kindings (E1 & E2) E3 Ts Ks.
Proof.
  introv Hks He.
  remember (E2 & E3) as E23.
  induction Hks; subst; auto using kinding_extend.
Qed.

(* *************************************************************** *)
(** Weakening type equality *)

Lemma type_equal_weakening : forall v E1 E2 E3 E4 T1 T2 K,
   type_equal v (E1 & E3) E4 T1 T2 K -> 
   type_environment (E1 & E2 & E3) ->
   type_environment_extension (E1 & E2 & E3) E4 ->
   type_equal v (E1 & E2 & E3) E4 T1 T2 K.
Proof.
  introv Hte He1 He2.
  remember (E1 & E3) as E13.
  generalize dependent E3.
  induction Hte; intros E4 Heq He1 He2; subst;
    eauto using kinding_weakening, binds_tenv_weakening;
    constructor;
    match goal with
    | IH : forall E5 : LibEnv.env rng,
        E1 & E4 & ?E = E1 & E5 ->
        type_environment (E1 & E2 & E5) ->
        type_environment_extension 
          (E1 & E2 & E5) empty ->
        type_equal v (E1 & E2 & E5) empty ?Tl ?Tr ?Kt
      |- type_equal v (E1 & E2 & E4 & ?E) empty ?Tl ?Tr _ =>
      rewrite <- concat_assoc;
        apply IH; rewrite concat_assoc;
          auto using type_environment_extend
    | _ => auto
    end.
Qed.

Lemma type_equal_weakening_l : forall v E1 E2 E3 T1 T2 K,
   type_equal v E1 E3 T1 T2 K -> 
   type_environment (E1 & E2) ->
   type_environment_extension (E1 & E2) E3 ->
   type_equal v (E1 & E2) E3 T1 T2 K.
Proof.
  introv Hv He1 He2.
  rewrite <- concat_empty_r with (E := E1 & E2).
  apply type_equal_weakening;
    rewrite concat_empty_r; assumption.
Qed.

Lemma subtype_weakening : forall v E1 E2 E3 E4 T1 T2 K,
   subtype v (E1 & E3) E4 T1 T2 K -> 
   type_environment (E1 & E2 & E3) ->
   type_environment_extension (E1 & E2 & E3) E4 ->
   subtype v (E1 & E2 & E3) E4 T1 T2 K.
Proof.
  intros.
  apply type_equal_weakening; auto.
Qed.

Lemma subtype_weakening_l : forall v E1 E2 E3 T1 T2 K,
   subtype v E1 E3 T1 T2 K -> 
   type_environment (E1 & E2) ->
   type_environment_extension (E1 & E2) E3 ->
   subtype v (E1 & E2) E3 T1 T2 K.
Proof.
  intros.
  apply type_equal_weakening_l; auto.
Qed.

(* *************************************************************** *)
(** Weakening recursive environment of type equaliy *)

Lemma type_equal_weakening_assoc : forall v E1 E2 E3 E4 T1 T2 K,
    type_equal v (E1 & (E2 & E4)) empty T1 T2 K ->
    type_environment E1 ->
    type_environment_extension E1 (E2 & E3 & E4) ->
    type_equal v (E1 & (E2 & E3 & E4)) empty T1 T2 K.
Proof.
  introv Hte He1 He2.
  autorewrite with rew_env_concat in *.
  apply type_equal_weakening; auto.
  rewrite <- concat_assoc.
  rewrite <- concat_assoc.
  apply type_environment_extend;
    autorewrite with rew_env_concat in *; auto.
Qed.

Lemma type_equal_weakening_rec : forall v E1 E2 E3 E4 T1 T2 K,
   type_equal v E1 (E2 & E4) T1 T2 K -> 
   type_environment E1 ->
   type_environment_extension E1 (E2 & E3 & E4) ->
   type_equal v E1 (E2 & E3 & E4) T1 T2 K.
Proof.
  introv Hte He1 He2.
  remember (E2 & E4) as E24.
  induction Hte; subst;
    auto using kinding_weakening_rec, type_equal_weakening_assoc;
    eauto.
Qed.

Lemma type_equal_weakening_rec_l : forall v E1 E2 E3 T1 T2 K,
   type_equal v E1 E2 T1 T2 K -> 
   type_environment E1 ->
   type_environment_extension E1 (E2 & E3) ->
   type_equal v E1 (E2 & E3) T1 T2 K.
Proof.
  introv Hte He1 He2.
  rewrite <- concat_empty_r with (E := E2 & E3).
  apply type_equal_weakening_rec;
    rewrite? concat_empty_r; auto.
Qed.

Lemma subtype_weakening_rec : forall v E1 E2 E3 E4 T1 T2 K,
   subtype v E1 (E2 & E4) T1 T2 K -> 
   type_environment E1 ->
   type_environment_extension E1 (E2 & E3 & E4) ->
   subtype v E1 (E2 & E3 & E4) T1 T2 K.
Proof.
  intros.
  apply type_equal_weakening_rec; auto.
Qed.

Lemma subtype_weakening_assoc : forall v E1 E2 E3 E4 T1 T2 K,
    subtype v (E1 & (E2 & E4)) empty T1 T2 K ->
    type_environment E1 ->
    type_environment_extension E1 (E2 & E3 & E4) ->
    subtype v (E1 & (E2 & E3 & E4)) empty T1 T2 K.
Proof.
  introv Hte He1 He2.
  unfold subtype in *.
  auto using type_equal_weakening_assoc.
Qed.

(* *************************************************************** *)
(** Extending environment with recursive environment *)

Lemma type_equal_extend : forall v E1 E2 E3 T1 T2 K,
   type_equal v E1 (E2 & E3) T1 T2 K -> 
   type_environment_extension E1 E2 ->
   type_equal v (E1 & E2) E3 T1 T2 K.
Proof.
  introv Hte He.
  remember (E2 & E3) as E23.
  induction Hte; subst;
    auto using type_environment_extend, kinding_extend;
    try solve [ constructor;
                autorewrite with rew_env_concat in *;
                auto ].
  - apply type_equal_range_lower with (T1 := T1) (T2 := T2).
    apply binds_tenv_extend; auto.
  - apply type_equal_range_upper with (T1 := T1) (T2 := T2).
    apply binds_tenv_extend; auto.
  - eauto.    
Qed.

Lemma type_equal_extend_empty : forall v E1 E2 T1 T2 K,
   type_equal v E1 E2 T1 T2 K -> 
   type_environment_extension E1 E2 ->
   type_equal v (E1 & E2) empty T1 T2 K.
Proof.
  introv Hte He.
  apply type_equal_extend;
    autorewrite with rew_env_concat; auto.
Qed.

Lemma subtype_extend : forall v E1 E2 E3 T1 T2 K,
   subtype v E1 (E2 & E3) T1 T2 K -> 
   type_environment_extension E1 E2 ->
   subtype v (E1 & E2) E3 T1 T2 K.
Proof.
  introv Hs He.
  apply type_equal_extend; auto.
Qed.

(* *************************************************************** *)
(** Weakening ranging *)

Lemma ranging_weakening : forall v E1 E2 E3 E4 T R,
   ranging v (E1 & E3) E4 T R -> 
   type_environment (E1 & E2 & E3) ->
   type_environment_extension (E1 & E2 & E3) E4 ->
   ranging v (E1 & E2 & E3) E4 T R.
Proof.
  introv Hr He1 He2.
  remember (E1 & E3) as E13.
  destruct Hr; subst;
    auto using kinding_weakening, subtype_weakening.
Qed.

Lemma ranging_weakening_l : forall v E1 E2 E3 T R,
   ranging v E1 E3 T R -> 
   type_environment (E1 & E2) ->
   type_environment_extension (E1 & E2) E3 ->
   ranging v (E1 & E2) E3 T R.
Proof.
  introv Hv He1 He2.
  rewrite <- concat_empty_r with (E := E1 & E2).
  apply ranging_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma ranging_weakening_rec : forall v E1 E2 E3 E4 T R,
   ranging v E1 (E2 & E4) T R -> 
   type_environment E1 ->
   type_environment_extension E1 (E2 & E3 & E4) ->
   ranging v E1 (E2 & E3 & E4) T R.
Proof.
  introv Hr He1 He2.
  remember (E2 & E4) as E24.
  destruct Hr; subst;
    auto using kinding_weakening_rec, subtype_weakening_rec.
Qed.

Lemma ranging_extend : forall v E1 E2 E3 T R,
   ranging v E1 (E2 & E3) T R -> 
   type_environment_extension E1 E2 ->
   ranging v (E1 & E2) E3 T R.
Proof.
  introv Hr He.
  remember (E2 & E3) as E23.
  destruct Hr; subst; auto using kinding_extend, subtype_extend.
Qed.

Lemma rangings_weakening : forall v E1 E2 E3 E4 Ts Rs,
   rangings v (E1 & E3) E4 Ts Rs -> 
   type_environment (E1 & E2 & E3) ->
   type_environment_extension (E1 & E2 & E3) E4 ->
   rangings v (E1 & E2 & E3) E4 Ts Rs.
Proof.
  introv Hr He1 He2.
  remember (E1 & E3) as E13.
  induction Hr; subst; eauto using ranging_weakening.
Qed.

Lemma rangings_weakening_l : forall v E1 E2 E3 Ts Rs,
   rangings v E1 E3 Ts Rs -> 
   type_environment (E1 & E2) ->
   type_environment_extension (E1 & E2) E3 ->
   rangings v (E1 & E2) E3 Ts Rs.
Proof.
  introv Hks He1 He2.
  induction Hks; subst; auto using ranging_weakening_l.
Qed.

Lemma rangings_extend : forall v E1 E2 E3 Ts Rs,
   rangings v E1 (E2 & E3) Ts Rs -> 
   type_environment_extension E1 E2 ->
   rangings v (E1 & E2) E3 Ts Rs.
Proof.
  introv Hrs He.
  remember (E2 & E3) as E23.
  induction Hrs; subst; auto using ranging_extend.
Qed.

Lemma rangings_weakening_rec : forall v E1 E2 E3 E4 Ts Rs,
   rangings v E1 (E2 & E4) Ts Rs -> 
   type_environment E1 ->
   type_environment_extension E1 (E2 & E3 & E4) ->
   rangings v E1 (E2 & E3 & E4) Ts Rs.
Proof.
  introv Hr He1 He2.
  remember (E2 & E4) as E24.
  induction Hr; subst; eauto using ranging_weakening_rec.
Qed.

Lemma rangings_weakening_rec_empty : forall v E1 E2 Ts Rs,
   rangings v E1 empty Ts Rs -> 
   type_environment E1 ->
   type_environment_extension E1 E2 ->
   rangings v E1 E2 Ts Rs.
Proof.
  introv Hr He1 He2.
  rewrite <- concat_empty_l with (E := E2).
  rewrite <- concat_empty_r with (E := empty & E2).
  apply rangings_weakening_rec;
    autorewrite with rew_env_concat; auto.
Qed.

(* *************************************************************** *)
(** Weakening valid type environment extensions *)

Lemma valid_range_weakening : forall v E1 E2 E3 E4 R,
   valid_range v (E1 & E3) E4 R -> 
   type_environment (E1 & E2 & E3) ->
   type_environment_extension (E1 & E2 & E3) E4 ->
   valid_range v (E1 & E2 & E3) E4 R.
Proof.
  introv Hr He1 He2.
  remember (E1 & E3) as E13.
  destruct Hr; subst;
    auto using kinding_weakening, subtype_weakening.
Qed.

Lemma valid_range_weakening_rec : forall v E1 E2 E3 E4 R,
   valid_range v E1 (E2 & E4) R -> 
   type_environment E1 ->
   type_environment_extension E1 (E2 & E3 & E4) ->
   valid_range v E1 (E2 & E3 & E4) R.
Proof.
  introv Hr He1 He2.
  remember (E2 & E4) as E24.
  destruct Hr; subst;
    auto using kinding_weakening_rec, subtype_weakening_rec.
Qed.

Lemma valid_range_extend : forall v E1 E2 E3 R,
   valid_range v E1 (E2 & E3) R -> 
   type_environment_extension E1 E2 ->
   valid_range v (E1 & E2) E3 R.
Proof.
  introv Hr He.
  remember (E2 & E3) as E23.
  destruct Hr; subst; auto using kinding_extend, subtype_extend.
Qed.

Lemma valid_tenv_rec_weakening : forall v E1 E2 E3 E4 E5,
   valid_tenv_rec v (E1 & E3) E4 E5 -> 
   type_environment (E1 & E2 & E3) ->
   type_environment_extension (E1 & E2 & E3) E4 ->
   type_environment_extension (E1 & E2 & E3 & E4) E5 ->
   valid_tenv_rec v (E1 & E2 & E3) E4 E5.
Proof.
  introv Hv He1 He2 He3.
  remember (E1 & E3) as E13.
  induction Hv; subst; auto.
  destruct (type_environment_push_inv He2)
    as [He4 [Hn1 [Hn2 Hr]]].
  autorewrite with rew_env_concat in He3.
  apply type_environment_extension_strengthen_l in He3.
  apply valid_tenv_rec_push;
    auto using type_environment_extension_rev_push.
  rewrite <- concat_assoc.
  apply valid_range_weakening; rewrite concat_assoc;
    auto using type_environment_extend,
      type_environment_extension_rev_push.
Qed.

Lemma valid_tenv_rec_weakening_rec : forall v E1 E2 E3 E4 E5,
  valid_tenv_rec v E1 E2 (E3 & E5)->
  type_environment E1 ->
  type_environment_extension E1 E2 ->
  type_environment_extension (E1 & E2) (E3 & E4 & E5) ->
  valid_tenv_rec v E1 E2 (E3 & E4 & E5).
Proof.
  introv Hte He1 He2 He3.
  remember (E3 & E5) as E35.
  generalize dependent E3.
  induction Hte; introv Heq He3; subst; auto.
  destruct (type_environment_extend_middle_inv He2 He3)
    as [He4 [He5 [Hr [Hn1 [Hn2 Hn3]]]]].
  assert (type_environment_extension
            (E1 & E2) (X ~ R & E0 & E4 & E5))
    by (rewrite <- concat_assoc2;
        auto using type_environment_extension_rev_push).
  autorewrite with rew_env_concat in *.
  apply valid_tenv_rec_push; rewrite? concat_assoc2; auto.
  apply valid_range_weakening_rec;
    auto using type_environment_extend.
Qed.

Lemma valid_tenv_rec_weakening_rec_r : forall v E1 E2 E3 E4,
  valid_tenv_rec v E1 E2 E4->
  type_environment E1 ->
  type_environment_extension E1 E2 ->
  type_environment_extension (E1 & E2) (E3 & E4) ->
  valid_tenv_rec v E1 E2 (E3 & E4).
Proof.
  introv Hte He1 He2 He3.
  rewrite <- concat_empty_l with (E := E3).
  apply valid_tenv_rec_weakening_rec;
    rewrite? concat_empty_l; auto.
Qed.

Lemma valid_tenv_extension_weakening : forall v E1 E2 E3 E4,
   valid_tenv_extension v (E1 & E3) E4 -> 
   type_environment (E1 & E2 & E3) ->
   type_environment_extension (E1 & E2 & E3) E4 ->
   valid_tenv_extension v (E1 & E2 & E3) E4.
Proof.
  introv Hv He1 He2.
  auto using valid_tenv_rec_weakening.
Qed.

Lemma  valid_tenv_extension_and_type_weakening :
  forall v E1 E2 E3 E4 T,
    valid_tenv_extension_and_type v (E1 & E3) E4 T ->
    type_environment (E1 & E2 & E3) ->
    type_environment_extension (E1 & E2 & E3) E4 ->
    valid_tenv_extension_and_type v (E1 & E2 & E3) E4 T.
Proof.
  introv Hv He1 He2.
  remember (E1 & E3) as E13.
  destruct Hv; subst.
  apply valid_tenv_extension_and_type_c;
    auto using valid_tenv_extension_weakening.
  rewrite <- concat_assoc.
  apply kinding_weakening; rewrite concat_assoc;
    auto using type_environment_extend.
Qed.

(* *************************************************************** *)
(** Weakening valid schemes *)

Lemma valid_scheme_aux_subset : forall v E L1 L2 M,
   valid_scheme_aux v L1 E M -> 
   subset L1 L2 ->
   valid_scheme_aux v L2 E M.
Proof.
  introv Hv Hs.
  apply valid_scheme_aux_c.
  introv Hf.
  destruct Hv as [? ? ? ? Hv].
  eauto using fresh_subset.
Qed.

Lemma valid_scheme_aux_weakening : forall v E1 E2 E3 L M,
   valid_scheme_aux v L (E1 & E3) M -> 
   type_environment (E1 & E2 & E3) ->
   valid_scheme_aux v (dom (E1 & E2 & E3) \u L) (E1 & E2 & E3) M.
Proof.
  introv Hs He.
  apply valid_scheme_aux_subset
    with (L2 := dom (E1 & E2 & E3) \u L) in Hs;
      auto using subset_union_weak_r.
  remember (E1 & E3) as E13.
  remember (dom (E1 & E2 & E3) \u L) as Ld.
  assert (scheme_aux Ld M) by auto with wellformed.
  destruct Hs; subst.
  apply valid_scheme_aux_c.
  introv Hf.
  apply valid_tenv_extension_and_type_weakening; auto.  
  apply type_environment_extension_ranges
    with (dom (E1 & E2 & E3) \u L); auto.
Qed.

Lemma valid_scheme_weakening : forall v E1 E2 E3 M,
   valid_scheme v (E1 & E3) M -> 
   type_environment (E1 & E2 & E3) ->
   valid_scheme v (E1 & E2 & E3) M.
Proof.
  introv Hs He.
  remember (E1 & E3) as E13.
  destruct Hs as [? ? ? ? Hs]; subst.
  eauto using valid_scheme_aux_weakening.
Qed.

Lemma valid_schemes_weakening : forall v E1 E2 E3 Ms,
   valid_schemes v (E1 & E3) Ms -> 
   type_environment (E1 & E2 & E3) ->
   valid_schemes v (E1 & E2 & E3) Ms.
Proof.
  introv Hss He.
  remember (E1 & E3) as E13.
  induction Hss; subst; auto using valid_scheme_weakening.
Qed.

(* *************************************************************** *)
(** Weakening valid instances *)

Lemma valid_instance_weakening : forall v E1 E2 E3 Ts M,
   valid_instance v (E1 & E3) Ts M -> 
   type_environment (E1 & E2 & E3) ->
   valid_instance v (E1 & E2 & E3) Ts M.
Proof.
  introv Hv He.
  remember (E1 & E3) as E13.
  induction Hv; subst; eauto using rangings_weakening.
Qed.

Lemma valid_instance_weakening_l : forall v E1 E2 Ts M,
   valid_instance v E1 Ts M -> 
   type_environment (E1 & E2) ->
   valid_instance v (E1 & E2) Ts M.
Proof.
  introv He1 He2.
  rewrite <- concat_empty_r with (E := E1 & E2).
  apply valid_instance_weakening;
    rewrite concat_empty_r; assumption.
Qed.

(* ****************************************************** *)
(** ** Weakening typing type environment *)

Lemma typing_tenv_weakening : forall v E1 E2 E3 D P t T,
    typing v (E1 & E3) D P t T ->
    type_environment (E1 & E2 & E3) ->
    typing v (E1 & E2 & E3) D P t T.
Proof.
  introv Ht He.
  remember (E1 & E3) as E13.
  generalize dependent E3.
  induction Ht; introv Heq He; subst;
    eauto using binds_env_weakening,
      kinding_weakening, subtype_weakening, type_equal_weakening,
      ranging_weakening, valid_instance_weakening.
  - apply typing_let_val
      with (M := M) (L := dom (E1 & E2 & E3) \u L);
      eauto using valid_scheme_aux_weakening.
    intros Xs Hf.
    assert (type_environment (E1 & E2 & E3 & Xs ~: M)) as He2
      by (apply type_environment_push_ranges with L;
           auto with wellformed).
    rewrite <- concat_assoc.
    rewrite <- concat_assoc in He2.
    auto using concat_assoc.
  - eapply typing_match with (T1 := T1) (T2 := T2) (T3 := T3);
      eauto using binds_env_weakening,
        kinding_weakening, subtype_weakening, type_equal_weakening,
        ranging_weakening, valid_instance_weakening.
  - eapply typing_destruct with (T1 := T1) (T2 := T2) (T3 := T3);
      eauto using binds_env_weakening,
        kinding_weakening, subtype_weakening, type_equal_weakening,
        ranging_weakening, valid_instance_weakening.
Qed.    

Lemma typing_tenv_weakening_l : forall v E1 E2 D P t T,
    typing v E1 D P t T ->
    type_environment (E1 & E2) ->
    typing v (E1 & E2) D P t T.
Proof.
  introv Ht He.
  rewrite <- concat_empty_r with (E := E1 & E2).
  apply typing_tenv_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma valid_tenv_extension_and_typing_tenv_weakening :
  forall v E1 E2 E3 E4 D P t T,
    valid_tenv_extension_and_typing v
      (E1 & E3) E4 D P t T ->
    type_environment (E1 & E2 & E3) ->
    type_environment_extension (E1 & E2 & E3) E4 ->
    valid_tenv_extension_and_typing v
      (E1 & E2 & E3) E4 D P t T.
Proof.
  introv Hv He1 He2.
  remember (E1 & E3) as E13.
  destruct Hv; subst.
  constructor; auto using valid_tenv_extension_weakening.
  rewrite <- concat_assoc.
  apply typing_tenv_weakening;
    rewrite concat_assoc; auto using type_environment_extend.
Qed.

Lemma typing_scheme_tenv_weakening : forall v E1 E2 E3 D P t M,
    typing_scheme v (E1 & E3) D P t M ->
    type_environment (E1 & E2 & E3) ->
    typing_scheme v (E1 & E2 & E3) D P t M.
Proof.
  introv Ht He.
  remember (E1 & E3) as E13.
  destruct Ht; subst.
  apply typing_scheme_c
    with (L := dom E1 \u dom E2 \u dom E3 \u L).
  inst_fresh.
  apply valid_tenv_extension_and_typing_tenv_weakening;
    auto using type_environment_extension_ranges_weakening
      with wellformed.
Qed.

Lemma typing_schemes_tenv_weakening : forall v E1 E2 E3 D P ts Ms,
    typing_schemes v (E1 & E3) D P ts Ms ->
    type_environment (E1 & E2 & E3) ->
    typing_schemes v (E1 & E2 & E3) D P ts Ms.
Proof.
  introv Ht He.
  remember (E1 & E3) as E13.
  induction Ht; subst;
    auto using typing_scheme_tenv_weakening.
Qed.

Lemma typing_schemes_tenv_weakening_l : forall v E1 E2 D P ts Ms,
    typing_schemes v E1 D P ts Ms ->
    type_environment (E1 & E2) ->
    typing_schemes v (E1 & E2) D P ts Ms.
Proof.
  introv Ht Hv.
  rewrite <- concat_empty_r with (E := E1 & E2).
  apply typing_schemes_tenv_weakening;
    rewrite concat_empty_r; assumption.
Qed.

(* *************************************************************** *)
(** Weakening term environments *)

Lemma valid_env_weakening : forall v E1 E2 E3 D,
    valid_env v (E1 & E3) D ->
    type_environment (E1 & E2 & E3) ->
    valid_env v (E1 & E2 & E3) D.
Proof.
  introv Hd He.
  remember (E1 & E3) as E13.
  induction Hd; subst; auto using valid_scheme_weakening.
Qed.

Lemma valid_env_weakening_l : forall v E1 E2 D,
    valid_env v E1 D ->
    type_environment (E1 & E2) ->
    valid_env v (E1 & E2) D.
Proof.
  introv Hd He.
  rewrite <- concat_empty_r with (E := E1 & E2).
  apply valid_env_weakening;
    rewrite concat_empty_r; auto.
Qed.

(* ****************************************************** *)
(** ** Weakening valid store type *)

Lemma valid_store_type_weakening : forall E1 E2 E3 P,
    valid_store_type (E1 & E3) P ->
    type_environment (E1 & E2 & E3) ->
    valid_store_type (E1 & E2 & E3) P.
Proof.
  introv Hv He.
  remember (E1 & E3) as E13.
  induction Hv; subst; auto using kinding_weakening.
Qed.

Lemma valid_store_type_weakening_l : forall E1 E2 P,
    valid_store_type E1 P ->
    type_environment (E1 & E2) ->
    valid_store_type (E1 & E2) P.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E1 & E2).
  apply valid_store_type_weakening;
    rewrite concat_empty_r; auto.
Qed.

(* ****************************************************** *)
(** ** Weakening typing term environment *)

Lemma typing_env_weakening : forall v E D1 D2 D3 P t T,
    typing v E (D1 & D3) P t T ->
    type_environment E ->
    environment (D1 & D2 & D3) ->
    store_type P ->
    typing v E (D1 & D2 & D3) P t T.
Proof.
  introv Ht He Hd Hp.
  remember (D1 & D3) as D13.
  generalize dependent D3.
  induction Ht; introv Heq Hd; subst;
    eauto using binds_env_weakening.
  - apply typing_abs with (L \u dom D1 \u dom D2 \u dom D3); auto.
    intros x Hn.
    assert (environment (D1 & D2 & D3 & x ~ sch_empty T1)) as He3
      by auto with wellformed.
    rewrite <- concat_assoc.
    rewrite <- concat_assoc in He3.
    auto using concat_assoc.
  - assert (valid_scheme_aux v
              (L \u dom E \u dom D1 \u dom D2 \u dom D3) E M)
      by eauto using valid_scheme_aux_subset, subset_union_weak_l.
    assert (scheme_aux (L \u dom E \u dom D1 \u dom D2 \u dom D3) M)
      by auto with wellformed.
    apply typing_let_val
      with (L := L \u dom E \u dom D1 \u dom D2 \u dom D3) (M := M);
      eauto using type_environment_push_ranges with wellformed.
    intros x Hn.
    assert (environment (D1 & D2 & D3 & x ~ M)) as He3
      by auto with wellformed.
    rewrite <- concat_assoc.
    rewrite <- concat_assoc in He3.
    auto using concat_assoc.
  - apply typing_let
      with (L := L \u dom D1 \u dom D2 \u dom D3) (T1 := T1);
      auto.
    intros x Hn.
    assert (typing v E (D1 & D2 & D3) P t1 T1) by auto.
    assert (environment (D1 & D2 & D3 & x ~ sch_empty T1))
      as He2 by auto with wellformed.
    rewrite <- concat_assoc.
    rewrite <- concat_assoc in He2.
    auto using concat_assoc.
  - apply typing_match
      with (L := L \u dom D1 \u dom D2 \u dom D3) (T1 := T1)
           (T2 := T2) (T3 := T3) (T4 := T4); auto.
    + intros x Hn.
      pose (type_environment_extension_empty E) as He2.
      assert (type (typ_proj CSet.universe (CSet.singleton c) T2))
        as Ht2 by auto with wellformed.
      inversion Ht2; subst.
      assert (environment
                (D1 & D2 & D3
                 & x ~ sch_empty (typ_variant T2))) as He3
        by auto with wellformed.
      rewrite <- concat_assoc.
      rewrite <- concat_assoc in He3.
      auto using concat_assoc.
    + intros x Hn.
      pose (type_environment_extension_empty E) as He2.
      assert (type (typ_proj CSet.universe (CSet.cosingleton c) T3))
        as Ht2 by auto with wellformed.
      inversion Ht2; subst.
      assert (environment
                (D1 & D2 & D3
                 & x ~ sch_empty (typ_variant T3))) as He3
        by auto with wellformed.
      rewrite <- concat_assoc.
      rewrite <- concat_assoc in He3.
      auto using concat_assoc.
  - apply typing_destruct
      with (L := L \u dom D1 \u dom D2 \u dom D3) (T1 := T1)
           (T2 := T2) (T3 := T3); auto.
    intros x Hn.
    pose (type_environment_extension_empty E) as He2.
    assert (type (typ_constructor c T2))
      as Ht2 by auto with wellformed.
    inversion Ht2; subst.
    assert (environment (D1 & D2 & D3 & x ~ sch_empty T2))
      as He3 by auto with wellformed.
    rewrite <- concat_assoc in He3.
    assert
      (typing v E (D1 & D2 & (D3 & x ~ sch_empty T2)) P (t2 ^ x) T3)
      by auto using concat_assoc.
    assert (type T3) by auto with wellformed.
    assert (environment (D1 & D2 & D3 & x ~ sch_empty T3)) as He4
      by auto with wellformed.
    rewrite <- concat_assoc.
    rewrite <- concat_assoc in He4.
    auto using concat_assoc.
  - apply typing_fix
      with (L := L \u dom D1 \u dom D2 \u dom D3); auto.
    intros x y Hn1 Hn2.    
    assert (environment
              (D1 & D2 & D3
               & x ~ sch_empty (typ_arrow T1 T2)
               & y ~ sch_empty T1)) as He2
      by auto with wellformed.
    rewrite <- concat_assoc2.
    rewrite <- concat_assoc2 in He2.
    auto using concat_assoc2.
Qed.    

Lemma typing_env_weakening_l : forall v E D1 D2 P t T,
    typing v E D1 P t T ->
    type_environment E ->
    environment (D1 & D2) ->
    store_type P ->
    typing v E (D1 & D2) P t T.
Proof.
  introv Ht He Hd Hp.
  rewrite <- concat_empty_r with (E := D1 & D2).
  apply typing_env_weakening; rewrite ?concat_empty_r; auto.
Qed.

Lemma valid_tenv_extension_and_typing_env_weakening :
  forall v E1 E2 D1 D2 D3 P t T,
    valid_tenv_extension_and_typing v
      E1 E2 (D1 & D3) P t T ->
    type_environment E1 ->
    environment (D1 & D2 & D3) ->
    store_type P ->
    valid_tenv_extension_and_typing v
      E1 E2 (D1 & D2 & D3) P t T.
Proof.
  introv Hv He Hd Hp.
  remember (D1 & D3) as D13.
  assert (type_environment_extension E1 E2)
    by auto with wellformed.
  destruct Hv; subst.
  auto using typing_env_weakening, type_environment_extend.
Qed.

Lemma typing_scheme_env_weakening : forall v E D1 D2 D3 P t M,
    typing_scheme v E (D1 & D3) P t M ->
    type_environment E ->
    environment (D1 & D2 & D3) ->
    store_type P ->
    typing_scheme v E (D1 & D2 & D3) P t M.
Proof.
  introv Ht He Hd Hp.
  remember (D1 & D3) as D13.
  destruct Ht; subst.
  eauto using valid_tenv_extension_and_typing_env_weakening.
Qed.

Lemma typing_schemes_env_weakening : forall v E D1 D2 D3 P ts Ms,
    typing_schemes v E (D1 & D3) P ts Ms ->
    type_environment E ->
    environment (D1 & D2 & D3) ->
    store_type P ->
    typing_schemes v E (D1 & D2 & D3) P ts Ms.
Proof.
  introv Ht He Hd Hp.
  remember (D1 & D3) as D13.
  induction Ht; subst;
    auto using typing_scheme_env_weakening.
Qed.

Lemma typing_schemes_env_weakening_l : forall v E D1 D2 P ts Ms,
    typing_schemes v E D1 P ts Ms ->
    type_environment E ->
    environment (D1 & D2) ->
    store_type P ->
    typing_schemes v E (D1 & D2) P ts Ms.
Proof.
  introv Ht He Hd Hp.
  rewrite <- concat_empty_r with (E := D1 & D2).
  apply typing_schemes_env_weakening;
    rewrite ?concat_empty_r; auto.
Qed.
