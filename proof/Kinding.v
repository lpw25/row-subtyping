(************************************************
 *          Row Subtyping - Kinding             *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import LibLN Cofinite Disjoint Definitions
        Substitution Wellformedness.

(* *************************************************************** *)
(** ** Add hints for kinding constructors *)

Hint Constructors kinding kindings.

(* *************************************************************** *)
(** Length of kindings *)

Lemma kindings_length : forall E Ts Ks,
  kindings E Ts Ks ->
  length Ts = length Ks.
Proof.
  introv Hks.
  induction Hks; simpl; auto.
Qed.

(* *************************************************************** *)
(** Valid output *)

Lemma output_kinding : forall E T K,
  kinding E T K ->
  type_environment E ->
  kind K.
Proof.
  introv Hk He.
  induction Hk; subst; auto with csetdec.
  - eauto using range_from_tenv, rng_knd_kind. 
  - specialize (IHHk1 He).
    specialize (IHHk2 He).
    inversion IHHk1; inversion IHHk2; subst.
    auto with csetdec.
Qed.

Lemma output_kindings : forall E Ts Ks,
  kindings E Ts Ks ->
  type_environment E ->
  kinds Ks.
Proof.
  introv Hk He.
  induction Hk; eauto using output_kinding.
Qed.

(* *************************************************************** *)
(** Weakening *)

Lemma kinding_weakening : forall E1 E2 E3 T K,
   kinding (E1 & E3) T K -> 
   type_environment (E1 & E2 & E3) ->
   kinding (E1 & E2 & E3) T K.
Proof.
  introv Hk He.
  remember (E1 & E3) as E13.
  induction Hk; subst;
    eauto using binds_tenv_weakening.
Qed.

Lemma kinding_weakening_l : forall E1 E2 T K,
   kinding E1 T K -> 
   type_environment (E1 & E2) ->
   kinding (E1 & E2) T K.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E1 & E2).
  apply kinding_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma kindings_weakening : forall E1 E2 E3 Ts Ks,
   kindings (E1 & E3) Ts Ks -> 
   type_environment (E1 & E2 & E3) ->
   kindings (E1 & E2 & E3) Ts Ks.
Proof.
  introv Hks He.
  remember (E1 & E3) as E13.
  induction Hks; subst; auto using kinding_weakening.
Qed.

Lemma kindings_weakening_l : forall E1 E2 Ts Ks,
   kindings E1 Ts Ks -> 
   type_environment (E1 & E2) ->
   kindings (E1 & E2) Ts Ks.
Proof.
  introv Hks He.
  induction Hks; subst; auto using kinding_weakening_l.
Qed.

(* *************************************************************** *)
(** Closed *)

Lemma kinding_closed : forall E T K X,
    kinding E T K ->
    X # E ->
    X \notin (typ_fv T).
Proof.
  introv Hk Hn.
  induction Hk; simpl; auto.
  - apply notin_singleton_l.
    intro; subst.
    eauto using get_some_inv, binds_get.
Qed.

Lemma kindings_closed : forall E Ts Ks X,
    kindings E Ts Ks ->
    X # E ->
    X \notin (typ_fv_list Ts).
Proof.
  introv Hks Hn.
  induction Hks; simpl; eauto using kinding_closed.
Qed.  

(* *************************************************************** *)
(** Preserved by type substitution *)

Lemma kinding_typ_subst_var : forall E1 E2 E3 Xs Rs Us X R,
    binds X R (E1 & Xs ~* Rs & E2) ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    kindings E3 Us (rngs_knds Rs) ->
    kinding E3 (typ_var_subst Xs Us X) (rng_knd R)
    \/ (binds X R (E1 & E2)
        /\ typ_var_subst Xs Us X = typ_fvar X).
Proof.
  introv Hb Hl1 He Hks.
  assert (length Us = length Rs) as Hl2
    by (rewrite length_rngs_knds; eauto using kindings_length).
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

Lemma kinding_typ_subst : forall E1 E2 Xs Rs Us T K,
    kinding (E1 & Xs ~* Rs & E2) T K ->
    length Xs = length Rs ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    kindings (tenv_subst Xs Us (E1 & E2))
      Us (rngs_knds (rng_subst_list Xs Us Rs)) ->
    kinding (tenv_subst Xs Us (E1 & E2)) (typ_subst Xs Us T) K.
Proof.
  introv Hk Hl He Hks.
  remember (E1 & Xs ~* Rs & E2) as E3.
  induction Hk; subst; simpl; eauto.
  - rewrite <- rngs_knds_subst_list in Hks.
    destruct kinding_typ_subst_var
      with (E1 := E1) (E2 := E2) (E3 := tenv_subst Xs Us (E1 & E2))
           (Xs := Xs) (Rs := Rs) (Us := Us) (X := X) (R := R)
      as [?|[Hb Heq]]; auto.
    rewrite Heq.
    eauto using tenv_subst_binds, rng_knd_subst.
Qed.

Lemma kinding_typ_subst_l : forall E Xs Rs Us T K,
    kinding (E & Xs ~* Rs) T K ->
    length Xs = length Rs ->
    type_environment (E & Xs ~* Rs) ->
    kindings (tenv_subst Xs Us E)
      Us (rngs_knds (rng_subst_list Xs Us Rs)) ->
    kinding (tenv_subst Xs Us E) (typ_subst Xs Us T) K.
Proof.
  introv Hk Hl He Hks.
  rewrite <- (concat_empty_r E).
  rewrite <- (concat_empty_r E) in Hks.
  rewrite <- (concat_empty_r (E & Xs ~* Rs)) in Hk, He.
  eauto using kinding_typ_subst.
Qed.

(* *************************************************************** *)
(** Implied by ranging *)

Lemma ranging_kinding : forall E T R K,
  ranging E T R ->
  K = rng_knd R ->
  kinding E T K.
Proof.
  introv Hr Heq.
  induction Hr; subst; simpl; eauto.
Qed.

Lemma rangings_kindings : forall E Ts Rs Ks,
  rangings E Ts Rs ->
  Ks = rngs_knds Rs ->
  kindings E Ts Ks.
Proof.
  introv Hrs Heq.
  generalize dependent Ks.
  induction Hrs; introv Heq; subst; simpl;
    eauto using ranging_kinding.
Qed.

(* *************************************************************** *)
(** Unique *)

Lemma kinding_unique : forall E T K1 K2,
  kinding E T K1 ->
  kinding E T K2 ->
  K1 = K2.
Proof.
  introv Hk1 Hk2.
  generalize dependent K2.
  induction Hk1; introv Hk2; inversion Hk2; subst; auto.
  - assert (R = R0) by eauto using binds_func; subst.
    reflexivity.
Qed.

(* *************************************************************** *)
(** Inversions *)

Lemma kinding_constructor_inv : forall E c T cs,
    kinding E (typ_constructor c T) (knd_row cs) ->
    kinding E T knd_type.
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_or_inv_l : forall E T1 T2 cs1 cs2 cs3,
    kinding E (typ_or cs1 T1 cs2 T2) (knd_row cs3) ->
    kinding E T1 (knd_row cs1).
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_or_inv_r : forall E T1 T2 cs1 cs2 cs3,
    kinding E (typ_or cs1 T1 cs2 T2) (knd_row cs3) ->
    kinding E T2 (knd_row cs2).
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_proj_inv : forall E T cs1 cs2,
    kinding E (typ_proj cs1 T cs2) (knd_row cs2) ->
    kinding E T (knd_row cs1).
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_variant_inv : forall E T,
    kinding E (typ_variant T) knd_type ->
    kinding E T knd_range.
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_arrow_inv_l : forall E T1 T2,
    kinding E (typ_arrow T1 T2) knd_type ->
    kinding E T1 knd_type.
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_arrow_inv_r : forall E T1 T2,
    kinding E (typ_arrow T1 T2) knd_type ->
    kinding E T2 knd_type.
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_ref_inv : forall E T,
    kinding E (typ_ref T) knd_type ->
    kinding E T knd_type.
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_prod_inv_l : forall E T1 T2,
    kinding E (typ_prod T1 T2) knd_type ->
    kinding E T1 knd_type.
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_prod_inv_r : forall E T1 T2,
    kinding E (typ_prod T1 T2) knd_type ->
    kinding E T2 knd_type.
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_meet_inv_l : forall E T1 T2 cs,
    kinding E (typ_meet T1 T2) (knd_row cs) ->
    kinding E T1 (knd_row cs).
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_meet_inv_r : forall E T1 T2 cs,
    kinding E (typ_meet T1 T2) (knd_row cs) ->
    kinding E T2 (knd_row cs).
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_join_inv_l : forall E T1 T2 cs,
    kinding E (typ_join T1 T2) (knd_row cs) ->
    kinding E T1 (knd_row cs).
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

Lemma kinding_join_inv_r : forall E T1 T2 cs,
    kinding E (typ_join T1 T2) (knd_row cs) ->
    kinding E T2 (knd_row cs).
Proof.
  introv Hk.
  inversion Hk; auto.
Qed.

(* *************************************************************** *)
(** Automation *)

Ltac extract_kinding H T :=
  match type of H with
  | kinding _ T _ => exact H
  | kinding _ (typ_constructor _ _) _ =>
      extract_kinding (kinding_constructor_inv H) T
  | kinding _ (typ_or _ ?T1 _ _) _ =>
      match T1 with
      | context[T] => extract_kinding (kinding_or_inv_l H) T
      | _ => extract_kinding (kinding_or_inv_r H) T
      end
  | kinding _ (typ_proj _ _ _) _ =>
      extract_kinding (kinding_proj_inv H) T
  | kinding _ (typ_variant _) _ =>
      extract_kinding (kinding_variant_inv H) T
  | kinding _ (typ_arrow ?T1 _) _ =>
      match T1 with
      | context[T] => extract_kinding (kinding_arrow_inv_l H) T
      | _ => extract_kinding (kinding_arrow_inv_r H) T
      end
  | kinding _ (typ_ref _) _ =>
      extract_kinding (kinding_ref_inv H) T
  | kinding _ (typ_prod ?T1 _) _ =>
      match T1 with
      | context[T] => extract_kinding (kinding_prod_inv_l H) T
      | _ => extract_kinding (kinding_prod_inv_r H) T
      end
  | kinding _ (typ_meet ?T1 _) _ =>
      match T1 with
      | context[T1] => extract_kinding (kinding_meet_inv_l H) T
      | _ => extract_kinding (kinding_meet_inv_r H) T
      end
  | kinding _ (typ_join ?T1 _) _ =>
      match T1 with
      | context[T] => extract_kinding (kinding_join_inv_l H) T
      | _ => extract_kinding (kinding_join_inv_r H) T
      end
  end.

Ltac kinding :=
  match goal with
  | |- kinding ?E ?T _ =>
    match goal with
    | H : kinding E ?Th _ |- _ =>
      match Th with
      | context[T] => extract_kinding H T
      end
    | H : ?Q -> kinding E ?Th _, Hq : ?Q |- _ =>
      match Th with
      | context[T] => extract_kinding (H Hq) T
      end
    | H : ?Q1 -> ?Q2 -> kinding E ?Th _,
      Hq1 : ?Q1, Hq2 : ?Q2 |- _ =>
      match Th with
      | context[T] => extract_kinding (H Hq1 Hq2) T
      end
    end
  end.

Hint Extern 1 (kinding _ _ _) => kinding : kinding.
