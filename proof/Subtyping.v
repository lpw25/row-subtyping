(************************************************
 *          Row Subtyping - Subtyping           *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import Arith LibLN.
Require Import Cofinite Disjoint Definitions Substitution
        Wellformedness Kinding.

(* ****************************************************** *)
(** ** Add hints for subtyping constructors *)

Hint Constructors type_equal_core type_equal_symm
     type_equal_cong type_equal subtype.

(* *************************************************************** *)
(** Valid output *)

Lemma output_type_equal_core : forall E T1 T2 K,
  type_equal_core E T1 T2 K ->
  type_environment E ->
  kind K.
Proof.
  introv Hte He.
  induction Hte; eauto 3 using output_kinding;
    auto with csetdec.
  - assert (kind (knd_row cs3)) as Hk
      by eauto using output_kinding.
    inversion Hk; subst.
    auto with csetdec.
Qed.

(* *************************************************************** *)
(** Kinding from type equality *)

Lemma type_equal_core_kinding_1 : forall E T1 T2 K,
    type_equal_core E T1 T2 K ->
    type_environment E ->
    kinding E T1 K.
Proof.
  introv Hte He.
  induction Hte; auto with csetdec.
  - assert (kind (knd_row cs1)) as Hk
      by eauto using output_kinding.
    inversion Hk; subst.
    auto with csetdec.
  - assert (kind (knd_row cs1)) as Hk
      by eauto using output_kinding.
    inversion Hk; subst.
    auto.
  - assert (kind (knd_row cs1)) as Hk
      by eauto using output_kinding.
    inversion Hk; subst.
    auto.
Qed.

Lemma type_equal_core_kinding_2 : forall E T1 T2 K,
    type_equal_core E T1 T2 K ->
    type_environment E ->
    kinding E T2 K.
Proof.
  introv Hte He.
  induction Hte; auto with csetdec.
Qed.

Lemma type_equal_symm_kinding_1 : forall E T1 T2 K,
    type_equal_symm E T1 T2 K ->
    type_environment E ->
    kinding E T1 K.
Proof.
  introv Hte He.
  destruct Hte;
    eauto using type_equal_core_kinding_1,
      type_equal_core_kinding_2.
Qed.

Lemma type_equal_symm_kinding_2 : forall E T1 T2 K,
    type_equal_symm E T1 T2 K ->
    type_environment E ->
    kinding E T2 K.
Proof.
  introv Hte He.
  destruct Hte;
    eauto using type_equal_core_kinding_1,
      type_equal_core_kinding_2.
Qed.

Lemma type_equal_cong_kinding_1 : forall E T1 T2 K,
    type_equal_cong E T1 T2 K ->
    type_environment E ->
    kinding E T1 K.
Proof.
  introv Hte He.
  induction Hte;
    eauto using type_equal_symm_kinding_1.
Qed.

Lemma type_equal_cong_kinding_2 : forall E T1 T2 K,
    type_equal_cong E T1 T2 K ->
    type_environment E ->
    kinding E T2 K.
Proof.
  introv Hte He.
  induction Hte;
    eauto using type_equal_symm_kinding_2.
Qed.

Lemma type_equal_kinding_1 : forall E T1 T2 K,
    type_equal E T1 T2 K ->
    type_environment E ->
    kinding E T1 K.
Proof.
  introv Hte He.
  induction Hte;
    eauto using type_equal_cong_kinding_1.
Qed.

Lemma type_equal_kinding_2 : forall E T1 T2 K,
    type_equal E T1 T2 K ->
    type_environment E ->
    kinding E T2 K.
Proof.
  introv Hte He.
  induction Hte;
    eauto using type_equal_cong_kinding_2.
Qed.

Lemma subtype_kinding_1 : forall E T1 T2 cs,
    subtype E T1 T2 cs ->
    type_environment E ->
    kinding E T1 (knd_row cs).
Proof.
  introv Hte He.
  induction Hte;
    eauto using type_equal_kinding_1.
Qed.

Lemma subtype_kinding_2 : forall E T1 T2 cs,
    subtype E T1 T2 cs ->
    type_environment E ->
    kinding E T2 (knd_row cs).
Proof.
  introv Hte He.
  assert (kinding E (typ_meet T1 T2) (knd_row cs)) as Hk
    by (induction Hte; eauto using type_equal_kinding_2).
  inversion Hk; subst.
  auto.
Qed.

(* *************************************************************** *)
(** Automation *)

Ltac equality_kinding :=
  match goal with
  | |- kinding ?E ?T _ =>
    match goal with
    | He : type_environment ?E,
      H : type_equal_core ?E ?Th _ _ |- _ =>
      match Th with
      | context[T] =>
          extract_kinding (type_equal_core_kinding_1 H He) T
      end
    | He : type_environment ?E,
      H : type_equal_core ?E _ ?Th _ |- _ =>
      match Th with
      | context[T] =>
          extract_kinding (type_equal_core_kinding_2 H He) T
      end
    | He : type_environment ?E,
      H : type_equal_symm ?E ?Th _ _ |- _ =>
      match Th with
      | context[T] =>
          extract_kinding (type_equal_symm_kinding_1 H He) T
      end
    | He : type_environment ?E,
      H : type_equal_symm ?E _ ?Th _ |- _ =>
      match Th with
      | context[T] =>
          extract_kinding (type_equal_symm_kinding_2 H He) T
      end
    | He : type_environment ?E,
      H : type_equal_cong ?E ?Th _ _ |- _ =>
      match Th with
      | context[T] =>
          extract_kinding (type_equal_cong_kinding_1 H He) T
      end
    | He : type_environment ?E,
      H : type_equal_cong ?E _ ?Th _ |- _ =>
      match Th with
      | context[T] =>
          extract_kinding (type_equal_cong_kinding_2 H He) T
      end
    | He : type_environment ?E,
      H : type_equal ?E ?Th _ _ |- _ =>
      match Th with
      | context[T] =>
          extract_kinding (type_equal_kinding_1 H He) T
      end
    | He : type_environment ?E,
      H : type_equal ?E _ ?Th _ |- _ =>
      match Th with
      | context[T] =>
          extract_kinding (type_equal_kinding_2 H He) T
      end
    | He : type_environment ?E,
      H : subtype ?E ?Th _ _ |- _ =>
      match Th with
      | context[T] =>
          extract_kinding (subtype_kinding_1 H He) T
      end
    | He : type_environment ?E,
      H : subtype ?E _ ?Th _ |- _ =>
      match Th with
      | context[T] =>
          extract_kinding (subtype_kinding_2 H He) T
      end
    end
  end. 

Hint Extern 1 (kinding _ _ _) => equality_kinding : kinding.

(* *************************************************************** *)
(** Weakening *)

Lemma type_equal_core_weakening : forall E1 E2 E3 T1 T2 K,
   type_equal_core (E1 & E3) T1 T2 K -> 
   type_environment (E1 & E2 & E3) ->
   type_equal_core (E1 & E2 & E3) T1 T2 K.
Proof.
  introv Hte He.
  remember (E1 & E3) as E4.
  destruct Hte; subst; auto using kinding_weakening.
Qed.

Lemma type_equal_symm_weakening : forall E1 E2 E3 T1 T2 K,
   type_equal_symm (E1 & E3) T1 T2 K -> 
   type_environment (E1 & E2 & E3) ->
   type_equal_symm (E1 & E2 & E3) T1 T2 K.
Proof.
  introv Hte He.
  remember (E1 & E3) as E4.
  destruct Hte; subst; auto using type_equal_core_weakening.
Qed.

Lemma type_equal_cong_weakening : forall E1 E2 E3 T1 T2 K,
   type_equal_cong (E1 & E3) T1 T2 K -> 
   type_environment (E1 & E2 & E3) ->
   type_equal_cong (E1 & E2 & E3) T1 T2 K.
Proof.
  introv Hte He.
  remember (E1 & E3) as E4.
  induction Hte; subst;
    auto using type_equal_symm_weakening, kinding_weakening.
Qed.

Lemma type_equal_weakening : forall E1 E2 E3 T1 T2 K,
   type_equal (E1 & E3) T1 T2 K -> 
   type_environment (E1 & E2 & E3) ->
   type_equal (E1 & E2 & E3) T1 T2 K.
Proof.
  introv Hte He.
  remember (E1 & E3) as E4.
  induction Hte; subst;
    eauto using kinding_weakening, type_equal_cong_weakening.
Qed.

Lemma type_equal_weakening_l : forall E1 E2 T1 T2 K,
   type_equal E1 T1 T2 K -> 
   type_environment (E1 & E2) ->
   type_equal (E1 & E2) T1 T2 K.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E1 & E2).
  apply type_equal_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma subtype_weakening : forall E1 E2 E3 T1 T2 cs,
   subtype (E1 & E3) T1 T2 cs -> 
   type_environment (E1 & E2 & E3) ->
   subtype (E1 & E2 & E3) T1 T2 cs.
Proof.
  introv Hsb He.
  remember (E1 & E3) as E4.
  destruct Hsb; subst; auto using type_equal_weakening.
Qed.

Lemma subtype_weakening_l : forall E1 E2 T1 T2 cs,
   subtype E1 T1 T2 cs -> 
   type_environment (E1 & E2) ->
   subtype (E1 & E2) T1 T2 cs.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E1 & E2).
  apply subtype_weakening; rewrite concat_empty_r; assumption.
Qed.

(* *************************************************************** *)
(** Closed *)

Lemma type_equal_core_closed_l : forall E T1 T2 K X,
    type_equal_core E T1 T2 K ->
    X # E ->
    X \notin (typ_fv T1).
Proof.
  introv Hte Hn.
  - destruct Hte; simpl;
      rewrite ?notin_union;
      intuition eauto using kinding_closed.
Qed.

Lemma type_equal_core_closed_r : forall E T1 T2 K X,
    type_equal_core E T1 T2 K ->
    X # E ->
    X \notin (typ_fv T2).
Proof.
  introv Hte Hn.
  - destruct Hte; simpl;
      rewrite ?notin_union;
      intuition eauto using kinding_closed.
Qed.

Lemma type_equal_symm_closed_l : forall E T1 T2 K X,
    type_equal_symm E T1 T2 K ->
    X # E ->
    X \notin (typ_fv T1).
Proof.
  introv Hte Hn.
  destruct Hte;
    eauto using type_equal_core_closed_l, type_equal_core_closed_r.
Qed.

Lemma type_equal_symm_closed_r : forall E T1 T2 K X,
    type_equal_symm E T1 T2 K ->
    X # E ->
    X \notin (typ_fv T2).
Proof.
  introv Hte Hn.
  destruct Hte;
    eauto using type_equal_core_closed_l, type_equal_core_closed_r.
Qed.

Lemma type_equal_cong_closed_l : forall E T1 T2 K X,
    type_equal_cong E T1 T2 K ->
    X # E ->
    X \notin (typ_fv T1).
Proof.
  introv Hte Hn.
  induction Hte; simpl;
    rewrite ?notin_union;
    intuition eauto using kinding_closed, type_equal_symm_closed_l.
Qed.  

Lemma type_equal_cong_closed_r : forall E T1 T2 K X,
    type_equal_cong E T1 T2 K ->
    X # E ->
    X \notin (typ_fv T2).
Proof.
  introv Hte Hn.
  induction Hte; simpl;
    rewrite ?notin_union;
    intuition eauto using kinding_closed, type_equal_symm_closed_r.
Qed.

Lemma type_equal_closed_l : forall E T1 T2 K X,
    type_equal E T1 T2 K ->
    X # E ->
    X \notin (typ_fv T1).
Proof.
  introv Hte Hn.
  induction Hte;
    eauto using kinding_closed, type_equal_cong_closed_l.
Qed.

Lemma type_equal_closed_r : forall E T1 T2 K X,
    type_equal E T1 T2 K ->
    X # E ->
    X \notin (typ_fv T2).
Proof.
  introv Hte Hn.
  induction Hte; eauto using kinding_closed.
Qed.

Lemma subtype_closed_l : forall E T1 T2 cs X,
    subtype E T1 T2 cs ->
    X # E ->
    X \notin (typ_fv T1).
Proof.
  introv Hsb Hn.
  destruct Hsb.
  eauto using type_equal_closed_l.
Qed.

Lemma subtype_closed_r : forall E T1 T2 cs X,
    subtype E T1 T2 cs ->
    X # E ->
    X \notin (typ_fv T2).
Proof.
  introv Hsb Hn.
  destruct Hsb.
  assert (X \notin (typ_fv (typ_meet T1 T2)))
    by eauto using type_equal_closed_r.
  simpl in *.
  auto.
Qed.

(* *************************************************************** *)
(** Preserved by type substitution *)

Lemma type_equal_core_typ_subst : forall E1 E2 Xs Rs Us T1 T2 K,
  type_equal_core (E1 & Xs ~* Rs & E2) T1 T2 K ->
  length Xs = length Rs ->
  type_environment (E1 & Xs ~* Rs & E2) ->
  rangings (tenv_subst Xs Us (E1 & E2))
    Us (rng_subst_list Xs Us Rs) ->
  type_equal_core (tenv_subst Xs Us (E1 & E2))
    (typ_subst Xs Us T1) (typ_subst Xs Us T2) K.
Proof.
  introv Hte Hl He Hrs.
  assert (kindings (tenv_subst Xs Us (E1 & E2))
            Us (rngs_knds (rng_subst_list Xs Us Rs)))
    by eauto using kinding_typ_subst, rangings_kindings.
  remember (E1 & Xs ~* Rs & E2) as E3.
  destruct Hte; subst; simpl; eauto using kinding_typ_subst.
  - apply type_equal_core_or_meet_distribution;
      eauto using kinding_typ_subst.
  - apply type_equal_core_or_join_distribution;
      eauto using kinding_typ_subst.
Qed.

Lemma type_equal_symm_typ_subst : forall E1 E2 Xs Rs Us T1 T2 K,
  type_equal_symm (E1 & Xs ~* Rs & E2) T1 T2 K ->
  length Xs = length Rs ->
  type_environment (E1 & Xs ~* Rs & E2) ->
  rangings (tenv_subst Xs Us (E1 & E2))
    Us (rng_subst_list Xs Us Rs) ->
  type_equal_symm (tenv_subst Xs Us (E1 & E2))
    (typ_subst Xs Us T1) (typ_subst Xs Us T2) K.
Proof.
  introv Hte Hl He Hrs.
  remember (E1 & Xs ~* Rs & E2) as E3.
  destruct Hte; subst; simpl;
    eauto using type_equal_core_typ_subst.
Qed.

Lemma type_equal_cong_typ_subst : forall E1 E2 Xs Rs Us T1 T2 K,
  type_equal_cong (E1 & Xs ~* Rs & E2) T1 T2 K ->
  length Xs = length Rs ->
  type_environment (E1 & Xs ~* Rs & E2) ->
  rangings (tenv_subst Xs Us (E1 & E2))
    Us (rng_subst_list Xs Us Rs) ->
  type_equal_cong (tenv_subst Xs Us (E1 & E2))
    (typ_subst Xs Us T1) (typ_subst Xs Us T2) K.
Proof.
  introv Hte Hl He Hrs.
  assert (kindings (tenv_subst Xs Us (E1 & E2))
            Us (rngs_knds (rng_subst_list Xs Us Rs)))
    by eauto using kinding_typ_subst, rangings_kindings.
  remember (E1 & Xs ~* Rs & E2) as E3.
  induction Hte; subst; simpl;
    eauto using type_equal_symm_typ_subst, kinding_typ_subst.
Qed.

Lemma type_equal_typ_subst : forall E1 E2 Xs Rs Us T1 T2 K,
  type_equal (E1 & Xs ~* Rs & E2) T1 T2 K ->
  length Xs = length Rs ->
  type_environment (E1 & Xs ~* Rs & E2) ->
  rangings (tenv_subst Xs Us (E1 & E2))
    Us (rng_subst_list Xs Us Rs) ->
  type_equal (tenv_subst Xs Us (E1 & E2))
    (typ_subst Xs Us T1) (typ_subst Xs Us T2) K.
Proof.
  introv Hte Hl He Hrs.
  assert (kindings (tenv_subst Xs Us (E1 & E2))
            Us (rngs_knds (rng_subst_list Xs Us Rs)))
    by eauto using kinding_typ_subst, rangings_kindings.
  remember (E1 & Xs ~* Rs & E2) as E3.
  induction Hte; subst; simpl; eauto using kinding_typ_subst.
  apply type_equal_step
    with (T2 := typ_subst Xs Us T2);
      eauto using type_equal_cong_typ_subst.
Qed.

Lemma type_equal_typ_subst_l : forall E Xs Rs Us T1 T2 K,
  type_equal (E & Xs ~* Rs) T1 T2 K ->
  length Xs = length Rs ->
  type_environment (E & Xs ~* Rs) ->
  rangings (tenv_subst Xs Us E)
    Us (rng_subst_list Xs Us Rs) ->
  type_equal (tenv_subst Xs Us E)
    (typ_subst Xs Us T1) (typ_subst Xs Us T2) K.
Proof.
  introv Hte Hl He Hrs.
  rewrite <- (concat_empty_r E).
  rewrite <- (concat_empty_r E) in Hrs.
  rewrite <- (concat_empty_r (E & Xs ~* Rs)) in Hte, He.
  eauto using type_equal_typ_subst.
Qed.

Lemma subtype_typ_subst : forall E1 E2 Xs Rs Us T1 T2 cs,
  subtype (E1 & Xs ~* Rs & E2) T1 T2 cs ->
  length Xs = length Rs ->
  type_environment (E1 & Xs ~* Rs & E2) ->
  rangings (tenv_subst Xs Us (E1 & E2))
    Us (rng_subst_list Xs Us Rs) ->
  subtype (tenv_subst Xs Us (E1 & E2))
    (typ_subst Xs Us T1) (typ_subst Xs Us T2) cs.
Proof.
  introv Hsb Hl He Hrs.
  remember (E1 & Xs ~* Rs & E2) as E3.
  destruct Hsb; subst.
  apply subtype_c.
  replace (typ_meet (typ_subst Xs Us T1) (typ_subst Xs Us T2))
    with (typ_subst Xs Us (typ_meet T1 T2)) by auto.
  eauto using type_equal_typ_subst.
Qed.

Lemma subtype_typ_subst_l : forall E Xs Rs Us T1 T2 cs,
  subtype (E & Xs ~* Rs) T1 T2 cs ->
  length Xs = length Rs ->
  type_environment (E & Xs ~* Rs) ->
  rangings (tenv_subst Xs Us E)
    Us (rng_subst_list Xs Us Rs) ->
  subtype (tenv_subst Xs Us E)
    (typ_subst Xs Us T1) (typ_subst Xs Us T2) cs.
Proof.
  introv Hsb Hl He Hrs.
  rewrite <- (concat_empty_r E).
  rewrite <- (concat_empty_r E) in Hrs.
  rewrite <- (concat_empty_r (E & Xs ~* Rs)) in Hsb, He.
  eauto using subtype_typ_subst.
Qed.

(* **************************************************** *)
(** Type equality is an equivalence *)

Lemma type_equal_reflexive : forall E T K,
    kinding E T K ->
    type_equal E T T K.
Proof.
  auto.
Qed.

Lemma type_equal_transitive : forall E T1 T2 T3 K,
    type_equal E T1 T2 K ->
    type_equal E T2 T3 K ->
    type_equal E T1 T3 K.
Proof.
  introv Hte1 Hte2.
  induction Hte1; eauto.
Qed.

Lemma type_equal_symm_symmetric : forall E T1 T2 K,
    type_equal_symm E T1 T2 K ->
    type_equal_symm E T2 T1 K.
Proof.
  introv Hte.
  destruct Hte; auto.
Qed.

Lemma type_equal_cong_symmetric : forall E T1 T2 K,
    type_equal_cong E T1 T2 K ->
    type_equal_cong E T2 T1 K.
Proof.
  introv Hte.
  induction Hte; auto using type_equal_symm_symmetric.
Qed.
  
Lemma type_equal_symmetric_ind : forall E T1 T2 T3 K,
    type_equal E T2 T1 K ->
    type_equal E T2 T3 K ->
    type_equal E T3 T1 K.
Proof.
  introv Hacc Hte.
  induction Hte; eauto using type_equal_cong_symmetric. 
Qed.  

Lemma type_equal_symmetric : forall E T1 T2 K,
    type_equal E T1 T2 K ->
    type_environment E ->
    type_equal E T2 T1 K.
Proof.
  introv Hte He.
  destruct Hte; auto.
  eauto using type_equal_symmetric_ind with kinding.
Qed.

(* ****************************************************** *)
(** Convenient lemmas for single-step equality proofs *)

Lemma type_equal_single : forall E T1 T2 K,
    type_equal_cong E T1 T2 K ->
    type_environment E ->
    type_equal E T1 T2 K.
Proof.
  introv Hte.
  eauto with kinding.
Qed.

Lemma type_equal_post_step : forall E T1 T2 T3 K,
    type_equal E T1 T2 K ->
    type_equal_cong E T2 T3 K ->
    type_environment E ->
    type_equal E T1 T3 K.
Proof.
  introv Hte1 Hte2 He.
  eauto using type_equal_transitive, type_equal_single.
Qed.

(* ***************************************************** *)
(** Idempotence of join and meet *)

Lemma type_equal_join_idempotent : forall E T cs,
    type_environment E ->
    kinding E T (knd_row cs) ->
    type_equal E T (typ_join T T) (knd_row cs).
Proof.
  introv He Hk.
  assert (kind (knd_row cs)) as Hknd
    by eauto using output_kinding.
  inversion Hknd; subst.
  apply type_equal_step
    with (T2 := typ_join T (typ_meet T (typ_top cs))); auto.
  apply type_equal_single; auto.
Qed.    

Lemma type_equal_meet_idempotent : forall E T cs,
    type_environment E ->
    kinding E T (knd_row cs) ->
    type_equal E T (typ_meet T T) (knd_row cs).
Proof.
  introv He Hk.
  assert (kind (knd_row cs)) as Hknd
    by eauto using output_kinding.
  inversion Hknd; subst.
  apply type_equal_step
    with (T2 := typ_meet T (typ_join T (typ_bot cs))); auto.
  apply type_equal_single; auto.
Qed.

(* *************************************************************** *)
(** Congruence of type equality *)

Lemma type_equal_constructor : forall E c T1 T1' cs,
    type_equal E T1 T1' knd_type ->
    cs = CSet.singleton c ->
    type_equal E
      (typ_constructor c T1) (typ_constructor c T1')
      (knd_row cs).
Proof.
  introv Hte Heq.
  remember knd_type as K.
  induction Hte; subst; eauto.
Qed.

Lemma type_equal_proj : forall E T1 T1' cs1 cs2,
    type_equal E T1 T1' (knd_row cs1) ->
    CSet.Subset cs2 cs1 ->
    CSet.Nonempty cs2 ->
    type_equal E (typ_proj cs1 T1 cs2)
      (typ_proj cs1 T1' cs2) (knd_row cs2).
Proof.
  introv Hte Hs Hn.
  remember (knd_row cs1) as K.
  induction Hte; subst; eauto.
Qed.

Lemma type_equal_variant : forall E T1 T1',
    type_equal E T1 T1' knd_range ->
    type_equal E (typ_variant T1) (typ_variant T1') knd_type.
Proof.
  introv Hte.
  remember knd_range as K.
  induction Hte; subst; eauto.
Qed.
 
Lemma type_equal_or : forall E T1 T1' T2 T2' cs1 cs2 cs3,
    type_equal E T1 T1' (knd_row cs1) ->
    type_equal E T2 T2' (knd_row cs2) ->
    CSet.Disjoint cs1 cs2 ->
    cs3 = CSet.union cs1 cs2 ->
    type_environment E ->
    type_equal E (typ_or cs1 T1 cs2 T2)
      (typ_or cs1 T1' cs2 T2') (knd_row cs3).
Proof.
  introv Hte1 Hte2 Hd Heq He.
  apply type_equal_transitive with (typ_or cs1 T1' cs2 T2).
  - remember (knd_row cs1) as K.
    induction Hte1; subst; eauto with kinding.
  - remember (knd_row cs2) as K.
    induction Hte2; subst; eauto with kinding.
Qed.    

Lemma type_equal_arrow : forall E T1 T1' T2 T2',
    type_equal E T1 T1' knd_type ->
    type_equal E T2 T2' knd_type ->
    type_environment E ->
    type_equal E (typ_arrow T1 T2) (typ_arrow T1' T2') knd_type.
Proof.
  introv Hte1 Hte2 He.
  apply type_equal_transitive with (typ_arrow T1' T2).
  - remember knd_type as K.
    induction Hte1; subst; eauto with kinding.
  - remember knd_type as K.
    induction Hte2; subst; eauto with kinding.
Qed.

Lemma type_equal_meet : forall E T1 T1' T2 T2' cs,
    type_equal E T1 T1' (knd_row cs) ->
    type_equal E T2 T2' (knd_row cs) ->
    type_environment E ->
    type_equal E (typ_meet T1 T2) (typ_meet T1' T2') (knd_row cs).
Proof.
  introv Hte1 Hte2 Hke.
  apply type_equal_transitive with (typ_meet T1' T2).
  - remember (knd_row cs) as K.
    induction Hte1; subst; eauto with kinding.
  - remember (knd_row cs) as K.
    induction Hte2; subst; eauto with kinding.
Qed.

Lemma type_equal_join : forall E T1 T1' T2 T2' cs,
    type_equal E T1 T1' (knd_row cs) ->
    type_equal E T2 T2' (knd_row cs) ->
    type_environment E ->
    type_equal E (typ_join T1 T2) (typ_join T1' T2') (knd_row cs).
Proof.
  introv Hte1 Hte2 He.
  apply type_equal_transitive with (typ_join T1' T2).
  - remember (knd_row cs) as K.
    induction Hte1; subst; eauto with kinding.
  - remember (knd_row cs) as K.
    induction Hte2; subst; eauto with kinding.
Qed.

(* ****************************************************** *)
(** Subtyping is a partial order *)

Lemma subtype_refl : forall E T cs,
    type_environment E ->
    kinding E T (knd_row cs) ->
    subtype E T T cs.
Proof.
  intros He Hk.
  auto using type_equal_meet_idempotent.
Qed.

Lemma subtype_reflexive : forall E T1 T2 cs,
    type_equal E T1 T2 (knd_row cs) ->
    type_environment E ->
    subtype E T1 T2 cs.
Proof.
  introv Hte He.
  apply subtype_c.
  apply type_equal_transitive with (typ_meet T1 T1);
    eauto using type_equal_meet_idempotent, type_equal_meet
      with kinding.
Qed.
     
Lemma subtype_transitive : forall E T1 T2 T3 cs,
    subtype E T1 T2 cs ->
    subtype E T2 T3 cs ->
    type_environment E ->
    subtype E T1 T3 cs.
Proof.
  introv Hs1 Hs2 He.
  destruct Hs1.
  destruct Hs2.
  apply subtype_c.
  apply type_equal_transitive with (typ_meet T1 T0); auto.
  apply type_equal_transitive with (typ_meet T1 (typ_meet T0 T2));
    eauto using type_equal_meet, subtype_kinding_1,
      subtype_kinding_2.
  apply type_equal_step with (typ_meet (typ_meet T1 T0) T2);
    auto with kinding.
  auto using type_equal_meet, type_equal_symmetric with kinding.
Qed.

Lemma subtype_antisymmetric : forall E T1 T2 cs,
    subtype E T1 T2 cs ->
    subtype E T2 T1 cs ->
    type_environment E ->
    type_equal E T1 T2 (knd_row cs).
Proof.
  introv Hs1 Hs2 He.
  destruct Hs1; destruct Hs2.
  apply type_equal_transitive with (typ_meet T2 T1); auto.
  apply type_equal_step with (typ_meet T1 T2);
    eauto with kinding.
  apply type_equal_symmetric; auto.
Qed.

(* *************************************************************** *)
(** Typing lattice is bounded *)

Lemma subtype_top : forall E T cs,
    type_environment E ->
    kinding E T (knd_row cs) ->
    subtype E T (typ_top cs) cs.
Proof.
  introv He Hk.
  assert (kind (knd_row cs)) as Hknd
    by eauto using output_kinding.
  inversion Hknd; subst.
  auto 6 using type_equal_single.
Qed.

Lemma subtype_bot : forall E T cs,
    type_environment E ->
    kinding E T (knd_row cs) ->
    subtype E (typ_bot cs) T cs.
Proof.
  introv He Hk.
  assert (kind (knd_row cs)) as Hknd
    by eauto using output_kinding.
  inversion Hknd; subst.
  apply subtype_c.
  apply type_equal_step
    with (typ_meet (typ_bot cs) (typ_join (typ_bot cs) T)); auto.
  apply type_equal_step
    with (typ_meet (typ_bot cs) (typ_join T (typ_bot cs))); auto 6.
  apply type_equal_single; auto.
Qed.  

(* ****************************************************** *)
(** Convenient lemmas for subtyping proofs *)

Lemma subtype_reflexive_single : forall E T1 T2 cs,
    type_equal_cong E T1 T2 (knd_row cs) ->
    type_environment E ->
    subtype E T1 T2 cs.
Proof.
  introv Hte He.
  apply subtype_reflexive; auto.
  apply type_equal_single; auto.
Qed.

Lemma subtype_reflexive_step : forall E T1 T2 T3 cs,
    subtype E T1 T2 cs ->
    type_equal_cong E T1 T3 (knd_row cs) ->
    type_environment E ->
    subtype E T3 T2 cs.
Proof.
  introv Hs He Hte.
  destruct Hs.
  apply subtype_c.
  apply type_equal_step with T1;
    auto using type_equal_cong_symmetric.
  apply type_equal_transitive with (typ_meet T1 T2); auto.
  apply type_equal_single; auto with kinding.
Qed.

Lemma subtype_reflexive_post_step : forall E T1 T2 T3 cs,
    subtype E T1 T2 cs ->
    type_equal_cong E T2 T3 (knd_row cs) ->
    type_environment E ->
    subtype E T1 T3 cs.
Proof.
  introv Hs Hte He.
  destruct Hs.
  apply subtype_c.
  apply type_equal_transitive with (typ_meet T1 T2); auto.
  apply type_equal_single; eauto with kinding.
Qed.

(* *************************************************************** *)
(** Congruence of subtyping *)

Lemma subtype_proj : forall E T1 T1' cs1 cs2,
    subtype E T1 T1' cs1 ->
    CSet.Subset cs2 cs1 ->
    CSet.Nonempty cs2 ->
    type_environment E ->
    subtype E (typ_proj cs1 T1 cs2) (typ_proj cs1 T1' cs2) cs2.
Proof.
  introv Hs Hsb Hn He.
  destruct Hs.
  apply subtype_c.
  apply type_equal_post_step
    with (typ_proj cs (typ_meet T1 T2) cs2);
      eauto using type_equal_proj with kinding. 
Qed.

Lemma subtype_or : forall E T1 T1' T2 T2' cs1 cs2 cs,
    subtype E T1 T1' cs1 ->
    subtype E T2 T2' cs2 ->
    CSet.Disjoint cs1 cs2 ->
    cs = CSet.union cs1 cs2 ->
    type_environment E ->
    subtype E (typ_or cs1 T1 cs2 T2) (typ_or cs1 T1' cs2 T2') cs.
Proof.
  introv Hs1 Hs2 Hd Heq He.
  destruct Hs1.
  destruct Hs2.
  apply subtype_c.
  apply type_equal_post_step
    with (typ_or cs0 (typ_meet T1 T0) cs1 (typ_meet T2 T3));
    eauto using type_equal_or with kinding.
Qed.

Lemma subtype_meet : forall E T1 T1' T2 T2' cs,
    subtype E T1 T1' cs ->
    subtype E T2 T2' cs ->
    type_environment E ->
    subtype E (typ_meet T1 T2) (typ_meet T1' T2') cs.
Proof.
  introv Hs1 Hs2 He.
  destruct Hs1.
  destruct Hs2.
  apply subtype_c.
  apply type_equal_transitive
    with (typ_meet (typ_meet T1 T0) (typ_meet T2 T3));
    auto using type_equal_meet.
  apply type_equal_step
    with (T2 := typ_meet (typ_meet (typ_meet T1 T0) T2) T3);
    auto with kinding.
  apply type_equal_step
    with (T2 := typ_meet (typ_meet (typ_meet T0 T1) T2) T3);
    auto 6 with kinding.
  apply type_equal_step
    with (T2 := typ_meet (typ_meet T0 (typ_meet T1 T2)) T3);
    auto with kinding.
  apply type_equal_step
    with (T2 := typ_meet (typ_meet (typ_meet T1 T2) T0) T3);
    auto 6 with kinding.
  apply type_equal_single; auto with kinding.
Qed.

Lemma subtype_join : forall E T1 T1' T2 T2' cs,
    subtype E T1 T1' cs ->
    subtype E T2 T2' cs ->
    type_environment E ->
    subtype E (typ_join T1 T2) (typ_join T1' T2') cs.
Proof.
  introv Hs1 Hs2 He.
  destruct Hs1.
  destruct Hs2.
  apply subtype_c.
  apply type_equal_transitive
    with (typ_join (typ_meet T1 T0) (typ_meet T2 T3));
    auto using type_equal_join.
  apply type_equal_step
    with (typ_join (typ_meet T1 (typ_meet T0 (typ_join T0 T3)))
            (typ_meet T2 T3)); auto 6 with kinding.
  apply type_equal_step
    with (typ_join (typ_meet (typ_meet T1 T0) (typ_join T0 T3))
            (typ_meet T2 T3)); auto 6 with kinding.
  apply type_equal_step
    with (typ_join (typ_meet (typ_meet T1 T0) (typ_join T0 T3))
           (typ_meet T2 (typ_meet T3 (typ_join T3 T0))));
    auto 6 with kinding.
  apply type_equal_step
    with (typ_join (typ_meet (typ_meet T1 T0) (typ_join T0 T3))
            (typ_meet (typ_meet T2 T3) (typ_join T3 T0)));
    auto 6 with kinding.
  apply type_equal_step
    with (typ_join (typ_meet (typ_meet T1 T0) (typ_join T0 T3))
            (typ_meet (typ_meet T2 T3) (typ_join T0 T3)));
    auto 6 with kinding.
  apply type_equal_step
    with (typ_join (typ_meet (typ_join T0 T3) (typ_meet T1 T0))
            (typ_meet (typ_meet T2 T3) (typ_join T0 T3)));
    auto 6 with kinding.
  apply type_equal_step
    with (typ_join (typ_meet (typ_join T0 T3) (typ_meet T1 T0))
            (typ_meet (typ_join T0 T3) (typ_meet T2 T3)));
    auto 6 with kinding.
  apply type_equal_transitive
    with (typ_join (typ_meet (typ_join T0 T3) T1)
            (typ_meet (typ_join T0 T3) T2));
    auto using type_equal_join, type_equal_meet,
      type_equal_symmetric with kinding.
  apply type_equal_step
    with (typ_meet (typ_join T0 T3) (typ_join T1 T2));
    auto with kinding.
  apply type_equal_single; auto with kinding.
Qed.

(* ****************************************************** *)
(** Projection on top and bottom *)

Lemma type_equal_proj_bot : forall E cs1 cs2,
    CSet.Subset cs2 cs1 ->
    CSet.Nonempty cs2 ->
    type_environment E ->
    type_equal E
      (typ_proj cs1 (typ_bot cs1) cs2) (typ_bot cs2) (knd_row cs2).
Proof.
  introv Hs Hn He.
  remember (CSet.is_empty (CSet.diff cs1 cs2)) as emp.
  destruct emp.
  - symmetry in Heqemp.
    rewrite CSet.is_empty_spec1 in Heqemp.
    assert (CSet.Equal cs1 cs2) as Heq by csetdec.
    apply CSet.eq_leibniz in Heq; subst.
    apply type_equal_single; auto.
  - symmetry in Heqemp.
    rewrite CSet.is_empty_spec2 in Heqemp.
    assert (kinding E
              (typ_proj cs1
                 (typ_or cs2 (typ_bot cs2)
                    (CSet.diff cs1 cs2)
                    (typ_bot (CSet.diff cs1 cs2))) cs2)
              (knd_row cs2))
      by (apply kinding_proj with (cs1 := cs1);
          auto with csetdec;
          apply kinding_or
            with (cs1 := cs2) (cs2 := CSet.diff cs1 cs2);
          auto with csetdec).
    apply type_equal_step
      with (typ_proj cs1
              (typ_or cs2 (typ_bot cs2)
                (CSet.diff cs1 cs2)
                (typ_bot (CSet.diff cs1 cs2))) cs2);
      auto with csetdec.
    apply type_equal_step
      with (T2 := typ_proj cs2 (typ_bot cs2) cs2);
      auto 6 with csetdec.
    apply type_equal_single; auto.
Qed.

Lemma type_equal_proj_top : forall E cs1 cs2,
    CSet.Subset cs2 cs1 ->
    CSet.Nonempty cs2 ->
    type_environment E ->
    type_equal E
      (typ_proj cs1 (typ_top cs1) cs2) (typ_top cs2) (knd_row cs2).
Proof.
  introv Hs Hn He.
  remember (CSet.is_empty (CSet.diff cs1 cs2)) as emp.
  destruct emp.
  - symmetry in Heqemp.
    rewrite CSet.is_empty_spec1 in Heqemp.
    assert (CSet.Equal cs1 cs2) as Heq by csetdec.
    apply CSet.eq_leibniz in Heq; subst.
    apply type_equal_single; auto.
  - symmetry in Heqemp.
    rewrite CSet.is_empty_spec2 in Heqemp.
    assert (kinding E
              (typ_proj cs1
                 (typ_or cs2 (typ_top cs2)
                         (CSet.diff cs1 cs2)
                         (typ_top (CSet.diff cs1 cs2))) cs2)
              (knd_row cs2))
      by (apply kinding_proj with (cs1 := cs1);
          auto with csetdec;
          apply kinding_or
            with (cs1 := cs2) (cs2 := CSet.diff cs1 cs2);
          auto with csetdec).
    apply type_equal_step
      with (typ_proj cs1
              (typ_or cs2 (typ_top cs2)
                 (CSet.diff cs1 cs2)
                 (typ_top (CSet.diff cs1 cs2))) cs2);
      auto with csetdec.
    apply type_equal_step with (typ_proj cs2 (typ_top cs2) cs2);
      auto with csetdec.
    apply type_equal_single; auto.
Qed.

(* *************************************************************** *)
(** Subtyping of projections can be restricted to a subset *)

Lemma subtype_proj_subset : forall E T1 T2 cs1 cs2 cs3 cs4,
    subtype E (typ_proj cs1 T1 cs3) (typ_proj cs2 T2 cs3) cs3 ->
    CSet.Subset cs4 cs3 ->
    CSet.Nonempty cs4 ->
    type_environment E ->
    subtype E (typ_proj cs1 T1 cs4) (typ_proj cs2 T2 cs4) cs4.
Proof.
  introv Hs Hsb Hn He.
  assert (kinding E (typ_proj cs1 T1 cs3) (knd_row cs3)) as Hk1
    by auto with kinding.
  assert (kinding E (typ_proj cs2 T2 cs3) (knd_row cs3)) as Hk2
    by auto with kinding.
  inversion Hk1; inversion Hk2; subst.
  apply subtype_proj with (cs2 := cs4) in Hs; auto.
  apply subtype_reflexive_step
    with (typ_proj cs3 (typ_proj cs1 T1 cs3) cs4); auto.
  apply subtype_transitive
    with (T2 := typ_proj cs3 (typ_proj cs2 T2 cs3) cs4); eauto.
  apply subtype_reflexive_single; auto. 
Qed.

Lemma subtype_proj_subset_bottom : forall E T cs1 cs2 cs3,
    subtype E (typ_proj cs1 T cs2) (typ_bot cs2) cs2 ->
    CSet.Subset cs3 cs2 ->
    CSet.Nonempty cs3 ->
    type_environment E ->
    subtype E (typ_proj cs1 T cs3) (typ_bot cs3) cs3.
Proof.
  introv Hs Hsb Hn He.
  assert (kinding E (typ_proj cs1 T cs2) (knd_row cs2)) as Hk
    by auto with kinding.
  inversion Hk; subst.
  apply subtype_transitive
    with (typ_proj cs1 (typ_bot cs1) cs3);
    auto using subtype_reflexive, type_equal_proj_bot with csetdec.
  apply subtype_proj_subset with cs2; auto with csetdec.
  apply subtype_transitive with (typ_bot cs2); auto. 
  auto using subtype_reflexive,
    type_equal_symmetric, type_equal_proj_bot.
Qed.  

(* *************************************************************** *)
(** Subtyping preserves the argument type of constructors *)

Inductive preserves : tenv -> nat -> typ -> typ -> Prop :=
  | preserves_top : forall E c T cs,
      CSet.In c cs ->
      preserves E c T (typ_top cs)
  | preserves_constructor : forall E c T1 T2,
      type_equal E T1 T2 knd_type ->
      preserves E c T1 (typ_constructor c T2)
  | preserves_or_l : forall E c T1 cs2 T2 cs3 T3,
      preserves E c T1 T2 ->
      preserves E c T1 (typ_or cs2 T2 cs3 T3)
  | preserves_or_r : forall E c T1 cs2 T2 cs3 T3,
      preserves E c T1 T3 ->
      preserves E c T1 (typ_or cs2 T2 cs3 T3)
  | preserves_proj : forall E c T1 T2 cs1 cs2,
      preserves E c T1 T2 ->
      CSet.In c cs2 ->
      preserves E c T1 (typ_proj cs1 T2 cs2)
  | preserves_meet : forall E c T1 T2 T3,
      preserves E c T1 T2 ->
      preserves E c T1 T3 ->
      preserves E c T1 (typ_meet T2 T3)
  | preserves_join_l : forall E c T1 T2 T3,
      preserves E c T1 T2 ->
      preserves E c T1 (typ_join T2 T3)
  | preserves_join_r : forall E c T1 T2 T3,
      preserves E c T1 T3 ->
      preserves E c T1 (typ_join T2 T3).

Hint Constructors preserves.

Lemma in_preserves : forall E c T1 T2 cs,
    preserves E c T1 T2 ->
    kinding E T2 (knd_row cs) ->
    CSet.In c cs.
Proof.
  introv Hp Hk.
  generalize dependent cs.
  induction Hp; introv Hk; inversion Hk;
    subst; auto with csetdec.
  - assert (CSet.In c cs2) by auto.
    auto with csetdec.
  - assert (CSet.In c cs3) by auto.
    auto with csetdec.
Qed.

Ltac invert_preserves :=
  repeat match goal with
  | H : preserves _ _ _ (typ_constructor _ _) |- _ =>
    inversion H; clear H
  | H : preserves _ _ _ (typ_or _ _ _ _) |- _ =>
    inversion H; clear H
  | H : preserves _ _ _ (typ_proj _ _ _) |- _ =>
    inversion H; clear H
  | H : preserves _ _ _ (typ_variant _) |- _ =>
    inversion H; clear H
  | H : preserves _ _ _ (typ_arrow _ _) |- _ =>
    inversion H; clear H
  | H : preserves _ _ _ (typ_ref _) |- _ =>
    inversion H; clear H
  | H : preserves _ _ _ (typ_prod _ _) |- _ =>
    inversion H; clear H
  | H : preserves _ _ _ (typ_top _) |- _ =>
    inversion H; clear H
  | H : preserves _ _ _ (typ_bot _) |- _ =>
    inversion H; clear H
  | H : preserves _ _ _ (typ_meet _ _) |- _ =>
    inversion H; clear H
  | H : preserves _ _ _ (typ_join _ _) |- _ =>
    inversion H; clear H
  end.

Ltac invert_kinding :=
  repeat match goal with
  | H : kinding _ (typ_constructor _ _) (knd_row _) |- _ =>
    inversion H; clear H
  | H : kinding _ (typ_or _ _ _ _) (knd_row _) |- _ =>
    inversion H; clear H
  | H : kinding _ (typ_meet _ _) (knd_row _) |- _ =>
    inversion H; clear H
  | H : kinding _ (typ_join _ _) (knd_row _) |- _ =>
    inversion H; clear H
  | H : kinding _ (typ_proj _ _ _) (knd_row _) |- _ =>
    inversion H; clear H
  | H : kinding _ (typ_top _) (knd_row _) |- _ =>
    inversion H; clear H
  end.

Ltac in_preserves :=
  repeat match goal with
  | H1 : preserves _ ?c _ ?T2,
      H2 : kinding _ ?T2 (knd_row ?cs) |- _ =>
    assert (CSet.In c cs) by eauto using in_preserves;
    clear H2
  end.

Lemma type_equal_core_preserves_l : forall E c T1 T2 T3 cs,
    preserves E c T1 T2 ->
    type_equal_core E T2 T3 (knd_row cs) ->
    type_environment E ->
    preserves E c T1 T3.
Proof.
  introv Hp Hte He.
  induction Hte;
    inversion Hp; subst; clear Hp; invert_preserves;
      in_preserves; subst; auto with csetdec.
  - assert (not (CSet.In c cs2)) by csetdec.
    contradiction.
  - assert (not (CSet.In c cs1)) by csetdec.
    contradiction.
Qed.

Lemma type_equal_core_preserves_r : forall E c T1 T2 T3 cs,
    preserves E c T1 T2 ->
    type_equal_core E T3 T2 (knd_row cs) ->
    type_environment E ->
    preserves E c T1 T3.
Proof.
  introv Hp Hte He.
  induction Hte;
    inversion Hp; subst; clear Hp;
      invert_preserves; invert_kinding;
        in_preserves; subst; auto with csetdec.
  - destruct (CSet.In_dec c cs1); auto.
    assert (CSet.In c cs2) by csetdec; auto.
  - assert (not (CSet.In c cs2)) by csetdec.
    contradiction.
  - assert (not (CSet.In c cs2)) by csetdec.
    contradiction.
  - destruct (CSet.In_dec c cs2); auto.
    assert (CSet.In c cs3); auto with csetdec.
Qed.

Lemma type_equal_symm_preserves : forall E c T1 T2 T3 cs,
    preserves E c T1 T2 ->
    type_equal_symm E T2 T3 (knd_row cs) ->
    type_environment E ->
    preserves E c T1 T3.
Proof.
  introv Hp Hte He.
  remember (knd_row cs) as K.
  destruct Hte; subst.
  - eauto using type_equal_core_preserves_l.
  - eauto using type_equal_core_preserves_r.
Qed.    

Lemma type_equal_cong_preserves : forall E c T1 T2 T3 cs,
    preserves E c T1 T2 ->
    type_equal_cong E T2 T3 (knd_row cs) ->
    type_environment E ->
    preserves E c T1 T3.
Proof.
  introv Hp Hte He.
  remember (knd_row cs) as K.
  generalize dependent cs.
  induction Hte; introv Heq; invert_preserves; subst; eauto.
  - eauto using type_equal_post_step.
  - eauto using type_equal_symm_preserves.
Qed.

Lemma type_equal_preserves : forall E c T1 T2 T3 cs,
    preserves E c T1 T2 ->
    type_equal E T2 T3 (knd_row cs) ->
    type_environment E ->
    preserves E c T1 T3.
Proof.
  introv Hp Hte He.
  remember (knd_row cs) as K.
  induction Hte; subst;
    eauto using type_equal_cong_preserves.
Qed.

Lemma subtype_preserves : forall E c T1 T2 T3 cs,
    preserves E c T1 T2 ->
    subtype E T2 T3 cs ->
    type_environment E ->
    preserves E c T1 T3.
Proof.
  introv Hp Hs He.
  destruct Hs.
  apply type_equal_preserves with (c := c) (T1 := T1) in H; auto.
  inversion H; subst; auto.
Qed.

Lemma subtype_preserves_constructor : forall E T1 T2 c,
    subtype E
      (typ_constructor c T1) (typ_constructor c T2)
      (CSet.singleton c) ->
    type_environment E ->
    type_equal E T1 T2 knd_type.
Proof.
  introv Hs He.
  assert (kinding E (typ_constructor c T1)
           (knd_row (CSet.singleton c))) as Hk
      by auto with kinding.
  inversion Hk; subst.
  assert (preserves E c T1 (typ_constructor c T1)) by auto.
  assert (preserves E c T1 (typ_constructor c T2)) as Hp
    by eauto using subtype_preserves.
  inversion Hp; subst; try solve [exfalso; auto]; auto.
Qed.

Lemma no_subtype_constructor_bot : forall E T c,
    subtype E
      (typ_constructor c T) (typ_bot (CSet.singleton c))
      (CSet.singleton c) ->
    type_environment E ->
    False.
Proof.
  introv Hs He.
  assert (kinding E (typ_constructor c T)
            (knd_row (CSet.singleton c))) as Hk
      by auto with kinding.
  inversion Hk; subst.
  assert (preserves E c T (typ_constructor c T)) by auto.
  assert (preserves E c T (typ_bot (CSet.singleton c))) as Hp
    by eauto using subtype_preserves.
  inversion Hp.
Qed.

(* *************************************************************** *)
(** No interesting equalities at kinds other than knd_row *)

Lemma type_equal_symm_inv_type : forall E T1 T2,
    type_equal_symm E T1 T2 knd_type ->
    False.
Proof.
  introv Hte.
  inversion Hte; subst.
  - assert (type_equal_core E T1 T2 knd_type) as Hte2 by assumption.
    inversion Hte2.
  - assert (type_equal_core E T2 T1 knd_type) as Hte2 by assumption.
    inversion Hte2.
Qed.

Lemma type_equal_symm_inv_range : forall E T1 T2,
    type_equal_symm E T1 T2 knd_range ->
    False.
Proof.
  introv Hte.
  inversion Hte; subst.
  - assert (type_equal_core E T1 T2 knd_range) as Hte2 by assumption.
    inversion Hte2.
  - assert (type_equal_core E T2 T1 knd_range) as Hte2 by assumption.
    inversion Hte2.
Qed.