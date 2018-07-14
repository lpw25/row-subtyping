(************************************************
 *          Row Subtyping - Subtyping           *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import Arith LibLN.
Require Import Cofinite Definitions Substitution Wellformedness Kinding.

(* *************************************************************** *)
(** Type equality in an equivalence *)

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
  apply validated_type_equal in Hte1.
  apply validated_type_equal in Hte2.
  eauto using type_equal_validated_transitive.
Qed.

Lemma type_equal_symmetric : forall E T1 T2 K,
    type_equal E T1 T2 K ->
    type_equal E T2 T1 K.
Proof.
  introv Hte.
  apply validated_type_equal in Hte.
  eauto using type_equal_validated_symmetric.
Qed.

Lemma type_equal_cong_symmetric : forall E T1 T2 K,
    type_equal_cong E T1 T2 K ->
    type_equal_cong E T2 T1 K.
Proof.
  introv Hte.
  apply validated_type_equal_cong in Hte.
  eauto using type_equal_cong_validated_symmetric.
Qed.

(* *************************************************************** *)
(** Convenient lemmas for single-step equality proofs *)

Lemma type_equal_single : forall E T1 T2 K,
    type_equal_cong E T1 T2 K ->
    type_equal E T1 T2 K.
Proof.
  introv Hte.
  eauto with type_equal_cong_validated.
Qed.

Lemma type_equal_post_step : forall E T1 T2 T3 K,
    type_equal E T1 T2 K ->
    type_equal_cong E T2 T3 K ->
    type_equal E T1 T3 K.
Proof.
  introv Hte1 Hte2.
  eauto using type_equal_transitive, type_equal_single.
Qed.

(* *************************************************************** *)
(** Idempotence of join and meet *)

Lemma type_equal_join_idempotent : forall E T cs,
    kinding E T (knd_row cs) ->
    type_equal E T (typ_join T T) (knd_row cs).
Proof.
  introv Hk.
  apply type_equal_step
    with (T2 := typ_join T (typ_meet T (typ_top cs)));
    auto with kinding_validated kinding_regular.
  apply type_equal_step with (T2 := typ_join T T); auto.
Qed.    

Lemma type_equal_meet_idempotent : forall E T cs,
    kinding E T (knd_row cs) ->
    type_equal E T (typ_meet T T) (knd_row cs).
Proof.
  introv Hte.
  apply validated_kinding in Hte.
  eauto using type_equal_validated_meet_idempotent.
Qed.

(* *************************************************************** *)
(** Projection on top and bottom *)

Lemma type_equal_proj_bot : forall E cs1 cs2,
    valid_env E ->
    CSet.Subset cs2 cs1 ->
    CSet.Nonempty cs2 ->
    type_equal E
      (typ_proj cs1 (typ_bot cs1) cs2) (typ_bot cs2) (knd_row cs2).
Proof.
  introv Hv Hs Hn.
  remember (CSet.is_empty (CSet.diff cs1 cs2)) as emp.
  destruct emp.
  - symmetry in Heqemp.
    rewrite CSet.is_empty_spec1 in Heqemp.
    assert (CSet.Equal cs1 cs2) as Heq by csetdec.
    apply CSet.eq_leibniz in Heq; subst.
    apply type_equal_single; auto.
  - symmetry in Heqemp.
    rewrite CSet.is_empty_spec2 in Heqemp.
    apply type_equal_step
      with (T2 :=
              typ_proj
                cs1 (typ_or cs2 (typ_bot cs2)
                (CSet.diff cs1 cs2) (typ_bot (CSet.diff cs1 cs2)))
                cs2);
      auto with csetdec.
    apply type_equal_step
      with (T2 := typ_proj cs2 (typ_bot cs2) cs2);
      auto with csetdec.
    apply type_equal_single; auto.
Qed.

Lemma type_equal_proj_top : forall E cs1 cs2,
    valid_env E ->
    CSet.Subset cs2 cs1 ->
    CSet.Nonempty cs2 ->
    type_equal E
      (typ_proj cs1 (typ_top cs1) cs2) (typ_top cs2) (knd_row cs2).
Proof.
  introv Hv Hs Hn.
  remember (CSet.is_empty (CSet.diff cs1 cs2)) as emp.
  destruct emp.
  - symmetry in Heqemp.
    rewrite CSet.is_empty_spec1 in Heqemp.
    assert (CSet.Equal cs1 cs2) as Heq by csetdec.
    apply CSet.eq_leibniz in Heq; subst.
    apply type_equal_single; auto.
  - symmetry in Heqemp.
    rewrite CSet.is_empty_spec2 in Heqemp.
    apply type_equal_step
      with (T2 :=
              typ_proj
                cs1 (typ_or cs2 (typ_top cs2)
                (CSet.diff cs1 cs2) (typ_top (CSet.diff cs1 cs2)))
                cs2);
      auto with csetdec.
    apply type_equal_step
      with (T2 := typ_proj cs2 (typ_top cs2) cs2);
      auto with csetdec.
    apply type_equal_single; auto.
Qed.

(* *************************************************************** *)
(** Subtyping is a partial order *)

Lemma subtype_refl : forall E T cs,
    kinding E T (knd_row cs) ->
    subtype E T T cs.
Proof.
  introv Hk.
  apply validated_kinding in Hk.
  eauto using subtype_validated_refl.
Qed.

Lemma subtype_reflexive : forall E T1 T2 cs,
    type_equal E T1 T2 (knd_row cs) ->
    subtype E T1 T2 cs.
Proof.
  introv Hte.
  apply validated_type_equal in Hte.
  eauto using subtype_validated_reflexive.
Qed.
     
Lemma subtype_transitive : forall E T1 T2 T3 cs,
    subtype E T1 T2 cs ->
    subtype E T2 T3 cs ->
    subtype E T1 T3 cs.
Proof.
  introv Hs1 Hs2.
  apply validated_subtype in Hs1.
  apply validated_subtype in Hs2.
  eauto using subtype_validated_transitive.
Qed.

Lemma subtype_antisymmetric : forall E T1 T2 cs,
    subtype E T1 T2 cs ->
    subtype E T2 T1 cs ->
    type_equal E T1 T2 (knd_row cs).
Proof.
  introv Hs1 Hs2.
  apply validated_subtype in Hs1.
  apply validated_subtype in Hs2.
  eauto using subtype_validated_antisymmetric.
Qed.

(* *************************************************************** *)
(** Congruence of type equality *)

Lemma type_equal_range_subsumption : forall E T1 T2 T3 T4 T3' T4',
    type_equal E T1 T2 (knd_range T3 T4) ->
    subtype E T3 T3' CSet.universe ->
    subtype E T4' T4 CSet.universe ->
    type_equal E T1 T2 (knd_range T3' T4').
Proof.
  introv Hte Hs1 Hs2.
  remember (knd_range T3 T4) as K.
  induction Hte; subst.
  - eauto.
  - assert (type_equal_cong E T1 T2 (knd_range T3 T4))
      as Hec by assumption.
    inversion Hec; subst.
    assert (type_equal_symm E T1 T2 (knd_range T3 T4))
      as Hes by assumption.
    inversion Hes; subst.
    + assert (type_equal_core E T1 T2 (knd_range T3 T4))
        as Her by assumption.
      inversion Her; subst.
    + assert (type_equal_core E T2 T1 (knd_range T3 T4))
        as Her by assumption.
      inversion Her; subst.
Qed.

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
    type_equal E
      (typ_proj cs1 T1 cs2) (typ_proj cs1 T1' cs2)
      (knd_row cs2).
Proof.
  introv Hte Hs Hn.
  remember (knd_row cs1) as K.
  induction Hte; subst; eauto.
Qed.

Lemma type_equal_variant : forall E T1 T1',
    type_equal E T1 T1'
      (knd_range (typ_top CSet.universe) (typ_bot CSet.universe)) ->
    type_equal E (typ_variant T1) (typ_variant T1') knd_type.
Proof.
  introv Hte.
  remember
    (knd_range (typ_top CSet.universe) (typ_bot CSet.universe)) as K.
  induction Hte; subst.
  - eauto.  
  - assert
      (type_equal_cong E T1 T2
        (knd_range (typ_top CSet.universe) (typ_bot CSet.universe)))
      as Hec by assumption.
    inversion Hec; subst.
    assert
      (type_equal_symm E T1 T2
        (knd_range (typ_top CSet.universe) (typ_bot CSet.universe)))
      as Hes by assumption.
    inversion Hes; subst.
    + assert
        (type_equal_core E T1 T2
          (knd_range (typ_top CSet.universe) (typ_bot CSet.universe)))
        as Her by assumption.
      inversion Her.
    + assert
        (type_equal_core E T2 T1
          (knd_range (typ_top CSet.universe) (typ_bot CSet.universe)))
        as Her by assumption.
      inversion Her.
Qed.
 
Lemma type_equal_or : forall E T1 T1' T2 T2' cs1 cs2 cs,
    type_equal E T1 T1' (knd_row cs1) ->
    type_equal E T2 T2' (knd_row cs2) ->
    CSet.Disjoint cs1 cs2 ->
    cs = CSet.union cs1 cs2 ->
    type_equal E
      (typ_or cs1 T1 cs2 T2) (typ_or cs1 T1' cs2 T2') (knd_row cs).
Proof.
  introv Hte1 Hte2 Hd Heq.
  apply type_equal_transitive with (typ_or cs1 T1' cs2 T2).
  - remember (knd_row cs1) as K.
    induction Hte1; subst;
      eauto with type_equal_validated.
  - remember (knd_row cs2) as K.
    induction Hte2; subst;
      eauto with type_equal_validated.
Qed.

Lemma type_equal_arrow : forall E T1 T1' T2 T2',
    type_equal E T1 T1' knd_type ->
    type_equal E T2 T2' knd_type ->
    type_equal E (typ_arrow T1 T2) (typ_arrow T1' T2') knd_type.
Proof.
  introv Hte1 Hte2.
  remember knd_type as K.
  apply type_equal_transitive with (typ_arrow T1' T2).
  - induction Hte1; subst; eauto with type_equal_validated.
  - induction Hte2; subst; eauto with type_equal_validated.
Qed.

Lemma type_equal_meet : forall E T1 T1' T2 T2' cs,
    type_equal E T1 T1' (knd_row cs) ->
    type_equal E T2 T2' (knd_row cs) ->
    type_equal E (typ_meet T1 T2) (typ_meet T1' T2') (knd_row cs).
Proof.
  introv Hte1 Hte2.
  remember (knd_row cs) as K.
  apply type_equal_transitive with (typ_meet T1' T2).
  - induction Hte1; subst; eauto with type_equal_validated.
  - induction Hte2; subst; eauto with type_equal_validated.
Qed.

Lemma type_equal_join : forall E T1 T1' T2 T2' cs,
    type_equal E T1 T1' (knd_row cs) ->
    type_equal E T2 T2' (knd_row cs) ->
    type_equal E (typ_join T1 T2) (typ_join T1' T2') (knd_row cs).
Proof.
  introv Hte1 Hte2.
  remember (knd_row cs) as K.
  apply type_equal_transitive with (typ_join T1' T2).
  - induction Hte1; subst; eauto with type_equal_validated.
  - induction Hte2; subst; eauto with type_equal_validated.
Qed.

(* *************************************************************** *)
(** Congruence of subtyping *)

Lemma subtype_proj : forall E T1 T1' cs1 cs2,
    subtype E T1 T1' cs1 ->
    CSet.Subset cs2 cs1 ->
    CSet.Nonempty cs2 ->
    subtype E (typ_proj cs1 T1 cs2) (typ_proj cs1 T1' cs2) cs2.
Proof.
  introv Hs Hsb Hn.
  remember Hs as Hs'.
  destruct Hs.
  apply subtype_c.
  apply type_equal_post_step
    with (T2 := typ_proj cs (typ_meet T1 T2) cs2);
    auto using type_equal_proj with subtype_validated.
Qed.

Lemma subtype_or : forall E T1 T1' T2 T2' cs1 cs2 cs,
    subtype E T1 T1' cs1 ->
    subtype E T2 T2' cs2 ->
    CSet.Disjoint cs1 cs2 ->
    cs = CSet.union cs1 cs2 ->
    subtype E (typ_or cs1 T1 cs2 T2) (typ_or cs1 T1' cs2 T2') cs.
Proof.
  introv Hs1 Hs2 Hd Heq.
  remember Hs1 as Hs1'.
  destruct Hs1.
  remember Hs2 as Hs2'.
  destruct Hs2.
  apply subtype_c.
  apply type_equal_post_step
    with (T2 := typ_or cs0 (typ_meet T1 T0) cs1 (typ_meet T2 T3));
    auto using type_equal_or with subtype_validated.
Qed.

Lemma subtype_meet : forall E T1 T1' T2 T2' cs,
    subtype E T1 T1' cs ->
    subtype E T2 T2' cs ->
    subtype E (typ_meet T1 T2) (typ_meet T1' T2') cs.
Proof.
  introv Hs1 Hs2.
  remember Hs1 as Hs1'.
  destruct Hs1.
  remember Hs2 as Hs2'.
  destruct Hs2.
  apply subtype_c.
  apply type_equal_transitive
    with (T2 := typ_meet (typ_meet T1 T0) (typ_meet T2 T3));
    auto using type_equal_meet.
  apply type_equal_step
    with (T2 := typ_meet (typ_meet (typ_meet T1 T0) T2) T3);
    auto with subtype_validated.
  apply type_equal_step
    with (T2 := typ_meet (typ_meet (typ_meet T0 T1) T2) T3);
    auto 6 with subtype_validated.
  apply type_equal_step
    with (T2 := typ_meet (typ_meet T0 (typ_meet T1 T2)) T3);
    auto with subtype_validated.
  apply type_equal_step
    with (T2 := typ_meet (typ_meet (typ_meet T1 T2) T0) T3);
    auto 6 with subtype_validated.
  apply type_equal_single; auto with subtype_validated.
Qed.

Lemma subtype_join : forall E T1 T1' T2 T2' cs,
    subtype E T1 T1' cs ->
    subtype E T2 T2' cs ->
    subtype E (typ_join T1 T2) (typ_join T1' T2') cs.
Proof.
  introv Hs1 Hs2.
  remember Hs1 as Hs1'.
  destruct Hs1.
  remember Hs2 as Hs2'.
  destruct Hs2.
  apply subtype_c.
  apply type_equal_transitive
    with (T2 := typ_join (typ_meet T1 T0) (typ_meet T2 T3));
    auto using type_equal_join.
  apply type_equal_step
    with (T2 := typ_join (typ_meet T1 (typ_meet T0 (typ_join T0 T3)))
                         (typ_meet T2 T3));
    auto 6 with subtype_validated.
  apply type_equal_step
    with (T2 := typ_join (typ_meet (typ_meet T1 T0) (typ_join T0 T3))
                         (typ_meet T2 T3));
    auto 6 with subtype_validated.
  apply type_equal_step
    with (T2 := typ_join (typ_meet (typ_meet T1 T0) (typ_join T0 T3))
                  (typ_meet T2 (typ_meet T3 (typ_join T3 T0))));
    auto 6 with subtype_validated.
  apply type_equal_step
    with (T2 := typ_join (typ_meet (typ_meet T1 T0) (typ_join T0 T3))
                  (typ_meet (typ_meet T2 T3) (typ_join T3 T0)));
    auto 6 with subtype_validated.
  apply type_equal_step
    with (T2 := typ_join (typ_meet (typ_meet T1 T0) (typ_join T0 T3))
                  (typ_meet (typ_meet T2 T3) (typ_join T0 T3)));
    auto 6 with subtype_validated.
  apply type_equal_step
    with (T2 := typ_join (typ_meet (typ_join T0 T3) (typ_meet T1 T0))
                  (typ_meet (typ_meet T2 T3) (typ_join T0 T3)));
    auto 6 with subtype_validated.
  apply type_equal_step
    with (T2 := typ_join (typ_meet (typ_join T0 T3) (typ_meet T1 T0))
                  (typ_meet (typ_join T0 T3) (typ_meet T2 T3)));
    auto 6 with subtype_validated.
  apply type_equal_transitive
    with (T2 := typ_join (typ_meet (typ_join T0 T3) T1)
                         (typ_meet (typ_join T0 T3) T2));
    auto using type_equal_join, type_equal_meet, type_equal_symmetric
      with subtype_validated.
  apply type_equal_step
    with (T2 := typ_meet (typ_join T0 T3) (typ_join T1 T2));
    auto 6 with subtype_validated.
  apply type_equal_single;
    auto with subtype_validated.
Qed.

(* *************************************************************** *)
(** Typing lattice is bounded *)

Lemma subtype_top : forall E T cs,
    kinding E T (knd_row cs) ->
    subtype E T (typ_top cs) cs.
Proof.
  introv Hk.
  apply validated_kinding in Hk.
  auto using subtype_validated_top.
Qed.

Lemma subtype_bot : forall E T cs,
    kinding E T (knd_row cs) ->
    subtype E (typ_bot cs) T cs.
Proof.
  introv Hk.
  apply validated_kinding in Hk.
  auto using subtype_validated_bot.
Qed.  

Lemma kinding_range_top_bot : forall E T1 T2 T3,
    kinding E T1 (knd_range T2 T3) ->
    kinding E T1
      (knd_range (typ_top CSet.universe) (typ_bot CSet.universe)).
Proof.
  introv Hk.
  apply validated_kinding in Hk.
  eauto using kinding_validated_range_top_bot.
Qed.  

(* *************************************************************** *)
(** Kinding respects type equality *)
(*
Lemma kinding_type_equal_core_l : forall E T1 T2 K1 K2,
    kinding E T1 K1 ->
    type_equal_core E T1 T2 K2 ->
    kinding E T2 K1.
Proof.
  introv Hk Hte.
  generalize dependent K2.
  generalize dependent T2.
  induction Hk; introv Hte;
    eauto; inversion Hte; subst; auto; auto with csetdec;
    inversion Hk2; subst; auto.
Qed.

Lemma kinding_type_equal_core_r : forall E T1 T2 K1 K2,
    kinding E T1 K1 ->
    type_equal_core E T2 T1 K2 ->
    kinding E T2 K1.
Proof.
  introv Hk Hte.
  generalize dependent K1.
  induction Hte; introv Hk.
  - remember (typ_or cs2 T2 cs1 T1) as T.
    induction Hk; inversion HeqT; subst; eauto with csetdec.
  - remember (typ_or cs12 (typ_or cs1 T1 cs2 T2) cs3 T3) as T.
    induction Hk; inversion HeqT; subst; eauto with csetdec.
  - remember (typ_bot cs12) as T.
    induction Hk; inversion HeqT; subst; eauto.
  - remember (typ_top cs12) as T.
    induction Hk; inversion HeqT; subst; eauto.
  - remember
      (typ_meet (typ_or cs1 T1 cs2 T2) (typ_or cs1 T3 cs2 T4)) as T.
    induction Hk; inversion HeqT; subst; eauto;
      inversion Hk1; inversion Hk2; subst; auto.
  - remember
      (typ_join (typ_or cs1 T1 cs2 T2) (typ_or cs1 T3 cs2 T4)) as T.
    induction Hk; inversion HeqT; subst; eauto;
      inversion Hk1; inversion Hk2; subst; auto.
  - remember (typ_proj cs1 T cs23) as Tk.
    induction Hk; inversion HeqTk; subst; eauto.
  - induction Hk; eauto; inversion H; subst;
      auto with csetdec kinding_regular.
    + assert (bind_knd K = bind_knd (knd_row cs)) as Heq
        by eauto using binds_func.
      inversion Heq; subst.
      auto with csetdec kinding_regular.
    + apply IHHk1.

  induction Hk; introv Hte.
  - inversion Hte; subst.
    + assert (kinding E (typ_fvar X) (knd_row cs)) as Hk2
        by assumption.
      inversion Hk2; subst.
      assert (bind_knd K = bind_knd (knd_row cs)) as Heq
        by eauto using binds_func.
      inversion Heq; subst.
      apply kinding_proj; auto with csetdec kinding_regular.
    + 
Qed.

Lemma kinding_type_equal_cong : forall E T1 T2 K1 K2,
    kinding E T1 K1 ->
    type_equal_cong E T1 T2 K2 ->
    kinding E T2 K1.
Proof.
  introv Hk Hte.
  generalize dependent K1.
  induction Hte; introv Hk.
  - remember (typ_constructor c T1) as T.
    induction Hk; inversion HeqT; subst; eauto.
  - remember (typ_or cs1 T1 cs2 T2) as T.
    induction Hk; inversion HeqT; subst; eauto.
  - remember (typ_or cs1 T1 cs2 T2) as T.
    induction Hk; inversion HeqT; subst; eauto.
  - remember (typ_row T1) as T.
    induction Hk; inversion HeqT; subst; eauto.
    apply kinding_range_subsumption
      with (T1 := T1') (T2 := T1'); auto;
      apply subtype_reflexive; eauto using type_equal_symmetric.
  - remember (typ_variant T1) as T.
    induction Hk; inversion HeqT; subst; eauto.
  - remember (typ_arrow T1 T2) as T.
    induction Hk; inversion HeqT; subst; eauto.
  - remember (typ_arrow T1 T2) as T.
    induction Hk; inversion HeqT; subst; eauto.
  - remember (typ_meet T1 T2) as T.
    induction Hk; inversion HeqT; subst; eauto.
  - remember (typ_meet T1 T2) as T.
    induction Hk; inversion HeqT; subst; eauto.
  - remember (typ_join T1 T2) as T.
    induction Hk; inversion HeqT; subst; eauto.
  - remember (typ_join T1 T2) as T.
    induction Hk; inversion HeqT; subst; eauto.
  - auto.
  - eauto using kinding_type_equal_core.
Qed.

Lemma kinding_type_equal_symm : forall E T1 T2 K1 K2,
    kinding E T1 K1 ->
    type_equal_symm E T1 T2 K2 ->
    kinding E T2 K1.
Proof.
  introv Hk Hte.
  destruct Hte;
    eauto using kinding_type_equal_cong.


Lemma kinding_type_equal : forall E T1 T2 K1 K2,
    kinding E T1 K1 ->
    type_equal E T1 T2 K2 ->
    kinding E T2 K1.
Proof.
  introv Hk Hte.
  induction Hk.
*)  

(* *************************************************************** *)
(** Different ranges for the same type are subtypes *)

Lemma subtype_from_ranges : forall E T1 T2 T3 T4 T5,
    kinding E T1 (knd_range T2 T3) ->
    kinding E T1 (knd_range T4 T5) ->
    subtype E T5 T2 CSet.universe.
Proof.
  introv Hk1 Hk2.
  apply validated_kinding in Hk1.
  remember (knd_range T2 T3) as K.
  generalize dependent T2.
  generalize dependent T3.
  induction Hk1; introv HeqK; inversion HeqK; subst.
  - remember (knd_range T4 T5) as K.
    remember (typ_fvar X) as T.
    generalize dependent T4.
    generalize dependent T5.
    induction Hk2; introv HeqK; inversion HeqK; inversion HeqT; subst.
    + assert
        (bind_knd (knd_range T2 T3) = bind_knd (knd_range T4 T5))
        as Heq by eauto using binds_func.
      inversion Heq; subst.
      assert (valid_kind_validated E (knd_range T4 T5)) as Hv
        by assumption.
      inversion Hv; subst.
      auto.
    + eauto using subtype_transitive.
  - eauto using subtype_transitive.
Qed.

(* *************************************************************** *)
(** Subtyping of projections can be restricted to a subset *)

Lemma subtype_proj_subset : forall E T1 T2 cs1 cs2 cs3,
    subtype E (typ_proj cs1 T1 cs2) (typ_proj cs1 T2 cs2) cs2 ->
    CSet.Subset cs3 cs2 ->
    CSet.Nonempty cs3 ->
    subtype E (typ_proj cs1 T1 cs3) (typ_proj cs1 T2 cs3) cs3.
Proof.
  introv Hs Hsb Hn.
  assert
      (kinding E (typ_proj cs2 (typ_proj cs1 T1 cs2) cs3)
               (knd_row cs3))
      as Hk by auto with subtype_validated.
  inversion Hk; subst.
  assert (kinding E (typ_proj cs1 T1 cs2) (knd_row cs2)) as Hk2
    by assumption.
  inversion Hk2; subst.
  assert
      (kinding E (typ_proj cs2 (typ_proj cs1 T2 cs2) cs3)
               (knd_row cs3))
      as Hk3 by auto with subtype_validated.
  inversion Hk3; subst.
  assert (kinding E (typ_proj cs1 T2 cs2) (knd_row cs2)) as Hk4
    by assumption.
  inversion Hk4; subst.
  apply subtype_proj with (cs2 := cs3) in Hs; auto.
  apply subtype_transitive
    with (T2 := typ_proj cs2 (typ_proj cs1 T1 cs2) cs3);
    auto 6 using subtype_reflexive, type_equal_single.
  apply subtype_transitive
    with (T2 := typ_proj cs2 (typ_proj cs1 T2 cs2) cs3);
    auto 6 using subtype_reflexive, type_equal_single.
Qed.

Lemma subtype_proj_subset_bottom : forall E T cs1 cs2 cs3,
    subtype E (typ_proj cs1 T cs2) (typ_bot cs2) cs2 ->
    CSet.Subset cs3 cs2 ->
    CSet.Nonempty cs3 ->
    subtype E (typ_proj cs1 T cs3) (typ_bot cs3) cs3.
Proof.
  introv Hs Hsb Hn.
  assert
      (kinding E (typ_proj cs2 (typ_proj cs1 T cs2) cs3)
               (knd_row cs3))
      as Hk by auto with subtype_validated.
  inversion Hk; subst.
  assert (kinding E (typ_proj cs1 T cs2) (knd_row cs2)) as Hk2
    by assumption.
  inversion Hk2; subst.
  apply subtype_proj with (cs2 := cs3) in Hs; auto.
  apply subtype_transitive
    with (T2 := typ_proj cs2 (typ_proj cs1 T cs2) cs3);
    auto 6 using subtype_reflexive, type_equal_single.
  apply subtype_transitive
    with (T2 := typ_proj cs2 (typ_bot cs2) cs3); auto.
  apply subtype_reflexive.
  apply type_equal_proj_bot; auto with kinding_validated.
Qed.  

(* *************************************************************** *)
(** Subtyping preserves the argument type of constructors *)

Inductive preserves : env -> nat -> typ -> typ -> Prop :=
  | preserves_top : forall E c T cs,
      preserves E c T (typ_top cs)
  | preserves_equal : forall E c T1 T2,
      type_equal E T1 T2 knd_type ->
      preserves E c T1 (typ_constructor c T2)
  | preserves_other : forall E c1 c2 T1 T2,
      c1 <> c2 ->
      preserves E c1 T1 (typ_constructor c2 T2)
  | preserves_or_l : forall E c T1 T2 T3 cs1 cs2,
      CSet.In c cs1 ->
      preserves E c T1 T2 ->
      preserves E c T1 (typ_or cs1 T2 cs2 T3)
  | preserves_or_r : forall E c T1 T2 T3 cs1 cs2,
      CSet.In c cs2 ->
      preserves E c T1 T3 ->
      preserves E c T1 (typ_or cs1 T2 cs2 T3)
  | preserves_proj : forall E c T1 T2 cs1 cs2,
      preserves E c T1 T2 ->
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

Lemma type_equal_core_preserves_l : forall E c T1 T2 T3 cs,
    preserves E c T1 T2 ->
    type_equal_core E T2 T3 (knd_row cs) ->
    CSet.In c cs ->
    preserves E c T1 T3.
Proof.
  introv Hp Hte Hin.
  remember (knd_row cs) as K.
  induction Hte;
    inversion HeqK; inversion Hp; subst; clear Hp;
      repeat match goal with
      | [ H : preserves _ _ _ (typ_or _ _ _ _) |- _] =>
        inversion H; clear H
      | [ H : preserves _ _ _ (typ_meet _ _) |- _] =>
        inversion H; clear H
      | [ H : preserves _ _ _ (typ_join _ _) |- _] =>
        inversion H; clear H
      | [ H : preserves _ _ _ (typ_proj _ _ _) |- _] =>
        inversion H; clear H
      | [ H : preserves _ _ _ (typ_bot _) |- _] =>
        inversion H; clear H
      end; subst; auto with csetdec.
  - assert (not (CSet.In c cs2)) by csetdec.
    contradiction.
  - assert (not (CSet.In c cs1)) by csetdec.
    contradiction.
Qed.

Lemma type_equal_core_preserves_r : forall E c T1 T2 T3 cs,
    preserves E c T1 T2 ->
    type_equal_core E T3 T2 (knd_row cs) ->
    CSet.In c cs ->
    preserves E c T1 T3.
Proof.
  introv Hp Hte Hin.
  remember (knd_row cs) as K.
  induction Hte;
    inversion HeqK; inversion Hp; subst; clear Hp;
      repeat match goal with
      | [ H : preserves _ _ _ (typ_or _ _ _ _) |- _] =>
        inversion H; clear H
      | [ H : preserves _ _ _ (typ_meet _ _) |- _] =>
        inversion H; clear H
      | [ H : preserves _ _ _ (typ_join _ _) |- _] =>
        inversion H; clear H
      | [ H : preserves _ _ _ (typ_proj _ _ _) |- _] =>
        inversion H; clear H
      | [ H : preserves _ _ _ (typ_bot _) |- _] =>
        inversion H; clear H
      end; subst; auto with csetdec.
  - destruct (CSet.In_dec c cs1); auto.
    assert (CSet.In c cs2) by csetdec.
    auto.
  - assert (not (CSet.In c cs2)) by csetdec.
    contradiction.
  - assert (not (CSet.In c cs2)) by csetdec.
    contradiction.
  - destruct (CSet.In_dec c cs2); auto.
    assert (CSet.In c cs3) by csetdec.
    auto.
Qed.

Lemma type_equal_symm_preserves : forall E c T1 T2 T3 cs,
    preserves E c T1 T2 ->
    type_equal_symm E T2 T3 (knd_row cs) ->
    CSet.In c cs ->
    preserves E c T1 T3.
Proof.
  introv Hp Hte Hin.
  remember (knd_row cs) as K.
  destruct Hte; subst.
  - eauto using type_equal_core_preserves_l.
  - eauto using type_equal_core_preserves_r.
Qed.    

Lemma type_equal_cong_preserves : forall E c T1 T2 T3 cs,
    preserves E c T1 T2 ->
    type_equal_cong E T2 T3 (knd_row cs) ->
    CSet.In c cs ->
    preserves E c T1 T3.
Proof.
  introv Hp Hte Hin.
  remember (knd_row cs) as K.
  generalize dependent cs.
  induction Hte; introv HeqK Hin; inversion HeqK; subst;
    try solve [inversion Hp; subst; eauto].
  - destruct (Nat.eq_dec c c0); subst;
      inversion Hp; subst; eauto using type_equal_post_step.
  - eauto using type_equal_symm_preserves.
Qed.

Lemma type_equal_preserves : forall E c T1 T2 T3 cs,
    preserves E c T1 T2 ->
    type_equal E T2 T3 (knd_row cs) ->
    CSet.In c cs ->
    preserves E c T1 T3.
Proof.
  introv Hp Hte Hin.
  remember (knd_row cs) as K.
  induction Hte; subst;
    eauto using type_equal_cong_preserves.
Qed.

Lemma subtype_preserves : forall E c T1 T2 T3 cs,
    preserves E c T1 T2 ->
    subtype E T2 T3 cs ->
    CSet.In c cs ->
    preserves E c T1 T3.
Proof.
  introv Hp Hs Hin.
  destruct Hs.
  apply type_equal_preserves with (c := c) (T1 := T1) in H; auto.
  inversion H; subst; auto.
Qed.

Lemma subtype_preserves_constructor : forall E T1 T2 c,
    subtype E
      (typ_constructor c T1) (typ_constructor c T2)
      (CSet.singleton c) ->
    type_equal E T1 T2 knd_type.
Proof.
  introv Hs.
  assert
    (kinding E (typ_constructor c T1) (knd_row (CSet.singleton c)))
    as Hk by auto with subtype_validated.
  inversion Hk; subst.
  assert (preserves E c T1 (typ_constructor c T1)) by auto.
  assert (preserves E c T1 (typ_constructor c T2))
    as Hp by eauto using subtype_preserves with csetdec.
  inversion Hp; subst; try solve [exfalso; auto]; auto.
Qed.

Lemma no_subtype_constructor_bot : forall E T c,
    subtype E
      (typ_constructor c T) (typ_bot (CSet.singleton c))
      (CSet.singleton c) ->
    False.
Proof.
  introv Hs.
  assert
    (kinding E (typ_constructor c T) (knd_row (CSet.singleton c)))
    as Hk by auto with subtype_validated.
  inversion Hk; subst.
  assert (preserves E c T (typ_constructor c T)) by auto.
  assert (preserves E c T (typ_bot (CSet.singleton c)))
    as Hp by eauto using subtype_preserves with csetdec.
  inversion Hp.
Qed.