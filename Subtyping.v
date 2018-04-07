(************************************************
 *          Row Subtyping - Subtyping           *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import LibLN Cofinite Definitions Substitution Wellformedness Kinding.

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
(** Congruence *)

Lemma type_equal_range_subsumption : forall E T1 T2 T3 T4 T3' T4',
    type_equal E T1 T2 (knd_range T3 T4) ->
    subtype E T3 T3' CSet.universe ->
    subtype E T4' T4 CSet.universe ->
    type_equal E T1 T2 (knd_range T3' T4').
Proof.
  introv Hte Hs1 Hs2.
  remember (knd_range T3 T4) as K.
  induction Hte; subst; eauto.
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

Lemma type_equal_row : forall E T1 T1',
    type_equal E T1 T1' (knd_row CSet.universe) ->
    type_equal E (typ_row T1) (typ_row T1') (knd_range T1 T1).
Proof.
  introv Hte.
  remember (knd_row CSet.universe) as K.
  induction Hte; subst; auto.
  apply type_equal_step with (T2 := typ_row T2); auto.
  apply type_equal_range_subsumption
    with (T3 := T2) (T4 := T2);
      eauto using subtype_reflexive, type_equal_symmetric,
        type_equal_reflexive
          with type_equal_cong_validated.
Qed.

Lemma type_equal_variant : forall E T1 T1',
    type_equal E T1 T1'
      (knd_range (typ_top CSet.universe) (typ_bot CSet.universe)) ->
    type_equal E (typ_variant T1) (typ_variant T1') knd_type.
Proof.
  introv Hte.
  remember
    (knd_range (typ_top CSet.universe) (typ_bot CSet.universe)) as K.
  induction Hte; subst; eauto.
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
(** Kinding respects type equality on ranges *)
 
Lemma kinding_type_equal_cong_range : forall E T1 T2 T3 T4 T5 T6,
    kinding E T1 (knd_range T3 T4) ->
    type_equal_cong E T1 T2 (knd_range T5 T6) ->
    kinding E T2 (knd_range T3 T4).
Proof.
  introv Hk Hte.
  remember (knd_range T5 T6) as K.
  generalize dependent T5.
  generalize dependent T6.
  induction Hte; introv HeqK; inversion HeqK; subst.
  - clear IHHte HeqK.
    remember (typ_row T6) as T.
    remember (knd_range T3 T4) as K.
    generalize dependent T3.
    generalize dependent T4.
    induction Hk; introv HeqK; inversion HeqT; inversion HeqK;
      subst; subst.
    + apply kinding_range_subsumption
        with (T1 := T1') (T2 := T1');
        eauto using subtype_reflexive, type_equal_symmetric
          with type_equal_cong_validated. 
    + apply kinding_range_subsumption
        with (T1 := T1) (T2 := T2); eauto.
  - eauto.
  - inversion H; subst.
    + inversion H1.
    + inversion H1.
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
