(************************************************
 *          Row Subtyping - Kinding             *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import LibLN Cofinite Definitions Substitution Wellformedness.

Hint Constructors
     valid_kind kinding valid_scheme_vars valid_instance valid_env
     type_equal_core type_equal_symm type_equal_cong type_equal.

(* *************************************************************** *)
(** * Retraction of valid environments *)

Lemma valid_env_retract : forall E F,
    valid_env (E & F) -> valid_env E.
Proof.
  introv He.
  induction F using env_ind;
    autorewrite with rew_env_concat in *; auto.
  remember (E & F & x ~ v) as G.
  destruct He.
  - exfalso. eapply empty_push_inv. eassumption.
  - destruct (eq_push_inv HeqG) as [_ [_ Hem]].
    rewrite Hem in He.
    auto.
  - destruct (eq_push_inv HeqG) as [_ [_ Hem]].
    rewrite Hem in He.
    auto.
Qed.

(* *************************************************************** *)
(** * Convenient inversions of valid environments *)

Lemma valid_env_kind_inv : forall E X K,
    valid_env (E & X ~:: K) ->
    valid_env E /\ X # E /\ valid_kind E K.
Proof.
  introv He.
  remember (E & X ~:: K) as F eqn:Hf.
  destruct He.
  - apply empty_push_inv in Hf; contradiction.
  - destruct (eq_push_inv Hf) as [? [Hk ?]].
    inversion Hk.
    subst.
    auto.
  - destruct (eq_push_inv Hf) as [_ [Hk _]].
    discriminate.
Qed.

Lemma valid_env_type_inv : forall E x M,
    valid_env (E & x ~: M) ->
    valid_env E /\ x # E /\ valid_scheme E M.
Proof.
  introv He.
  remember (E & x ~: M) as F eqn:Hf.
  destruct He.
  - apply empty_push_inv in Hf; contradiction.
  - destruct (eq_push_inv Hf) as [_ [Hm _]].
    discriminate.
  - destruct (eq_push_inv Hf) as [? [Hm ?]].
    inversion Hm.
    subst.
    auto.
Qed.    

(* *************************************************************** *)
(** Weakening *)

Lemma combined_kinding_weakening :
     (forall EG K,
      valid_kind_regular EG K ->
      (forall E F G,
          EG = E & G ->
          valid_env (E & F & G) ->
          valid_kind (E & F & G) K))
  /\ (forall EG T K,
      kinding_regular EG T K ->
      (forall E F G,
          EG = E & G ->
          valid_env (E & F & G) ->
          kinding (E & F & G) T K))
  /\ (forall EG M Xs,
      valid_scheme_vars_regular EG M Xs ->
      (forall E F G,
          fresh (dom F) (sch_arity M) Xs ->
          EG = E & G ->
          valid_env (E & F & G) ->
          valid_scheme_vars (E & F & G) M Xs))
  /\ (forall EG M,
      valid_scheme_regular EG M ->
      (forall E F G,
          EG = E & G ->
          valid_env (E & F & G) ->
          valid_scheme (E & F & G) M))
  /\ (forall E, valid_env_regular E -> valid_env E)
  /\ (forall EG T1 T2 K,
      type_equal_core_regular EG T1 T2 K ->
      (forall E F G,
          EG = E & G ->
          valid_env (E & F & G) ->
          type_equal_core (E & F & G) T1 T2 K))
  /\ (forall EG T1 T2 K,
      type_equal_symm_regular EG T1 T2 K ->
      (forall E F G,
          EG = E & G ->
          valid_env (E & F & G) ->
          type_equal_symm (E & F & G) T1 T2 K))
  /\ (forall EG T1 T2 K,
      type_equal_cong_regular EG T1 T2 K ->
      (forall E F G,
          EG = E & G ->
          valid_env (E & F & G) ->
          type_equal_cong (E & F & G) T1 T2 K))
  /\ (forall EG T1 T2 K,
      type_equal_regular EG T1 T2 K ->
      (forall E F G,
          EG = E & G ->
          valid_env (E & F & G) ->
          type_equal (E & F & G) T1 T2 K))
  /\ (forall EG T1 T2 cs,
      subtype_regular EG T1 T2 cs ->
      (forall E F G,
          EG = E & G ->
          valid_env (E & F & G) ->
          subtype (E & F & G) T1 T2 cs)).
Proof.
  apply combined_kinding_regular_mutind; intros; subst; econstr auto.
  - auto using binds_weakening with valid_env_regular.
  - assert (fresh (dom F) (sch_arity (sch_bind K M)) (X :: Xs)) as Hf
        by assumption.
    destruct Hf.
    apply valid_scheme_vars_bind; auto.
    rewrite <- concat_assoc.
    apply H0;
      autorewrite with rew_sch_arity; rewrite? concat_assoc; auto.
    apply valid_env_kind; auto.
    assert (environment (E0 & G & X ~:: K)) as Henv by assumption.
    destruct (environment_knd_inv Henv).
    auto.
  - apply valid_scheme_c
      with (L := (L \u dom F)); auto.
Qed.

Lemma valid_kind_weakening : forall E F G K,
    valid_kind (E & G) K ->
    valid_env (E & F & G) ->
    valid_kind (E & F & G) K.
Proof.
  introv Hv He.
  apply regular_valid_kind in Hv.
  pose combined_kinding_weakening.
  intuition eauto.
Qed.

Lemma valid_kind_weakening_l : forall E F K,
    valid_kind E K ->
    valid_env (E & F) ->
    valid_kind (E & F) K.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply valid_kind_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma kinding_weakening : forall E F G T K,
   kinding (E & G) T K -> 
   valid_env (E & F & G) ->
   kinding (E & F & G) T K.
Proof.
  introv Hk He.
  apply regular_kinding in Hk.
  pose combined_kinding_weakening.
  intuition eauto.
Qed.

Lemma kinding_weakening_l : forall E F T K,
   kinding E T K -> 
   valid_env (E & F) ->
   kinding (E & F) T K.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply kinding_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma valid_scheme_vars_weakening : forall E F G M Xs,
    fresh (dom F) (sch_arity M) Xs ->
    valid_scheme_vars (E & G) M Xs ->
    valid_env (E & F & G) ->
    valid_scheme_vars (E & F & G) M Xs.
Proof.
  introv Hf Hs He.
  apply regular_valid_scheme_vars in Hs.
  pose combined_kinding_weakening.
  intuition eauto.
Qed.

Lemma valid_scheme_vars_weakening_l : forall E F M Xs,
    fresh (dom F) (sch_arity M) Xs ->
    valid_scheme_vars E M Xs ->
    valid_env (E & F) ->
    valid_scheme_vars (E & F) M Xs.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply valid_scheme_vars_weakening;
    rewrite? concat_empty_r; assumption.
Qed.

Lemma valid_scheme_weakening : forall E F G M,
    valid_scheme (E & G) M ->
    valid_env (E & F & G) ->
    valid_scheme (E & F & G) M.
Proof.
  introv Hs He.
  apply regular_valid_scheme in Hs.
  pose combined_kinding_weakening.
  intuition eauto.
Qed.

Lemma valid_scheme_weakening_l : forall E F M,
    valid_scheme E M ->
    valid_env (E & F) ->
    valid_scheme (E & F) M.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply valid_scheme_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma type_equal_core_weakening : forall E F G T1 T2 K,
   type_equal_core (E & G) T1 T2 K -> 
   valid_env (E & F & G) ->
   type_equal_core (E & F & G) T1 T2 K.
Proof.
  introv Hte He.
  apply regular_type_equal_core in Hte.
  pose combined_kinding_weakening.
  intuition eauto.
Qed.

Lemma type_equal_core_weakening_l : forall E F T1 T2 K,
   type_equal_core E T1 T2 K -> 
   valid_env (E & F) ->
   type_equal_core (E & F) T1 T2 K.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply type_equal_core_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma type_equal_symm_weakening : forall E F G T1 T2 K,
   type_equal_symm (E & G) T1 T2 K -> 
   valid_env (E & F & G) ->
   type_equal_symm (E & F & G) T1 T2 K.
Proof.
  introv Hte He.
  apply regular_type_equal_symm in Hte.
  pose combined_kinding_weakening.
  intuition eauto.
Qed.

Lemma type_equal_symm_weakening_l : forall E F T1 T2 K,
   type_equal_symm E T1 T2 K -> 
   valid_env (E & F) ->
   type_equal_symm (E & F) T1 T2 K.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply type_equal_symm_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma type_equal_cong_weakening : forall E F G T1 T2 K,
   type_equal_cong (E & G) T1 T2 K -> 
   valid_env (E & F & G) ->
   type_equal_cong (E & F & G) T1 T2 K.
Proof.
  introv Hte He.
  apply regular_type_equal_cong in Hte.
  pose combined_kinding_weakening.
  intuition eauto.
Qed.

Lemma type_equal_cong_weakening_l : forall E F T1 T2 K,
   type_equal_cong E T1 T2 K -> 
   valid_env (E & F) ->
   type_equal_cong (E & F) T1 T2 K.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply type_equal_cong_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma type_equal_weakening : forall E F G T1 T2 K,
   type_equal (E & G) T1 T2 K -> 
   valid_env (E & F & G) ->
   type_equal (E & F & G) T1 T2 K.
Proof.
  introv Hte He.
  apply regular_type_equal in Hte.
  pose combined_kinding_weakening.
  intuition eauto.
Qed.

Lemma type_equal_weakening_l : forall E F T1 T2 K,
   type_equal E T1 T2 K -> 
   valid_env (E & F) ->
   type_equal (E & F) T1 T2 K.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply type_equal_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma subtype_weakening : forall E F G T1 T2 cs,
    subtype (E & G) T1 T2 cs ->
    valid_env (E & F & G) ->
    subtype (E & F & G) T1 T2 cs.
Proof.
  introv Hs He.
  apply regular_subtype in Hs.
  pose combined_kinding_weakening.
  intuition eauto.
Qed.

Lemma subtype_weakening_l : forall E F T1 T2 cs,
    subtype E T1 T2 cs ->
    valid_env (E & F) ->
    subtype (E & F) T1 T2 cs.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply subtype_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma valid_instance_weakening : forall E F G Ts M,
  valid_instance (E & G) Ts M ->
  valid_env (E & F & G) ->
  valid_instance (E & F & G) Ts M.
Proof.
  introv Hk He.
  remember (E & G) as EG.
  induction Hk; subst; auto using kinding_weakening.
Qed.

Lemma valid_instance_weakening_l : forall E F Ts M,
  valid_instance E Ts M ->
  valid_env (E & F) ->
  valid_instance (E & F) Ts M.
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply valid_instance_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma valid_env_kind_weakening : forall E F G X K,
    X # F ->
    valid_env (E & G & X ~:: K) ->
    valid_env (E & F & G) ->
    valid_env (E & F & G & X ~:: K).
Proof.
  introv Hin He1 He2.
  assert (environment (E & F & G))
    by auto with valid_env_regular.
  destruct (valid_env_kind_inv He1) as [_ [? ?]].
  auto using valid_kind_weakening.
Qed.

Lemma valid_env_kind_weakening_l : forall E F X K,
    X # F ->
    valid_env (E & X ~:: K) ->
    valid_env (E & F) ->
    valid_env (E & F & X ~:: K).
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply valid_env_kind_weakening; rewrite? concat_empty_r; assumption.
Qed.

Lemma valid_env_type_weakening : forall E F G x M,
    x # F ->
    valid_env (E & G & x ~: M) ->
    valid_env (E & F & G) ->
    valid_env (E & F & G & x ~: M).
Proof.
  introv Hin He1 He2.
  assert (environment (E & F & G))
    by auto with valid_env_regular.
  destruct (valid_env_type_inv He1) as [_ [? ?]].
  auto using valid_scheme_weakening.
Qed.

Lemma valid_env_type_weakening_l : forall E F x M,
    x # F ->
    valid_env (E & x ~: M) ->
    valid_env (E & F) ->
    valid_env (E & F & x ~: M).
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply valid_env_type_weakening; rewrite? concat_empty_r; assumption.
Qed.

Lemma valid_env_kinds_weakening : forall E F G Xs M,
    fresh (dom F) (sch_arity M) Xs ->
    valid_env (E & G & Xs ~::* M) ->
    valid_env (E & F & G) ->
    valid_env (E & F & G & Xs ~::* M).
Proof.
  introv Hf He1 He2.
  fresh_length Hf as Hl.
  generalize dependent G.
  generalize dependent M.
  induction Xs; introv Hf Hl He1 He2; subst; simpl.
  - autorewrite with rew_env_concat; auto.
  - destruct M; simpl in Hl; try discriminate.
    simpl in He1.
    autorewrite with rew_env_concat in *.
    destruct Hf.
    inversion Hl.
    rewrite <- concat_assoc with (E := E & F).
    apply IHXs with (G := G & a ~:: k);
      autorewrite with rew_sch_arity;
      autorewrite with rew_env_dom;
      autorewrite with rew_env_concat; auto.
    apply valid_env_kind_weakening;
      eauto using valid_env_retract.
Qed.

Lemma valid_env_kinds_weakening_l : forall E F Xs M,
    fresh (dom F) (sch_arity M) Xs ->
    valid_env (E & Xs ~::* M) ->
    valid_env (E & F) ->
    valid_env (E & F & Xs ~::* M).
Proof.
  introv Hv He.
  rewrite <- concat_empty_r with (E := E & F).
  apply valid_env_kinds_weakening;
    rewrite? concat_empty_r; assumption.
Qed.

(* *************************************************************** *)
(** * Valid bindings *)

Lemma valid_scheme_from_env : forall E x M,
    valid_env E ->
    binds x (bind_typ M) E ->
    valid_scheme E M.
Proof.
  introv He Hb.
  apply regular_valid_env in He.
  induction He.
  - apply binds_empty_inv in Hb; contradiction.
  - destruct (binds_push_inv Hb) as [[Hx Hbnd]|[Hx Hbnd]];
      try discriminate.
    rewrite <- concat_empty_r with (E := E & X ~:: K).
    apply valid_scheme_weakening; rewrite concat_empty_r; auto.
  - destruct (binds_push_inv Hb) as [[Hx Hbnd]|[Hx Hbnd]];
      inversion Hbnd; subst;
      rewrite <- concat_empty_r with (E := E & x0 ~: M0);
      apply valid_scheme_weakening; rewrite concat_empty_r; auto.
Qed.

Lemma valid_kind_from_env : forall E X K,
    valid_env E ->
    binds X (bind_knd K) E ->
    valid_kind E K.
Proof.
  introv He Hb.
  apply regular_valid_env in He.
  induction He.
  - apply binds_empty_inv in Hb; contradiction.
  - destruct (binds_push_inv Hb) as [[Hx Hbnd]|[Hx Hbnd]];
      inversion Hbnd; subst;
      rewrite <- concat_empty_r with (E := E & X0 ~:: K0);
      apply valid_kind_weakening; rewrite concat_empty_r; auto.
  - destruct (binds_push_inv Hb) as [[Hx Hbnd]|[Hx Hbnd]];
      try discriminate.
    rewrite <- concat_empty_r with (E := E & x ~: M).
    apply valid_kind_weakening; rewrite concat_empty_r; auto.
Qed.

(* *************************************************************** *)
(** Judegments are closed *)

Lemma combined_kinding_closed :
     (forall E K,
      valid_kind_regular E K ->
      (forall X,
          X # E ->
          X \notin (knd_fv K)))
  /\ (forall E T K,
      kinding_regular E T K ->
         (forall X,
          X # E ->
          X \notin (typ_fv T))
      /\ (forall X,
          X # E ->
          X \notin (knd_fv K)))
  /\ (forall E M Xs,
      valid_scheme_vars_regular E M Xs ->
      (forall X,
          fresh \{X} (sch_arity M) Xs ->
          X # E ->
          X \notin (sch_fv M)))
  /\ (forall E M,
      valid_scheme_regular E M ->
      (forall X,
          X # E ->
          X \notin (sch_fv M)))
  /\ (forall E,
      valid_env_regular E ->
      (forall X Y K,
          X # E ->
          binds Y (bind_knd K) E ->
          X \notin (knd_fv K)))
  /\ (forall E T1 T2 K,
      type_equal_core_regular E T1 T2 K ->
         (forall X,
          X # E ->
          X \notin (typ_fv T1))
      /\ (forall X,
          X # E ->
          X \notin (typ_fv T2))
      /\ (forall X,
          X # E ->
          X \notin (knd_fv K)))
  /\ (forall E T1 T2 K,
      type_equal_symm_regular E T1 T2 K ->
         (forall X,
          X # E ->
          X \notin (typ_fv T1))
      /\ (forall X,
          X # E ->
          X \notin (typ_fv T2))
      /\ (forall X,
          X # E ->
          X \notin (knd_fv K)))
  /\ (forall E T1 T2 K,
      type_equal_cong_regular E T1 T2 K ->
         (forall X,
          X # E ->
          X \notin (typ_fv T1))
      /\ (forall X,
          X # E ->
          X \notin (typ_fv T2))
      /\ (forall X,
          X # E ->
          X \notin (knd_fv K)))
  /\ (forall E T1 T2 K,
      type_equal_regular E T1 T2 K ->
         (forall X,
          X # E ->
          X \notin (typ_fv T1))
      /\ (forall X,
          X # E ->
          X \notin (typ_fv T2))
      /\ (forall X,
          X # E ->
          X \notin (knd_fv K)))
  /\ (forall E T1 T2 cs,
      subtype_regular E T1 T2 cs ->
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
  - autorewrite with rew_sch_arity in *.
    eauto using sch_open_var_fv_inv.
  - pick_freshes_gen (L \u \{X}) (sch_arity M) Xs.
    eauto.
  - exfalso.
    eapply binds_empty_inv.
    eassumption.
  - assert (binds Y (bind_knd K0) (E & X ~:: K)) as Hb by assumption.
    destruct (binds_push_inv Hb) as [[Heq1 Heq2]|[Hneq Hb2]].
    + inversion Heq2; auto.
    + eauto.
  - assert (binds Y (bind_knd K) (E & x ~: M)) as Hb by assumption.
    destruct (binds_push_inv Hb) as [[Heq1 Heq2]|[Hneq Hb2]].
    + discriminate.
    + eauto.
  - assert (X \notin (typ_fv T1) \u (typ_fv T2))
      by (simpl in *; auto).
    auto.
Qed.

Lemma valid_kind_closed : forall E K X,
    valid_kind E K ->
    X # E ->
    X \notin (knd_fv K).
Proof.
  introv Hk Hn.
  apply regular_valid_kind in Hk.
  pose combined_kinding_closed.
  intuition eauto.
Qed.

Lemma kinding_closed : forall E T K X,
    kinding E T K ->
    X # E ->
    X \notin ((typ_fv T) \u (knd_fv K)).
Proof.
  introv Hk Hn.
  apply regular_kinding in Hk.
  pose combined_kinding_closed.
  jauto_set.
  assert
    ((forall X : var, X # E -> X \notin typ_fv T)
  /\ (forall X : var, X # E -> X \notin knd_fv K)) as Hc by auto.
  intuition auto.
Qed.

Lemma valid_scheme_vars_closed : forall E M Xs X,
    valid_scheme_vars E M Xs ->
    fresh \{X} (sch_arity M) Xs ->
    X # E ->
    X \notin (sch_fv M).
Proof.
  introv Hs Hn.
  apply regular_valid_scheme_vars in Hs.
  pose combined_kinding_closed.
  intuition eauto.
Qed.

Lemma valid_scheme_closed : forall E M X,
    valid_scheme E M ->
    X # E ->
    X \notin (sch_fv M).
Proof.
  introv Hs Hn.
  apply regular_valid_scheme in Hs.
  pose combined_kinding_closed.
  intuition eauto.
Qed.

Lemma valid_env_binds_knd_closed : forall E X Y K,
    valid_env E ->
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
    valid_env E ->
    X # E ->
    binds x (bind_typ M) E ->
    X \notin (sch_fv M).
Proof.
  introv He Hn Hb.
  induction He.
  - exfalso. eapply binds_empty_inv. eassumption.
  - destruct (binds_push_inv Hb) as [[? ?]|[? ?]].
    + discriminate.
    + auto.
  - destruct (binds_push_inv Hb) as [[? Heq]|[? ?]].
    + inversion Heq; subst.
      eauto using valid_scheme_closed.
    + auto.     
Qed.

Lemma valid_env_knd_closed : forall E X K,
    valid_env (E & X ~:: K) ->
    X # E ->
    X \notin knd_fv K.
Proof.
  introv He Hn.
  remember (E & X ~:: K) as EX.
  induction He; intros; subst.
  - exfalso. eapply empty_push_inv. eassumption.
  - destruct (eq_push_inv HeqEX) as [? [HeqK ?]].
    inversion HeqK; subst.
    eauto using valid_kind_closed.
  - destruct (eq_push_inv HeqEX) as [? [HeqK ?]].
    discriminate.
Qed.

Lemma valid_env_typ_closed : forall E x M,
    valid_env (E & x ~: M) ->
    x # E ->
    x \notin sch_fv M.
Proof.
  introv He Hn.
  remember (E & x ~: M) as Ex.
  induction He; intros; subst.
  - exfalso. eapply empty_push_inv. eassumption.
  - destruct (eq_push_inv HeqEx) as [? [HeqK ?]].
    discriminate.
  - destruct (eq_push_inv HeqEx) as [? [HeqK ?]].
    inversion HeqK; subst.
    eauto using valid_scheme_closed.
Qed.

Lemma type_equal_core_closed : forall E T1 T2 K X,
    type_equal_core E T1 T2 K ->
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
  /\ (forall X : var, X # E -> X \notin knd_fv K)) as Hc by auto.
  intuition auto.
Qed.

Lemma type_equal_symm_closed : forall E T1 T2 K X,
    type_equal_symm E T1 T2 K ->
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
  /\ (forall X : var, X # E -> X \notin knd_fv K)) as Hc by auto.
  intuition auto.
Qed.

Lemma type_equal_cong_closed : forall E T1 T2 K X,
    type_equal_cong E T1 T2 K ->
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
  /\ (forall X : var, X # E -> X \notin knd_fv K)) as Hc by auto.
  intuition auto.
Qed.

Lemma type_equal_closed : forall E T1 T2 K X,
    type_equal E T1 T2 K ->
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
  /\ (forall X : var, X # E -> X \notin knd_fv K)) as Hc by auto.
  intuition auto.
Qed.

Lemma subtype_closed : forall E T1 T2 cs X,
    subtype E T1 T2 cs ->
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

Lemma valid_instance_closed : forall E Ts M X,
  valid_instance E Ts M ->
  X # E ->
  X \notin ((typ_fv_list Ts) \u (sch_fv M)).
Proof.
  introv Hi Hn.
  induction Hi; simpl.
  - assert (kinding E T knd_type) as Hk by assumption.
    apply kinding_closed with (X := X) in Hk; auto.
  - assert (kinding E T K) as Hk by assumption.
    apply kinding_closed with (X := X) in Hk; auto.
    assert (X \notin typ_fv_list Ts \u sch_fv (sch_open M T)) as Hn2
      by auto.
    eauto using sch_open_fv_inv.
Qed.

(* *************************************************************** *)
(** Preserved by type substitution *)

Lemma combined_kinding_typ_subst :
     (forall EXF K,
      valid_kind_regular EXF K ->
      (forall E F X J S,
          EXF = E & X ~:: J & F ->
          kinding E S J ->
          valid_kind (E & env_subst X S F) (knd_subst X S K)))
  /\ (forall EXF T K,
      kinding_regular EXF T K ->
      (forall E F X J S,
          EXF = E & X ~:: J & F ->
          kinding E S J ->
          kinding (E & env_subst X S F)
            (typ_subst X S T) (knd_subst X S K)))
  /\ (forall EXF M Xs,
      valid_scheme_vars_regular EXF M Xs ->
      (forall E F X J S,
          fresh \{X} (sch_arity M) Xs ->
          EXF = E & X ~:: J & F ->
          kinding E S J ->
          valid_scheme_vars (E & env_subst X S F)
            (sch_subst X S M) Xs))
  /\ (forall EXF M,
      valid_scheme_regular EXF M ->
      (forall E F X J S,
          EXF = E & X ~:: J & F ->
          kinding E S J ->
          valid_scheme (E & env_subst X S F) (sch_subst X S M)))
  /\ (forall EXF,
      valid_env_regular EXF ->
      (forall E F X J S,
          EXF = E & X ~:: J & F ->
          kinding E S J ->
          valid_env (E & env_subst X S F)))
  /\ (forall EXF T1 T2 K,
      type_equal_core_regular EXF T1 T2 K ->
      (forall E F X J S,
          EXF = E & X ~:: J & F ->
          kinding E S J ->
          type_equal_core (E & env_subst X S F)
            (typ_subst X S T1) (typ_subst X S T2) (knd_subst X S K)))
  /\ (forall EXF T1 T2 K,
      type_equal_symm_regular EXF T1 T2 K ->
      (forall E F X J S,
          EXF = E & X ~:: J & F ->
          kinding E S J ->
          type_equal_symm (E & env_subst X S F)
            (typ_subst X S T1) (typ_subst X S T2) (knd_subst X S K)))
  /\ (forall EXF T1 T2 K,
      type_equal_cong_regular EXF T1 T2 K ->
      (forall E F X J S,
          EXF = E & X ~:: J & F ->
          kinding E S J ->
          type_equal_cong (E & env_subst X S F)
            (typ_subst X S T1) (typ_subst X S T2) (knd_subst X S K)))
  /\ (forall EXF T1 T2 K,
      type_equal_regular EXF T1 T2 K ->
      (forall E F X J S,
          EXF = E & X ~:: J & F ->
          kinding E S J ->
          type_equal (E & env_subst X S F)
            (typ_subst X S T1) (typ_subst X S T2) (knd_subst X S K)))
  /\ (forall EXF T1 T2 cs,
      subtype_regular EXF T1 T2 cs ->
      (forall E F X J S,
          EXF = E & X ~:: J & F ->
          kinding E S J ->
          subtype (E & env_subst X S F)
            (typ_subst X S T1) (typ_subst X S T2) cs)).
Proof.
  apply combined_kinding_regular_mutind; intros; subst; simpl;
    econstr eauto.
  - case_var.
    + assert (bind_knd K = bind_knd J) as Hbnd
        by eauto using binds_middle_eq_inv, ok_from_environment.
      inversion Hbnd; subst.
      rewrite knd_subst_fresh; eauto using kinding_weakening_l.
      assert (environment (E0 & X0 ~:: J)) as He
        by eauto using environment_retract.
      destruct (environment_knd_inv He).
      eauto using valid_env_knd_closed, valid_env_retract.
    + { assert (binds X (bind_knd K) (E0 & X0 ~:: J & F)) as Hb
          by assumption.
        destruct (binds_middle_inv Hb)
          as [Hbf | [[Hn [Heq1 Heq2]] | [Hn [Hneq Hbe]]]].
        - apply env_subst_binds with (Z := X0) (U := S) in Hbf.
          simpl in Hbf.
          apply binds_concat_right with (E1 := E0) in Hbf.
          eauto.
        - contradiction.
        - assert (environment (E0 & X0 ~:: J)) as He
            by eauto using environment_retract.
          destruct (environment_knd_inv He).
          assert (valid_env E0) by eauto using valid_env_retract.
          rewrite knd_subst_fresh; eauto using kinding_weakening_l.
          apply valid_env_binds_knd_closed
            with (E := E0) (Y := X); auto. }
  - apply kinding_range_subsumption
      with (T1 := typ_subst X S T1) (T2 := typ_subst X S T2); eauto.
  - apply valid_scheme_vars_bind; eauto.
    rewrite <- concat_assoc.
    rewrite <- env_subst_knd.
    rewrite sch_subst_open_var; auto with kinding_regular.
    assert (fresh \{X0} (sch_arity (sch_bind K M)) (X :: Xs)) as Hf
      by assumption.
    destruct Hf as [? Hf].
    rewrite <- sch_open_var_arity with (X := X) in Hf.
    eauto using concat_assoc.
  - apply valid_scheme_c with (L := L \u \{X}).
    autorewrite with rew_sch_arity.
    eauto.
  - exfalso. eapply empty_middle_inv. eassumption.
  - assert (E & X ~:: K = E0 & X0 ~:: J & F) as Heq
      by assumption.
    destruct F using env_ind.
    + rewrite concat_empty_r in Heq.
      destruct (eq_push_inv Heq) as [? [Heqb ?]].
      inversion Heqb; subst.
      autorewrite with rew_env_subst rew_env_concat.
      auto.
    + rewrite concat_assoc in Heq.
      destruct (eq_push_inv Heq) as [? [? ?]]; subst.
      autorewrite with rew_env_subst rew_env_concat.
      simpl.
      apply valid_env_kind; autorewrite with rew_env_dom; eauto.
  - assert (E & x ~: M = E0 & X ~:: J & F) as Heq
      by assumption.
    destruct F using env_ind.
    + rewrite concat_empty_r in Heq.
      destruct (eq_push_inv Heq) as [? [Heqb ?]].
      discriminate.
    + rewrite concat_assoc in Heq.
      destruct (eq_push_inv Heq) as [? [? ?]]; subst.
      autorewrite with rew_env_subst rew_env_concat.
      simpl.
      apply valid_env_type; autorewrite with rew_env_dom; eauto.
  - apply type_equal_cong_range_subsumption
      with (T3 := typ_subst X S T3) (T4 := typ_subst X S T4); eauto.
Qed.

Lemma valid_kind_typ_subst : forall E F X J S K,
    valid_kind (E & X ~:: J & F) K ->
    kinding E S J ->
    valid_kind (E & env_subst X S F) (knd_subst X S K).
Proof.
  introv Hv Hk.
  apply regular_valid_kind in Hv.
  pose combined_kinding_typ_subst.
  intuition eauto.
Qed.

Lemma valid_kind_typ_subst_l : forall E X J S K,
    valid_kind (E & X ~:: J) K ->
    kinding E S J ->
    valid_kind E (knd_subst X S K).
Proof.
  introv Hv Hk.
  rewrite <- concat_empty_r with (E := E & X ~:: J) in Hv.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- env_subst_empty with (X := X) (U := S).
  eauto using valid_kind_typ_subst.
Qed.

Lemma kinding_typ_subst : forall E F X J S T K,
    kinding (E & X ~:: J & F) T K ->
    kinding E S J ->
    kinding (E & env_subst X S F)
      (typ_subst X S T) (knd_subst X S K).
Proof.
  introv Hk1 Hk2.
  apply regular_kinding in Hk1.
  pose combined_kinding_typ_subst.
  intuition eauto.
Qed.

Lemma kinding_typ_subst_l : forall E X J S T K,
    kinding (E & X ~:: J) T K ->
    kinding E S J ->
    kinding E (typ_subst X S T) (knd_subst X S K).
Proof.
  introv Hk1 Hk2.
  rewrite <- concat_empty_r with (E := E & X ~:: J) in Hk1.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- env_subst_empty with (X := X) (U := S).
  eauto using kinding_typ_subst.
Qed.

Lemma valid_scheme_vars_typ_subst : forall E F X J S M Xs,
    valid_scheme_vars (E & X ~:: J & F) M Xs ->
    fresh \{X} (sch_arity M) Xs ->
    kinding E S J ->
    valid_scheme_vars (E & env_subst X S F) (sch_subst X S M) Xs.
Proof.
  introv Hv Hf Hk.
  apply regular_valid_scheme_vars in Hv.
  pose combined_kinding_typ_subst.
  intuition eauto.
Qed.

Lemma valid_scheme_vars_typ_subst_l : forall E X J S M Xs,
    valid_scheme_vars (E & X ~:: J) M Xs ->
    fresh \{X} (sch_arity M) Xs ->
    kinding E S J ->
    valid_scheme_vars E (sch_subst X S M) Xs.
Proof.
  introv Hv Hf Hk.
  rewrite <- concat_empty_r with (E := E & X ~:: J) in Hv.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- env_subst_empty with (X := X) (U := S).
  eauto using valid_scheme_vars_typ_subst.
Qed.

Lemma valid_scheme_typ_subst : forall E F X J S M,
    valid_scheme (E & X ~:: J & F) M ->
    kinding E S J ->
    valid_scheme (E & env_subst X S F) (sch_subst X S M).
Proof.
  introv Hv Hk.
  apply regular_valid_scheme in Hv.
  pose combined_kinding_typ_subst.
  intuition eauto.
Qed.

Lemma valid_scheme_typ_subst_l : forall E X J S M,
    valid_scheme (E & X ~:: J) M ->
    kinding E S J ->
    valid_scheme E (sch_subst X S M).
Proof.
  introv Hv Hk.
  rewrite <- concat_empty_r with (E := E & X ~:: J) in Hv.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- env_subst_empty with (X := X) (U := S).
  eauto using valid_scheme_typ_subst.
Qed.

Lemma valid_env_typ_subst: forall E F X J S,
    valid_env (E & X ~:: J & F) ->
    kinding E S J ->
    valid_env (E & env_subst X S F).
Proof.
  introv Hv Hk.
  apply regular_valid_env in Hv.
  pose combined_kinding_typ_subst.
  intuition eauto.
Qed.

Lemma binds_typ_typ_subst : forall E F X J S x M,
    valid_env (E & X ~:: J & F) ->
    kinding E S J ->
    binds x (bind_typ M) (E & X ~:: J & F) ->
    binds x (bind_typ (sch_subst X S M)) (E & env_subst X S F).
Proof.
  introv Hv Hk Hb.
  assert (valid_env (E & env_subst X S F))
      by eauto using valid_env_typ_subst.
  assert (ok (E & X ~:: J & F)) as Hok1
    by auto using ok_from_environment with valid_env_regular.
  destruct (ok_middle_inv Hok1).
  assert (ok (E & env_subst X S F)) as Hok2
    by auto using ok_from_environment with valid_env_regular.
  destruct (binds_middle_inv Hb) as [?|[[_[_?]]|[_[_?]]]].
  + eauto using binds_concat_right, env_subst_binds_typ.
  + discriminate.
  + replace (sch_subst X S M) with M;
      auto using binds_concat_left_ok.
    symmetry.
    apply sch_subst_fresh.
    eapply valid_env_binds_typ_closed with (E := E);
      eauto using valid_env_retract.
Qed.  

Lemma type_equal_core_typ_subst : forall E F X J S T1 T2 K,
    type_equal_core (E & X ~:: J & F) T1 T2 K ->
    kinding E S J ->
    type_equal_core (E & env_subst X S F)
      (typ_subst X S T1) (typ_subst X S T2) (knd_subst X S K).
Proof.
  introv Hte Hk.
  apply regular_type_equal_core in Hte.
  pose combined_kinding_typ_subst.
  intuition eauto.
Qed.

Lemma type_equal_core_typ_subst_l : forall E X J S T1 T2 K,
    type_equal_core (E & X ~:: J) T1 T2 K ->
    kinding E S J ->
    type_equal_core E
      (typ_subst X S T1) (typ_subst X S T2) (knd_subst X S K).
Proof.
  introv Hte Hk.
  rewrite <- concat_empty_r with (E := E & X ~:: J) in Hte.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- env_subst_empty with (X := X) (U := S).
  eauto using type_equal_core_typ_subst.
Qed.

Lemma type_equal_symm_typ_subst : forall E F X J S T1 T2 K,
    type_equal_symm (E & X ~:: J & F) T1 T2 K ->
    kinding E S J ->
    type_equal_symm (E & env_subst X S F)
      (typ_subst X S T1) (typ_subst X S T2) (knd_subst X S K).
Proof.
  introv Hte Hk.
  apply regular_type_equal_symm in Hte.
  pose combined_kinding_typ_subst.
  intuition eauto.
Qed.

Lemma type_equal_symm_typ_subst_l : forall E X J S T1 T2 K,
    type_equal_symm (E & X ~:: J) T1 T2 K ->
    kinding E S J ->
    type_equal_symm E
      (typ_subst X S T1) (typ_subst X S T2) (knd_subst X S K).
Proof.
  introv Hte Hk.
  rewrite <- concat_empty_r with (E := E & X ~:: J) in Hte.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- env_subst_empty with (X := X) (U := S).
  eauto using type_equal_symm_typ_subst.
Qed.

Lemma type_equal_cong_typ_subst : forall E F X J S T1 T2 K,
    type_equal_cong (E & X ~:: J & F) T1 T2 K ->
    kinding E S J ->
    type_equal_cong (E & env_subst X S F)
      (typ_subst X S T1) (typ_subst X S T2) (knd_subst X S K).
Proof.
  introv Hte Hk.
  apply regular_type_equal_cong in Hte.
  pose combined_kinding_typ_subst.
  intuition eauto.
Qed.

Lemma type_equal_cong_typ_subst_l : forall E X J S T1 T2 K,
    type_equal_cong (E & X ~:: J) T1 T2 K ->
    kinding E S J ->
    type_equal_cong E
      (typ_subst X S T1) (typ_subst X S T2) (knd_subst X S K).
Proof.
  introv Hte Hk.
  rewrite <- concat_empty_r with (E := E & X ~:: J) in Hte.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- env_subst_empty with (X := X) (U := S).
  eauto using type_equal_cong_typ_subst.
Qed.

Lemma type_equal_typ_subst : forall E F X J S T1 T2 K,
    type_equal (E & X ~:: J & F) T1 T2 K ->
    kinding E S J ->
    type_equal (E & env_subst X S F)
      (typ_subst X S T1) (typ_subst X S T2) (knd_subst X S K).
Proof.
  introv Hte Hk.
  apply regular_type_equal in Hte.
  pose combined_kinding_typ_subst.
  intuition eauto.
Qed.

Lemma type_equal_typ_subst_l : forall E X J S T1 T2 K,
    type_equal (E & X ~:: J) T1 T2 K ->
    kinding E S J ->
    type_equal E
      (typ_subst X S T1) (typ_subst X S T2) (knd_subst X S K).
Proof.
  introv Hte Hk.
  rewrite <- concat_empty_r with (E := E & X ~:: J) in Hte.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- env_subst_empty with (X := X) (U := S).
  eauto using type_equal_typ_subst.
Qed.

Lemma subtype_typ_subst : forall E F X J S T1 T2 cs,
    subtype (E & X ~:: J & F) T1 T2 cs ->
    kinding E S J ->
    subtype (E & env_subst X S F)
      (typ_subst X S T1) (typ_subst X S T2) cs.
Proof.
  introv Hs Hk.
  apply regular_subtype in Hs.
  pose combined_kinding_typ_subst.
  intuition eauto.
Qed.

Lemma subtype_typ_subst_l : forall E X J S T1 T2 cs,
    subtype (E & X ~:: J) T1 T2 cs ->
    kinding E S J ->
    subtype E (typ_subst X S T1) (typ_subst X S T2) cs.
Proof.
  introv Hte Hk.
  rewrite <- concat_empty_r with (E := E & X ~:: J) in Hte.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- env_subst_empty with (X := X) (U := S).
  eauto using subtype_typ_subst.
Qed.

Lemma valid_instance_typ_subst : forall E F X J S Ts M,
  valid_instance (E & X ~:: J & F) Ts M ->
  kinding E S J ->
  valid_instance (E & env_subst X S F)
       (List.map (typ_subst X S) Ts) (sch_subst X S M).
Proof.
  introv Hi He.
  remember (E & X ~:: J & F) as EXF.
  induction Hi; subst.
  - apply valid_instance_empty.
    fold (knd_subst X S knd_type).
    eauto using kinding_typ_subst.
  - apply valid_instance_bind; eauto using kinding_typ_subst.
    fold (List.map (typ_subst X S) Ts).
    fold (sch_subst X S M).
    rewrite <- sch_subst_open; auto with kinding_regular.
Qed.

Lemma valid_instance_typ_subst_l : forall E X J S Ts M,
  valid_instance (E & X ~:: J) Ts M ->
  kinding E S J ->
  valid_instance E (List.map (typ_subst X S) Ts) (sch_subst X S M).
Proof.
  introv Hv Hk.
  rewrite <- concat_empty_r with (E := E & X ~:: J) in Hv.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- env_subst_empty with (X := X) (U := S).
  eauto using valid_instance_typ_subst.
Qed.

Lemma kinding_instance : forall E Ts M,
    valid_instance E Ts M ->
    kinding E (instance M Ts) knd_type.
Proof.
  introv Hi.
  generalize dependent M.
  induction Ts; introv Hi; destruct M; simpl;
    inversion Hi; subst; auto.
Qed.

(* *************************************************************** *)
(** * Convenient inversions of valid schemes *)

Lemma valid_scheme_bind_inv_knd : forall E K M,
    valid_scheme E (sch_bind K M) -> valid_kind E K.
Proof.
  introv Hs.
  remember (sch_bind K M) as Mb.
  destruct Hs; subst.
  pick_freshes_gen L (sch_arity (sch_bind K M)) Xs.
  fresh_length Fr as Hl.
  assert (valid_scheme_vars E (sch_bind K M) Xs) as Hs by auto.
  inversion Hs.
  auto.
Qed.  

Lemma valid_scheme_bind_inv_sch : forall E K M X,
    X # E ->
    valid_env E ->
    valid_scheme E (sch_bind K M) ->
    valid_scheme (E & X ~:: K) (M ^ X).
Proof.
  introv Hn He Hs.
  assert (valid_kind E K) by eauto using valid_scheme_bind_inv_knd.
  remember (sch_bind K M) as Mb.
  destruct Hs; subst.
  pick_fresh Y.
  apply valid_scheme_c with (L := \{X} \u L \u \{Y}).
  introv Hf.
  fresh_length Hf as Hl.
  autorewrite with rew_sch_arity in Hf.
  assert (valid_scheme_vars E (sch_bind K M) (Y :: Xs)) as Hs by auto.
  inversion Hs; subst.
  assert (valid_env (E & X ~:: K & Y ~:: K))
    by auto using valid_env_kind_weakening_l.
  assert (valid_scheme_vars (E & X ~:: K & Y ~:: K)
                            (sch_open_var M Y) Xs)
    as Hv by (apply valid_scheme_vars_weakening;
          autorewrite with rew_env_dom rew_sch_arity; auto).
  apply valid_scheme_vars_typ_subst_l with (S := (typ_fvar X)) in Hv;
    autorewrite with rew_sch_arity; auto.
  unfold sch_open_var.
  rewrite sch_subst_intro with (X := Y); auto.
Qed.

(* *************************************************************** *)
(** * Constructor of valid "kinds" bindings  *)

Lemma valid_env_kinds : forall E Xs M,
    valid_env E ->
    (fresh (dom E) (sch_arity M) Xs) ->
    valid_scheme E M ->
    valid_env (E & Xs ~::* M).
Proof.
  introv He Hf Hs.
  fresh_length Hf as Hl.
  rewrite <- (concat_empty_r E) in *.
  generalize dependent (@empty bind).
  generalize dependent M.
  induction Xs; intros M Hl F He Hf Hs; simpl.
  - autorewrite with rew_env_concat; auto.
  - destruct M.
    + autorewrite with rew_env_concat; auto.
    + { destruct Hf.
        rewrite concat_assoc.
        rewrite <- (concat_assoc E).
        apply IHXs.
        - autorewrite with rew_sch_arity. auto.
        - rewrite concat_assoc.
          apply valid_env_kind; auto.
          apply valid_scheme_bind_inv_knd with (M := M).
          auto.
        - autorewrite with rew_env_dom in *.
          autorewrite with rew_sch_arity.
          auto.
        - rewrite concat_assoc.
          auto using valid_scheme_bind_inv_sch. }
Qed.

(* *************************************************************** *)
(** Can remove type bindings *)

Lemma combined_kinding_remove_typ_bind :
     (forall EXF K,
      valid_kind EXF K ->
      (forall E F x M,
          EXF = E & x ~: M & F ->
          valid_kind (E & F) K))
  /\ (forall EXF T K,
      kinding EXF T K ->
      (forall E F x M,
          EXF = E & x ~: M & F ->
          kinding (E & F) T K))
  /\ (forall EXF Ms Xs,
      valid_scheme_vars EXF Ms Xs ->
      (forall E F x M,
          EXF = E & x ~: M & F ->
          valid_scheme_vars (E & F) Ms Xs))
  /\ (forall EXF Ms,
      valid_scheme EXF Ms ->
      (forall E F x M,
          EXF = E & x ~: M & F ->
          valid_scheme (E & F) Ms))
  /\ (forall EXF,
      valid_env EXF ->
      (forall E F x M,
          EXF = E & x ~: M & F ->
          valid_env (E & F)))
  /\ (forall EXF T1 T2 K,
      type_equal_core EXF T1 T2 K ->
      (forall E F x M,
          EXF = E & x ~: M & F ->
          type_equal_core (E & F) T1 T2 K))
  /\ (forall EXF T1 T2 K,
      type_equal_symm EXF T1 T2 K ->
      (forall E F x M,
          EXF = E & x ~: M & F ->
          type_equal_symm (E & F) T1 T2 K))
  /\ (forall EXF T1 T2 K,
      type_equal_cong EXF T1 T2 K ->
      (forall E F x M,
          EXF = E & x ~: M & F ->
          type_equal_cong (E & F) T1 T2 K))
  /\ (forall EXF T1 T2 K,
      type_equal EXF T1 T2 K ->
      (forall E F x M,
          EXF = E & x ~: M & F ->
          type_equal (E & F) T1 T2 K))
  /\ (forall EXF T1 T2 cs,
      subtype EXF T1 T2 cs ->
      (forall E F x M,
          EXF = E & x ~: M & F ->
          subtype (E & F) T1 T2 cs)).
Proof.
  apply combined_kinding_mutind; intros; subst; simpl; econstr eauto.
  - assert (binds X (bind_knd K) (E0 & x ~: M & F)) as Hb
      by assumption.
    destruct (binds_middle_inv Hb) as [? | [[? [? ?]] | [? [? ?]]]];
      try discriminate; eauto.
  - apply valid_scheme_vars_bind; eauto.
    rewrite <- concat_assoc.
    eauto using concat_assoc.
  - exfalso. eapply empty_middle_inv. eassumption.
  - assert (E & X ~:: K = E0 & x ~: M & F) as Heq
      by assumption.
    destruct F using env_ind.
    + rewrite concat_empty_r in Heq.
      destruct (eq_push_inv Heq) as [? [Heqb ?]].
      discriminate.
    + rewrite concat_assoc in Heq.
      destruct (eq_push_inv Heq) as [? [? ?]]; subst.
      rewrite concat_assoc.
      apply valid_env_kind; eauto.
  - assert (E & x ~: M = E0 & x0 ~: M0 & F) as Heq
      by assumption.
    destruct F using env_ind.
    + rewrite concat_empty_r in Heq.
      destruct (eq_push_inv Heq) as [? [Heq2 ?]].
      inversion Heq2; subst.
      rewrite concat_empty_r.
      assumption.
    + rewrite concat_assoc in Heq.
      destruct (eq_push_inv Heq) as [? [? ?]]; subst.
      rewrite concat_assoc.
      apply valid_env_type; eauto.
Qed.      

Lemma valid_kind_remove_typ_bind : forall E F x M K,
    valid_kind (E & x ~: M & F) K ->
    valid_kind (E & F) K.
Proof.
  introv Hv.
  pose combined_kinding_remove_typ_bind.
  intuition eauto.
Qed.

Lemma valid_kind_remove_typ_bind_l : forall E x M K,
    valid_kind (E & x ~: M) K ->
    valid_kind E K.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using valid_kind_remove_typ_bind.
Qed.

Lemma kinding_remove_typ_bind : forall E F x M T K,
    kinding (E & x ~: M & F) T K ->
    kinding (E & F) T K.
Proof.
  introv Hk.
  pose combined_kinding_remove_typ_bind.
  intuition eauto.
Qed.

Lemma kinding_remove_typ_bind_l : forall E x M T K,
    kinding (E & x ~: M) T K ->
    kinding E T K.
Proof.
  introv Hk.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Hk.
  rewrite <- concat_empty_r with (E := E).
  eauto using kinding_remove_typ_bind.
Qed.

Lemma valid_scheme_vars_remove_typ_bind : forall E F x M Ms Xs,
    valid_scheme_vars (E & x ~: M & F) Ms Xs ->
    valid_scheme_vars (E & F) Ms Xs.
Proof.
  introv Hv.
  pose combined_kinding_remove_typ_bind.
  intuition eauto.
Qed.

Lemma valid_scheme_vars_remove_typ_bind_l : forall E x M Ms Xs,
    valid_scheme_vars (E & x ~: M) Ms Xs ->
    valid_scheme_vars E Ms Xs.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using valid_scheme_vars_remove_typ_bind.
Qed.

Lemma valid_scheme_remove_typ_bind : forall E F x M Ms,
    valid_scheme (E & x ~: M & F) Ms ->
    valid_scheme (E & F) Ms.
Proof.
  introv Hv.
  pose combined_kinding_remove_typ_bind.
  intuition eauto.
Qed.

Lemma valid_scheme_remove_typ_bind_l : forall E x M Ms,
    valid_scheme (E & x ~: M) Ms ->
    valid_scheme E Ms.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using valid_scheme_remove_typ_bind.
Qed.

Lemma valid_env_remove_typ_bind : forall E F x M,
    valid_env (E & x ~: M & F) ->
    valid_env (E & F).
Proof.
  introv Hv.
  pose combined_kinding_remove_typ_bind.
  intuition eauto.
Qed.

Lemma valid_env_remove_typ_bind_l : forall E x M,
    valid_env (E & x ~: M) ->
    valid_env E.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using valid_env_remove_typ_bind.
Qed.

Lemma type_equal_core_remove_typ_bind : forall E F x M T1 T2 K,
    type_equal_core (E & x ~: M & F) T1 T2 K ->
    type_equal_core (E & F) T1 T2 K.
Proof.
  introv Hte.
  pose combined_kinding_remove_typ_bind.
  intuition eauto.
Qed.

Lemma type_equal_core_remove_typ_bind_l : forall E x M T1 T2 K,
    type_equal_core (E & x ~: M) T1 T2 K ->
    type_equal_core E T1 T2 K.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using type_equal_core_remove_typ_bind.
Qed.

Lemma type_equal_symm_remove_typ_bind : forall E F x M T1 T2 K,
    type_equal_symm (E & x ~: M & F) T1 T2 K ->
    type_equal_symm (E & F) T1 T2 K.
Proof.
  introv Hte.
  pose combined_kinding_remove_typ_bind.
  intuition eauto.
Qed.

Lemma type_equal_symm_remove_typ_bind_l : forall E x M T1 T2 K,
    type_equal_symm (E & x ~: M) T1 T2 K ->
    type_equal_symm E T1 T2 K.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using type_equal_symm_remove_typ_bind.
Qed.

Lemma type_equal_cong_remove_typ_bind : forall E F x M T1 T2 K,
    type_equal_cong (E & x ~: M & F) T1 T2 K ->
    type_equal_cong (E & F) T1 T2 K.
Proof.
  introv Hte.
  pose combined_kinding_remove_typ_bind.
  intuition eauto.
Qed.

Lemma type_equal_cong_remove_typ_bind_l : forall E x M T1 T2 K,
    type_equal_cong (E & x ~: M) T1 T2 K ->
    type_equal_cong E T1 T2 K.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using type_equal_cong_remove_typ_bind.
Qed.

Lemma type_equal_remove_typ_bind : forall E F x M T1 T2 K,
    type_equal (E & x ~: M & F) T1 T2 K ->
    type_equal (E & F) T1 T2 K.
Proof.
  introv Hte.
  pose combined_kinding_remove_typ_bind.
  intuition eauto.
Qed.

Lemma type_equal_remove_typ_bind_l : forall E x M T1 T2 K,
    type_equal (E & x ~: M) T1 T2 K ->
    type_equal E T1 T2 K.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using type_equal_remove_typ_bind.
Qed.

Lemma subtype_remove_typ_bind : forall E F x M T1 T2 cs,
    subtype (E & x ~: M & F) T1 T2 cs ->
    subtype (E & F) T1 T2 cs.
Proof.
  introv Hs.
  pose combined_kinding_remove_typ_bind.
  intuition eauto.
Qed.

Lemma subtype_remove_typ_bind_l : forall E x M T1 T2 cs,
    subtype (E & x ~: M) T1 T2 cs ->
    subtype E T1 T2 cs.
Proof.
  introv Hv.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Hv.
  rewrite <- concat_empty_r with (E := E).
  eauto using subtype_remove_typ_bind.
Qed.

Lemma valid_instance_remove_typ_bind : forall E F x M1 Ts M2,
    valid_instance (E & x ~: M1 & F) Ts M2 ->
    valid_instance (E & F) Ts M2.
Proof.
  introv Hv.
  remember (E & x ~: M1 & F) as ExF.
  remember (E & F) as EF.
  induction Hv; subst; eauto using kinding_remove_typ_bind.
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

(* *************************************************************** *)
(** Can add type bindings *)

Lemma combined_kinding_add_typ_bind :
     (forall EF K,
      valid_kind EF K ->
      (forall E F x M,
          EF = E & F ->
          valid_scheme E M ->
          x # E & F ->
          valid_kind (E & x ~: M & F) K))
  /\ (forall EF T K,
      kinding EF T K ->
      (forall E F x M,
          EF = E & F ->
          valid_scheme E M ->
          x # E & F ->
          kinding (E & x ~: M & F) T K))
  /\ (forall EF Ms Xs,
      valid_scheme_vars EF Ms Xs ->
      (forall E F x M,
          EF = E & F ->
          valid_scheme E M ->
          x # E & F ->
          x \notin (from_list Xs) ->
          valid_scheme_vars (E & x ~: M & F) Ms Xs))
  /\ (forall EF Ms,
      valid_scheme EF Ms ->
      (forall E F x M,
          EF = E & F ->
          valid_scheme E M ->
          x # E & F ->
          valid_scheme (E & x ~: M & F) Ms))
  /\ (forall EF,
      valid_env EF ->
      (forall E F x M,
          EF = E & F ->
          valid_scheme E M ->
          x # E & F ->
          valid_env (E & x ~: M & F)))
  /\ (forall EF T1 T2 K,
      type_equal_core EF T1 T2 K ->
      (forall E F x M,
          EF = E & F ->
          valid_scheme E M ->
          x # E & F ->
          type_equal_core (E & x ~: M & F) T1 T2 K))
  /\ (forall EF T1 T2 K,
      type_equal_symm EF T1 T2 K ->
      (forall E F x M,
          EF = E & F ->
          valid_scheme E M ->
          x # E & F ->
          type_equal_symm (E & x ~: M & F) T1 T2 K))
  /\ (forall EF T1 T2 K,
      type_equal_cong EF T1 T2 K ->
      (forall E F x M,
          EF = E & F ->
          valid_scheme E M ->
          x # E & F ->
          type_equal_cong (E & x ~: M & F) T1 T2 K))
  /\ (forall EF T1 T2 K,
      type_equal EF T1 T2 K ->
      (forall E F x M,
          EF = E & F ->
          valid_scheme E M ->
          x # E & F ->
          type_equal (E & x ~: M & F) T1 T2 K))
  /\ (forall EF T1 T2 cs,
      subtype EF T1 T2 cs ->
      (forall E F x M,
          EF = E & F ->
          valid_scheme E M ->
          x # E & F ->
          subtype (E & x ~: M & F) T1 T2 cs)).
Proof.
  apply combined_kinding_mutind; intros; subst; simpl; econstr eauto.
  - assert (valid_env (E0 & x ~: M & F)) by auto.
    auto using binds_weakening with valid_env_regular.
  - rewrite from_list_cons in *.
    apply valid_scheme_vars_bind; eauto.
    rewrite <- concat_assoc.
    eauto using concat_assoc.
  - apply valid_scheme_c with (L := L \u \{x}).
    introv Hf.
    eauto using fresh_single_notin.
  - assert (empty = E & F) as He by assumption.
    destruct (empty_concat_inv He); subst.
    rewrite concat_empty_r.
    auto.
  - assert (E & X ~:: K = E0 & F) as Heq
      by assumption.
    destruct F using env_ind.
    + autorewrite with rew_env_concat in *; subst.
      auto.
    + rewrite concat_assoc in Heq.
      destruct (eq_push_inv Heq) as [? [? ?]]; subst.
      rewrite concat_assoc.
      eauto.
  - assert (E & x ~: M = E0 & F) as Heq
      by assumption.
    destruct F using env_ind.
    + autorewrite with rew_env_concat in *; subst.
      auto.
    + rewrite concat_assoc in Heq.
      destruct (eq_push_inv Heq) as [? [? ?]]; subst.
      rewrite concat_assoc.
      eauto.
Qed.      

Lemma valid_kind_add_typ_bind : forall E F x M K,
    valid_kind (E & F) K ->
    valid_scheme E M ->
    x # E & F ->
    valid_kind (E & x ~: M & F) K.
Proof.
  introv Hv Hs Hn.
  pose combined_kinding_add_typ_bind.
  intuition eauto.
Qed.

Lemma valid_kind_add_typ_bind_l : forall E x M K,
    valid_kind E K ->
    valid_scheme E M ->
    x # E ->
    valid_kind (E & x ~: M) K.
Proof.
  introv Hv Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M).
  rewrite <- concat_empty_r with (E := E) in Hv.
  eauto using valid_kind_add_typ_bind.
Qed.

Lemma kinding_add_typ_bind : forall E F x M T K,
    kinding (E & F) T K ->
    valid_scheme E M ->
    x # E & F ->
    kinding (E & x ~: M & F) T K.
Proof.
  introv Hk Hs Hn.
  pose combined_kinding_add_typ_bind.
  intuition eauto.
Qed.

Lemma kinding_add_typ_bind_l : forall E x M T K,
    kinding E T K ->
    valid_scheme E M ->
    x # E ->
    kinding (E & x ~: M) T K.
Proof.
  introv Hk Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M).
  rewrite <- concat_empty_r with (E := E) in Hk.
  eauto using kinding_add_typ_bind.
Qed.

Lemma valid_scheme_vars_add_typ_bind : forall E F x M Ms Xs,
    valid_scheme_vars (E & F) Ms Xs ->
    valid_scheme E M ->
    x # E & F ->
    x \notin (from_list Xs) ->
    valid_scheme_vars (E & x ~: M & F) Ms Xs.
Proof.
  introv Hk Hs Hn1 Hn2.
  pose combined_kinding_add_typ_bind.
  intuition eauto.
Qed.

Lemma valid_scheme_vars_add_typ_bind_l : forall E x M Ms Xs,
    valid_scheme_vars E Ms Xs ->
    valid_scheme E M ->
    x # E ->
    x \notin (from_list Xs) ->
    valid_scheme_vars (E & x ~: M) Ms Xs.
Proof.
  introv Hv Hs Hn1 Hn2.
  rewrite <- concat_empty_r with (E := E & x ~: M).
  rewrite <- concat_empty_r with (E := E) in Hv.
  eauto using valid_scheme_vars_add_typ_bind.
Qed.

Lemma valid_scheme_add_typ_bind : forall E F x M Ms,
    valid_scheme (E & F) Ms ->
    valid_scheme E M ->
    x # E & F ->
    valid_scheme (E & x ~: M & F) Ms.
Proof.
  introv Hk Hs Hn.
  pose combined_kinding_add_typ_bind.
  intuition eauto.
Qed.

Lemma valid_scheme_add_typ_bind_l : forall E x M Ms,
    valid_scheme E Ms ->
    valid_scheme E M ->
    x # E ->
    valid_scheme (E & x ~: M) Ms.
Proof.
  introv Hv Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M).
  rewrite <- concat_empty_r with (E := E) in Hv.
  eauto using valid_scheme_add_typ_bind.
Qed.

Lemma valid_env_add_typ_bind : forall E F x M,
    valid_env (E & F) ->
    valid_scheme E M ->
    x # E & F ->
    valid_env (E & x ~: M & F).
Proof.
  introv Hk Hs Hn.
  pose combined_kinding_add_typ_bind.
  intuition eauto.
Qed.

Lemma valid_env_add_typ_bind_l : forall E x M,
    valid_env E ->
    valid_scheme E M ->
    x # E ->
    valid_env (E & x ~: M).
Proof.
  introv Hv Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M).
  rewrite <- concat_empty_r with (E := E) in Hv.
  eauto using valid_env_add_typ_bind.
Qed.

Lemma type_equal_core_add_typ_bind : forall E F x M T1 T2 K,
    type_equal_core (E & F) T1 T2 K ->
    valid_scheme E M ->
    x # E & F ->
    type_equal_core (E & x ~: M & F) T1 T2 K.
Proof.
  introv Hte Hs Hn.
  pose combined_kinding_add_typ_bind.
  intuition eauto.
Qed.

Lemma type_equal_core_add_typ_bind_l : forall E x M T1 T2 K,
    type_equal_core E T1 T2 K ->
    valid_scheme E M ->
    x # E ->
    type_equal_core (E & x ~: M) T1 T2 K.
Proof.
  introv Hv Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M).
  rewrite <- concat_empty_r with (E := E) in Hv.
  eauto using type_equal_core_add_typ_bind.
Qed.

Lemma type_equal_symm_add_typ_bind : forall E F x M T1 T2 K,
    type_equal_symm (E & F) T1 T2 K ->
    valid_scheme E M ->
    x # E & F ->
    type_equal_symm (E & x ~: M & F) T1 T2 K.
Proof.
  introv Hte Hs Hn.
  pose combined_kinding_add_typ_bind.
  intuition eauto.
Qed.

Lemma type_equal_symm_add_typ_bind_l : forall E x M T1 T2 K,
    type_equal_symm E T1 T2 K ->
    valid_scheme E M ->
    x # E ->
    type_equal_symm (E & x ~: M) T1 T2 K.
Proof.
  introv Hv Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M).
  rewrite <- concat_empty_r with (E := E) in Hv.
  eauto using type_equal_symm_add_typ_bind.
Qed.

Lemma type_equal_cong_add_typ_bind : forall E F x M T1 T2 K,
    type_equal_cong (E & F) T1 T2 K ->
    valid_scheme E M ->
    x # E & F ->
    type_equal_cong (E & x ~: M & F) T1 T2 K.
Proof.
  introv Hte Hs Hn.
  pose combined_kinding_add_typ_bind.
  intuition eauto.
Qed.

Lemma type_equal_cong_add_typ_bind_l : forall E x M T1 T2 K,
    type_equal_cong E T1 T2 K ->
    valid_scheme E M ->
    x # E ->
    type_equal_cong (E & x ~: M) T1 T2 K.
Proof.
  introv Hv Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M).
  rewrite <- concat_empty_r with (E := E) in Hv.
  eauto using type_equal_cong_add_typ_bind.
Qed.

Lemma type_equal_add_typ_bind : forall E F x M T1 T2 K,
    type_equal (E & F) T1 T2 K ->
    valid_scheme E M ->
    x # E & F ->
    type_equal (E & x ~: M & F) T1 T2 K.
Proof.
  introv Hte Hs Hn.
  pose combined_kinding_add_typ_bind.
  intuition eauto.
Qed.

Lemma type_equal_add_typ_bind_l : forall E x M T1 T2 K,
    type_equal E T1 T2 K ->
    valid_scheme E M ->
    x # E ->
    type_equal (E & x ~: M) T1 T2 K.
Proof.
  introv Hv Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M).
  rewrite <- concat_empty_r with (E := E) in Hv.
  eauto using type_equal_add_typ_bind.
Qed.

Lemma subtype_add_typ_bind : forall E F x M T1 T2 cs,
    subtype (E & F) T1 T2 cs ->
    valid_scheme E M ->
    x # E & F ->
    subtype (E & x ~: M & F) T1 T2 cs.
Proof.
  introv Hs Hsc Hn.
  pose combined_kinding_add_typ_bind.
  intuition eauto.
Qed.

Lemma subtype_add_typ_bind_l : forall E x M T1 T2 cs,
    subtype E T1 T2 cs ->
    valid_scheme E M ->
    x # E ->
    subtype (E & x ~: M) T1 T2 cs.
Proof.
  introv Hv Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M).
  rewrite <- concat_empty_r with (E := E) in Hv.
  eauto using subtype_add_typ_bind.
Qed.

Lemma valid_instance_add_typ_bind : forall E F x M1 Ts M2,
    valid_instance (E & F) Ts M2 ->
    valid_scheme E M1 ->
    x # E & F ->
    valid_instance (E & x ~: M1 & F) Ts M2.
Proof.
  introv Hv Hs Hn.
  remember (E & x ~: M1 & F) as ExF.
  remember (E & F) as EF.
  induction Hv; subst; eauto using kinding_add_typ_bind.
Qed.

Lemma valid_instance_add_typ_bind_l : forall E x M1 Ts M2,
    valid_instance E Ts M2 ->
    valid_scheme E M1 ->
    x # E ->
    valid_instance (E & x ~: M1) Ts M2.
Proof.
  introv Hv Hs Hn.
  rewrite <- concat_empty_r with (E := E & x ~: M1).
  rewrite <- concat_empty_r with (E := E) in Hv.
  eauto using valid_instance_add_typ_bind.
Qed.

(* *************************************************************** *)
(** Can swap type bindings *)

Lemma environment_middle_inv : forall E F x b,
    environment (E & x ~ b & F) ->
    x # (E & F).
Proof.
  introv He.
  assert (ok (E & x ~ b & F)) as Hok
    by auto using ok_from_environment.
  destruct (ok_middle_inv Hok).
  auto.
Qed.

Lemma valid_kind_swap_typ_bind : forall E F x M1 M2 K,
    valid_kind (E & x ~: M1 & F) K ->
    valid_scheme E M2 ->
    valid_kind (E & x ~: M2 & F) K.
Proof.
  introv Hk Hs.
  apply valid_kind_add_typ_bind;
    eauto
      using valid_kind_remove_typ_bind, environment_middle_inv
      with valid_kind_regular.
Qed.

Lemma kinding_swap_typ_bind : forall E F x M1 M2 T K,
    kinding (E & x ~: M1 & F) T K ->
    valid_scheme E M2 ->
    kinding (E & x ~: M2 & F) T K.
Proof.
  introv Hk Hs.
  apply kinding_add_typ_bind;
    eauto
      using kinding_remove_typ_bind, environment_middle_inv
      with kinding_regular.
Qed.

Lemma valid_scheme_swap_typ_bind : forall E F x M1 M2 Ms,
    valid_scheme (E & x ~: M1 & F) Ms ->
    valid_scheme E M2 ->
    valid_scheme (E & x ~: M2 & F) Ms.
Proof.
  introv Hs1 Hs2.
  apply valid_scheme_add_typ_bind;
    eauto
      using valid_scheme_remove_typ_bind, environment_middle_inv
      with valid_scheme_regular.
Qed.

Lemma valid_env_swap_typ_bind : forall E F x M1 M2,
    valid_env (E & x ~: M1 & F) ->
    valid_scheme E M2 ->
    valid_env (E & x ~: M2 & F).
Proof.
  introv He Hs.
  apply valid_env_add_typ_bind;
    eauto
      using valid_env_remove_typ_bind, environment_middle_inv
      with valid_env_regular.
Qed.  

Lemma type_equal_swap_typ_bind : forall E F x M1 M2 T1 T2 K,
    type_equal (E & x ~: M1 & F) T1 T2 K ->
    valid_scheme E M2 ->
    type_equal (E & x ~: M2 & F) T1 T2 K.
Proof.
  introv Hte Hs.
  apply type_equal_add_typ_bind;
    eauto
      using type_equal_remove_typ_bind, environment_middle_inv
      with type_equal_regular.
Qed.

Lemma subtype_swap_typ_bind : forall E F x M1 M2 T1 T2 cs,
    subtype (E & x ~: M1 & F) T1 T2 cs ->
    valid_scheme E M2 ->
    subtype (E & x ~: M2 & F) T1 T2 cs.
Proof.
  introv Hs Hsc.
  apply subtype_add_typ_bind;
    eauto
      using subtype_remove_typ_bind, environment_middle_inv
      with subtype_regular.
Qed.

Lemma valid_instance_swap_typ_bind : forall E F x M1 M2 Ts M3,
    valid_instance (E & x ~: M1 & F) Ts M3 ->
    valid_scheme E M2 ->
    valid_instance (E & x ~: M2 & F) Ts M3.
Proof.
  introv Hs Hsc.
  apply valid_instance_add_typ_bind;
    eauto
      using valid_instance_remove_typ_bind, environment_middle_inv
      with valid_instance_regular.
Qed.

(* *************************************************************** *)
(** Kinding of schemes with no parameters *)

Lemma valid_scheme_empty_type : forall E T,
    valid_scheme E (sch_empty T) <-> kinding E T knd_type.
Proof.
  split.
  - intro Hv.
    remember (sch_empty T) as M.
    destruct Hv; subst.
    simpl in *.
    assert (valid_scheme_vars E (sch_empty T) nil) as Hv by auto.
    inversion Hv.
    auto.
  - introv Hk.
    apply valid_scheme_c with (L := typ_fv T).
    introv Hf.
    simpl in Hf.
    fresh_length Hf as Hl.
    destruct Xs; simpl in Hl; try discriminate.
    auto.
Qed.

(* *************************************************************** *)
(** * "Validated" versions of kinding judgements *)

Inductive valid_kind_validated : env -> knd -> Prop :=
  | valid_kind_validated_type : forall E,
      valid_env_validated E ->
      environment E ->
      valid_kind_validated E knd_type
  | valid_kind_validated_row :  forall E cs,
      valid_env_validated E ->
      CSet.Nonempty cs ->
      environment E ->
      valid_kind_validated E (knd_row cs)
  | valid_kind_validated_range : forall E T1 T2,
      subtype_validated E T2 T1 CSet.universe ->
      environment E ->
      type T1 ->
      type T2 ->
      valid_env_validated E ->
      kinding_validated E T1 (knd_row CSet.universe) ->
      kinding_validated E T2 (knd_row CSet.universe) ->
      valid_kind_validated E (knd_range T1 T2)

with kinding_validated : env -> typ -> knd -> Prop :=
  | kinding_validated_var : forall E X K,
      valid_env_validated E ->
      binds X (bind_knd K) E ->
      environment E ->
      kind K ->
      valid_kind_validated E K ->
      kinding_validated E (typ_fvar X) K
  | kinding_validated_constructor : forall E c T cs,
      kinding_validated E T knd_type ->
      cs = CSet.singleton c ->
      environment E ->
      type T ->
      valid_env_validated E ->
      kinding_validated E (typ_constructor c T) (knd_row cs)
  | kinding_validated_or : forall E T1 T2 cs1 cs2 cs12,
      kinding_validated E T1 (knd_row cs1) ->
      kinding_validated E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      valid_env_validated E ->
      kinding_validated E (typ_or cs1 T1 cs2 T2) (knd_row cs12)
  | kinding_validated_proj : forall E T cs cs',
      kinding_validated E T (knd_row cs) ->
      CSet.Subset cs' cs ->
      CSet.Nonempty cs' ->
      environment E ->
      type T ->
      CSet.Nonempty cs ->
      valid_env_validated E ->
      kinding_validated E (typ_proj cs T cs') (knd_row cs')
  | kinding_validated_row : forall E T,
      kinding_validated E T (knd_row CSet.universe) ->
      environment E ->
      type T ->
      valid_env_validated E ->
      valid_kind_validated E (knd_range T T) ->
      kinding_validated E (typ_row T) (knd_range T T)
  | kinding_validated_variant : forall E T,
      kinding_validated E T
        (knd_range (typ_top CSet.universe) (typ_bot CSet.universe)) ->
      environment E ->
      type T ->
      valid_env_validated E ->
      kinding_validated E (typ_variant T) knd_type
  | kinding_validated_arrow : forall E T1 T2,
      kinding_validated E T1 knd_type -> 
      kinding_validated E T2 knd_type -> 
      environment E ->
      type T1 ->
      type T2 ->
      valid_env_validated E ->
      kinding_validated E (typ_arrow T1 T2) knd_type
  | kinding_validated_top : forall E cs,
      valid_env_validated E ->
      CSet.Nonempty cs ->
      environment E ->
      valid_env_validated E ->
      kinding_validated E (typ_top cs) (knd_row cs)
  | kinding_validated_bot : forall E cs,
      valid_env_validated E ->
      CSet.Nonempty cs ->
      environment E ->
      valid_env_validated E ->
      kinding_validated E (typ_bot cs) (knd_row cs)
  | kinding_validated_meet : forall E T1 T2 cs,
      kinding_validated E T1 (knd_row cs) ->
      kinding_validated E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env_validated E ->
      kinding_validated E (typ_meet T1 T2) (knd_row cs)
  | kinding_validated_join : forall E T1 T2 cs,
      kinding_validated E T1 (knd_row cs) ->
      kinding_validated E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env_validated E ->
      kinding_validated E (typ_join T1 T2) (knd_row cs)
  | kinding_validated_range_subsumption : forall E T T1 T2 T1' T2',
      kinding_validated E T (knd_range T1 T2) ->
      subtype_validated E T1 T1' CSet.universe ->
      subtype_validated E T2' T2 CSet.universe ->
      environment E ->
      type T ->
      type T1 ->
      type T2 ->
      type T1' ->
      type T2' ->
      valid_env_validated E ->
      kinding_validated E T1 (knd_row CSet.universe) ->
      kinding_validated E T1' (knd_row CSet.universe) ->
      kinding_validated E T2 (knd_row CSet.universe) ->
      kinding_validated E T2' (knd_row CSet.universe) ->
      subtype_validated E T2 T1 CSet.universe ->
      subtype_validated E T2' T1' CSet.universe ->
      valid_kind_validated E (knd_range T1 T2) ->
      valid_kind_validated E (knd_range T1' T2') ->
      kinding_validated E T (knd_range T1' T2')

with valid_scheme_vars_validated : env -> sch -> list var -> Prop :=
  | valid_scheme_vars_validated_empty : forall E T,
      kinding_validated E T knd_type ->
      environment E ->
      type T ->
      valid_env_validated E ->
      valid_scheme_vars_validated E (sch_empty T) nil
  | valid_scheme_vars_validated_bind : forall X Xs E K M,
      valid_kind_validated E K ->
      valid_scheme_vars_validated (E & X ~:: K) (M ^ X) Xs ->
      environment E ->
      environment (E & X ~:: K) ->
      kind K ->
      scheme_vars (M ^ X) Xs ->
      scheme_vars (sch_bind K M) (X :: Xs) ->
      valid_env_validated E ->
      valid_env_validated (E & X ~:: K) ->
      valid_scheme_vars_validated E (sch_bind K M) (X :: Xs)

with valid_scheme_validated : env -> sch -> Prop :=
  | valid_scheme_validated_c : forall E M L,
      (forall Xs,
          fresh L (sch_arity M) Xs ->
          valid_scheme_vars_validated E M Xs) ->
      environment E ->
      scheme M ->
      valid_env_validated E ->
      valid_scheme_validated E M

with valid_env_validated : env -> Prop :=
  | valid_env_validated_empty :
      valid_env_validated empty
  | valid_env_validated_kind : forall E X K,
      valid_env_validated E ->
      valid_kind_validated E K ->
      X # E ->
      environment E ->
      environment (E & X ~:: K) ->
      kind K ->
      valid_env_validated (E & X ~:: K)
  | valid_env_validated_type : forall E x M,
      valid_env_validated E ->
      valid_scheme_validated E M ->
      x # E ->
      environment E ->
      environment (E & x ~: M) ->
      scheme M ->
      valid_env_validated (E & x ~: M)

with type_equal_core_validated : env -> typ -> typ -> knd -> Prop :=
  | type_equal_core_validated_or_commutative :
      forall E T1 T2 cs1 cs2 cs12,
      kinding_validated E T1 (knd_row cs1) ->
      kinding_validated E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      valid_env_validated E ->
      type_equal_core_validated E
        (typ_or cs1 T1 cs2 T2) (typ_or cs2 T2 cs1 T1) (knd_row cs12)
  | type_equal_core_validated_or_associative :
      forall E T1 cs1 T2 cs2 T3 cs3 cs12 cs23 cs123,
      kinding_validated E T1 (knd_row cs1) ->
      kinding_validated E T2 (knd_row cs2) ->
      kinding_validated E T3 (knd_row cs3) ->
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
      valid_env_validated E ->
      type_equal_core_validated E
        (typ_or cs1 T1 cs23 (typ_or cs2 T2 cs3 T3))
        (typ_or cs12 (typ_or cs1 T1 cs2 T2) cs3 T3)
        (knd_row cs123)
  | type_equal_core_validated_or_bot : forall E cs1 cs2 cs12,
      valid_env_validated E ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type_equal_core_validated E
        (typ_or cs1 (typ_bot cs1) cs2 (typ_bot cs2)) (typ_bot cs12)
        (knd_row cs12)
  | type_equal_core_validated_or_top : forall E cs1 cs2 cs12,
      valid_env_validated E ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type_equal_core_validated E
        (typ_or cs1 (typ_top cs1) cs2 (typ_top cs2)) (typ_top cs12)
        (knd_row cs12)
  | type_equal_core_validated_or_meet_distribution :
      forall E T1 T2 T3 T4 cs1 cs2 cs12,
      kinding_validated E T1 (knd_row cs1) ->
      kinding_validated E T2 (knd_row cs2) ->
      kinding_validated E T3 (knd_row cs1) ->
      kinding_validated E T4 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      type T4 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      valid_env_validated E ->
      type_equal_core_validated E
        (typ_or cs1 (typ_meet T1 T3) cs2 (typ_meet T2 T4))
        (typ_meet (typ_or cs1 T1 cs2 T2) (typ_or cs1 T3 cs2 T4))
        (knd_row cs12)
  | type_equal_core_validated_or_join_distribution :
      forall E T1 T2 T3 T4 cs1 cs2 cs12,
      kinding_validated E T1 (knd_row cs1) ->
      kinding_validated E T2 (knd_row cs2) ->
      kinding_validated E T3 (knd_row cs1) ->
      kinding_validated E T4 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      type T4 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      valid_env_validated E ->
      type_equal_core_validated E
        (typ_or cs1 (typ_join T1 T3) cs2 (typ_join T2 T4))
        (typ_join (typ_or cs1 T1 cs2 T2) (typ_or cs1 T3 cs2 T4))
        (knd_row cs12)
  | type_equal_core_validated_or_proj : forall E T cs1 cs2 cs3 cs23,
      kinding_validated E T (knd_row cs1) ->
      CSet.Disjoint cs2 cs3 ->
      CSet.Subset cs2 cs1 ->
      CSet.Nonempty cs2 ->
      CSet.Subset cs3 cs1 ->
      CSet.Nonempty cs3 ->
      cs23 = CSet.union cs2 cs3 ->
      environment E ->
      type T ->
      CSet.Nonempty cs1 ->
      valid_env_validated E ->
      type_equal_core_validated E
        (typ_or cs2 (typ_proj cs1 T cs2) cs3 (typ_proj cs1 T cs3))
        (typ_proj cs1 T cs23)
        (knd_row cs23)
  | type_equal_core_validated_proj_id : forall E T cs,
      kinding_validated E T (knd_row cs) ->
      environment E ->
      type T ->
      CSet.Nonempty cs ->
      valid_env_validated E ->
      type_equal_core_validated E (typ_proj cs T cs) T (knd_row cs)
  | type_equal_core_validated_proj_or_l :
      forall E T1 T2 cs1 cs1' cs2 cs12,
      kinding_validated E T1 (knd_row cs1) ->
      kinding_validated E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      CSet.Subset cs1' cs1 ->
      CSet.Nonempty cs1' ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      valid_env_validated E ->
      type_equal_core_validated E
        (typ_proj cs12 (typ_or cs1 T1 cs2 T2) cs1')
        (typ_proj cs1 T1 cs1')
        (knd_row cs1')
  | type_equal_core_validated_proj_or_r :
      forall E T1 T2 cs1 cs2 cs2' cs12,
      kinding_validated E T1 (knd_row cs1) ->
      kinding_validated E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      CSet.Subset cs2' cs2 ->
      CSet.Nonempty cs2' ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      valid_env_validated E ->
      type_equal_core_validated E
        (typ_proj cs12 (typ_or cs1 T1 cs2 T2) cs2')
        (typ_proj cs2 T2 cs2')
        (knd_row cs2')
  | type_equal_core_validated_proj_or_both :
      forall E T1 T2 cs1 cs2 cs1' cs2' cs12 cs12',
      kinding_validated E T1 (knd_row cs1) ->
      kinding_validated E T2 (knd_row cs2) ->
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
      valid_env_validated E ->
      type_equal_core_validated E
        (typ_proj cs12 (typ_or cs1 T1 cs2 T2) cs12')
        (typ_or cs1' (typ_proj cs1 T1 cs1')
                cs2' (typ_proj cs2 T2 cs2'))
        (knd_row cs12')
  | type_equal_core_validated_proj_meet : forall E T1 T2 cs cs',
      kinding_validated E T1 (knd_row cs) ->
      kinding_validated E T2 (knd_row cs) ->
      CSet.Subset cs' cs ->
      CSet.Nonempty cs' ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env_validated E ->
      type_equal_core_validated E
        (typ_proj cs (typ_meet T1 T2) cs')
        (typ_meet (typ_proj cs T1 cs') (typ_proj cs T2 cs'))
        (knd_row cs')
  | type_equal_core_validated_proj_join : forall E T1 T2 cs cs',
      kinding_validated E T1 (knd_row cs) ->
      kinding_validated E T2 (knd_row cs) ->
      CSet.Subset cs' cs ->
      CSet.Nonempty cs' ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env_validated E ->
      type_equal_core_validated E
        (typ_proj cs (typ_join T1 T2) cs')
        (typ_join (typ_proj cs T1 cs') (typ_proj cs T2 cs'))
        (knd_row cs')
  | type_equal_core_validated_meet_commutative : forall E T1 T2 cs,
      kinding_validated E T1 (knd_row cs) ->
      kinding_validated E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env_validated E ->
      type_equal_core_validated E
        (typ_meet T1 T2) (typ_meet T2 T1) (knd_row cs)
  | type_equal_core_validated_meet_associative : forall E T1 T2 T3 cs,
      kinding_validated E T1 (knd_row cs) ->
      kinding_validated E T2 (knd_row cs) ->
      kinding_validated E T3 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      CSet.Nonempty cs ->
      valid_env_validated E ->
      type_equal_core_validated E
        (typ_meet T1 (typ_meet T2 T3))
        (typ_meet (typ_meet T1 T2) T3)
        (knd_row cs)
  | type_equal_core_validated_meet_identity : forall E T1 cs,
      kinding_validated E T1 (knd_row cs) ->
      environment E ->
      type T1 ->
      CSet.Nonempty cs ->
      valid_env_validated E ->
      type_equal_core_validated E
        (typ_meet T1 (typ_top cs)) T1 (knd_row cs)
  | type_equal_core_validated_meet_absorption : forall E T1 T2 cs,
      kinding_validated E T1 (knd_row cs) ->
      kinding_validated E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env_validated E ->
      type_equal_core_validated E
        (typ_meet T1 (typ_join T1 T2)) T1 (knd_row cs)
  | type_equal_core_validated_meet_distribution :
      forall E T1 T2 T3 cs,
      kinding_validated E T1 (knd_row cs) ->
      kinding_validated E T2 (knd_row cs) ->
      kinding_validated E T3 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      CSet.Nonempty cs ->
      valid_env_validated E ->
      type_equal_core_validated E
        (typ_meet T1 (typ_join T2 T3))
        (typ_join (typ_meet T1 T2) (typ_meet T1 T3))
        (knd_row cs)
  | type_equal_core_validated_join_commutative : forall E T1 T2 cs,
      kinding_validated E T1 (knd_row cs) ->
      kinding_validated E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env_validated E ->
      type_equal_core_validated E
        (typ_join T1 T2) (typ_join T2 T1) (knd_row cs)
  | type_equal_core_validated_join_associative : forall E T1 T2 T3 cs,
      kinding_validated E T1 (knd_row cs) ->
      kinding_validated E T2 (knd_row cs) ->
      kinding_validated E T3 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      CSet.Nonempty cs ->
      valid_env_validated E ->
      type_equal_core_validated E
        (typ_join T1 (typ_join T2 T3))
        (typ_join (typ_join T1 T2) T3)
        (knd_row cs)
  | type_equal_core_validated_join_identity : forall E T1 cs,
      kinding_validated E T1 (knd_row cs) ->
      environment E ->
      type T1 ->
      CSet.Nonempty cs ->
      valid_env_validated E ->
      type_equal_core_validated E
        (typ_join T1 (typ_bot cs)) T1 (knd_row cs)
  | type_equal_core_validated_join_absorption : forall E T1 T2 cs,
      kinding_validated E T1 (knd_row cs) ->
      kinding_validated E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env_validated E ->
      type_equal_core_validated E
        (typ_join T1 (typ_meet T1 T2)) T1 (knd_row cs)
  | type_equal_core_validated_join_distribution :
      forall E T1 T2 T3 cs,
      kinding_validated E T1 (knd_row cs) ->
      kinding_validated E T2 (knd_row cs) ->
      kinding_validated E T3 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      CSet.Nonempty cs ->
      valid_env_validated E ->
      type_equal_core_validated E
        (typ_join T1 (typ_meet T2 T3))
        (typ_meet (typ_join T1 T2) (typ_join T1 T3))
        (knd_row cs)

with type_equal_symm_validated : env -> typ -> typ -> knd -> Prop :=
  | type_equal_symm_validated_l : forall E T1 T2 K,
      type_equal_core_validated E T1 T2 K ->
      environment E ->
      type T1 ->
      type T2 ->
      kind K ->
      valid_env_validated E ->
      kinding_validated E T1 K ->
      kinding_validated E T2 K ->
      valid_kind_validated E K ->
      type_equal_symm_validated E T1 T2 K
  | type_equal_symm_validated_r : forall E T1 T2 K,
      type_equal_core_validated E T1 T2 K ->
      environment E ->
      type T1 ->
      type T2 ->
      kind K ->
      valid_env_validated E ->
      kinding_validated E T1 K ->
      kinding_validated E T2 K ->
      valid_kind_validated E K ->
      type_equal_symm_validated E T2 T1 K

with type_equal_cong_validated : env -> typ -> typ -> knd -> Prop :=
  | type_equal_cong_validated_constructor : forall E c T1 T1' cs,
      type_equal_cong_validated E T1 T1' knd_type ->
      cs = CSet.singleton c ->
      environment E ->
      type T1 ->
      type T1' ->
      valid_env_validated E ->
      kinding_validated E T1 knd_type ->
      kinding_validated E T1' knd_type ->
      type_equal_cong_validated E
        (typ_constructor c T1) (typ_constructor c T1')
        (knd_row cs)
  | type_equal_cong_validated_or_l : forall E T1 T1' T2 cs1 cs2 cs12,
      kinding_validated E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_cong_validated E T1 T1' (knd_row cs1) ->
      environment E ->
      type T1 ->
      type T1' ->
      type T2 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      valid_env_validated E ->
      kinding_validated E T1 (knd_row cs1) ->
      kinding_validated E T1' (knd_row cs1) ->
      type_equal_cong_validated E
        (typ_or cs1 T1 cs2 T2) (typ_or cs1 T1' cs2 T2) (knd_row cs12)
  | type_equal_cong_validated_or_r : forall E T1 T2 T2' cs1 cs2 cs12,
      kinding_validated E T1 (knd_row cs1) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_cong_validated E T2 T2' (knd_row cs2) ->
      environment E ->
      type T1 ->
      type T2 ->
      type T2' ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      valid_env_validated E ->
      kinding_validated E T2 (knd_row cs2) ->
      kinding_validated E T2' (knd_row cs2) ->
      type_equal_cong_validated E
        (typ_or cs1 T1 cs2 T2) (typ_or cs1 T1 cs2 T2') (knd_row cs12)
  | type_equal_cong_validated_row : forall E T1 T1',
      type_equal_cong_validated E T1 T1' (knd_row CSet.universe) ->
      environment E ->
      type T1 ->
      type T1' ->
      valid_env_validated E ->
      kinding_validated E T1 (knd_row CSet.universe) ->
      kinding_validated E T1' (knd_row CSet.universe) ->
      kinding_validated E (typ_row T1') (knd_range T1 T1) ->
      valid_kind_validated E (knd_range T1 T1) ->
      type_equal_cong_validated E
        (typ_row T1) (typ_row T1') (knd_range T1 T1)
  | type_equal_cong_validated_variant : forall E T1 T1',
      type_equal_cong_validated E T1 T1'
        (knd_range (typ_top CSet.universe) (typ_bot CSet.universe)) ->
      environment E ->
      type T1 ->
      type T1' ->
      valid_env_validated E ->
      kinding_validated E T1
        (knd_range (typ_top CSet.universe) (typ_bot CSet.universe)) ->
      kinding_validated E T1'
        (knd_range (typ_top CSet.universe) (typ_bot CSet.universe)) ->
      type_equal_cong_validated E
        (typ_variant T1) (typ_variant T1') knd_type
  | type_equal_cong_validated_arrow_l : forall E T1 T1' T2,
      kinding_validated E T2 knd_type ->
      type_equal_cong_validated E T1 T1' knd_type ->
      environment E ->
      type T1 ->
      type T1' ->
      type T2 ->
      valid_env_validated E ->
      kinding_validated E T1 knd_type ->
      kinding_validated E T1' knd_type ->
      type_equal_cong_validated E
        (typ_arrow T1 T2) (typ_arrow T1' T2) knd_type
  | type_equal_cong_validated_arrow_r : forall E T1 T2 T2',
      kinding_validated E T1 knd_type ->
      type_equal_cong_validated E T2 T2' knd_type ->
      environment E ->
      type T1 ->
      type T2 ->
      type T2' ->
      valid_env_validated E ->
      kinding_validated E T2 knd_type ->
      kinding_validated E T2' knd_type ->
      type_equal_cong_validated E
        (typ_arrow T1 T2) (typ_arrow T1 T2') knd_type
  | type_equal_cong_validated_meet_l : forall E T1 T1' T2 cs,
      kinding_validated E T2 (knd_row cs) ->
      type_equal_cong_validated E T1 T1' (knd_row cs) ->
      environment E ->
      type T1 ->
      type T1' ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env_validated E ->
      kinding_validated E T1 (knd_row cs) ->
      kinding_validated E T1' (knd_row cs) ->
      type_equal_cong_validated E
        (typ_meet T1 T2) (typ_meet T1' T2) (knd_row cs)
  | type_equal_cong_validated_meet_r : forall E T1 T2 T2' cs,
      kinding_validated E T1 (knd_row cs) ->
      type_equal_cong_validated E T2 T2' (knd_row cs) -> 
      environment E ->
      type T1 ->
      type T2 ->
      type T2' ->
      CSet.Nonempty cs ->
      valid_env_validated E ->
      kinding_validated E T2 (knd_row cs) ->
      kinding_validated E T2' (knd_row cs) ->
      type_equal_cong_validated E
        (typ_meet T1 T2) (typ_meet T1 T2') (knd_row cs)
  | type_equal_cong_validated_join_l : forall E T1 T1' T2 cs,
      kinding_validated E T2 (knd_row cs) ->
      type_equal_cong_validated E T1 T1' (knd_row cs) ->
      environment E ->
      type T1 ->
      type T1' ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env_validated E ->
      kinding_validated E T1 (knd_row cs) ->
      kinding_validated E T1' (knd_row cs) ->
      type_equal_cong_validated E
        (typ_join T1 T2) (typ_join T1' T2) (knd_row cs)
  | type_equal_cong_validated_join_r : forall E T1 T2 T2' cs,
      kinding_validated E T1 (knd_row cs) ->
      type_equal_cong_validated E T2 T2' (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      type T2' ->
      CSet.Nonempty cs ->
      valid_env_validated E ->
      kinding_validated E T2 (knd_row cs) ->
      kinding_validated E T2' (knd_row cs) ->
      type_equal_cong_validated E
        (typ_join T1 T2) (typ_join T1 T2') (knd_row cs)
  | type_equal_cong_validated_range_subsumption :
      forall E T1 T2 T3 T4 T3' T4',
      type_equal_cong_validated E T1 T2 (knd_range T3 T4) ->
      subtype_validated E T3 T3' CSet.universe ->
      subtype_validated E T4' T4 CSet.universe ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      type T3' ->
      type T4 ->
      type T4' ->
      valid_env_validated E ->
      kinding_validated E T1 (knd_range T3 T4) ->
      kinding_validated E T2 (knd_range T3 T4) ->
      kinding_validated E T3 (knd_row CSet.universe) ->
      kinding_validated E T3' (knd_row CSet.universe) ->
      kinding_validated E T4 (knd_row CSet.universe) ->
      kinding_validated E T4' (knd_row CSet.universe) ->
      subtype_validated E T4 T3 CSet.universe ->
      subtype_validated E T4' T3' CSet.universe ->
      valid_kind_validated E (knd_range T3 T4) ->
      valid_kind_validated E (knd_range T3' T4') ->
      type_equal_cong_validated E T1 T2 (knd_range T3' T4')
  | type_equal_cong_validated_symm : forall E T1 T1' K,
      type_equal_symm_validated E T1 T1' K ->
      environment E ->
      type T1 ->
      type T1' ->
      kind K ->
      valid_env_validated E ->
      kinding_validated E T1 K ->
      kinding_validated E T1' K ->
      valid_kind_validated E K ->
      type_equal_cong_validated E T1 T1' K

with type_equal_validated : env -> typ -> typ -> knd -> Prop :=
  | type_equal_validated_refl : forall E T K,
      kinding_validated E T K ->
      environment E ->
      type T ->
      kind K ->
      valid_env_validated E ->
      valid_kind_validated E K ->
      type_equal_validated E T T K
  | type_equal_validated_step : forall E T1 T2 T3 K,
      type_equal_cong_validated E T1 T2 K ->
      type_equal_validated E T2 T3 K ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      kind K ->
      valid_env_validated E ->
      kinding_validated E T1 K ->
      kinding_validated E T2 K ->
      kinding_validated E T3 K ->
      valid_kind_validated E K ->
      type_equal_validated E T1 T3 K

with subtype_validated : env -> typ -> typ -> cset -> Prop :=
  | subtype_validated_c : forall E T1 T2 cs,
      type_equal_validated E T1 (typ_meet T1 T2) (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env_validated E ->
      kinding_validated E T1 (knd_row cs) ->
      kinding_validated E T2 (knd_row cs) ->
      subtype_validated E T1 T2 cs.

Scheme valid_kind_validated_mutind :=
         Induction for valid_kind_validated Sort Prop
  with kinding_validated_mutind :=
         Induction for kinding_validated Sort Prop
  with valid_scheme_vars_validated_mutind :=
         Induction for valid_scheme_vars_validated Sort Prop
  with valid_scheme_validated_mutind :=
         Induction for valid_scheme_validated Sort Prop
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
       valid_scheme_vars_validated_mutind,
       valid_scheme_validated_mutind,
       valid_env_validated_mutind, type_equal_core_validated_mutind,
       type_equal_symm_validated_mutind,
       type_equal_cong_validated_mutind,
       type_equal_validated_mutind, subtype_validated_mutind.

Lemma unvalidated_combined_kinding :
  (forall E K, valid_kind_validated E K -> valid_kind E K)
  /\ (forall E T K, kinding_validated E T K -> kinding E T K)
  /\ (forall E M Xs,
         valid_scheme_vars_validated E M Xs -> valid_scheme_vars E M Xs)
  /\ (forall E M, valid_scheme_validated E M -> valid_scheme E M)
  /\ (forall E, valid_env_validated E -> valid_env E)
  /\ (forall E T1 T2 K,
       type_equal_core_validated E T1 T2 K -> type_equal_core E T1 T2 K)
  /\ (forall E T1 T2 K,
       type_equal_symm_validated E T1 T2 K -> type_equal_symm E T1 T2 K)
  /\ (forall E T1 T2 K,
       type_equal_cong_validated E T1 T2 K -> type_equal_cong E T1 T2 K)
  /\ (forall E T1 T2 K,
       type_equal_validated E T1 T2 K -> type_equal E T1 T2 K)
  /\ (forall E T1 T2 cs,
       subtype_validated E T1 T2 cs -> subtype E T1 T2 cs).
Proof.
  apply combined_kinding_validated_mutind;
    intros; subst; econstr auto.
Qed.

Lemma unvalidated_valid_kind : forall E K,
    valid_kind_validated E K -> valid_kind E K.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_valid_kind.

Lemma unvalidated_kinding : forall E T K,
    kinding_validated E T K -> kinding E T K.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_kinding.

Lemma unvalidated_valid_scheme_vars : forall E M Xs,
    valid_scheme_vars_validated E M Xs -> valid_scheme_vars E M Xs.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_valid_scheme_vars.

Lemma unvalidated_valid_scheme : forall E M,
    valid_scheme_validated E M -> valid_scheme E M.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_valid_scheme.

Lemma unvalidated_valid_env : forall E,
    valid_env_validated E -> valid_env E.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_valid_env.

Lemma unvalidated_type_equal_core : forall E T1 T2 K,
    type_equal_core_validated E T1 T2 K -> type_equal_core E T1 T2 K.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_type_equal_core.

Lemma unvalidated_type_equal_symm : forall E T1 T2 K,
    type_equal_symm_validated E T1 T2 K -> type_equal_symm E T1 T2 K.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_type_equal_symm.

Lemma unvalidated_type_equal_cong : forall E T1 T2 K,
    type_equal_cong_validated E T1 T2 K -> type_equal_cong E T1 T2 K.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_type_equal_cong.

Lemma unvalidated_type_equal : forall E T1 T2 K,
    type_equal_validated E T1 T2 K -> type_equal E T1 T2 K.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_type_equal.

Lemma unvalidated_subtype : forall E T1 T2 K,
    subtype_validated E T1 T2 K -> subtype E T1 T2 K.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_subtype.

Lemma valid_kind_validated_inv : forall E K,
    valid_kind_validated E K ->
    valid_env_validated E.
Proof.
  introv Hv.
  induction Hv; auto.
Qed.

Hint Constructors valid_kind_validated : valid_kind_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_kind_validated E _ |- _ =>
      apply (proj1 (valid_kind_regular_inv
               (regular_valid_kind (unvalidated_valid_kind H))))
  end : valid_kind_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : valid_kind_validated _ K |- _ =>
      apply (proj2 (valid_kind_regular_inv
               (regular_valid_kind (unvalidated_valid_kind H))))
  end : valid_kind_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : valid_kind_validated _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj2 (valid_kind_regular_inv
                   (regular_valid_kind (unvalidated_valid_kind H))));
      inversion Hknd; assumption
  end : valid_kind_regular.

Hint Extern 1 (valid_env_validated ?E) =>
  match goal with
  | H : valid_kind_validated E _ |- _ =>
      apply (valid_kind_validated_inv H)
  end : valid_kind_validated.

Hint Extern 1 (valid_env ?E) =>
  match goal with
  | H : valid_kind_validated E _ |- _ =>
      apply (unvalidated_valid_env (valid_kind_validated_inv H))
  end : valid_kind_validated.

Lemma kinding_validated_inv : forall E T K,
    kinding_validated E T K ->
    valid_env_validated E /\ valid_kind_validated E K.
Proof.
  introv Hk.
  split; destruct Hk;
    auto with valid_kind_validated csetdec.
Qed.

Hint Constructors kinding_validated : kinding_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : kinding_validated E _ _ |- _ =>
      apply (proj31 (kinding_regular_inv
               (regular_kinding (unvalidated_kinding H))))
  end : kinding_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : kinding_validated _ T _ |- _ =>
      apply (proj32 (kinding_regular_inv
               (regular_kinding (unvalidated_kinding H))))
  end : kinding_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : kinding_validated _ _ K |- _ =>
      apply (proj33 (kinding_regular_inv 
               (regular_kinding (unvalidated_kinding H))))
  end : kinding_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : kinding_validated _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj33 (kinding_regular_inv 
                    (regular_kinding (unvalidated_kinding H))));
      inversion Hknd; assumption
  end : kinding_regular.

Hint Extern 1 (valid_env_validated ?E) =>
  match goal with
  | H : kinding_validated E _ _ |- _ =>
      apply (proj1 (kinding_validated_inv H))
  end : kinding_validated.

Hint Extern 1 (valid_kind_validated ?E ?K) =>
  match goal with
  | H : kinding_validated E _ K |- _ =>
      apply (proj2 (kinding_validated_inv H))
  end : kinding_validated.

Hint Extern 1 (valid_env ?E) =>
  match goal with
  | H : kinding_validated E _ _ |- _ =>
      apply (unvalidated_valid_env (proj1 (kinding_validated_inv H)))
  end : kinding_validated.

Hint Extern 1 (valid_kind ?E ?K) =>
  match goal with
  | H : kinding_validated E _ K |- _ =>
      apply (unvalidated_valid_kind (proj2 (kinding_validated_inv H)))
  end : kinding_validated.

Lemma valid_scheme_vars_validated_inv : forall E M Xs,
    valid_scheme_vars_validated E M Xs ->
    valid_env_validated E.
Proof.
  introv Hs.
  destruct Hs; auto.
Qed.

Hint Constructors valid_scheme_vars_validated
  : valid_scheme_vars_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_scheme_vars_validated E _ _ |- _ =>
      apply (proj1 (valid_scheme_vars_regular_inv
               (regular_valid_scheme_vars
                  (unvalidated_valid_scheme_vars H))))
  end : valid_scheme_vars_regular.

Hint Extern 1 (scheme_vars ?M ?Xs) =>
  match goal with
  | H : valid_scheme_vars_validated _ M Xs |- _ =>
      apply (proj2 (valid_scheme_vars_regular_inv
               (regular_valid_scheme_vars
                  (unvalidated_valid_scheme_vars H))))
  end : valid_scheme_vars_regular.

Hint Extern 1 (valid_env_validated ?E) =>
  match goal with
  | H : valid_scheme_vars_validated E _ _ |- _ =>
      apply (valid_scheme_vars_validated_inv H)
  end : valid_scheme_vars_validated.

Hint Extern 1 (valid_env ?E) =>
  match goal with
  | H : valid_scheme_vars_validated E _ _ |- _ =>
      apply (unvalidated_valid_env
               (valid_scheme_vars_validated_inv H))
  end : valid_scheme_vars_validated.

Lemma valid_scheme_validated_inv : forall E M,
    valid_scheme_validated E M ->
    valid_env_validated E.
Proof.
  introv Hs.
  destruct Hs; auto.
Qed.

Hint Constructors valid_scheme_validated : valid_scheme_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_scheme_validated E _ |- _ =>
      apply (proj1 (valid_scheme_regular_inv
               (regular_valid_scheme (unvalidated_valid_scheme H))))
  end : valid_scheme_regular.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H : valid_scheme_validated _ M |- _ =>
      apply (proj2 (valid_scheme_regular_inv
               (regular_valid_scheme (unvalidated_valid_scheme H))))
  end : valid_scheme_regular.

Hint Extern 1 (valid_env_validated ?E) =>
  match goal with
  | H : valid_scheme_validated E _ |- _ =>
      apply (valid_scheme_validated_inv H)
  end : valid_scheme_validated.

Hint Extern 1 (valid_env ?E) =>
  match goal with
  | H : valid_scheme_validated E _ |- _ =>
      apply (unvalidated_valid_env (valid_scheme_validated_inv H))
  end : valid_scheme_validated.

Hint Constructors valid_env_validated : valid_env_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_env_validated E |- _ =>
      apply (valid_env_regular_inv
               (regular_valid_env (unvalidated_valid_env H)))
  end : valid_env_regular.

Lemma type_equal_core_validated_inv : forall E T1 T2 K,
    type_equal_core_validated E T1 T2 K ->
    valid_env_validated E
    /\ kinding_validated E T1 K
    /\ kinding_validated E T2 K
    /\ valid_kind_validated E K.
Proof.
  introv Hte.
  destruct Hte; subst; splits;
    auto;
    econstr solve
     [ auto with kinding_validated
     | csetdec
     | eauto with kinding_validated ].
Qed.

Hint Constructors type_equal_core_validated
  : type_equal_core_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_core_validated E _ _ _ |- _ =>
      apply (proj41 (type_equal_core_regular_inv
        (regular_type_equal_core (unvalidated_type_equal_core H))))
  end : type_equal_core_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_core_validated _ T _ _ |- _ =>
      apply (proj42 (type_equal_core_regular_inv
        (regular_type_equal_core (unvalidated_type_equal_core H))))
  | H : type_equal_core_validated _ _ T _ |- _ =>
      apply (proj43 (type_equal_core_regular_inv
        (regular_type_equal_core (unvalidated_type_equal_core H))))
  end : type_equal_core_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_core_validated _ _ _ K |- _ =>
      apply (proj44 (type_equal_core_regular_inv
        (regular_type_equal_core (unvalidated_type_equal_core H))))
  end : type_equal_core_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_core_validated _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_core_regular_inv
         (regular_type_equal_core (unvalidated_type_equal_core H))));
      inversion Hknd; assumption
  end : type_equal_core_regular.

Hint Extern 1 (valid_env_validated ?E) =>
  match goal with
  | H : type_equal_core_validated E _ _ _ |- _ =>
      apply (proj41 (type_equal_core_validated_inv H))
  end : type_equal_core_validated.

Hint Extern 1 (kinding_validated ?E ?T ?K) =>
  match goal with
  | H : type_equal_core_validated E T _ K |- _ =>
      apply (proj42 (type_equal_core_validated_inv H))
  | H : type_equal_core_validated E _ T K |- _ =>
      apply (proj43 (type_equal_core_validated_inv H))
  end : type_equal_core_validated.

Hint Extern 1 (valid_kind_validated ?E ?K) =>
  match goal with
  | H : type_equal_core_validated E _ _ K |- _ =>
      apply (proj44 (type_equal_core_validated_inv H))
  end : type_equal_core_validated.

Hint Extern 1 (valid_env ?E) =>
  match goal with
  | H : type_equal_core_validated E _ _ _ |- _ =>
      apply (unvalidated_valid_env
               (proj41 (type_equal_core_validated_inv H)))
  end : type_equal_core_regular.

Hint Extern 1 (kinding ?E ?T ?K) =>
  match goal with
  | H : type_equal_core_validated E T _ K |- _ =>
      apply (unvalidated_kinding
               (proj42 (type_equal_core_validated_inv H)))
  | H : type_equal_core_validated E _ T K |- _ =>
      apply (unvalidated_kinding
               (proj43 (type_equal_core_validated_inv H)))
  end : type_equal_core_validated.

Hint Extern 1 (valid_kind ?E ?K) =>
  match goal with
  | H : type_equal_core_validated E _ _ K |- _ =>
      apply (unvalidated_valid_kind
               (proj44 (type_equal_core_validated_inv H)))
  end : type_equal_core_validated.

Lemma type_equal_symm_validated_inv : forall E T1 T2 K,
    type_equal_symm_validated E T1 T2 K ->
    valid_env_validated E
    /\ kinding_validated E T1 K
    /\ kinding_validated E T2 K
    /\ valid_kind_validated E K.
Proof.
  introv Hte.
  destruct Hte; auto.
Qed.

Hint Constructors type_equal_symm_validated
  : type_equal_symm_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_symm_validated E _ _ _ |- _ =>
      apply (proj41 (type_equal_symm_regular_inv
        (regular_type_equal_symm (unvalidated_type_equal_symm H))))
  end : type_equal_symm_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_symm_validated _ T _ _ |- _ =>
      apply (proj42 (type_equal_symm_regular_inv
        (regular_type_equal_symm (unvalidated_type_equal_symm H))))
  | H : type_equal_symm_validated _ _ T _ |- _ =>
      apply (proj43 (type_equal_symm_regular_inv
        (regular_type_equal_symm (unvalidated_type_equal_symm H))))
  end : type_equal_symm_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_symm_validated _ _ _ K |- _ =>
      apply (proj44 (type_equal_symm_regular_inv
        (regular_type_equal_symm (unvalidated_type_equal_symm H))))
  end : type_equal_symm_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_symm_validated _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_symm_regular_inv
         (regular_type_equal_symm (unvalidated_type_equal_symm H))));
      inversion Hknd; assumption
  end : type_equal_symm_regular.

Hint Extern 1 (valid_env_validated ?E) =>
  match goal with
  | H : type_equal_symm_validated E _ _ _ |- _ =>
      apply (proj41 (type_equal_symm_validated_inv H))
  end : type_equal_symm_validated.

Hint Extern 1 (kinding_validated ?E ?T ?K) =>
  match goal with
  | H : type_equal_symm_validated E T _ K |- _ =>
      apply (proj42 (type_equal_symm_validated_inv H))
  | H : type_equal_symm_validated E _ T K |- _ =>
      apply (proj43 (type_equal_symm_validated_inv H))
  end : type_equal_symm_validated.

Hint Extern 1 (valid_kind_validated ?E ?K) =>
  match goal with
  | H : type_equal_symm_validated E _ _ K |- _ =>
      apply (proj44 (type_equal_symm_validated_inv H))
  end : type_equal_symm_validated.

Hint Extern 1 (valid_env ?E) =>
  match goal with
  | H : type_equal_symm_validated E _ _ _ |- _ =>
      apply (unvalidated_valid_env
               (proj41 (type_equal_symm_validated_inv H)))
  end : type_equal_symm_regular.

Hint Extern 1 (kinding ?E ?T ?K) =>
  match goal with
  | H : type_equal_symm_validated E T _ K |- _ =>
      apply (unvalidated_kinding
               (proj42 (type_equal_symm_validated_inv H)))
  | H : type_equal_symm_validated E _ T K |- _ =>
      apply (unvalidated_kinding
               (proj43 (type_equal_symm_validated_inv H)))
  end : type_equal_symm_validated.

Hint Extern 1 (valid_kind ?E ?K) =>
  match goal with
  | H : type_equal_symm_validated E _ _ K |- _ =>
      apply (unvalidated_valid_kind
               (proj44 (type_equal_symm_validated_inv H)))
  end : type_equal_symm_validated.

Lemma type_equal_cong_validated_inv : forall E T1 T2 K,
    type_equal_cong_validated E T1 T2 K ->
    valid_env_validated E
    /\ kinding_validated E T1 K
    /\ kinding_validated E T2 K
    /\ valid_kind_validated E K.
Proof.
  introv Hte.
  destruct Hte; splits;
    auto with valid_kind_validated kinding_validated csetdec;
    eauto with kinding_validated.
Qed.

Hint Constructors type_equal_cong_validated
  : type_equal_cong_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_cong_validated E _ _ _ |- _ =>
      apply (proj41 (type_equal_cong_regular_inv
        (regular_type_equal_cong (unvalidated_type_equal_cong H))))
  end : type_equal_cong_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_cong_validated _ T _ _ |- _ =>
      apply (proj42 (type_equal_cong_regular_inv
        (regular_type_equal_cong (unvalidated_type_equal_cong H))))
  | H : type_equal_cong_validated _ _ T _ |- _ =>
      apply (proj43 (type_equal_cong_regular_inv
        (regular_type_equal_cong (unvalidated_type_equal_cong H))))
  end : type_equal_cong_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_cong_validated _ _ _ K |- _ =>
      apply (proj44 (type_equal_cong_regular_inv
        (regular_type_equal_cong (unvalidated_type_equal_cong H))))
  end : type_equal_cong_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_cong_validated _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_cong_regular_inv
         (regular_type_equal_cong (unvalidated_type_equal_cong H))));
      inversion Hknd; assumption
  end : type_equal_cong_regular.

Hint Extern 1 (valid_env_validated ?E) =>
  match goal with
  | H : type_equal_cong_validated E _ _ _ |- _ =>
      apply (proj41 (type_equal_cong_validated_inv H))
  end : type_equal_cong_validated.

Hint Extern 1 (kinding_validated ?E ?T ?K) =>
  match goal with
  | H : type_equal_cong_validated E T _ K |- _ =>
      apply (proj42 (type_equal_cong_validated_inv H))
  | H : type_equal_cong_validated E _ T K |- _ =>
      apply (proj43 (type_equal_cong_validated_inv H))
  end : type_equal_cong_validated.

Hint Extern 1 (valid_kind_validated ?E ?K) =>
  match goal with
  | H : type_equal_cong_validated E _ _ K |- _ =>
      apply (proj44 (type_equal_cong_validated_inv H))
  end : type_equal_cong_validated.

Hint Extern 1 (valid_env ?E) =>
  match goal with
  | H : type_equal_cong_validated E _ _ _ |- _ =>
      apply (unvalidated_valid_env
               (proj41 (type_equal_cong_validated_inv H)))
  end : type_equal_cong_regular.

Hint Extern 1 (kinding ?E ?T ?K) =>
  match goal with
  | H : type_equal_cong_validated E T _ K |- _ =>
      apply (unvalidated_kinding
               (proj42 (type_equal_cong_validated_inv H)))
  | H : type_equal_cong_validated E _ T K |- _ =>
      apply (unvalidated_kinding
               (proj43 (type_equal_cong_validated_inv H)))
  end : type_equal_cong_validated.

Hint Extern 1 (valid_kind ?E ?K) =>
  match goal with
  | H : type_equal_cong_validated E _ _ K |- _ =>
      apply (unvalidated_valid_kind
               (proj44 (type_equal_cong_validated_inv H)))
  end : type_equal_cong_validated.

Lemma type_equal_validated_inv : forall E T1 T2 K,
    type_equal_validated E T1 T2 K ->
    valid_env_validated E
    /\ kinding_validated E T1 K
    /\ kinding_validated E T2 K
    /\ valid_kind_validated E K.
Proof.
  introv Hk.
  destruct Hk; auto.
Qed.

Hint Constructors type_equal_validated : type_equal_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_validated E _ _ _ |- _ =>
      apply (proj41 (type_equal_regular_inv
        (regular_type_equal (unvalidated_type_equal H))))
  end : type_equal_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_validated _ T _ _ |- _ =>
      apply (proj42 (type_equal_regular_inv
        (regular_type_equal (unvalidated_type_equal H))))
  | H : type_equal_validated _ _ T _ |- _ =>
      apply (proj43 (type_equal_regular_inv
        (regular_type_equal (unvalidated_type_equal H))))
  end : type_equal_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_validated _ _ _ K |- _ =>
      apply (proj44 (type_equal_regular_inv
        (regular_type_equal (unvalidated_type_equal H))))
  end : type_equal_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_validated _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_regular_inv
         (regular_type_equal (unvalidated_type_equal H))));
      inversion Hknd; assumption
  end : type_equal_regular.

Hint Extern 1 (valid_env_validated ?E) =>
  match goal with
  | H : type_equal_validated E _ _ _ |- _ =>
      apply (proj41 (type_equal_validated_inv H))
  end : type_equal_validated.

Hint Extern 1 (kinding_validated ?E ?T ?K) =>
  match goal with
  | H : type_equal_validated E T _ K |- _ =>
      apply (proj42 (type_equal_validated_inv H))
  | H : type_equal_validated E _ T K |- _ =>
      apply (proj43 (type_equal_validated_inv H))
  end : type_equal_validated.

Hint Extern 1 (valid_kind_validated ?E ?K) =>
  match goal with
  | H : type_equal_validated E _ _ K |- _ =>
      apply (proj44 (type_equal_validated_inv H))
  end : type_equal_validated.

Hint Extern 1 (valid_env ?E) =>
  match goal with
  | H : type_equal_validated E _ _ _ |- _ =>
      apply (unvalidated_valid_env
               (proj41 (type_equal_validated_inv H)))
  end : type_equal_regular.

Hint Extern 1 (kinding ?E ?T ?K) =>
  match goal with
  | H : type_equal_validated E T _ K |- _ =>
      apply (unvalidated_kinding
               (proj42 (type_equal_validated_inv H)))
  | H : type_equal_validated E _ T K |- _ =>
      apply (unvalidated_kinding
               (proj43 (type_equal_validated_inv H)))
  end : type_equal_validated.

Hint Extern 1 (valid_kind ?E ?K) =>
  match goal with
  | H : type_equal_validated E _ _ K |- _ =>
      apply (unvalidated_valid_kind
               (proj44 (type_equal_validated_inv H)))
  end : type_equal_validated.

Lemma subtype_validated_inv : forall E T1 T2 cs,
    subtype_validated E T1 T2 cs ->
    valid_env_validated E
    /\ kinding_validated E T1 (knd_row cs)
    /\ kinding_validated E T2 (knd_row cs).
Proof.
  introv Hk.
  destruct Hk; auto.
Qed.

Hint Constructors subtype_validated : subtype_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : subtype_validated E _ _ _ |- _ =>
      apply (proj41 (subtype_regular_inv
        (regular_subtype (unvalidated_subtype H))))
  end : subtype_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : subtype_validated _ T _ _ |- _ =>
      apply (proj42 (subtype_regular_inv
        (regular_subtype (unvalidated_subtype H))))
  | H : subtype_validated _ _ T _ |- _ =>
      apply (proj43 (subtype_regular_inv
        (regular_subtype (unvalidated_subtype H))))
  end : subtype_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : subtype_validated _ _ _ cs |- _ =>
      apply (proj44 (subtype_regular_inv
        (regular_subtype (unvalidated_subtype H))))
  end : subtype_regular.

Hint Extern 1 (valid_env_validated ?E) =>
  match goal with
  | H : subtype_validated E _ _ _ |- _ =>
      apply (proj31 (subtype_validated_inv H))
  end : subtype_validated.

Hint Extern 1 (kinding_validated ?E ?T (knd_row ?cs)) =>
  match goal with
  | H : subtype_validated E T _ cs |- _ =>
      apply (proj32 (subtype_validated_inv H))
  | H : subtype_validated E _ T cs |- _ =>
      apply (proj33 (subtype_validated_inv H))
  end : subtype_validated.

Hint Extern 1 (valid_env ?E) =>
  match goal with
  | H : subtype_validated E _ _ _ |- _ =>
      apply (unvalidated_valid_env (proj31 (subtype_validated_inv H)))
  end : subtype_validated.

Hint Extern 1 (kinding ?E ?T (knd_row ?cs)) =>
  match goal with
  | H : subtype_validated E T _ cs |- _ =>
      apply (unvalidated_kinding (proj32 (subtype_validated_inv H)))
  | H : subtype_validated E _ T cs |- _ =>
      apply (unvalidated_kinding (proj33 (subtype_validated_inv H)))
  end : subtype_validated.

Lemma combined_kinding_validated_weakening :
     (forall EG K,
      valid_kind_validated EG K ->
      (forall E F G,
          EG = E & G ->
          valid_env_validated (E & F & G) ->
          valid_kind_validated (E & F & G) K))
  /\ (forall EG T K,
      kinding_validated EG T K ->
      (forall E F G,
          EG = E & G ->
          valid_env_validated (E & F & G) ->
          kinding_validated (E & F & G) T K))
  /\ (forall EG M Xs,
      valid_scheme_vars_validated EG M Xs ->
      (forall E F G,
          fresh (dom F) (sch_arity M) Xs ->
          EG = E & G ->
          valid_env_validated (E & F & G) ->
          valid_scheme_vars_validated (E & F & G) M Xs))
  /\ (forall EG M,
      valid_scheme_validated EG M ->
      (forall E F G,
          EG = E & G ->
          valid_env_validated (E & F & G) ->
          valid_scheme_validated (E & F & G) M))
  /\ (forall EGX,
      valid_env_validated EGX ->
      (forall E F G X K,
          X # F ->
          EGX = E & G & X ~:: K ->
          valid_env_validated (E & F & G) ->
          valid_env_validated (E & F & G & X ~:: K)))
  /\ (forall EG T1 T2 K,
      type_equal_core_validated EG T1 T2 K ->
      (forall E F G,
          EG = E & G ->
          valid_env_validated (E & F & G) ->
          type_equal_core_validated (E & F & G) T1 T2 K))
  /\ (forall EG T1 T2 K,
      type_equal_symm_validated EG T1 T2 K ->
      (forall E F G,
          EG = E & G ->
          valid_env_validated (E & F & G) ->
          type_equal_symm_validated (E & F & G) T1 T2 K))
  /\ (forall EG T1 T2 K,
      type_equal_cong_validated EG T1 T2 K ->
      (forall E F G,
          EG = E & G ->
          valid_env_validated (E & F & G) ->
          type_equal_cong_validated (E & F & G) T1 T2 K))
  /\ (forall EG T1 T2 K,
      type_equal_validated EG T1 T2 K ->
      (forall E F G,
          EG = E & G ->
          valid_env_validated (E & F & G) ->
          type_equal_validated (E & F & G) T1 T2 K))
  /\ (forall EG T1 T2 cs,
      subtype_validated EG T1 T2 cs ->
      (forall E F G,
          EG = E & G ->
          valid_env_validated (E & F & G) ->
          subtype_validated (E & F & G) T1 T2 cs)).
Proof.
  apply combined_kinding_validated_mutind;
    intros; subst; econstr auto with valid_env_regular.
  - auto using binds_weakening
      with kinding_validated valid_env_validated valid_env_regular.
  - apply kinding_validated_range_subsumption
      with (T1 := T1) (T2 := T2);
      auto with valid_env_regular.
  - assert (fresh (dom F) (sch_arity (sch_bind K M)) (X :: Xs)) as Hf
        by assumption.
    destruct Hf.
    apply valid_scheme_vars_validated_bind;
      auto using environment_knd_weakening with valid_env_regular.
    rewrite <- concat_assoc.
    apply H0;
      autorewrite with rew_sch_arity; rewrite? concat_assoc; auto.
  - apply valid_scheme_validated_c
      with (L := (L \u dom F)); auto with valid_env_regular.
  - exfalso. eauto using empty_push_inv.
  - destruct (eq_push_inv H2) as [? [Heq ?]].
    inversion Heq; subst.
    auto with valid_env_validated valid_env_regular.
  - destruct (eq_push_inv H2) as [_ [? _]].
    discriminate.
  - apply type_equal_cong_validated_range_subsumption
      with (T3 := T3) (T4 := T4); auto with valid_env_regular.
  - apply type_equal_validated_step with (T2 := T2);
      auto with valid_env_regular.
Qed.

Lemma valid_kind_validated_weakening : forall E F G K,
    valid_kind_validated (E & G) K ->
    valid_env_validated (E & F & G) ->
    valid_kind_validated (E & F & G) K.
Proof.
  pose combined_kinding_validated_weakening.
  intuition eauto.
Qed.

Lemma valid_kind_validated_from_env : forall E X K,
    valid_env_validated E ->
    binds X (bind_knd K) E ->
    valid_kind_validated E K.
Proof.
  introv He Hb.
  induction He.
  - apply binds_empty_inv in Hb; contradiction.
  - destruct (binds_push_inv Hb) as [[Hx Hbnd]|[Hx Hbnd]];
      inversion Hbnd; subst;
      rewrite <- concat_empty_r with (E := E & X0 ~:: K0);
      apply valid_kind_validated_weakening;
      rewrite concat_empty_r; auto with valid_env_validated.
  - destruct (binds_push_inv Hb) as [[Hx Hbnd]|[Hx Hbnd]];
      try discriminate.
    rewrite <- concat_empty_r with (E := E & x ~: M).
    apply valid_kind_validated_weakening;
      rewrite concat_empty_r; auto with valid_env_validated.
Qed.

(* (Validated) Type equality is a preorder *)

Lemma type_equal_validated_reflexive : forall E T K,
    kinding_validated E T K ->
    type_equal_validated E T T K.
Proof.
  intros.
  auto using type_equal_validated_refl
    with kinding_regular kinding_validated.
Qed.

Lemma type_equal_validated_transitive : forall E T1 T2 T3 K,
    type_equal_validated E T1 T2 K ->
    type_equal_validated E T2 T3 K ->
    type_equal_validated E T1 T3 K.
Proof.
  introv Hte1 Hte2.
  induction Hte1;
    eauto using type_equal_validated
      with type_equal_regular type_equal_validated.
Qed.

(* Useful properties of type equality on meets *)

Lemma type_equal_validated_meet_idempotent : forall E T cs,
    kinding_validated E T (knd_row cs) ->
    type_equal_validated E T (typ_meet T T) (knd_row cs).
Proof.
  introv Hk.
  apply type_equal_validated_step
    with (T2 := typ_meet T (typ_join T (typ_bot cs)));
    auto 6 with kinding_regular kinding_validated
      type_equal_symm_validated type_equal_cong_validated
      type_equal_core_validated.
  apply type_equal_validated_step
    with (T2 := typ_meet T T);
    auto 6 with kinding_regular kinding_validated
      type_equal_symm_validated type_equal_cong_validated
      type_equal_core_validated.
  apply type_equal_validated_refl;
    auto with kinding_regular kinding_validated.
Qed.

Lemma type_equal_validated_meet_r : forall E T1 T2 T2' cs,
    kinding_validated E T1 (knd_row cs) ->
    type_equal_validated E T2 T2' (knd_row cs) ->
    type_equal_validated E
      (typ_meet T1 T2) (typ_meet T1 T2') (knd_row cs).
Proof.
  introv Hk Hte.
  remember (knd_row cs).
  induction Hte; subst.
  - apply type_equal_validated_refl;
      auto with kinding_regular kinding_validated.
  - apply type_equal_validated_step
      with (T2 := typ_meet T1 T2);
      auto with kinding_regular kinding_validated.
    eauto using type_equal_cong_validated with kinding_regular.
Qed.

Lemma type_equal_validated_meet_l : forall E T1 T1' T2 cs,
    kinding_validated E T2 (knd_row cs) ->
    type_equal_validated E T1 T1' (knd_row cs) ->
    type_equal_validated E
      (typ_meet T1 T2) (typ_meet T1' T2) (knd_row cs).
Proof.
  introv Hk Hte.
  remember (knd_row cs).
  induction Hte; subst.
  - apply type_equal_validated_refl;
      auto with kinding_regular kinding_validated.
  - apply type_equal_validated_step
      with (T2 := typ_meet T0 T2);
      auto with kinding_regular kinding_validated.
    eauto using type_equal_cong_validated with kinding_regular.
Qed.

(* (Validated) Subtyping is reflexive *)

Lemma subtype_validated_refl : forall E T cs,
    kinding_validated E T (knd_row cs) ->
    subtype_validated E T T cs.
Proof.
  introv Hk.
  apply subtype_validated_c;
    auto with kinding_regular kinding_validated.
  apply type_equal_validated_step
    with (T2 := (typ_meet T (typ_join T (typ_bot cs))));
    auto 6 with kinding_regular kinding_validated
      type_equal_symm_validated type_equal_cong_validated
      type_equal_core_validated.
  apply type_equal_validated_step
    with (T2 := (typ_meet T T));
    auto 6 with kinding_regular kinding_validated
      type_equal_symm_validated type_equal_cong_validated
      type_equal_core_validated.
  apply type_equal_validated_refl;
    auto with kinding_regular kinding_validated.
Qed.

Lemma subtype_validated_reflexive : forall E T1 T2 cs,
    type_equal_validated E T1 T2 (knd_row cs) ->
    subtype_validated E T1 T2 cs.
Proof.
  introv Hte.
  apply subtype_validated_c;
    auto with type_equal_regular type_equal_validated.
  apply type_equal_validated_transitive with (T2 := typ_meet T1 T1);
    auto using type_equal_validated_meet_idempotent
      with type_equal_validated.
  auto using type_equal_validated_meet_r
    with type_equal_validated.
Qed.

(* (Validated) Type equality is symmetric (and thus an equivalence) *)
    
Lemma type_equal_symm_validated_symmetric : forall E T1 T2 K,
    type_equal_symm_validated E T1 T2 K ->
    type_equal_symm_validated E T2 T1 K.
Proof.
  introv Hte.
  induction Hte; auto using type_equal_symm_validated.
Qed.

Lemma type_equal_cong_validated_symmetric : forall E T1 T2 K,
    type_equal_cong_validated E T1 T2 K ->
    type_equal_cong_validated E T2 T1 K.
Proof.
  introv Hte.
  induction Hte;
    eauto using type_equal_symm_validated_symmetric,
      type_equal_cong_validated.
  assert (type_equal_validated E T1 T1' (knd_row CSet.universe))
    by eauto
         using type_equal_validated_reflexive, type_equal_validated
         with kinding_regular kinding_validated.
  assert (type_equal_validated E T1' T1 (knd_row CSet.universe))
    by eauto
         using type_equal_validated_reflexive, type_equal_validated
         with kinding_regular kinding_validated.
  assert (subtype_validated E T1 T1' CSet.universe)
    by auto using subtype_validated_reflexive.
  assert (subtype_validated E T1' T1 CSet.universe)
    by auto using subtype_validated_reflexive.
  assert (valid_kind_validated E (knd_range T1' T1'))
    by auto using valid_kind_validated, subtype_validated_refl.
  assert (kinding_validated E (typ_row T1') (knd_range T1' T1'))
    by eauto using kinding_validated.
  assert (kinding_validated E (typ_row T1) (knd_range T1' T1'))
    by (eapply kinding_validated_range_subsumption;
          eauto using subtype_validated_refl with kinding_validated).
  apply type_equal_cong_validated_range_subsumption
    with (T3 := T1') (T4 := T1');
    eauto using subtype_validated_refl, type_equal_cong_validated,
      valid_kind_validated, subtype_validated_refl.
Qed.

Lemma type_equal_validated_symmetric_ind : forall E T1 T2 T3 K,
    type_equal_validated E T2 T1 K ->
    type_equal_validated E T2 T3 K ->
    type_equal_validated E T3 T1 K.
Proof.
  introv Hacc Hte.
  induction Hte;
    eauto using type_equal_cong_validated_symmetric
      with type_equal_validated type_equal_regular.
Qed.

Lemma type_equal_validated_symmetric : forall E T1 T2 K,
    type_equal_validated E T1 T2 K ->
    type_equal_validated E T2 T1 K.
Proof.
  introv Hte.
  apply type_equal_validated_symmetric_ind with (T2 := T1);
    try assumption.
  apply type_equal_validated_refl;
    auto with type_equal_regular type_equal_validated.
Qed.

(* (Validated) Subtyping is transitive and antisymmetric (and
   thus a partial order) *)

Lemma subtype_validated_transitive : forall E T1 T2 T3 cs,
    subtype_validated E T1 T2 cs ->
    subtype_validated E T2 T3 cs ->
    subtype_validated E T1 T3 cs.
Proof.
  introv Hs1 Hs2.
  apply subtype_validated_c;
    auto with subtype_regular subtype_validated.
  destruct Hs1. destruct Hs2.
  apply type_equal_validated_transitive
    with (T2 := typ_meet T1 T0); auto.
  apply type_equal_validated_transitive
    with (T2 := typ_meet T1 (typ_meet T0 T2));
    auto using type_equal_validated_meet_r.
  apply type_equal_validated_step
    with (T2 := typ_meet (typ_meet T1 T0) T2);
    auto with kinding_regular kinding_validated
      type_equal_symm_validated type_equal_cong_validated
      type_equal_core_validated.
  apply type_equal_validated_transitive with (T2 := typ_meet T1 T2);
    auto using type_equal_validated_meet_l,
      type_equal_validated_reflexive,
      type_equal_validated_symmetric.
Qed.

Lemma subtype_validated_antisymmetric : forall E T1 T2 cs,
    subtype_validated E T1 T2 cs ->
    subtype_validated E T2 T1 cs ->
    type_equal_validated E T1 T2 (knd_row cs).
Proof.
  introv Hs1 Hs2.
  destruct Hs1. destruct Hs2.
  apply type_equal_validated_transitive
    with (T2 := typ_meet T2 T1); auto.
  apply type_equal_validated_step
    with (T2 := typ_meet T1 T2);
    auto with kinding_regular kinding_validated
      type_equal_symm_validated type_equal_cong_validated
      type_equal_core_validated.
  apply type_equal_validated_symmetric; auto.
Qed.

Lemma validated_combined_kinding_regular :
  (forall E K, valid_kind_regular E K -> valid_kind_validated E K)
  /\ (forall E T K, kinding_regular E T K -> kinding_validated E T K)
  /\ (forall E M Xs,
         valid_scheme_vars_regular E M Xs ->
         valid_scheme_vars_validated E M Xs)
  /\ (forall E M, valid_scheme_regular E M ->
                  valid_scheme_validated E M)
  /\ (forall E, valid_env_regular E -> valid_env_validated E)
  /\ (forall E T1 T2 K,
       type_equal_core_regular E T1 T2 K ->
       type_equal_core_validated E T1 T2 K)
  /\ (forall E T1 T2 K,
       type_equal_symm_regular E T1 T2 K ->
       type_equal_symm_validated E T1 T2 K)
  /\ (forall E T1 T2 K,
       type_equal_cong_regular E T1 T2 K ->
       type_equal_cong_validated E T1 T2 K)
  /\ (forall E T1 T2 K,
       type_equal_regular E T1 T2 K -> type_equal_validated E T1 T2 K)
  /\ (forall E T1 T2 cs,
       subtype_regular E T1 T2 cs -> subtype_validated E T1 T2 cs).
Proof.
  apply combined_kinding_regular_mutind; intros; subst;
    econstr auto with valid_kind_validated kinding_validated
           valid_scheme_vars_validated valid_scheme_validated
           valid_env_validated type_equal_core_validated
           type_equal_symm_validated type_equal_cong_validated
           type_equal_validated subtype_validated.
  - assert (valid_env_validated E) by auto with valid_env_validated.
    assert (valid_kind_validated E K)
      by (eapply valid_kind_validated_from_env; eassumption).   
    auto with kinding_validated.
  - auto using subtype_validated_refl
      with valid_kind_validated kinding_regular kinding_validated.
  - assert (valid_kind_validated E (knd_range T1 T2)) as Hknd
      by auto with kinding_validated.
    inversion Hknd; subst.
    assert (subtype_validated E T2' T1' CSet.universe)
      by eauto using subtype_validated_transitive.
    apply kinding_validated_range_subsumption
      with (T1 := T1) (T2 := T2);
      auto with subtype_validated valid_kind_validated.
  - apply valid_scheme_validated_c with (L := L); try assumption.
    pick_freshes_gen L (sch_arity M) Xs.
    assert (valid_scheme_vars_validated E M Xs) by auto.
    auto with valid_scheme_vars_validated.
  - assert (subtype_validated E T1' T1' CSet.universe)
      by auto using subtype_validated_refl
           with type_equal_cong_validated.
    assert (subtype_validated E T1 T1 CSet.universe)
      by auto using subtype_validated_refl
           with type_equal_cong_validated.
    assert (subtype_validated E T1 T1' CSet.universe)
      by eauto using subtype_validated_reflexive
           with type_equal_validated
                  type_equal_cong_regular type_equal_cong_validated.
    assert (subtype_validated E T1' T1 CSet.universe)
      by eauto
           using subtype_validated_reflexive,
                   type_equal_validated_symmetric
           with type_equal_validated
                  type_equal_cong_regular type_equal_cong_validated.
    apply type_equal_cong_validated_row;
      auto with valid_kind_validated type_equal_cong_validated.
    apply kinding_validated_range_subsumption
      with (T1 := T1') (T2 := T1');
      auto with valid_kind_validated kinding_validated
        type_equal_cong_regular type_equal_cong_validated.
  - assert (valid_kind_validated E (knd_range T3 T4)) as Hknd
      by auto with type_equal_cong_validated.
    inversion Hknd; subst.
    assert (subtype_validated E T4' T3' CSet.universe)
      by eauto using subtype_validated_transitive.
    econstructor; try eassumption;
      auto with valid_kind_validated
        type_equal_cong_validated subtype_validated.
  - assert (kinding_validated E (typ_meet T1 T2) (knd_row cs)) as Hk
      by auto with type_equal_validated.
    inversion Hk; subst.
    auto with subtype_validated type_equal_validated.
Qed.

Lemma validated_valid_kind : forall E K,
    valid_kind E K -> valid_kind_validated E K.
Proof.
  introv Hv.
  apply regular_valid_kind in Hv.
  pose validated_combined_kinding_regular.
  intuition auto.
Qed.

Hint Extern 1 (valid_env ?E) =>
  match goal with
  | H : valid_kind E _ |- _ =>
      apply (unvalidated_valid_env
               (valid_kind_validated_inv (validated_valid_kind H)))
  end : valid_kind_validated.

Lemma validated_kinding : forall E T K,
    kinding E T K -> kinding_validated E T K.
Proof.
  introv Hk.
  apply regular_kinding in Hk.
  pose validated_combined_kinding_regular.
  intuition auto.
Qed.

Hint Extern 1 (valid_env ?E) =>
  match goal with
  | H : kinding E _ _ |- _ =>
      apply (unvalidated_valid_env
               (proj1 (kinding_validated_inv (validated_kinding H))))
  end : kinding_validated.

Hint Extern 1 (valid_kind ?E ?K) =>
  match goal with
  | H : kinding E _ K |- _ =>
      apply (unvalidated_valid_kind
               (proj2 (kinding_validated_inv (validated_kinding H))))
  end : kinding_validated.

Lemma validated_valid_scheme_vars : forall E M Xs,
    valid_scheme_vars E M Xs -> valid_scheme_vars_validated E M Xs.
Proof.
  introv Hv.
  apply regular_valid_scheme_vars in Hv.
  pose validated_combined_kinding_regular.
  intuition auto.
Qed.

Hint Extern 1 (valid_env ?E) =>
  match goal with
  | H : valid_scheme_vars E _ _ |- _ =>
      apply (unvalidated_valid_env
               (valid_scheme_vars_validated_inv
                  (validated_valid_scheme_vars H)))
  end : valid_scheme_vars_validated.

Lemma validated_valid_scheme : forall E M,
    valid_scheme E M -> valid_scheme_validated E M.
Proof.
  introv Hv.
  apply regular_valid_scheme in Hv.
  pose validated_combined_kinding_regular.
  intuition auto.
Qed.

Hint Extern 1 (valid_env ?E) =>
  match goal with
  | H : valid_scheme E _ |- _ =>
      apply (unvalidated_valid_env
               (valid_scheme_validated_inv
                  (validated_valid_scheme H)))
  end : valid_scheme_validated.

Lemma validated_valid_env : forall E,
    valid_env E -> valid_env_validated E.
Proof.
  introv Hv.
  apply regular_valid_env in Hv.
  pose validated_combined_kinding_regular.
  intuition auto.
Qed.

Lemma validated_type_equal_core : forall E T1 T2 K,
    type_equal_core E T1 T2 K -> type_equal_core_validated E T1 T2 K.
Proof.
  introv He.
  apply regular_type_equal_core in He.
  pose validated_combined_kinding_regular.
  intuition auto.
Qed.

Hint Extern 1 (valid_env ?E) =>
  match goal with
  | H : type_equal_core E _ _ _ |- _ =>
      apply (unvalidated_valid_env
               (proj41 (type_equal_core_validated_inv
                          (validated_type_equal_core H))))
  end : type_equal_core_regular.

Hint Extern 1 (kinding ?E ?T ?K) =>
  match goal with
  | H : type_equal_core E T _ K |- _ =>
      apply (unvalidated_kinding
               (proj42 (type_equal_core_validated_inv
                          (validated_type_equal_core H))))
  | H : type_equal_core E _ T K |- _ =>
      apply (unvalidated_kinding
               (proj43 (type_equal_core_validated_inv
                          (validated_type_equal_core H))))
  end : type_equal_core_validated.

Hint Extern 1 (valid_kind ?E ?K) =>
  match goal with
  | H : type_equal_core E _ _ K |- _ =>
      apply (unvalidated_valid_kind
               (proj44 (type_equal_core_validated_inv
                          (validated_type_equal_core H))))
  end : type_equal_core_validated.

Lemma validated_type_equal_symm : forall E T1 T2 K,
    type_equal_symm E T1 T2 K -> type_equal_symm_validated E T1 T2 K.
Proof.
  introv He.
  apply regular_type_equal_symm in He.
  pose validated_combined_kinding_regular.
  intuition auto.
Qed.

Hint Extern 1 (valid_env ?E) =>
  match goal with
  | H : type_equal_symm E _ _ _ |- _ =>
      apply (unvalidated_valid_env
               (proj41 (type_equal_symm_validated_inv
                          (validated_type_equal_symm H))))
  end : type_equal_symm_regular.

Hint Extern 1 (kinding ?E ?T ?K) =>
  match goal with
  | H : type_equal_symm E T _ K |- _ =>
      apply (unvalidated_kinding
               (proj42 (type_equal_symm_validated_inv
                          (validated_type_equal_symm H))))
  | H : type_equal_symm E _ T K |- _ =>
      apply (unvalidated_kinding
               (proj43 (type_equal_symm_validated_inv
                          (validated_type_equal_symm H))))
  end : type_equal_symm_validated.

Hint Extern 1 (valid_kind ?E ?K) =>
  match goal with
  | H : type_equal_symm E _ _ K |- _ =>
      apply (unvalidated_valid_kind
               (proj44 (type_equal_symm_validated_inv
                          (validated_type_equal_symm H))))
  end : type_equal_symm_validated.

Lemma validated_type_equal_cong : forall E T1 T2 K,
    type_equal_cong E T1 T2 K -> type_equal_cong_validated E T1 T2 K.
Proof.
  introv He.
  apply regular_type_equal_cong in He.
  pose validated_combined_kinding_regular.
  intuition auto.
Qed.

Hint Extern 1 (valid_env ?E) =>
  match goal with
  | H : type_equal_cong E _ _ _ |- _ =>
      apply (unvalidated_valid_env
               (proj41 (type_equal_cong_validated_inv
                          (validated_type_equal_cong H))))
  end : type_equal_cong_regular.

Hint Extern 1 (kinding ?E ?T ?K) =>
  match goal with
  | H : type_equal_cong E T _ K |- _ =>
      apply (unvalidated_kinding
               (proj42 (type_equal_cong_validated_inv
                          (validated_type_equal_cong H))))
  | H : type_equal_cong E _ T K |- _ =>
      apply (unvalidated_kinding
               (proj43 (type_equal_cong_validated_inv
                          (validated_type_equal_cong H))))
  end : type_equal_cong_validated.

Hint Extern 1 (valid_kind ?E ?K) =>
  match goal with
  | H : type_equal_cong E _ _ K |- _ =>
      apply (unvalidated_valid_kind
               (proj44 (type_equal_cong_validated_inv
                          (validated_type_equal_cong H))))
  end : type_equal_cong_validated.

Lemma validated_type_equal : forall E T1 T2 K,
    type_equal E T1 T2 K -> type_equal_validated E T1 T2 K.
Proof.
  introv He.
  apply regular_type_equal in He.
  pose validated_combined_kinding_regular.
  intuition auto.
Qed.

Hint Extern 1 (valid_env ?E) =>
  match goal with
  | H : type_equal E _ _ _ |- _ =>
      apply (unvalidated_valid_env
               (proj41 (type_equal_validated_inv
                          (validated_type_equal H))))
  end : type_equal_regular.

Hint Extern 1 (kinding ?E ?T ?K) =>
  match goal with
  | H : type_equal E T _ K |- _ =>
      apply (unvalidated_kinding
               (proj42 (type_equal_validated_inv
                          (validated_type_equal H))))
  | H : type_equal E _ T K |- _ =>
      apply (unvalidated_kinding
               (proj43 (type_equal_validated_inv
                          (validated_type_equal H))))
  end : type_equal_validated.

Hint Extern 1 (valid_kind ?E ?K) =>
  match goal with
  | H : type_equal E _ _ K |- _ =>
      apply (unvalidated_valid_kind
               (proj44 (type_equal_validated_inv
                          (validated_type_equal H))))
  end : type_equal_validated.

Lemma validated_subtype : forall E T1 T2 K,
    subtype E T1 T2 K -> subtype_validated E T1 T2 K.
Proof.
  introv Hs.
  apply regular_subtype in Hs.
  pose validated_combined_kinding_regular.
  intuition auto.
Qed.

Hint Extern 1 (valid_env ?E) =>
  match goal with
  | H : subtype E _ _ _ |- _ =>
      apply (unvalidated_valid_env
               (proj31 (subtype_validated_inv (validated_subtype H))))
  end : subtype_validated.

Hint Extern 1 (kinding ?E ?T (knd_row ?cs)) =>
  match goal with
  | H : subtype E T _ cs |- _ =>
      apply (unvalidated_kinding
               (proj32 (subtype_validated_inv (validated_subtype H))))
  | H : subtype E _ T cs |- _ =>
      apply (unvalidated_kinding
               (proj33 (subtype_validated_inv (validated_subtype H))))
  end : subtype_validated.

Inductive valid_instance_validated
  : env -> list typ -> sch -> Prop :=
  | valid_instance_validated_empty : forall E T,
      kinding E T knd_type ->
      valid_env E ->
      valid_instance_validated E nil (sch_empty T)
  | valid_instance_validated_bind : forall E K M T Ts,
      kinding E T K ->
      valid_instance_validated E Ts (M ^^ T) ->
      valid_env E ->
      valid_instance_validated E (T :: Ts) (sch_bind K M).

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

Hint Extern 1 (types (sch_arity ?M) ?Ts) =>
  match goal with
  | H : valid_instance_validated _ Ts M |- _ =>
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
    valid_env E.
Proof.
  introv Hv.
  destruct Hv; auto.
Qed.    

Hint Extern 1 (valid_env ?E) =>
  match goal with
  | H : valid_instance_validated E _ _ |- _ =>
      apply (valid_instance_validated_inv H)
  end : valid_instance_validated.

Lemma validated_valid_instance_regular : forall E Ts M,
    valid_instance_regular E Ts M -> valid_instance_validated E Ts M.
Proof.
  introv Hv.
  induction Hv; auto with valid_instance_validated kinding_validated.
Qed.

Lemma validated_valid_instance : forall E Ts M,
    valid_instance E Ts M -> valid_instance_validated E Ts M.
Proof.
  introv Hv.
  auto using
    regular_valid_instance, validated_valid_instance_regular.
Qed.

Hint Extern 1 (valid_env ?E) =>
  match goal with
  | H : valid_instance E _ _ |- _ =>
      apply (valid_instance_validated_inv
               (validated_valid_instance H))
  end : valid_instance_validated.

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
(** Typing lattice is bounded *)

Lemma subtype_top : forall E T cs,
    kinding E T (knd_row cs) ->
    subtype E T (typ_top cs) cs.
Proof.
  introv Hk.
  apply validated_kinding in Hk.
  apply subtype_c.
  apply type_equal_step with (typ_meet T (typ_top cs));
    auto with kinding_validated kinding_regular.
Qed.

Lemma subtype_bot : forall E T cs,
    kinding E T (knd_row cs) ->
    subtype E (typ_bot cs) T cs.
Proof.
  introv Hk.
  apply validated_kinding in Hk.
  apply subtype_c.
  apply type_equal_step
    with (typ_meet (typ_bot cs) (typ_join (typ_bot cs) T));
    auto with kinding_validated kinding_regular.
  apply type_equal_step
    with (typ_meet (typ_bot cs) (typ_join T (typ_bot cs)));
    auto 6 with kinding_validated kinding_regular.
  apply type_equal_step with (typ_meet (typ_bot cs) T);
    auto 6 with kinding_validated kinding_regular.
Qed.  

Lemma kinding_range_top_bot : forall E T1 T2 T3,
    kinding E T1 (knd_range T2 T3) ->
    kinding E T1
      (knd_range (typ_top CSet.universe) (typ_bot CSet.universe)).
Proof.
  introv Hk.
  apply validated_kinding in Hk.
  assert (valid_kind_validated E (knd_range T2 T3))
    as Hknd by auto with kinding_validated.
  inversion Hknd; subst.  
  apply kinding_range_subsumption with (T1 := T2) (T2 := T3);
    auto using subtype_top, subtype_bot.
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
(** * "Validated" version of typing judgement *)

Inductive typing_validated : env -> trm -> typ -> Prop :=
  | typing_validated_var : forall E x M T Us,
      valid_env E -> 
      binds x (bind_typ M) E -> 
      valid_instance E Us M ->
      type_equal E T (instance M Us) knd_type ->
      environment E ->
      scheme M ->
      types (sch_arity M) Us ->
      type T ->
      valid_scheme E M ->
      kinding E T knd_type ->
      typing_validated E (trm_fvar x) T
  | typing_validated_abs : forall L E T1 T2 t1,
      kinding E T1 knd_type ->
      (forall x, x \notin L -> 
        typing_validated
          (E & x ~ bind_typ (sch_empty T1)) (t1 ^ x) T2) ->
      environment E ->
      (forall x, x \notin L ->
         environment (E & x ~ bind_typ (sch_empty T1))) ->
      type T1 ->
      type T2 ->
      term_body t1 ->
      valid_env E ->
      (forall x, x \notin L -> 
        valid_env (E & x ~ bind_typ (sch_empty T1))) ->
      kinding E T2 knd_type ->
      (forall x, x \notin L -> 
        kinding
          (E & x ~ bind_typ (sch_empty T1)) T2 knd_type) ->
      typing_validated E (trm_abs t1) (typ_arrow T1 T2)
  | typing_validated_app : forall E S T t1 t2, 
      typing_validated E t1 (typ_arrow S T) ->
      typing_validated E t2 S ->
      environment E ->
      type S ->
      type T ->
      term t1 ->
      term t2 ->
      valid_env E ->
      kinding E S knd_type ->
      kinding E T knd_type ->
      typing_validated E (trm_app t1 t2) T
  | typing_validated_let : forall M L E T2 t1 t2,
      (forall Xs, fresh L (sch_arity M) Xs ->
         typing_validated
           (E & Xs ~::* M)
           t1 (instance_vars M Xs)) ->
      (forall x, x \notin L ->
         typing_validated (E & x ~ (bind_typ M)) (t2 ^ x) T2) ->
      environment E ->
      (forall Xs, fresh L (sch_arity M) Xs ->
         environment (E & Xs ~::* M)) ->
      (forall x, x \notin L ->
         environment (E & x ~ (bind_typ M))) -> 
      type T2 ->
      (forall Xs, fresh L (sch_arity M) Xs ->
         type (instance_vars M Xs)) ->
      scheme M ->
      term t1 ->
      term_body t2 ->
      valid_env E ->
      (forall Xs, fresh L (sch_arity M) Xs ->
         valid_env (E & Xs ~::* M)) ->
      (forall x, x \notin L ->
         valid_env (E & x ~ (bind_typ M))) ->
      (forall Xs, fresh L (sch_arity M) Xs ->
         kinding (E & Xs ~::* M) (instance_vars M Xs) knd_type) ->
      valid_scheme E M ->
      kinding E T2 knd_type ->
      (forall x, x \notin L ->
         kinding (E & x ~ (bind_typ M)) T2 knd_type) ->
      typing_validated E (trm_let t1 t2) T2
  | typing_validated_constructor : forall c E T1 T2 T3 t,
      kinding E T1 (knd_range (typ_top CSet.universe) T2) ->
      subtype E
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (typ_constructor c T3)
        (CSet.singleton c) ->
      typing_validated E t T3 ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      term t ->
      valid_env E ->
      kinding E T2 (knd_row CSet.universe) ->
      kinding E T3 knd_type ->
      typing_validated E (trm_constructor c t) (typ_variant T1)
  | typing_validated_match : forall c L E T1 T2 T3 T4 T5
                          T6 T7 T8 t1 t2 t3,
      subtype E
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (typ_constructor c T7)
        (CSet.singleton c) ->
      subtype E
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (typ_proj CSet.universe T4 (CSet.singleton c))
        (CSet.singleton c) ->
      subtype E
        (typ_proj CSet.universe T2 (CSet.cosingleton c))
        (typ_proj CSet.universe T6 (CSet.cosingleton c))
        (CSet.cosingleton c) ->
      kinding E T1 (knd_range T2 (typ_bot CSet.universe)) ->
      kinding E T3 (knd_range (typ_top CSet.universe) T4) ->
      kinding E T5 (knd_range (typ_top CSet.universe) T6) ->
      typing_validated E t1 (typ_variant T1) ->
      (forall x, x \notin L ->
         typing_validated (E & x ~: (sch_empty (typ_variant T3)))
                (t2 ^ x) T8) ->
      (forall y, y \notin L -> 
         typing_validated (E & y ~: (sch_empty (typ_variant T5)))
                (t3 ^ y) T8) ->
      environment E ->
      (forall x, x \notin L ->
         environment (E & x ~: (sch_empty (typ_variant T3)))) ->
      (forall y, y \notin L -> 
         environment (E & y ~: (sch_empty (typ_variant T5)))) ->
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
      valid_env E ->
      (forall x, x \notin L ->
         valid_env (E & x ~: (sch_empty (typ_variant T3)))) ->
      (forall y, y \notin L -> 
         valid_env (E & y ~: (sch_empty (typ_variant T5)))) ->
      kinding E T2 (knd_row CSet.universe) ->
      kinding E T4 (knd_row CSet.universe) ->
      kinding E T6 (knd_row CSet.universe) ->
      kinding E T7 knd_type ->
      kinding E T8 knd_type ->
      (forall x, x \notin L ->
         kinding (E & x ~: (sch_empty (typ_variant T3)))
                 T8 knd_type) ->
      (forall y, y \notin L -> 
         kinding (E & y ~: (sch_empty (typ_variant T5)))
                 T8 knd_type) ->
      typing_validated E (trm_match t1 c t2 t3) T8
  | typing_validated_destruct : forall c L E T1 T2 T3 T4 t1 t2,
      kinding E T1 (knd_range T2 (typ_bot CSet.universe)) ->
      subtype E
        (typ_constructor c T3)
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (CSet.singleton c) ->
      typing_validated E t1 (typ_variant T1) ->
      (forall x, x \notin L ->
         typing_validated (E & x ~: (sch_empty T3))
                (t2 ^ x) T4) ->
      environment E ->
      (forall x, x \notin L ->
         environment (E & x ~: (sch_empty T3))) ->
      type T1 ->
      type T2 ->
      type T3 ->
      type T4 ->
      term t1 ->
      term_body t2 ->
      valid_env E ->
      (forall x, x \notin L ->
         valid_env (E & x ~: (sch_empty T3))) ->
      kinding E T2 (knd_row CSet.universe) ->
      kinding E T3 knd_type ->
      kinding E T4 knd_type ->
      (forall x, x \notin L ->
          kinding (E & x ~: (sch_empty T3))
                  T4 knd_type) ->
      typing_validated E (trm_destruct t1 c t2) T4
  | typing_validated_absurd : forall E T1 T2 t1,
      kinding E T1 (knd_range (typ_bot CSet.universe)
                              (typ_bot CSet.universe)) ->
      kinding E T2 knd_type ->
      typing_validated E t1 (typ_variant T1) ->
      environment E ->
      type T1 ->
      type T2 ->
      term t1 ->
      valid_env E ->
      typing_validated E (trm_absurd t1) T2.

Lemma unvalidated_typing : forall E t T,
    typing_validated E t T -> typing E t T.
Proof.
  introv Ht.
  induction Ht; eauto using typing.
Qed.

Hint Resolve unvalidated_typing.

Lemma typing_validated_inv : forall E t T,
    typing_validated E t T ->
    valid_env E /\ kinding E T knd_type.
Proof.
  introv Ht.
  induction Ht; splits; eauto using kinding_range_top_bot.
Qed.

Hint Constructors typing_validated : typing_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : typing_validated E _ _ |- _ =>
      apply (proj31 (typing_regular_inv
                       (regular_typing (unvalidated_typing H))))
  end : typing_validated.

Hint Extern 1 (term ?t) =>
  match goal with
  | H : typing_validated _ t _ |- _ =>
      apply (proj32 (typing_regular_inv
                       (regular_typing (unvalidated_typing H))))
  end : typing_validated.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : typing_validated _ _ T |- _ =>
      apply (proj33 (typing_regular_inv 
                       (regular_typing (unvalidated_typing H))))
  end : typing_validated.

Hint Extern 1 (valid_env ?E) =>
  match goal with
  | H : typing_validated E _ _ |- _ =>
      apply (proj1 (typing_validated_inv H))
  end : typing_validated.

Hint Extern 1 (kinding ?E ?T knd_type) =>
  match goal with
  | H : typing_validated E _ T |- _ =>
      apply (proj2 (typing_validated_inv H))
  end : typing_validated.

Lemma validated_typing_regular : forall E t T,
    typing_regular E t T -> typing_validated E t T.
Proof.
  introv Ht.
  induction Ht.
  - econstructor; try eassumption; auto.
    + apply valid_scheme_from_env with (x := x); assumption.
    + auto with type_equal_validated.
  - pick_fresh x.
    assert (typing_validated (E & x ~: sch_empty T1) (t1 ^ x) T2)
      by auto.
    assert (valid_env E)
      by eauto using valid_env_retract with typing_validated.
    assert (kinding E T2 knd_type)
      by eauto using kinding_remove_typ_bind_l with typing_validated.
    econstructor; eauto with typing_validated;
      intros y Hn;
      assert (typing_validated (E & y ~: sch_empty T1) (t1 ^ y) T2)
        by auto;
      auto with typing_validated.
  - assert (kinding E (typ_arrow S T) knd_type)
      as Hk by auto with typing_validated.
    inversion Hk; subst.
    econstr auto with typing_validated.
  - pick_fresh x.
    assert (typing_validated (E & x ~: M) (t2 ^ x) T2) by auto.
    assert (kinding E T2 knd_type)
      by eauto using kinding_remove_typ_bind_l with typing_validated.
    assert (valid_env (E & x ~: M)) by auto with typing_validated.
    assert (valid_env E) by eauto using valid_env_retract.
    assert (valid_scheme E M)
      by eauto using binds_push_eq,
         valid_scheme_from_env, valid_scheme_remove_typ_bind_l.
    econstructor; eauto;
      try
        (intros Ys Hf;
         assert
           (typing_validated (E & Ys ~::* M) t1 (instance_vars M Ys))
           by auto;
         auto with typing_validated);
      try
        (intros y Hn;
         assert (typing_validated (E & y ~: M) (t2 ^ y) T2)
           by auto;
         auto with typing_validated).
  - assert (valid_kind E (knd_range (typ_top CSet.universe) T2))
      as Hk by auto with kinding_validated.
    inversion Hk; subst.
    assert (kinding E T2 (knd_row CSet.universe))
      by auto with subtype_validated.
    econstr auto with typing_validated.
  - assert (valid_kind E (knd_range T2 (typ_bot CSet.universe)))
      as Hk1 by auto with kinding_validated.
    inversion Hk1; subst.
    assert (kinding E T2 (knd_row CSet.universe))
      by auto with subtype_validated.
    assert (valid_kind E (knd_range (typ_top CSet.universe) T4))
      as Hk2 by auto with kinding_validated.
    inversion Hk2; subst.
    assert (kinding E T4 (knd_row CSet.universe))
      by auto with subtype_validated.
    assert (valid_kind E (knd_range (typ_top CSet.universe) T6))
      as Hk3 by auto with kinding_validated.
    inversion Hk3; subst.
    assert (kinding E T6 (knd_row CSet.universe))
      by auto with subtype_validated.
    assert (kinding E (typ_constructor c T7)
                    (knd_row (CSet.singleton c)))
      as Hk4 by auto with subtype_validated.
    inversion Hk4; subst.
    pick_fresh x.
    assert (typing_validated (E & x ~: sch_empty (typ_variant T5))
                             (t3 ^ x) T8)
      by auto.
    assert (kinding E T8 knd_type)
      by eauto using kinding_remove_typ_bind_l with typing_validated.
    econstructor; eauto with typing_validated;
      intros y Hn;
      assert
        (typing_validated
           (E & y ~: sch_empty (typ_variant T3)) (t2 ^ y) T8)
        by auto;
      assert (typing_validated
                (E & y ~: sch_empty (typ_variant T5)) (t3 ^ y) T8)
        by auto;
      auto with typing_validated.
  - assert (valid_kind E (knd_range T2 (typ_bot CSet.universe)))
      as Hk1 by auto with kinding_validated.
    inversion Hk1; subst.
    assert (kinding E T2 (knd_row CSet.universe))
      by auto with subtype_validated.
    assert (kinding E (typ_constructor c T3)
                    (knd_row (CSet.singleton c)))
      as Hk2 by auto with subtype_validated.
    inversion Hk2; subst.
    pick_fresh x.
    assert (typing_validated (E & x ~: sch_empty T3)
                             (t2 ^ x) T4)
      by auto.
    assert (kinding E T4 knd_type)
      by eauto using kinding_remove_typ_bind_l with typing_validated.
    econstructor; eauto with typing_validated;
      intros y Hn;
      assert (typing_validated
                (E & y ~: sch_empty T3) (t2 ^ y) T4)
        by auto;
      auto with typing_validated.   
  - econstr auto with typing_validated.
Qed.

Lemma validated_typing : forall E t T,
    typing E t T -> typing_validated E t T.
Proof.
  intros.
  apply validated_typing_regular.
  apply regular_typing.
  assumption.
Qed.

Hint Extern 1 (valid_env ?E) =>
  match goal with
  | H : typing E _ _ |- _ =>
      apply (proj1 (typing_validated_inv (validated_typing H)))
  end : typing_validated.

Hint Extern 1 (kinding ?E ?T knd_type) =>
  match goal with
  | H : typing E _ T |- _ =>
      apply (proj2 (typing_validated_inv (validated_typing H)))
  end : typing_validated.
