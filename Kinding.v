(************************************************
 *          Row Subtyping - Kinding             *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import LibLN Cofinite Definitions Substitution Wellformedness.

Hint Constructors
     valid_kind kinding valid_scheme_vars valid_instance valid_env
     type_equal_core type_equal_cong type_equal_symm type_equal.

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
  - destruct (empty_concat_inv HeqG) as [_ Hem].
    apply empty_single_inv in Hem.
    contradiction.
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
      type_equal_cong_regular EG T1 T2 K ->
      (forall E F G,
          EG = E & G ->
          valid_env (E & F & G) ->
          type_equal_cong (E & F & G) T1 T2 K))
  /\ (forall EG T1 T2 K,
      type_equal_symm_regular EG T1 T2 K ->
      (forall E F G,
          EG = E & G ->
          valid_env (E & F & G) ->
          type_equal_symm (E & F & G) T1 T2 K))
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
  - apply type_equal_core_or_associative
      with (cs1 := cs1) (cs2 := cs2) (cs3 := cs3); auto.
Qed.

Lemma valid_kind_weakening : forall E F G K,
    valid_kind (E & G) K ->
    valid_env (E & F & G) ->
    valid_kind (E & F & G) K.
Proof.
  introv Hv He.
  apply regular_valid_kind in Hv.
  remember (E & G) as EG.
  generalize dependent G.
  generalize dependent F.
  generalize dependent E.
  generalize dependent K.
  generalize dependent EG.
  pose combined_kinding_weakening.
  intuition assumption.
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
  remember (E & G) as EG.
  generalize dependent G.
  generalize dependent F.
  generalize dependent E.
  generalize dependent K.
  generalize dependent T.
  generalize dependent EG.
  pose combined_kinding_weakening.
  intuition assumption.
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
  remember (E & G) as EG.
  generalize dependent He.
  generalize dependent HeqEG.
  generalize dependent Hf.
  generalize dependent G.
  generalize dependent F.
  generalize dependent E.
  generalize dependent Xs.
  generalize dependent M.
  generalize dependent EG.
  pose combined_kinding_weakening.
  intuition assumption.
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
  remember (E & G) as EG.
  generalize dependent G.
  generalize dependent F.
  generalize dependent E.
  generalize dependent M.
  generalize dependent EG.
  pose combined_kinding_weakening.
  intuition assumption.
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
  remember (E & G) as EG.
  generalize dependent G.
  generalize dependent F.
  generalize dependent E.
  generalize dependent K.
  generalize dependent T2.
  generalize dependent T1.
  generalize dependent EG.
  pose combined_kinding_weakening.
  intuition assumption.
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

Lemma type_equal_cong_weakening : forall E F G T1 T2 K,
   type_equal_cong (E & G) T1 T2 K -> 
   valid_env (E & F & G) ->
   type_equal_cong (E & F & G) T1 T2 K.
Proof.
  introv Hte He.
  apply regular_type_equal_cong in Hte.
  remember (E & G) as EG.
  generalize dependent G.
  generalize dependent F.
  generalize dependent E.
  generalize dependent K.
  generalize dependent T2.
  generalize dependent T1.
  generalize dependent EG.
  pose combined_kinding_weakening.
  intuition assumption.
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

Lemma type_equal_symm_weakening : forall E F G T1 T2 K,
   type_equal_symm (E & G) T1 T2 K -> 
   valid_env (E & F & G) ->
   type_equal_symm (E & F & G) T1 T2 K.
Proof.
  introv Hte He.
  apply regular_type_equal_symm in Hte.
  remember (E & G) as EG.
  generalize dependent G.
  generalize dependent F.
  generalize dependent E.
  generalize dependent K.
  generalize dependent T2.
  generalize dependent T1.
  generalize dependent EG.
  pose combined_kinding_weakening.
  intuition assumption.
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

Lemma type_equal_weakening : forall E F G T1 T2 K,
   type_equal (E & G) T1 T2 K -> 
   valid_env (E & F & G) ->
   type_equal (E & F & G) T1 T2 K.
Proof.
  introv Hte He.
  apply regular_type_equal in Hte.
  remember (E & G) as EG.
  generalize dependent G.
  generalize dependent F.
  generalize dependent E.
  generalize dependent K.
  generalize dependent T2.
  generalize dependent T1.
  generalize dependent EG.
  pose combined_kinding_weakening.
  intuition assumption.
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
  remember (E & G) as EG.
  generalize dependent G.
  generalize dependent F.
  generalize dependent E.
  generalize dependent cs.
  generalize dependent T2.
  generalize dependent T1.
  generalize dependent EG.
  pose combined_kinding_weakening.
  intuition assumption.
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
  remember (E & G) as EG.
  generalize dependent E.
  generalize dependent G.
  generalize dependent EG.
  generalize dependent F.
  generalize dependent M.
  induction Xs; introv Hl Hf He1 Heq He2; subst; simpl.
  - autorewrite with rew_env_concat; auto.
  - destruct M; simpl in Hl; try discriminate.
    simpl in He1.
    autorewrite with rew_env_concat in *.
    destruct Hf.
    inversion Hl.
    rewrite <- concat_assoc with (E := E & F).
    apply IHXs with (EG := E & G & a ~:: k);
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
    eauto using sch_open_var_fv.
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
    eauto using sch_open_fv.
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
      type_equal_cong_regular EXF T1 T2 K ->
      (forall E F X J S,
          EXF = E & X ~:: J & F ->
          kinding E S J ->
          type_equal_cong (E & env_subst X S F)
            (typ_subst X S T1) (typ_subst X S T2) (knd_subst X S K)))
  /\ (forall EXF T1 T2 K,
      type_equal_symm_regular EXF T1 T2 K ->
      (forall E F X J S,
          EXF = E & X ~:: J & F ->
          kinding E S J ->
          type_equal_symm (E & env_subst X S F)
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
  - apply kinding_variant
      with (T1 := typ_subst X S T1) (T2 := typ_subst X S T2).
    eauto.
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
  - apply type_equal_core_or_associative
      with (cs1 := cs1) (cs2 := cs2) (cs3 := cs3); eauto.
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
(** Not affected by type bindings *)

Lemma combined_kinding_typ_bind :
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
      type_equal_cong EXF T1 T2 K ->
      (forall E F x M,
          EXF = E & x ~: M & F ->
          type_equal_cong (E & F) T1 T2 K))
  /\ (forall EXF T1 T2 K,
      type_equal_symm EXF T1 T2 K ->
      (forall E F x M,
          EXF = E & x ~: M & F ->
          type_equal_symm (E & F) T1 T2 K))
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
  - apply type_equal_core_or_associative
      with (cs1 := cs1) (cs2 := cs2) (cs3 := cs3); eauto.
Qed.      

Lemma valid_kind_typ_bind : forall E F x M K,
    valid_kind (E & x ~: M & F) K ->
    valid_kind (E & F) K.
Proof.
  introv Hv.
  pose combined_kinding_typ_bind.
  intuition eauto.
Qed.

Lemma kinding_typ_bind : forall E F x M T K,
    kinding (E & x ~: M & F) T K ->
    kinding (E & F) T K.
Proof.
  introv Hk.
  pose combined_kinding_typ_bind.
  intuition eauto.
Qed.

Lemma valid_scheme_vars_typ_bind : forall E F x M Ms Xs,
    valid_scheme_vars (E & x ~: M & F) Ms Xs ->
    valid_scheme_vars (E & F) Ms Xs.
Proof.
  introv Hv.
  pose combined_kinding_typ_bind.
  intuition eauto.
Qed.

Lemma valid_scheme_typ_bind : forall E F x M Ms,
    valid_scheme (E & x ~: M & F) Ms ->
    valid_scheme (E & F) Ms.
Proof.
  introv Hv.
  pose combined_kinding_typ_bind.
  intuition eauto.
Qed.

Lemma valid_env_typ_bind : forall E F x M,
    valid_env (E & x ~: M & F) ->
    valid_env (E & F).
Proof.
  introv Hv.
  pose combined_kinding_typ_bind.
  intuition eauto.
Qed.

Lemma type_equal_core_typ_bind : forall E F x M T1 T2 K,
    type_equal_core (E & x ~: M & F) T1 T2 K ->
    type_equal_core (E & F) T1 T2 K.
Proof.
  introv Hte.
  pose combined_kinding_typ_bind.
  intuition eauto.
Qed.

Lemma type_equal_cong_typ_bind : forall E F x M T1 T2 K,
    type_equal_cong (E & x ~: M & F) T1 T2 K ->
    type_equal_cong (E & F) T1 T2 K.
Proof.
  introv Hte.
  pose combined_kinding_typ_bind.
  intuition eauto.
Qed.

Lemma type_equal_symm_typ_bind : forall E F x M T1 T2 K,
    type_equal_symm (E & x ~: M & F) T1 T2 K ->
    type_equal_symm (E & F) T1 T2 K.
Proof.
  introv Hte.
  pose combined_kinding_typ_bind.
  intuition eauto.
Qed.

Lemma type_equal_typ_bind : forall E F x M T1 T2 K,
    type_equal (E & x ~: M & F) T1 T2 K ->
    type_equal (E & F) T1 T2 K.
Proof.
  introv Hte.
  pose combined_kinding_typ_bind.
  intuition eauto.
Qed.

Lemma subtype_typ_bind : forall E F x M T1 T2 cs,
    subtype (E & x ~: M & F) T1 T2 cs ->
    subtype (E & F) T1 T2 cs.
Proof.
  introv Hs.
  pose combined_kinding_typ_bind.
  intuition eauto.
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
(** Type equality is an equivalence relation. This "raw" version
    of the symmetry lemma requires separate evidence of the
    well-kindedness of the types involved. A version that extracts
    this evidence from the given relations is defined later in
    the file. *)

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
  induction Hte; auto.
Qed.

Lemma type_equal_symmetric_ind : forall E T1 T2 T3 K,
    type_equal E T2 T1 K ->
    type_equal E T2 T3 K ->
    type_equal E T3 T1 K.
Proof.
  introv Hacc Hte.
  induction Hte; auto.
  eauto using type_equal_symm_symmetric.
Qed.

Lemma raw_type_equal_symmetric : forall E T1 T2 K,
    kinding E T1 K ->
    type_equal E T1 T2 K ->
    type_equal E T2 T1 K.
Proof.
  introv Hte.
  apply type_equal_symmetric_ind with (T2 := T1); try assumption.
  apply type_equal_refl.
  assumption.
Qed.

(* *************************************************************** *)
(** The subtyping relation is a partial order. These "raw" versions
    require separate evidence of the well-kindedness of the types
    involved. Versions that extract this evidence from the given
    relations are defined later in the file. *)

Lemma raw_subtype_reflexive : forall E T cs,
    valid_env E ->
    kinding E T (knd_row cs) ->
    subtype E T T cs.
Proof.
  introv Hv Hk.
  assert (kind (knd_row cs)) as Hknd by auto with kinding_regular.
  inversion Hknd; subst.
  apply subtype_c.
  apply type_equal_step
    with (T2 := (typ_meet T (typ_join T (typ_bot cs)))); auto.
  apply type_equal_step with (T2 := (typ_meet T T));
    inversion Hk; subst; auto with kinding_regular.
Qed.

Lemma raw_type_equal_meet_r : forall E T1 T2 T2' cs,
    kinding E (typ_meet T1 T2') (knd_row cs) ->
    type_equal E T2 T2' (knd_row cs) ->
    type_equal E (typ_meet T1 T2) (typ_meet T1 T2') (knd_row cs).
Proof.
  introv Hk Hte.
  remember (knd_row cs).
  induction Hte; subst.
  - auto using type_equal_refl.
  - apply type_equal_step with (T2 := typ_meet T1 T2); auto.
    assert (type_equal_symm E T0 T2 (knd_row cs)) as Htes
      by assumption.
    inversion Hk.
    remember (knd_row cs).
    destruct Htes; subst; auto.
Qed.

Lemma raw_type_equal_meet_l : forall E T1 T1' T2 cs,
    kinding E (typ_meet T1' T2) (knd_row cs) ->
    type_equal E T1 T1' (knd_row cs) ->
    type_equal E (typ_meet T1 T2) (typ_meet T1' T2) (knd_row cs).
Proof.
  introv Hk Hte.
  remember (knd_row cs).
  induction Hte; subst.
  - auto using type_equal_refl.
  - apply type_equal_step with (T2 := typ_meet T0 T2); auto.  
    assert (type_equal_symm E T1 T0 (knd_row cs)) as Htes
      by assumption.
    inversion Hk.
    remember (knd_row cs).
    destruct Htes; subst; auto.
Qed.
      
Lemma raw_subtype_transitive : forall E T1 T2 T3 cs,
    kinding E T1 (knd_row cs) ->
    kinding E T2 (knd_row cs) ->
    kinding E T3 (knd_row cs) ->
    subtype E T1 T2 cs ->
    subtype E T2 T3 cs ->
    subtype E T1 T3 cs.
Proof.
  introv Hk1 Hk2 Hk3 Hs1 Hs2.
  apply subtype_c.
  destruct Hs1. destruct Hs2.
  apply type_equal_transitive
    with (T2 := typ_meet T1 T0); auto.
  apply type_equal_transitive
    with (T2 := typ_meet T1 (typ_meet T0 T2));
    auto using raw_type_equal_meet_r.
  apply type_equal_step
    with (T2 := typ_meet (typ_meet T1 T0) T2);
    auto.
  apply type_equal_transitive with (T2 := typ_meet T1 T2);
    auto using raw_type_equal_meet_l, raw_type_equal_symmetric.
Qed.

Lemma raw_subtype_antisymmetric : forall E T1 T2 cs,
    kinding E T1 (knd_row cs) ->
    kinding E T2 (knd_row cs) ->
    subtype E T1 T2 cs ->
    subtype E T2 T1 cs ->
    type_equal E T1 T2 (knd_row cs).
Proof.
  introv Hk1 Hk2 Hs1 Hs2.
  destruct Hs1. destruct Hs2.
  apply type_equal_transitive with (T2 := typ_meet T2 T1); auto.
  apply type_equal_step with (T2 := typ_meet T1 T2); auto.
  apply raw_type_equal_symmetric; auto.
Qed.

(* *************************************************************** *)
(** * "Validated" versions of judgements *)

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
      valid_env E ->
      kinding E T1 (knd_row CSet.universe) ->
      kinding E T2 (knd_row CSet.universe) ->
      valid_kind_validated E (knd_range T1 T2)

with kinding_validated : env -> typ -> knd -> Prop :=
  | kinding_validated_var : forall E X K,
      valid_env_validated E ->
      binds X (bind_knd K) E ->
      environment E ->
      kind K ->
      valid_kind E K ->
      kinding_validated E (typ_fvar X) K
  | kinding_validated_constructor : forall E c T cs,
      kinding_validated E T knd_type ->
      cs = CSet.singleton c ->
      environment E ->
      type T ->
      valid_env E ->
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
      valid_env E ->
      kinding_validated E (typ_or T1 T2) (knd_row cs12)
  | kinding_validated_proj : forall E T cs cs',
      kinding_validated E T (knd_row cs) ->
      CSet.Subset cs' cs ->
      CSet.Nonempty cs' ->
      environment E ->
      type T ->
      CSet.Nonempty cs ->
      valid_env E ->
      kinding_validated E (typ_proj T cs') (knd_row cs')
  | kinding_validated_row : forall E T,
      kinding_validated E T (knd_row CSet.universe) ->
      environment E ->
      type T ->
      valid_env E ->
      kinding_validated E (typ_row T) (knd_range T T)
  | kinding_validated_variant : forall E T T1 T2,
      kinding_validated E T (knd_range T1 T2) ->
      environment E ->
      type T ->
      type T1 ->
      type T2 ->
      valid_env E ->
      kinding E T1 (knd_row CSet.universe) ->
      kinding E T2 (knd_row CSet.universe) ->
      subtype E T2 T1 CSet.universe ->
      kinding_validated E (typ_variant T) knd_type
  | kinding_validated_arrow : forall E T1 T2,
      kinding_validated E T1 knd_type -> 
      kinding_validated E T2 knd_type -> 
      environment E ->
      type T1 ->
      type T2 ->
      valid_env E ->
      kinding_validated E (typ_arrow T1 T2) knd_type
  | kinding_validated_top : forall E cs,
      valid_env_validated E ->
      CSet.Nonempty cs ->
      environment E ->
      valid_env E ->
      kinding_validated E (typ_top cs) (knd_row cs)
  | kinding_validated_bot : forall E cs,
      valid_env_validated E ->
      CSet.Nonempty cs ->
      environment E ->
      valid_env E ->
      kinding_validated E (typ_bot cs) (knd_row cs)
  | kinding_validated_meet : forall E T1 T2 cs,
      kinding_validated E T1 (knd_row cs) ->
      kinding_validated E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env E ->
      kinding_validated E (typ_meet T1 T2) (knd_row cs)
  | kinding_validated_join : forall E T1 T2 cs,
      kinding_validated E T1 (knd_row cs) ->
      kinding_validated E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env E ->
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
      valid_env E ->
      kinding E T1 (knd_row CSet.universe) ->
      kinding E T1' (knd_row CSet.universe) ->
      kinding E T2 (knd_row CSet.universe) ->
      kinding E T2' (knd_row CSet.universe) ->
      subtype E T2 T1 CSet.universe ->
      subtype E T2' T1' CSet.universe ->
      kinding_validated E T (knd_range T1' T2')

with valid_scheme_vars_validated : env -> sch -> list var -> Prop :=
  | valid_scheme_vars_validated_empty : forall E T,
      kinding_validated E T knd_type ->
      environment E ->
      type T ->
      valid_env E ->
      valid_scheme_vars_validated E (sch_empty T) nil
  | valid_scheme_vars_validated_bind : forall X Xs E K M,
      valid_kind_validated E K ->
      valid_scheme_vars_validated (E & X ~:: K) (M ^ X) Xs ->
      environment E ->
      environment (E & X ~:: K) ->
      kind K ->
      scheme_vars (M ^ X) Xs ->
      scheme_vars (sch_bind K M) (X :: Xs) ->
      valid_env E ->
      valid_env (E & X ~:: K) ->
      valid_scheme_vars_validated E (sch_bind K M) (X :: Xs)

with valid_scheme_validated : env -> sch -> Prop :=
  | valid_scheme_validated_c : forall E M L,
      (forall Xs,
          fresh L (sch_arity M) Xs ->
          valid_scheme_vars_validated E M Xs) ->
      environment E ->
      scheme M ->
      valid_env E ->
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
      valid_env E ->
      type_equal_core_validated E
        (typ_or T1 T2) (typ_or T2 T1) (knd_row cs12)
  | type_equal_core_validated_or_associative :
      forall E T1 cs1 T2 cs2 T3 cs3 cs123,
      kinding_validated E T1 (knd_row cs1) ->
      kinding_validated E T2 (knd_row cs2) ->
      kinding_validated E T3 (knd_row cs3) ->
      CSet.Disjoint cs1 cs2 ->
      CSet.Disjoint cs1 cs3 ->
      CSet.Disjoint cs2 cs3 ->
      cs123 = CSet.union cs1 (CSet.union cs2 cs3) ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      CSet.Nonempty cs3 ->
      valid_env E ->
      type_equal_core_validated E
        (typ_or T1 (typ_or T2 T3)) (typ_or (typ_or T1 T2) T3)
        (knd_row cs123)
  | type_equal_core_validated_or_bot : forall E cs1 cs2 cs12,
      valid_env_validated E ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type_equal_core_validated E
        (typ_or (typ_bot cs1) (typ_bot cs2)) (typ_bot cs12)
        (knd_row cs12)
  | type_equal_core_validated_or_top : forall E cs1 cs2 cs12,
      valid_env_validated E ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type_equal_core_validated E
        (typ_or (typ_top cs1) (typ_top cs2)) (typ_top cs12)
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
      valid_env E ->
      type_equal_core_validated E
        (typ_or (typ_meet T1 T3) (typ_meet T2 T4))
        (typ_meet (typ_or T1 T2) (typ_or T3 T4))
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
      valid_env E ->
      type_equal_core_validated E
        (typ_or (typ_join T1 T3) (typ_join T2 T4))
        (typ_join (typ_or T1 T2) (typ_or T3 T4))
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
      valid_env E ->
      type_equal_core_validated E
        (typ_or (typ_proj T cs2) (typ_proj T cs3))
        (typ_proj T cs23)
        (knd_row cs23)
  | type_equal_core_validated_proj_id : forall E T cs,
      kinding_validated E T (knd_row cs) ->
      environment E ->
      type T ->
      CSet.Nonempty cs ->
      valid_env E ->
      type_equal_core_validated E (typ_proj T cs) T (knd_row cs)
  | type_equal_core_validated_proj_or_l : forall E T1 T2 cs1 cs1' cs2,
      kinding_validated E T1 (knd_row cs1) ->
      kinding_validated E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      CSet.Subset cs1' cs1 ->
      CSet.Nonempty cs1' ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      valid_env E ->
      type_equal_core_validated E
        (typ_proj (typ_or T1 T2) cs1') (typ_proj T1 cs1')
        (knd_row cs1')
  | type_equal_core_validated_proj_or_r : forall E T1 T2 cs1 cs2 cs2',
      kinding_validated E T1 (knd_row cs1) ->
      kinding_validated E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      CSet.Subset cs2' cs2 ->
      CSet.Nonempty cs2' ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      valid_env E ->
      type_equal_core_validated E
        (typ_proj (typ_or T1 T2) cs2') (typ_proj T2 cs2')
        (knd_row cs2')
  | type_equal_core_validated_proj_or_both :
      forall E T1 T2 cs1 cs2 cs1' cs2' cs12',
      kinding_validated E T1 (knd_row cs1) ->
      kinding_validated E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      CSet.Subset cs1' cs1 ->
      CSet.Nonempty cs1' ->
      CSet.Subset cs2' cs2 ->
      CSet.Nonempty cs2' ->
      cs12' = CSet.union cs1' cs2' ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      valid_env E ->
      type_equal_core_validated E
        (typ_proj (typ_or T1 T2) cs12')
        (typ_or (typ_proj T1 cs1') (typ_proj T2 cs2'))
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
      valid_env E ->
      type_equal_core_validated E
        (typ_proj (typ_meet T1 T2) cs')
        (typ_meet (typ_proj T1 cs') (typ_proj T2 cs'))
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
      valid_env E ->
      type_equal_core_validated E
        (typ_proj (typ_join T1 T2) cs')
        (typ_join (typ_proj T1 cs') (typ_proj T2 cs'))
        (knd_row cs')
  | type_equal_core_validated_meet_commutative : forall E T1 T2 cs,
      kinding_validated E T1 (knd_row cs) ->
      kinding_validated E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env E ->
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
      valid_env E ->
      type_equal_core_validated E
        (typ_meet T1 (typ_meet T2 T3))
        (typ_meet (typ_meet T1 T2) T3)
        (knd_row cs)
  | type_equal_core_validated_meet_identity : forall E T1 cs,
      kinding_validated E T1 (knd_row cs) ->
      environment E ->
      type T1 ->
      CSet.Nonempty cs ->
      valid_env E ->
      type_equal_core_validated E
        (typ_meet T1 (typ_top cs)) T1 (knd_row cs)
  | type_equal_core_validated_meet_absorption : forall E T1 T2 cs,
      kinding_validated E T1 (knd_row cs) ->
      kinding_validated E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env E ->
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
      valid_env E ->
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
      valid_env E ->
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
      valid_env E ->
      type_equal_core_validated E
        (typ_join T1 (typ_join T2 T3))
        (typ_join (typ_join T1 T2) T3)
        (knd_row cs)
  | type_equal_core_validated_join_identity : forall E T1 cs,
      kinding_validated E T1 (knd_row cs) ->
      environment E ->
      type T1 ->
      CSet.Nonempty cs ->
      valid_env E ->
      type_equal_core_validated E
        (typ_join T1 (typ_bot cs)) T1 (knd_row cs)
  | type_equal_core_validated_join_absorption : forall E T1 T2 cs,
      kinding_validated E T1 (knd_row cs) ->
      kinding_validated E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env E ->
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
      valid_env E ->
      type_equal_core_validated E
        (typ_join T1 (typ_meet T2 T3))
        (typ_meet (typ_join T1 T2) (typ_join T1 T3))
        (knd_row cs)

with type_equal_cong_validated : env -> typ -> typ -> knd -> Prop :=
  | type_equal_cong_validated_constructor : forall E c T1 T1' cs,
      type_equal_cong_validated E T1 T1' knd_type ->
      cs = CSet.singleton c ->
      environment E ->
      type T1 ->
      type T1' ->
      valid_env E ->
      kinding E T1 knd_type ->
      kinding E T1' knd_type ->
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
      valid_env E ->
      kinding E T1 (knd_row cs1) ->
      kinding E T1' (knd_row cs1) ->
      type_equal_cong_validated E
        (typ_or T1 T2) (typ_or T1' T2) (knd_row cs12)
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
      valid_env E ->
      kinding E T2 (knd_row cs2) ->
      kinding E T2' (knd_row cs2) ->
      type_equal_cong_validated E
        (typ_or T1 T2) (typ_or T1 T2') (knd_row cs12)
  | type_equal_cong_validated_row : forall E T1 T1',
      type_equal_cong_validated E T1 T1' (knd_row CSet.universe) ->
      environment E ->
      type T1 ->
      type T1' ->
      valid_env E ->
      kinding E T1 (knd_row CSet.universe) ->
      kinding E T1' (knd_row CSet.universe) ->
      type_equal_cong_validated E
        (typ_row T1) (typ_row T1') (knd_range T1 T1)
  | type_equal_cong_validated_variant : forall E T1 T1' T2 T3,
      type_equal_cong_validated E T1 T1' (knd_range T2 T3) ->
      environment E ->
      type T1 ->
      type T1' ->
      type T2 ->
      type T3 ->
      valid_env E ->
      kinding E T1 (knd_range T2 T3) ->
      kinding E T1' (knd_range T2 T3) ->
      kinding E T2 (knd_row CSet.universe) ->
      kinding E T3 (knd_row CSet.universe) ->
      subtype E T3 T2 CSet.universe ->
      type_equal_cong_validated E
        (typ_variant T1) (typ_variant T1') (knd_range T2 T3)
  | type_equal_cong_validated_arrow_l : forall E T1 T1' T2,
      kinding_validated E T2 knd_type ->
      type_equal_cong_validated E T1 T1' knd_type ->
      environment E ->
      type T1 ->
      type T1' ->
      type T2 ->
      valid_env E ->
      kinding E T1 knd_type ->
      kinding E T1' knd_type ->
      type_equal_cong_validated E
        (typ_arrow T1 T2) (typ_arrow T1' T2) knd_type
  | type_equal_cong_validated_arrow_r : forall E T1 T2 T2',
      kinding_validated E T1 knd_type ->
      type_equal_cong_validated E T2 T2' knd_type ->
      environment E ->
      type T1 ->
      type T2 ->
      type T2' ->
      valid_env E ->
      kinding E T2 knd_type ->
      kinding E T2' knd_type ->
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
      valid_env E ->
      kinding E T1 (knd_row cs) ->
      kinding E T1' (knd_row cs) ->
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
      valid_env E ->
      kinding E T2 knd_type ->
      kinding E T2' knd_type ->
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
      valid_env E ->
      kinding E T1 knd_type ->
      kinding E T1' knd_type ->
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
      valid_env E ->
      kinding E T2 knd_type ->
      kinding E T2' knd_type ->
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
      valid_env E ->
      kinding E T1 (knd_range T3 T4) ->
      kinding E T2 (knd_range T3 T4) ->
      kinding E T3 (knd_row CSet.universe) ->
      kinding E T3' (knd_row CSet.universe) ->
      kinding E T4 (knd_row CSet.universe) ->
      kinding E T4' (knd_row CSet.universe) ->
      subtype E T4 T3 CSet.universe ->
      subtype E T4' T3' CSet.universe ->
      type_equal_cong_validated E T1 T2 (knd_range T3' T4')
  | type_equal_cong_validated_core : forall E T1 T1' K,
      type_equal_core_validated E T1 T1' K ->
      environment E ->
      type T1 ->
      type T1' ->
      kind K ->
      valid_env E ->
      kinding E T1 K ->
      kinding E T1' K ->
      valid_kind E K ->
      type_equal_cong_validated E T1 T1' K

with type_equal_symm_validated : env -> typ -> typ -> knd -> Prop :=
  | type_equal_symm_validated_l : forall E T1 T2 K,
      type_equal_cong_validated E T1 T2 K ->
      environment E ->
      type T1 ->
      type T2 ->
      kind K ->
      valid_env E ->
      kinding E T1 K ->
      kinding E T2 K ->
      valid_kind E K ->
      type_equal_symm_validated E T1 T2 K
  | type_equal_symm_validated_r : forall E T1 T2 K,
      type_equal_cong_validated E T1 T2 K ->
      environment E ->
      type T1 ->
      type T2 ->
      kind K ->
      valid_env E ->
      kinding E T1 K ->
      kinding E T2 K ->
      valid_kind E K ->
      type_equal_symm_validated E T2 T1 K

with type_equal_validated : env -> typ -> typ -> knd -> Prop :=
  | type_equal_validated_refl : forall E T K,
      kinding_validated E T K ->
      environment E ->
      type T ->
      kind K ->
      valid_env E ->
      valid_kind E K ->
      type_equal_validated E T T K
  | type_equal_validated_step : forall E T1 T2 T3 K,
      type_equal_symm_validated E T1 T2 K ->
      type_equal_validated E T2 T3 K ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      kind K ->
      valid_env E ->
      kinding E T1 K ->
      kinding E T2 K ->
      kinding E T3 K ->
      valid_kind E K ->
      type_equal_validated E T1 T3 K

with subtype_validated : env -> typ -> typ -> cset -> Prop :=
  | subtype_validated_c : forall E T1 T2 cs,
      type_equal_validated E T1 (typ_meet T1 T2) (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      valid_env E ->
      kinding E T1 (knd_row cs) ->
      kinding E T2 (knd_row cs) ->
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
  with type_equal_cong_validated_mutind :=
         Induction for type_equal_cong_validated Sort Prop
  with type_equal_symm_validated_mutind :=
         Induction for type_equal_symm_validated Sort Prop
  with type_equal_validated_mutind :=
         Induction for type_equal_validated Sort Prop
  with subtype_validated_mutind :=
         Induction for subtype_validated Sort Prop.

Combined Scheme combined_kinding_validated_mutind
  from valid_kind_validated_mutind, kinding_validated_mutind,
       valid_scheme_vars_validated_mutind, valid_scheme_validated_mutind,
       valid_env_validated_mutind, type_equal_core_validated_mutind,
       type_equal_cong_validated_mutind, type_equal_symm_validated_mutind,
       type_equal_validated_mutind, subtype_validated_mutind.

Lemma valid_kind_validated_inv : forall E K,
    valid_kind_validated E K ->
    environment E /\ kind K.
Proof.
  introv Hv.
  destruct Hv; auto.
Qed.

Hint Constructors valid_kind_validated : valid_kind_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_kind_validated E _ |- _ =>
      apply (proj1 (valid_kind_validated_inv H))
  end : valid_kind_validated.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : valid_kind_validated _ K |- _ =>
      apply (proj2 (valid_kind_validated_inv H))
  end : valid_kind_validated.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : valid_kind_validated _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj2 (valid_kind_validated_inv H));
      inversion Hknd; assumption
  end : valid_kind_validated.

Lemma kinding_validated_inv : forall E T K,
    kinding_validated E T K ->
    environment E /\ type T /\ kind K.
Proof.
  introv Hk.
  destruct Hk; auto with csetdec.
Qed.

Hint Constructors kinding_validated : kinding_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : kinding_validated E _ _ |- _ =>
      apply (proj31 (kinding_validated_inv H))
  end : kinding_validated.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : kinding_validated _ T _ |- _ =>
      apply (proj32 (kinding_validated_inv H))
  end : kinding_validated.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : kinding_validated _ _ K |- _ =>
      apply (proj33 (kinding_validated_inv H))
  end : kinding_validated.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : kinding_validated _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj33 (kinding_validated_inv H));
      inversion Hknd; assumption
  end : kinding_validated.

Lemma valid_scheme_vars_validated_inv : forall E M Xs,
    valid_scheme_vars_validated E M Xs ->
    environment E /\ scheme_vars M Xs.
Proof.
  introv Hs.
  destruct Hs; auto.
Qed.

Hint Constructors valid_scheme_vars_validated
  : valid_scheme_vars_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_scheme_vars_validated E _ _ |- _ =>
      apply (proj1 (valid_scheme_vars_validated_inv H))
  end : valid_scheme_vars_validated.

Hint Extern 1 (scheme_vars ?M ?Xs) =>
  match goal with
  | H : valid_scheme_vars_validated _ M Xs |- _ =>
      apply (proj2 (valid_scheme_vars_validated_inv H))
  end : valid_scheme_vars_validated.

Lemma valid_scheme_validated_inv : forall E M,
    valid_scheme_validated E M ->
    environment E /\ scheme M.
Proof.
  introv Hs.
  destruct Hs; auto.
Qed.

Hint Constructors valid_scheme_validated : valid_scheme_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_scheme_validated E _ |- _ =>
      apply (proj1 (valid_scheme_validated_inv H))
  end : valid_scheme_validated.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H : valid_scheme_validated _ M |- _ =>
      apply (proj2 (valid_scheme_validated_inv H))
  end : valid_scheme_validated.

Lemma valid_env_validated_inv : forall E,
    valid_env_validated E -> environment E.
Proof.
  introv He.
  destruct He; auto.
Qed.

Hint Constructors valid_env_validated : valid_env_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_env_validated E |- _ =>
      apply (valid_env_validated_inv H)
  end : valid_env_validated.

Lemma type_equal_core_validated_inv : forall E T1 T2 K,
    type_equal_core_validated E T1 T2 K ->
    environment E /\ type T1 /\ type T2 /\ kind K.
Proof.
  introv Hte.
  destruct Hte; subst; split; auto with csetdec.
Qed.

Hint Constructors type_equal_core_validated : type_equal_core_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_core_validated E _ _ _ |- _ =>
      apply (proj41 (type_equal_core_validated_inv H))
  end : type_equal_core_validated.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_core_validated _ T _ _ |- _ =>
      apply (proj42 (type_equal_core_validated_inv H))
  | H : type_equal_core_validated _ _ T _ |- _ =>
      apply (proj43 (type_equal_core_validated_inv H))
  end : type_equal_core_validated.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_core_validated _ _ _ K |- _ =>
      apply (proj44 (type_equal_core_validated_inv H))
  end : type_equal_core_validated.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_core_validated _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_core_validated_inv H));
      inversion Hknd; assumption
  end : type_equal_core_validated.

Lemma type_equal_cong_validated_inv : forall E T1 T2 K,
    type_equal_cong_validated E T1 T2 K ->
    environment E /\ type T1 /\ type T2 /\ kind K.
Proof.
  introv Hte.
  destruct Hte; split; auto with csetdec.
Qed.

Hint Constructors type_equal_cong_validated : type_equal_cong_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_cong_validated E _ _ _ |- _ =>
      apply (proj41 (type_equal_cong_validated_inv H))
  end : type_equal_cong_validated.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_cong_validated _ T _ _ |- _ =>
      apply (proj42 (type_equal_cong_validated_inv H))
  | H : type_equal_cong_validated _ _ T _ |- _ =>
      apply (proj43 (type_equal_cong_validated_inv H))
  end : type_equal_cong_validated.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_cong_validated _ _ _ K |- _ =>
      apply (proj44 (type_equal_cong_validated_inv H))
  end : type_equal_cong_validated.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_cong_validated _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_cong_validated_inv H));
      inversion Hknd; assumption
  end : type_equal_cong_validated.

Lemma type_equal_symm_validated_inv : forall E T1 T2 K,
    type_equal_symm_validated E T1 T2 K ->
    environment E /\ type T1 /\ type T2 /\ kind K.
Proof.
  introv Hte.
  destruct Hte; auto.
Qed.

Hint Constructors type_equal_symm_validated : type_equal_symm_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_symm_validated E _ _ _ |- _ =>
      apply (proj41 (type_equal_symm_validated_inv H))
  end : type_equal_symm_validated.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_symm_validated _ T _ _ |- _ =>
      apply (proj42 (type_equal_symm_validated_inv H))
  | H : type_equal_symm_validated _ _ T _ |- _ =>
      apply (proj43 (type_equal_symm_validated_inv H))
  end : type_equal_symm_validated.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_symm_validated _ _ _ K |- _ =>
      apply (proj44 (type_equal_symm_validated_inv H))
  end : type_equal_symm_validated.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_symm_validated _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_symm_validated_inv H));
      inversion Hknd; assumption
  end : type_equal_symm_validated.

Lemma type_equal_validated_inv : forall E T1 T2 K,
    type_equal_validated E T1 T2 K ->
    environment E /\ type T1 /\ type T2 /\ kind K.
Proof.
  introv Hk.
  destruct Hk; auto.
Qed.

Hint Constructors type_equal_validated : type_equal_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_validated E _ _ _ |- _ =>
      apply (proj41 (type_equal_validated_inv H))
  end : type_equal_validated.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_validated _ T _ _ |- _ =>
      apply (proj42 (type_equal_validated_inv H))
  | H : type_equal_validated _ _ T _ |- _ =>
      apply (proj43 (type_equal_validated_inv H))
  end : type_equal_validated.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_validated _ _ _ K |- _ =>
      apply (proj44 (type_equal_validated_inv H))
  end : type_equal_validated.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_validated _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_validated_inv H));
      inversion Hknd; assumption
  end : type_equal_validated.

Lemma subtype_validated_inv : forall E T1 T2 cs,
    subtype_validated E T1 T2 cs ->
    environment E /\ type T1 /\ type T2 /\ CSet.Nonempty cs.
Proof.
  introv Hk.
  destruct Hk; auto.
Qed.

Hint Constructors subtype_validated : subtype_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : subtype_validated E _ _ _ |- _ =>
      apply (proj41 (subtype_validated_inv H))
  end : subtype_validated.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : subtype_validated _ T _ _ |- _ =>
      apply (proj42 (subtype_validated_inv H))
  | H : subtype_validated _ _ T _ |- _ =>
      apply (proj43 (subtype_validated_inv H))
  end : subtype_validated.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : subtype_validated _ _ _ cs |- _ =>
      apply (proj44 (subtype_validated_inv H))
  end : subtype_validated.

Lemma validated_combined_kinding :
  (forall E K, valid_kind E K -> valid_kind_validated E K)
  /\ (forall E T K, kinding E T K -> kinding_validated E T K)
  /\ (forall E M Xs,
         valid_scheme_vars E M Xs -> valid_scheme_vars_validated E M Xs)
  /\ (forall E M, valid_scheme E M -> valid_scheme_validated E M)
  /\ (forall E, valid_env E -> valid_env_validated E)
  /\ (forall E T1 T2 K,
       type_equal_core E T1 T2 K -> type_equal_core_validated E T1 T2 K)
  /\ (forall E T1 T2 K,
       type_equal_cong E T1 T2 K -> type_equal_cong_validated E T1 T2 K)
  /\ (forall E T1 T2 K,
       type_equal_symm E T1 T2 K -> type_equal_symm_validated E T1 T2 K)
  /\ (forall E T1 T2 K,
       type_equal E T1 T2 K -> type_equal_validated E T1 T2 K)
  /\ (forall E T1 T2 cs,
       subtype E T1 T2 cs -> subtype_validated E T1 T2 cs).
Proof.
  apply combined_kinding_mutind; intros; subst;
    econstr auto with valid_kind_validated kinding_validated
           valid_scheme_vars_validated valid_scheme_validated
           valid_env_validated type_equal_core_validated
           type_equal_cong_validated type_equal_symm_validated
           type_equal_validated subtype_validated.
  - assert (environment E) by auto with valid_env_validated.
    assert (kind K) by (eapply kind_from_env; eassumption).
    auto with kinding_validated.
  - assert (kind (knd_range T1 T2)) as Hknd
      by auto with kinding_validated.
    inversion Hknd; subst.
    apply kinding_validated_variant with (T1 := T1) (T2 := T2);
      auto with kinding_validated.
  - apply valid_scheme_validated_c with (L := L); try assumption.
    + pick_freshes_gen L (sch_arity M) Xs.
      assert (valid_scheme_vars_validated E M Xs) by auto.
      auto with valid_scheme_vars_validated.
    + exists L. intros.
      assert (valid_scheme_vars_validated E M Xs) by auto.
      auto with valid_scheme_vars_validated.
  - assert (kind (knd_range T2 T3)) as Hknd
      by auto with type_equal_cong_validated.
    inversion Hknd; subst.
    auto with type_equal_cong_validated.
  - assert (type (typ_meet T1 T2)) as Ht
      by auto with type_equal_validated.
    inversion Ht; subst.
    auto with subtype_validated type_equal_validated.
Qed.

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
       type_equal_cong_validated E T1 T2 K -> type_equal_cong E T1 T2 K)
  /\ (forall E T1 T2 K,
       type_equal_symm_validated E T1 T2 K -> type_equal_symm E T1 T2 K)
  /\ (forall E T1 T2 K,
       type_equal_validated E T1 T2 K -> type_equal E T1 T2 K)
  /\ (forall E T1 T2 cs,
       subtype_validated E T1 T2 cs -> subtype E T1 T2 cs).
Proof.
  apply combined_kinding_validated_mutind; intros; subst; econstr auto.
Qed.

Lemma validated_valid_kind : forall E K,
    valid_kind E K -> valid_kind_validated E K.
Proof.
  pose validated_combined_kinding.
  tauto.
Qed.

Lemma unvalidated_valid_kind : forall T1 T2,
    valid_kind_validated T1 T2 -> valid_kind T1 T2.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_valid_kind.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_kind E _ |- _ =>
      apply (proj1 (valid_kind_validated_inv
                      (validated_valid_kind H)))
  end : valid_kind_validated.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : valid_kind _ K |- _ =>
      apply (proj2 (valid_kind_validated_inv
                      (validated_valid_kind H)))
  end : valid_kind_validated.

Lemma validated_kinding : forall E T K,
    kinding E T K -> kinding_validated E T K.
Proof.
  pose validated_combined_kinding.
  tauto.
Qed.

Lemma unvalidated_kinding : forall E T K,
    kinding_validated E T K -> kinding E T K.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_kinding.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : kinding E _ _ |- _ =>
      apply (proj31 (kinding_validated_inv (validated_kinding H)))
  end : kinding_validated.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : kinding _ T _ |- _ =>
      apply (proj32 (kinding_validated_inv (validated_kinding H)))
  end : kinding_validated.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : kinding _ _ K |- _ =>
      apply (proj33 (kinding_validated_inv (validated_kinding H)))
  end : kinding_validated.

Lemma validated_valid_scheme_vars : forall E M Xs,
    valid_scheme_vars E M Xs -> valid_scheme_vars_validated E M Xs.
Proof.
  pose validated_combined_kinding.
  tauto.
Qed.

Lemma unvalidated_valid_scheme_vars : forall E M Xs,
    valid_scheme_vars_validated E M Xs -> valid_scheme_vars E M Xs.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_valid_scheme_vars.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_scheme_vars E _ _ |- _ =>
      apply (proj1 (valid_scheme_vars_validated_inv
                      (validated_valid_scheme_vars H)))
  end : valid_scheme_vars_validated.

Hint Extern 1 (scheme_vars ?M ?Xs) =>
  match goal with
  | H : valid_scheme_vars _ M Xs |- _ =>
      apply (proj2 (valid_scheme_vars_validated_inv
                      (validated_valid_scheme_vars H)))
  end : valid_scheme_vars_validated.

Lemma validated_valid_scheme : forall E M,
    valid_scheme E M -> valid_scheme_validated E M.
Proof.
  pose validated_combined_kinding.
  tauto.
Qed.

Lemma unvalidated_valid_scheme : forall E M,
    valid_scheme_validated E M -> valid_scheme E M.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_valid_scheme.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_scheme E _ |- _ =>
      apply (proj1 (valid_scheme_validated_inv
                      (validated_valid_scheme H)))
  end : valid_scheme_validated.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H : valid_scheme _ M |- _ =>
      apply (proj2 (valid_scheme_validated_inv
                      (validated_valid_scheme H)))
  end : valid_scheme_validated.

Lemma validated_valid_env : forall E,
    valid_env E -> valid_env_validated E.
Proof.
  pose validated_combined_kinding.
  tauto.
Qed.

Lemma unvalidated_valid_env : forall E,
    valid_env_validated E -> valid_env E.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_valid_env.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_env E |- _ =>
      apply (valid_env_validated_inv
               (validated_valid_env H))
  end : valid_env_validated.

Lemma validated_type_equal_core : forall E T1 T2 K,
    type_equal_core E T1 T2 K -> type_equal_core_validated E T1 T2 K.
Proof.
  pose validated_combined_kinding.
  tauto.
Qed.

Lemma unvalidated_type_equal_core : forall E T1 T2 K,
    type_equal_core_validated E T1 T2 K -> type_equal_core E T1 T2 K.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_type_equal_core.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_core E _ _ _ |- _ =>
      apply (proj41 (type_equal_core_validated_inv
                       (validated_type_equal_core H)))
  end : type_equal_core_validated.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_core _ T _ _ |- _ =>
      apply (proj42 (type_equal_core_validated_inv
                       (validated_type_equal_core H)))
  | H : type_equal_core _ _ T _ |- _ =>
      apply (proj43 (type_equal_core_validated_inv
                       (validated_type_equal_core H)))
  end : type_equal_core_validated.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_core _ _ _ K |- _ =>
      apply (proj44 (type_equal_core_validated_inv
                       (validated_type_equal_core H)))
  end : type_equal_core_validated.

Lemma validated_type_equal_cong : forall E T1 T2 K,
    type_equal_cong E T1 T2 K -> type_equal_cong_validated E T1 T2 K.
Proof.
  pose validated_combined_kinding.
  tauto.
Qed.

Lemma unvalidated_type_equal_cong : forall E T1 T2 K,
    type_equal_cong_validated E T1 T2 K -> type_equal_cong E T1 T2 K.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_type_equal_cong.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_cong E _ _ _ |- _ =>
      apply (proj41 (type_equal_cong_validated_inv
                       (validated_type_equal_cong H)))
  end : type_equal_cong_validated.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_cong _ T _ _ |- _ =>
      apply (proj42 (type_equal_cong_validated_inv
                       (validated_type_equal_cong H)))
  | H : type_equal_cong _ _ T _ |- _ =>
      apply (proj43 (type_equal_cong_validated_inv
                       (validated_type_equal_cong H)))
  end : type_equal_cong_validated.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_cong _ _ _ K |- _ =>
      apply (proj44 (type_equal_cong_validated_inv
                       (validated_type_equal_cong H)))
  end : type_equal_cong_validated.

Lemma validated_type_equal_symm : forall E T1 T2 K,
    type_equal_symm E T1 T2 K -> type_equal_symm_validated E T1 T2 K.
Proof.
  pose validated_combined_kinding.
  tauto.
Qed.

Lemma unvalidated_type_equal_symm : forall E T1 T2 K,
    type_equal_symm_validated E T1 T2 K -> type_equal_symm E T1 T2 K.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_type_equal_symm.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_symm E _ _ _ |- _ =>
      apply (proj41 (type_equal_symm_validated_inv
                       (validated_type_equal_symm H)))
  end : type_equal_symm_validated.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_symm _ T _ _ |- _ =>
      apply (proj42 (type_equal_symm_validated_inv
                       (validated_type_equal_symm H)))
  | H : type_equal_symm _ _ T _ |- _ =>
      apply (proj43 (type_equal_symm_validated_inv
                       (validated_type_equal_symm H)))
  end : type_equal_symm_validated.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_symm _ _ _ K |- _ =>
      apply (proj44 (type_equal_symm_validated_inv
                       (validated_type_equal_symm H)))
  end : type_equal_symm_validated.

Lemma validated_type_equal : forall E T1 T2 K,
    type_equal E T1 T2 K -> type_equal_validated E T1 T2 K.
Proof.
  pose validated_combined_kinding.
  tauto.
Qed.

Lemma unvalidated_type_equal : forall E T1 T2 K,
    type_equal_validated E T1 T2 K -> type_equal E T1 T2 K.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_type_equal.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal E _ _ _ |- _ =>
      apply (proj41 (type_equal_validated_inv
                       (validated_type_equal H)))
  end : type_equal_validated.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal _ T _ _ |- _ =>
      apply (proj42 (type_equal_validated_inv
                       (validated_type_equal H)))
  | H : type_equal _ _ T _ |- _ =>
      apply (proj43 (type_equal_validated_inv
                       (validated_type_equal H)))
  end : type_equal_validated.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal _ _ _ K |- _ =>
      apply (proj44 (type_equal_validated_inv
                       (validated_type_equal H)))
  end : type_equal_validated.

Lemma validated_subtype : forall E T1 T2 K,
    subtype E T1 T2 K -> subtype_validated E T1 T2 K.
Proof.
  pose validated_combined_kinding.
  tauto.
Qed.

Lemma unvalidated_subtype : forall E T1 T2 K,
    subtype_validated E T1 T2 K -> subtype E T1 T2 K.
Proof.
  pose unvalidated_combined_kinding.
  tauto.
Qed.

Hint Resolve unvalidated_subtype.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : subtype E _ _ _ |- _ =>
      apply (proj41 (subtype_validated_inv
                       (validated_subtype H)))
  end : subtype_validated.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : subtype _ T _ _ |- _ =>
      apply (proj42 (subtype_validated_inv
                       (validated_subtype H)))
  | H : subtype _ _ T _ |- _ =>
      apply (proj43 (subtype_validated_inv
                       (validated_subtype H)))
  end : subtype_validated.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : subtype _ _ _ cs |- _ =>
      apply (proj44 (subtype_validated_inv
                       (validated_subtype H)))
  end : subtype_validated.

Inductive valid_instance_validated : env -> list typ -> sch -> Prop :=
  | valid_instance_validated_empty : forall E T,
      kinding E T knd_type ->
      environment E ->
      type T ->
      types (sch_arity (sch_empty T)) nil ->
      valid_instance_validated E nil (sch_empty T)
  | valid_instance_validated_bind : forall E K M T Ts,
      kinding E T K ->
      valid_instance_validated E Ts (M ^^ T) ->
      environment E ->
      type T ->
      types (sch_arity M) Ts ->
      scheme (M ^^ T) ->
      kind K ->
      types (sch_arity (sch_bind K M)) (T :: Ts) ->
      valid_instance_validated E (T :: Ts) (sch_bind K M).

Lemma valid_instance_validated_inv : forall E Ts M,
    valid_instance_validated E Ts M ->
    environment E /\ types (sch_arity M) Ts /\ scheme M.
Proof.
  introv Hi.
  induction Hi; splits; auto.
  assert (scheme (M ^^ T)) as Hs by assumption.
  destruct Hs as [L Hs].
  pick_fresh_gen (L \u sch_fv M) Y.
  exists (L \u \{Y}).
  introv Hl.
  destruct Xs.
  + contradict Hl.
  + destruct Hl.
    apply scheme_vars_bind; auto.
    unfold sch_open_var.
    rewrite sch_subst_intro with (X := Y); auto.
    rewrite sch_subst_vars_type; autorewrite with rew_sch_arity; auto.
    autorewrite with rew_sch_arity in *.
    assert (scheme_vars (sch_open M T) Xs) as Hsv by auto.
    rewrite sch_subst_intro with (X := Y) in Hsv; auto.
    rewrite sch_subst_vars_type in Hsv;
      autorewrite with rew_sch_arity; auto.
Qed.

Hint Constructors valid_instance_validated : valid_instance_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_instance_validated E _ _ |- _ =>
      apply (proj31 (valid_instance_validated_inv H))
  end : valid_instance_validated.

Hint Extern 1 (types (sch_arity ?M) ?Ts) =>
  match goal with
  | H : valid_instance_validated _ Ts M |- _ =>
      apply (proj32 (valid_instance_validated_inv H))
  end : valid_instance_validated.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H : valid_instance_validated _ _ M |- _ =>
      apply (proj33 (valid_instance_validated_inv H))
  end : valid_instance_validated.

Lemma validated_valid_instance : forall E Ts M,
    valid_instance E Ts M -> valid_instance_validated E Ts M.
Proof.
  introv Hi.
  induction Hi; auto with valid_instance_validated.
  - auto with valid_instance_validated kinding_validated.
  - assert (type T) by auto with kinding_validated.
    assert (types (sch_arity (sch_open M T)) Ts) as Hts
      by auto with valid_instance_validated.
    destruct Hts as [Hl Hts].
    apply valid_instance_validated_bind;
      auto with valid_instance_validated kinding_validated.
    + rewrite <- sch_open_arity with (U := T).
      auto with valid_instance_validated.
    + autorewrite with rew_sch_arity in Hl.
      split; simpl; auto.
Qed.

Lemma unvalidated_valid_instance : forall E Ts M,
    valid_instance_validated E Ts M -> valid_instance E Ts M.
Proof.
  introv Hi.
  induction Hi; auto using valid_instance.
Qed.

Hint Resolve unvalidated_valid_instance.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_instance E _ _ |- _ =>
      apply (proj31 (valid_instance_validated_inv
                       (validated_valid_instance H)))
  end : valid_instance_validated.

Hint Extern 1 (types (sch_arity ?M) ?Ts) =>
  match goal with
  | H : valid_instance _ Ts M |- _ =>
      apply (proj32 (valid_instance_validated_inv
                       (validated_valid_instance H)))
  end : valid_instance_validated.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H : valid_instance_validated _ _ M |- _ =>
      apply (proj33 (valid_instance_validated_inv
                       (validated_valid_instance H)))
  end : valid_instance_validated.

Inductive typing_validated : env -> trm -> typ -> Prop :=
  | typing_validated_var : forall E x M Us,
      environment E ->
      scheme M ->
      types (sch_arity M) Us ->
      type (instance M Us) ->
      valid_env E -> 
      binds x (bind_typ M) E -> 
      valid_instance E Us M ->
      typing_validated E (trm_fvar x) (instance M Us)
  | typing_validated_abs : forall L E T1 T2 t1,
      environment E ->
      (forall x, x \notin L ->
         environment (E & x ~ bind_typ (sch_empty T1))) ->
      type T1 ->
      type T2 ->
      term_body t1 ->
      (forall x, x \notin L -> 
        typing_validated
          (E & x ~ bind_typ (sch_empty T1)) (t1 ^ x) T2) -> 
      typing_validated E (trm_abs t1) (typ_arrow T1 T2)
  | typing_validated_app : forall E S T t1 t2, 
      environment E ->
      type S ->
      type T ->
      term t1 ->
      term t2 ->
      typing_validated E t1 (typ_arrow S T) ->
      typing_validated E t2 S ->   
      typing_validated E (trm_app t1 t2) T
  | typing_validated_let : forall M L E T2 t1 t2,
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
      (forall Xs, fresh L (sch_arity M) Xs ->
         typing_validated
           (E & Xs ~::* M)
           t1 (instance_vars M Xs)) ->
      (forall x, x \notin L ->
         typing_validated (E & x ~ (bind_typ M)) (t2 ^ x) T2) -> 
      typing_validated E (trm_let t1 t2) T2
  | typing_validated_constructor : forall c E T1 T2 T3 t,
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      term t ->
      kinding E T1 (knd_range (typ_top CSet.universe) T2) ->
      subtype E
        (typ_proj T2 (CSet.singleton c))
        (typ_constructor c T3)
        (CSet.singleton c) ->
      typing_validated E t T3 ->
      typing_validated E (trm_constructor c t) (typ_variant T1)
  | typing_validated_match : forall c L E T1 T2 T3 T4 T5
                          T6 T7 T8 t1 t2 t3,
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
      kinding E T1 (knd_range T2 (typ_bot CSet.universe)) ->
      kinding E T3 (knd_range (typ_top CSet.universe) T4) ->
      kinding E T5 (knd_range (typ_top CSet.universe) T6) ->
      subtype E
        (typ_proj T2 (CSet.singleton c))
        (typ_constructor c T7)
        (CSet.singleton c) ->
      subtype E
        (typ_proj T2 (CSet.singleton c))
        (typ_proj T4 (CSet.singleton c))
        (CSet.singleton c) ->
      subtype E
        (typ_proj T2 (CSet.cosingleton c))
        (typ_proj T6 (CSet.cosingleton c))
        (CSet.cosingleton c) ->
      typing_validated E t1 (typ_variant T1) ->
      (forall x, x \notin L ->
         typing_validated (E & x ~: (sch_empty (typ_variant T3)))
                (t2 ^ x) T8) ->
      (forall y, y \notin L -> 
         typing_validated (E & y ~: (sch_empty (typ_variant T5)))
                (t3 ^ y) T8) ->
      typing_validated E (trm_match t1 c t2 t3) T8
  | typing_validated_destruct : forall c L E T1 T2 T3 T4 t1 t2,
      environment E ->
      (forall x, x \notin L ->
         environment (E & x ~: (sch_empty T3))) ->
      type T1 ->
      type T2 ->
      type T3 ->
      type T4 ->
      term t1 ->
      term_body t2 ->
      kinding E T1 (knd_range T2 (typ_bot CSet.universe)) ->
      subtype E
        (typ_constructor c T3)
        (typ_proj T2 (CSet.singleton c))
        (CSet.singleton c) ->
      typing_validated E t1 (typ_variant T1) ->
      (forall x, x \notin L ->
         typing_validated (E & x ~: (sch_empty T3))
                (t2 ^ x) T4) ->
      typing_validated E (trm_destruct t1 c t2) T4
  | typing_validated_absurd : forall E T1 T2 t1,
      environment E ->
      type T1 ->
      type T2 ->
      term t1 ->
      kinding E T1 (knd_range (typ_bot CSet.universe)
                              (typ_bot CSet.universe)) ->
      kinding E T2 knd_type ->
      typing_validated E t1 (typ_variant T1) ->
      typing_validated E (trm_absurd t1) T2.

Lemma typing_validated_inv : forall E t T,
    typing_validated E t T ->
      environment E /\ term t /\ type T.
Proof.
  introv Ht.
  induction Ht; auto.
Qed.

Hint Constructors typing_validated : typing_validated.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : typing_validated E _ _ |- _ =>
      apply (proj31 (typing_validated_inv H))
  end : typing_validated.

Hint Extern 1 (term ?t) =>
  match goal with
  | H : typing_validated _ t _ |- _ =>
      apply (proj32 (typing_validated_inv H))
  end : typing_validated.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : typing_validated _ _ T |- _ =>
      apply (proj33 (typing_validated_inv H))
  end : typing_validated.

Lemma validated_typing : forall E t T,
    typing E t T -> typing_validated E t T.
Proof.
  introv Ht.
  induction Ht.
  - assert (environment E)
      by auto with valid_env_validated.
    assert (scheme M)
      by (eapply scheme_from_env; eassumption).
    assert (types (sch_arity M) Us)
      by auto with valid_instance_validated.   
    assert (type (instance M Us))
      by auto using scheme_instance_type.
    auto with typing_validated.
  - pick_fresh_gen L x.
    assert (typing_validated (E & x ~: sch_empty T1) (t1 ^ x) T2)
      by auto.
    apply typing_validated_abs with (L := L); auto with typing_validated.
    + eauto using environment_retract with typing_validated.
    + intros y Hn.
      assert (typing_validated (E & y ~: sch_empty T1) (t1 ^ y) T2)
        by auto.
      auto with typing_validated.
    + rewrite scheme_empty_type.
      eauto using scheme_from_env with typing_validated.
    + exists L.
      intros y Hny.
      assert (typing_validated (E & y ~: sch_empty T1) (t1 ^ y) T2)
        by auto.
      auto with typing_validated.
  - assert (type (typ_arrow S T)) as Hta
      by auto with typing_validated.
    inversion Hta; subst.
    eauto with typing_validated.
  - pick_freshes_gen L (sch_arity M) Xs.
    assert (typing_validated (E & Xs ~::* M) t1 (instance_vars M Xs))
      by auto.
    pick_fresh_gen L x.
    assert (typing_validated (E & x ~: M) (t2 ^ x) T2) by auto.
    apply typing_validated_let with (M := M) (L := L);
      auto with typing_validated.
    + eauto using environment_retract with typing_validated.
    + intros Ys Hf.
      assert (typing_validated (E & Ys ~::* M) t1 (instance_vars M Ys))
        by auto.
      auto with typing_validated.
    + intros y Hn.
      assert (typing_validated (E & y ~: M) (t2 ^ y) T2)
        by auto.
      auto with typing_validated.
    + intros Ys Hl.
      assert (typing_validated (E & Ys ~::* M) t1 (instance_vars M Ys))
        by auto.
      auto with typing_validated.
    + eauto using scheme_from_env with typing_validated.
    + exists L.
      intros y Hny.
      assert (typing_validated (E & y ~: M) (t2 ^ y) T2)
        by auto.
      auto with typing_validated.
  - assert (kind (knd_range (typ_top CSet.universe) T2)) as Hknd
        by auto with kinding_validated.
    inversion Hknd; subst.
    apply typing_validated_constructor with (T2 := T2) (T3 := T3);
      auto with typing_validated kinding_validated.
  - assert
      (kind (knd_range T2 (typ_bot CSet.universe))) as Hknd1
        by auto with kinding_validated.
    inversion Hknd1; subst.
    assert
      (kind (knd_range (typ_top CSet.universe) T4)) as Hknd2
      by auto with kinding_validated.
    inversion Hknd2; subst.
    assert
      (kind (knd_range (typ_top CSet.universe) T6)) as Hknd3
      by auto with kinding_validated.
    inversion Hknd3; subst.
    pick_fresh_gen L x.
    assert
      (typing_validated (E & x ~: sch_empty (typ_variant T3)) 
         (t2 ^ x) T8) by auto.
    apply typing_validated_match
      with (L := L) (T1 := T1) (T2 := T2) (T3 := T3)
           (T4 := T4) (T5 := T5) (T6 := T6) (T7 := T7);
      auto with typing_validated kinding_validated.
    + intros y Hny.
      assert
        (typing_validated (E & y ~: sch_empty (typ_variant T3)) 
                        (t2 ^ y) T8)
        by auto.
      auto with typing_validated.
    + intros y Hny.
      assert
        (typing_validated (E & y ~: sch_empty (typ_variant T5)) 
                        (t3 ^ y) T8)
        by auto.
      auto with typing_validated.
    + assert (type (typ_constructor c T7)) as Hto
          by auto with subtype_validated.
      inversion Hto; subst.
      assumption.
    + exists L.
      intros y Hny.
      assert
        (typing_validated (E & y ~: sch_empty (typ_variant T3)) 
                        (t2 ^ y) T8)
        by auto.
      auto with typing_validated.
    + exists L.
      intros y Hny.
      assert
        (typing_validated (E & y ~: sch_empty (typ_variant T5)) 
                        (t3 ^ y) T8)
        by auto.
      auto with typing_validated.
  - apply typing_validated_destruct
      with (L := L) (T1 := T1) (T2 := T2) (T3 := T3);
      auto with typing_validated kinding_validated.
    + intros y Hfy.
      assert (typing_validated (E & y ~: sch_empty T3) (t2 ^ y) T4)
        by auto.
      auto with typing_validated.
    + assert (type (typ_proj T2 (CSet.singleton c))) as Htp
        by auto with subtype_validated.
      inversion Htp; assumption.
    + assert (type (typ_constructor c T3)) as Htc
        by auto with subtype_validated.
      inversion Htc; assumption.
    + pick_fresh_gen L x.
      assert (typing_validated (E & x ~: sch_empty T3) (t2 ^ x) T4)
        by auto.
      auto with typing_validated.
    + exists L.
      intros y Hny.
      assert
        (typing_validated (E & y ~: sch_empty T3) (t2 ^ y) T4)
        by auto.
      auto with typing_validated.
  - apply typing_validated_absurd with (T1 := T1);
      auto with typing_validated kinding_validated.
Qed.

Lemma unvalidated_typing : forall E t T,
    typing_validated E t T -> typing E t T.
Proof.
  introv Ht.
  induction Ht; eauto using typing.
Qed.

Hint Resolve unvalidated_typing.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : typing E _ _ |- _ =>
      apply (proj31 (typing_validated_inv (validated_typing H)))
  end : typing_validated.

Hint Extern 1 (term ?t) =>
  match goal with
  | H : typing _ t _ |- _ =>
      apply (proj32 (typing_validated_inv (validated_typing H)))
  end : typing_validated.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : typing _ _ T |- _ =>
      apply (proj33 (typing_validated_inv (validated_typing H)))
  end : typing_validated.

(* *************************************************************** *)
(** * Convenient inversions of valid schemes *)

Lemma valid_scheme_bind_inv_sch : forall E K M X,
    X # E ->
    valid_scheme E (sch_bind K M) ->
    valid_scheme (E & X ~:: K) (M ^ X).
Proof.
  introv Hn Hs.
  remember (sch_bind K M) as Mb.
  destruct Hs; subst.
  pick_fresh Y.
  apply valid_scheme_c with (L := \{X} \u L \u \{Y}).
  introv Hf.
  fresh_length Hf as Hl.
  autorewrite with rew_sch_arity in Hf.
  assert (valid_scheme_vars E (sch_bind K M) (Y :: Xs)) as Hs by auto.
  inversion Hs; subst.
  assert (valid_env (E & Y ~:: K & X ~:: K)).
  { apply valid_env_kind.

  assert (Y \notin 
  destruct Xs; simpl in Hl; inversion Hl.
  inversion Hs; subst.

  pick_fresh Y.
  unfold sch_open_var.
  rewrite sch_subst_intro with (X := Y); auto.
  apply valid_scheme_typ_subst; auto.
  exists (L \u \{Y}).
  introv Hf.
  specialize (Hs (Y :: Xs)).
  simpl in Hs.
  autorewrite with rew_sch_arity in Hf.
  assert (scheme_vars (sch_bind K M) (Y :: Xs)) as Hsb by auto.
  inversion Hsb; subst; auto.
Qed.  

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
        - }
Qed.


(* *************************************************************** *)
(** A version of the symmetry lemma for type equality that does
    not require separate evidence that the types involved are
    well-kinded. *)

Lemma type_equal_symmetric : forall E T1 T2 K,
    type_equal E T1 T2 K ->
    type_equal E T2 T1 K.
Proof.
Qed.

(* *************************************************************** *)
(** Versions of the partial order lemmas for subtyping that do not
    require separate evidence that the types involved are
    well-kinded. *)

Lemma subtype_reflexive : forall E T cs,
    kinding E T (knd_row cs) ->
    subtype E T T cs.
Proof.
Qed.
     
Lemma subtype_transitive : forall E T1 T2 T3 cs,
    subtype E T1 T2 cs ->
    subtype E T2 T3 cs ->
    subtype E T1 T3 cs.
Proof.
Qed.

Lemma subtype_antisymmetric : forall E T1 T2 cs,
    subtype E T1 T2 cs ->
    subtype E T2 T1 cs ->
    type_equal E T1 T2 (knd_row cs).
Proof.
Qed.
