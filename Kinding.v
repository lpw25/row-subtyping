(************************************************
 *          Row Subtyping - Kinding             *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import LibLN Cofinite Definitions Substitution Wellformedness.

Hint Constructors
     kinding_core kinding
     type_equal_or type_equal_meet type_equal_join type_equal_core
     type_equal_cong type_equal_symm type_equal
     valid_kind valid_scheme_vars valid_instance valid_env.

(* *************************************************************** *)
(** Weakening *)

Lemma kinding_core_weakening : forall E F G T K,
   kinding_core (E & G) T K ->
   environment (E & F & G) ->
   kinding_core (E & F & G) T K.
Proof.
  introv Hk He.
  remember (E & G) as EG.
  induction Hk; subst; auto.
  - auto using binds_weakening.
  - eauto.
Qed.

Lemma kinding_type_equal_weakening :
  (forall EG T K,
      kinding EG T K ->
      (forall E F G,
          EG = E & G ->
          environment (E & F & G) ->
          kinding (E & F & G) T K))
  /\ (forall EG T1 T2 K,
      type_equal EG T1 T2 K ->
      (forall E F G,
          EG = E & G ->
          environment (E & F & G) ->
          type_equal (E & F & G) T1 T2 K)).
Proof.
  apply kinding_type_equal_mutind; intros; subst;
    eauto using kinding_core_weakening.
Qed.

Lemma kinding_weakening : forall E F G T K,
   kinding (E & G) T K -> 
   environment (E & F & G) ->
   kinding (E & F & G) T K.
Proof.
  destruct kinding_type_equal_weakening.
  eauto.
Qed.

Lemma type_equal_weakening : forall E F G T1 T2 K,
   type_equal (E & G) T1 T2 K -> 
   environment (E & F & G) ->
   type_equal (E & F & G) T1 T2 K.
Proof.
  destruct kinding_type_equal_weakening.
  eauto.
Qed.

Lemma subtype_weakening : forall E F G T1 T2,
    subtype (E & G) T1 T2 ->
    environment (E & F & G) ->
    subtype (E & F & G) T1 T2.
Proof.
  unfold subtype.
  intros.
  apply type_equal_weakening; assumption.
Qed.

Lemma valid_kind_weakening : forall E F G K,
    valid_kind (E & G) K ->
    environment (E & F & G) ->
    valid_kind (E & F & G) K.
Proof.
  introv Hv He.
  remember (E & G) as EG.
  induction Hv; subst; auto using subtype_weakening.
Qed.

Lemma valid_scheme_vars_weakening : forall E F G M Xs,
    fresh (dom F) (sch_arity M) Xs ->
    valid_scheme_vars (E & G) M Xs ->
    environment (E & F & G) ->
    valid_scheme_vars (E & F & G) M Xs.
Proof.
  introv Hf Hk He.
  apply regular_valid_scheme_vars in Hk.
  remember (E & G) as EG.
  generalize dependent E.
  generalize dependent G.
  induction Hk; intros; subst.
  - auto using kinding_weakening.
  - destruct Hf.
    apply valid_scheme_vars_bind; auto using valid_kind_weakening.
    rewrite <- concat_assoc.
    apply IHHk;
      autorewrite with rew_sch_arity; rewrite? concat_assoc; auto.
    apply environment_knd_weakening; assumption.
Qed.
    
Lemma valid_scheme_weakening : forall E F G M,
    valid_scheme (E & G) M ->
    environment (E & F & G) ->
    valid_scheme (E & F & G) M.
Proof.
  introv [L Hk] He.
  exists (L \u dom F); introv Hf.
  apply valid_scheme_vars_weakening; auto.
Qed.  

Lemma valid_instance_weakening : forall E F G Ts M,
  valid_instance (E & G) Ts M ->
  environment (E & F & G) ->
  valid_instance (E & F & G) Ts M.
Proof.
  introv Hk He.
  remember (E & G) as EG.
  induction Hk; subst.
  - apply valid_instance_empty.
  - auto using kinding_weakening.
Qed.

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

Lemma valid_env_kind_inv : forall E X K,
    valid_env (E & X ~:: K) ->
    valid_kind E K /\ X # E.
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
    valid_scheme E M /\ x # E.
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

Lemma valid_env_kind_weakening : forall E F G X K,
    X # F ->
    valid_env (E & G & X ~:: K) ->
    valid_env (E & F & G) ->
    valid_env (E & F & G & X ~:: K).
Proof.
  introv Hin He1 He2.
  assert (environment (E & F & G))
    by auto with valid_env_regular.
  destruct (valid_env_kind_inv He1).
  auto using valid_kind_weakening.
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
  destruct (valid_env_type_inv He1).
  auto using valid_scheme_weakening.
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

Lemma subtype_reflexive : forall E T,
    kinding E T (knd_row CSet.universe) ->
    subtype E T T.
Proof.
  introv Hk.
  unfold subtype.
  apply type_equal_step
    with (T2 := (typ_meet T (typ_join T (typ_bot CSet.universe))));
    auto.
  apply type_equal_step with (T2 := (typ_meet T T));
    inversion Hk; subst; auto with kinding_regular.
Qed.

Lemma valid_kind_kinding_core : forall E T K,
    valid_env E ->
    kinding_core E T K ->
    valid_kind E K.
Proof.
  introv Hv Hk.
  apply regular_kinding_core in Hk.
  induction Hk; auto.
  - eauto using valid_kind_from_env.
  - auto using subtype_reflexive.
Qed.
      
Lemma kinding_of_kinding_core : forall E T K,
    valid_env E ->
    kinding_core E T K ->
    kinding E T K.
Proof.
  introv Hv Hkc.
  destruct K; auto.
  eapply kinding_range.
  - apply Hkc.
  - apply subtype_reflexive.
    assert (valid_kind E (knd_range t t0)) as Hvk
      by eauto using valid_kind_kinding_core.
    inversion Hvk; subst.

(* *************************************************************** *)
(** Preserved by type substitution *)

Lemma kinding_core_typ_subst : forall E X T S K J,
  kinding_core (E & X ~:: J) T K -> 
  kinding E S J -> 
  kinding E (typ_subst X S T) K.
Proof.
  introv Hkc Hk.
  apply regular_kinding_core in Hkc.
  remember (E & X ~:: J) as F.
  induction Hkc; subst; simpl.
  - case_var.
    + assert (binds X (bind_knd K) (E & X ~:: J)) as Hb
        by assumption.
      apply binds_push_eq_inv in Hb.
      inversion Hb; subst.
      assumption.
    + assert (binds X0 (bind_knd K) (E & X ~:: J)) as Hb
        by assumption.
      apply binds_push_neq_inv in Hb; try assumption.
      assert (kinding_core E (typ_fvar X0) K)
        by eauto using environment_retract.
      

(* *************************************************************** *)
(** Not affected by type bindings *)

Lemma kinding_bind_typ : forall E F T K x S,
    kinding (E & x ~: S & F) T K ->
    kinding (E & F) T K.
Proof.
  introv Hk.
  gen_eq Ex : (E & x ~: S & F).
  induction Hk; intro; subst; eauto.
  destruct (binds_middle_inv H0) as [|[[_[_ Heq]]|]]; iauto.
  inversion Heq.
Qed.

Lemma kinding_bind_typ_l : forall E T K x S,
    kinding (E & x ~: S) T K ->
    kinding E T K.
Proof.
  introv Hk.
  rewrite <- concat_empty_r with (E := E).
  apply kinding_bind_typ with (x := x) (S := S).
  rewrite concat_empty_r.
  auto.
Qed.

Lemma kindings_bind_typ : forall E F n T K x S,
    kindings (E & x ~: S & F) n T K ->
    kindings (E & F) n T K.
Proof.
  introv Hk.
  gen_eq G : (E & x ~: S & F).
  induction Hk; intros; subst.
  - apply* kindings_nil.
  - apply* kindings_cons.
    apply kinding_bind_typ with (x := x) (S := S).
    auto.
Qed.

Lemma kinding_scheme_bind_typ : forall E F M x S,
    kinding_scheme (E & x ~: S & F) M ->
    kinding_scheme (E & F) M.
Proof.
  unfold kinding_scheme, kinding_body.
  introv [L Hk].
  exists_fresh Xs HFr.
  destruct Hk with Xs as [Hkd Hks]; auto.
  split; auto.
  rewrite <- concat_assoc.
  apply kinding_bind_typ with (x := x) (S := S).
  rewrite concat_assoc.
  auto.
Qed.

Hint Resolve kinding_bind_typ : bind_typ.
Hint Resolve kinding_bind_typ_l : bind_typ.
Hint Resolve kindings_bind_typ : bind_typ.
Hint Resolve kinding_scheme_bind_typ : bind_typ.

(* *************************************************************** *)
(** Preserved by type substitution *)

Lemma kinding_typ_subst : forall E F X T S K J,
  kinding (E & X ~:: J & F) T K -> 
  kinding E S J -> 
  kinding (E & (environment_subst X S F)) (typ_subst X S T) K.
Proof.
  introv Hkt Hks.
  gen_eq G : (E & X ~:: J & F).
  induction Hkt; introv Heq; subst; simpl typ_subst; eauto.
  - case_var.
    + lets Hb : (binds_middle_eq_inv H0 (ok_from_environment H)).
      inversion Hb; subst.
      apply* kinding_weakening_l.
    + { apply* kinding_var.
        - apply binds_subst_inv_r.
          eapply binds_subst.
          + apply H0.
          + auto. }
Qed.

Lemma kinding_typ_subst_l : forall E X T S K J,
  kinding (E & X ~:: J) T K -> 
  kinding E S J -> 
  kinding E (typ_subst X S T) K.
Proof.
  introv Hk1 Hk2.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- environment_subst_empty with (X := X) (T := S).
  apply kinding_typ_subst with (J := J); auto.
  rewrite concat_empty_r.
  auto.
Qed.

Lemma kinding_typ_substs : forall E F Xs T Ss K Js n,
  kinding (E & Xs ~::* Js & F) T K -> 
  kindings E n Ss Js -> 
  length Xs = n ->
  length Js = n ->
  length Ss = n ->
  kinding (E & (environment_substs Xs Ss F)) (typ_substs Xs Ss T) K.
Proof.
  intros.
  gen Ss Js T F n.
  induction Xs; destruct Js; destruct Ss;
    introv Hkt Hks; intros; subst; tryfalse; rew_kinds* in Hkt.
  inversion Hks.
  eapply IHXs; eauto.
  eapply kinding_typ_subst.
  - apply Hkt.
  - apply* kinding_weakening_l.
    eauto using environment_concat_inv_l.
Qed.

Lemma kinding_typ_substs_l : forall E Xs T Ss K Js n,
  kinding (E & Xs ~::* Js) T K -> 
  kindings E n Ss Js -> 
  length Xs = n ->
  length Js = n ->
  length Ss = n ->
  kinding E (typ_substs Xs Ss T) K.
Proof.
  introv Hk1 Hk2 Hlx Hlj Hls.
  rewrite <- concat_empty_r with (E := E).
  rewrite <- environment_substs_empty with (Xs := Xs) (Ts := Ss).
  - apply kinding_typ_substs with (Js := Js) (n := n); auto.
    rewrite concat_empty_r.
    auto.
  - subst*.
Qed.

Lemma kindings_typ_subst : forall n E F X Ts S Ks J,
  kindings (E & X ~:: J & F) n Ts Ks -> 
  kinding E S J -> 
  kindings (E & (environment_subst X S F)) n
           (List.map (typ_subst X S) Ts) Ks.
Proof.
  introv Hks Hk.
  gen_eq G : (E & X ~:: J & F).
  induction Hks; intro; subst; simpl.
  - apply kindings_nil.
    destruct* (environment_kind_middle_inv H).
  - apply kindings_cons; auto.
    apply kinding_typ_subst with J; auto.
Qed.

Lemma kinding_scheme_typ_subst : forall E F M X T K,
    kinding_scheme (E & X ~:: K & F) M ->
    kinding E T K ->
    kinding_scheme (E & environment_subst X T F) (sch_subst X T M).
Proof.
  unfold kinding_scheme, kinding_body.
  introv [L Hs] Ht.
  exists_fresh Xs Hf.
  unfold sch_arity in Hf.
  lets Hlx : (fresh_length _ _ _ Hf).
  lets Hf2 : Hf.
  rewrite Hlx in Hf2.
  apply fresh_length_arity_subst in Hf.
  destruct Hs with Xs as [Hkd Hks]; auto.
  split; auto.
  rewrite <- concat_assoc.
  rewrite* <- environment_subst_kinds.
  fold (sch_open_vars (sch_subst X T M) Xs).
  rewrite* <- sch_subst_open_vars.
  unfold sch_open_vars.
  apply kinding_typ_subst with (J := K); auto.
  rewrite concat_assoc.
  unfold sch_subst.
  simpl.
  apply Hs.
  unfold sch_arity.
  unfold sch_subst in Hf.
  simpl in Hf.
  auto.
Qed.

Hint Resolve kinding_typ_subst : typ_subst.
Hint Resolve kinding_typ_subst_l : typ_subst.
Hint Resolve kinding_typ_substs : typ_subst.
Hint Resolve kinding_typ_substs_l : typ_subst.
Hint Resolve kindings_typ_subst : typ_subst.

Lemma kinding_sch_open : forall E M Ts,
  kinding_scheme E M ->
  kindings E (sch_arity M) Ts (sch_kinds M) ->
  kinding E (sch_open M Ts) knd_type.
Proof.
  introv Hks Hkt.
  destruct Hks as [L Hks].
  pick_freshes (sch_arity M) Xs.
  destruct Hks with Xs as [Hkd Hkk]; auto.
  lets Hlx : (fresh_length _ _ _ Fr).
  lets Hlk : (proj1 (proj32 (kindings_regular Hkt))).
  rewrite* (@typ_substs_intro_sch M Xs Ts).
  unfold sch_open_vars.
  apply kinding_typ_substs_l
    with (Js := sch_kinds M) (n := sch_arity M); auto.
Qed.

Hint Resolve kinding_sch_open : kinding.
 
(* *************************************************************** *)
(** Kinding of schemes with no parameters *)

Lemma kinding_scheme_no_params : forall E T M,
    kinding E T knd_type ->
    M = Sch nil T ->
    kinding_scheme E M.
Proof.
  introv Hk Heq.
  subst.
  exists_fresh Xs Hf.
  simpl.
  destruct (List.length_zero_iff_nil Xs) as [Hlz _].
  rewrite (Hlz (eq_sym (fresh_length _ _ _ Hf))).
  rewrite singles_nil.
  rewrite map_empty.
  rewrite concat_empty_r.
  unfold typ_open_vars.
  rewrite* <- (@typ_open_type T (typ_fvars nil)).
Qed.

(* *************************************************************** *)
(** * Properties of well-kinded environments *)

Lemma kinding_env_shorten : forall E G,
    kinding_env (E & G) ->
    kinding_env E.
Proof.
  introv Hk.
  induction G using env_ind;
    autorewrite with rew_env_concat in Hk; auto.
  inversion Hk.
  - destruct (empty_concat_inv H0) as [ He1 _ ].
    destruct (empty_concat_inv He1) as [ He2 _ ].
    rewrite* <- He2.
  - destruct (eq_push_inv H) as [ _ [ _ He ] ].
    subst*.
  - destruct (eq_push_inv H) as [ _ [ _ He ] ].
    subst*.
Qed.

Lemma kinding_env_kinds : forall E n Ks Xs,
    kinding_env E ->
    (fresh (dom E) n Xs) ->
    kinds n Ks ->
    kinding_env (E & Xs ~::* Ks).
Proof.
  introv Hk Hf Hlk.
  lets Hlx : (eq_sym (fresh_length _ _ _ Hf)).
  gen Ks n.
  unfold kinds.
  induction Xs; destruct Ks;
    introv Hf [Hlk Hkd] Hlx; subst; tryfalse; rew_kinds*.
  apply kinding_env_kind.
  - apply IHXs with (length Ks); auto.
    destruct* Hf.
    inversion Hkd.
    split; auto.
  - inversion Hkd.
    auto.
  - eapply fresh_kinds; auto.
Qed.

Hint Resolve kinding_env_kinds : kinding.

Lemma kinding_env_typ_push_inv : forall E x M,
    kinding_env (E & x ~: M) ->
    kinding_env E /\ x # E /\ kinding_scheme E M.
Proof.
  introv H.
  inverts H as H1 H2 H3 H4.
  - false (empty_push_inv H1).
  - destruct (eq_push_inv H4) as [_ [Hv _]].
    false Hv.
  - destruct (eq_push_inv H4) as [Hx [Hv He]].
    inversion Hv.
    subst.
    easy.
Qed.

Lemma kinding_env_kind_push_inv : forall E x K,
    kinding_env (E & x ~:: K) ->
    kinding_env E /\ x # E.
Proof.
  introv H.
  inverts H as H1 H2 H3 H4.
  - false (empty_push_inv H1).
  - destruct (eq_push_inv H4) as [Hx [_ He]].
    subst.
    easy.
  - destruct (eq_push_inv H4) as [_ [Hv _]].
    false Hv.
Qed.

Lemma kinding_scheme_from_env : forall E x M,
    kinding_env E ->
    binds x (bind_typ M) E ->
    kinding_scheme E M.
Proof.
  introv He Hb.
  induction E using env_ind; rew_env_concat.
  - false (binds_empty_inv Hb).
  - destruct (binds_push_inv Hb); jauto_set.
    + subst.
      destruct (kinding_env_typ_push_inv He).
      jauto_set.
      auto with weaken.
    + eauto using kinding_env_shorten with weaken.
Qed.

Hint Resolve kinding_scheme_from_env : kinding.

Lemma kinding_env_well_scoped : forall E F X B,
    kinding_env (E & X ~ B & F) ->
    X \notin (env_fv E).
Proof.
  introv Hkef Hfv.
  assert (kinding_env E) as Hke by eauto using kinding_env_shorten. 
  lets Hd : (kinding_env_closed Hke Hfv).
  assert (ok (E & X ~ B & F)) as Hok by auto.
  apply ok_middle_inv in Hok.
  iauto.
Qed.

(* *************************************************************** *)
(** Not affected by type bindings *)

Lemma kinding_env_bind_typ : forall E F x M,
    kinding_env (E & x ~: M & F) ->
    kinding_env (E & F).
Proof.
  introv Hk.
  induction F using env_ind.
  - rewrite concat_empty_r.
    eauto using kinding_env_shorten.
  - rewrite concat_assoc in *.
    inversion Hk.
    + apply empty_push_inv in H0.
      tryfalse.
    + destruct (eq_push_inv H) as [Ha [Hb Hc]].
      subst.
      apply kinding_env_kind; auto.
    + destruct (eq_push_inv H) as [Ha [Hb Hc]].
      subst; eauto using kinding_scheme_bind_typ.
Qed.

Hint Resolve kinding_env_bind_typ : bind_typ.

(* *************************************************************** *)
(** Preserved by type substitution *)

Lemma kinding_env_typ_subst : forall E F X K T,
  kinding_env (E & X ~:: K & F) -> 
  kinding E T K -> 
  kinding_env (E & (environment_subst X T F)).
Proof.
  introv He Hk.
  induction F using env_ind.
  - rewrite environment_subst_empty.
    rewrite concat_empty_r.
    eauto using kinding_env_shorten.
  - rewrite environment_subst_push.
    rewrite concat_assoc.
    rewrite concat_assoc in He.
    destruct v; simpl binding_subst.
    + { destruct (kinding_env_kind_push_inv He).
        apply kinding_env_kind; auto.
        - lets Hee : (kinding_env_regular He).
          apply kind_from_env with
            (E := E & X ~:: K & F & x ~:: k)
            (x := x); auto.
        - rewrite dom_concat.
          rewrite dom_environment_subst.
          auto. }
    + { destruct (kinding_env_typ_push_inv He) as [H1 [H2 H3]].
        apply kinding_env_typ; auto.
        - apply kinding_scheme_typ_subst with K; auto.
        - rewrite dom_concat.
          rewrite* dom_environment_subst. }
Qed.

Hint Resolve kinding_env_typ_subst: typ_subst.

Lemma kinding_closed : forall E T K X,
    kinding E T K ->
    X \in typ_fv T ->
    X \in dom E.
Proof.
  introv Hk Hfv.
  induction Hk; simpl in Hfv; rew_in in Hfv; iauto.
  subst.
  eapply get_some_inv.
  apply H0.
Qed.

Lemma kinding_scheme_closed : forall E M X,
    kinding_scheme E M ->
    X \in sch_fv M ->
    X \in dom E.
Proof.
  introv Hks Hfv.
  unfold kinding_scheme, kinding_body in Hks.
  unfold sch_fv in Hfv.
  destruct Hks as [L Hk].
  pick_freshes (sch_arity M) Xs.
  destruct Hk with Xs as [_ Hkk]; auto.
  eapply kinding_closed with (X := X) in Hkk; auto.
  - rewrite dom_concat in Hkk.
    rew_in in Hkk.
    destruct* Hkk.
    rewrite dom_map in H.
    rewrite dom_singles in H.
    + assert (fresh \{X} (sch_arity M) Xs) by auto.
      eapply fresh_single_notin in H; auto.
      tryfalse.
    + apply fresh_length in Fr.
      unfold sch_arity in Fr.
      rewrite! liblist_length_eq_length.
      auto.
  - apply* typ_fv_open_vars.
Qed.

Lemma kinding_env_closed : forall E X,
    kinding_env E ->
    X \in env_fv E ->
    X \in dom E.
Proof.
  introv Hk Hfv.
  induction Hk.
  - rewrite env_fv_empty in Hfv.
    rew_in in Hfv.
    iauto.
  - rewrite env_fv_push_inv in Hfv.
    rewrite dom_push.
    rew_in.
    right.
    rew_in in Hfv.
    destruct* Hfv.
  - rewrite env_fv_push_inv in Hfv.
    rewrite dom_push.
    rew_in.
    right.
    rew_in in Hfv.
    destruct* Hfv.
    simpl in H1.
    apply kinding_scheme_closed with M; auto.
Qed.
