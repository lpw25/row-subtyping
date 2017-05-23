
(************************************************
 *          Row Subtyping - Soundness           *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import LibLN Definitions Infrastructure Kinding.              

(* *************************************************************** *)
(** * Properties of typing *)

Lemma typing_scheme_no_params : forall E e T,
    typing E e T ->
    typing_scheme E e (Sch nil T).
Proof.
  introv Ht.
  unfold typing_scheme, sch_arity.
  simpl.
  exists_fresh Xs Hfr.
  apply fresh_length in Hfr.
  apply eq_sym in Hfr.
  rewrite List.length_zero_iff_nil in Hfr.
  subst.
  rewrite singles_nil.
  rewrite map_empty.
  rewrite concat_empty_r.
  unfold sch_open_vars, typ_open_vars.
  simpl.
  rewrite* <- typ_open_type.
Qed.

Lemma typing_kinding_env : forall E e T,
    typing E e T ->
    kinding_env E.
Proof.
  introv Ht.
  induction* Ht.
  - pick_fresh x.
    eapply kinding_env_shorten in H0; auto.
  - pick_freshes (sch_arity M) Xs.
    eapply kinding_env_shorten in H0; auto.
Qed.

Hint Resolve typing_kinding_env : kinding.

Lemma typing_kinding : forall E e T,
    typing E e T ->
    kinding E T knd_type.
Proof.
  introv Ht.
  induction Ht; eauto with kinding.
  - apply* kinding_arrow.
    pick_fresh x.
    eapply kinding_bind_typ_l in H0; auto.
  - inversion* IHHt1.
  - pick_fresh x.
    eapply kinding_bind_typ_l in H2; auto.
  - pick_fresh x.
    eapply kinding_bind_typ_l in H0; auto.
  - pick_fresh x.
    eapply kinding_bind_typ_l in H0; auto.
Qed.

Hint Resolve typing_kinding : kinding.

Lemma typing_scheme_kinding : forall E e M,
    typing_scheme E e M ->
    kinding_scheme E M.
Proof.
  introv [L Ht].
  exists_fresh Xs Hf.
  eapply typing_kinding in Ht; eauto.
Qed.  

Hint Resolve typing_scheme_kinding : kinding.

(* *************************************************************** *)
(** Weakening *)

Lemma fresh_dom_concat : forall (E : env) F n Xs,
    fresh (dom E \u dom F) n Xs ->
    fresh (dom (E & F)) n Xs.
Proof.
  intros.
  rewrite* dom_concat.
Qed.

Hint Resolve fresh_dom_concat : weaken.

Lemma typing_weakening : forall E F G e T,
   typing (E & G) e T -> 
   kinding_env (E & F & G) ->
   typing (E & F & G) e T.
Proof.
  introv Ht.
  gen_eq EG : (E & G).
  gen E F G.
  induction Ht; intros; subst; eauto with weaken.
  - apply_fresh typing_abs as y; auto with weaken.
    apply_ih_bind H0;
      eauto using kinding_scheme_no_params with weaken.
  - apply_fresh (@typing_let M) as Ys.
    + apply_ih_bind H0; eauto with weaken.
    + apply_ih_bind H2; auto.
      apply kinding_env_typ; auto.
      eapply typing_scheme_kinding.
      exists_fresh Xs Hf.
      apply_ih_bind H0; eauto with weaken.
  - let G := gather_vars in
    eapply typing_match with (L := G) (T10 := T10);
      eauto with weaken; introv Hf.
    + apply_ih_bind H0; auto.
      apply kinding_env_typ; auto.
      apply kinding_scheme_no_params with (typ_variant T3 T4);
        auto with weaken kinding.
    + apply_ih_bind H2; auto.
      apply kinding_env_typ; auto.
      apply kinding_scheme_no_params with (typ_variant T6 T7);
        auto with weaken kinding.
  - let G := gather_vars in
    eapply typing_destruct with (L := G) (T3 := T3);
      eauto with weaken; introv Hf.
    apply_ih_bind H0; auto.
    apply kinding_env_typ; auto.
    apply kinding_scheme_no_params with T3; auto with weaken.
  - eapply typing_absurd; auto with weaken.
Qed.

Lemma typing_scheme_weakening : forall E F G e M,
   typing_scheme (E & G) e M -> 
   kinding_env (E & F & G) ->
   typing_scheme (E & F & G) e M.
Proof.
  unfold typing_scheme.
  introv [L Hs] Hk.
  exists (L \u dom (E & F & G)).
  introv Hf.
  rewrite <- concat_assoc.
  apply typing_weakening.
  - rewrite concat_assoc.
    apply* Hs.
  - rewrite concat_assoc.
    apply kinding_env_kinds with (sch_arity M); auto.
Qed.

Lemma typing_scheme_weakening_l : forall E F e M,
   typing_scheme E e M -> 
   kinding_env (E & F) ->
   typing_scheme (E & F) e M.
Proof.
  introv Hs Hk.
  rewrite <- concat_empty_r with (E := E) in Hs.
  rewrite <- concat_empty_r in Hk.
  rewrite <- concat_empty_r with (E := F).
  rewrite concat_assoc.
  apply* typing_scheme_weakening.
Qed.

Hint Resolve typing_weakening : weaken.
Hint Resolve typing_scheme_weakening : weaken.
Hint Resolve typing_scheme_weakening_l : weaken.

(* *************************************************************** *)
(** Preserved by type substitution *)

Lemma typing_typ_subst : forall E F X K U t T,
  E & X ~:: K & F |= t -: T ->
  kinding E U K ->
  E & (environment_subst X U F) |= t -: (typ_subst X U T).
Proof.
  introv Ht Hk.
  gen_eq G : (E & X ~:: K & F).
  gen E F.
  induction Ht; intros; subst; simpl; eauto.
  - rewrite* sch_subst_open.
    apply typing_var;
      eauto using kinding_env_well_scoped with typ_subst.
  - apply_fresh typing_abs as Y; eauto with typ_subst.
    rewrite <- sch_subst_no_params.
    remember (Sch nil T1) as M.
    fold (binding_subst X U (bind_typ M)).
    rewrite <- concat_assoc.
    rewrite <- environment_subst_push.
    apply H0; auto.
    rewrite* concat_assoc.
  - apply_fresh (@typing_let (sch_subst X U M)) as Y.
    + rewrite <- concat_assoc.
      rewrite <- environment_subst_kinds; auto.
      rewrite <- sch_subst_open_vars; eauto.
      apply H0; eauto.
      rewrite concat_assoc.
      auto.
    + rewrite <- concat_assoc.
      fold (binding_subst X U (bind_typ M)).
      rewrite <- environment_subst_push; auto.
      apply H2; auto.
      rewrite concat_assoc.
      auto.
  - apply typing_constructor with (typ_subst X U T1);
      eauto with typ_subst.
    rewrite <- typ_subst_constructor.
    rewrite <- typ_subst_bot with (X := X) (U := U).
    rewrite <- typ_subst_or.
    apply subtype_typ_subst with K; auto.
  - let G := gather_vars in
    apply typing_match with (L := G)
      (T1 := typ_subst X U T1)
      (T2 := typ_subst X U T2)
      (T3 := typ_subst X U T3)
      (T4 := typ_subst X U T4)
      (T5 := typ_subst X U T5)
      (T6 := typ_subst X U T6)
      (T7 := typ_subst X U T7)
      (T8 := typ_subst X U T8)
      (T9 := typ_subst X U T9)
      (T10 := typ_subst X U T10);
      try rewrite <- typ_subst_bot with (X := X) (U := U);
      try rewrite <- typ_subst_or;
      eauto with typ_subst.
    + introv Hf.
      rewrite <- typ_subst_variant.
      rewrite <- sch_subst_no_params.
      remember (Sch nil (typ_variant T3 T4)) as M.
      fold (binding_subst X U (bind_typ M)).
      rewrite <- concat_assoc.
      rewrite <- environment_subst_push.
      apply H0; auto.
      rewrite* concat_assoc.
    + introv Hf.
      rewrite <- typ_subst_variant.
      rewrite <- sch_subst_no_params.
      remember (Sch nil (typ_variant T6 T7)) as M.
      fold (binding_subst X U (bind_typ M)).
      rewrite <- concat_assoc.
      rewrite <- environment_subst_push.
      apply H2; auto.
      rewrite* concat_assoc.
    + rewrite <- typ_subst_row.
      apply subtype_typ_subst with K; auto.
  - let G := gather_vars in
    apply typing_destruct with (L := G)
      (T1 := typ_subst X U T1)
      (T2 := typ_subst X U T2)
      (T3 := typ_subst X U T3);
      try rewrite <- typ_subst_bot with (X := X) (U := U);
      try rewrite <- typ_subst_row;
      eauto with typ_subst.
    introv Hf.
    rewrite <- sch_subst_no_params.
    remember (Sch nil T3) as M.
    fold (binding_subst X U (bind_typ M)).
    rewrite <- concat_assoc.
    rewrite <- environment_subst_push.
    apply H0; auto.
    rewrite concat_assoc.
    easy.
  - apply typing_absurd with
      (T1 := typ_subst X U T1)
      (T2 := typ_subst X U T2); eauto with typ_subst.
    rewrite <- typ_subst_bot with (X := X) (U := U).
    apply subtype_typ_subst with K; auto.
Qed.

Lemma typing_typ_substs : forall E F Xs Ks Us t T,
  E & Xs ~::* Ks & F |= t -: T ->
  kindings E (length Xs) Us Ks ->
  E & (environment_substs Xs Us F) |= t -: (typ_substs Xs Us T).
Proof.
  introv Ht Hk.
  destruct (kindings_length Hk) as [Hlu Hlk].
  gen Ks Us T F.
  induction Xs; introv Hlk Hk Hlu Ht;
    destruct Ks; destruct Us; simpl; tryfalse.
  - rewrite singles_nil in Ht.
    rewrite map_empty in Ht.
    rewrite concat_empty_r in Ht.
    auto.
  - inversion Hk; subst; tryfalse.
    apply IHXs with Ks; auto.
    apply typing_typ_subst with k.
    + rewrite <- concat_assoc with (F := Xs ~::* Ks).
      rewrite <- map_push.
      rewrite <- singles_cons.
      auto.
    + apply kinding_weakening_l; auto.
      assert (kinding_env (E & (a :: Xs) ~::* (k :: Ks) & F))
        as Hke by eauto with kinding.
      rewrite singles_cons in Hke.
      rewrite map_push in Hke.
      rewrite concat_assoc in Hke.
      apply kinding_env_shorten in Hke.
      apply kinding_env_shorten in Hke.
      auto.
Qed.

(* *************************************************************** *)
(** Preserved by term substitution *)

Lemma typing_trm_subst : forall E F x M s t T,
  E & x ~: M & F |= t -: T ->
  typing_scheme E s M ->
  E & F |= (trm_subst x s t) -: T.
Proof.
  introv Ht Hs.
  gen_eq G : (E & x ~: M & F).
  gen E F.
  induction Ht; intros; subst; simpl; eauto with bind_typ.
  - case_var.
    + destruct (kindings_length H1) as [Hlu _].
      apply binds_middle_eq_inv in H0; auto.
      inversion H0.
      subst.
      destruct Hs as [L Hm].
      pick_freshes (sch_arity M) Xs.
      lets Hlx : (fresh_length _ _ _ Fr).
      rewrite typ_substs_intro_sch with (Xs := Xs); iauto.
      rewrite <- concat_empty_r with (E := E0 & F).
      rewrite Hlx in Hlu.
      rewrite <- environment_substs_empty
        with (Xs := Xs) (Ts := Us); auto.
      apply kindings_bind_typ in H1.
      rewrite Hlx in H1.
      apply typing_typ_substs with (sch_kinds M); auto.
      rewrite concat_empty_r.
      eauto 6 with weaken bind_typ.
    + apply typing_var; eauto with bind_typ.
      apply binds_subst with (x2 := x) (v2 := bind_typ M); auto.
  - apply_fresh typing_abs as Y; eauto with bind_typ.
    rewrite* trm_subst_open_var.
    apply_ih_bind* H0.
  - apply_fresh (@typing_let M0) as Y.
    + apply_ih_bind* H0.
    + rewrite* trm_subst_open_var.
      apply_ih_bind* H2.
  - let G := gather_vars in
    apply typing_match with (L := G)
      (T1 := T1) (T2 := T2) (T3 := T3) (T4 := T4)
      (T5 := T5) (T6 := T6) (T7 := T7) (T8 := T8)
      (T9 := T9) (T10 := T10); eauto with bind_typ.
    + introv Hf.
      rewrite* trm_subst_open_var.
      apply_ih_bind* H0.
    + introv Hf.
      rewrite* trm_subst_open_var.
      apply_ih_bind* H2.
  - let G := gather_vars in
    apply typing_destruct with (L := G)
      (T1 := T1) (T2 := T2) (T3 := T3);
      eauto with bind_typ.
    introv Hf.
    rewrite trm_subst_open_var; auto.
    apply_ih_bind* H0.
  - apply typing_absurd with (T1 := T1) (T2 := T2);
      eauto with bind_typ.
Qed.

Lemma typing_trm_subst_l : forall E x M s t T,
  E & x ~: M |= t -: T ->
  typing_scheme E s M ->
  E |= (trm_subst x s t) -: T.
Proof.
  introv Ht Hs.
  rewrite <- concat_empty_r with (E := E & x ~: M) in Ht.
  rewrite <- concat_empty_r with (E := E).
  apply typing_trm_subst with M; auto.
Qed.  

(* *************************************************************** *)
(** * Soundness *)

(* *************************************************************** *)
(** Preservation by term substitution *)

Lemma preservation : preservation.
Proof.
  unfold preservation.
  introv Ht Hr.
  gen E T.
  induction Hr; introv Ht; inversion Ht; subst; eauto.
  - pick_fresh x.
    rewrite trm_subst_intro with (x := x); auto.
    apply typing_trm_subst_l with M; auto.
    unfold typing_scheme. 
    eauto.
  - inversion H4.
    subst.
    pick_fresh x.
    rewrite trm_subst_intro with (x := x); auto.
    apply typing_trm_subst_l with (Sch nil S); auto.
    auto using typing_scheme_no_params.
  - inversion H7.
    subst.
    pick_fresh x.
    rewrite trm_subst_intro with (x := x); auto.
    apply typing_trm_subst_l with (Sch nil (typ_variant T3 T4)); auto.
    apply typing_scheme_no_params.
    apply typing_constructor with T0; auto.
    apply subtype_trans with T2; auto.
    apply subtype_trans with T1; auto.
    apply subtype_trans with (typ_or T8 T9); auto.
    apply subtype_trans with
      (typ_or T8 (typ_bot (cons_cofinite (from_list cs)))); auto.
    apply subtype_or_project_l.
    + assert (kinding E
             (typ_or T8 (typ_bot (cons_cofinite (from_list cs))))
             (knd_row cons_universe)) as Hk
        by auto with kinding.
      rewrite <- cons_diff_universe_cofinite.
      apply kinding_or_inv_l with
        (typ_bot (cons_cofinite (from_list cs))); auto.
    + assert (kinding E
             (typ_or (typ_bot (cons_finite (from_list cs))) T9)
             (knd_row cons_universe)) as Hk
        by auto with kinding.
      rewrite <- cons_diff_universe_finite.
      apply kinding_or_inv_r with
        (typ_bot (cons_finite (from_list cs))); auto.
  - inversion H7.
    subst.
    pick_fresh x.
    rewrite trm_subst_intro with (x := x); auto.
    apply typing_trm_subst_l with (Sch nil (typ_variant T6 T7)); auto.
    apply typing_scheme_no_params.
    apply typing_constructor with T0; auto.
    apply subtype_trans with T2; auto.
    apply subtype_trans with T1; auto.
    apply subtype_trans with (typ_or T8 T9); auto.
    apply subtype_trans with
      (typ_or (typ_bot (cons_finite (from_list cs))) T9); auto.
    apply subtype_or_project_r.
    + assert (kinding E
             (typ_or T8 (typ_bot (cons_cofinite (from_list cs))))
             (knd_row cons_universe)) as Hk
        by auto with kinding.
      rewrite <- cons_diff_universe_cofinite.
      apply kinding_or_inv_l with
        (typ_bot (cons_cofinite (from_list cs))); auto.
    + assert (kinding E
             (typ_or (typ_bot (cons_finite (from_list cs))) T9)
             (knd_row cons_universe)) as Hk
        by auto with kinding.
      rewrite <- cons_diff_universe_finite.
      apply kinding_or_inv_r with
        (typ_bot (cons_finite (from_list cs))); auto.
  - 