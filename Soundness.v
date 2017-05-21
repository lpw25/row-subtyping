(************************************************
 *          Row Subtyping - Soundness           *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import LibLN Definitions Infrastructure.

(* *************************************************************** *)
(** * Properties of kinding *)

(* *************************************************************** *)
(** Inverses *)

Lemma kinding_constructor_inv : forall E c T K,
    kinding E (typ_constructor c T) K ->
    kinding E T knd_type /\
    K = (knd_row (cons_finite \{c})).
Proof.
  introv Hk.
  inversion Hk; subst.
  auto.
Qed.

Lemma kinding_or_inv : forall E T1 T2 K,
    kinding E (typ_or T1 T2) K ->
    exists cs1 cs2,
    kinding E T1 (knd_row cs1) /\
    kinding E T2 (knd_row cs2) /\
    K = (knd_row (cons_union cs1 cs2)).
Proof.
  introv Hk.
  inversion Hk; subst.
  exists cs1 cs2.
  auto.
Qed.

Lemma kinding_variant_inv : forall E T1 T2 K,
    kinding E (typ_variant T1 T2) K ->
    kinding E T1 (knd_row cons_universe) /\
    kinding E T2 (knd_row cons_universe) /\
    K = knd_type.
Proof.
  introv Hk.
  inversion Hk; subst.
  auto.
Qed.

Lemma kinding_arrow_inv : forall E T1 T2 K,
    kinding E (typ_arrow T1 T2) K ->
    kinding E T1 knd_type /\
    kinding E T2 knd_type /\
    K = knd_type.
Proof.
  introv Hk.
  inversion Hk; subst.
  auto.
Qed.

Lemma kinding_meet_inv : forall E T1 T2 K,
    kinding E (typ_meet T1 T2) K ->
    exists cs,
    kinding E T1 (knd_row cs) /\
    kinding E T2 (knd_row cs) /\
    K = knd_row cs.
Proof.
  introv Hk.
  inversion Hk; subst.
  exists cs.
  auto.
Qed.

Lemma kinding_join_inv : forall E T1 T2 K,
    kinding E (typ_join T1 T2) K ->
    exists cs,
    kinding E T1 (knd_row cs) /\
    kinding E T2 (knd_row cs) /\
    K = knd_row cs.
Proof.
  introv Hk.
  inversion Hk; subst.
  exists cs.
  auto.
Qed.

Hint Resolve kinding_constructor_inv kinding_or_inv
     kinding_variant_inv kinding_arrow_inv
     kinding_meet_inv kinding_join_inv: kinding.

(* *************************************************************** *)
(** Weakening *)

Hint Resolve binds_weaken : weaken.

Lemma kinding_weakening : forall E F G T K,
   kinding (E & G) T K -> 
   environment (E & F & G) ->
   kinding (E & F & G) T K.
Proof.
  introv Hk He.
  inductions Hk; eauto with weaken.
Qed.

Hint Resolve kinding_weakening : weaken.

Lemma kinding_weakening_l : forall E F T K,
    kinding E T K ->
    environment (E & F) ->
    kinding (E & F) T K.
Proof.
  introv Hk He.
  rewrite <- (concat_empty_r E) in Hk.
  rewrite <- (concat_empty_r F) in *.
  rewrite (concat_assoc E F empty) in *.
  apply* kinding_weakening.
Qed.

Hint Resolve kinding_weakening_l : weaken.

Lemma kinding_weakening_r : forall E F T K,
    kinding E T K ->
    environment (F & E) ->
    kinding (F & E) T K.
Proof.
  introv Hk He.
  rewrite <- (concat_empty_l E) in Hk.
  rewrite <- (concat_empty_l F) in *.
  apply* kinding_weakening.
Qed.

Hint Resolve kinding_weakening_r : weaken.

Lemma kindings_weakening : forall E F G n Ts Ks,
   kindings (E & G) n Ts Ks -> 
   environment (E & F & G) ->
   kindings (E & F & G) n Ts Ks.
Proof.
  introv Hk He.
  gen_eq EG : (E & G).
  induction Hk; intro; subst; auto.
  - apply kindings_nil; auto.
  - apply kindings_cons; auto with weaken.
Qed.

Hint Resolve kindings_weakening : weaken.

Lemma kinding_body_weakening : forall E F G n Ks T,
    kinding_body (E & G) n Ks T ->
    length Ks = n ->
    environment (E & F & G) ->
    kinding_body (E & F & G) n Ks T.
Proof.
  introv Hk He.
  destruct (kinding_body_regular Hk) as [_ [Hkd _]].
  unfold kinding_body in *.
  destruct Hk as [L Hk].
  exists_fresh Xs Hf.
  split; auto.
  apply_ih_bind kinding_weakening.
  - apply Hk; auto.
  - apply environment_kinds with n; auto.
    + rewrite! dom_concat.
      auto.
    + destruct Hkd; auto.
Qed.

Hint Resolve kinding_body_weakening : weaken.

Lemma kinding_scheme_weakening : forall E F G M,
    kinding_scheme (E & G) M ->
    environment (E & F & G) ->
    kinding_scheme (E & F & G) M.
Proof.
  unfold kinding_scheme.
  introv Hk He.
  apply* kinding_body_weakening.
Qed.

Hint Resolve kinding_scheme_weakening : weaken.

Lemma kinding_scheme_weakening_l : forall E F M,
    kinding_scheme E M ->
    environment (E & F) ->
    kinding_scheme (E & F) M.
Proof.
  introv Hk He.
  rewrite <- (concat_empty_r E) in Hk.
  rewrite <- (concat_empty_r F) in *.
  rewrite (concat_assoc E F empty) in *.
  apply* kinding_scheme_weakening.
Qed.  

Hint Resolve kinding_scheme_weakening_l : weaken.

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

Hint Resolve kinding_env_kinds.

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

(* *************************************************************** *)
(** Uniqueness *)

Lemma kinding_unique : forall E T K1 K2,
    kinding E T K1 ->
    kinding E T K2 ->
    K1 = K2.
Proof.
  introv Hk1 Hk2.
  gen K2.
  induction Hk1; introv Hk2; inversion Hk2; subst; auto.
  - lets Hke : (binds_func H0 H4).
    inversion Hke; auto.
  - lets Hke1 : (IHHk1_1 _ H3).
    lets Hke2 : (IHHk1_2 _ H4).
    inversion Hke1.
    inversion Hke2.
    reflexivity.
Qed.

(* *************************************************************** *)
(** Extract kinding from [typ_or] *)

Lemma kinding_or_inv_l : forall E T1 T2 cs1 cs2,
    kinding E (typ_or T1 T2) (knd_row cs1) ->
    kinding E T2 (knd_row cs2) ->
    kinding E T1 (knd_row (cons_diff cs1 cs2)).
Proof.
  introv Hk1 Hk2.
  inversion Hk1.
  assert (knd_row cs2 = knd_row cs3) as Heq
    by eauto using kinding_unique.
  inversion Heq.
  subst.
  rewrite cons_diff_union; auto.
Qed.  

Lemma kinding_or_inv_r : forall E T1 T2 cs1 cs2,
    kinding E (typ_or T1 T2) (knd_row cs1) ->
    kinding E T1 (knd_row cs2) ->
    kinding E T2 (knd_row (cons_diff cs1 cs2)).
Proof.
  introv Hk1 Hk2.
  inversion Hk1.
  assert (knd_row cs0 = knd_row cs2) as Heq
    by eauto using kinding_unique.
  inversion Heq.
  subst.
  rewrite cons_union_commutative.
  rewrite cons_diff_union; auto with constrs.
Qed.  

(* *************************************************************** *)
(** * Properties of type equality *)

(* *************************************************************** *)
(** Transitivity *)

Lemma type_equal_trans : forall E T1 T2 T3 K,
    type_equal E T1 T2 K ->
    type_equal E T2 T3 K ->
    type_equal E T1 T3 K.
Proof.
  introv He.
  induction He; eauto 0 3.
Qed.

(* *************************************************************** *)
(** Well-kindedness *)

Ltac invert_all_kinds2 Hs :=
  try match goal with
  | [ H : kinding _ (typ_constructor _ _) _ |- _ ] =>
    invert_all_kinds2_body Hs H
  | [ H : kinding _ (typ_or _ _) _ |- _ ] =>
    invert_all_kinds2_body Hs H
  | [ H : kinding _ (typ_variant _ _) _ |- _ ] =>
    invert_all_kinds2_body Hs H
  | [ H : kinding _ (typ_arrow _ _) _ |- _ ] =>
    invert_all_kinds2_body Hs H
  | [ H : kinding _ (typ_meet _ _) _ |- _ ] =>
    invert_all_kinds2_body Hs H
  | [ H : kinding _ (typ_join _ _) _ |- _ ] =>
    invert_all_kinds2_body Hs H
  | [ H : kinding _ (typ_top _) _ |- _ ] =>
    invert_all_kinds2_body Hs H
  | [ H : kinding _ (typ_bot _) _ |- _ ] =>
    invert_all_kinds2_body Hs H
  end

with invert_all_kinds2_body Hs H :=
  let b := inList H Hs in
  match b with
  | true => fail 1
  | false =>
    try invert_all_kinds2 (H, Hs);
    inversion H
  end.

(* TODO move this *)
Lemma kinding_unique_row : forall E T cs1 cs2,
    kinding E T (knd_row cs1) ->
    kinding E T (knd_row cs2) ->
    cs1 = cs2.
Proof.
  introv H1 H2.
  remember (kinding_unique H1 H2) as Heq.
  inversion Heq.
  easy.
Qed.

Lemma type_equal_kinding : forall E T1 T2 K,
    type_equal E T1 T2 K ->
    kinding E T1 K /\ kinding E T2 K.
Proof.
  introv He.
  induction He; split; intuition auto;
    invert_all_kinds2 tt;
    invert_all_kinds2 tt;
    subst;
    repeat match goal with
    | H1 : kinding ?E ?T ?K,
      H2 : kinding ?E ?T ?K |- _ =>
      clear H1
    | H1 : kinding ?E ?T (knd_row ?cs1),
      H2 : kinding ?E ?T (knd_row ?cs2) |- _ =>
      replace cs1 with cs2 in *
        by (apply (kinding_unique_row H2 H1))
    | H1 : kinding ?E ?T ?K1,
      H2 : kinding ?E ?T knd_type |- _ =>
      replace K1 with knd_type in *
        by apply (kinding_unique H2 H1)
    | H1 : kinding ?E ?T ?K1,
      H2 : kinding ?E ?T (knd_row ?cs) |- _ =>
      replace K1 with (knd_row cs) in *
        by apply (kinding_unique H2 H1)
    end;
    eauto.
  - eauto with constrs.
  - eauto with constrs.
  - eauto with constrs.
Qed.

Hint Extern 1 (kinding ?E ?T ?K) =>
  match goal with
  | H: type_equal E T _ K |- _ =>
      apply (proj1 (type_equal_kinding H))
  | H: type_equal E _ T K |- _ =>
      apply (proj2 (type_equal_kinding H))
  end : kinding.

(* *************************************************************** *)
(** Symmetry *)

Lemma type_equal_symm : forall E T1 T2 K,
    type_equal E T1 T2 K ->
    type_equal E T2 T1 K.
Proof.
  introv He.
  induction (He); auto;
    repeat match goal with
    | [ H1 : type_equal ?E ?T1 ?T2 ?K,
        H2 : type_equal ?E ?T1 ?T2 ?K -> type_equal _ _ _ _ |- _ ] =>
      specialize (H2 H1)
    end;
    destruct (type_equal_kinding He) as [Hr _];
    apply type_equal_refl in Hr;
    eapply type_equal_trans;
    eauto 0 2 with kinding.
  - destruct (type_equal_kinding t) as [Hk _].
    inversion Hk; subst.
    inversion H; subst. 
    inversion H5; subst.
    inversion H7; subst.
    eauto.
  - destruct (type_equal_kinding t) as [Hk _].
    inversion Hk; subst.
    inversion H; subst. 
    inversion H5; subst.
    inversion H7; subst.
    eauto.
  - destruct (type_equal_kinding t) as [Hk _].
    inversion Hk; subst.
    inversion H1; subst.
    inversion H2; subst.
    eauto.
  - destruct (type_equal_kinding t) as [Hk _].
    inversion Hk; subst.
    inversion H1; subst.
    inversion H2; subst.
    eauto.
  - destruct (type_equal_kinding t) as [Hk _].
    inversion Hk; subst.
    auto.
  - destruct (type_equal_kinding t) as [Hk _].
    inversion Hk; subst.
    inversion H4; subst.
    eauto.
  - destruct (type_equal_kinding t) as [Hk _].
    inversion Hk; subst.
    auto.
  - destruct (type_equal_kinding t) as [Hk _].
    inversion Hk; subst.
    inversion H4; subst.
    eauto.
Qed.

(* *************************************************************** *)
(** Idempotence of join and meet *)

Lemma type_equal_join_idempotent : forall E T cs,
    kinding E T (knd_row cs) ->
    type_equal E (typ_join T T) T (knd_row cs).
Proof.
  introv Hk.
  eapply type_equal_join
    with (T1' := T) (K1 := knd_row cs)
         (T2' := (typ_meet T (typ_top cs)));
    auto using type_equal_symm.
  eapply type_equal_join_absorption_l; auto.
Qed.    

Lemma type_equal_meet_idempotent : forall E T cs,
    kinding E T (knd_row cs) ->
    type_equal E (typ_meet T T) T (knd_row cs).
Proof.
  introv Hk.
  eapply type_equal_meet
    with (T1' := T) (K1 := knd_row cs)
         (T2' := (typ_join T (typ_bot cs)));
    auto using type_equal_symm.
  eapply type_equal_meet_absorption_l; auto.
Qed.

Hint Resolve type_equal_join_idempotent.
Hint Resolve type_equal_meet_idempotent.
    
(* *************************************************************** *)
(** Not affected by type bindings *)

Lemma type_equal_bind_typ : forall E F T1 T2 K x S,
    type_equal (E & x ~: S & F) T1 T2 K ->
    type_equal (E & F) T1 T2 K.
Proof.
  introv He.
  gen_eq G : (E & x ~: S & F).
  induction He; intros; subst;
    eauto 6 using type_equal_refl with bind_typ; auto with constrs.
Qed.  

(* *************************************************************** *)
(** Preserved by type substitution *)

Lemma type_equal_typ_subst : forall E F X T1 T2 S K J,
  type_equal (E & X ~:: J & F) T1 T2 K -> 
  kinding E S J -> 
  type_equal (E & (environment_subst X S F))
             (typ_subst X S T1) (typ_subst X S T2) K.
Proof.
  introv Hkt Hks.
  gen_eq G: (E & X ~:: J & F).
  inductions Hkt; introv Heq; subst;
    simpl typ_subst; eauto 6 using type_equal_refl with typ_subst; auto with constrs.
  - case_var.
    + apply type_equal_refl.
      lets Hb : (binds_middle_eq_inv H0 (ok_from_environment H)).
      inversion Hb; subst.
      apply* kinding_weakening_l.
    + { apply* type_equal_var.
        apply* binds_subst_inv_r.
        eapply binds_subst.
        - apply H0.
        - auto. }
Qed.

Hint Resolve type_equal_typ_subst : typ_subst.

(* *************************************************************** *)
(** Weakening *)

Lemma type_equal_weakening : forall E F G T1 T2 K,
   type_equal (E & G) T1 T2 K -> 
   environment (E & F & G) ->
   type_equal (E & F & G) T1 T2 K.
Proof.
  introv Heq Henv.
  inductions Heq; auto with weaken.
  - apply type_equal_trans with T2.
    + apply IHHeq1 with (E0 := E) (G0 := G); auto.
    + apply IHHeq2 with (E0 := E) (G0 := G); auto.
Qed.

Hint Resolve type_equal_weakening : weaken.

(* *************************************************************** *)
(** Kind can be replaced *)

Lemma type_equal_replace_kind : forall E T1 T2 K1 K2,
    kinding E T1 K1 ->
    type_equal E T1 T2 K2 ->
    type_equal E T1 T2 K1.
Proof.
  introv Hk He.
  assert (K1 = K2) as Heq
    by eauto using kinding_unique with kinding.
  rewrite Heq.
  assumption.
Qed.    

(* *************************************************************** *)
(** * Properties of Subtyping *)

(* *************************************************************** *)
(** Reflexivity *)

Lemma subtype_refl : forall E T,
  kinding E T (knd_row cons_universe) -> 
  subtype E T T.
Proof.
  introv Hk.
  inversion Hk; subst; unfold subtype; auto using type_equal_symm.
Qed.

(* *************************************************************** *)
(** Transitivity *)

Lemma subtype_trans : forall E T1 T2 T3,
    subtype E T1 T2 ->
    subtype E T2 T3 ->
    subtype E T1 T3.
Proof.
  introv H12 H23.
  unfold subtype in *.
  destruct (type_equal_kinding H23) as [ _ Hk ].
  inversion Hk; subst.
  apply type_equal_trans with (typ_meet T1 T2); auto.
  apply type_equal_trans with (typ_meet T1 (typ_meet T2 T3));
    auto using type_equal_refl with kinding.
  apply type_equal_trans with (typ_meet (typ_meet T1 T2) T3);
    auto with kinding.
  auto using type_equal_refl, type_equal_symm.
Qed.

(* *************************************************************** *)
(** Anti-symmetry *)

Lemma subtype_antisymm : forall E T1 T2,
    subtype E T1 T2 ->
    subtype E T2 T1 ->
    type_equal E T1 T2 (knd_row cons_universe).
Proof.
  introv H12 H21.
  unfold subtype in *.
  apply type_equal_trans with (typ_meet T1 T2); auto.
  apply type_equal_trans with (typ_meet T2 T1);
    auto using type_equal_symm.
  auto with kinding.
Qed.

(* *************************************************************** *)
(* Well-kindedness *)

Lemma subtype_kinding : forall E T1 T2,
    subtype E T1 T2 ->
    kinding E T1 (knd_row cons_universe)
    /\ kinding E T2 (knd_row cons_universe).
Proof.
  introv He.
  destruct (type_equal_kinding He) as [ Hk Hj ].
  split*.
  inversion* Hj.
Qed.

Hint Extern 1 (kinding ?E ?T (knd_row cons_universe)) =>
  match goal with
  | H: subtype E T _ |- _ =>
      apply (proj1 (subtype_kinding H))
  | H: subtype E _ T |- _ =>
      apply (proj2 (subtype_kinding H))
  end : kinding.

(* *************************************************************** *)
(** Weakening *)

Lemma subtype_weakening : forall E F G T1 T2,
   subtype (E & G) T1 T2 -> 
   environment (E & F & G) ->
   subtype (E & F & G) T1 T2.
Proof.
  introv Hs He.
  apply* type_equal_weakening.
Qed.

Hint Resolve subtype_weakening : weaken.

(* *************************************************************** *)
(** Not affected by type bindings *)

Lemma subtype_bind_typ : forall E F T1 T2 x S,
    subtype (E & x ~: S & F) T1 T2 ->
    subtype (E & F) T1 T2.
Proof.
  unfold subtype.
  introv He.
  eapply type_equal_bind_typ.
  apply He.
Qed.  

Hint Resolve subtype_bind_typ : bind_typ.

(* *************************************************************** *)
(** Preserved by type substitution *)

Lemma subtype_typ_subst : forall E F X T1 T2 S J,
  subtype (E & X ~:: J & F) T1 T2 -> 
  kinding E S J -> 
  subtype (E & (environment_subst X S F))
          (typ_subst X S T1) (typ_subst X S T2).
Proof.
  unfold subtype.
  introv Hs Hk.
  lets H : (type_equal_typ_subst Hs Hk).
  simpl in H.
  auto.
Qed.

Hint Resolve subtype_typ_subst : typ_subst.

(* *************************************************************** *)
(* Let's try projection as a function *)
(*
Fixpoint projection (env : env) (cs : constructors) (t : typ)
  : option (option typ) :=
  match t with
  | typ_bvar _ => None
  | typ_fvar v =>
      match EnvOps.get v env with
      | None => None
      | Some (bind_typ _) => None
      | Some (bind_knd knd_type) => None
      | Some (bind_knd (knd_row cs')) =>
          match cons_subset cs' cs with
          | True => Some (Some t)
          | False =>
            let cs'' := cons_inter cs cs' in
            match cons_non_empty cs'' with
            | True => None
            | False => Some None
            end
          end
      end
  | typ_constructor c _ =>
      match mem c cs with
      | True => Some (Some t)
      | _ => Some None
      end
  | typ_or t1 t2 =>
      match projection t1, projection t2 with
      | Some (Some p1), Some (Some p2) => Some (Some (typ_or p1 p2))
      | Some (Some p), Some None => Some (Some p)
      | Some None, Some (Some p) => Some (Some p)
      | Some None, Some None => Some None
      | _, _ => None
      end
  | typ_variant _ _ => None
  | typ_arrow _ _ => None
  | typ_top cs' =>
      let cs'' := cons_inter cs cs' in
      match cons_non_empty cs'' with
      | True => Some (Some (typ_top cs''))
      | False => Some None
      end
  | typ_bot cs' =>
      let cs'' := cons_inter cs cs' in
      match cons_non_empty cs'' with
      | True => Some (Some (typ_bot cs''))
      | False => Some None
      end
  | typ_meet t1 t2 =>
      match projection t1, projection t2 with
      | Some (Some p1), Some (Some p2) => Some (Some (typ_meet p1 p2))
      | Some None, Some None => Some None
      | _, _ => None
      end
  | typ_join t1 t2 =>
      match projection t1, projection t2 with
      | Some (Some p1), Some (Some p2) => Some (Some (typ_join p1 p2))
      | Some None, Some None => Some None
      | _, _ => None
      end
  end.
*)

(* *************************************************************** *)
(** TODO: Describe and rename these lemmas *)

Inductive row_projection : env -> typ -> constructors ->
                           typ -> constructors -> Prop :=
  | row_projection_var : forall E cs X,
      environment E ->
      binds X (bind_knd (knd_row cs)) E ->
      row_projection E (typ_fvar X) cs (typ_fvar X) cs
  | row_projection_constructor : forall E c cs T,
      kinding E T knd_type ->
      cs = cons_finite \{c} ->
      row_projection E (typ_constructor c T) cs
                       (typ_constructor c T) cs
  | row_projection_or : forall E cs1 cs2 cs3 cs4 T1 T2 T,
      cons_disjoint cs3 cs4 ->
      cs2 = cons_union cs3 cs4 ->
      kinding E T1 (knd_row cs3) ->
      kinding E T2 (knd_row cs4) ->
      or_projection E T1 cs3 T2 cs4 T cs1 ->
      row_projection E (typ_or T1 T2) cs2 T cs1
  | row_projection_meet : forall E cs1 cs2 T1 T2 T3 T4,
      row_projection E T1 cs2 T3 cs1 ->
      row_projection E T2 cs2 T4 cs1 ->
      row_projection E (typ_meet T1 T2) cs2 (typ_meet T3 T4) cs1
  | row_projection_join : forall E cs1 cs2 T1 T2 T3 T4,
      row_projection E T1 cs2 T3 cs1 ->
      row_projection E T2 cs2 T4 cs1 ->
      row_projection E (typ_join T1 T2) cs2 (typ_join T3 T4) cs1
  | row_projection_bot : forall E cs1 cs2,
      environment E ->
      cons_non_empty cs1 ->
      cons_subset cs1 cs2 ->
      row_projection E (typ_bot cs2) cs2 (typ_bot cs1) cs1
  | row_projection_top : forall E cs1 cs2,
      environment E ->
      cons_non_empty cs1 ->
      cons_subset cs1 cs2 ->
      row_projection E (typ_top cs2) cs2 (typ_top cs1) cs1

with or_projection : env ->
                     typ -> constructors ->
                     typ -> constructors ->
                     typ -> constructors -> Prop :=
  | or_left : forall E T1 cs1 T2 cs2 T cs,
      cons_subset cs cs1 ->
      row_projection E T1 cs1 T cs ->
      or_projection E T1 cs1 T2 cs2 T cs
  | or_right : forall E T1 cs1 T2 cs2 T cs,
      cons_subset cs cs2 ->
      row_projection E T2 cs2 T cs ->
      or_projection E T1 cs1 T2 cs2 T cs
  | or_both : forall E T1 cs1 T2 cs2 T1' T2' cs,
      cons_non_empty (cons_inter cs cs1) ->
      cons_non_empty (cons_inter cs cs2) ->
      cs = (cons_union (cons_inter cs cs1) (cons_inter cs cs2)) ->
      row_projection E T1 cs1 T1' (cons_inter cs cs1) ->
      row_projection E T2 cs2 T2' (cons_inter cs cs2) ->
      or_projection E T1 cs1 T2 cs2 (typ_or T1' T2') cs.

Hint Constructors row_projection or_projection.

Scheme row_projection_mut := Induction for row_projection Sort Prop
  with or_projection_mut := Induction for or_projection Sort Prop.

Combined Scheme projection_mut from
         row_projection_mut, or_projection_mut.

Lemma row_projection_identity : forall E cs T,
    kinding E T (knd_row cs) ->
    row_projection E T cs T cs.
Proof.
  introv Hk.
  gen_eq K : (knd_row cs).
  gen cs.
  induction Hk; introv Hknd; inversion Hknd; subst; auto with constrs.
  - apply row_projection_or with (cs3 := cs1) (cs4 := cs2); auto.
    apply or_both;
      replace (cons_inter (cons_union cs1 cs2) cs1)
        with cs1
        by constrs;
      replace (cons_inter (cons_union cs1 cs2) cs2)
        with cs2
        by constrs;
      auto.
Qed.    

Lemma row_projection_kinding_mut :
    (forall E T cs T' cs',
    row_projection E T cs T' cs' ->
    kinding E T (knd_row cs) /\ kinding E T' (knd_row cs'))
/\ (forall E T1 cs1 T2 cs2 T' cs',
    or_projection E T1 cs1 T2 cs2 T' cs' ->
    cons_disjoint cs1 cs2 ->
    kinding E T1 (knd_row cs1) ->
    kinding E T2 (knd_row cs2) ->
    kinding E T' (knd_row cs')).
Proof.
  apply projection_mut; intros; substs; intuition auto with constrs.
  - rewrite e.
    auto with constrs.
Qed.

Definition row_projection_kinding :=
  proj1 row_projection_kinding_mut.

Hint Extern 1 (kinding ?E ?T (knd_row ?cs)) =>
  match goal with
  | H: row_projection E T (knd_row ?cs) _ _ |- _ =>
      apply (proj1 (row_projection_kinding H))
  | H: row_projection E _ _ cs T |- _ =>
      apply (proj2 (row_projection_kinding H))
  end : kinding.

Lemma row_projection_idem : forall E cs T T',
    row_projection E T (knd_row cs) cs T' ->
    T = T'.
Proof.
  introv Hpr.
  gen_eq K : (knd_row cs).
  induction Hpr; intro; auto.
  - assert (cons_non_empty cs3) by auto.
    apply row_projection_kinding in Hpr.
    assert (cons_non_empty cs2) by iauto.
    inversion H2; subst.
    false.
    constrs.
  - assert (cons_non_empty cs2) by auto.
    apply row_projection_kinding in Hpr.
    assert (cons_non_empty cs3) by iauto.
    inversion H2; subst.
    false.
    constrs.
  - inversion H3; subst.
    replace T1' with T1
      by auto with constrs.
    replace T2' with T2
      by auto with constrs.
    auto.
  - replace T3 with T1 by auto.
    replace T4 with T2 by auto.
    auto.
  - replace T3 with T1 by auto.
    replace T4 with T2 by auto.
    auto.
  - inversion H2.
    auto.
  - inversion H2.
    auto.
Qed.

Ltac equal_kinds :=
  repeat
    match goal with
    | [ Hr : row_projection ?E ?T (knd_row ?cs) _ _ |- _ ] =>
      match goal with
      | [ Hk : kinding E T (knd_row cs) |- _ ] =>
        fail 1
      | _ =>
        let Hk := fresh "Hk" in
        assert (kinding E T (knd_row cs)) as Hk
            by (apply (proj1 (row_projection_kinding Hr)))
      end
    | [ He : type_equal ?E ?T _ (knd_row ?cs) |- _ ] =>
      match goal with
      | [ Hk : kinding E T (knd_row cs) |- _ ] =>
        fail 1
      | _ =>
        let Hk := fresh "Hk" in
        assert (kinding E T (knd_row cs)) as Hk
            by (apply (proj1 (type_equal_kinding He)))
      end
    | [ He : type_equal ?E _ ?T (knd_row ?cs) |- _ ] =>
      match goal with
      | [ Hk : kinding E T (knd_row cs) |- _ ] =>
        fail 1
      | _ =>
        let Hk := fresh "Hk" in
        assert (kinding E T (knd_row cs)) as Hk
            by (apply (proj2 (type_equal_kinding He)))
      end
    end;
  repeat
    match goal with
    | [ Hk1 : kinding ?E ?T (knd_row ?cs1),
        Hk2 : kinding ?E ?T (knd_row ?cs2) |- _ ] =>
      match goal with
      | [ Heq : (knd_row cs1) = (knd_row cs2) |- _ ] =>
        fail 1
      | [ Heq : (knd_row cs2) = (knd_row cs1) |- _ ] =>
        fail 1
      | _ =>
        let Heq := fresh "Heq" in
        assert ((knd_row cs1) = (knd_row cs2)) as Heq
            by apply (kinding_unique Hk1 Hk2);
        inversion Heq;
        clear Heq;
        clear Hk2
      end
    end;
  substs.

Lemma row_projection_unique : forall E cs T K T' T'',
    row_projection E T K cs T' ->
    row_projection E T K cs T'' ->
    T' = T''.
Proof.
  introv Hpr1 Hpr2.
  gen T''.
  induction Hpr1; introv Hpr2.
  - eauto using row_projection_idem.
  - inversion Hpr2; subst; equal_kinds; auto.
    + assert (cons_non_empty cs3) by auto.
      false.
      constrs.
    + assert (cons_non_empty cs1).
      { apply row_projection_kinding in Hpr1.
        iauto. }
      false.
      constrs.
    + false.
      constrs.
  - inversion Hpr2; subst; equal_kinds; auto.
    + assert (cons_non_empty cs2) by auto.
      false.
      constrs.
    + assert (cons_non_empty cs1).
      { apply row_projection_kinding in Hpr1.
        iauto. }
      false.
      constrs.
    + false.
      constrs.
  - inversion Hpr2; subst.
    + replace (cons_inter (cons_union cs2 cs3) cs2)
        with cs2 in Hpr1_1 by constrs.
      replace (cons_inter (cons_union cs2 cs3) cs3)
        with cs3 in Hpr1_2 by constrs.
      apply row_projection_idem in Hpr1_1.
      apply row_projection_idem in Hpr1_2.
      subst.
      reflexivity.
    + equal_kinds.
      false.
      constrs.
    + equal_kinds.
      false.
      constrs.
    + equal_kinds.
      f_equal; auto.
  - inversion Hpr2; subst.
    + apply row_projection_idem in Hpr1_1.
      apply row_projection_idem in Hpr1_2.
      subst.
      reflexivity.
    + f_equal; auto.
  - inversion Hpr2; subst.
    + apply row_projection_idem in Hpr1_1.
      apply row_projection_idem in Hpr1_2.
      subst.
      reflexivity.
    + f_equal; auto.
  - inversion Hpr2; subst; auto.
  - inversion Hpr2; subst; auto.
Qed.

Lemma type_equal_project : forall E cs T1 T2 T1' K,
    type_equal E T1 T2 K ->
    row_projection E T1 K cs T1' ->
    exists T2',
    row_projection E T2 K cs T2' /\
    type_equal E T1' T2' (knd_row cs).
Proof.
  introv He Hpr.
  gen T1' cs.
  induction He; introv Hpr.
  - eauto using type_equal_refl with kinding.
  - inversion Hpr; subst.
    exists (typ_constructor c T').
    auto with kinding.
  - inversion Hpr; subst.
    + exists (typ_or T1' T2').
      auto with kinding.
    + equal_kinds.
      destruct (IHHe1 _ _ H6) as [T1'' ?].
      exists T1''.
      iauto.
    + equal_kinds.
      destruct (IHHe2 _ _ H9) as [T2'' ?].
      exists T2''.
      iauto.
    + equal_kinds.
      destruct (IHHe1 _ _ H8) as [T1'' ?].
      destruct (IHHe2 _ _ H11) as [T2'' ?].
      exists (typ_or T1'' T2'').
      split; iauto.
      replace cs
        with (cons_union (cons_inter cs cs1) (cons_inter cs cs2))
        by constrs.
      intuition auto with constrs.
  - inversion Hpr.
  - inversion Hpr.
  - inversion Hpr; subst; eauto with kinding.
  - inversion Hpr; subst; eauto with kinding.
  - inversion Hpr; subst.
    + exists (typ_meet T1' T2').
      auto with kinding.
    + destruct (IHHe1 _ _ H2) as [T1'' ?].
      destruct (IHHe2 _ _ H6) as [T2'' ?].
      exists (typ_meet T1'' T2'').
      iauto.
  - inversion Hpr; subst.
    + exists (typ_join T1' T2').
      auto with kinding.
    + destruct (IHHe1 _ _ H2) as [T1'' ?].
      destruct (IHHe2 _ _ H6) as [T2'' ?].
      exists (typ_join T1'' T2'').
      iauto.
  - destruct (IHHe1 _ _ Hpr) as [T2' [Hpr2 ?]].
    destruct (IHHe2 _ _ Hpr2) as [T3' ?].
    iauto.
  - replace (cons_union cs1 cs2)
        with (cons_union cs2 cs1) in * by constrs.
    assert (cons_disjoint cs2 cs1) by constrs.
    inversion Hpr; subst.
    + exists (typ_or T2 T1).
      intuition auto using type_equal_symm.
    + equal_kinds.
      exists T1'.
      replace (cons_union cs3 cs4)
        with (cons_union cs4 cs3) in * by constrs.
      auto using type_equal_refl with kinding.
    + equal_kinds.
      exists T1'.
      replace (cons_union cs3 cs4)
        with (cons_union cs4 cs3) in * by constrs.
      auto using type_equal_refl with kinding.
    + equal_kinds.
      exists (typ_or T2' T1'0).
      replace (cons_union cs3 cs4)
        with (cons_union cs4 cs3) in * by constrs.
      split; auto.
      replace cs
        with (cons_union (cons_inter cs cs3) (cons_inter cs cs4))
        by constrs.
      auto with kinding constrs.
  - inversion Hpr; subst.
    + exists (typ_or (typ_or T1 T2) T3).
      split; auto.
      rewrite cons_union_associative.
      auto with constrs.
    + assert (kinding E (typ_or T2 T3) (knd_row (cons_union cs2 cs3)))
        by auto.
      equal_kinds.
      exists T1'.
      split; auto using type_equal_refl with kinding.
      rewrite cons_union_associative.
      apply row_projection_or_l; auto with kinding; constrs.
    + { inversion H14; subst.
        - assert
            (kinding E (typ_or T2 T3) (knd_row (cons_union cs2 cs3)))
            by auto.
          equal_kinds.
          assert (cons_non_empty cs2) by auto.
          assert (cons_non_empty cs3) by auto.
          exists (typ_or T2 T3).
          split; auto using type_equal_refl with kinding.
          rewrite cons_union_associative.
          apply row_projection_or_both; auto with constrs.
          + replace (cons_inter (cons_union cs2 cs3)
                                (cons_union cs4 cs2))
              with cs2 by constrs.
            apply row_projection_or_r; auto; constrs.
          + replace (cons_inter (cons_union cs2 cs3) cs3)
              with cs3 by constrs.
            apply row_projection_identity.
            auto with kinding.
        - equal_kinds.
          exists T1'.
          split; auto using type_equal_refl with kinding.
          rewrite cons_union_associative.
          apply row_projection_or_l; auto; constrs.
        - equal_kinds.
          exists T1'.
          split; auto using type_equal_refl with kinding.
          rewrite cons_union_associative.
          apply row_projection_or_r; auto; constrs.
        - equal_kinds.
          exists (typ_or T1'0 T2').
          split; auto using type_equal_refl with kinding.
          rewrite cons_union_associative.
          apply row_projection_or_both; auto with constrs.
          apply row_projection_or_r; auto with constrs.
          replace (cons_inter cs (cons_union cs4 cs6))
            with (cons_inter cs cs6) by constrs.
          auto. }
      + { inversion H16; substs.
          - assert
              (kinding E (typ_or T2 T3)
                       (knd_row (cons_union cs2 cs3)))
              by auto.
            rewrite <- H15 in H14.
            equal_kinds.
            exists (typ_or (typ_or T1'0 T2) T3).
            split.
            + { rewrite <- H15.
                rewrite cons_union_associative.
                apply row_projection_or_both.
                - constrs.
                - constrs.
                - constrs.

            + assert
                (kinding E (typ_or T1'0 (typ_or T2 T3)) (knd_row cs))
                by auto with kinding.
              assert
                (kinding E (typ_or T1'0 (typ_or T2 T3))
                         (knd_row (cons_union (cons_inter cs cs4)
                                              (cons_union cs2 cs3)))).
              { apply row_projection_kinding in H13.
                apply kinding_or; auto with constrs. }
              equal_kinds.
              apply type_equal_or_associative_l;
                auto with constrs kinding.
              

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