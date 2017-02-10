(************************************************
 *          Row Subtyping - Soundness           *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import LibLN Definitions Infrastructure.

(* *************************************************************** *)
(** * Properties of kinding *)

(* *************************************************************** *)
(** Weakening *)

Hint Resolve binds_weaken.

Lemma kinding_weakening : forall E F G T K,
   kinding (E & G) T K -> 
   environment (E & F & G) ->
   kinding (E & F & G) T K.
Proof.
  introv Hk He.
  inductions Hk; auto.
Qed.

Hint Resolve kinding_weakening.

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

Hint Resolve kinding_weakening_l.

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

Hint Resolve kinding_weakening_r.

Lemma kindings_weakening : forall E F G n Ts Ks,
   kindings (E & G) n Ts Ks -> 
   environment (E & F & G) ->
   kindings (E & F & G) n Ts Ks.
Proof.
  introv Hk He.
  gen_eq EG : (E & G).
  induction Hk; intro; subst; auto.
  - apply* kindings_nil.
  - apply* kindings_cons.
Qed.

Hint Resolve kindings_weakening.

Lemma kinding_body_weakening : forall E F G n Ks T,
    kinding_body (E & G) n Ks T ->
    length Ks = n ->
    environment (E & F & G) ->
    kinding_body (E & F & G) n Ks T.
Proof.
  unfold kinding_body.
  introv Hk He.
  destruct Hk as [L Hk].
  exists_fresh Xs Hf.
  apply_ih_bind* kinding_weakening.
  apply environment_kinds with n; auto.
  rewrite! dom_concat.
  auto.
Qed.  

Hint Resolve kinding_body_weakening.

Lemma kinding_scheme_weakening : forall E F G M,
    kinding_scheme (E & G) M ->
    environment (E & F & G) ->
    kinding_scheme (E & F & G) M.
Proof.
  unfold kinding_scheme.
  introv Hk He.
  apply* kinding_body_weakening.
Qed.

Hint Resolve kinding_scheme_weakening.

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

Hint Resolve kinding_scheme_weakening_l.

(* *************************************************************** *)
(** Not affected by type bindings *)

Lemma kinding_bind_typ : forall E T K x S,
    kinding (E & x ~: S) T K ->
    kinding E T K.
Proof.
  introv Hk.
  gen_eq Ex : (E & x ~: S).
  induction Hk; intro; subst; eauto.
  destruct* (binds_push_inv H0) as [ [ _ Heq ] | ].
  inversion Heq.
Qed.

(* *************************************************************** *)
(** Preserved by type substitution *)

Lemma kinding_typ_subst : forall E F X T S K J,
  kinding (E & X ~:: J & F) T K -> 
  kinding E S J -> 
  kinding (E & (environment_subst X S F)) (typ_subst X S T) K.
Proof.
  introv Hkt Hks.
  gen_eq G : (E & X ~:: J & F).
  induction Hkt; introv Heq; subst; simpl typ_subst; auto.
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

Hint Resolve kinding_typ_subst.

(* *************************************************************** *)
(** Manipulating well-kinded environments *)

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

Hint Resolve kinding_env_shorten.

Lemma kinding_env_kinds : forall E n Ks Xs,
    kinding_env E ->
    (fresh (dom E) n Xs) ->
    length Ks = n ->
    kinding_env (E & Xs ~::* Ks).
Proof.
  introv Hk Hf Hlk.
  lets Hlx : (eq_sym (fresh_length _ _ _ Hf)).
  gen Ks n.
  induction Xs; destruct Ks;
    intros; subst; tryfalse; rew_kinds*.
  apply kinding_env_kind.
  - eapply IHXs; intuition.
    destruct* Hf.
  - eapply fresh_kinds; auto.
Qed.

Hint Resolve kinding_env_kinds.

Lemma kinding_scheme_from_env : forall E x M,
    kinding_env E ->
    binds x (bind_typ M) E ->
    kinding_scheme E M.
Proof.
  introv He Hb.
  induction E using env_ind; rew_env_concat.
  - false (binds_empty_inv Hb).
  - destruct (binds_push_inv Hb)
      as [ [ Hvar Hbind ] | [ Hvar Hbind ] ].
    + { subst.
        inversion He.
        - false (empty_push_inv H0).
        - destruct (eq_push_inv H) as [_ [Heq _]].
          false Heq.
        - destruct (eq_push_inv H) as [_ [Heq _]].
          inversion Heq.
          subst.
          apply* kinding_scheme_weakening_l. }
    + apply* kinding_scheme_weakening_l.
Qed.

Hint Resolve kinding_scheme_from_env.

(* *************************************************************** *)
(** Kinding of schemes with no parameters *)

Lemma kinding_scheme_no_params : forall E T M,
    kinding E T kind_type ->
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

Hint Resolve kinding_env_shorten.

(* *************************************************************** *)
(** * Properties of type equality *)

(* *************************************************************** *)
(** Reflexivity *)

Lemma type_equal_refl : forall E T K,
    kinding E T K ->
    type_equal E T T K.
Proof.
  introv Hk.
  induction* Hk.
Qed.

Hint Resolve type_equal_refl.

(* *************************************************************** *)
(** Symmetry *)

Lemma type_equal_symm : forall E T1 T2 K,
    type_equal E T1 T2 K ->
    type_equal E T2 T1 K.
Proof.
  introv He.
  induction* He.
Qed.

Hint Resolve type_equal_symm.

(* *************************************************************** *)
(** Idempotence of join and meet *)

Lemma type_equal_join_idempotent : forall E T,
    kinding E T kind_row ->
    type_equal E (typ_join T T) T kind_row.
Proof.
  introv Hk.
  apply type_equal_trans
    with (typ_join T (typ_meet T typ_top)); auto.
Qed.

Hint Resolve type_equal_join_idempotent.

Lemma type_equal_meet_idempotent : forall E T,
    kinding E T kind_row ->
    type_equal E (typ_meet T T) T kind_row.
Proof.
  introv Ht.
  apply type_equal_trans
    with (typ_meet T (typ_join T typ_bot)); auto.
Qed.

Hint Resolve type_equal_meet_idempotent.

(* *************************************************************** *)
(** Well-kindedness *)

Lemma type_equal_kinding : forall E T1 T2 K,
    type_equal E T1 T2 K ->
    kinding E T1 K /\ kinding E T2 K.
Proof.
  introv He.
  induction* He.
Qed.

Hint Extern 1 (kinding ?E ?T ?K) =>
  match goal with
  | H: type_equal E T _ K |- _ =>
      apply (proj1 (type_equal_kinding H))
  | H: type_equal E _ T K |- _ =>
      apply (proj2 (type_equal_kinding H))
  end.

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
  inductions Hkt; introv Heq; subst; simpl typ_subst; eauto.
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

Hint Resolve type_equal_typ_subst.

(* *************************************************************** *)
(** Weakening *)

Lemma type_equal_weakening : forall E F G T1 T2 K,
   type_equal (E & G) T1 T2 K -> 
   environment (E & F & G) ->
   type_equal (E & F & G) T1 T2 K.
Proof.
  introv Heq Henv.
  inductions Heq; auto.
  - apply type_equal_trans with T2.
    + apply IHHeq1 with (E0 := E) (G0 := G); auto.
    + apply IHHeq2 with (E0 := E) (G0 := G); auto.
Qed.

Hint Resolve type_equal_weakening.

(* *************************************************************** *)
(** * Properties of Subtyping *)

(* *************************************************************** *)
(** Reflexivity *)

Lemma subtype_refl : forall E T,
  kinding E T kind_row -> 
  subtype E T T.
Proof.
  introv Hk.
  inversion Hk; unfold subtype; auto.
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
  apply type_equal_trans with (typ_join T1 T2); auto.
  apply type_equal_trans with (typ_join T1 (typ_join T2 T3)); auto.
  apply type_equal_trans with (typ_join (typ_join T1 T2) T3); auto.
Qed.

(* *************************************************************** *)
(** Anti-symmetry *)

Lemma subtype_antisymm : forall E T1 T2,
    subtype E T1 T2 ->
    subtype E T2 T1 ->
    type_equal E T1 T2 kind_row.
Proof.
  introv H12 H21.
  unfold subtype in *.
  apply type_equal_trans with (typ_join T1 T2); auto.
  apply type_equal_trans with (typ_join T2 T1); auto.
Qed.

(* *************************************************************** *)
(* Well-kindedness *)

Lemma subtype_kinding : forall E T1 T2,
    subtype E T1 T2 ->
    kinding E T1 kind_row /\ kinding E T2 kind_row.
Proof.
  introv He.
  destruct (type_equal_kinding He) as [ Hk Hj ].
  split*.
  inversion* Hj.
Qed.

Hint Extern 1 (kinding ?E ?T kind_row) =>
  match goal with
  | H: subtype E T _ |- _ =>
      apply (proj1 (subtype_kinding H))
  | H: subtype E _ T |- _ =>
      apply (proj2 (subtype_kinding H))
  end.

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

Hint Resolve subtype_weakening.

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

Hint Resolve subtype_typ_subst.

(* *************************************************************** *)
(** * Properties of typing *)

Lemma typing_kinding_env : forall E e T,
    typing E e T ->
    kinding_env E.
Proof.
  introv Ht.
  induction* Ht.
  - pick_fresh x.
    eapply kinding_env_shorten in H1; auto.
  - pick_freshes (sch_arity M) Xs.
    eapply kinding_env_shorten in H0; auto.
Qed.

Hint Resolve typing_kinding_env.

Lemma typing_kinding : forall E e T,
    typing E e T ->
    kinding E T kind_type.
Proof.
  introv Ht.
  induction* Ht.
  - assert (kinding_scheme E M).
    { apply kinding_scheme_from_env with x; auto. }
    destruct H2 as [L Hs].
    unfold sch_open.
    pick_freshes (sch_arity M) Xs.
    unfold sch_fv in Fr.
    lets Hlx : (fresh_length _ _ _ Fr).
    lets Hlk : (proj1 (proj2 (kindings_regular H1))).
    apply kinding_typ_substs_l
      with (Xs := Xs) (n := sch_arity M) (Ss := Us)
      in Hs; auto.
    rewrite (@typ_substs_intro Xs Us _); auto.
    rewrite* <- Hlx.
  - apply* kinding_arrow.
    pick_fresh x.
    eapply kinding_bind_typ in H1; auto.
  - inversion* IHHt1.
  - pick_fresh x.
    eapply kinding_bind_typ in H2; auto.
  - pick_fresh x.
    eapply kinding_bind_typ in H0; auto.
Qed.

Hint Resolve typing_kinding.

Lemma typing_scheme_kinding : forall E e M,
    typing_scheme E e M ->
    kinding_scheme E M.
Proof.
  introv [L Ht].
  exists_fresh Xs Hf.
  eapply typing_kinding in Ht; eauto.
Qed.  

Hint Resolve typing_scheme_kinding.

(* *************************************************************** *)
(** Weakening *)

Lemma typing_weakening : forall E F G e T,
   typing (E & G) e T -> 
   kinding_env (E & F & G) ->
   typing (E & F & G) e T.
Proof.
  introv Ht.
  gen_eq EG : (E & G).
  gen E F G.
  induction Ht; intros; subst; eauto.
  - apply_fresh* typing_abs as y.
    apply_ih_bind H1; auto.
    eapply kinding_scheme_no_params in H; auto.
    apply* kinding_env_typ.
  - apply_fresh (@typing_let M) as Ys.
    + apply_ih_bind H0; auto.
      apply kinding_env_kinds with (sch_arity M); auto.
      rewrite! dom_concat.
      auto.
    + apply_ih_bind H2; auto.
      apply* kinding_env_typ.
      eapply typing_scheme_kinding.
      exists_fresh Xs Hf.
      apply_ih_bind H0; auto.
      apply kinding_env_kinds with (sch_arity M); auto.
      rewrite! dom_concat.
      auto.
  - apply_fresh* (@typing_match c) as Ys.
    + { apply_ih_bind H0; auto.
        apply* kinding_env_typ.
        apply kinding_scheme_no_params with T3; auto.
        assert (kinding (E0 & F & G)
                  (typ_join (typ_constructor c T3) T6) kind_row)
          by eauto.
        inversion H6.
        inversion H11.
        auto. }
    + apply_ih_bind H2; auto.
      apply* kinding_env_typ.
      apply kinding_scheme_no_params with (typ_variant T5 T6); auto.
  - eapply typing_absurd; auto.
Qed.
   
(* *************************************************************** *)
(** Preserved by type substitution *)

Lemma typing_typ_subst : forall F Z U E t T,
  Z \notin (env_fv E) -> 
  type U -> 
  E & F |= t ~: T -> 
  E & (map (sch_subst Z U) F) |= t ~: (typ_subst Z U T).

