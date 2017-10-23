(************************************************
 *          Row Subtyping - Kinding             *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import LibLN Definitions Infrastructure.

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

(* =============================================================== *)
(** ** Automation for kinding *)

Hint Resolve cons_non_empty_kind : kinding.

Ltac unlessInList X Xs T :=
  let b := inList X Xs in
  match b with
  | true => fail 1
  | false => constr:T
  end.

Ltac find_kinding Ts :=
  match goal with
  | [ H : kinding _ (typ_constructor ?c ?T) _ |- _ ] =>
    unlessInList (typ_constructor c T) Ts H
  | [ H : kinding _ (typ_or ?T1 ?T2) _ |- _ ] =>
    unlessInList (typ_or T1 T2) Ts H
  | [ H : kinding _ (typ_variant ?T1 ?T2) _ |- _ ] =>
    unlessInList (typ_variant T1 T2) Ts H
  | [ H : kinding _ (typ_arrow ?T1 ?T2) _ |- _ ] =>
    unlessInList (typ_arrow T1 T2) Ts H
  | [ H : kinding _ (typ_meet ?T1 ?T2) _ |- _ ] =>
    unlessInList (typ_meet T1 T2) Ts H
  | [ H : kinding _ (typ_join ?T1 ?T2) _ |- _ ] =>
    unlessInList (typ_join T1 T2) Ts H
  | [ H : kinding _ (typ_top ?cs) _ |- _ ] =>
    unlessInList (typ_top cs) Ts H
  | [ H : kinding _ (typ_bot ?cs) _ |- _ ] =>
    unlessInList (typ_bot cs) Ts H
  end.

Ltac kinding_type H :=
  match type of H with
  | kinding _ ?T _ => constr:T
  end.

Ltac invert_kinding_rec Ts :=
  try
    (let H := find_kinding Ts in
     let T := kinding_type H in
     inversion H;
     invert_kinding_rec (T, Ts)).

Ltac is_simple cs :=
  match cs with
  | cons_union _ _ => constr:false
  | cons_inter _ _ => constr:false
  | cons_universe => constr:false
  | cons_diff _ _ => constr:false
  | _ => constr:true
  end.

Ltac invert_knd_row_equal :=
  repeat
    match goal with
    | H : knd_row ?cs = knd_row ?cs |- _ =>
      clear H
    | H : knd_row ?cs1 = knd_row ?cs2 |- _ =>
      let var1 := is_simple cs1 in
      match var1 with
      | true =>
        replace cs1 with cs2 in * by
            (inversion H; reflexivity)
      | false =>
        let var2 := is_simple cs2 in
        match var2 with
        | true =>
          replace cs2 with cs1 in * by
              (inversion H; reflexivity)
        | false =>
          idtac
        end
      end
    end.

Ltac unique_kinding :=
  repeat
    match goal with
    | H1 : kinding ?E ?T ?K,
      H2 : kinding ?E ?T ?K |- _ =>
      clear H1
    | H1 : kinding ?E ?T (knd_row ?cs1),
      H2 : kinding ?E ?T (knd_row ?cs2) |- _ =>
      replace cs1 with cs2 in *
        by (apply (kinding_unique_row H2 H1))
    | H1 : kinding ?E ?T ?K1,
      H2 : kinding ?E ?T ?K2 |- _ =>
      replace K1 with K2 in *
        by apply (kinding_unique H2 H1)
    end.

Ltac invert_kinding :=
  invert_kinding_rec tt;
  subst;
  invert_knd_row_equal;
  unique_kinding.

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