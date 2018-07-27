(************************************************
 *          Row Subtyping - Well-formedness     *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import List LibLN Cofinite Disjoint Definitions Substitution.

(* *************************************************************** *)
(** ** Automation *)

Hint Constructors
  kind kinds type types kinds_and_type
  scheme schemes term terms environment store store_type.

Hint Extern 1 (types _ _) => split; auto.

Tactic Notation "econstr" tactic3(tac2) :=
  try (econstructor; try eassumption; solve [tac2]).

(* =============================================================== *)
(** * Properties of terms *)

Lemma term_abs_body : forall t1,
    term_body t1 -> term (trm_abs t1).
Proof.
  introv [L Ht].
  eauto.
Qed.

Lemma term_let_body : forall t1 t2,
    term t1 -> term_body t2 ->
    term (trm_let t1 t2).
Proof.
  introv Ht1 [L Ht2].
  eauto.
Qed.

Lemma term_match_body : forall t1 c t2 t3,
    term t1 ->
    term_body t2 ->
    term_body t3 ->
    term (trm_match t1 c t2 t3).
Proof.
  introv Ht1 [L2 Ht2] [L3 Ht3].
  apply term_match with (L := L2 \u L3); eauto.
Qed.

Lemma term_destruct_body : forall t1 c t2,
    term t1 ->
    term_body t2 ->
    term (trm_destruct t1 c t2).
Proof.
  introv Ht1 [L Ht2].
  eauto.
Qed.

Lemma term_fix_body : forall t1,
    term_body2 t1 ->
    term (trm_fix t1).
Proof.
  introv [L Ht].
  eauto.
Qed.

Hint Resolve term_abs_body term_let_body
     term_match_body term_destruct_body term_fix_body.

(** Terms are stable by substitution *)

Lemma trm_var_subst_term : forall x zs us,
    terms us -> term (trm_var_subst zs us x).
Proof.
  introv Ht.
  generalize dependent us.
  induction zs; introv Ht; induction us; simpl; auto.
  inversion Ht; subst.
  case_var; auto.
Qed.

Lemma trm_subst_term : forall t zs us,
  terms us -> term t -> term (trm_subst zs us t).
Proof.
  introv Htu Ht.
  induction Ht; simpl in *; auto using trm_var_subst_term. 
  - apply_fresh term_abs as y;
      rewrite trm_subst_open_var; auto.
  - apply_fresh term_let as y;
      rewrite? trm_subst_open_var; auto.
  - apply_fresh term_match as y;
      rewrite? trm_subst_open_var; auto.
  - apply_fresh term_destruct as y;
      rewrite? trm_subst_open_var; auto.
  - apply_fresh term_fix as x.
    introv Hf1 Hf2.
    rewrite trm_subst_open_vars; simpl; auto.
Qed.

(** ** Opening a body with a term gives a term *)

Lemma trm_open_term : forall t u,
  term_body t -> term u -> term (t ^^ u).
Proof.
  introv Htb Ht.
  destruct Htb.
  pick_fresh y.
  rewrite (@trm_subst_intro (y::nil)); auto.
  apply trm_subst_term; auto.
  replace (trm_fvars (y :: nil)) with (trm_fvar y :: nil) by auto.
  auto.
Qed.

Hint Resolve trm_open_term.

Lemma trm_open_term_var : forall t x,
  term_body t -> term (t ^ x).
Proof.
  introv Ht.
  apply trm_open_term; auto.
Qed.

Hint Resolve trm_open_term_var.

Lemma trm_open_term2 : forall t u v,
  term_body2 t -> term u -> term v -> term (t ^^* (u::v::nil)).
Proof.
  introv Htb Ht1 Ht2.
  destruct Htb.
  pick_fresh y.
  pick_fresh z.
  rewrite (@trm_subst_intro (y::z::nil)); auto.
  apply trm_subst_term; auto.
Qed.

Hint Resolve trm_open_term2.

Lemma trm_open_term_var2 : forall t x y,
  term_body2 t -> term (t ^* (x::y::nil)).
Proof.
  introv Ht.
  apply trm_open_term2; auto.
Qed.

Hint Resolve trm_open_term_var2.

(* =============================================================== *)
(** * Properties of types *)

(** Types of fvars *)
Lemma types_fvars : forall Xs,
    types (typ_fvars Xs).
Proof.
  induction Xs; simpl; auto.
Qed.

Hint Resolve types_fvars.
 
(** Types are stable by type substitution *)

Lemma typ_var_subst_type : forall X Zs Us,
    types Us -> type (typ_var_subst Zs Us X).
Proof.
  introv Ht.
  generalize dependent Us.
  induction Zs; introv Ht; induction Us; simpl; auto.
  inversion Ht; subst.
  case_var; auto.
Qed.

Lemma typ_subst_type : forall T Zs Us,
  types Us -> type (typ_subst Zs Us T) <-> type T.
Proof.
  introv Htu.
  split.
  - introv Ht.
    induction T; simpl in Ht; inversion Ht; auto.
  - introv Ht.
    induction Ht; simpl in *; auto using typ_var_subst_type. 
Qed.

(** List of types are stable by type substitution *)

Lemma typ_subst_type_list : forall Zs Us Ts,
  types Us ->
  types (typ_subst_list Zs Us Ts) <-> types Ts.
Proof.
  introv Ht.
  induction Ts; simpl in *;
    split; introv Hts; inversion Hts; subst; auto.
  - rewrite typ_subst_type in *; auto.
    rewrite IHTs in *; auto.
  - rewrite <- typ_subst_type with (Zs := Zs) (Us := Us) in *; auto.
    rewrite <- IHTs in *; auto.
Qed.

(* =============================================================== *)
(** * Properties of kinds *)

(** Kinds are stable by type substitution *)

Lemma knd_subst_kind : forall K Zs Us,
  types Us -> kind (knd_subst Zs Us K) <-> kind K.
Proof.
  introv Ht.
  split.
  - introv Hk.
    induction K; simpl in Hk; auto.
    inversion Hk.
    rewrite typ_subst_type in *; auto.
  - introv Hk.
    induction Hk; simpl; auto.
    apply kind_range; rewrite typ_subst_type; auto.
Qed.  

Lemma knd_subst_kind_list : forall Ks Zs Us,
  types Us -> kinds (knd_subst_list Zs Us Ks) <-> kinds Ks.
Proof.
  introv Ht.
  induction Ks; simpl in *;
    split; introv Hks; inversion Hks; subst; auto.
  - rewrite knd_subst_kind in *; auto.
    rewrite IHKs in *; auto.
  - rewrite <- knd_subst_kind with (Zs := Zs) (Us := Us) in *; auto.
    rewrite <- IHKs in *; auto.
Qed.  

(* =============================================================== *)
(** * Properties of schemes *)

Lemma scheme_empty_type : forall T,
    type T <-> scheme (sch_empty T).
Proof.
  split.
  - introv Ht.
    apply scheme_c with (L := \{}).
    simpl.
    introv Fr.
    fresh_length Fr as Hl.
    destruct Xs; try discriminate.
    rewrite typ_open_vars_nil.
    auto.
  - introv Hs.
    inversion Hs as [M L H]; subst.
    simpl in H.
    specialize (H nil I).
    rewrite typ_open_vars_nil in H.
    destruct H.
    auto.
Qed.

Hint Resolve -> scheme_empty_type.

(** Schemes are stable by type substitution *)

Lemma sch_subst_type : forall M Zs Us,
    types Us -> scheme (sch_subst Zs Us M) <-> scheme M.
Proof.
  introv Hu.
  split.
  - introv Hs.
    inversion Hs as [L ? H]; subst.
    apply scheme_c with (L := L \u (from_list Zs)).
    autorewrite with rew_sch_arity in *.
    introv Hf.
    assert (fresh L (sch_arity M) Xs) as Hf2 by auto.
    specialize (H Xs Hf2).
    inversion H as [? ? Hks Ht]; subst.
    simpl in *.
    rewrite <- knd_subst_list_open_vars in Hks; auto.
    rewrite knd_subst_kind_list in Hks; auto.
    rewrite typ_subst_open_vars in Ht; auto.
    rewrite typ_subst_type in Ht; auto.
  - introv Hs.
    inversion Hs as [L ? H]; subst.
    apply scheme_c
      with (L := from_list Zs \u L \u (typ_fv_list Us)).
    autorewrite with rew_sch_arity in *.
    introv Hf.
    assert (fresh L (sch_arity M) Xs) as Hf2 by auto.
    specialize (H Xs Hf2).
    inversion H as [? ? Hks Ht]; subst.
    rewrite <- knd_subst_kind_list
      with (Zs := Zs) (Us := Us) in Hks; auto.
    rewrite knd_subst_list_open_vars in Hks; auto.
    rewrite <- typ_subst_type
      with (Zs := Zs) (Us := Us) in Ht; auto.
    rewrite <- typ_subst_open_vars in Ht; auto.
Qed.

Lemma sch_subst_scheme_list : forall Ms Zs Us,
  types Us -> schemes (sch_subst_list Zs Us Ms) <-> schemes Ms.
Proof.
  introv Ht.
  induction Ms; simpl in *;
    split; introv Hss; inversion Hss; subst; auto.
  - rewrite sch_subst_type in *; auto.
    rewrite IHMs in *; auto.
  - rewrite <- sch_subst_type with (Zs := Zs) (Us := Us) in *; auto.
    rewrite <- IHMs in *; auto.
Qed.

(** ** Instantiating a scheme with types gives a type *)

Lemma scheme_instance_type : forall M Us,
    types Us -> length Us = sch_arity M ->
    scheme M ->
    type (instance M Us).
Proof.
  introv Hts Hl Hs.
  destruct Hs as [L ? H].
  pick_freshes (sch_arity M) Xs.
  rewrite typ_subst_intro_instance with (Xs := Xs); auto.
  apply typ_subst_type; auto.
  assert (fresh L (sch_arity M) Xs) as Hf by auto.
  specialize (H Xs Hf).
  inversion H; subst.
  auto. 
Qed.

(* =============================================================== *)
(** * Properties of environment *)

Lemma ok_middle : forall A E F x (v : A),
  ok (E & F) ->
  x # (E & F) ->
  ok (E & x ~ v & F).
Proof.
  introv Hok Hn.
  induction F using env_ind;
    autorewrite with rew_env_concat in *;
    autorewrite with rew_env_dom in *; auto.
  destruct (ok_push_inv Hok).
  auto.
Qed.

Lemma ok_concat : forall A (E : LibEnv.env A) F,
    ok E -> ok F ->
    disjoint (dom E) (dom F) ->
    ok (E & F).
Proof.
  introv Hok1 Hok2 Hd.
  induction F using env_ind;
    autorewrite with rew_env_concat in *;
    autorewrite with rew_env_dom in *; auto.
  destruct (ok_push_inv Hok2).
  auto.
Qed.

Lemma ok_concat_inv : forall A (E : LibEnv.env A) F,
    ok (E & F) ->
    disjoint (dom E) (dom F) /\ ok E /\ ok F.
Proof.
  introv Hok.
  splits; eauto using ok_concat_inv_l, ok_concat_inv_r.
  induction F using env_ind;
    autorewrite with rew_env_concat in *;
    autorewrite with rew_env_dom in *; auto.
  destruct (ok_push_inv Hok).
  autorewrite with rew_env_dom in *.
  auto.
Qed.

Lemma ok_from_environment : forall E,
  environment E -> ok E.
Proof.
  introv He.
  induction He; auto. 
Qed.

(* Constructor for concatenations *)

Lemma environment_concat : forall E F,
    environment E ->
    environment F ->
    ok (E & F) ->
    environment (E & F).
Proof.
  introv He1 He2 Hok.
  induction He2;
    autorewrite with rew_env_concat in *; auto.
  - remember (E & E0 & X ~:: K) as F.
    destruct Hok; auto.
    destruct (eq_push_inv HeqF) as [? [? ?]]; subst; auto.
  - remember (E & E0 & x ~: M) as F.
    destruct Hok; auto.
    destruct (eq_push_inv HeqF) as [? [? ?]]; subst; auto.
Qed.

(* Constructors for bind_knds and sch_bind_knds *)

Lemma environment_bind_knds : forall E Xs Ks,
    environment E ->
    fresh (dom E) (length Ks) Xs ->
    kinds Ks ->
    environment (E & bind_knds Xs Ks).
Proof.
  introv He Hf Hks.
  generalize dependent Ks.
  generalize dependent E.
  induction Xs; introv He Hf Hks; simpl.
  - autorewrite with rew_env_concat; auto.
  - induction Ks; simpl.
    + autorewrite with rew_env_concat; auto.
    + destruct Hf.
      inversion Hks; subst.
      rewrite concat_assoc.
      apply IHXs; auto.
      autorewrite with rew_env_dom in *.
      auto.
Qed.

Lemma environment_kinds : forall E Xs M,
    environment E ->
    fresh (dom E) (sch_arity M) Xs ->
    scheme M ->
    environment (E & Xs ~::* M).
Proof.
  introv He Hf Hs.
  destruct Hs as [L ? H].
  destruct M as [Ks T].
  unfold bind_sch_kinds.
  simpl in *.
  fresh_length Hf as Hl.
  rewrite Hl in *.
  apply environment_bind_knds;
    try rewrite knd_open_vars_list_length, Hl;
    auto.
  pick_freshes (length Xs) Ys.
  assert (fresh L (length Xs) Ys) as Hf2 by auto.
  unfold knd_open_vars_list.
  rewrite knd_subst_list_intro with (Xs := Ys); auto.
  - rewrite knd_subst_kind_list; auto.    
    specialize (H Ys Hf2).
    inversion H; subst; auto.
  - unfold typ_fvars.
    rewrite map_length.
    auto.
Qed.

Lemma environment_bind_typs : forall E xs Ms,
    environment E ->
    fresh (dom E) (length Ms) xs ->
    schemes Ms ->
    environment (E & bind_typs xs Ms).
Proof.
  introv He Hf Hss.
  generalize dependent Ms.
  generalize dependent E.
  induction xs; introv He Hf Hss; simpl.
  - autorewrite with rew_env_concat; auto.
  - induction Ms; simpl.
    + autorewrite with rew_env_concat; auto.
    + destruct Hf.
      inversion Hss; subst.
      rewrite concat_assoc.
      apply IHxs; auto.
      autorewrite with rew_env_dom in *.
      auto.
Qed.

(* Inversions for various constructors *)

Lemma environment_typ_inv : forall E x M,
    environment (E & x ~: M) ->
    environment E /\ x # E /\ scheme M.
Proof.
  introv He.
  remember (E & x ~: M) as Ex.
  destruct He.
  - apply empty_push_inv in HeqEx; contradiction.
  - destruct (eq_push_inv HeqEx) as [? [? ?]].
    discriminate.
  - destruct (eq_push_inv HeqEx) as [? [Hb ?]].
    inversion Hb; subst.
    splits; auto.
Qed.

Lemma environment_knd_inv : forall E X K,
    environment (E & X ~:: K) ->
    environment E /\ X # E /\ kind K.
Proof.
  introv He.
  remember (E & X ~:: K) as Ex.
  destruct He.
  - apply empty_push_inv in HeqEx; contradiction.
  - destruct (eq_push_inv HeqEx) as [? [Hb ?]].
    inversion Hb; subst.
    splits; auto.
  - destruct (eq_push_inv HeqEx) as [? [? ?]].
    discriminate.
Qed.

Lemma environment_concat_inv : forall E F,
    environment (E & F) ->
    environment E /\ environment F.
Proof.
  introv He.
  remember (E & F) as EF.
  generalize dependent F.
  generalize dependent E.
  induction He; introv HeqEF.
  - destruct (empty_concat_inv HeqEF); subst.
    split; auto.
  - induction F using env_ind;
      autorewrite with rew_env_concat in *; subst.
    + intuition auto.
    + destruct (eq_push_inv HeqEF) as [? [? ?]]; subst.
      specialize (IHHe E0 F).
      intuition auto.
  - induction F using env_ind;
      autorewrite with rew_env_concat in *; subst.
    + intuition auto.
    + destruct (eq_push_inv HeqEF) as [? [? ?]]; subst.
      specialize (IHHe E0 F).
      intuition auto.
Qed.

Lemma environment_bind_knds_inv : forall E Xs Ks,
    environment (E & bind_knds Xs Ks) ->
    length Ks = length Xs ->
    environment E /\ fresh (dom E) (length Ks) Xs /\ kinds Ks.
Proof.
  introv He Hl.
  generalize dependent Ks.
  induction Xs; introv He Hl; induction Ks; try discriminate;
    simpl in *; autorewrite with rew_env_concat in *.
  - splits; auto.
  - destruct (environment_concat_inv He) as [He2 ?].
    destruct (environment_knd_inv He2) as [? [? ?]].
    inversion Hl.
    assert (a # bind_knds Xs Ks)
      by eauto using ok_middle_inv_r, ok_from_environment.
    assert (ok (E & bind_knds Xs Ks))
      by eauto using ok_remove, ok_from_environment.    
    destruct IHXs with (Ks := Ks) as [? [? ?]];
      auto using environment_concat.
    autorewrite with rew_env_dom in *; auto.
    splits; auto using fresh_from_notin.
Qed.

Lemma environment_bind_typs_inv : forall E xs Ms,
    environment (E & bind_typs xs Ms) ->
    length Ms = length xs ->
    environment E /\ fresh (dom E) (length Ms) xs /\ schemes Ms.
Proof.
  introv He Hl.
  generalize dependent Ms.
  induction xs; introv He Hl; induction Ms; try discriminate;
    simpl in *; autorewrite with rew_env_concat in *.
  - splits; auto.
  - destruct (environment_concat_inv He) as [He2 ?].
    destruct (environment_typ_inv He2) as [? [? ?]].
    inversion Hl.
    assert (a # bind_typs xs Ms)
      by eauto using ok_middle_inv_r, ok_from_environment.
    assert (ok (E & bind_typs xs Ms))
      by eauto using ok_remove, ok_from_environment.    
    destruct IHxs with (Ms := Ms) as [? [? ?]];
      auto using environment_concat.
    autorewrite with rew_env_dom in *; auto.
    splits; auto using fresh_from_notin.
Qed.
    
(* Middle constructors and inversions *)

Lemma environment_middle_typ : forall E F x M,
    environment (E & F) ->
    scheme M ->
    x # E & F ->
    environment (E & x ~: M & F).
Proof.
  introv He Hs Hn.
  destruct (environment_concat_inv He) as [? ?].
  auto using environment_concat, ok_middle, ok_from_environment.
Qed.

Lemma environment_middle_typ_inv : forall E F x M,
    environment (E & x ~: M & F) ->
    environment (E & F) /\ scheme M /\ x # E & F.
Proof.
  introv He.
  assert (ok (E & x ~: M & F)) as Hok
    by auto using ok_from_environment.
  destruct (ok_middle_inv Hok).
  apply ok_remove in Hok.
  destruct (environment_concat_inv He) as [He2 ?].
  destruct (environment_typ_inv He2) as [? [? ?]].
  splits; auto using environment_concat.
Qed.

Lemma environment_middle_knd : forall E F X K,
    environment (E & F) ->
    kind K ->
    X # E & F ->
    environment (E & X ~:: K & F).
Proof.
  introv He Hs Hn.
  destruct (environment_concat_inv He) as [? ?].
  auto using environment_concat, ok_middle, ok_from_environment.
Qed.

Lemma environment_middle_knd_inv : forall E F X K,
    environment (E & X ~:: K & F) ->
    environment (E & F) /\ kind K /\ X # E & F.
Proof.
  introv He.
  assert (ok (E & X ~:: K & F)) as Hok
    by auto using ok_from_environment.
  destruct (ok_middle_inv Hok).
  apply ok_remove in Hok.
  destruct (environment_concat_inv He) as [He2 ?].
  destruct (environment_knd_inv He2) as [? [? ?]].
  splits; auto using environment_concat.
Qed.

Lemma environment_middle_bind_knds : forall E F Xs Ks,
    environment (E & F) ->
    fresh (dom E \u dom F) (length Ks) Xs ->
    kinds Ks ->
    environment (E & bind_knds Xs Ks & F).
Proof.
  introv He Hf Hks.
  destruct (environment_concat_inv He).
  destruct (ok_concat_inv (ok_from_environment He)) as [? [? ?]].
  fresh_length Hf as Hl.
  assert (environment (E & bind_knds Xs Ks))
    by auto using environment_bind_knds.
  apply environment_concat; auto.
  apply ok_concat; auto using ok_from_environment.
  autorewrite with rew_env_dom; auto.
Qed.

Lemma environment_middle_bind_knds_inv : forall E F Xs Ks,
    environment (E & bind_knds Xs Ks & F) ->
    length Ks = length Xs ->
    environment (E & F)
    /\ fresh (dom E \u dom F) (length Ks) Xs /\ kinds Ks.
Proof.
  introv He Hl.
  destruct (environment_concat_inv He) as [He2 ?].
  destruct (environment_bind_knds_inv Xs Ks He2) as [? [? ?]]; auto.
  splits;
    eauto using environment_concat, ok_remove, ok_from_environment.
  destruct (ok_concat_inv (ok_from_environment He)) as [? [? ?]].
  autorewrite with rew_env_dom in *; auto using fresh_disjoint.
Qed.
  
Lemma environment_middle_kinds : forall E F Xs M,
    environment (E & F) ->
    fresh (dom (E & F)) (sch_arity M) Xs ->
    scheme M ->
    environment (E & Xs ~::* M & F).
Proof.
  introv He Hf Hs.
  autorewrite with rew_env_dom in Hf.
  fresh_length Hf as Hl.
  destruct (environment_concat_inv He) as [? ?].
  assert (environment (E & Xs ~::* M))
    by auto using environment_kinds.
  assert (ok (E & F)) as Hok
    by auto using ok_from_environment.
  destruct (ok_concat_inv Hok) as [? [? ?]].
  apply environment_concat; auto.
  apply ok_concat;
     autorewrite with rew_env_dom; auto using ok_from_environment.
Qed.

Lemma environment_middle_bind_typs : forall E F xs Ms,
    environment (E & F) ->
    fresh (dom E \u dom F) (length Ms) xs ->
    schemes Ms ->
    environment (E & bind_typs xs Ms & F).
Proof.
  introv He Hf Hss.
  destruct (environment_concat_inv He).
  destruct (ok_concat_inv (ok_from_environment He)) as [? [? ?]].
  fresh_length Hf as Hl.
  assert (environment (E & bind_typs xs Ms))
    by auto using environment_bind_typs.
  apply environment_concat; auto.
  apply ok_concat; auto using ok_from_environment.
  autorewrite with rew_env_dom; auto.
Qed.

Lemma environment_middle_bind_typs_inv : forall E F xs Ms,
    environment (E & bind_typs xs Ms & F) ->
    length Ms = length xs ->
    environment (E & F)
    /\ fresh (dom E \u dom F) (length Ms) xs /\ schemes Ms.
Proof.
  introv He Hl.
  destruct (environment_concat_inv He) as [He2 ?].
  destruct (environment_bind_typs_inv xs Ms He2) as [? [? ?]]; auto.
  splits;
    eauto using environment_concat, ok_remove, ok_from_environment.
  destruct (ok_concat_inv (ok_from_environment He)) as [? [? ?]].
  autorewrite with rew_env_dom in *; auto using fresh_disjoint.
Qed.
  
(* Various parital inversions *)

Lemma environment_concat_inv_l : forall E F,
    environment (E & F) ->
    environment E.
Proof.
  introv He.
  destruct (environment_concat_inv He).
  assumption.
Qed.

Lemma environment_concat_inv_r : forall E F,
    environment (E & F) ->
    environment F.
Proof.
  introv He.
  destruct (environment_concat_inv He).
  assumption.
Qed.

Lemma environment_remove : forall E F G,
    environment (E & F & G) ->
    environment (E & G).
Proof.
  introv He.
  destruct (environment_concat_inv He) as [He2 ?].
  destruct (environment_concat_inv He2) as [? ?].
  eauto using environment_concat, ok_remove, ok_from_environment.
Qed.

Lemma environment_middle_inv_fresh : forall E F x b,
    environment (E & x ~ b & F) ->
    x # (E & F).
Proof.
  introv He.
  assert (ok (E & x ~ b & F)) as Hok
    by auto using ok_from_environment.
  destruct (ok_middle_inv Hok).
  auto.
Qed.

Lemma environment_push_inv_fresh : forall E x b,
    environment (E & x ~ b) ->
    x # E.
Proof.
  introv He.
  rewrite <- concat_empty_r in He.
  rewrite <- (concat_empty_r E).
  eauto using environment_middle_inv_fresh.
Qed.

Lemma environment_typ_inv_scheme : forall E x M,
    environment (E & x ~: M) ->
    scheme M.
Proof.
  introv He.
  destruct (environment_typ_inv He) as [? [? ?]].
  assumption.
Qed.

Lemma environment_knd_inv_kind : forall E X K,
    environment (E & X ~:: K) ->
    kind K.
Proof.
  introv He.
  destruct (environment_knd_inv He) as [? [? ?]].
  assumption.
Qed.

Lemma environment_middle_inv_env : forall E F x v,
    environment (E & x ~ v & F) ->
    environment (E & F).
Proof.
  introv He.
  destruct (environment_concat_inv He) as [He2 ?].
  destruct (environment_concat_inv He2) as [? ?].
  eauto using environment_concat, ok_remove, ok_from_environment.
Qed.

Lemma environment_typ_middle_inv_scheme : forall E F x M,
    environment (E & x ~: M & F) ->
    scheme M.
Proof.
  introv He.
  destruct (environment_concat_inv He) as [He2 ?].
  eauto using environment_typ_inv_scheme.
Qed.

Lemma environment_knd_middle_inv_kind : forall E F X K,
    environment (E & X ~:: K & F) ->
    kind K.
Proof.
  introv He.
  destruct (environment_concat_inv He) as [He2 ?].
  eauto using environment_knd_inv_kind.
Qed.

Lemma environment_middle_bind_knds_swap : forall E F Xs Ks Ys,
  length Xs = length Ks ->
  fresh (dom E \u dom F) (length Ks) Ys ->
  environment (E & bind_knds Xs Ks & F) ->
  environment (E & bind_knds Ys Ks & F).
Proof.
  introv Hl Hf He.
  destruct (environment_middle_bind_knds_inv Xs Ks He) as [? [? ?]];
    auto using environment_middle_bind_knds.
Qed.

Lemma binds_weakening : forall E F G X B,
    binds X B (E & G) ->
    environment (E & F & G) ->
    binds X B (E & F & G).
Proof.
  introv Hb He.
  assert (ok (E & F & G))
    by auto using ok_from_environment.
  apply binds_weaken; assumption.
Qed.

Lemma binds_in_dom : forall A x (v : A) E,
  binds x v E -> x \in dom E.
Proof.
  eauto using binds_get, get_some_inv.
Qed.

Lemma binds_typ_bind_knds_inv : forall x M Xs Ks,
  binds x (bind_typ M) (bind_knds Xs Ks) -> False.
Proof.
  introv Hb.
  generalize dependent Ks.
  induction Xs; introv Hb; destruct Ks; simpl in Hb;
    eauto using binds_empty_inv.
  destruct (binds_concat_inv Hb) as [?|[? Hb2]]; eauto.
  destruct (binds_single_inv Hb2); discriminate.
Qed.

Lemma binds_typ_middle_bind_knds_inv : forall x M E F Xs Ks,
  binds x (bind_typ M) (E & bind_knds Xs Ks & F) ->
  binds x (bind_typ M) (E & F).
Proof.
  introv Hb.
  destruct (binds_concat_inv Hb) as [?|[? Hb2]]; auto.
  destruct (binds_concat_inv Hb2) as [Hb3|[Hn ?]]; auto.
  exfalso; eauto using binds_typ_bind_knds_inv.
Qed.

Lemma environment_knd_weakening : forall E F G X K,
    X # F ->
    environment (E & G & X ~:: K) ->
    environment (E & F & G) ->
    environment (E & F & G & X ~:: K).
Proof.
  introv Hin He1 He2.
  destruct (environment_knd_inv He1) as [? [? ?]].
  auto.
Qed.

Lemma environment_typ_weakening : forall E F G x M,
    x # F ->
    environment (E & G & x ~: M) ->
    environment (E & F & G) ->
    environment (E & F & G & x ~: M).
Proof.
  introv Hin He1 He2.
  destruct (environment_typ_inv He1) as [? [? ?]].
  auto.
Qed.

Lemma environment_bind_knds_weakening : forall E F G Xs Ks,
    fresh (dom F) (length Ks) Xs ->
    environment (E & G & bind_knds Xs Ks) ->
    environment (E & F & G) ->
    environment (E & F & G & bind_knds Xs Ks).
Proof.
  introv Hf He1 He2.
  fresh_length Hf as Hl.
  destruct (@environment_bind_knds_inv _ _ _ He1)as [? [? ?]]; auto.
  apply environment_bind_knds; auto.
  autorewrite with rew_env_dom in *.
  auto.
Qed.
 
Lemma environment_kinds_weakening : forall E F G Xs M,
    fresh (dom F) (sch_arity M) Xs ->
    environment (E & G & Xs ~::* M) ->
    environment (E & F & G) ->
    environment (E & F & G & Xs ~::* M).
Proof.
  introv Hf He1 He2.
  destruct M as [Ks ?].
  unfold bind_sch_kinds in *.
  simpl in *.
  apply environment_bind_knds_weakening; auto.
  rewrite <- length_knd_open_vars_list.
  assumption.
Qed.

Lemma env_subst_environment : forall Xs Us E,
    types Us -> environment E ->
    environment (env_subst Xs Us E).
Proof.
  introv Ht He.
  induction He; autorewrite with rew_env_subst; auto.
  - apply environment_knd; auto.
    + rewrite knd_subst_kind; auto.
    + autorewrite with rew_env_dom.
      assumption.
  - apply environment_typ; auto.
    + rewrite sch_subst_type; auto.
    + autorewrite with rew_env_dom.
      assumption.
Qed.

Lemma scheme_from_env : forall E x M,
    environment E ->
    binds x (bind_typ M) E ->
    scheme M.
Proof.
  introv He Hb.
  induction He.
  - apply binds_empty_inv in Hb; contradiction.
  - destruct (binds_push_inv Hb) as [[Hx Hbnd]|[Hx Hbnd]];
      try discriminate; auto.
  - destruct (binds_push_inv Hb) as [[Hx Hbnd]|[Hx Hbnd]];
      auto.
    inversion Hbnd; subst; assumption.
Qed.

Lemma kind_from_env : forall E X K,
    environment E ->
    binds X (bind_knd K) E ->
    kind K.
Proof.
  introv He Hb.
  induction He.
  - apply binds_empty_inv in Hb; contradiction.
  - destruct (binds_push_inv Hb) as [[Hx Hbnd]|[Hx Hbnd]];
      auto.
    inversion Hbnd; subst; assumption.
  - destruct (binds_push_inv Hb) as [[Hx Hbnd]|[Hx Hbnd]];
      try discriminate; auto.
Qed.

(* =============================================================== *)
(** * Properties of stores and store types *)

Lemma ok_from_store_type : forall P,
  store_type P -> ok P.
Proof.
  introv Hs.
  induction Hs; auto. 
Qed.

Lemma binds_store_type_weakening : forall P Q R X T,
    binds X T (P & R) ->
    store_type (P & Q & R) ->
    binds X T (P & Q & R).
Proof.
  introv Hb He.
  assert (ok (P & Q & R))
    by auto using ok_from_store_type.
  apply binds_weaken; assumption.
Qed.

Lemma store_type_retract : forall P Q,
    store_type (P & Q) -> store_type P.
Proof.
  introv Hs.
  induction Q using env_ind;
    autorewrite with rew_env_concat in *; auto.
  remember (P & Q & x ~ v) as R.
  destruct Hs.
  - destruct (empty_concat_inv HeqR) as [_ Hem].
    apply empty_single_inv in Hem.
    contradiction.
  - destruct (eq_push_inv HeqR) as [_ [_ Hem]].
    rewrite Hem in Hs.
    auto.
Qed.

Lemma styp_subst_store_type : forall P Zs Us,
  types Us -> store_type (styp_subst Zs Us P) <-> store_type P.
Proof.
  introv Ht.
  split.
  - introv Hs.
    induction P using env_ind; autorewrite with rew_styp_subst in Hs;
      auto.
    remember (styp_subst Zs Us P & x ~ typ_subst Zs Us v) as Q.
    destruct Hs.
    + apply empty_push_inv in HeqQ; contradiction.
    + apply eq_push_inv in HeqQ as [A [B C]]; subst.
      apply store_type_push;
        try rewrite typ_subst_type in *;
        autorewrite with rew_styp_dom in *; auto.
  - introv Hs.
    induction Hs; autorewrite with rew_styp_subst; auto.
    apply store_type_push; auto.
    + rewrite typ_subst_type; assumption.
    + autorewrite with rew_styp_dom; assumption.
Qed.

Lemma type_from_store_type : forall P l T,
    store_type P ->
    binds l T P ->
    type T.
Proof.
  introv Hs Hb.
  induction Hs.
  - apply binds_empty_inv in Hb; contradiction.
  - destruct (binds_push_inv Hb) as [[Hl Hbnd]|[Hl Hbnd]];
      subst; auto.
Qed.

Lemma value_from_store : forall V l t,
    store V ->
    binds l t V ->
    value t.
Proof.
  introv Hs Hb.
  induction Hs.
  - apply binds_empty_inv in Hb; contradiction.
  - destruct (binds_push_inv Hb) as [[Hl Hbnd]|[Hl Hbnd]];
      subst; auto.
Qed.

(* =============================================================== *)
(** * Regularity of judgments *)

Inductive valid_kind_regular : bool -> env -> knd -> Prop :=
  | valid_kind_regular_type : forall chk E,
      valid_env_regular chk E ->
      environment E ->
      valid_kind_regular chk E knd_type
  | valid_kind_regular_row :  forall chk E cs,
      valid_env_regular chk E ->
      CSet.Nonempty cs ->
      environment E ->
      valid_kind_regular chk E (knd_row cs)
  | valid_kind_regular_range : forall chk E T1 T2,
      subtype_regular chk E T2 T1 CSet.universe ->
      environment E ->
      type T1 ->
      type T2 ->
      valid_kind_regular chk E (knd_range T1 T2)

with kinding_regular : bool -> env -> typ -> knd -> Prop :=
  | kinding_regular_var : forall chk E X K,
      valid_env_regular chk E ->
      binds X (bind_knd K) E ->
      environment E ->
      kind K ->
      kinding_regular chk E (typ_fvar X) K
  | kinding_regular_constructor : forall chk E c T cs,
      kinding_regular chk E T knd_type ->
      cs = CSet.singleton c ->
      environment E ->
      type T ->
      kinding_regular chk E (typ_constructor c T) (knd_row cs)
  | kinding_regular_or : forall chk E T1 T2 cs1 cs2 cs12,
      kinding_regular chk E T1 (knd_row cs1) ->
      kinding_regular chk E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      kinding_regular chk E (typ_or cs1 T1 cs2 T2) (knd_row cs12)
  | kinding_regular_proj : forall chk E T cs cs',
      kinding_regular chk E T (knd_row cs) ->
      CSet.Subset cs' cs ->
      CSet.Nonempty cs' ->
      environment E ->
      type T ->
      CSet.Nonempty cs ->
      kinding_regular chk E (typ_proj cs T cs') (knd_row cs')
  | kinding_regular_variant : forall chk E T,
      kinding_regular chk E T
        (knd_range (typ_top CSet.universe) (typ_bot CSet.universe)) ->
      environment E ->
      type T ->
      kinding_regular chk E (typ_variant T) knd_type
  | kinding_regular_arrow : forall chk E T1 T2,
      kinding_regular chk E T1 knd_type -> 
      kinding_regular chk E T2 knd_type -> 
      environment E ->
      type T1 ->
      type T2 ->
      kinding_regular chk E (typ_arrow T1 T2) knd_type
  | kinding_regular_ref : forall chk E T,
      kinding_regular chk E T knd_type ->
      environment E ->
      type T ->
      kinding_regular chk E (typ_ref T) knd_type
  | kinding_regular_unit : forall chk E,
      valid_env_regular chk E ->
      environment E ->
      kinding_regular chk E typ_unit knd_type
  | kinding_regular_prod : forall chk E T1 T2,
      kinding_regular chk E T1 knd_type -> 
      kinding_regular chk E T2 knd_type -> 
      environment E ->
      type T1 ->
      type T2 ->
      kinding_regular chk E (typ_prod T1 T2) knd_type
  | kinding_regular_top : forall chk E cs,
      valid_env_regular chk E ->
      CSet.Nonempty cs ->
      environment E ->
      kinding_regular chk E (typ_top cs) (knd_row cs)
  | kinding_regular_bot : forall chk E cs,
      valid_env_regular chk E ->
      CSet.Nonempty cs ->
      environment E ->
      kinding_regular chk E (typ_bot cs) (knd_row cs)
  | kinding_regular_meet : forall chk E T1 T2 cs,
      kinding_regular chk E T1 (knd_row cs) ->
      kinding_regular chk E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      kinding_regular chk E (typ_meet T1 T2) (knd_row cs)
  | kinding_regular_join : forall chk E T1 T2 cs,
      kinding_regular chk E T1 (knd_row cs) ->
      kinding_regular chk E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      kinding_regular chk E (typ_join T1 T2) (knd_row cs)
  | kinding_regular_range_subsumption : forall chk E T T1 T2 T1' T2',
      kinding_regular chk E T (knd_range T1 T2) ->
      subtype_regular chk E T1 T1' CSet.universe ->
      subtype_regular chk E T2' T2 CSet.universe ->
      environment E ->
      type T ->
      type T1 ->
      type T2 ->
      type T1' ->
      type T2' ->
      kinding_regular chk E T (knd_range T1' T2')

with valid_kinds_regular : bool -> env -> list knd -> Prop :=
  | valid_kinds_regular_nil : forall chk E,
      valid_env_regular chk E ->
      environment E ->
      valid_kinds_regular chk E nil
  | valid_kinds_regular_cons : forall chk E K Ks,
      valid_kind_regular chk E K ->
      valid_kinds_regular chk E Ks ->
      environment E ->
      kind K ->
      kinds Ks ->
      valid_kinds_regular chk E (K :: Ks)

with valid_kinds_and_type_regular
     : bool -> env -> list knd -> typ -> Prop :=
  | valid_kinds_and_type_regular_c : forall chk E Ks T,
      valid_kinds_regular chk E Ks ->
      kinding_regular chk E T knd_type ->
      environment E ->
      kinds Ks ->
      type T ->
      valid_kinds_and_type_regular chk E Ks T

with valid_scheme_regular : bool -> env -> sch -> Prop :=
  | valid_scheme_regular_c : forall L chk E M,
      valid_env_regular chk E ->
      (forall Xs,
          fresh L (sch_arity M) Xs ->
          valid_kinds_and_type_regular chk (E & Xs ~::* M)
            (knd_open_vars_list (sch_kinds M) Xs)
            (typ_open_vars (sch_body M) Xs)) ->
      environment E ->
      scheme M ->
      valid_scheme_regular chk E M

with valid_env_aux_regular : env -> env -> Prop :=
  | valid_env_aux_regular_empty : forall E,
      environment E ->
      valid_env_aux_regular E empty
  | valid_env_aux_regular_kind : forall E F X K,
      valid_env_aux_regular E F ->
      valid_kind_regular false E K ->
      X # F ->
      environment E ->
      environment F ->
      environment (F & X ~:: K) ->
      kind K ->
      valid_env_aux_regular E (F & X ~:: K)
  | valid_env_aux_regular_type : forall E F x M,
      valid_env_aux_regular E F ->
      valid_scheme_regular false E M ->
      x # F ->
      environment E ->
      environment F ->
      environment (F & x ~: M) ->
      scheme M ->
      valid_env_aux_regular E (F & x ~: M)

with valid_env_regular : bool -> env -> Prop :=
  | valid_env_regular_check : forall E,
      valid_env_aux_regular E E ->
      environment E ->
      valid_env_regular true E
  | valid_env_regular_no_check : forall E,
      environment E ->
      valid_env_regular false E

with type_equal_core_regular
     : bool -> env -> typ -> typ -> knd -> Prop :=
  | type_equal_core_regular_or_commutative :
      forall chk E T1 T2 cs1 cs2 cs12,
      kinding_regular chk E T1 (knd_row cs1) ->
      kinding_regular chk E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      type_equal_core_regular chk E
        (typ_or cs1 T1 cs2 T2) (typ_or cs2 T2 cs1 T1) (knd_row cs12)
  | type_equal_core_regular_or_associative :
      forall chk E T1 cs1 T2 cs2 T3 cs3 cs12 cs23 cs123,
      kinding_regular chk E T1 (knd_row cs1) ->
      kinding_regular chk E T2 (knd_row cs2) ->
      kinding_regular chk E T3 (knd_row cs3) ->
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
      type_equal_core_regular chk E
        (typ_or cs1 T1 cs23 (typ_or cs2 T2 cs3 T3))
        (typ_or cs12 (typ_or cs1 T1 cs2 T2) cs3 T3)
        (knd_row cs123)
  | type_equal_core_regular_or_bot : forall chk E cs1 cs2 cs12,
      valid_env_regular chk E ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type_equal_core_regular chk E
        (typ_or cs1 (typ_bot cs1) cs2 (typ_bot cs2)) (typ_bot cs12)
        (knd_row cs12)
  | type_equal_core_regular_or_top : forall chk E cs1 cs2 cs12,
      valid_env_regular chk E ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type_equal_core_regular chk E
        (typ_or cs1 (typ_top cs1) cs2 (typ_top cs2)) (typ_top cs12)
        (knd_row cs12)
  | type_equal_core_regular_or_meet_distribution :
      forall chk E T1 T2 T3 T4 cs1 cs2 cs12,
      kinding_regular chk E T1 (knd_row cs1) ->
      kinding_regular chk E T2 (knd_row cs2) ->
      kinding_regular chk E T3 (knd_row cs1) ->
      kinding_regular chk E T4 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      type T4 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      type_equal_core_regular chk E
        (typ_or cs1 (typ_meet T1 T3) cs2 (typ_meet T2 T4))
        (typ_meet (typ_or cs1 T1 cs2 T2) (typ_or cs1 T3 cs2 T4))
        (knd_row cs12)
  | type_equal_core_regular_or_join_distribution :
      forall chk E T1 T2 T3 T4 cs1 cs2 cs12,
      kinding_regular chk E T1 (knd_row cs1) ->
      kinding_regular chk E T2 (knd_row cs2) ->
      kinding_regular chk E T3 (knd_row cs1) ->
      kinding_regular chk E T4 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      type T4 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      type_equal_core_regular chk E
        (typ_or cs1 (typ_join T1 T3) cs2 (typ_join T2 T4))
        (typ_join (typ_or cs1 T1 cs2 T2) (typ_or cs1 T3 cs2 T4))
        (knd_row cs12)
  | type_equal_core_regular_or_proj : forall chk E T cs1 cs2 cs3 cs23,
      kinding_regular chk E T (knd_row cs1) ->
      CSet.Disjoint cs2 cs3 ->
      CSet.Subset cs2 cs1 ->
      CSet.Nonempty cs2 ->
      CSet.Subset cs3 cs1 ->
      CSet.Nonempty cs3 ->
      cs23 = CSet.union cs2 cs3 ->
      environment E ->
      type T ->
      CSet.Nonempty cs1 ->
      type_equal_core_regular chk E
        (typ_or cs2 (typ_proj cs1 T cs2) cs3 (typ_proj cs1 T cs3))
        (typ_proj cs1 T cs23)
        (knd_row cs23)
  | type_equal_core_regular_proj_id : forall chk E T cs,
      kinding_regular chk E T (knd_row cs) ->
      environment E ->
      type T ->
      CSet.Nonempty cs ->
      type_equal_core_regular chk E (typ_proj cs T cs) T (knd_row cs)
  | type_equal_core_regular_proj_compose : forall chk E T cs1 cs2 cs3,
      kinding_regular chk E T (knd_row cs1) ->
      CSet.Subset cs2 cs1 ->
      CSet.Subset cs3 cs2 ->
      CSet.Nonempty cs3 ->
      environment E ->
      type T ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      type_equal_core_regular chk E
        (typ_proj cs2 (typ_proj cs1 T cs2) cs3)
        (typ_proj cs1 T cs3)
        (knd_row cs3)
  | type_equal_core_regular_proj_or_l :
      forall chk E T1 T2 cs1 cs1' cs2 cs12,
      kinding_regular chk E T1 (knd_row cs1) ->
      kinding_regular chk E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      CSet.Subset cs1' cs1 ->
      CSet.Nonempty cs1' ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      type_equal_core_regular chk E
        (typ_proj cs12 (typ_or cs1 T1 cs2 T2) cs1')
        (typ_proj cs1 T1 cs1')
        (knd_row cs1')
  | type_equal_core_regular_proj_or_r :
      forall chk E T1 T2 cs1 cs2 cs2' cs12,
      kinding_regular chk E T1 (knd_row cs1) ->
      kinding_regular chk E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      CSet.Subset cs2' cs2 ->
      CSet.Nonempty cs2' ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      type_equal_core_regular chk E
        (typ_proj cs12 (typ_or cs1 T1 cs2 T2) cs2')
        (typ_proj cs2 T2 cs2')
        (knd_row cs2')
  | type_equal_core_regular_proj_or_both :
      forall chk E T1 T2 cs1 cs2 cs1' cs2' cs12 cs12',
      kinding_regular chk E T1 (knd_row cs1) ->
      kinding_regular chk E T2 (knd_row cs2) ->
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
      type_equal_core_regular chk E
        (typ_proj cs12 (typ_or cs1 T1 cs2 T2) cs12')
        (typ_or cs1' (typ_proj cs1 T1 cs1')
                cs2' (typ_proj cs2 T2 cs2'))
        (knd_row cs12')
  | type_equal_core_regular_proj_meet : forall chk E T1 T2 cs cs',
      kinding_regular chk E T1 (knd_row cs) ->
      kinding_regular chk E T2 (knd_row cs) ->
      CSet.Subset cs' cs ->
      CSet.Nonempty cs' ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      type_equal_core_regular chk E
        (typ_proj cs (typ_meet T1 T2) cs')
        (typ_meet (typ_proj cs T1 cs') (typ_proj cs T2 cs'))
        (knd_row cs')
  | type_equal_core_regular_proj_join : forall chk E T1 T2 cs cs',
      kinding_regular chk E T1 (knd_row cs) ->
      kinding_regular chk E T2 (knd_row cs) ->
      CSet.Subset cs' cs ->
      CSet.Nonempty cs' ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      type_equal_core_regular chk E
        (typ_proj cs (typ_join T1 T2) cs')
        (typ_join (typ_proj cs T1 cs') (typ_proj cs T2 cs'))
        (knd_row cs')
  | type_equal_core_regular_meet_commutative : forall chk E T1 T2 cs,
      kinding_regular chk E T1 (knd_row cs) ->
      kinding_regular chk E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      type_equal_core_regular chk E
        (typ_meet T1 T2) (typ_meet T2 T1) (knd_row cs)
  | type_equal_core_regular_meet_associative :
      forall chk E T1 T2 T3 cs,
      kinding_regular chk E T1 (knd_row cs) ->
      kinding_regular chk E T2 (knd_row cs) ->
      kinding_regular chk E T3 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      CSet.Nonempty cs ->
      type_equal_core_regular chk E
        (typ_meet T1 (typ_meet T2 T3))
        (typ_meet (typ_meet T1 T2) T3)
        (knd_row cs)
  | type_equal_core_regular_meet_identity : forall chk E T1 cs,
      kinding_regular chk E T1 (knd_row cs) ->
      environment E ->
      type T1 ->
      CSet.Nonempty cs ->
      type_equal_core_regular chk E
        (typ_meet T1 (typ_top cs)) T1 (knd_row cs)
  | type_equal_core_regular_meet_absorption : forall chk E T1 T2 cs,
      kinding_regular chk E T1 (knd_row cs) ->
      kinding_regular chk E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      type_equal_core_regular chk E
        (typ_meet T1 (typ_join T1 T2)) T1 (knd_row cs)
  | type_equal_core_regular_meet_distribution :
      forall chk E T1 T2 T3 cs,
      kinding_regular chk E T1 (knd_row cs) ->
      kinding_regular chk E T2 (knd_row cs) ->
      kinding_regular chk E T3 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      CSet.Nonempty cs ->
      type_equal_core_regular chk E
        (typ_meet T1 (typ_join T2 T3))
        (typ_join (typ_meet T1 T2) (typ_meet T1 T3))
        (knd_row cs)
  | type_equal_core_regular_join_commutative : forall chk E T1 T2 cs,
      kinding_regular chk E T1 (knd_row cs) ->
      kinding_regular chk E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      type_equal_core_regular chk E
        (typ_join T1 T2) (typ_join T2 T1) (knd_row cs)
  | type_equal_core_regular_join_associative :
      forall chk E T1 T2 T3 cs,
      kinding_regular chk E T1 (knd_row cs) ->
      kinding_regular chk E T2 (knd_row cs) ->
      kinding_regular chk E T3 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      CSet.Nonempty cs ->
      type_equal_core_regular chk E
        (typ_join T1 (typ_join T2 T3))
        (typ_join (typ_join T1 T2) T3)
        (knd_row cs)
  | type_equal_core_regular_join_identity : forall chk E T1 cs,
      kinding_regular chk E T1 (knd_row cs) ->
      environment E ->
      type T1 ->
      CSet.Nonempty cs ->
      type_equal_core_regular chk E
        (typ_join T1 (typ_bot cs)) T1 (knd_row cs)
  | type_equal_core_regular_join_absorption : forall chk E T1 T2 cs,
      kinding_regular chk E T1 (knd_row cs) ->
      kinding_regular chk E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      type_equal_core_regular chk E
        (typ_join T1 (typ_meet T1 T2)) T1 (knd_row cs)
  | type_equal_core_regular_join_distribution :
      forall chk E T1 T2 T3 cs,
      kinding_regular chk E T1 (knd_row cs) ->
      kinding_regular chk E T2 (knd_row cs) ->
      kinding_regular chk E T3 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      CSet.Nonempty cs ->
      type_equal_core_regular chk E
        (typ_join T1 (typ_meet T2 T3))
        (typ_meet (typ_join T1 T2) (typ_join T1 T3))
        (knd_row cs)

with type_equal_symm_regular
     : bool -> env -> typ -> typ -> knd -> Prop :=
  | type_equal_symm_regular_l : forall chk E T1 T2 K,
      type_equal_core_regular chk E T1 T2 K ->
      environment E ->
      type T1 ->
      type T2 ->
      kind K ->
      type_equal_symm_regular chk E T1 T2 K
  | type_equal_symm_regular_r : forall chk E T1 T2 K,
      type_equal_core_regular chk E T1 T2 K ->
      environment E ->
      type T1 ->
      type T2 ->
      kind K ->
      type_equal_symm_regular chk E T2 T1 K

with type_equal_cong_regular
     : bool -> env -> typ -> typ -> knd -> Prop :=
  | type_equal_cong_regular_constructor : forall chk E c T1 T1' cs,
      type_equal_cong_regular chk E T1 T1' knd_type ->
      cs = CSet.singleton c ->
      environment E ->
      type T1 ->
      type T1' ->
      type_equal_cong_regular chk E
        (typ_constructor c T1) (typ_constructor c T1')
        (knd_row cs)
  | type_equal_cong_regular_or_l :
      forall chk E T1 T1' T2 cs1 cs2 cs12,
      kinding_regular chk E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_cong_regular chk E T1 T1' (knd_row cs1) ->
      environment E ->
      type T1 ->
      type T1' ->
      type T2 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      type_equal_cong_regular chk E
        (typ_or cs1 T1 cs2 T2) (typ_or cs1 T1' cs2 T2) (knd_row cs12)
  | type_equal_cong_regular_or_r :
      forall chk E T1 T2 T2' cs1 cs2 cs12,
      kinding_regular chk E T1 (knd_row cs1) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_cong_regular chk E T2 T2' (knd_row cs2) ->
      environment E ->
      type T1 ->
      type T2 ->
      type T2' ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      type_equal_cong_regular chk E
        (typ_or cs1 T1 cs2 T2) (typ_or cs1 T1 cs2 T2') (knd_row cs12)
  | type_equal_cong_regular_proj : forall chk E T1 T1' cs1 cs2,
      CSet.Subset cs2 cs1 ->
      CSet.Nonempty cs2 ->
      type_equal_cong_regular chk E T1 T1' (knd_row cs1) ->
      environment E ->
      type T1 ->
      type T1' ->
      CSet.Nonempty cs1 ->
      type_equal_cong_regular chk E
        (typ_proj cs1 T1 cs2) (typ_proj cs1 T1' cs2) (knd_row cs2)
  | type_equal_cong_regular_arrow_l : forall chk E T1 T1' T2,
      kinding_regular chk E T2 knd_type ->
      type_equal_cong_regular chk E T1 T1' knd_type ->
      environment E ->
      type T1 ->
      type T1' ->
      type T2 ->
      type_equal_cong_regular chk E
        (typ_arrow T1 T2) (typ_arrow T1' T2) knd_type
  | type_equal_cong_regular_arrow_r : forall chk E T1 T2 T2',
      kinding_regular chk E T1 knd_type ->
      type_equal_cong_regular chk E T2 T2' knd_type ->
      environment E ->
      type T1 ->
      type T2 ->
      type T2' ->
      type_equal_cong_regular chk E
        (typ_arrow T1 T2) (typ_arrow T1 T2') knd_type
  | type_equal_cong_regular_prod_l : forall chk E T1 T1' T2,
      kinding_regular chk E T2 knd_type ->
      type_equal_cong_regular chk E T1 T1' knd_type ->
      environment E ->
      type T1 ->
      type T1' ->
      type T2 ->
      type_equal_cong_regular chk E
        (typ_prod T1 T2) (typ_prod T1' T2) knd_type
  | type_equal_cong_regular_prod_r : forall chk E T1 T2 T2',
      kinding_regular chk E T1 knd_type ->
      type_equal_cong_regular chk E T2 T2' knd_type ->
      environment E ->
      type T1 ->
      type T2 ->
      type T2' ->
      type_equal_cong_regular chk E
        (typ_prod T1 T2) (typ_prod T1 T2') knd_type
  | type_equal_cong_regular_ref : forall chk E T1 T1',
      type_equal_cong_regular chk E T1 T1' knd_type ->
      environment E ->
      type T1 ->
      type T1' ->
      type_equal_cong_regular chk E
        (typ_ref T1) (typ_ref T1') knd_type
  | type_equal_cong_regular_meet_l : forall chk E T1 T1' T2 cs,
      kinding_regular chk E T2 (knd_row cs) ->
      type_equal_cong_regular chk E T1 T1' (knd_row cs) ->
      environment E ->
      type T1 ->
      type T1' ->
      type T2 ->
      CSet.Nonempty cs ->
      type_equal_cong_regular chk E
        (typ_meet T1 T2) (typ_meet T1' T2) (knd_row cs)
  | type_equal_cong_regular_meet_r : forall chk E T1 T2 T2' cs,
      kinding_regular chk E T1 (knd_row cs) ->
      type_equal_cong_regular chk E T2 T2' (knd_row cs) -> 
      environment E ->
      type T1 ->
      type T2 ->
      type T2' ->
      CSet.Nonempty cs ->
      type_equal_cong_regular chk E
        (typ_meet T1 T2) (typ_meet T1 T2') (knd_row cs)
  | type_equal_cong_regular_join_l : forall chk E T1 T1' T2 cs,
      kinding_regular chk E T2 (knd_row cs) ->
      type_equal_cong_regular chk E T1 T1' (knd_row cs) ->
      environment E ->
      type T1 ->
      type T1' ->
      type T2 ->
      CSet.Nonempty cs ->
      type_equal_cong_regular chk E
        (typ_join T1 T2) (typ_join T1' T2) (knd_row cs)
  | type_equal_cong_regular_join_r : forall chk E T1 T2 T2' cs,
      kinding_regular chk E T1 (knd_row cs) ->
      type_equal_cong_regular chk E T2 T2' (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      type T2' ->
      CSet.Nonempty cs ->
      type_equal_cong_regular chk E
        (typ_join T1 T2) (typ_join T1 T2') (knd_row cs)
  | type_equal_cong_regular_symm : forall chk E T1 T1' K,
      type_equal_symm_regular chk E T1 T1' K ->
      environment E ->
      type T1 ->
      type T1' ->
      kind K ->
      type_equal_cong_regular chk E T1 T1' K

with type_equal_regular : bool -> env -> typ -> typ -> knd -> Prop :=
  | type_equal_regular_refl : forall chk E T K,
      kinding_regular chk E T K ->
      environment E ->
      type T ->
      kind K ->
      type_equal_regular chk E T T K
  | type_equal_regular_step : forall chk E T1 T2 T3 K,
      type_equal_cong_regular chk E T1 T2 K ->
      type_equal_regular chk E T2 T3 K ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      kind K ->
      type_equal_regular chk E T1 T3 K

with subtype_regular : bool -> env -> typ -> typ -> cset -> Prop :=
  | subtype_regular_c : forall chk E T1 T2 cs,
      type_equal_regular chk E T1 (typ_meet T1 T2) (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      subtype_regular chk E T1 T2 cs.

Scheme valid_kind_regular_mutind :=
         Induction for valid_kind_regular Sort Prop
  with kinding_regular_mutind :=
         Induction for kinding_regular Sort Prop
  with valid_kinds_regular_mutind :=
         Induction for valid_kinds_regular Sort Prop
  with valid_kinds_and_type_regular_mutind :=
         Induction for valid_kinds_and_type_regular Sort Prop
  with valid_scheme_regular_mutind :=
         Induction for valid_scheme_regular Sort Prop
  with valid_env_aux_regular_mutind :=
         Induction for valid_env_aux_regular Sort Prop
  with valid_env_regular_mutind :=
         Induction for valid_env_regular Sort Prop
  with type_equal_core_regular_mutind :=
         Induction for type_equal_core_regular Sort Prop
  with type_equal_symm_regular_mutind :=
         Induction for type_equal_symm_regular Sort Prop
  with type_equal_cong_regular_mutind :=
         Induction for type_equal_cong_regular Sort Prop
  with type_equal_regular_mutind :=
         Induction for type_equal_regular Sort Prop
  with subtype_regular_mutind :=
         Induction for subtype_regular Sort Prop.

Combined Scheme combined_kinding_regular_mutind
  from valid_kind_regular_mutind, kinding_regular_mutind,
       valid_kinds_regular_mutind,
       valid_kinds_and_type_regular_mutind,
       valid_scheme_regular_mutind,
       valid_env_aux_regular_mutind, valid_env_regular_mutind,
       type_equal_core_regular_mutind,
       type_equal_symm_regular_mutind, type_equal_cong_regular_mutind,
       type_equal_regular_mutind, subtype_regular_mutind.

Lemma valid_kind_regular_inv : forall chk E K,
    valid_kind_regular chk E K ->
    environment E /\ kind K.
Proof.
  introv Hv.
  destruct Hv; auto.
Qed.

Hint Constructors valid_kind_regular : valid_kind_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_kind_regular _ E _ |- _ =>
      apply (proj1 (valid_kind_regular_inv H))
  end : valid_kind_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : valid_kind_regular _ _ K |- _ =>
      apply (proj2 (valid_kind_regular_inv H))
  end : valid_kind_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : valid_kind_regular _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj2 (valid_kind_regular_inv H));
      inversion Hknd; assumption
  end : valid_kind_regular.

Lemma kinding_regular_inv : forall chk E T K,
    kinding_regular chk E T K ->
    environment E /\ type T /\ kind K.
Proof.
  introv Hk.
  destruct Hk; auto with csetdec.
Qed.

Hint Constructors kinding_regular : kinding_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : kinding_regular _ E _ _ |- _ =>
      apply (proj31 (kinding_regular_inv H))
  end : kinding_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : kinding_regular _ _ T _ |- _ =>
      apply (proj32 (kinding_regular_inv H))
  end : kinding_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : kinding_regular _ _ _ K |- _ =>
      apply (proj33 (kinding_regular_inv H))
  end : kinding_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : kinding_regular _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj33 (kinding_regular_inv H));
      inversion Hknd; assumption
  end : kinding_regular.

Lemma valid_kinds_regular_inv : forall chk E Ks,
    valid_kinds_regular chk E Ks ->
    environment E /\ kinds Ks.
Proof.
  introv Hks.
  destruct Hks; auto.  
Qed.

Hint Constructors valid_kinds_regular : valid_kinds_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_kinds_regular _ E _ |- _ =>
      apply (proj1 (valid_kinds_regular_inv H))
  end : valid_kinds_regular.

Hint Extern 1 (kinds ?Ks) =>
  match goal with
  | H : valid_kinds_regular _ _ Ks |- _ =>
      apply (proj2 (valid_kinds_regular_inv H))
  end : valid_kinds_regular.

Lemma valid_kinds_and_type_regular_inv : forall chk E Ks T,
    valid_kinds_and_type_regular chk E Ks T ->
    environment E /\ kinds Ks /\ type T.
Proof.
  introv Hkt.
  destruct Hkt; auto.
Qed.

Hint Constructors valid_kinds_and_type_regular
  : valid_kinds_and_type_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_kinds_and_type_regular _ E _ _ |- _ =>
      apply (proj31 (valid_kinds_and_type_regular_inv H))
  end : valid_kinds_and_type_regular.

Hint Extern 1 (kinds ?Ks) =>
  match goal with
  | H : valid_kinds_and_type_regular _ _ Ks _ |- _ =>
      apply (proj32 (valid_kinds_and_type_regular_inv H))
  end : valid_kinds_and_type_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : valid_kinds_and_type_regular _ _ _ T |- _ =>
      apply (proj33 (valid_kinds_and_type_regular_inv H))
  end : valid_kinds_and_type_regular.

Lemma valid_scheme_regular_inv : forall chk E M,
    valid_scheme_regular chk E M ->
    environment E /\ scheme M.
Proof.
  introv Hs.
  destruct Hs; auto.
Qed.

Hint Constructors valid_scheme_regular : valid_scheme_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_scheme_regular _ E _ |- _ =>
      apply (proj1 (valid_scheme_regular_inv H))
  end : valid_scheme_regular.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H : valid_scheme_regular _ _ M |- _ =>
      apply (proj2 (valid_scheme_regular_inv H))
  end : valid_scheme_regular.

Lemma valid_env_aux_regular_inv : forall E F,
    valid_env_aux_regular E F ->
    environment E /\ environment F.
Proof.
  introv He.
  destruct He; auto.
Qed.

Hint Constructors valid_env_aux_regular : valid_env_aux_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_env_aux_regular E _ |- _ =>
      apply (proj1 (valid_env_aux_regular_inv H))
  | H : valid_env_aux_regular _ E |- _ =>
      apply (proj2 (valid_env_aux_regular_inv H))
  end : valid_env_aux_regular.

Lemma valid_env_regular_inv : forall chk E,
    valid_env_regular chk E -> environment E.
Proof.
  introv He.
  destruct He; auto.
Qed.

Hint Constructors valid_env_regular : valid_env_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_env_regular _ E |- _ =>
      apply (valid_env_regular_inv H)
  end : valid_env_regular.

Lemma type_equal_core_regular_inv : forall chk E T1 T2 K,
    type_equal_core_regular chk E T1 T2 K ->
    environment E /\ type T1 /\ type T2 /\ kind K.
Proof.
  introv Hte.
  destruct Hte; subst; split; auto with csetdec.
Qed.

Hint Constructors type_equal_core_regular : type_equal_core_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_core_regular _ E _ _ _ |- _ =>
      apply (proj41 (type_equal_core_regular_inv H))
  end : type_equal_core_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_core_regular _ _ T _ _ |- _ =>
      apply (proj42 (type_equal_core_regular_inv H))
  | H : type_equal_core_regular _ _ _ T _ |- _ =>
      apply (proj43 (type_equal_core_regular_inv H))
  end : type_equal_core_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_core_regular _ _ _ _ K |- _ =>
      apply (proj44 (type_equal_core_regular_inv H))
  end : type_equal_core_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_core_regular _ _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_core_regular_inv H));
      inversion Hknd; assumption
  end : type_equal_core_regular.

Lemma type_equal_symm_regular_inv : forall chk E T1 T2 K,
    type_equal_symm_regular chk E T1 T2 K ->
    environment E /\ type T1 /\ type T2 /\ kind K.
Proof.
  introv Hte.
  destruct Hte; auto.
Qed.

Hint Constructors type_equal_symm_regular : type_equal_symm_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_symm_regular _ E _ _ _ |- _ =>
      apply (proj41 (type_equal_symm_regular_inv H))
  end : type_equal_symm_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_symm_regular _ _ T _ _ |- _ =>
      apply (proj42 (type_equal_symm_regular_inv H))
  | H : type_equal_symm_regular _ _ _ T _ |- _ =>
      apply (proj43 (type_equal_symm_regular_inv H))
  end : type_equal_symm_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_symm_regular _ _ _ _ K |- _ =>
      apply (proj44 (type_equal_symm_regular_inv H))
  end : type_equal_symm_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_symm_regular _ _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_symm_regular_inv H));
      inversion Hknd; assumption
  end : type_equal_symm_regular.

Lemma type_equal_cong_regular_inv : forall chk E T1 T2 K,
    type_equal_cong_regular chk E T1 T2 K ->
    environment E /\ type T1 /\ type T2 /\ kind K.
Proof.
  introv Hte.
  destruct Hte; split; auto with csetdec.
Qed.

Hint Constructors type_equal_cong_regular : type_equal_cong_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_cong_regular _ E _ _ _ |- _ =>
      apply (proj41 (type_equal_cong_regular_inv H))
  end : type_equal_cong_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_cong_regular _ _ T _ _ |- _ =>
      apply (proj42 (type_equal_cong_regular_inv H))
  | H : type_equal_cong_regular _ _ _ T _ |- _ =>
      apply (proj43 (type_equal_cong_regular_inv H))
  end : type_equal_cong_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_cong_regular _ _ _ _ K |- _ =>
      apply (proj44 (type_equal_cong_regular_inv H))
  end : type_equal_cong_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_cong_regular _ _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_cong_regular_inv H));
      inversion Hknd; assumption
  end : type_equal_cong_regular.

Lemma type_equal_regular_inv : forall chk E T1 T2 K,
    type_equal_regular chk E T1 T2 K ->
    environment E /\ type T1 /\ type T2 /\ kind K.
Proof.
  introv Hk.
  destruct Hk; auto.
Qed.

Hint Constructors type_equal_regular : type_equal_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_regular _ E _ _ _ |- _ =>
      apply (proj41 (type_equal_regular_inv H))
  end : type_equal_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_regular _ _ T _ _ |- _ =>
      apply (proj42 (type_equal_regular_inv H))
  | H : type_equal_regular _ _ _ T _ |- _ =>
      apply (proj43 (type_equal_regular_inv H))
  end : type_equal_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_regular _ _ _ _ K |- _ =>
      apply (proj44 (type_equal_regular_inv H))
  end : type_equal_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_regular _ _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_regular_inv H));
      inversion Hknd; assumption
  end : type_equal_regular.

Lemma subtype_regular_inv : forall chk E T1 T2 cs,
    subtype_regular chk E T1 T2 cs ->
    environment E /\ type T1 /\ type T2 /\ CSet.Nonempty cs.
Proof.
  introv Hk.
  destruct Hk; auto.
Qed.

Hint Constructors subtype_regular : subtype_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : subtype_regular _ E _ _ _ |- _ =>
      apply (proj41 (subtype_regular_inv H))
  end : subtype_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : subtype_regular _ _ T _ _ |- _ =>
      apply (proj42 (subtype_regular_inv H))
  | H : subtype_regular _ _ _ T _ |- _ =>
      apply (proj43 (subtype_regular_inv H))
  end : subtype_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : subtype_regular _ _ _ _ cs |- _ =>
      apply (proj44 (subtype_regular_inv H))
  end : subtype_regular.

Lemma regular_combined_kinding :
  (forall chk E K, valid_kind chk E K -> valid_kind_regular chk E K)
  /\ (forall chk E T K,
       kinding chk E T K -> kinding_regular chk E T K)
  /\ (forall chk E Ks, 
       valid_kinds chk E Ks -> valid_kinds_regular chk E Ks)
  /\ (forall chk E Ks T, 
       valid_kinds_and_type chk E Ks T ->
       valid_kinds_and_type_regular chk E Ks T)
  /\ (forall chk E M,
       valid_scheme chk E M -> valid_scheme_regular chk E M)
  /\ (forall E F,
       valid_env_aux E F -> valid_env_aux_regular E F)
  /\ (forall chk E, valid_env chk E -> valid_env_regular chk E)
  /\ (forall chk E T1 T2 K,
       type_equal_core chk E T1 T2 K -> type_equal_core_regular chk E T1 T2 K)
  /\ (forall chk E T1 T2 K,
       type_equal_symm chk E T1 T2 K -> type_equal_symm_regular chk E T1 T2 K)
  /\ (forall chk E T1 T2 K,
       type_equal_cong chk E T1 T2 K -> type_equal_cong_regular chk E T1 T2 K)
  /\ (forall chk E T1 T2 K,
       type_equal chk E T1 T2 K -> type_equal_regular chk E T1 T2 K)
  /\ (forall chk E T1 T2 cs,
       subtype chk E T1 T2 cs -> subtype_regular chk E T1 T2 cs).
Proof.
  apply combined_kinding_mutind; intros; subst;
    eauto with valid_kind_regular kinding_regular
      valid_kinds_regular valid_kinds_and_type_regular
      valid_scheme_regular valid_env_aux_regular
      valid_env_regular type_equal_core_regular
      type_equal_symm_regular type_equal_cong_regular
      type_equal_regular subtype_regular.
  - assert (environment E) by auto with valid_env_regular.
    assert (kind K) by (eapply kind_from_env; eassumption).
    auto with kinding_regular.
  - apply valid_scheme_regular_c with (L := L); try assumption.
    + pick_freshes_gen L (sch_arity M) Xs.
      assert
        (valid_kinds_and_type_regular chk (E & Xs ~::* M)
           (knd_open_vars_list (sch_kinds M) Xs)
           (typ_open_vars (sch_body M) Xs)) by auto.
      eauto using environment_concat_inv_l
        with valid_kinds_and_type_regular.
    + exists L; introv Hf.
      assert
        (valid_kinds_and_type_regular chk (E & Xs ~::* M)
           (knd_open_vars_list (sch_kinds M) Xs)
           (typ_open_vars (sch_body M) Xs)) by auto.
      auto with valid_kinds_and_type_regular.
  - apply type_equal_core_regular_proj_compose;
      auto with kinding_regular csetdec.
  - assert (type (typ_meet T1 T2)) as Ht
      by auto with type_equal_regular.
    inversion Ht; subst.
    auto with subtype_regular type_equal_regular.
Qed.

Lemma unregular_combined_kinding :
  (forall chk E K, valid_kind_regular chk E K -> valid_kind chk E K)
  /\ (forall chk E T K,
         kinding_regular chk E T K -> kinding chk E T K)
  /\ (forall chk E Ks,
         valid_kinds_regular chk E Ks -> valid_kinds chk E Ks)
  /\ (forall chk E Ks T,
         valid_kinds_and_type_regular chk E Ks T ->
           valid_kinds_and_type chk E Ks T)
  /\ (forall chk E M,
         valid_scheme_regular chk E M -> valid_scheme chk E M)
  /\ (forall E F, valid_env_aux_regular E F -> valid_env_aux E F)
  /\ (forall chk E, valid_env_regular chk E -> valid_env chk E)
  /\ (forall chk E T1 T2 K,
       type_equal_core_regular chk E T1 T2 K ->
         type_equal_core chk E T1 T2 K)
  /\ (forall chk E T1 T2 K,
       type_equal_symm_regular chk E T1 T2 K ->
         type_equal_symm chk E T1 T2 K)
  /\ (forall chk E T1 T2 K,
       type_equal_cong_regular chk E T1 T2 K ->
         type_equal_cong chk E T1 T2 K)
  /\ (forall chk E T1 T2 K,
       type_equal_regular chk E T1 T2 K -> type_equal chk E T1 T2 K)
  /\ (forall chk E T1 T2 cs,
       subtype_regular chk E T1 T2 cs -> subtype chk E T1 T2 cs).
Proof.
  apply combined_kinding_regular_mutind; intros; subst; econstr auto.
Qed.

Lemma regular_valid_kind : forall chk E K,
    valid_kind chk E K -> valid_kind_regular chk E K.
Proof.
  pose regular_combined_kinding.
  tauto.
Qed.

Lemma unregular_valid_kind : forall chk E K,
    valid_kind_regular chk E K -> valid_kind chk E K.
Proof.
  pose unregular_combined_kinding.
  tauto.
Qed.

Hint Resolve unregular_valid_kind.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_kind _ E _ |- _ =>
      apply (proj1 (valid_kind_regular_inv
                      (regular_valid_kind H)))
  end : valid_kind_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : valid_kind _ _ K |- _ =>
      apply (proj2 (valid_kind_regular_inv
                      (regular_valid_kind H)))
  end : valid_kind_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : valid_kind _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj2 (valid_kind_regular_inv
                           (regular_valid_kind H)));
      inversion Hknd; assumption
  end : valid_kind_regular.

Lemma regular_kinding : forall chk E T K,
    kinding chk E T K -> kinding_regular chk E T K.
Proof.
  pose regular_combined_kinding.
  tauto.
Qed.

Lemma unregular_kinding : forall chk E T K,
    kinding_regular chk E T K -> kinding chk E T K.
Proof.
  pose unregular_combined_kinding.
  tauto.
Qed.

Hint Resolve unregular_kinding.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : kinding _ E _ _ |- _ =>
      apply (proj31 (kinding_regular_inv (regular_kinding H)))
  end : kinding_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : kinding _ _ T _ |- _ =>
      apply (proj32 (kinding_regular_inv (regular_kinding H)))
  end : kinding_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : kinding _ _ _ K |- _ =>
      apply (proj33 (kinding_regular_inv (regular_kinding H)))
  end : kinding_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : kinding _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj33 (kinding_regular_inv (regular_kinding H)));
      inversion Hknd; assumption
  end : kinding_regular.

Lemma regular_valid_kinds : forall chk E Ks,
    valid_kinds chk E Ks -> valid_kinds_regular chk E Ks.
Proof.
  pose regular_combined_kinding.
  tauto.
Qed.

Lemma unregular_valid_kinds : forall chk E Ks,
    valid_kinds_regular chk E Ks -> valid_kinds chk E Ks.
Proof.
  pose unregular_combined_kinding.
  tauto.
Qed.

Hint Resolve unregular_valid_kinds.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_kinds _ E _ |- _ =>
      apply (proj1 (valid_kinds_regular_inv
                      (regular_valid_kinds H)))
  end : valid_kinds_regular.

Hint Extern 1 (kinds ?Ks) =>
  match goal with
  | H : valid_kinds _ _ Ks |- _ =>
      apply (proj2 (valid_kinds_regular_inv
                      (regular_valid_kinds H)))
  end : valid_kinds_regular.

Lemma regular_valid_kinds_and_type : forall chk E Ks T,
    valid_kinds_and_type chk E Ks T ->
    valid_kinds_and_type_regular chk E Ks T.
Proof.
  pose regular_combined_kinding.
  tauto.
Qed.

Lemma unregular_valid_kinds_and_type : forall chk E Ks T,
    valid_kinds_and_type_regular chk E Ks T ->
    valid_kinds_and_type chk E Ks T.
Proof.
  pose unregular_combined_kinding.
  tauto.
Qed.

Hint Resolve unregular_valid_kinds_and_type.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_kinds_and_type _ E _ _ |- _ =>
      apply (proj31 (valid_kinds_and_type_regular_inv
                      (regular_valid_kinds_and_type H)))
  end : valid_kinds_and_type_regular.

Hint Extern 1 (kinds ?Ks) =>
  match goal with
  | H : valid_kinds_and_type _ _ Ks _ |- _ =>
      apply (proj32 (valid_kinds_and_type_regular_inv
                      (regular_valid_kinds_and_type H)))
  end : valid_kinds_and_type_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : valid_kinds_and_type _ _ _ T |- _ =>
      apply (proj33 (valid_kinds_and_type_regular_inv
                       (regular_valid_kinds_and_type H)))
  end : valid_kinds_and_type_regular.

Lemma regular_valid_scheme : forall chk E M,
    valid_scheme chk E M -> valid_scheme_regular chk E M.
Proof.
  pose regular_combined_kinding.
  tauto.
Qed.

Lemma unregular_valid_scheme : forall chk E M,
    valid_scheme_regular chk E M -> valid_scheme chk E M.
Proof.
  pose unregular_combined_kinding.
  tauto.
Qed.

Hint Resolve unregular_valid_scheme.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_scheme _ E _ |- _ =>
      apply (proj1 (valid_scheme_regular_inv
                      (regular_valid_scheme H)))
  end : valid_scheme_regular.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H : valid_scheme _ _ M |- _ =>
      apply (proj2 (valid_scheme_regular_inv
                      (regular_valid_scheme H)))
  end : valid_scheme_regular.

Lemma regular_valid_env_aux : forall E F,
    valid_env_aux E F -> valid_env_aux_regular E F.
Proof.
  pose regular_combined_kinding.
  tauto.
Qed.

Lemma unregular_valid_env_aux : forall E F,
    valid_env_aux_regular E F -> valid_env_aux E F.
Proof.
  pose unregular_combined_kinding.
  tauto.
Qed.

Hint Resolve unregular_valid_env_aux.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_env_aux E _ |- _ =>
      apply (proj1 (valid_env_aux_regular_inv
                      (regular_valid_env_aux H)))
  | H : valid_env_aux _ E |- _ =>
      apply (proj2 (valid_env_aux_regular_inv
                      (regular_valid_env_aux H)))
  end : valid_env_aux_regular.

Lemma regular_valid_env : forall chk E,
    valid_env chk E -> valid_env_regular chk E.
Proof.
  pose regular_combined_kinding.
  tauto.
Qed.

Lemma unregular_valid_env : forall chk E,
    valid_env_regular chk E -> valid_env chk E.
Proof.
  pose unregular_combined_kinding.
  tauto.
Qed.

Hint Resolve unregular_valid_env.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_env _ E |- _ =>
      apply (valid_env_regular_inv
               (regular_valid_env H))
  end : valid_env_regular.

Lemma regular_type_equal_core : forall chk E T1 T2 K,
    type_equal_core chk E T1 T2 K ->
    type_equal_core_regular chk E T1 T2 K.
Proof.
  pose regular_combined_kinding.
  tauto.
Qed.

Lemma unregular_type_equal_core : forall chk E T1 T2 K,
    type_equal_core_regular chk E T1 T2 K ->
    type_equal_core chk E T1 T2 K.
Proof.
  pose unregular_combined_kinding.
  tauto.
Qed.

Hint Resolve unregular_type_equal_core.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_core _ E _ _ _ |- _ =>
      apply (proj41 (type_equal_core_regular_inv
                       (regular_type_equal_core H)))
  end : type_equal_core_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_core _ _ T _ _ |- _ =>
      apply (proj42 (type_equal_core_regular_inv
                       (regular_type_equal_core H)))
  | H : type_equal_core _ _ _ T _ |- _ =>
      apply (proj43 (type_equal_core_regular_inv
                       (regular_type_equal_core H)))
  end : type_equal_core_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_core _ _ _ _ K |- _ =>
      apply (proj44 (type_equal_core_regular_inv
                       (regular_type_equal_core H)))
  end : type_equal_core_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_core _ _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_core_regular_inv
                            (regular_type_equal_core H)));
      inversion Hknd; assumption
  end : type_equal_core_regular.

Lemma regular_type_equal_symm : forall chk E T1 T2 K,
    type_equal_symm chk E T1 T2 K ->
    type_equal_symm_regular chk E T1 T2 K.
Proof.
  pose regular_combined_kinding.
  tauto.
Qed.

Lemma unregular_type_equal_symm : forall chk E T1 T2 K,
    type_equal_symm_regular chk E T1 T2 K ->
    type_equal_symm chk E T1 T2 K.
Proof.
  pose unregular_combined_kinding.
  tauto.
Qed.

Hint Resolve unregular_type_equal_symm.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_symm _ E _ _ _ |- _ =>
      apply (proj41 (type_equal_symm_regular_inv
                       (regular_type_equal_symm H)))
  end : type_equal_symm_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_symm _ _ T _ _ |- _ =>
      apply (proj42 (type_equal_symm_regular_inv
                       (regular_type_equal_symm H)))
  | H : type_equal_symm _ _ _ T _ |- _ =>
      apply (proj43 (type_equal_symm_regular_inv
                       (regular_type_equal_symm H)))
  end : type_equal_symm_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_symm _ _ _ _ K |- _ =>
      apply (proj44 (type_equal_symm_regular_inv
                       (regular_type_equal_symm H)))
  end : type_equal_symm_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_symm _ _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_symm_regular_inv
                            (regular_type_equal_symm H)));
      inversion Hknd; assumption
  end : type_equal_symm_regular.

Lemma regular_type_equal_cong : forall chk E T1 T2 K,
    type_equal_cong chk E T1 T2 K ->
    type_equal_cong_regular chk E T1 T2 K.
Proof.
  pose regular_combined_kinding.
  tauto.
Qed.

Lemma unregular_type_equal_cong : forall chk E T1 T2 K,
    type_equal_cong_regular chk E T1 T2 K ->
    type_equal_cong chk E T1 T2 K.
Proof.
  pose unregular_combined_kinding.
  tauto.
Qed.

Hint Resolve unregular_type_equal_cong.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_cong _ E _ _ _ |- _ =>
      apply (proj41 (type_equal_cong_regular_inv
                       (regular_type_equal_cong H)))
  end : type_equal_cong_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_cong _ _ T _ _ |- _ =>
      apply (proj42 (type_equal_cong_regular_inv
                       (regular_type_equal_cong H)))
  | H : type_equal_cong _ _ _ T _ |- _ =>
      apply (proj43 (type_equal_cong_regular_inv
                       (regular_type_equal_cong H)))
  end : type_equal_cong_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_cong _ _ _ _ K |- _ =>
      apply (proj44 (type_equal_cong_regular_inv
                       (regular_type_equal_cong H)))
  end : type_equal_cong_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_cong _ _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_cong_regular_inv
                            (regular_type_equal_cong H)));
      inversion Hknd; assumption
  end : type_equal_cong_regular.

Lemma regular_type_equal : forall chk E T1 T2 K,
    type_equal chk E T1 T2 K -> type_equal_regular chk E T1 T2 K.
Proof.
  pose regular_combined_kinding.
  tauto.
Qed.

Lemma unregular_type_equal : forall chk E T1 T2 K,
    type_equal_regular chk E T1 T2 K -> type_equal chk E T1 T2 K.
Proof.
  pose unregular_combined_kinding.
  tauto.
Qed.

Hint Resolve unregular_type_equal.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal _ E _ _ _ |- _ =>
      apply (proj41 (type_equal_regular_inv
                       (regular_type_equal H)))
  end : type_equal_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal _ _ T _ _ |- _ =>
      apply (proj42 (type_equal_regular_inv
                       (regular_type_equal H)))
  | H : type_equal _ _ _ T _ |- _ =>
      apply (proj43 (type_equal_regular_inv
                       (regular_type_equal H)))
  end : type_equal_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal _ _ _ _ K |- _ =>
      apply (proj44 (type_equal_regular_inv
                       (regular_type_equal H)))
  end : type_equal_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal _ _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_regular_inv
                            (regular_type_equal H)));
      inversion Hknd; assumption
  end : type_equal_regular.

Lemma regular_subtype : forall chk E T1 T2 K,
    subtype chk E T1 T2 K -> subtype_regular chk E T1 T2 K.
Proof.
  pose regular_combined_kinding.
  tauto.
Qed.

Lemma unregular_subtype : forall chk E T1 T2 K,
    subtype_regular chk E T1 T2 K -> subtype chk E T1 T2 K.
Proof.
  pose unregular_combined_kinding.
  tauto.
Qed.

Hint Resolve unregular_subtype.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : subtype _ E _ _ _ |- _ =>
      apply (proj41 (subtype_regular_inv
                       (regular_subtype H)))
  end : subtype_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : subtype _ _ T _ _ |- _ =>
      apply (proj42 (subtype_regular_inv
                       (regular_subtype H)))
  | H : subtype _ _ _ T _ |- _ =>
      apply (proj43 (subtype_regular_inv
                       (regular_subtype H)))
  end : subtype_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : subtype _ _ _ _ cs |- _ =>
      apply (proj44 (subtype_regular_inv
                       (regular_subtype H)))
  end : subtype_regular.

Inductive kindings_regular
  : bool -> env -> list typ -> list knd -> Prop :=
  | kindings_regular_nil : forall chk E,
      valid_env chk E ->
      environment E ->
      kindings_regular chk E nil nil
  | kindings_regular_cons : forall chk E T Ts K Ks,
      kinding chk E T K ->
      kindings_regular chk E Ts Ks ->
      environment E ->
      type T ->
      types Ts ->
      kind K ->
      kinds Ks ->
      kindings_regular chk E (T :: Ts) (K :: Ks).

Lemma kindings_regular_inv : forall chk E Ts Ks,
    kindings_regular chk E Ts Ks ->
    environment E /\ types Ts /\ kinds Ks.
Proof.
  introv Hks.
  destruct Hks; auto.
Qed.

Hint Constructors kindings_regular : kindings_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : kindings_regular _ E _ _ |- _ =>
      apply (proj31 (kindings_regular_inv H))
  end : kindings_regular.

Hint Extern 1 (types ?Ts) =>
  match goal with
  | H : kindings_regular _ _ Ts _ |- _ =>
      apply (proj32 (kindings_regular_inv H))
  end : kindings_regular.

Hint Extern 1 (kinds ?Ks) =>
  match goal with
  | H : kindings_regular _ _ _ Ks |- _ =>
      apply (proj33 (kindings_regular_inv H))
  end : kindings_regular.

Lemma regular_kindings : forall chk E Ts Ks,
    kindings chk E Ts Ks -> kindings_regular chk E Ts Ks.
Proof.
  introv Hks.
  induction Hks;
    auto with valid_env_regular kinding_regular kindings_regular.
Qed.

Lemma unregular_kindings : forall chk E Ts Ks,
    kindings_regular chk E Ts Ks -> kindings chk E Ts Ks.
Proof.
  introv Hks.
  induction Hks; auto using kindings.
Qed.

Hint Resolve unregular_kindings.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : kindings _ E _ _ |- _ =>
      apply (proj31 (kindings_regular_inv
                       (regular_kindings H)))
  end : kindings_regular.

Hint Extern 1 (types ?Ts) =>
  match goal with
  | H : kindings _ _ Ts _ |- _ =>
      apply (proj32 (kindings_regular_inv
                       (regular_kindings H)))
  end : kindings_regular.

Hint Extern 1 (kinds ?Ks) =>
  match goal with
  | H : kindings _ _ _ Ks |- _ =>
      apply (proj33 (kindings_regular_inv
                       (regular_kindings H)))
  end : kindings_regular.

Lemma kindings_length : forall chk E Ts Ks,
    kindings chk E Ts Ks ->
    length Ts = length Ks.
Proof.
  introv Hks.
  induction Hks; simpl; auto.
Qed.

Inductive valid_schemes_regular : bool -> env -> list sch -> Prop :=
  | valid_schemes_regular_nil : forall chk E,
      valid_env chk E ->
      environment E ->
      valid_schemes_regular chk E nil
  | valid_schemes_regular_cons : forall chk E M Ms,
      valid_scheme chk E M ->
      valid_schemes_regular chk E Ms ->
      environment E ->
      scheme M ->
      schemes Ms ->
      valid_schemes_regular chk E (M :: Ms).

Lemma valid_schemes_regular_inv : forall chk E Ms,
    valid_schemes_regular chk E Ms ->
    environment E /\ schemes Ms.
Proof.
  introv Hss.
  destruct Hss; auto.
Qed.

Hint Constructors valid_schemes_regular : valid_schemes_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_schemes_regular _ E _ |- _ =>
      apply (proj1 (valid_schemes_regular_inv H))
  end : valid_schemes_regular.

Hint Extern 1 (schemes ?Ms) =>
  match goal with
  | H : valid_schemes_regular _ _ Ms |- _ =>
      apply (proj2 (valid_schemes_regular_inv H))
  end : valid_schemes_regular.

Lemma regular_valid_schemes : forall chk E Ms,
    valid_schemes chk E Ms -> valid_schemes_regular chk E Ms.
Proof.
  introv Hss.
  induction Hss;
    auto with valid_env_regular valid_scheme_regular
      valid_schemes_regular.
Qed.

Lemma unregular_valid_schemes : forall chk E Ms,
    valid_schemes_regular chk E Ms -> valid_schemes chk E Ms.
Proof.
  introv Hss.
  induction Hss; auto using valid_schemes.
Qed.

Hint Resolve unregular_valid_schemes.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_schemes _ E _ |- _ =>
      apply (proj1 (valid_schemes_regular_inv
                       (regular_valid_schemes H)))
  end : valid_schemes_regular.

Hint Extern 1 (schemes ?Ms) =>
  match goal with
  | H : valid_schemes _ _ Ms |- _ =>
      apply (proj2 (valid_schemes_regular_inv
                       (regular_valid_schemes H)))
  end : valid_schemes_regular.

Inductive valid_instance_regular : env -> list typ -> sch -> Prop :=
  | valid_instance_regular_c : forall E Ts M,
      kindings true E Ts (knd_open_list (sch_kinds M) Ts) ->
      kinding true E (typ_open (sch_body M) Ts) knd_type ->
      environment E ->
      types Ts ->
      scheme M ->
      kinds (knd_open_list (sch_kinds M) Ts) ->
      type (typ_open (sch_body M) Ts) ->
      valid_instance_regular E Ts M.

Lemma valid_instance_regular_inv : forall E Ts M,
    valid_instance_regular E Ts M ->
    environment E /\ types Ts /\ scheme M.
Proof.
  introv Hi.
  destruct Hi; auto.
Qed.

Hint Constructors valid_instance_regular : valid_instance_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_instance_regular E _ _ |- _ =>
      apply (proj31 (valid_instance_regular_inv H))
  end : valid_instance_regular.

Hint Extern 1 (types ?Ts) =>
  match goal with
  | H : valid_instance_regular _ Ts _ |- _ =>
      apply (proj32 (valid_instance_regular_inv H))
  end : valid_instance_regular.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H : valid_instance_regular _ _ M |- _ =>
      apply (proj33 (valid_instance_regular_inv H))
  end : valid_instance_regular.

Lemma regular_valid_instance : forall E Ts M,
    valid_instance E Ts M -> valid_instance_regular E Ts M.
Proof.
  introv Hi.
  induction Hi.
  apply valid_instance_regular_c;
    auto with kindings_regular kinding_regular.
  apply scheme_c with (L := typ_fv_list Ts \u sch_fv M).
  destruct M; simpl in *.
  introv Hf.
  rewrite <- knd_open_list_length with (Us := Ts) in Hf.
  rewrite <- kindings_length
    with (chk := true) (E := E) (Ts := Ts) in Hf; auto.
  apply kinds_and_type_c.
  - assert (kinds (knd_open_list sch_kinds Ts)) as Hks
      by auto with kindings_regular.
    rewrite knd_subst_list_intro with (Xs := Xs) in Hks;
      auto with kindings_regular.
    rewrite knd_subst_kind_list in Hks;
      auto with kindings_regular.    
  - assert (type (typ_open sch_body Ts)) as Ht
      by auto with kinding_regular.
    rewrite typ_subst_intro with (Xs := Xs) in Ht;
      auto with kindings_regular.
    rewrite typ_subst_type in Ht;
      auto with kindings_regular.
Qed.

Lemma unregular_valid_instance : forall E Ts M,
    valid_instance_regular E Ts M -> valid_instance E Ts M.
Proof.
  introv Hi.
  induction Hi; auto using valid_instance.
Qed.

Hint Resolve unregular_valid_instance.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_instance E _ _ |- _ =>
      apply (proj31 (valid_instance_regular_inv
                       (regular_valid_instance H)))
  end : valid_instance_regular.

Hint Extern 1 (types ?Ts) =>
  match goal with
  | H : valid_instance _ Ts _ |- _ =>
      apply (proj32 (valid_instance_regular_inv
                       (regular_valid_instance H)))
  end : valid_instance_regular.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H : valid_instance _ _ M |- _ =>
      apply (proj33 (valid_instance_regular_inv
                       (regular_valid_instance H)))
  end : valid_instance_regular.

Inductive valid_store_type_regular : env -> styp -> Prop :=
  | valid_store_type_regular_empty : forall E,
      valid_env true E ->
      environment E ->
      valid_store_type_regular E empty
  | valid_store_type_regular_push : forall E P l T,
      valid_store_type_regular E P ->
      kinding true E T knd_type ->
      l # P ->
      environment E ->
      type T ->
      valid_store_type_regular E (P & l ~ T).

Lemma valid_store_type_regular_inv : forall E P,
    valid_store_type_regular E P ->
    environment E /\ store_type P.
Proof.
  introv Hs.
  induction Hs; splits; intuition auto.
Qed.

Hint Constructors valid_store_type_regular : valid_store_type_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_store_type_regular E _ |- _ =>
      apply (proj1 (valid_store_type_regular_inv H))
  end : valid_store_type_regular.

Hint Extern 1 (store_type ?P) =>
  match goal with
  | H : valid_store_type_regular _ P |- _ =>
      apply (proj2 (valid_store_type_regular_inv H))
  end : valid_store_type_regular.

Lemma regular_valid_store_type : forall E P,
    valid_store_type E P -> valid_store_type_regular E P.
Proof.
  introv Hs.
  induction Hs;
    auto with valid_store_type_regular
      valid_env_regular kinding_regular.
Qed.

Lemma unregular_valid_store_type : forall E P,
    valid_store_type_regular E P -> valid_store_type E P.
Proof.
  introv Hs.
  induction Hs; auto using valid_store_type.
Qed.

Hint Resolve unregular_valid_store_type.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_store_type E _ |- _ =>
      apply (proj1 (valid_store_type_regular_inv
                       (regular_valid_store_type H)))
  end : valid_store_type_regular.

Hint Extern 1 (store_type ?P) =>
  match goal with
  | H : valid_store_type _ P |- _ =>
      apply (proj2 (valid_store_type_regular_inv
                       (regular_valid_store_type H)))
  end : valid_store_type_regular.

Inductive typing_regular : env -> styp -> trm -> typ -> Prop :=
  | typing_regular_var : forall E P x M T Us,
      environment E ->
      store_type P ->
      scheme M ->
      types Us ->
      type T ->
      valid_env true E ->
      valid_store_type E P ->
      binds x (bind_typ M) E -> 
      valid_instance E Us M ->
      type_equal true E T (instance M Us) knd_type ->
      typing_regular E P (trm_fvar x) T
  | typing_regular_abs : forall L E P T1 T2 t1,
      kinding true E T1 knd_type ->
      environment E ->
      (forall x, x \notin L ->
         environment (E & x ~: sch_empty T1)) ->
      store_type P ->
      type T1 ->
      type T2 ->
      term_body t1 ->
      (forall x, x \notin L -> 
        typing_regular
          (E & x ~: sch_empty T1) P (t1 ^ x) T2) -> 
      typing_regular E P (trm_abs t1) (typ_arrow T1 T2)
  | typing_regular_app : forall E P S T t1 t2, 
      environment E ->
      store_type P ->
      type S ->
      type T ->
      term t1 ->
      term t2 ->
      typing_regular E P t1 (typ_arrow S T) ->
      typing_regular E P t2 S ->   
      typing_regular E P (trm_app t1 t2) T
  | typing_regular_let_val : forall L M E P T2 t1 t2,
      environment E ->
      (forall Xs, fresh L (sch_arity M) Xs ->
         environment (E & Xs ~::* M)) ->
      (forall x, x \notin L ->
         environment (E & x ~: M)) -> 
      store_type P ->
      type T2 ->
      (forall Xs, fresh L (sch_arity M) Xs ->
         type (instance_vars M Xs)) ->
      scheme M ->
      term t1 ->
      term_body t2 ->
      value t1 ->
      (forall Xs, fresh L (sch_arity M) Xs ->
         typing_regular
           (E & Xs ~::* M) P
           t1 (instance_vars M Xs)) ->
      (forall x, x \notin L ->
         typing_regular (E & x ~: M) P (t2 ^ x) T2) -> 
      typing_regular E P (trm_let t1 t2) T2
  | typing_regular_let : forall L E P T1 T2 t1 t2,
      environment E ->
      (forall x, x \notin L ->
         environment (E & x ~: sch_empty T1)) -> 
      store_type P ->
      type T1 ->
      type T2 ->
      term t1 ->
      term_body t2 ->
      typing_regular E P t1 T1 ->
      (forall x, x \notin L ->
         typing_regular (E & x ~: sch_empty T1) P (t2 ^ x) T2) -> 
      typing_regular E P (trm_let t1 t2) T2
  | typing_regular_constructor : forall c E P T1 T2 T3 t,
      environment E ->
      store_type P ->
      type T1 ->
      type T2 ->
      type T3 ->
      term t ->
      kinding true E T1 (knd_range (typ_top CSet.universe) T2) ->
      subtype true E
        (typ_constructor c T3)
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (CSet.singleton c) ->
      typing_regular E P t T3 ->
      typing_regular E P (trm_constructor c t) (typ_variant T1)
  | typing_regular_match : forall L c E P T1 T2 T3 T4 T5
                          T6 T7 T8 t1 t2 t3,
      environment E ->
      (forall x, x \notin L ->
         environment (E & x ~: (sch_empty (typ_variant T3)))) ->
      (forall y, y \notin L -> 
         environment (E & y ~: (sch_empty (typ_variant T5)))) ->
      store_type P ->
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
      kinding true E T1 (knd_range T2 (typ_bot CSet.universe)) ->
      kinding true E T3 (knd_range (typ_top CSet.universe) T4) ->
      kinding true E T5 (knd_range (typ_top CSet.universe) T6) ->
      subtype true E
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (typ_constructor c T7)
        (CSet.singleton c) ->
      subtype true E
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (typ_proj CSet.universe T4 (CSet.singleton c))
        (CSet.singleton c) ->
      subtype true E
        (typ_proj CSet.universe T2 (CSet.cosingleton c))
        (typ_proj CSet.universe T6 (CSet.cosingleton c))
        (CSet.cosingleton c) ->
      typing_regular E P t1 (typ_variant T1) ->
      (forall x, x \notin L ->
         typing_regular (E & x ~: (sch_empty (typ_variant T3))) P
                (t2 ^ x) T8) ->
      (forall y, y \notin L -> 
         typing_regular (E & y ~: (sch_empty (typ_variant T5))) P
                (t3 ^ y) T8) ->
      typing_regular E P (trm_match t1 c t2 t3) T8
  | typing_regular_destruct : forall L c E P T1 T2 T3 T4 t1 t2,
      environment E ->
      (forall x, x \notin L ->
         environment (E & x ~: (sch_empty T3))) ->
      store_type P ->
      type T1 ->
      type T2 ->
      type T3 ->
      type T4 ->
      term t1 ->
      term_body t2 ->
      kinding true E T1 (knd_range T2 (typ_bot CSet.universe)) ->
      subtype true E
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (typ_constructor c T3)
        (CSet.singleton c) ->
      subtype true E
        (typ_proj CSet.universe T2 (CSet.cosingleton c))
        (typ_bot (CSet.cosingleton c))
        (CSet.cosingleton c) ->
      typing_regular E P t1 (typ_variant T1) ->
      (forall x, x \notin L ->
         typing_regular (E & x ~: (sch_empty T3)) P
                (t2 ^ x) T4) ->
      typing_regular E P (trm_destruct t1 c t2) T4
  | typing_regular_absurd : forall E P T1 T2 t1,
      environment E ->
      store_type P ->
      type T1 ->
      type T2 ->
      term t1 ->
      kinding true E T1 (knd_range (typ_bot CSet.universe)
                              (typ_bot CSet.universe)) ->
      kinding true E T2 knd_type ->
      typing_regular E P t1 (typ_variant T1) ->
      typing_regular E P (trm_absurd t1) T2
  | typing_regular_fix : forall L E P T1 T2 t1,
      environment E ->
      (forall x y, x \notin L -> y \notin (L \u \{x}) ->
         environment
           (E & x ~: sch_empty (typ_arrow T1 T2)
              & y ~: sch_empty T1)) ->
      store_type P ->
      type T1 ->
      type T2 ->
      term_body2 t1 ->
      (forall x y,
          x \notin L -> y \notin (L \u \{x}) ->
          typing_regular
            (E & x ~: sch_empty (typ_arrow T1 T2) & y ~: sch_empty T1)
            P (t1 ^* (x::y::nil)) T2) -> 
      typing_regular E P (trm_fix t1) (typ_arrow T1 T2)      
  | typing_regular_unit : forall E P,
      environment E ->
      store_type P ->
      valid_env true E ->
      valid_store_type E P ->
      typing_regular E P trm_unit typ_unit
  | typing_regular_prod : forall E P T1 T2 t1 t2,
      environment E ->
      store_type P ->
      type T1 ->
      type T2 ->
      term t1 ->
      term t2 ->
      typing_regular E P t1 T1 ->
      typing_regular E P t2 T2 ->
      typing_regular E P (trm_prod t1 t2) (typ_prod T1 T2)
  | typing_regular_fst : forall E P T1 T2 t1,
      environment E ->
      store_type P ->
      type T1 ->
      type T2 ->
      term t1 ->
      typing_regular E P t1 (typ_prod T1 T2) ->
      typing_regular E P (trm_fst t1) T1
  | typing_regular_snd : forall E P T1 T2 t1,
      environment E ->
      store_type P ->
      type T1 ->
      type T2 ->
      term t1 ->
      typing_regular E P t1 (typ_prod T1 T2) ->
      typing_regular E P (trm_snd t1) T2
  | typing_regular_loc : forall E P l T1 T2,
      environment E ->
      store_type P ->
      type T1 ->
      type T2 ->
      valid_env true E ->
      valid_store_type E P ->
      binds l T1 P ->
      type_equal true E T1 T2 knd_type ->
      typing_regular E P (trm_loc l) (typ_ref T2)
  | typing_regular_ref : forall E P t1 T,
      environment E ->
      store_type P ->
      type T ->
      term t1 ->
      typing_regular E P t1 T ->
      typing_regular E P (trm_ref t1) (typ_ref T)
  | typing_regular_get : forall E P t1 T,
      environment E ->
      store_type P ->
      type T ->
      term t1 ->
      typing_regular E P t1 (typ_ref T) ->
      typing_regular E P (trm_get t1) T
  | typing_regular_set : forall E P t1 t2 T,
      environment E ->
      store_type P ->
      type T ->
      term t1 ->
      term t2 ->
      typing_regular E P t1 (typ_ref T) ->
      typing_regular E P t2 T ->
      typing_regular E P (trm_set t1 t2) typ_unit.

Lemma typing_regular_inv : forall E P t T,
    typing_regular E P t T ->
      environment E /\ store_type P /\ term t /\ type T.
Proof.
  introv Ht.
  induction Ht; auto.
Qed.

Hint Constructors typing_regular : typing_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : typing_regular E _ _ _ |- _ =>
      apply (proj41 (typing_regular_inv H))
  end : typing_regular.

Hint Extern 1 (store_type ?P) =>
  match goal with
  | H : typing_regular _ P _ _ |- _ =>
      apply (proj42 (typing_regular_inv H))
  end : typing_regular.

Hint Extern 1 (term ?t) =>
  match goal with
  | H : typing_regular _ _ t _ |- _ =>
      apply (proj43 (typing_regular_inv H))
  end : typing_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : typing_regular _ _ _ T |- _ =>
      apply (proj44 (typing_regular_inv H))
  end : typing_regular.

Lemma regular_typing : forall E P t T,
    typing E P t T -> typing_regular E P t T.
Proof.
  introv Ht.
  induction Ht.
  - assert (environment E)
      by auto with valid_env_regular.
    assert (store_type P)
      by auto with valid_store_type_regular.
    assert (scheme M)
      by (eapply scheme_from_env; eassumption).
    assert (types Us)
      by auto with valid_instance_regular.   
    assert (type T)
      as Ht by auto with type_equal_regular.
    eauto with typing_regular.
  - pick_fresh_gen L x.
    assert (typing_regular (E & x ~: sch_empty T1) P (t1 ^ x) T2)
      by auto.
    apply typing_regular_abs with (L := L); auto with typing_regular.
    + eauto using environment_concat_inv_l with typing_regular.
    + intros y Hn.
      assert (typing_regular (E & y ~: sch_empty T1) P (t1 ^ y) T2)
        by auto.
      auto with typing_regular.
    + rewrite scheme_empty_type.
      eauto using scheme_from_env with typing_regular.
    + exists L.
      intros y Hny.
      assert (typing_regular (E & y ~: sch_empty T1) P (t1 ^ y) T2)
        by auto.
      auto with typing_regular.
  - assert (type (typ_arrow S T)) as Hta
      by auto with typing_regular.
    inversion Hta; subst.
    eauto with typing_regular.
  - pick_freshes_gen L (sch_arity M) Xs.
    assert (typing_regular (E & Xs ~::* M) P t1 (instance_vars M Xs))
      by auto.
    pick_fresh_gen L x.
    assert (typing_regular (E & x ~: M) P (t2 ^ x) T2) by auto.
    apply typing_regular_let_val with (M := M) (L := L);
      auto with typing_regular.
    + eauto using environment_concat_inv_l with typing_regular.
    + intros Ys Hf.
      assert
        (typing_regular (E & Ys ~::* M) P t1 (instance_vars M Ys))
        by auto.
      auto with typing_regular.
    + intros y Hn.
      assert (typing_regular (E & y ~: M) P (t2 ^ y) T2)
        by auto.
      auto with typing_regular.
    + intros Ys Hl.
      assert
        (typing_regular (E & Ys ~::* M) P t1 (instance_vars M Ys))
        by auto.
      auto with typing_regular.
    + eauto using scheme_from_env with typing_regular.
    + exists L.
      intros y Hny.
      assert (typing_regular (E & y ~: M) P (t2 ^ y) T2)
        by auto.
      auto with typing_regular.
  - pick_fresh_gen L x.
    assert (typing_regular (E & x ~: sch_empty T1) P (t2 ^ x) T2)
      by auto.
    apply typing_regular_let with (T1 := T1) (L := L);
      auto with typing_regular.
    + intros y Hn.
      assert (typing_regular (E & y ~: sch_empty T1) P (t2 ^ y) T2)
        by auto.
      auto with typing_regular.
    + exists L.
      intros y Hn.
      assert (typing_regular (E & y ~: sch_empty T1) P (t2 ^ y) T2)
        by auto.
      auto with typing_regular.
  - assert (kind (knd_range (typ_top CSet.universe) T2)) as Hknd
        by auto with kinding_regular.
    inversion Hknd; subst.
    apply typing_regular_constructor with (T2 := T2) (T3 := T3);
      auto with typing_regular kinding_regular.
  - assert
      (kind (knd_range T2 (typ_bot CSet.universe))) as Hknd1
        by auto with kinding_regular.
    inversion Hknd1; subst.
    assert
      (kind (knd_range (typ_top CSet.universe) T4)) as Hknd2
      by auto with kinding_regular.
    inversion Hknd2; subst.
    assert
      (kind (knd_range (typ_top CSet.universe) T6)) as Hknd3
      by auto with kinding_regular.
    inversion Hknd3; subst.
    pick_fresh_gen L x.
    assert
      (typing_regular (E & x ~: sch_empty (typ_variant T3)) P
         (t2 ^ x) T8) by auto.
    apply typing_regular_match
      with (L := L) (T1 := T1) (T2 := T2) (T3 := T3)
           (T4 := T4) (T5 := T5) (T6 := T6) (T7 := T7);
      auto with typing_regular kinding_regular.
    + intros y Hny.
      assert
        (typing_regular (E & y ~: sch_empty (typ_variant T3)) P
                        (t2 ^ y) T8)
        by auto.
      auto with typing_regular.
    + intros y Hny.
      assert
        (typing_regular (E & y ~: sch_empty (typ_variant T5)) P
                        (t3 ^ y) T8)
        by auto.
      auto with typing_regular.
    + assert (type (typ_constructor c T7)) as Hto
          by auto with subtype_regular.
      inversion Hto; subst.
      assumption.
    + exists L.
      intros y Hny.
      assert
        (typing_regular (E & y ~: sch_empty (typ_variant T3)) P
                        (t2 ^ y) T8)
        by auto.
      auto with typing_regular.
    + exists L.
      intros y Hny.
      assert
        (typing_regular (E & y ~: sch_empty (typ_variant T5)) P
                        (t3 ^ y) T8)
        by auto.
      auto with typing_regular.
  - apply typing_regular_destruct
      with (L := L) (T1 := T1) (T2 := T2) (T3 := T3);
      auto with typing_regular kinding_regular.
    + intros y Hfy.
      assert (typing_regular (E & y ~: sch_empty T3) P (t2 ^ y) T4)
        by auto.
      auto with typing_regular.
    + assert (type (typ_proj CSet.universe T2 (CSet.singleton c)))
        as Htp by auto with subtype_regular.
      inversion Htp; assumption.
    + assert (type (typ_constructor c T3)) as Htc
        by auto with subtype_regular.
      inversion Htc; assumption.
    + pick_fresh_gen L x.
      assert (typing_regular (E & x ~: sch_empty T3) P (t2 ^ x) T4)
        by auto.
      auto with typing_regular.
    + exists L.
      intros y Hny.
      assert
        (typing_regular (E & y ~: sch_empty T3) P (t2 ^ y) T4)
        by auto.
      auto with typing_regular.
  - apply typing_regular_absurd with (T1 := T1);
      auto with typing_regular kinding_regular.
  - pick_fresh_gen L x.
    pick_fresh_gen (L \u \{x}) y.
    assert
      (typing_regular
         (E & x ~: sch_empty (typ_arrow T1 T2) & y ~: sch_empty T1)
         P (t1 ^* x :: y :: nil) T2) by auto.
    assert (type (typ_arrow T1 T2)) as Ht
      by (rewrite scheme_empty_type;
          eauto using scheme_from_env with typing_regular).
    inversion Ht; subst.
    apply typing_regular_fix with (L := L); auto with typing_regular.
    + eauto using environment_concat_inv_l with typing_regular.
    + intros x' y' Hn1 Hn2.
      assert
        (typing_regular
           (E & x' ~: sch_empty (typ_arrow T1 T2)
              & y' ~: sch_empty T1) P (t1 ^* x' :: y' :: nil) T2)
        by auto.
      auto with typing_regular.
    + exists L.
      intros x' y' Hn1 Hn2.
      assert
        (typing_regular
           (E & x' ~: sch_empty (typ_arrow T1 T2)
              & y' ~: sch_empty T1) P (t1 ^* x' :: y' :: nil) T2)
        by auto.
      auto with typing_regular.
  - apply typing_regular_unit;
      auto with valid_store_type_regular.
  - apply typing_regular_prod;
      auto with typing_regular.
  - assert (type (typ_prod T1 T2)) as Htyp
      by auto with typing_regular.
    inversion Htyp; subst.
    apply typing_regular_fst with (T2 := T2);
      auto with typing_regular.
  - assert (type (typ_prod T1 T2)) as Htyp
      by auto with typing_regular.
    inversion Htyp; subst.
    apply typing_regular_snd with (T1 := T1);
      auto with typing_regular.
  - apply typing_regular_loc with (T1 := T1);
      auto with valid_store_type_regular.
    + eauto using type_from_store_type with valid_store_type_regular.
    + auto with type_equal_regular.
  - apply typing_regular_ref;
      auto with typing_regular.
  - assert (type (typ_ref T)) as Htyp
      by auto with typing_regular.
    inversion Htyp; subst.
    apply typing_regular_get;
      auto with typing_regular.
  - apply typing_regular_set with (T := T);
      auto with typing_regular.
Qed.

Lemma unregular_typing : forall E P t T,
    typing_regular E P t T -> typing E P t T.
Proof.
  introv Ht.
  induction Ht; eauto using typing.
Qed.

Hint Resolve unregular_typing.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : typing E _ _ _ |- _ =>
      apply (proj41 (typing_regular_inv (regular_typing H)))
  end : typing_regular.

Hint Extern 1 (store_type ?P) =>
  match goal with
  | H : typing _ P _ _ |- _ =>
      apply (proj42 (typing_regular_inv (regular_typing H)))
  end : typing_regular.

Hint Extern 1 (term ?t) =>
  match goal with
  | H : typing _ _ t _ |- _ =>
      apply (proj43 (typing_regular_inv (regular_typing H)))
  end : typing_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : typing _ _ _ T |- _ =>
      apply (proj44 (typing_regular_inv (regular_typing H)))
  end : typing_regular.

Inductive typing_scheme_regular : env -> styp -> trm -> sch -> Prop :=
  | typing_scheme_regular_c : forall L E P t M,
      environment E ->
      (forall Xs, fresh L (sch_arity M) Xs ->
         environment (E & Xs ~::* M)) ->
      store_type P ->
      scheme M ->
      term t ->
      valid_scheme true E M ->
      valid_store_type E P ->
      (forall Xs,
         fresh L (sch_arity M) Xs ->
         typing (E & Xs ~::* M) P t (instance_vars M Xs)) ->     
      typing_scheme_regular E P t M.

Lemma typing_scheme_regular_inv : forall E P t M,
    typing_scheme_regular E P t M ->
      environment E /\ store_type P /\ term t /\ scheme M.
Proof.
  introv Ht.
  induction Ht; auto.
Qed.

Hint Constructors typing_scheme_regular : typing_scheme_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : typing_scheme_regular E _ _ _ |- _ =>
      apply (proj41 (typing_scheme_regular_inv H))
  end : typing_scheme_regular.

Hint Extern 1 (store_type ?P) =>
  match goal with
  | H : typing_scheme_regular _ P _ _ |- _ =>
      apply (proj42 (typing_scheme_regular_inv H))
  end : typing_scheme_regular.

Hint Extern 1 (term ?t) =>
  match goal with
  | H : typing_scheme_regular _ _ t _ |- _ =>
      apply (proj43 (typing_scheme_regular_inv H))
  end : typing_scheme_regular.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H : typing_scheme_regular _ _ _ M |- _ =>
      apply (proj44 (typing_scheme_regular_inv H))
  end : typing_scheme_regular.

Lemma regular_typing_scheme : forall E P t M,
    typing_scheme E P t M -> typing_scheme_regular E P t M.
Proof.
  introv Ht.
  destruct Ht.
  pick_freshes_gen L (sch_arity M) Xs.
  assert (typing (E & Xs ~::* M) P t (instance_vars M Xs)) by auto.
  apply typing_scheme_regular_c with (L := L);
    eauto using environment_concat_inv_l
      with typing_regular valid_scheme_regular.
  - intros Ys Hn.
    assert (typing (E & Ys ~::* M) P t (instance_vars M Ys)) by auto.
    eauto with typing_regular.
Qed.

Lemma unregular_typing_scheme : forall E P t T,
    typing_scheme_regular E P t T -> typing_scheme E P t T.
Proof.
  introv Ht.
  induction Ht; eauto using typing_scheme.
Qed.

Hint Resolve unregular_typing_scheme.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : typing_scheme E _ _ _ |- _ =>
      apply (proj41 (typing_scheme_regular_inv
                       (regular_typing_scheme H)))
  end : typing_scheme_regular.

Hint Extern 1 (store_type ?P) =>
  match goal with
  | H : typing_scheme _ P _ _ |- _ =>
      apply (proj42 (typing_scheme_regular_inv
                       (regular_typing_scheme H)))
  end : typing_scheme_regular.

Hint Extern 1 (term ?t) =>
  match goal with
  | H : typing_scheme _ _ t _ |- _ =>
      apply (proj43 (typing_scheme_regular_inv
                       (regular_typing_scheme H)))
  end : typing_scheme_regular.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H : typing_scheme _ _ _ M |- _ =>
      apply (proj44 (typing_scheme_regular_inv
                       (regular_typing_scheme H)))
  end : typing_scheme_regular.

Inductive typing_schemes_regular
  : env -> styp -> list trm -> list sch -> Prop :=
  | typing_schemes_regular_nil : forall E P,
      valid_env true E ->
      valid_store_type E P ->
      environment E ->
      store_type P ->
      typing_schemes_regular E P nil nil
  | typing_schemes_regular_cons : forall E P t ts M Ms,
      typing_scheme E P t M ->
      typing_schemes_regular E P ts Ms ->
      environment E ->
      store_type P ->
      scheme M ->
      schemes Ms ->
      term t ->
      terms ts ->
      typing_schemes_regular E P (t :: ts) (M :: Ms).

Lemma typing_schemes_regular_inv : forall E P ts Ms,
    typing_schemes_regular E P ts Ms ->
    environment E /\ store_type P /\ terms ts /\ schemes Ms.
Proof.
  introv Hts.
  destruct Hts; auto.
Qed.

Hint Constructors typing_schemes_regular : typing_schemes_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : typing_schemes_regular E _ _ _ |- _ =>
      apply (proj41 (typing_schemes_regular_inv H))
  end : typing_schemes_regular.

Hint Extern 1 (store_type ?P) =>
  match goal with
  | H : typing_schemes_regular _ P _ _ |- _ =>
      apply (proj42 (typing_schemes_regular_inv H))
  end : typing_schemes_regular.

Hint Extern 1 (terms ?ts) =>
  match goal with
  | H : typing_schemes_regular _ _ ts _ |- _ =>
      apply (proj43 (typing_schemes_regular_inv H))
  end : typing_schemes_regular.

Hint Extern 1 (schemes ?Ms) =>
  match goal with
  | H : typing_schemes_regular _ _ _ Ms |- _ =>
      apply (proj44 (typing_schemes_regular_inv H))
  end : typing_schemes_regular.

Lemma regular_typing_schemes : forall E P ts Ms,
    typing_schemes E P ts Ms -> typing_schemes_regular E P ts Ms.
Proof.
  introv Hts.
  induction Hts;
    auto with valid_env_regular valid_store_type_regular
      typing_scheme_regular typing_schemes_regular.  
Qed.

Lemma unregular_typing_schemes : forall E P ts Ms,
    typing_schemes_regular E P ts Ms -> typing_schemes E P ts Ms.
Proof.
  introv Hts.
  induction Hts; auto using typing_schemes.
Qed.

Hint Resolve unregular_typing_schemes.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : typing_schemes E _ _ _ |- _ =>
      apply (proj41 (typing_schemes_regular_inv
                       (regular_typing_schemes H)))
  end : typing_schemes_regular.

Hint Extern 1 (store_type ?P) =>
  match goal with
  | H : typing_schemes _ P _ _ |- _ =>
      apply (proj42 (typing_schemes_regular_inv
                       (regular_typing_schemes H)))
  end : typing_schemes_regular.

Hint Extern 1 (terms ?ts) =>
  match goal with
  | H : typing_schemes _ _ ts _ |- _ =>
      apply (proj43 (typing_schemes_regular_inv
                       (regular_typing_schemes H)))
  end : typing_schemes_regular.

Hint Extern 1 (schemes ?Ms) =>
  match goal with
  | H : typing_schemes _ _ _ Ms |- _ =>
      apply (proj44 (typing_schemes_regular_inv
                       (regular_typing_schemes H)))
  end : typing_schemes_regular.

Lemma typing_schemes_length : forall E P ts Ms,
    typing_schemes E P ts Ms ->
    length ts = length Ms.
Proof.
  introv Hts.
  induction Hts; simpl; auto.
Qed.

Lemma typing_store_regular_inv : forall E V P,
    typing_store E V P ->
    environment E /\ store V /\ store_type P.
Proof.
  introv Ht.
  destruct Ht as [Hs [Hv _]].
  splits; auto with valid_store_type_regular.
Qed.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : typing_store E _ _ |- _ =>
      apply (proj31 (typing_store_regular_inv H))
  end : typing_store_regular.

Hint Extern 1 (store ?V) =>
  match goal with
  | H : typing_store _ V _ |- _ =>
      apply (proj32 (typing_store_regular_inv H))
  end : typing_store_regular.

Hint Extern 1 (store_type ?P) =>
  match goal with
  | H : typing_store _ _ P |- _ =>
      apply (proj32 (typing_store_regular_inv H))
  end : typing_store_regular.

Inductive value_regular : trm -> Prop :=
  | value_regular_constructor : forall c t,
      term t ->
      value_regular t ->
      value_regular (trm_constructor c t)
  | value_regular_abs : forall t,
      term_body t ->
      value_regular (trm_abs t)
  | value_regular_fix : forall t,
      term_body2 t ->
      value_regular (trm_fix t)
  | value_regular_unit :
      value_regular trm_unit
  | value_regular_prod : forall t1 t2,
      term t1 ->
      term t2 ->
      value_regular t1 ->
      value_regular t2 ->
      value_regular (trm_prod t1 t2)
  | value_regular_loc : forall l,
      value_regular (trm_loc l).

Lemma value_regular_inv : forall t,
    value_regular t -> term t.
Proof.
  introv Hv.
  induction Hv; auto.
Qed.

Hint Constructors value_regular : value_regular.

Hint Extern 1 (term ?t) =>
  match goal with
  | H : value_regular t |- _ =>
      apply (value_regular_inv H)
  end : value_regular.

Lemma regular_value : forall t,
    value t -> value_regular t.
Proof.
  introv Hv.
  induction Hv; auto with value_regular.
  - assert (term (trm_abs t)) as Ht by assumption.
    inversion Ht; subst.
    apply value_regular_abs; try assumption.
    exists L.
    auto.
  - assert (term (trm_fix t)) as Ht by assumption.
    inversion Ht; subst.
    apply value_regular_fix; try assumption.
    exists L.
    auto.
Qed.

Lemma unregular_value : forall t,
    value_regular t -> value t.
Proof.
  introv Hv.
  induction Hv; auto using value.
Qed.

Hint Resolve unregular_value.

Hint Extern 1 (term ?t) =>
  match goal with
  | H : value t |- _ =>
      apply (value_regular_inv (regular_value H))
  end : value_regular.

Inductive red_regular : trm -> sto -> trm -> sto -> Prop :=
  | red_regular_let_1 : forall V t1 t2,
      store V ->
      term t1 ->
      term_body t2 ->
      value t1 -> 
      red_regular (trm_let t1 t2) V (t2 ^^ t1) V
  | red_regular_let_2 : forall V V' t1 t1' t2,
      store V ->
      store V' ->
      term t1 ->
      term t1' ->
      term_body t2 ->
      red_regular t1 V t1' V' -> 
      red_regular (trm_let t1 t2) V (trm_let t1' t2) V'
  | red_regular_app_1 : forall V V' t1 t1' t2,
      store V ->
      store V' ->
      term t1 ->
      term t1' ->
      term t2 ->
      red_regular t1 V t1' V' -> 
      red_regular (trm_app t1 t2) V (trm_app t1' t2) V'
  | red_regular_app_2 : forall V V' t1 t2 t2', 
      store V ->
      store V' ->
      term t1 ->
      term t2 ->
      term t2' ->
      value t1 ->
      red_regular t2 V t2' V' ->
      red_regular (trm_app t1 t2) V (trm_app t1 t2') V'
  | red_regular_app_3 : forall V t1 t2, 
      store V ->
      term t2 ->
      term_body t1 ->
      value t2 ->  
      red_regular (trm_app (trm_abs t1) t2) V (t1 ^^ t2) V
  | red_regular_app_4 : forall V t1 t2,
      store V ->
      term t2 ->
      term_body2 t1 -> 
      value t2 ->
      red_regular (trm_app (trm_fix t1) t2) V 
          (t1 ^^* ((trm_fix t1)::t2::nil)) V
  | red_regular_constructor : forall V V' c t t',
      store V ->
      store V' ->
      term t ->
      term t' ->
      red_regular t V t' V' ->
      red_regular (trm_constructor c t) V (trm_constructor c t') V'
  | red_regular_match_1 : forall V V' c t1 t1' t2 t3,
      store V ->
      store V' ->
      term t1 ->
      term t1' ->
      term_body t2 ->
      term_body t3 ->
      red_regular t1 V t1' V' ->
      red_regular (trm_match t1 c t2 t3) V (trm_match t1' c t2 t3) V'
  | red_regular_match_2 : forall V c1 c2 t1 t2 t3,
      store V ->
      term t1 ->
      term_body t2 ->
      term_body t3 ->
      c1 = c2 ->
      value (trm_constructor c1 t1) ->
      red_regular (trm_match (trm_constructor c1 t1) c2 t2 t3) V
          (t2 ^^ (trm_constructor c1 t1)) V
  | red_regular_match_3 : forall V c1 c2 t1 t2 t3,
      store V ->
      term t1 ->
      term_body t2 ->
      term_body t3 ->
      c1 <> c2 ->
      value (trm_constructor c1 t1) ->
      red_regular (trm_match (trm_constructor c1 t1) c2 t2 t3) V
          (t3 ^^ (trm_constructor c1 t1)) V
  | red_regular_destruct_1 : forall V V' c t1 t1' t2,
      store V ->
      store V' ->
      term t1 ->
      term t1' ->
      term_body t2 ->
      red_regular t1 V t1' V' ->
      red_regular (trm_destruct t1 c t2) V (trm_destruct t1' c t2) V'
  | red_regular_destruct_2 : forall V c1 c2 t1 t2,
      store V ->
      term t1 ->
      term_body t2 ->
      c1 = c2 ->
      value (trm_constructor c1 t1) ->
      term_body t2 ->
      red_regular (trm_destruct (trm_constructor c1 t1) c2 t2) V
          (t2 ^^ t1) V
  | red_regular_absurd : forall V V' t t',
      store V ->
      store V' ->
      term t ->
      term t' ->
      red_regular t V t' V' ->
      red_regular (trm_absurd t) V (trm_absurd t') V'
  | red_regular_prod_1 : forall V V' t1 t1' t2,
      store V ->
      store V' ->
      term t1 ->
      term t1' ->
      term t2 ->
      red_regular t1 V t1' V' -> 
      red_regular (trm_prod t1 t2) V (trm_prod t1' t2) V'
  | red_regular_prod_2 : forall V V' t1 t2 t2', 
      store V ->
      store V' ->
      term t1 ->
      term t2 ->
      term t2' ->
      value t1 ->
      red_regular t2 V t2' V' ->
      red_regular (trm_prod t1 t2) V (trm_prod t1 t2') V'
  | red_regular_fst_1 : forall V V' t t',
      store V ->
      store V' ->
      term t ->
      term t' ->
      red_regular t V t' V' ->
      red_regular (trm_fst t) V (trm_fst t') V'
  | red_regular_fst_2 : forall V t1 t2, 
      store V ->
      term t1 ->
      term t2 ->
      value t1 -> 
      value t2 ->  
      red_regular (trm_fst (trm_prod t1 t2)) V t1 V
  | red_regular_snd_1 : forall V V' t t',
      store V ->
      store V' ->
      term t ->
      term t' ->
      red_regular t V t' V' ->
      red_regular (trm_snd t) V (trm_snd t') V'
  | red_regular_snd_2 : forall V t1 t2, 
      store V ->
      term t1 ->
      term t2 ->
      value t1 -> 
      value t2 ->  
      red_regular (trm_snd (trm_prod t1 t2)) V t2 V
  | red_regular_ref_1 : forall V V' t t',
      store V ->
      store V' ->
      term t ->
      term t' ->
      red_regular t V t' V' ->
      red_regular (trm_ref t) V (trm_ref t') V'
  | red_regular_ref_2 : forall V t l,
      store V ->
      term t ->
      value t ->
      l # V ->
      red_regular (trm_ref t) V (trm_loc l) (V & l ~ t)
  | red_regular_get_1 : forall V V' t t',
      store V ->
      store V' ->
      term t ->
      term t' ->
      red_regular t V t' V' ->
      red_regular (trm_get t) V (trm_get t') V'
  | red_regular_get_2 : forall V t l,
      store V ->
      term t ->
      binds l t V ->
      red_regular (trm_get (trm_loc l)) V t V
  | red_regular_set_1 : forall V V' t1 t1' t2,
      store V ->
      store V' ->
      term t1 ->
      term t1' ->
      term t2 ->
      red_regular t1 V t1' V' ->
      red_regular (trm_set t1 t2) V (trm_set t1' t2) V'
  | red_regular_set_2 : forall V V' t1 t2 t2',
      store V ->
      store V' ->
      term t1 ->
      term t2 ->
      term t2' ->
      value t1 ->
      red_regular t2 V t2' V' ->
      red_regular (trm_set t1 t2) V (trm_set t1 t2') V'
  | red_regular_set_3 : forall V l t2,
      store V ->
      term t2 ->
      value t2 ->
      red_regular (trm_set (trm_loc l) t2) V trm_unit (V & l ~ t2).

Lemma red_regular_inv : forall t1 V1 t2 V2,
    red_regular t1 V1 t2 V2 ->
    term t1 /\ store V1 /\ term t2 /\ store V2.
Proof.
  introv Hv.
  induction Hv; splits; auto.
Qed.

Hint Constructors red_regular : red_regular.

Hint Extern 1 (term ?t) =>
  match goal with
  | H : red_regular t _ _ _ |- _ =>
      apply (proj41 (red_regular_inv H))
  | H : red_regular _ _ t _ |- _ =>
      apply (proj43 (red_regular_inv H))
  end : red_regular.

Hint Extern 1 (store ?V) =>
  match goal with
  | H : red_regular _ V _ _ |- _ =>
      apply (proj42 (red_regular_inv H))
  | H : red_regular _ _ _ V |- _ =>
      apply (proj44 (red_regular_inv H))
  end : red_regular.

Lemma regular_red : forall t1 V1 t2 V2,
    red t1 V1 t2 V2 -> red_regular t1 V1 t2 V2.
Proof.
  introv Hr.
  induction Hr; auto with red_regular value_regular.
  - assert (term (trm_let t1 t2)) as Ht by assumption.
    inversion Ht; subst.
    assert (term_body t2)
      by (exists L; auto).
    auto with red_regular.
  - assert (term (trm_constructor c1 t1)) as Ht
        by auto with value_regular.
    inversion Ht; subst.
    auto with red_regular.
  - assert (term (trm_constructor c1 t1)) as Ht
        by auto with value_regular.
    inversion Ht; subst.
    auto with red_regular.
  - assert (term (trm_constructor c1 t1)) as Ht
        by auto with value_regular.
    inversion Ht; subst.
    auto with red_regular.
  - assert (value t).
    eauto using value_from_store.
    auto with red_regular value_regular.
Qed.

Lemma unregular_red : forall t1 V1 t2 V2,
    red_regular t1 V1 t2 V2 -> red t1 V1 t2 V2.
Proof.
  introv Hr.
  induction Hr; auto using red.
Qed.

Hint Resolve unregular_red.

Hint Extern 1 (term ?t) =>
  match goal with
  | H : red t _ _ _ |- _ =>
      apply (proj41 (red_regular_inv (regular_red H)))
  | H : red _ _ t _ |- _ =>
      apply (proj43 (red_regular_inv (regular_red H)))
  end : red_regular.

Hint Extern 1 (store ?V) =>
  match goal with
  | H : red _ V _ _ |- _ =>
      apply (proj42 (red_regular_inv (regular_red H)))
  | H : red _ _ _ V |- _ =>
      apply (proj44 (red_regular_inv (regular_red H)))
  end : red_regular.
