(************************************************
 *          Row Subtyping - Well-formedness     *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import List LibLN Cofinite Disjoint Utilities
        Definitions Substitution.

(* *************************************************************** *)
(** ** Add hints for wellformedness constructors *)

Hint Constructors
  kind kinds type types range ranges ranges_and_type
  scheme schemes term terms type_environment environment
  store store_type.

Hint Extern 1 (scheme _) =>
  let L' := gather_vars in
  let L' := beautify_fset L' in
  apply scheme_c with (L := L').

Hint Extern 1 (term (trm_abs ?t)) =>
  let L' := gather_vars in
  let L' := beautify_fset L' in
  apply term_abs with (L := L').

Hint Extern 1 (term (trm_let ?t1 ?t2)) =>
  let L' := gather_vars in
  let L' := beautify_fset L' in
  apply term_let with (L := L').

Hint Extern 1 (term (trm_match ?t1 ?c ?t2 ?t3)) =>
  let L' := gather_vars in
  let L' := beautify_fset L' in
  apply term_match with (L := L').

Hint Extern 1 (term (trm_destruct ?t1 ?c ?t2)) =>
  let L' := gather_vars in
  let L' := beautify_fset L' in
  apply term_destruct with (L := L').

Hint Extern 1 (term (trm_fix ?t)) =>
  let L' := gather_vars in
  let L' := beautify_fset L' in
  apply term_fix with (L := L').

(* ****************************************************** *)
(** * Properties of terms *)

Lemma term_abs_body : forall t1,
    term_body t1 -> term (trm_abs t1).
Proof.
  introv [L Ht].
  auto.
Qed.

Lemma term_let_body : forall t1 t2,
    term t1 -> term_body t2 ->
    term (trm_let t1 t2).
Proof.
  introv Ht1 [L Ht2].
  auto.
Qed.

Lemma term_match_body : forall t1 c t2 t3,
    term t1 ->
    term_body t2 ->
    term_body t3 ->
    term (trm_match t1 c t2 t3).
Proof.
  introv Ht1 [L2 Ht2] [L3 Ht3].
  apply term_match with (L := L2 \u L3); auto.
Qed.

Lemma term_destruct_body : forall t1 c t2,
    term t1 ->
    term_body t2 ->
    term (trm_destruct t1 c t2).
Proof.
  introv Ht1 [L Ht2].
  auto.
Qed.

Lemma term_fix_body : forall t1,
    term_body2 t1 ->
    term (trm_fix t1).
Proof.
  introv [L Ht].
  auto.
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

(* *************************************************************** *)
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

(* *************************************************************** *)
(** * Properties of kinds *)

Lemma rng_knd_kind : forall R,
  range R ->
  kind (rng_knd R).
Proof.
  introv Hr.
  destruct Hr; simpl; auto.
Qed.

Lemma rngs_knds_kinds : forall R,
  ranges R ->
  kinds (rngs_knds R).
Proof.
  introv Hrs.
  induction Hrs; simpl; auto using rng_knd_kind.
Qed.

(** Range lists have kinds of the same length *)

Lemma length_rngs_knds : forall Rs,
    length Rs = length (rngs_knds Rs).
Proof.
  intros.
  induction Rs; simpl; auto.
Qed.

(* *************************************************************** *)
(** * Properties of ranges *)

(** Ranges are stable by type substitution *)

Lemma rng_subst_range : forall R Zs Us,
  types Us -> range (rng_subst Zs Us R) <-> range R.
Proof.
  introv Ht.
  split.
  - introv Hr.
    induction R; simpl in Hr; auto.
    inversion Hr.
    rewrite typ_subst_type in *; auto.
  - introv Hr.
    induction Hr; simpl; auto.
    apply range_range; rewrite typ_subst_type; auto.
Qed.  

Lemma rng_subst_range_list : forall Rs Zs Us,
  types Us -> ranges (rng_subst_list Zs Us Rs) <-> ranges Rs.
Proof.
  introv Ht.
  induction Rs; simpl in *;
    split; introv Hrs; inversion Hrs; subst; auto.
  - rewrite rng_subst_range in *; auto.
    rewrite IHRs in *; auto.
  - rewrite <- rng_subst_range with (Zs := Zs) (Us := Us) in *; auto.
    rewrite <- IHRs in *; auto.
Qed.  

(* *************************************************************** *)
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

Lemma scheme_for_empty_type : forall T,
    type T -> scheme (sch_empty T).
Proof.
  introv Ht.
  rewrite <- scheme_empty_type.
  assumption.
Qed.

Hint Resolve scheme_for_empty_type.

(** Schemes are stable by type substitution *)

Lemma sch_subst_scheme : forall M Zs Us,
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
    inversion H as [? ? Hrs Ht]; subst.
    simpl in *.
    rewrite <- rng_subst_list_open_vars in Hrs; auto.
    rewrite rng_subst_range_list in Hrs; auto.
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
    inversion H as [? ? Hrs Ht]; subst.
    rewrite <- rng_subst_range_list
      with (Zs := Zs) (Us := Us) in Hrs; auto.
    rewrite rng_subst_list_open_vars in Hrs; auto.
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
  - rewrite sch_subst_scheme in *; auto.
    rewrite IHMs in *; auto.
  - rewrite <- sch_subst_scheme with (Zs := Zs) (Us := Us) in *; auto.
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

(* *************************************************************** *)
(** * Extra lemmas about the [ok] predicate *)

Lemma ok_middle : forall A E1 E2 x (v : A),
  ok (E1 & E2) ->
  x # (E1 & E2) ->
  ok (E1 & x ~ v & E2).
Proof.
  introv Hok Hn.
  induction E2 using env_ind;
    autorewrite with rew_env_concat in *;
    autorewrite with rew_env_dom in *; auto.
  destruct (ok_push_inv Hok).
  auto.
Qed.

Lemma ok_concat : forall A (E1 : LibEnv.env A) E2,
    ok E1 -> ok E2 ->
    disjoint (dom E1) (dom E2) ->
    ok (E1 & E2).
Proof.
  introv Hok1 Hok2 Hd.
  induction E2 using env_ind;
    autorewrite with rew_env_concat in *;
    autorewrite with rew_env_dom in *; auto.
  destruct (ok_push_inv Hok2).
  auto.
Qed.

Lemma ok_concat_inv : forall A (E1 : LibEnv.env A) E2,
    ok (E1 & E2) ->
    disjoint (dom E1) (dom E2) /\ ok E1 /\ ok E2.
Proof.
  introv Hok.
  splits; eauto using ok_concat_inv_l, ok_concat_inv_r.
  induction E2 using env_ind;
    autorewrite with rew_env_concat in *;
    autorewrite with rew_env_dom in *; auto.
  destruct (ok_push_inv Hok).
  autorewrite with rew_env_dom in *.
  auto.
Qed.

(* *************************************************************** *)
(** * Properties of type environments *)

Lemma ok_from_type_environment : forall E,
  type_environment E -> ok E.
Proof.
  introv He.
  induction He; auto. 
Qed.

(* Constructor for concatenations *)

Lemma type_environment_concat : forall E1 E2,
    type_environment E1 ->
    type_environment E2 ->
    ok (E1 & E2) ->
    type_environment (E1 & E2).
Proof.
  introv He1 He2 Hok.
  induction He2;
    autorewrite with rew_env_concat in *; auto.
  remember (E1 & E & X ~ R) as E3.
  destruct Hok; auto.
  destruct (eq_push_inv HeqE3) as [? [? ?]]; subst; auto.
Qed.

(* Constructors for singles and sch_bind_rngs *)

Lemma type_environment_push_singles : forall E Xs Rs,
    type_environment E ->
    fresh (dom E) (length Rs) Xs ->
    ranges Rs ->
    type_environment (E & Xs ~* Rs).
Proof.
  introv He Hf Hrs.
  generalize dependent Rs.
  generalize dependent E.
  induction Xs; introv He Hf Hrs; simpl.
  - rewrite (fresh_length_nil _ _ Hf).
    rewrite singles_nil.
    autorewrite with rew_env_concat; auto.
  - destruct Rs; simpl in *; destruct Hf.
    inversion Hrs; subst.
    autorewrite with rew_env_concat.
    apply type_environment_push;
      autorewrite with rew_tenv_dom; try symmetry;
        eauto using fresh_length.
Qed.

Lemma type_environment_singles : forall Xs Rs,
    fresh \{} (length Rs) Xs ->
    ranges Rs ->
    type_environment (Xs ~* Rs).
Proof.
  introv Hf Hrs.
  rewrite <- concat_empty_l.
  apply type_environment_push_singles;
    autorewrite with rew_tenv_dom; auto.
Qed.

Lemma type_environment_push_ranges : forall E Xs M,
    type_environment E ->
    fresh (dom E) (sch_arity M) Xs ->
    scheme M ->
    type_environment (E & Xs ~: M).
Proof.
  introv He Hf Hs.
  destruct Hs as [L ? H].
  destruct M as [Rs T].
  unfold bind_sch_ranges.
  simpl in *.
  apply type_environment_push_singles;
    rewrite ?rng_open_vars_list_length; auto.
  pick_freshes (length Xs) Ys.
  unfold rng_open_vars_list.
  rewrite rng_subst_list_intro with (Xs := Ys);
    rewrite ?length_typ_fvars; auto.
  rewrite rng_subst_range_list; auto.
  specialize (H Ys).
  fresh_length Hf as Hl.
  rewrite Hl in Hf.
  destruct H; auto.
Qed.

Lemma type_environment_ranges : forall Xs M,
    fresh \{} (sch_arity M) Xs ->
    scheme M ->
    type_environment (Xs ~: M).
Proof.
  introv Hf Hs.
  rewrite <- concat_empty_l.
  apply type_environment_push_ranges;
    autorewrite with rew_tenv_dom; auto.
Qed.

(* Inversions for various constructors *)

Lemma type_environment_push_inv : forall E X R,
    type_environment (E & X ~ R) ->
    type_environment E /\ X # E /\ range R.
Proof.
  introv He.
  remember (E & X ~ R) as Ex.
  destruct He.
  - apply empty_push_inv in HeqEx; contradiction.
  - destruct (eq_push_inv HeqEx) as [? [? ?]]; subst.
    split; auto.
Qed.

Lemma type_environment_concat_inv : forall E1 E2,
    type_environment (E1 & E2) ->
    type_environment E1 /\ type_environment E2.
Proof.
  introv He.
  remember (E1 & E2) as Es.
  generalize dependent E2.
  generalize dependent E1.
  induction He; introv HeqEs.
  - destruct (empty_concat_inv HeqEs); subst; auto.
  - induction E2 using env_ind;
      autorewrite with rew_env_concat in *; subst; auto.
    destruct (eq_push_inv HeqEs) as [? [? ?]]; subst.
    specialize (IHHe E1 E2).
    intuition auto.
Qed.

Lemma type_environment_singles_inv : forall E Xs Rs,
    type_environment (E & Xs ~* Rs) ->
    length Rs = length Xs ->
    type_environment E /\ fresh (dom E) (length Rs) Xs /\ ranges Rs.
Proof.
  introv He Hl.
  generalize dependent Rs.
  induction Xs; introv He Hl; destruct Rs; try discriminate;
    simpl in *; autorewrite with rew_env_concat in *; auto.
  destruct (type_environment_push_inv He) as [He2 [? ?]].
  destruct (type_environment_concat_inv He2) as [? ?].
  inversion Hl.
  assert (a # Xs ~* Rs)
    by eauto using ok_middle_inv_r, ok_from_type_environment.
  assert (ok (E & Xs ~* Rs))
    by eauto using ok_remove, ok_from_type_environment.
  destruct IHXs with (Rs := Rs) as [? [? ?]];
    auto using type_environment_concat.
  autorewrite with rew_tenv_dom in *;
    auto using fresh_from_notin.
Qed.
   
(* Middle constructors and inversions *)

Lemma type_environment_middle : forall E1 E2 X R,
    type_environment (E1 & E2) ->
    range R ->
    X # E1 & E2 ->
    type_environment (E1 & X ~ R & E2).
Proof.
  introv He Hs Hn.
  destruct (type_environment_concat_inv He) as [? ?].
  auto using type_environment_concat, ok_middle,
    ok_from_type_environment.
Qed.

Lemma type_environment_middle_inv : forall E1 E2 X R,
    type_environment (E1 & X ~ R & E2) ->
    type_environment (E1 & E2) /\ range R /\ X # E1 & E2.
Proof.
  introv He.
  assert (ok (E1 & X ~ R & E2)) as Hok
    by auto using ok_from_type_environment.
  destruct (ok_middle_inv Hok).
  apply ok_remove in Hok.
  destruct (type_environment_concat_inv He) as [He2 ?].
  destruct (type_environment_push_inv He2) as [? [? ?]].
  auto using type_environment_concat.
Qed.

Lemma type_environment_middle_singles : forall E1 E2 Xs Rs,
    type_environment (E1 & E2) ->
    fresh (dom E1 \u dom E2) (length Rs) Xs ->
    ranges Rs ->
    type_environment (E1 & Xs ~* Rs & E2).
Proof.
  introv He Hf Hrs.
  destruct (type_environment_concat_inv He).
  destruct (ok_concat_inv (ok_from_type_environment He))
    as [? [? ?]].
  fresh_length Hf as Hl.
  assert (type_environment (E1 & Xs ~* Rs))
    by auto using type_environment_push_singles.
  apply type_environment_concat; auto.
  apply ok_concat; auto using ok_from_type_environment.
  autorewrite with rew_tenv_dom; auto.
Qed.

Lemma type_environment_middle_singles_inv : forall E1 E2 Xs Rs,
    type_environment (E1 & Xs ~* Rs & E2) ->
    length Rs = length Xs ->
    type_environment (E1 & E2)
    /\ fresh (dom E1 \u dom E2) (length Rs) Xs /\ ranges Rs.
Proof.
  introv He Hl.
  destruct (type_environment_concat_inv He) as [He2 ?].
  destruct (type_environment_singles_inv He2) as [? [? ?]];
    auto.
  destruct (ok_concat_inv (ok_from_type_environment He)) as [? [? ?]].
  split.
  - eauto using type_environment_concat,
      ok_remove, ok_from_type_environment.
  - autorewrite with rew_tenv_dom in *;
      auto using fresh_disjoint.
Qed.
  
Lemma type_environment_middle_ranges : forall E1 E2 Xs M,
    type_environment (E1 & E2) ->
    fresh (dom (E1 & E2)) (sch_arity M) Xs ->
    scheme M ->
    type_environment (E1 & Xs ~: M & E2).
Proof.
  introv He Hf Hs.
  autorewrite with rew_tenv_dom in Hf.
  fresh_length Hf as Hl.
  destruct (type_environment_concat_inv He) as [? ?].
  assert (type_environment (E1 & Xs ~: M))
    by auto using type_environment_push_ranges.
  assert (ok (E1 & E2)) as Hok
    by auto using ok_from_type_environment.
  destruct (ok_concat_inv Hok) as [? [? ?]].
  apply type_environment_concat; auto.
  apply ok_concat;
   autorewrite with rew_tenv_dom;
     auto using ok_from_type_environment.
Qed.
 
(* Various parital inversions *)

Lemma type_environment_concat_inv_l : forall E1 E2,
    type_environment (E1 & E2) ->
    type_environment E1.
Proof.
  introv He.
  destruct (type_environment_concat_inv He).
  assumption.
Qed.

Lemma type_environment_concat_inv_r : forall E1 E2,
    type_environment (E1 & E2) ->
    type_environment E2.
Proof.
  introv He.
  destruct (type_environment_concat_inv He).
  assumption.
Qed.

Lemma type_environment_remove : forall E1 E2 E3,
    type_environment (E1 & E2 & E3) ->
    type_environment (E1 & E3).
Proof.
  introv He.
  destruct (type_environment_concat_inv He) as [He2 ?].
  destruct (type_environment_concat_inv He2) as [? ?].
  eauto using type_environment_concat,
    ok_remove, ok_from_type_environment.
Qed.

Lemma type_environment_middle_inv_fresh : forall E1 E2 X R,
    type_environment (E1 & X ~ R & E2) ->
    X # (E1 & E2).
Proof.
  introv He.
  assert (ok (E1 & X ~ R & E2)) as Hok
    by auto using ok_from_type_environment.
  destruct (ok_middle_inv Hok).
  auto.
Qed.

Lemma type_environment_push_inv_fresh : forall E1 X R,
    type_environment (E1 & X ~ R) ->
    X # E1.
Proof.
  introv He.
  rewrite <- concat_empty_r in He.
  rewrite <- (concat_empty_r E1).
  eauto using type_environment_middle_inv_fresh.
Qed.

Lemma type_environment_push_inv_range : forall E1 X R,
    type_environment (E1 & X ~ R) ->
    range R.
Proof.
  introv He.
  destruct (type_environment_push_inv He) as [? [? ?]].
  assumption.
Qed.

Lemma type_environment_middle_inv_env : forall E1 E2 X R,
    type_environment (E1 & X ~ R & E2) ->
    type_environment (E1 & E2).
Proof.
  introv He.
  destruct (type_environment_concat_inv He) as [He2 ?].
  destruct (type_environment_concat_inv He2) as [? ?].
  eauto using type_environment_concat,
    ok_remove, ok_from_type_environment.
Qed.

Lemma type_environment_middle_inv_range : forall E1 E2 X R,
    type_environment (E1 & X ~ R & E2) ->
    range R.
Proof.
  introv He.
  destruct (type_environment_concat_inv He) as [He2 ?].
  eauto using type_environment_push_inv_range.
Qed.

Lemma type_environment_middle_singles_swap : forall E1 E2 Xs Rs Ys,
  length Xs = length Rs ->
  fresh (dom E1 \u dom E2) (length Rs) Ys ->
  type_environment (E1 & Xs ~* Rs & E2) ->
  type_environment (E1 & Ys ~* Rs & E2).
Proof.
  introv Hl Hf He.
  destruct (type_environment_middle_singles_inv He)
    as [? [? ?]]; auto using type_environment_middle_singles.
Qed.

Lemma binds_tenv_weakening : forall E1 E2 E3 X R,
    binds X R (E1 & E3) ->
    type_environment (E1 & E2 & E3) ->
    binds X R (E1 & E2 & E3).
Proof.
  introv Hb He.
  assert (ok (E1 & E2 & E3))
    by auto using ok_from_type_environment.
  apply binds_weaken; assumption.
Qed.

Lemma type_environment_push_weakening : forall E1 E2 E3 X R,
    X # E2 ->
    type_environment (E1 & E3 & X ~ R) ->
    type_environment (E1 & E2 & E3) ->
    type_environment (E1 & E2 & E3 & X ~ R).
Proof.
  introv Hin He1 He2.
  destruct (type_environment_push_inv He1) as [? [? ?]].
  auto.
Qed.

Lemma type_environment_singles_weakening : forall E1 E2 E3 Xs Rs,
    fresh (dom E2) (length Rs) Xs ->
    type_environment (E1 & E3 & Xs ~* Rs) ->
    type_environment (E1 & E2 & E3) ->
    type_environment (E1 & E2 & E3 & Xs ~* Rs).
Proof.
  introv Hf He1 He2.
  fresh_length Hf as Hl.
  destruct (type_environment_singles_inv He1)
    as [? [? ?]]; auto.
  apply type_environment_push_singles; auto.
  autorewrite with rew_tenv_dom in *.
  auto.
Qed.
 
Lemma type_environment_ranges_weakening : forall E1 E2 E3 Xs M,
    fresh (dom E2) (sch_arity M) Xs ->
    type_environment (E1 & E3 & Xs ~: M) ->
    type_environment (E1 & E2 & E3) ->
    type_environment (E1 & E2 & E3 & Xs ~: M).
Proof.
  introv Hf He1 He2.
  destruct M as [Rs ?].
  unfold bind_sch_ranges in *.
  simpl in *.
  apply type_environment_singles_weakening; auto.
  rewrite <- length_rng_open_vars_list.
  assumption.
Qed.

Lemma tenv_subst_type_environment : forall Xs Us E,
    types Us -> type_environment E ->
    type_environment (tenv_subst Xs Us E).
Proof.
  introv Ht He.
  induction He; autorewrite with rew_tenv_subst; auto.
  apply type_environment_push;
    rewrite ?rng_subst_range;
      autorewrite with rew_tenv_dom; auto.
Qed.

Lemma range_from_tenv : forall E X R,
    type_environment E ->
    binds X R E ->
    range R.
Proof.
  introv He Hb.
  induction He.
  - apply binds_empty_inv in Hb; contradiction.
  - destruct (binds_push_inv Hb) as [[Hx Hbnd]|[Hx Hbnd]];
      auto.
    inversion Hbnd; subst; assumption.
Qed.

(* *************************************************************** *)
(** * Properties of environments *)

Lemma ok_from_environment : forall D,
  environment D -> ok D.
Proof.
  introv He.
  induction He; auto. 
Qed.

(* Constructor for pushing twice *)

Lemma environment_push2 : forall E x1 x2 M1 M2,
    environment E ->
    scheme M1 ->
    scheme M2 ->
    x1 # E ->
    x2 # E ->
    x1 <> x2 ->
    environment (E & x1 ~ M1 & x2 ~ M2).
Proof.
  introv He Hs1 Hs2 Hf1 Hf2 Hn.
  auto.
Qed.

(* Constructor for concatenations *)

Lemma environment_concat : forall D1 D2,
    environment D1 ->
    environment D2 ->
    ok (D1 & D2) ->
    environment (D1 & D2).
Proof.
  introv He1 He2 Hok.
  induction He2;
    autorewrite with rew_env_concat in *; auto.
  remember (D1 & E & x ~ M) as D3.
  destruct Hok; auto.
  destruct (eq_push_inv HeqD3) as [? [? ?]]; subst; auto.
Qed.

Lemma environment_singles : forall D xs Ms,
    environment D ->
    fresh (dom D) (length Ms) xs ->
    schemes Ms ->
    environment (D & xs ~* Ms).
Proof.
  introv He Hf Hss.
  generalize dependent Ms.
  generalize dependent D.
  induction xs; introv He Hf Hss; simpl.
  - rewrite (fresh_length_nil _ _ Hf).
    rewrite singles_nil.
    autorewrite with rew_env_concat; auto.
  - destruct Ms; simpl in *; destruct Hf.
    inversion Hss; subst.
    rewrite singles_cons, concat_assoc.
    apply environment_push;
      autorewrite with rew_env_dom;
        eauto using fresh_length.
Qed.

(* Inversions for various constructors *)

Lemma environment_push_inv : forall D x M,
    environment (D & x ~ M) ->
    environment D /\ x # D /\ scheme M.
Proof.
  introv He.
  remember (D & x ~ M) as Dx.
  destruct He.
  - apply empty_push_inv in HeqDx; contradiction.
  - destruct (eq_push_inv HeqDx) as [? [Hb ?]].
    inversion Hb; subst.
    auto.
Qed.

Lemma environment_concat_inv : forall D1 D2,
    environment (D1 & D2) ->
    environment D1 /\ environment D2.
Proof.
  introv He.
  remember (D1 & D2) as Ds.
  generalize dependent D2.
  generalize dependent D1.
  induction He; introv HeqDs.
  - destruct (empty_concat_inv HeqDs); subst.
    split; auto.
  - induction D2 using env_ind;
      autorewrite with rew_env_concat in *; subst.
    + intuition auto.
    + destruct (eq_push_inv HeqDs) as [? [? ?]]; subst.
      specialize (IHHe D1 D2).
      intuition auto.
Qed.

Lemma environment_singles_inv : forall D xs Ms,
    environment (D & xs ~* Ms) ->
    length Ms = length xs ->
    environment D /\ fresh (dom D) (length Ms) xs /\ schemes Ms.
Proof.
  introv He Hl.
  generalize dependent Ms.
  induction xs; introv He Hl; induction Ms; try discriminate;
    simpl in *; autorewrite with rew_env_concat in *; auto.
  destruct (environment_push_inv He) as [He2 [? ?]].
  destruct (environment_concat_inv He2) as [? ?].
  inversion Hl.
  assert (a # xs ~* Ms)
    by eauto using ok_middle_inv_r, ok_from_environment.
  assert (ok (D & xs ~* Ms))
    by eauto using ok_remove, ok_from_environment.    
  destruct IHxs with (Ms := Ms) as [? [? ?]];
    auto using environment_concat.
  autorewrite with rew_env_dom in *;
    auto using fresh_from_notin.
Qed.
    
(* Middle constructors and inversions *)

Lemma environment_middle : forall D1 D2 x M,
    environment (D1 & D2) ->
    scheme M ->
    x # D1 & D2 ->
    environment (D1 & x ~ M & D2).
Proof.
  introv He Hs Hn.
  destruct (environment_concat_inv He) as [? ?].
  auto using environment_concat, ok_middle, ok_from_environment.
Qed.

Lemma environment_middle_inv : forall D1 D2 x M,
    environment (D1 & x ~ M & D2) ->
    environment (D1 & D2) /\ scheme M /\ x # D1 & D2.
Proof.
  introv He.
  assert (ok (D1 & x ~ M & D2)) as Hok
    by auto using ok_from_environment.
  destruct (ok_middle_inv Hok).
  apply ok_remove in Hok.
  destruct (environment_concat_inv He) as [He2 ?].
  destruct (environment_push_inv He2) as [? [? ?]].
  auto using environment_concat.
Qed.
  
Lemma environment_middle_singles : forall D1 D2 xs Ms,
    environment (D1 & D2) ->
    fresh (dom D1 \u dom D2) (length Ms) xs ->
    schemes Ms ->
    environment (D1 & xs ~* Ms & D2).
Proof.
  introv He Hf Hss.
  destruct (environment_concat_inv He).
  destruct (ok_concat_inv (ok_from_environment He)) as [? [? ?]].
  fresh_length Hf as Hl.
  assert (environment (D1 & xs ~* Ms))
    by auto using environment_singles.
  apply environment_concat; auto.
  apply ok_concat; auto using ok_from_environment.
  autorewrite with rew_env_dom; auto.
Qed.

Lemma environment_middle_singles_inv : forall D1 D2 xs Ms,
    environment (D1 & xs ~* Ms & D2) ->
    length Ms = length xs ->
    environment (D1 & D2)
    /\ fresh (dom D1 \u dom D2) (length Ms) xs /\ schemes Ms.
Proof.
  introv He Hl.
  destruct (environment_concat_inv He) as [He2 ?].
  destruct (environment_singles_inv He2) as [? [? ?]]; auto.
  destruct (ok_concat_inv (ok_from_environment He)) as [? [? ?]].
  split.
  - eauto using environment_concat,
      ok_remove, ok_from_environment.
  - autorewrite with rew_env_dom in *; auto using fresh_disjoint.
Qed.
  
(* Various parital inversions *)

Lemma environment_concat_inv_l : forall D1 D2,
    environment (D1 & D2) ->
    environment D1.
Proof.
  introv He.
  destruct (environment_concat_inv He).
  assumption.
Qed.

Lemma environment_concat_inv_r : forall D1 D2,
    environment (D1 & D2) ->
    environment D2.
Proof.
  introv He.
  destruct (environment_concat_inv He).
  assumption.
Qed.

Lemma environment_remove : forall D1 D2 D3,
    environment (D1 & D2 & D3) ->
    environment (D1 & D3).
Proof.
  introv He.
  destruct (environment_concat_inv He) as [He2 ?].
  destruct (environment_concat_inv He2) as [? ?].
  eauto using environment_concat, ok_remove, ok_from_environment.
Qed.

Lemma environment_middle_inv_fresh : forall D1 D2 x M,
    environment (D1 & x ~ M & D2) ->
    x # (D1 & D2).
Proof.
  introv He.
  assert (ok (D1 & x ~ M & D2)) as Hok
    by auto using ok_from_environment.
  destruct (ok_middle_inv Hok).
  auto.
Qed.

Lemma environment_push_inv_fresh : forall D x M,
    environment (D & x ~ M) ->
    x # D.
Proof.
  introv He.
  rewrite <- concat_empty_r in He.
  rewrite <- (concat_empty_r D).
  eauto using environment_middle_inv_fresh.
Qed.

Lemma environment_push_inv_scheme : forall D X M,
    environment (D & X ~ M) ->
    scheme M.
Proof.
  introv He.
  destruct (environment_push_inv He) as [? [? ?]].
  assumption.
Qed.

Lemma environment_middle_inv_env : forall D1 D2 x M,
    environment (D1 & x ~ M & D2) ->
    environment (D1 & D2).
Proof.
  introv He.
  destruct (environment_concat_inv He) as [He2 ?].
  destruct (environment_concat_inv He2) as [? ?].
  eauto using environment_concat, ok_remove, ok_from_environment.
Qed.

Lemma environment_middle_inv_scheme : forall D1 D2 x M,
    environment (D1 & x ~ M & D2) ->
    scheme M.
Proof.
  introv He.
  destruct (environment_concat_inv He) as [He2 ?].
  eauto using environment_push_inv_scheme.
Qed.

Lemma binds_env_weakening : forall D1 D2 D3 X B,
    binds X B (D1 & D3) ->
    environment (D1 & D2 & D3) ->
    binds X B (D1 & D2 & D3).
Proof.
  introv Hb He.
  assert (ok (D1 & D2 & D3))
    by auto using ok_from_environment.
  apply binds_weaken; assumption.
Qed.

Lemma environment_push_weakening : forall D1 D2 D3 x M,
    x # D2 ->
    environment (D1 & D3 & x ~ M) ->
    environment (D1 & D2 & D3) ->
    environment (D1 & D2 & D3 & x ~ M).
Proof.
  introv Hin He1 He2.
  destruct (environment_push_inv He1) as [? [? ?]].
  auto.
Qed.

Lemma env_subst_environment : forall Xs Us D,
    types Us -> environment D ->
    environment (env_subst Xs Us D).
Proof.
  introv Ht He.
  induction He; autorewrite with rew_env_subst; auto.
  apply environment_push;
    autorewrite with rew_env_dom; auto.
  rewrite sch_subst_scheme; auto.
Qed.

Lemma scheme_from_env : forall D x M,
    environment D ->
    binds x M D ->
    scheme M.
Proof.
  introv He Hb.
  induction He.
  - apply binds_empty_inv in Hb; contradiction.
  - destruct (binds_push_inv Hb) as [[Hx Hbnd]|[Hx Hbnd]];
      subst; auto.
Qed.

(* *************************************************************** *)
(** * Properties of stores and store types *)

Lemma ok_from_store_type : forall P,
  store_type P -> ok P.
Proof.
  introv Hs.
  induction Hs; auto. 
Qed.

Lemma binds_store_type_weakening : forall P1 P2 P3 X T,
    binds X T (P1 & P3) ->
    store_type (P1 & P2 & P3) ->
    binds X T (P1 & P2 & P3).
Proof.
  introv Hb He.
  assert (ok (P1 & P2 & P3))
    by auto using ok_from_store_type.
  apply binds_weaken; assumption.
Qed.

Lemma store_type_retract : forall P1 P2,
    store_type (P1 & P2) -> store_type P1.
Proof.
  introv Hs.
  induction P2 using env_ind;
    autorewrite with rew_env_concat in *; auto.
  remember (P1 & P2 & x ~ v) as P3.
  destruct Hs.
  - destruct (empty_concat_inv HeqP3) as [_ Hem].
    apply empty_single_inv in Hem.
    contradiction.
  - destruct (eq_push_inv HeqP3) as [_ [_ Hem]].
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

(* ****************************************************** *)
(** * Well-formedness of judgement subjects *)

Lemma wellformed_kinding : forall E T K,
    kinding E T K -> type T.
Proof.
  introv Hk.
  induction Hk; auto.
Qed.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : kinding _ T _ |- _ =>
      apply (wellformed_kinding H)
  end : wellformed.

Lemma wellformed_kindings : forall E Ts Ks,
    kindings E Ts Ks -> types Ts.
Proof.
  introv Hks.
  induction Hks; auto with wellformed.
Qed.

Hint Extern 1 (types ?Ts) =>
  match goal with
  | H : kindings _ Ts _ |- _ =>
      apply (wellformed_kindings H)
  end : wellformed.

Lemma wellformed_type_equal_core_1 : forall E T1 T2 K,
    type_equal_core E T1 T2 K -> type T1.
Proof.
  introv Hte.
  induction Hte; auto with wellformed.
Qed.

Lemma wellformed_type_equal_core_2 : forall E T1 T2 K,
    type_equal_core E T1 T2 K -> type T2.
Proof.
  introv Hte.
  induction Hte; auto with wellformed.
Qed.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_core _ T _ _ |- _ =>
      apply (wellformed_type_equal_core_1 H)
  | H : type_equal_core _ _ T _ |- _ =>
      apply (wellformed_type_equal_core_2 H)
  end : wellformed.

Lemma wellformed_type_equal_symm_1 : forall E T1 T2 K,
    type_equal_symm E T1 T2 K -> type T1.
Proof.
  introv Hte.
  induction Hte; auto with wellformed.
Qed.

Lemma wellformed_type_equal_symm_2 : forall E T1 T2 K,
    type_equal_symm E T1 T2 K -> type T2.
Proof.
  introv Hte.
  induction Hte; auto with wellformed.
Qed.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_symm _ T _ _ |- _ =>
      apply (wellformed_type_equal_symm_1 H)
  | H : type_equal_symm _ _ T _ |- _ =>
      apply (wellformed_type_equal_symm_2 H)
  end : wellformed.

Lemma wellformed_type_equal_cong_1 : forall E T1 T2 K,
    type_equal_cong E T1 T2 K -> type T1.
Proof.
  introv Hte.
  induction Hte; auto with wellformed.
Qed.

Lemma wellformed_type_equal_cong_2 : forall E T1 T2 K,
    type_equal_cong E T1 T2 K -> type T2.
Proof.
  introv Hte.
  induction Hte; auto with wellformed.
Qed.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_cong _ T _ _ |- _ =>
      apply (wellformed_type_equal_cong_1 H)
  | H : type_equal_cong _ _ T _ |- _ =>
      apply (wellformed_type_equal_cong_2 H)
  end : wellformed.

Lemma wellformed_type_equal_1 : forall E T1 T2 K,
    type_equal E T1 T2 K -> type T1.
Proof.
  introv Hte.
  induction Hte; auto with wellformed.
Qed.

Lemma wellformed_type_equal_2 : forall E T1 T2 K,
    type_equal E T1 T2 K -> type T2.
Proof.
  introv Hte.
  induction Hte; auto with wellformed.
Qed.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal _ T _ _ |- _ =>
      apply (wellformed_type_equal_1 H)
  | H : type_equal _ _ T _ |- _ =>
      apply (wellformed_type_equal_2 H)
  end : wellformed.

Lemma wellformed_subtype_1 : forall E T1 T2 cs,
    subtype E T1 T2 cs -> type T1.
Proof.
  introv Hs.
  induction Hs; auto with wellformed.
Qed.

Lemma wellformed_subtype_2 : forall E T1 T2 cs,
    subtype E T1 T2 cs -> type T2.
Proof.
  introv Hs.
  destruct Hs.
  assert (type (typ_meet T1 T2)) as Ht
    by auto with wellformed.
  inversion Ht; auto.
Qed.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : subtype _ T _ _ |- _ =>
      apply (wellformed_subtype_1 H)
  | H : subtype _ _ T _ |- _ =>
      apply (wellformed_subtype_2 H)
  end : wellformed.

Lemma wellformed_valid_range: forall E R,
    valid_range E R -> range R.
Proof.
  introv Hr.
  induction Hr; auto with wellformed.
Qed.

Hint Extern 1 (range ?R) =>
  match goal with
  | H : valid_range _ R |- _ =>
      apply (wellformed_valid_range H)
  end : wellformed.

Lemma wellformed_valid_ranges: forall E Rs,
    valid_ranges E Rs -> ranges Rs.
Proof.
  introv Hr.
  induction Hr; auto with wellformed.
Qed.

Hint Extern 1 (ranges ?Rs) =>
  match goal with
  | H : valid_ranges _ Rs |- _ =>
      apply (wellformed_valid_ranges H)
  end : wellformed.

Lemma wellformed_valid_ranges_and_type: forall E Rs T,
    valid_ranges_and_type E Rs T -> ranges_and_type Rs T.
Proof.
  introv Hr.
  induction Hr; auto with wellformed.
Qed.

Hint Extern 1 (ranges_and_type ?Rs ?T) =>
  match goal with
  | H : valid_ranges_and_type _ Rs T |- _ =>
      apply (wellformed_valid_ranges_and_type H)
  end : wellformed.

Lemma wellformed_valid_ranges_and_type_1: forall E Rs T,
    valid_ranges_and_type E Rs T -> ranges Rs.
Proof.
  introv Hr.
  induction Hr; auto with wellformed.
Qed.

Hint Extern 1 (ranges ?Rs) =>
  match goal with
  | H : valid_ranges_and_type _ Rs _ |- _ =>
      apply (wellformed_valid_ranges_and_type_1 H)
  end : wellformed.

Lemma wellformed_valid_ranges_and_type_2: forall E Rs T,
    valid_ranges_and_type E Rs T -> type T.
Proof.
  introv Hr.
  induction Hr; auto with wellformed.
Qed.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : valid_ranges _ _ T |- _ =>
      apply (wellformed_valid_ranges_and_type_2 H)
  end : wellformed.

Lemma wellformed_valid_scheme: forall E M,
    valid_scheme E M -> scheme M.
Proof.
  introv Hs.
  induction Hs; auto with wellformed fresh.
Qed.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H : valid_scheme _ M |- _ =>
      apply (wellformed_valid_scheme H)
  end : wellformed.

Lemma wellformed_valid_schemes: forall E Ms,
    valid_schemes E Ms -> schemes Ms.
Proof.
  introv Hs.
  induction Hs; auto with wellformed.
Qed.

Hint Extern 1 (schemes ?Ms) =>
  match goal with
  | H : valid_schemes _ Ms |- _ =>
      apply (wellformed_valid_schemes H)
  end : wellformed.

Lemma wellformed_valid_tenv_aux: forall E1 E2,
    valid_tenv_aux E1 E2 -> type_environment E2.
Proof.
  introv He.
  induction He; auto with wellformed.
Qed.

Hint Extern 1 (type_environment ?E) =>
  match goal with
  | H : valid_tenv_aux _ E |- _ =>
      apply (wellformed_valid_tenv_aux H)
  end : wellformed.

Lemma wellformed_valid_tenv: forall E,
    valid_tenv E -> type_environment E.
Proof.
  introv He.
  induction He; auto with wellformed.
Qed.

Hint Extern 1 (type_environment ?E) =>
  match goal with
  | H : valid_tenv E |- _ =>
      apply (wellformed_valid_tenv H)
  end : wellformed.

Lemma wellformed_ranging: forall E T R,
    ranging E T R -> type T.
Proof.
  introv Hr.
  induction Hr; auto with wellformed.
Qed.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : ranging _ T _ |- _ =>
      apply (wellformed_ranging H)
  end : wellformed.

Lemma wellformed_rangings: forall E Ts Rs,
    rangings E Ts Rs -> types Ts.
Proof.
  introv Hr.
  induction Hr; auto with wellformed.
Qed.

Hint Extern 1 (types ?Ts) =>
  match goal with
  | H : rangings _ Ts _ |- _ =>
      apply (wellformed_rangings H)
  end : wellformed.

Lemma wellformed_valid_instance: forall E Ts M,
    valid_instance E Ts M -> types Ts.
Proof.
  introv Hi.
  induction Hi; auto with wellformed.
Qed.

Hint Extern 1 (types ?Ts) =>
  match goal with
  | H : valid_instance _ Ts _ |- _ =>
      apply (wellformed_valid_instance H)
  end : wellformed.

Lemma wellformed_valid_env: forall E D,
    valid_env E D -> environment D.
Proof.
  introv He.
  induction He; auto with wellformed.
Qed.

Hint Extern 1 (environment ?D) =>
  match goal with
  | H : valid_env _ D |- _ =>
      apply (wellformed_valid_env H)
  end : wellformed.

Lemma wellformed_valid_store_type: forall E P,
    valid_store_type E P -> store_type P.
Proof.
  introv Hs.
  induction Hs; auto with wellformed.
Qed.

Hint Extern 1 (store_type ?P) =>
  match goal with
  | H : valid_store_type _ P |- _ =>
      apply (wellformed_valid_store_type H)
  end : wellformed.

Lemma wellformed_value: forall t,
    value t -> term t.
Proof.
  introv Hv.
  induction Hv; auto with wellformed.
Qed.

Hint Extern 1 (term ?t) =>
  match goal with
  | H : value t |- _ =>
      apply (wellformed_value H)
  end : wellformed.

Lemma wellformed_typing: forall E D P t T,
    typing E D P t T -> term t.
Proof.
  introv Ht.
  induction Ht; auto with wellformed fresh.
Qed.

Hint Extern 1 (term ?t) =>
  match goal with
  | H : typing _ _ _ t _ |- _ =>
      apply (wellformed_typing H)
  end : wellformed.

Lemma wellformed_typing_scheme: forall E D P t M,
    typing_scheme E D P t M -> term t.
Proof.
  introv Hs.
  induction Hs; spec_fresh; auto with wellformed.
Qed.

Hint Extern 1 (term ?t) =>
  match goal with
  | H : typing_scheme _ _ _ t _ |- _ =>
      apply (wellformed_typing_scheme H)
  end : wellformed.

Lemma wellformed_typing_schemes: forall E D P ts Ms,
    typing_schemes E D P ts Ms -> terms ts.
Proof.
  introv Hs.
  induction Hs; auto with wellformed.
Qed.

Hint Extern 1 (terms ?ts) =>
  match goal with
  | H : typing_schemes _ _ _ ts _ |- _ =>
      apply (wellformed_typing_schemes H)
  end : wellformed.
