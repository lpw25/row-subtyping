(************************************************
 *          Row Subtyping - FreeVars            *
 *                 Leo White                    *
 ************************************************)

(* Functions calculating the free variables of
   types and terms, and associated lemmas *)

Set Implicit Arguments.
Require Import List LibLN Disjoint Utilities Definitions
  Opening.

Fixpoint typ_fv (T : typ) : vars :=
  match T with
  | typ_bvar i => \{}
  | typ_fvar x => \{x}
  | typ_constructor c T1 => typ_fv T1
  | typ_or cs1 cs2 T1 T2 => (typ_fv T1) \u (typ_fv T2)
  | typ_proj cs1 cs2 T1 => typ_fv T1
  | typ_variant T1 => typ_fv T1
  | typ_arrow T1 T2 => (typ_fv T1) \u (typ_fv T2)
  | typ_ref T1 => typ_fv T1
  | typ_unit => \{}
  | typ_prod T1 T2 => (typ_fv T1) \u (typ_fv T2)
  | typ_mu K T1 => typ_fv T1
  | typ_top K => \{}
  | typ_bot K => \{}
  | typ_meet T1 T2 => (typ_fv T1) \u (typ_fv T2)
  | typ_join T1 T2 => (typ_fv T1) \u (typ_fv T2)
  end.

Definition typ_fv_list Ts :=
  fold_right (fun T acc => typ_fv T \u acc) \{} Ts.

Definition rng_fv R :=
  typ_fv (rng_lower R) \u typ_fv (rng_upper R).

Definition rng_fv_list Rs :=
  fold_right (fun R acc => rng_fv R \u acc) \{} Rs.

Fixpoint sch_fv (M : sch) : vars :=
  rng_fv_list (sch_ranges M) \u typ_fv (sch_body M).

Definition sch_fv_list Ms :=
  fold_right (fun M acc => sch_fv M \u acc) \{} Ms.

Definition tenv_fv := 
  fv_in_values rng_fv.

Definition env_fv := 
  fv_in_values sch_fv.

Definition styp_fv :=
  fv_in_values typ_fv.

Definition qenv_fv (Q : qenv) :=
  fold_right
    (fun '(T1, T2, _) acc => typ_fv T1 \u typ_fv T2 \u acc)
    \{} Q.

Fixpoint trm_fv (t : trm) {struct t} : vars :=
  match t with
  | trm_bvar i => \{}
  | trm_fvar x => \{x}
  | trm_abs t1 => trm_fv t1
  | trm_let t1 t2 => (trm_fv t1) \u (trm_fv t2)
  | trm_app t1 t2 => (trm_fv t1) \u (trm_fv t2)
  | trm_constructor c t1 => trm_fv t1
  | trm_match t1 c t2 t3 => (trm_fv t1) \u (trm_fv t2) \u (trm_fv t3)
  | trm_destruct t1 c t2 => (trm_fv t1) \u (trm_fv t2)
  | trm_absurd t1 => trm_fv t1
  | trm_fix t1 => trm_fv t1
  | trm_unit => \{}
  | trm_prod t1 t2 => (trm_fv t1) \u (trm_fv t2)
  | trm_fst t1 => trm_fv t1
  | trm_snd t1 => trm_fv t1
  | trm_loc l => \{}
  | trm_ref t1 => trm_fv t1
  | trm_get t1 => trm_fv t1
  | trm_set t1 t2 => (trm_fv t1) \u (trm_fv t2)
  end.

Definition trm_fv_list Ts :=
  fold_right (fun T acc => trm_fv T \u acc) \{} Ts.

(* ****************************************************** *)
(** ** Instantiation of Tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : list var => from_list x) in
  let D := gather_vars_with (fun x : tenv => tenv_fv x) in
  let E := gather_vars_with (fun x : tenv => dom x) in
  let F := gather_vars_with (fun x : trm => trm_fv x) in
  let G := gather_vars_with (fun x : list trm => trm_fv_list x) in
  let H := gather_vars_with (fun x : typ => typ_fv x) in
  let I := gather_vars_with (fun x : list typ => typ_fv_list x) in
  let J := gather_vars_with (fun x : rng => rng_fv x) in
  let K := gather_vars_with (fun x : list rng => rng_fv_list x) in
  let L := gather_vars_with (fun x : env => env_fv x) in
  let M := gather_vars_with (fun x : env => dom x) in
  let N := gather_vars_with (fun x : styp => styp_fv x) in
  let O := gather_vars_with (fun x : qenv => qenv_fv x) in
  let P := gather_vars_with (fun x : sch => sch_fv x) in
  let Q := gather_vars_with (fun x : list sch => sch_fv_list x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H
            \u I \u J \u K \u L \u M \u N \u O \u P \u Q).

Tactic Notation "pick_fresh" ident(x) :=
  let L := gather_vars in (pick_fresh_gen L x).

Tactic Notation "pick_freshes" constr(n) ident(x) :=
  let L := gather_vars in (pick_freshes_gen L n x).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "exists_fresh" ident(x) ident(Hfr) :=
  exists_fresh_gen gather_vars x Hfr.

Ltac spec_fresh :=
  let L := gather_vars in spec_fresh_gen L.

(* *************************************************************** *)
(** ** Add improved constructor hints using tactics *)

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

Hint Extern 1 (valid_scheme _ _) =>
  let L' := gather_vars in
  let L' := beautify_fset L' in
  apply valid_scheme_c with (L := L').

Hint Extern 1 (typing _ _ _ (trm_abs _) _) =>
  let L' := gather_vars in
  let L' := beautify_fset L' in
  apply typing_abs with (L := L').

Hint Extern 1 (typing _ _ _ (trm_let _ _) _) =>
  let L' := gather_vars in
  let L' := beautify_fset L' in
  apply typing_let_val with (L := L').

Hint Extern 1 (typing _ _ _ (trm_let _ _) _) =>
  let L' := gather_vars in
  let L' := beautify_fset L' in
  apply typing_let with (L := L').

Hint Extern 1 (typing _ _ _ (trm_match _ _ _ _) _) =>
  let L' := gather_vars in
  let L' := beautify_fset L' in
  apply typing_match with (L := L').

Hint Extern 1 (typing _ _ _ (trm_destruct _ _ _) _) =>
  let L' := gather_vars in
  let L' := beautify_fset L' in
  apply typing_destruct with (L := L').

Hint Extern 1 (typing _ _ _ (trm_fix _) _) =>
  let L' := gather_vars in
  let L' := beautify_fset L' in
  apply typing_fix with (L := L').

Hint Extern 1 (typing_scheme _ _ _ _ _) =>
  let L' := gather_vars in
  let L' := beautify_fset L' in
  apply typing_scheme_c with (L := L').

(* **************************************************** *)
(** ** Terms *)

Lemma trm_fv_list_fvars : forall xs,
    trm_fv_list (trm_fvars xs) = from_list xs.
Proof.
  induction xs; auto; simpl.
  rewrite from_list_cons.
  rewrite IHxs.
  reflexivity.
Qed.

(* *************************************************************** *)
(** * Types *)

Lemma typ_fv_list_fvars : forall Xs,
    typ_fv_list (typ_fvars Xs) = from_list Xs.
Proof.
  induction Xs; auto; simpl.
  rewrite from_list_cons.
  rewrite IHXs.
  reflexivity.
Qed.

Lemma typ_fv_nth : forall Ts S i,
    subset (typ_fv (nth i Ts S)) (typ_fv S \u typ_fv_list Ts).
Proof.
  intros.
  generalize dependent i.
  induction Ts; intro; induction i; simpl in *;
    auto using subset_union_weak_l.
  - rewrite union_comm; rewrite <- union_assoc.
    apply subset_union_weak_l.
  - rewrite union_comm with (E := typ_fv a).
    rewrite union_assoc.
    unfold subset in *; intros; rewrite in_union; left.
    eauto.
Qed.

Lemma typ_open_rec_fv_inv : forall k Us T,
    subset (typ_fv T) (typ_fv (typ_open_rec k T Us)).
Proof.
  intros.
  generalize dependent k.
  induction T; intros; simpl;
    auto using subset_empty_l, subset_refl, subset_union_2.
Qed.

Lemma typ_open_fv_inv : forall Us T,
    subset (typ_fv T) (typ_fv (typ_open T Us)).
Proof.
  intros.
  unfold typ_open.
  apply typ_open_rec_fv_inv.
Qed.

Lemma typ_var_open_fv : forall k n Us T,
    subset (typ_fv (typ_var_open k Us n T))
           (typ_fv T \u typ_fv_list Us).
Proof.
  intros.
  generalize dependent n.
  induction k; intros; simpl.
  - apply typ_fv_nth.
  - destruct n.
    + apply subset_union_weak_l.
    + auto.
Qed.

Lemma typ_open_rec_fv : forall k Us T,
    subset (typ_fv (typ_open_rec k T Us))
           (typ_fv T \u typ_fv_list Us).
Proof.
  intros.
  generalize dependent k.
  induction T; intros; simpl;
    try rewrite union_distribute with (R := typ_fv_list Us);
    auto using subset_empty_l, subset_refl, subset_union_weak_l,
      subset_union_2.
  apply typ_var_open_fv.
Qed.

Lemma typ_open_fv : forall Us T,
    subset (typ_fv (typ_open T Us)) (typ_fv T \u typ_fv_list Us).
Proof.
  intros.
  unfold typ_open.
  apply typ_open_rec_fv.
Qed.

Lemma typ_open_fresh_fv : forall Xs n Us T,
    fresh (typ_fv T \u typ_fv_list Us) n Xs ->
    fresh (typ_fv (typ_open T Us)) n Xs.
Proof.
  introv Hf.
  generalize dependent n.
  induction Xs; intros n Hf; subst;
    destruct n; simpl in *; auto.
  destruct Hf as [Hn Hf].
  split.
  - eauto using notin_subset, typ_open_fv.
  - assert (fresh (typ_fv (typ_open T Us)) n Xs) by auto.
    auto.
Qed.

Lemma typ_open_vars_fv_inv : forall Ys T,
     subset (typ_fv T) (typ_fv (typ_open_vars T Ys)).
Proof.
  intros.
  apply typ_open_fv_inv.
Qed.

Lemma typ_open_vars_fv : forall Ys T,
    subset (typ_fv (typ_open_vars T Ys)) (typ_fv T \u from_list Ys).
Proof.
  intros.
  rewrite <- typ_fv_list_fvars.
  apply typ_open_fv.
Qed.

(* *************************************************************** *)
(** ** Ranges *)

Lemma rng_open_fv_inv : forall Us R,
    subset (rng_fv R) (rng_fv (rng_open R Us)).
Proof.
  intros.
  induction R; simpl; auto using subset_empty_l. 
  apply subset_union_2; apply typ_open_fv_inv.
Qed.

Lemma rng_open_fv : forall Us R,
    subset (rng_fv (rng_open R Us)) (rng_fv R \u typ_fv_list Us).
Proof.
  intros.
  destruct R; unfold rng_open, rng_fv; simpl.
  rewrite union_distribute.
  apply subset_union_2; apply typ_open_fv.
Qed.  

Lemma rng_open_vars_fv_inv : forall Ys R,
     subset (rng_fv R) (rng_fv (rng_open_vars R Ys)).
Proof.
  intros.
  apply rng_open_fv_inv.
Qed.

Lemma rng_open_vars_fv : forall Ys R,
    subset (rng_fv (rng_open_vars R Ys)) (rng_fv R \u from_list Ys).
Proof.
  intros.
  rewrite <- typ_fv_list_fvars.
  apply rng_open_fv.
Qed.

Lemma rng_open_list_fv_inv : forall Us Rs,
    subset (rng_fv_list Rs) (rng_fv_list (rng_open_list Rs Us)).
Proof.
  intros.
  induction Rs; simpl; auto using subset_empty_l.
  apply subset_union_2; auto.
  apply rng_open_fv_inv.
Qed.

Lemma rng_open_list_fv : forall Us Rs,
    subset (rng_fv_list (rng_open_list Rs Us))
      (rng_fv_list Rs \u typ_fv_list Us).
Proof.
  intros.
  induction Rs; simpl; auto using subset_empty_l.
  rewrite union_distribute.
  apply subset_union_2; auto.
  apply rng_open_fv.
Qed.

Lemma rng_open_vars_list_fv_inv : forall Ys Rs,
    subset (rng_fv_list Rs)
      (rng_fv_list (rng_open_vars_list Rs Ys)).
Proof.
  intros.
  apply rng_open_list_fv_inv.
Qed.

Lemma rng_open_vars_list_fv : forall Ys Rs,
    subset (rng_fv_list (rng_open_vars_list Rs Ys))
      (rng_fv_list Rs \u from_list Ys).
Proof.
  intros.
  rewrite <- typ_fv_list_fvars.  
  apply rng_open_list_fv.
Qed.

(* *************************************************************** *)
(** ** Schemes *)

Lemma sch_fv_ranges : forall M,
    subset (rng_fv_list (sch_ranges M)) (sch_fv M).
Proof.
  intros.
  destruct M; simpl.
  apply subset_union_weak_l.
Qed.

Lemma sch_fv_body : forall M,
    subset (typ_fv (sch_body M)) (sch_fv M).
Proof.
  intros.
  destruct M; simpl.
  apply subset_union_weak_r.
Qed.

(* *************************************************************** *)
(** ** Type Environments *)

Lemma tenv_fv_empty :
  tenv_fv empty = \{}.
Proof.
  unfold tenv_fv, fv_in_values; rew_env_defs; simpl; reflexivity. 
Qed.

Lemma tenv_fv_single : forall x R,
  tenv_fv (x ~ R) = rng_fv R.
Proof.
  intros.
  unfold tenv_fv, fv_in_values; rew_env_defs; simpl. 
  apply union_empty_r.
Qed.

Lemma tenv_fv_concat : forall E1 E2,
  tenv_fv (E1 & E2) = tenv_fv E1 \u tenv_fv E2.
Proof.
  intros.
  unfold tenv_fv, fv_in_values; rew_env_defs.
  rewrite LibList.map_app.
  rewrite LibList.fold_right_app.
  induction E2.
  - simpl. symmetry. apply union_empty_r.
  - rewrite LibList.map_cons.
    simpl.
    rewrite union_comm_assoc.
    rewrite IHE2.
    reflexivity.
Qed. 

Lemma tenv_fv_singles : forall Xs Rs,
    length Xs = length Rs ->
    tenv_fv (Xs ~* Rs) = rng_fv_list Rs.
Proof.
  introv Hl.
  generalize dependent Rs.
  induction Xs; introv Hl; induction Rs; simpl;
    inversion Hl; autorewrite with rew_env_concat;
      rewrite? tenv_fv_empty; auto.
  rewrite tenv_fv_concat.
  rewrite tenv_fv_single; simpl.
  rewrite union_comm.
  f_equal; auto.
Qed.

Lemma tenv_fv_ranges : forall Xs M,
    length Xs = sch_arity M ->
    subset (tenv_fv (Xs ~: M))
           (rng_fv_list (sch_ranges M) \u from_list Xs).
Proof.
  introv Hl.
  destruct M; unfold bind_sch_ranges; simpl in *.
  rewrite tenv_fv_singles;
    try rewrite <- length_rng_open_vars_list;
    try rewrite Hl; auto.
  apply rng_open_vars_list_fv.
Qed.  

Hint Rewrite tenv_fv_empty tenv_fv_single tenv_fv_concat
  : rew_tenv_fv.

Hint Rewrite tenv_fv_singles using auto : rew_tenv_fv.

Hint Rewrite tenv_fv_ranges using auto : rew_tenv_fv.

(* *************************************************************** *)
(** ** Environments *)

Lemma env_fv_empty :
  env_fv empty = \{}.
Proof.
  unfold env_fv, fv_in_values; rew_env_defs; simpl; reflexivity. 
Qed.  

Lemma env_fv_single : forall x v,
  env_fv (x ~ v) = sch_fv v.
Proof.
  intros.
  unfold env_fv, fv_in_values; rew_env_defs; simpl. 
  apply union_empty_r.
Qed.

Lemma env_fv_concat : forall D1 D2,
  env_fv (D1 & D2) = env_fv D1 \u env_fv D2.
Proof.
  intros.
  unfold env_fv, fv_in_values; rew_env_defs.
  rewrite LibList.map_app.
  rewrite LibList.fold_right_app.
  induction D2.
  - simpl. symmetry. apply union_empty_r.
  - rewrite LibList.map_cons.
    simpl.
    rewrite union_comm_assoc.
    rewrite IHD2.
    reflexivity.
Qed.

Hint Rewrite env_fv_empty env_fv_single env_fv_concat : rew_env_fv.

Lemma env_fv_singles : forall xs Ms,
    length xs = length Ms ->
    env_fv (xs ~* Ms) = sch_fv_list Ms.
Proof.
  introv Hl.
  generalize dependent Ms.
  induction xs; introv Hl; induction Ms; simpl;
    inversion Hl;
    autorewrite with rew_env_concat;
    autorewrite with rew_env_fv; auto.
  rewrite union_comm.
  f_equal; auto.
Qed.

Hint Rewrite env_fv_singles using auto : rew_env_fv.

(* *************************************************************** *)
(** ** Store types *)

Lemma styp_fv_empty :
  styp_fv empty = \{}.
Proof.
  unfold styp_fv, fv_in_values; rew_env_defs; simpl; reflexivity. 
Qed.  

Lemma styp_fv_single : forall x T,
  styp_fv (x ~ T) = typ_fv T.
Proof.
  intros.
  unfold styp_fv, fv_in_values; rew_env_defs; simpl. 
  apply union_empty_r.
Qed.  

Lemma styp_fv_concat : forall E1 E2,
  styp_fv (E1 & E2) = styp_fv E1 \u styp_fv E2.
Proof.
  intros.
  unfold styp_fv, fv_in_values; rew_env_defs.
  rewrite LibList.map_app.
  rewrite LibList.fold_right_app.
  induction E2.
  - simpl. symmetry. apply union_empty_r.
  - rewrite LibList.map_cons.
    simpl.
    rewrite union_comm_assoc.
    rewrite IHE2.
    reflexivity.
Qed.

Hint Rewrite styp_fv_empty styp_fv_single styp_fv_concat
  : rew_styp_fv.

(* *************************************************************** *)
(** ** Equation environments *)

Lemma qenv_fv_nil :
  qenv_fv nil = \{}.
Proof.
  unfold qenv_fv; simpl; reflexivity.
Qed.  

Lemma qenv_fv_cons : forall T1 T2 K Q,
  qenv_fv ((T1, T2, K) :: Q)
  = typ_fv T1 \u typ_fv T2 \u qenv_fv Q.
Proof.
  intros.
  unfold qenv_fv; simpl.
  reflexivity.
Qed.

Lemma qenv_fv_app : forall Q1 Q2,
  qenv_fv (Q1 ++ Q2) = qenv_fv Q1 \u qenv_fv Q2.
Proof.
  intros.
  unfold qenv_fv.
  rewrite fold_right_app.
  induction Q1 as [|[[T1 T2] K]]; simpl.
  - rewrite union_empty_l; reflexivity.
  - rewrite IHQ1.
    rewrite <- union_assoc.
    rewrite <- union_assoc.
    reflexivity.
Qed.

Hint Rewrite qenv_fv_nil qenv_fv_cons qenv_fv_app : rew_qenv_fv.


