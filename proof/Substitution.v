(************************************************
 *          Row Subtyping - Substitution        *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import List LibLN Disjoint Utilities Definitions.

(* ****************************************************** *)
(** ** Free Variables *)

Fixpoint typ_fv (T : typ) : vars :=
  match T with
  | typ_bvar i => \{}
  | typ_fvar x => \{x}
  | typ_constructor c T1 => typ_fv T1
  | typ_or cs1 T1 cs2 T2 => (typ_fv T1) \u (typ_fv T2)
  | typ_proj cs1 T1 cs2 => typ_fv T1
  | typ_variant T1 => typ_fv T1
  | typ_arrow T1 T2 => (typ_fv T1) \u (typ_fv T2)
  | typ_ref T1 => typ_fv T1
  | typ_unit => \{}
  | typ_prod T1 T2 => (typ_fv T1) \u (typ_fv T2)
  | typ_top cs => \{}
  | typ_bot cs => \{}
  | typ_meet T1 T2 => (typ_fv T1) \u (typ_fv T2)
  | typ_join T1 T2 => (typ_fv T1) \u (typ_fv T2)
  end.

Definition typ_fv_list Ts :=
  fold_right (fun T acc => typ_fv T \u acc) \{} Ts.

Definition rng_fv R :=
  match R with
  | rng_type => \{}
  | rng_row _ => \{}
  | rng_range T1 T2 => (typ_fv T1) \u (typ_fv T2)
  end.

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
(** ** Types *)

Fixpoint typ_var_subst Zs Us (X : var) :=
  match Zs with
  | nil => typ_fvar X
  | Z :: Zs =>
    match Us with
    | nil => typ_fvar X
    | U :: Us =>
        If X = Z then U else typ_var_subst Zs Us X
    end
  end.

Fixpoint typ_subst Zs Us (T : typ) {struct T} : typ :=
  match T with
  | typ_bvar i => typ_bvar i
  | typ_fvar X => typ_var_subst Zs Us X
  | typ_constructor c T1 =>
      typ_constructor c (typ_subst Zs Us T1)
  | typ_or cs1 T1 cs2 T2 =>
      typ_or cs1 (typ_subst Zs Us T1)
             cs2 (typ_subst Zs Us T2)
  | typ_proj cs1 T1 cs2 =>
      typ_proj cs1 (typ_subst Zs Us T1) cs2
  | typ_variant T1 => typ_variant (typ_subst Zs Us T1)
  | typ_arrow T1 T2 =>
      typ_arrow (typ_subst Zs Us T1) (typ_subst Zs Us T2)
  | typ_ref T1 => typ_ref (typ_subst Zs Us T1)
  | typ_unit => typ_unit
  | typ_prod T1 T2 =>
      typ_prod (typ_subst Zs Us T1) (typ_subst Zs Us T2)
  | typ_top cs => typ_top cs
  | typ_bot cs => typ_bot cs
  | typ_meet T1 T2 =>
      typ_meet (typ_subst Zs Us T1) (typ_subst Zs Us T2)
  | typ_join T1 T2 =>
      typ_join (typ_subst Zs Us T1) (typ_subst Zs Us T2)
  end.

Definition typ_subst_list Zs Us Ts :=
  List.map (fun T => typ_subst Zs Us T) Ts.

(** Substitution for names for ranges. *)

Definition rng_subst Zs Us R :=
  match R with
  | rng_type => rng_type
  | rng_row cs => rng_row cs
  | rng_range T1 T2 =>
      rng_range (typ_subst Zs Us T1) (typ_subst Zs Us T2)
  end.

Definition rng_subst_list Zs Us Rs :=
  List.map (fun R => rng_subst Zs Us R) Rs.

(** Substitution for names for schemes. *)

Definition sch_subst Zs Us M :=
  Sch
    (rng_subst_list Zs Us (sch_ranges M))
    (typ_subst Zs Us (sch_body M)).

Definition sch_subst_list Zs Us Ms :=
  List.map (fun M => sch_subst Zs Us M) Ms.

(** Substitution for type environments *)
Definition tenv_subst Zs Us E :=
  map (rng_subst Zs Us) E.

(** Substitution for environments *)
Definition env_subst Zs Us D :=
  map (sch_subst Zs Us) D.

(** Substitution for store types *)
Definition styp_subst Zs Us P :=
  map (typ_subst Zs Us) P.

(** Substitution for name in a term. *)

Fixpoint trm_var_subst zs us (x : var) :=
  match zs with
  | nil => trm_fvar x
  | z :: zs =>
    match us with
    | nil => trm_fvar x
    | u :: us =>
        If x = z then u else trm_var_subst zs us x
    end
  end.

Fixpoint trm_subst (zs : list var) (us : list trm) (t : trm)
         {struct t} : trm :=
  match t with
  | trm_bvar i => trm_bvar i 
  | trm_fvar x => trm_var_subst zs us x
  | trm_abs t1 => trm_abs (trm_subst zs us t1) 
  | trm_let t1 t2 => trm_let (trm_subst zs us t1) (trm_subst zs us t2) 
  | trm_app t1 t2 => trm_app (trm_subst zs us t1) (trm_subst zs us t2)
  | trm_constructor c t1 => trm_constructor c (trm_subst zs us t1)
  | trm_match t1 c t2 t3 =>
      trm_match (trm_subst zs us t1) c
                (trm_subst zs us t2) (trm_subst zs us t3)
  | trm_destruct t1 c t2 =>
      trm_destruct (trm_subst zs us t1) c (trm_subst zs us t2)
  | trm_absurd t1 => trm_absurd (trm_subst zs us t1)
  | trm_fix t1 => trm_fix (trm_subst zs us t1)
  | trm_unit => trm_unit
  | trm_prod t1 t2 => trm_prod (trm_subst zs us t1) (trm_subst zs us t2)
  | trm_fst t1 => trm_fst (trm_subst zs us t1)
  | trm_snd t1 => trm_snd (trm_subst zs us t1)
  | trm_loc l => trm_loc l
  | trm_ref t1 => trm_ref (trm_subst zs us t1)
  | trm_get t1 => trm_get (trm_subst zs us t1)
  | trm_set t1 t2 => trm_set (trm_subst zs us t1) (trm_subst zs us t2)
  end.

Definition trm_subst_single z u t :=
  trm_subst (z::nil) (u::nil) t.

Definition trm_subst_list zs us ts :=
  List.map (fun t => trm_subst zs us t) ts.

(* ****************************************************** *)
(** ** Instanciation of Tactics *)

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
  let O := gather_vars_with (fun x : sch => sch_fv x) in
  let P := gather_vars_with (fun x : list sch => sch_fv_list x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H
            \u I \u J \u K \u L \u M \u N \u O \u P).

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

(** Substitution on indices is identity on well-formed
    terms. *)

Lemma var_open_below_domain : forall n k us t,
    n < k ->
    var_open k us n t = t.
Proof.
  unfold lt.
  introv Hle.
  generalize dependent n.
  induction k; introv Hle.
  - inversion Hle.
  - destruct n; simpl; auto with arith.
Qed.

Lemma var_open_above_domain : forall n k us t,
    n >= k + length us ->
    var_open k us n t = t.
Proof.
  unfold gt, lt.
  introv Hle.
  generalize dependent n.
  induction k; introv Hle; simpl.
  - auto using nth_overflow.
  - destruct n; simpl; auto with arith.
Qed.
    
Lemma var_open_rec_core :forall n j vs i us,
    j + length vs <= i ->
    var_open j vs n (trm_bvar n)
    = {i ~> us}(var_open j vs n (trm_bvar n)) ->
    trm_bvar n = var_open i us n (trm_bvar n).
Proof.
  introv Hlt Heq.
  destruct (Compare_dec.le_lt_dec (j + length vs) n).
  - rewrite var_open_above_domain in Heq; auto.
  - rewrite var_open_below_domain; auto.
    Omega.omega.
Qed.    

Lemma trm_open_rec_core :forall t j vs i us,
    j + length vs <= i ->
    {j ~> vs}t = {i ~> us}({j ~> vs}t) ->
    t = {i ~> us}t.
Proof.
  induction t; introv Hl Heq; simpl in *;
    assert (S j + length vs <= S i) by Omega.omega;
    assert (S (S j) + length vs <= S (S i)) by Omega.omega;
    inversion Heq; f_equal; eauto using var_open_rec_core.
Qed.

Lemma trm_open_rec : forall t us,
  term t -> forall k, t = {k ~> us}t.
Proof.
  introv Ht.
  induction Ht; intro; simpl; f_equal; auto.
  - pick_fresh x.
    apply trm_open_rec_core with (j := 0) (vs := (trm_fvar x)::nil);
      simpl; try Omega.omega; eauto.
  - pick_fresh x.
    apply trm_open_rec_core with (j := 0) (vs := (trm_fvar x)::nil);
      simpl; try Omega.omega; eauto.
  - pick_fresh x.
    apply trm_open_rec_core with (j := 0) (vs := (trm_fvar x)::nil);
      simpl; try Omega.omega; eauto.
  - pick_fresh x.
    apply trm_open_rec_core with (j := 0) (vs := (trm_fvar x)::nil);
      simpl; try Omega.omega; eauto.
  - pick_fresh x.
    apply trm_open_rec_core with (j := 0) (vs := (trm_fvar x)::nil);
      simpl; try Omega.omega; eauto.
  - pick_fresh x. pick_fresh y.
    apply trm_open_rec_core
      with (j := 0) (vs := (trm_fvar y)::(trm_fvar x)::nil);
      simpl; try Omega.omega.
    assert
      (forall k : nat,
        t ^* y :: x :: nil = {k ~> us} (t ^* y :: x :: nil)) as IH
        by auto.
    apply IH; auto.
Qed.

(** Substitution for a fresh name is identity. *)

Lemma trm_var_subst_fresh : forall xs us y,
  y \notin (from_list xs) ->
  trm_var_subst xs us y = trm_fvar y.
Proof.
  introv Hf.
  generalize dependent us.
  induction xs; intros; induction us; simpl; auto.
  rewrite from_list_cons in Hf.
  apply notin_union in Hf.
  destruct Hf as [Hf1 Hf2].
  rewrite notin_singleton in Hf1.
  case_var.
  auto.
Qed.    

Lemma trm_subst_fresh : forall xs us t, 
  disjoint (trm_fv t) (from_list xs) ->
  trm_subst xs us t = t.
Proof.
  introv Hf.
  induction t; simpls; f_equal; auto.
  apply trm_var_subst_fresh.
  apply disjoint_singleton_l.
  auto.
Qed.

Lemma trm_subst_fresh_list : forall xs us ts,
  disjoint (trm_fv_list ts) (from_list xs) -> 
  trm_subst_list xs us ts = ts.
Proof.
  induction ts; simpl; intros Fr.
  - easy.
  - f_equal*.
    auto using trm_subst_fresh.
Qed.

Lemma trm_subst_fresh_trm_fvars : forall xs us ys,
  disjoint (from_list ys) (from_list xs) ->
  trm_subst_list xs us (trm_fvars ys) = trm_fvars ys.
Proof.
  introv Hf.
  apply trm_subst_fresh_list.
  rewrite trm_fv_list_fvars.
  assumption.
Qed.

(** Substitution distributes on the open operation. *)

Lemma trm_subst_var_open : forall xs us k n ts t,
    terms us ->
    trm_subst xs us (var_open k ts n t)
    = var_open k (trm_subst_list xs us ts) n (trm_subst xs us t).
Proof.
  introv Ht.
  generalize dependent n.
  generalize dependent ts.
  induction k; intros; induction n; induction ts; simpl; auto.
  - unfold trm_subst_list.
    rewrite map_nth.
    auto.
  - rewrite IHk; simpl; auto.
  - rewrite IHk; simpl; auto.
Qed.

Lemma trm_var_subst_open : forall xs us y k ts,
  terms us ->
  trm_var_subst xs us y
  = {k ~> ts} trm_var_subst xs us y.
Proof.
  introv Hts.
  generalize dependent us.
  induction xs; intros; induction us; simpl; auto.
  inversion Hts; subst.
  case_var; auto using trm_open_rec.
Qed.

Lemma trm_subst_open : forall xs us t ts,
    terms us -> 
    trm_subst xs us (t ^^* ts)
    = (trm_subst xs us t) ^^* (trm_subst_list xs us ts).
Proof.
  unfold trm_open.
  introv Hts.
  generalize 0 as k.
  induction t; intros; simpl; f_equal; auto.
  - rewrite trm_subst_var_open; auto.
  - apply trm_var_subst_open; auto.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma trm_subst_open_vars : forall xs us ys t,
  disjoint (from_list ys) (from_list xs) ->
  terms us ->
  (trm_subst xs us t) ^* ys = trm_subst xs us (t ^* ys).
Proof.
  introv Hf Hts.
  rewrite trm_subst_open; auto.
  rewrite trm_subst_fresh_trm_fvars; auto.
Qed.

Lemma trm_subst_open_var : forall xs us y t,
  y \notin (from_list xs) ->
  terms us ->
  (trm_subst xs us t) ^ y = trm_subst xs us (t ^ y).
Proof.
  introv Hn Hts.
  replace (trm_fvar y :: nil) with (trm_fvars (y::nil)); auto.
  apply trm_subst_open_vars; auto.
Qed.

Lemma trm_subst_cons : forall x xs u us t,
    x \notin trm_fv t ->
    trm_subst (x :: xs) (u :: us) t = trm_subst xs us t.
Proof.
  introv Hn.
  induction t; simpl; simpl in Hn;
    rewrite? IHt; rewrite? IHt1; rewrite? IHt2; rewrite? IHt3;
      auto.
  case_var; auto.
Qed.

Lemma trm_subst_list_cons : forall x xs u us ts,
    x \notin trm_fv_list ts ->
    trm_subst_list (x :: xs) (u :: us) ts = trm_subst_list xs us ts.
Proof.
  introv Hn.
  induction ts; auto.
  simpl in *.
  rewrite trm_subst_cons; f_equal; auto.
Qed.

Lemma trm_subst_fvars : forall xs us,
    fresh \{} (length us) xs ->
    trm_subst_list xs us (trm_fvars xs) = us.
Proof.
  introv Hf.
  fresh_length Hf as Hl.
  generalize dependent us.
  induction xs; introv Hf Hl; induction us; try discriminate; auto.
  - simpl; case_var; f_equal.
    destruct Hf.
    rewrite trm_subst_list_cons; auto.
    rewrite trm_fv_list_fvars.
    eauto using fresh_single_notin.
Qed.

(** Opening up an abstraction of body t with a term u is the same as
  opening up the abstraction with a fresh name x and then substituting
  u for x. *)

Lemma trm_subst_intro : forall xs us t, 
  fresh (trm_fv t) (length us) xs -> terms us ->
  t ^^* us = trm_subst xs us (t ^* xs).
Proof.
  introv Hf Hts.
  rewrite trm_subst_open; auto.
  rewrite trm_subst_fresh; auto.
  rewrite trm_subst_fvars; auto.
Qed.

Lemma trm_subst_single_intro : forall x u t,
    x \notin (trm_fv t) -> term u ->
    t ^^ u = trm_subst_single x u (t ^ x).
Proof.
  introv Hn Ht.
  rewrite trm_subst_intro with (xs := x :: nil); auto using terms.
Qed.

(* *************************************************************** *)
(** * Properties of types *)

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

Lemma typ_open_fv_inv : forall Us T,
    subset (typ_fv T) (typ_fv (typ_open T Us)).
Proof.
  intros.
  induction T; simpl;
    auto using subset_empty_l, subset_refl, subset_union_2.
Qed.

Lemma typ_open_fv : forall Us T,
    subset (typ_fv (typ_open T Us)) (typ_fv T \u typ_fv_list Us).
Proof.
  intros.
  induction T; simpl;
    try rewrite union_distribute with (R := typ_fv_list Us);
    auto using subset_empty_l, subset_refl, subset_union_weak_l,
      subset_union_2.
  apply typ_fv_nth.
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

(** Open with nil is the identity. *)

Lemma typ_open_nil : forall T,
    typ_open T nil = T.
Proof.
  intros.
  induction T; simpl;
    rewrite? IHT; rewrite? IHT1; rewrite? IHT2; auto.
  - destruct n; auto.
Qed.

Lemma typ_open_vars_nil : forall T,
    typ_open_vars T nil = T.
Proof.
  intros.
  unfold typ_open_vars.
  apply typ_open_nil.
Qed.

(** Open on a type is the identity. *)

Lemma typ_open_type : forall T Us,
  type T -> T = typ_open T Us.
Proof.
  introv Htyp.
  induction Htyp; simpl; rewrite <- ? IHHtyp;
    rewrite <- ? IHHtyp1; rewrite <- ? IHHtyp2; auto.
Qed.

(** Length of typ_fvars *)

Lemma length_typ_fvars : forall Xs,
    length (typ_fvars Xs) = length Xs.
Proof.
  intros.
  induction Xs; simpl; auto.
Qed.

(** Length of type list not affected by substitution *)

Lemma length_typ_subst_list : forall Xs Us Ts,
    length Ts = length (typ_subst_list Xs Us Ts).
Proof.
  intros.
  unfold typ_subst_list.
  rewrite List.map_length.
  reflexivity.
Qed.

(** Substitution for a fresh name is identity. *)

Lemma typ_var_subst_fresh : forall Xs Us X,
  disjoint \{X} (from_list Xs) -> 
  typ_var_subst Xs Us X = typ_fvar X.
Proof.
  introv Hf.
  generalize dependent Us.
  induction Xs; intro; induction Us; simpl; auto.
  rewrite disjoint_from_list_cons_r in Hf.
  destruct Hf as [Hf1 Hf2].
  rewrite disjoint_singleton_singleton in Hf1.
  case_var.
  auto.
Qed.

Lemma typ_subst_fresh : forall Xs Us T, 
  disjoint (typ_fv T) (from_list Xs) -> 
  typ_subst Xs Us T = T.
Proof.
  introv Hf.
  induction T; simpl; simpl in Hf;
    rewrite? IHT; rewrite? IHT1; rewrite? IHT2;
    auto using typ_var_subst_fresh.
Qed.

Lemma typ_subst_fresh_list : forall Xs Us Ts,
  disjoint (typ_fv_list Ts) (from_list Xs) -> 
  typ_subst_list Xs Us Ts = Ts.
Proof.
  induction Ts; simpl; intros Fr.
  - easy.
  - f_equal*.
    auto using typ_subst_fresh.
Qed.

Lemma typ_subst_fresh_typ_fvars : forall Xs Us Ys,
  disjoint (from_list Ys) (from_list Xs) ->
  typ_subst_list Xs Us (typ_fvars Ys) = typ_fvars Ys.
Proof.
  introv Hf.
  apply typ_subst_fresh_list.
  rewrite typ_fv_list_fvars.
  assumption.
Qed.

(** Substitution distributes on the open operation. *)

Lemma typ_subst_nth : forall Xs Us Ts n T,
    typ_subst Xs Us (nth n Ts T) =
    nth n (typ_subst_list Xs Us Ts) (typ_subst Xs Us T).
Proof.
  intros.
  generalize dependent n.
  induction Ts; intro; simpl; induction n; auto.
Qed.   

Lemma type_var_subst : forall Xs Us X,
    types Us ->
    type (typ_var_subst Xs Us X).
Proof.
  introv Ht.
  generalize dependent Xs.
  induction Ht; intro; induction Xs; try apply type_fvar.
  simpl.
  case_var; auto.
Qed.

Lemma typ_var_subst_open : forall Xs Us Ts X,
  types Us ->
  typ_var_subst Xs Us X =
  typ_open (typ_var_subst Xs Us X) Ts.
Proof.
  introv Ht.
  auto using typ_open_type, type_var_subst.
Qed.

Lemma typ_subst_open : forall Xs Us T Ts,
  types Us -> 
  typ_subst Xs Us (typ_open T Ts) = 
   typ_open (typ_subst Xs Us T) (typ_subst_list Xs Us Ts).
Proof.
  introv Ht. 
  induction T; simpl; f_equal; auto.
  - simpl; rewrite typ_subst_nth; auto.
  - apply typ_var_subst_open; auto.
Qed.

(** Substitution and open_vars for distinct names commute. *)

Lemma typ_subst_open_vars : forall Xs Ys Us T,
    disjoint (from_list Ys) (from_list Xs) ->
    types Us ->
    typ_open_vars (typ_subst Xs Us T) Ys
    = typ_subst Xs Us (typ_open_vars T Ys).
Proof.
  introv Hf Ht.
  unfold typ_open_vars. 
  rewrite typ_subst_open; auto. 
  rewrite typ_subst_fresh_typ_fvars; auto.
Qed.

Lemma typ_subst_notin_cons : forall X Xs U Us T,
    X \notin typ_fv T ->
    typ_subst (X :: Xs) (U :: Us) T = typ_subst Xs Us T.
Proof.
  introv Hn.
  induction T; simpl; simpl in Hn;
    rewrite? IHT; rewrite? IHT1; rewrite? IHT2;
      auto.
  case_var; auto.
Qed.

Lemma typ_subst_list_notin_cons : forall X Xs U Us Ts,
    X \notin typ_fv_list Ts ->
    typ_subst_list (X :: Xs) (U :: Us) Ts = typ_subst_list Xs Us Ts.
Proof.
  introv Hn.
  induction Ts; auto.
  simpl in *.
  rewrite typ_subst_notin_cons; f_equal; auto.
Qed.

Lemma typ_subst_fvars : forall Xs Us,
    fresh \{} (length Us) Xs ->
    typ_subst_list Xs Us (typ_fvars Xs) = Us.
Proof.
  introv Hf.
  fresh_length Hf as Hl.
  generalize dependent Us.
  induction Xs; introv Hf Hl; induction Us; try discriminate; auto.
  - simpl; case_var; f_equal.
    destruct Hf.
    rewrite typ_subst_list_notin_cons; auto.
    rewrite typ_fv_list_fvars.
    eauto using fresh_single_notin.
Qed.

(** Opening up a type T with a type U is the same as opening up T
    with a fresh name X and then substituting U for X. *)
Lemma typ_subst_intro : forall Xs Us T, 
  fresh (typ_fv T) (length Us) Xs -> types Us ->
  typ_open T Us = typ_subst Xs Us (typ_open_vars T Xs).
Proof.
  introv Hf Ht.
  unfold typ_open_vars.
  fresh_length Hf as Hl.
  rewrite typ_subst_open; auto.
  rewrite typ_subst_fresh; auto.
  rewrite typ_subst_fvars; auto.
Qed.

Lemma typ_subst_nil : forall Xs Us T,
    Xs = nil \/ Us = nil ->
    typ_subst Xs Us T = T.
Proof.
  introv Heq.
  induction T; simpl;
    rewrite? IHT; rewrite? IHT1; rewrite? IHT2; auto.
  destruct Heq; subst; auto.
  destruct Xs; auto.
Qed.

Lemma typ_subst_list_nil : forall Xs Us Ts,
    Xs = nil \/ Us = nil ->
    typ_subst_list Xs Us Ts = Ts.
Proof.
  introv Heq.
  induction Ts; simpl; rewrite? typ_subst_nil; rewrite? IHTs; auto.
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
  induction R; simpl; auto using subset_empty_l.
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

Lemma rng_open_list_length : forall Rs Us,
    length (rng_open_list Rs Us) = length Rs.
Proof.
  intros.
  induction Rs; simpl; auto.
Qed.

Lemma rng_open_vars_list_length : forall Rs Xs,
    length (rng_open_vars_list Rs Xs) = length Rs.
Proof.
  unfold rng_open_vars_list.
  auto using rng_open_list_length.
Qed.

(** Open with nil is the identity. *)

Lemma rng_open_nil : forall R,
    rng_open R nil = R.
Proof.
  intros.
  induction R; simpl; rewrite? typ_open_nil; auto.
Qed.

Lemma rng_open_vars_nil : forall R,
    rng_open_vars R nil = R.
Proof.
  intros.
  unfold rng_open_vars.
  apply rng_open_nil.
Qed.

Lemma rng_open_list_nil : forall Rs,
    rng_open_list Rs nil = Rs.
Proof.
  intros.
  induction Rs; simpl; auto.
  rewrite rng_open_nil.
  rewrite IHRs.
  auto.
Qed.

Lemma rng_open_vars_list_nil : forall Rs,
    rng_open_vars_list Rs nil = Rs.
Proof.
  intros.
  unfold rng_open_vars_list.
  apply rng_open_list_nil.
Qed.

(** Open on a range is the identity. *)

Lemma rng_open_range : forall R Us,
  range R -> R = rng_open R Us.
Proof.
  introv Hr.
  induction Hr; simpl; auto.
  rewrite <- typ_open_type; auto.
  rewrite <- typ_open_type; auto.
Qed.

Lemma rng_open_ranges : forall Rs Us,
    ranges Rs -> Rs = rng_open_list Rs Us.
Proof.
  introv Hr.
  induction Hr; simpl; f_equal; auto using rng_open_range.
Qed.

(** Length of range list not affected by opening or substitution *)

Lemma length_rng_open_list : forall Rs Us,
    length Rs = length (rng_open_list Rs Us).
Proof.
  intros.
  unfold rng_open_list.
  rewrite List.map_length.
  reflexivity.
Qed.

Lemma length_rng_open_vars_list : forall Rs Xs,
    length Rs = length (rng_open_vars_list Rs Xs).
Proof.
  intros.
  unfold rng_open_vars_list.
  unfold rng_open_list.
  rewrite List.map_length.
  reflexivity.
Qed.

Lemma length_rng_subst_list : forall Xs Us Rs,
    length Rs = length (rng_subst_list Xs Us Rs).
Proof.
  intros.
  unfold rng_subst_list.
  rewrite List.map_length.
  reflexivity.
Qed.

(** Kind of a range not affected by opening or
    substitution *)

Lemma rng_knd_open : forall R Us,
  rng_knd R = rng_knd (rng_open R Us).
Proof.
  intros.
  induction R; simpl; auto.
Qed.

Lemma rng_knd_open_vars : forall R Xs,
  rng_knd R = rng_knd (rng_open_vars R Xs).
Proof.
  intros.
  induction R; simpl; auto.
Qed.

Lemma rng_knd_subst : forall Xs Us R,
  rng_knd R = rng_knd (rng_subst Xs Us R).
Proof.
  intros.
  induction R; simpl; auto.
Qed.

(** Kinds of a range list not affected by opening or
    substitution *)

Lemma rngs_knds_open_list : forall Rs Us,
  rngs_knds Rs = rngs_knds (rng_open_list Rs Us).
Proof.
  intros.
  induction Rs; simpl; auto.
  f_equal; auto using rng_knd_open.
Qed.

Lemma rngs_knds_open_vars_list : forall Rs Xs,
  rngs_knds Rs = rngs_knds (rng_open_vars_list Rs Xs).
Proof.
  intros.
  induction Rs; simpl; auto.
  f_equal; auto using rng_knd_open.
Qed.

Lemma rngs_knds_subst_list : forall Xs Us Rs,
  rngs_knds Rs = rngs_knds (rng_subst_list Xs Us Rs).
Proof.
  intros.
  induction Rs; simpl; auto.
  f_equal; auto using rng_knd_subst.
Qed.

(** Substitution for a fresh name is identity. *)

Lemma rng_subst_fresh : forall Xs Us R, 
  disjoint (rng_fv R) (from_list Xs) -> 
  rng_subst Xs Us R = R.
Proof.
  introv Hf.
  induction R; simpl in *; auto.
  rewrite typ_subst_fresh; auto.
  rewrite typ_subst_fresh; auto.
Qed.

Lemma rng_subst_list_fresh : forall Xs Us Rs,
  disjoint (rng_fv_list Rs) (from_list Xs) -> 
  rng_subst_list Xs Us Rs = Rs.
Proof.
  introv Hf.
  induction Rs; simpl in *; f_equal; auto using rng_subst_fresh.
Qed.

(** Substitution distributes on the open operation. *)

Lemma rng_subst_open : forall Xs Us R Ts,
    types Us -> 
    rng_subst Xs Us (rng_open R Ts)
    = rng_open (rng_subst Xs Us R) (typ_subst_list Xs Us Ts).
Proof.
  introv Ht.
  induction R; simpl in *; auto.
  rewrite typ_subst_open; auto.
  rewrite typ_subst_open; auto.
Qed.

Lemma rng_subst_list_open : forall Xs Us Rs Ts,
    types Us -> 
    rng_subst_list Xs Us (rng_open_list Rs Ts)
    = rng_open_list
        (rng_subst_list Xs Us Rs) (typ_subst_list Xs Us Ts).
Proof.
  introv Ht.
  induction Rs; simpl in *; f_equal; auto using rng_subst_open.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma rng_subst_open_vars : forall Xs Ys Us R, 
    disjoint (from_list Ys) (from_list Xs) ->
    types Us ->
    rng_subst Xs Us (rng_open_vars R Ys)
    = rng_open_vars (rng_subst Xs Us R) Ys.
Proof.
  introv Hf Ht.
  induction R; simpl; auto.
  rewrite typ_subst_open; auto.
  rewrite typ_subst_open; auto.
  rewrite typ_subst_fresh_list; auto.
  rewrite typ_fv_list_fvars; auto.
Qed.

Lemma rng_subst_list_open_vars : forall Xs Ys Us Rs, 
    disjoint (from_list Ys) (from_list Xs) ->
    types Us ->
    rng_subst_list Xs Us (rng_open_vars_list Rs Ys)
    = rng_open_vars_list (rng_subst_list Xs Us Rs) Ys.
Proof.
  introv Hf Ht.
  induction Rs; simpl in *; f_equal; auto. 
  rewrite rng_subst_open; auto.
  rewrite typ_subst_fresh_list; auto.
  rewrite typ_fv_list_fvars; auto.
Qed.

(** Opening up a range R with a type U is the same as opening up R
    with a fresh name X and then substituting U for X. *)
Lemma rng_subst_intro : forall Xs Us R,
  fresh (rng_fv R) (length Us) Xs -> types Us ->
  rng_open R Us = rng_subst Xs Us (rng_open_vars R Xs).
Proof.
  introv Hf Ht.
  induction R; simpl in *; auto.
  rewrite typ_subst_intro with (Xs := Xs); auto.
  rewrite typ_subst_intro with (Xs := Xs); auto.
Qed.

Lemma rng_subst_list_intro : forall Xs Us Rs,
  fresh (rng_fv_list Rs) (length Us) Xs -> types Us ->
  rng_open_list Rs Us
  = rng_subst_list Xs Us (rng_open_vars_list Rs Xs).
Proof.
  introv Hf Ht.
  induction Rs; simpl in *; f_equal; auto.
  rewrite rng_subst_intro with (Xs := Xs); auto.
Qed.

Lemma rng_subst_nil : forall Xs Us R,
    Xs = nil \/ Us = nil ->
    rng_subst Xs Us R = R.
Proof.
  introv Heq.
  induction R; simpl; rewrite? typ_subst_nil; auto.
Qed.

Lemma rng_subst_list_nil : forall Xs Us Rs,
    Xs = nil \/ Us = nil ->
    rng_subst_list Xs Us Rs = Rs.
Proof.
  introv Heq.
  induction Rs; simpl; rewrite? rng_subst_nil; rewrite? IHRs; auto.
Qed.

(* *************************************************************** *)
(** ** Schemes *)

Lemma sch_arity_length : forall M,
    sch_arity M = length (sch_ranges M).
Proof.
  intros.
  destruct M as [Rs T].
  simpl.
  reflexivity.
Qed.

Lemma sch_subst_arity : forall X U M,
    sch_arity (sch_subst X U M) = sch_arity M.
Proof.
  intros.
  destruct M.
  simpl.
  apply map_length.
Qed.

Hint Rewrite sch_subst_arity : rew_sch_arity.

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

Lemma length_sch_subst_list : forall Xs Us Ms,
    length Ms = length (sch_subst_list Xs Us Ms).
Proof.
  intros.
  unfold sch_subst_list.
  rewrite List.map_length.
  reflexivity.
Qed.

(** Substitution for a fresh name is identity. *)

Lemma sch_subst_fresh : forall Xs Us M,
  disjoint (sch_fv M) (from_list Xs) -> 
  sch_subst Xs Us M = M.
Proof.
  introv Hf.
  destruct M; unfold sch_subst; simpl in *.
  f_equal;
    eauto using rng_subst_list_fresh, typ_subst_fresh.
Qed.

Lemma sch_subst_list_fresh : forall Xs Us Ms,
  disjoint (sch_fv_list Ms) (from_list Xs) -> 
  sch_subst_list Xs Us Ms = Ms.
Proof.
  introv Hf.
  induction Ms; simpl in *; f_equal; auto using sch_subst_fresh.
Qed.

(** Substitution distributes on the sch_body. *)

Lemma sch_subst_body : forall Xs Us M,
    types Us ->
    typ_subst Xs Us (sch_body M) = sch_body (sch_subst Xs Us M).
Proof.
  introv Ht.
  destruct M; simpl; auto.
Qed.

(** Substitution distributes on empty schemes. *)

Lemma sch_subst_empty : forall X U T,
    sch_subst X U (sch_empty T) =
    sch_empty (typ_subst X U T).
Proof.
  unfold sch_subst.
  reflexivity.
Qed.

(** Substitution distributes on the instance operation. *)

Lemma sch_subst_instance : forall Xs Us M Ts,
    types Us -> 
    typ_subst Xs Us (instance M Ts) = 
    instance (sch_subst Xs Us M) (typ_subst_list Xs Us Ts).
Proof.
  introv Ht.
  unfold instance.
  rewrite <- sch_subst_body; auto using typ_subst_open.
Qed.

Lemma sch_subst_instance_vars : forall Zs Us M Xs,
    types Us -> disjoint (from_list Xs) (from_list Zs) ->
    typ_subst Zs Us (instance_vars M Xs) = 
    instance_vars (sch_subst Zs Us M) Xs.
Proof.
  introv Ht Hf.
  unfold instance_vars.
  rewrite <- typ_subst_fresh_typ_fvars
    with (Xs := Zs) (Us := Us) at 2; auto.
  apply sch_subst_instance.
  assumption.
Qed.

(** Instanciating with a type U is the same as instanciating
    with a fresh name X and then substituting U for X. *)

Lemma typ_subst_intro_instance : forall M Xs Us,
  fresh (sch_fv M \u typ_fv_list Us) (sch_arity M) Xs ->
  length Us = sch_arity M ->
  types Us ->
  instance M Us = typ_subst Xs Us (instance_vars M Xs).
Proof.
  introv Hf Hl Ht.
  destruct M;
    simpl sch_fv in Hf; simpl sch_arity in Hf;
      simpl sch_arity in Hl; unfold instance_vars;
        unfold instance; simpl.
  apply typ_subst_intro; auto.
Qed.

Lemma instance_empty_nil : forall T,
  instance (sch_empty T) nil = T.
Proof.
  intros.
  unfold instance.
  rewrite typ_open_nil.
  auto.
Qed.

Lemma sch_subst_nil : forall Xs Us M,
    Xs = nil \/ Us = nil ->
    sch_subst Xs Us M = M.
Proof.
  introv Heq.
  destruct M; unfold sch_subst; simpl.
  rewrite rng_subst_list_nil; auto.
  rewrite typ_subst_nil; auto.
Qed.

Lemma sch_subst_list_nil : forall Xs Us Ms,
    Xs = nil \/ Us = nil ->
    sch_subst_list Xs Us Ms = Ms.
Proof.
  introv Heq.
  induction Ms; simpl; rewrite? sch_subst_nil; rewrite? IHMs; auto.
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

Lemma tenv_subst_nil : forall Xs Us E,
    Xs = nil \/ Us = nil ->
    tenv_subst Xs Us E = E.
Proof.
  introv Heq.
  unfold tenv_subst.
  induction E using env_ind;
    rewrite? map_empty; rewrite? map_push;
    rewrite? IHE; rewrite? rng_subst_nil; auto.
Qed.

Lemma tenv_subst_empty : forall Xs Us,
  tenv_subst Xs Us empty = empty.
Proof.
  intros.
  unfold tenv_subst.
  autorewrite with rew_env_map.
  reflexivity.
Qed.  

Lemma tenv_subst_single : forall Xs Us x R,
  tenv_subst Xs Us (x ~ R) = (x ~ rng_subst Xs Us R).
Proof.
  intros.
  unfold tenv_subst.
  autorewrite with rew_env_map.
  reflexivity.
Qed.

Lemma tenv_subst_concat : forall Xs Us E1 E2,
  tenv_subst Xs Us (E1 & E2)
  = tenv_subst Xs Us E1 & tenv_subst Xs Us E2.
Proof.
  intros.
  unfold tenv_subst.
  autorewrite with rew_env_map.
  reflexivity. 
Qed.

Lemma tenv_subst_push : forall Zs Us E X R,
  tenv_subst Zs Us (E & X ~ R)
  = tenv_subst Zs Us E & X ~ rng_subst Zs Us R.
Proof.
  intros.
  unfold tenv_subst.
  autorewrite with rew_env_map.
  simpl.
  reflexivity.
Qed.

Lemma tenv_subst_singles : forall Zs Us Xs Rs,
  length Xs = length Rs ->
  tenv_subst Zs Us (Xs ~* Rs) =
  Xs ~* (rng_subst_list Zs Us Rs).
Proof.
  introv Hl.
  generalize dependent Rs.
  induction Xs; intros; destruct Rs; simpl;
    inversion Hl; autorewrite with rew_env_concat;
    auto using tenv_subst_empty.
  rewrite tenv_subst_concat.
  unfold tenv_subst at 2.
  rewrite map_single.
  f_equal; auto.
Qed.

Lemma tenv_subst_ranges : forall Zs Us Xs M,
  length Xs = sch_arity M ->
  disjoint (from_list Xs) (from_list Zs) ->
  types Us ->
  tenv_subst Zs Us (Xs ~: M) = Xs ~: (sch_subst Zs Us M).
Proof.
  introv Hl Hn Ht.
  destruct M as [Rs T].
  unfold bind_sch_ranges.
  simpl in *.
  rewrite tenv_subst_singles;
    rewrite? Hl; auto using length_rng_open_vars_list.
  f_equal.
  rewrite rng_subst_list_open_vars; auto.
Qed.

Hint Rewrite tenv_subst_empty tenv_subst_single tenv_subst_concat
  : rew_tenv_subst.

Hint Rewrite tenv_subst_singles using auto : rew_tenv_subst.

Hint Rewrite tenv_subst_ranges using auto : rew_tenv_subst.

Hint Rewrite dom_empty dom_single dom_concat : rew_tenv_dom.

Hint Rewrite from_list_nil from_list_cons : rew_tenv_dom.

Lemma tenv_dom_singles : forall Xs (Rs : list rng),
  length Xs = length Rs ->
  dom (Xs ~* Rs) = from_list Xs.
Proof.
  introv Hl.
  generalize dependent Rs.
  induction Xs; introv Hl; destruct Rs; inversion Hl;
    autorewrite with rew_env_concat;
    autorewrite with rew_tenv_dom; auto.
  rewrite union_comm.
  f_equal; auto.
Qed.

Lemma tenv_dom_ranges : forall Xs M,
  sch_arity M = length Xs ->
  dom (Xs ~: M) = from_list Xs.
Proof.
  introv Hl.
  destruct M as [Rs T].
  unfold bind_sch_ranges.
  simpl in *.
  rewrite length_rng_open_vars_list with (Xs := Xs) in Hl.
  rewrite tenv_dom_singles; auto.
Qed.

Lemma tenv_dom_subst : forall Zs Us E,
    dom (tenv_subst Zs Us E) = dom E.
Proof.
  intros.
  induction E using env_ind;
    autorewrite with rew_tenv_subst rew_env_dom.
  - reflexivity.
  - rewrite IHE. reflexivity.
Qed.

Hint Rewrite tenv_dom_subst : rew_tenv_dom.

Hint Rewrite tenv_dom_singles using auto : rew_tenv_dom.

Hint Rewrite tenv_dom_ranges using auto : rew_tenv_dom.

Lemma tenv_subst_fresh : forall Xs Us E, 
  disjoint (tenv_fv E) (from_list Xs) -> 
  tenv_subst Xs Us E = E.
Proof.
  introv Hf.
  induction E using env_ind;
    autorewrite with rew_tenv_subst rew_tenv_fv in *.
  - reflexivity.
  - rewrite rng_subst_fresh; auto.
    rewrite IHE; auto.
Qed.

Lemma tenv_subst_binds : forall X R E Zs Us,
    binds X R E ->
    binds X (rng_subst Zs Us R) (tenv_subst Zs Us E).
Proof.
  introv Hbd.
  induction E using env_ind.
  - apply binds_empty_inv in Hbd; contradiction.
  - destruct (binds_push_inv Hbd) as [[Hx Hb]|[Hx Hb]].
    + subst. autorewrite with rew_tenv_subst.
      apply binds_push_eq.
    + autorewrite with rew_tenv_subst.
      apply binds_push_neq; auto.
Qed.

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

Lemma env_subst_nil : forall Xs Us D,
    Xs = nil \/ Us = nil ->
    env_subst Xs Us D = D.
Proof.
  introv Heq.
  unfold env_subst.
  induction D using env_ind;
    rewrite? map_empty; rewrite? map_push;
    rewrite? IHD; rewrite? sch_subst_nil; auto.
Qed.

Lemma env_subst_empty : forall Xs Us,
  env_subst Xs Us empty = empty.
Proof.
  intros.
  unfold env_subst.
  autorewrite with rew_env_map.
  reflexivity. 
Qed.

Lemma env_subst_single : forall Xs Us x M,
  env_subst Xs Us (x ~ M) = (x ~ sch_subst Xs Us M).
Proof.
  intros.
  unfold env_subst.
  autorewrite with rew_env_map.
  reflexivity.
Qed.

Lemma env_subst_concat : forall Xs Us D1 D2,
  env_subst Xs Us (D1 & D2)
  = env_subst Xs Us D1 & env_subst Xs Us D2.
Proof.
  intros.
  unfold env_subst.
  autorewrite with rew_env_map.
  reflexivity. 
Qed.

Lemma env_subst_push : forall Zs Us D x M,
  env_subst Zs Us (D & x ~ M)
  = env_subst Zs Us D & x ~ sch_subst Zs Us M.
Proof.
  intros.
  unfold env_subst.
  autorewrite with rew_env_map.
  simpl.
  reflexivity.
Qed.

Hint Rewrite env_subst_empty env_subst_single
     env_subst_concat : rew_env_subst.

Lemma env_subst_singles : forall Zs Us xs Ms,
  length xs = length Ms ->
  env_subst Zs Us (xs ~* Ms) =
  xs ~* (sch_subst_list Zs Us Ms).
Proof.
  introv Hl.
  generalize dependent Ms.
  induction xs; intros; induction Ms; simpl;
    inversion Hl;
    autorewrite with rew_env_concat;
    autorewrite with rew_env_subst; auto.
  f_equal; auto.
Qed.

Hint Rewrite env_subst_singles using auto
  : rew_env_subst.

Hint Rewrite from_list_nil from_list_cons : rew_env_dom.

Lemma env_dom_singles : forall xs (Ms : list sch),
  length Ms = length xs ->
  dom (xs ~* Ms) = from_list xs.
Proof.
  introv Hl.
  generalize dependent Ms.
  induction xs; introv Hl; destruct Ms; inversion Hl;
    autorewrite with rew_env_concat;
    autorewrite with rew_env_dom; auto.
  rewrite union_comm.
  f_equal; auto.
Qed.

Lemma env_dom_subst : forall Zs Us D,
    dom (env_subst Zs Us D) = dom D.
Proof.
  intros.
  induction D using env_ind;
    autorewrite with rew_env_subst rew_env_dom.
  - reflexivity.
  - rewrite IHD. reflexivity.
Qed.

Hint Rewrite env_dom_singles using auto : rew_env_dom.

Hint Rewrite env_dom_subst : rew_env_dom.

Lemma env_subst_fresh : forall Xs Us D, 
  disjoint (env_fv D) (from_list Xs) -> 
  env_subst Xs Us D = D.
Proof.
  introv Hf.
  induction D using env_ind;
    autorewrite with rew_env_subst rew_env_fv in *.
  - reflexivity.
  - rewrite sch_subst_fresh; auto.
    rewrite IHD; auto.
Qed.

Lemma env_subst_binds : forall X M D Zs Us,
    binds X M D ->
    binds X (sch_subst Zs Us M) (env_subst Zs Us D).
Proof.
  introv Hbd.
  induction D using env_ind.
  - apply binds_empty_inv in Hbd; contradiction.
  - destruct (binds_push_inv Hbd) as [[Hx Hb]|[Hx Hb]].
    + subst. autorewrite with rew_env_subst.
      apply binds_push_eq.
    + autorewrite with rew_env_subst.
      apply binds_push_neq; auto.
Qed.

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

Lemma styp_subst_nil : forall Xs Us P,
    Xs = nil \/ Us = nil ->
    styp_subst Xs Us P = P.
Proof.
  introv Heq.
  unfold styp_subst.
  induction P using env_ind;
    rewrite? map_empty; rewrite? map_push;
    rewrite? IHP; rewrite? typ_subst_nil; auto.
Qed.

Lemma styp_subst_empty : forall Xs Us,
  styp_subst Xs Us empty = empty.
Proof.
  intros.
  unfold styp_subst.
  autorewrite with rew_env_map.
  reflexivity. 
Qed.

Lemma styp_subst_single : forall Xs Us x T,
  styp_subst Xs Us (x ~ T) = (x ~ typ_subst Xs Us T).
Proof.
  intros.
  unfold styp_subst.
  autorewrite with rew_env_map.
  reflexivity.
Qed.  

Lemma styp_subst_concat : forall Xs Us P1 P2,
  styp_subst Xs Us (P1 & P2)
  = styp_subst Xs Us P1 & styp_subst Xs Us P2.
Proof.
  intros.
  unfold styp_subst.
  autorewrite with rew_env_map.
  reflexivity. 
Qed.

Hint Rewrite styp_subst_empty styp_subst_single styp_subst_concat
  : rew_styp_subst.

Lemma styp_dom_subst : forall Zs Us P,
    dom (styp_subst Zs Us P) = dom P.
Proof.
  intros.
  induction P using env_ind;
    autorewrite with rew_styp_subst rew_env_dom.
  - reflexivity.
  - rewrite IHP. reflexivity.
Qed.

Hint Rewrite dom_empty dom_single dom_concat styp_dom_subst
  : rew_styp_dom.

Hint Rewrite from_list_nil from_list_cons : rew_styp_dom.

Lemma styp_subst_fresh : forall Xs Us P, 
  disjoint (styp_fv P) (from_list Xs) -> 
  styp_subst Xs Us P = P.
Proof.
  introv Hf.
  induction P using env_ind;
    autorewrite with rew_styp_subst rew_styp_fv in *.
  - reflexivity.
  - rewrite typ_subst_fresh; auto.
    rewrite IHP; auto.
Qed.

Lemma styp_subst_binds : forall X T P Zs Us,
    binds X T P ->
    binds X (typ_subst Zs Us T) (styp_subst Zs Us P).
Proof.
  introv Hbd.
  induction P using env_ind.
  - apply binds_empty_inv in Hbd; contradiction.
  - destruct (binds_push_inv Hbd) as [[Hx Hb]|[Hx Hb]].
    + subst. autorewrite with rew_styp_subst.
      apply binds_push_eq.
    + autorewrite with rew_styp_subst.
      apply binds_push_neq; auto.
Qed.
