(************************************************
 *          Row Subtyping - Substitution        *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import List LibLN Disjoint Definitions.
(* *************************************************************** *)
(** ** Free Variables *)

(** Computing free variables of a type. *)

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

(** Computing free variables of a list of terms. *)

Definition typ_fv_list Ts :=
  fold_right (fun T acc => typ_fv T \u acc) \{} Ts.

Definition knd_fv K :=
  match K with
  | knd_type => \{}
  | knd_row _ => \{}
  | knd_range T1 T2 => (typ_fv T1) \u (typ_fv T2)
  end.

Definition knd_fv_list Ks :=
  fold_right (fun K acc => knd_fv K \u acc) \{} Ks.

(** Computing free variables of a type scheme. *)

Fixpoint sch_fv (M : sch) : vars :=
  knd_fv_list (sch_kinds M) \u typ_fv (sch_body M).

Definition sch_fv_list Ms :=
  fold_right (fun M acc => sch_fv M \u acc) \{} Ms.

(** Computing free type variables of the values of an environment. *)

Definition bind_fv (B : bind) : vars :=
  match B with
  | bind_knd K => knd_fv K
  | bind_typ M => sch_fv M
  end.

Definition env_fv := 
  fv_in_values bind_fv.

Definition styp_fv :=
  fv_in_values typ_fv.

(** Computing free variables of a term. *)

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

(* *************************************************************** *)
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
  | typ_constructor c T1 => typ_constructor c (typ_subst Zs Us T1)
  | typ_or cs1 T1 cs2 T2 =>
      typ_or cs1 (typ_subst Zs Us T1) cs2 (typ_subst Zs Us T2)
  | typ_proj cs1 T1 cs2 => typ_proj cs1 (typ_subst Zs Us T1) cs2
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

(** Substitution for names for kinds. *)

Definition knd_subst Zs Us K :=
  match K with
  | knd_type => knd_type
  | knd_row cs => knd_row cs
  | knd_range T1 T2 =>
      knd_range (typ_subst Zs Us T1) (typ_subst Zs Us T2)
  end.

Definition knd_subst_list Zs Us Ks :=
  List.map (fun K => knd_subst Zs Us K) Ks.

(** Substitution for names for schemes. *)

Definition sch_subst Zs Us M :=
  Sch
    (knd_subst_list Zs Us (sch_kinds M))
    (typ_subst Zs Us (sch_body M)).

Definition sch_subst_list Zs Us Ms :=
  List.map (fun M => sch_subst Zs Us M) Ms.

(** Substitution for bindings *)
Definition bind_subst Zs Us B :=
  match B with
  | bind_knd K => bind_knd (knd_subst Zs Us K)
  | bind_typ M => bind_typ (sch_subst Zs Us M)
  end.

(** Substitution for environments *)
Definition env_subst Zs Us E :=
  map (bind_subst Zs Us) E.

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

(* =============================================================== *)
(** * Tactics *)

(* *************************************************************** *)
(** ** Instanciation of Tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : list var => from_list x) in
  let D := gather_vars_with (fun x : env => dom x) in
  let E := gather_vars_with (fun x : LibEnv.env bind => dom x) in
  let F := gather_vars_with (fun x : trm => trm_fv x) in
  let G := gather_vars_with (fun x : list trm => trm_fv_list x) in
  let H := gather_vars_with (fun x : typ => typ_fv x) in
  let I := gather_vars_with (fun x : list typ => typ_fv_list x) in
  let J := gather_vars_with (fun x : knd => knd_fv x) in
  let K := gather_vars_with (fun x : list knd => knd_fv_list x) in
  let L := gather_vars_with (fun x : env => env_fv x) in
  let M := gather_vars_with (fun x : styp => styp_fv x) in
  let N := gather_vars_with (fun x : LibEnv.env bind => env_fv x) in
  let O := gather_vars_with (fun x : sch => sch_fv x) in
  let P := gather_vars_with (fun x : list sch => sch_fv_list x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H
            \u I \u J \u K \u L \u M \u N \u O).

Tactic Notation "pick_fresh" ident(x) :=
  let L := gather_vars in (pick_fresh_gen L x).

Tactic Notation "pick_freshes" constr(n) ident(x) :=
  let L := gather_vars in (pick_freshes_gen L n x).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; autos*.

Tactic Notation "exists_fresh" ident(x) ident(Hfr) :=
  exists_fresh_gen gather_vars x Hfr.

(* *************************************************************** *)
(** ** Automation *)

Hint Extern 1 =>
  match goal with
  | H : forall x, x \notin ?L -> ?P |- ?P =>
    apply (H (proj1_sig (var_fresh L)) (proj2_sig (var_fresh L)))
  | H: forall Xs : list var,
      fresh ?L ?n Xs -> ?P |- ?P =>
    apply (H (proj1_sig (var_freshes L n))
             (proj2_sig (var_freshes L n)))
  end.

(* =============================================================== *)
(** Utilities *)

Lemma union_distribute : forall A (P : fset A) Q R,
    (P \u Q) \u R = (P \u R) \u (Q \u R).
Proof.
  intros.
  rewrite union_comm with (E := P).
  rewrite <- union_assoc.
  rewrite <- union_same with (E := R) at 1.
  rewrite union_assoc with (G := R).
  rewrite union_comm.
  rewrite <- union_assoc.
  rewrite union_comm with (E := R).
  reflexivity.
Qed.

Lemma notin_subset : forall A (X : A) P Q,
    X \notin Q ->
    subset P Q ->
    X \notin P.
Proof.
  unfold subset, notin, not.
  auto.
Qed.

Lemma fresh_subset : forall L M n Xs,
    fresh L n Xs ->
    subset M L ->
    fresh M n Xs.
Proof.
  introv Hf Hs.
  generalize dependent M.
  generalize dependent n.
  induction Xs; introv Hf Hs; destruct n; auto; simpl in *.
  unfold subset in Hs.
  unfold notin, not in *.
  intuition auto.
Qed.

Lemma fresh_disjoint : forall L n Xs,
    fresh \{} n Xs ->
    disjoint L (from_list Xs) ->
    fresh L n Xs.
Proof.
  introv Hf Hd.
  generalize dependent L.
  generalize dependent n.
  induction Xs; introv Hf Hd; destruct n; auto; simpl in *.
  apply disjoint_from_list_cons_r in Hd.
  destruct Hd; destruct Hf.
  auto.
Qed.

Lemma fresh_length : forall L n Xs,
  fresh L n Xs -> n = length Xs.
Proof using.
  intros. gen n L. induction Xs; simpl; intros n L Fr;
    destruct n; tryfalse*.
  easy.
  f_equal.
  rewrite* <- (@IHXs n (L \u \{a})).
Qed.  

Tactic Notation "fresh_length" constr(Fr) "as" ident(H) :=
  match type of Fr with
  | fresh _ ?n ?Xs =>
    assert (n = length Xs) as H
      by apply (fresh_length _ _ _ Fr)
  | _ =>
    fail 1
      "because it is not a freshness predicate"
  end.

Lemma fresh_from_notin : forall L X n Xs,
    fresh L n Xs ->
    X \notin (from_list Xs) ->
    fresh (L \u \{X}) n Xs.
Proof.
  introv Hf Hn.
  generalize dependent L.
  generalize dependent n.
  induction Xs; introv Hf; induction n; auto; simpl in *.
  rewrite from_list_cons in Hn.
  destruct Hf.
  split; auto.
  rewrite union_comm.
  rewrite union_assoc.
  auto.
Qed.

Lemma map_identity : forall A L,
    List.map (fun x : A => x) L = L.
Proof.
  intros.
  induction L; simpl; f_equal; auto.
Qed.

Lemma map_compose : forall A B C L (g : A -> B) (f : B -> C),
    List.map (fun x : A => f (g x)) L =
    List.map f (List.map g L).
Proof.
  intros.
  induction L; simpl; f_equal; auto.
Qed.

Lemma concat_assoc2 : forall A (E : LibEnv.env A) F G H,
  E & (F & G & H) = E & F & G & H.
Proof.
  intros.
  rewrite concat_assoc.
  rewrite concat_assoc.
  reflexivity.
Qed.

(* *************************************************************** *)
(** ** Terms *)

Lemma trm_fv_list_fvars : forall xs,
    trm_fv_list (trm_fvars xs) = from_list xs.
Proof.
  induction xs; auto; simpl.
  rewrite from_list_cons.
  rewrite IHxs.
  reflexivity.
Qed.

(** Substitution on indices is identity on well-formed terms. *)

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

(* =============================================================== *)
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
(** ** Kinds *)

Lemma knd_open_fv_inv : forall Us K,
    subset (knd_fv K) (knd_fv (knd_open K Us)).
Proof.
  intros.
  induction K; simpl; auto using subset_empty_l. 
  apply subset_union_2; apply typ_open_fv_inv.
Qed.

Lemma knd_open_fv : forall Us K,
    subset (knd_fv (knd_open K Us)) (knd_fv K \u typ_fv_list Us).
Proof.
  intros.
  induction K; simpl; auto using subset_empty_l.
  rewrite union_distribute.
  apply subset_union_2; apply typ_open_fv.
Qed.  

Lemma knd_open_vars_fv_inv : forall Ys K,
     subset (knd_fv K) (knd_fv (knd_open_vars K Ys)).
Proof.
  intros.
  apply knd_open_fv_inv.
Qed.

Lemma knd_open_vars_fv : forall Ys K,
    subset (knd_fv (knd_open_vars K Ys)) (knd_fv K \u from_list Ys).
Proof.
  intros.
  rewrite <- typ_fv_list_fvars.
  apply knd_open_fv.
Qed.

Lemma knd_open_list_fv_inv : forall Us Ks,
    subset (knd_fv_list Ks) (knd_fv_list (knd_open_list Ks Us)).
Proof.
  intros.
  induction Ks; simpl; auto using subset_empty_l.
  apply subset_union_2; auto.
  apply knd_open_fv_inv.
Qed.

Lemma knd_open_list_fv : forall Us Ks,
    subset (knd_fv_list (knd_open_list Ks Us))
      (knd_fv_list Ks \u typ_fv_list Us).
Proof.
  intros.
  induction Ks; simpl; auto using subset_empty_l.
  rewrite union_distribute.
  apply subset_union_2; auto.
  apply knd_open_fv.
Qed.

Lemma knd_open_vars_list_fv_inv : forall Ys Ks,
    subset (knd_fv_list Ks)
      (knd_fv_list (knd_open_vars_list Ks Ys)).
Proof.
  intros.
  apply knd_open_list_fv_inv.
Qed.

Lemma knd_open_vars_list_fv : forall Ys Ks,
    subset (knd_fv_list (knd_open_vars_list Ks Ys))
      (knd_fv_list Ks \u from_list Ys).
Proof.
  intros.
  rewrite <- typ_fv_list_fvars.  
  apply knd_open_list_fv.
Qed.

Lemma knd_open_list_length : forall Ks Us,
    length (knd_open_list Ks Us) = length Ks.
Proof.
  intros.
  induction Ks; simpl; auto.
Qed.

Lemma knd_open_vars_list_length : forall Ks Xs,
    length (knd_open_vars_list Ks Xs) = length Ks.
Proof.
  unfold knd_open_vars_list.
  auto using knd_open_list_length.
Qed.

(** Open with nil is the identity. *)

Lemma knd_open_nil : forall K,
    knd_open K nil = K.
Proof.
  intros.
  induction K; simpl; rewrite? typ_open_nil; auto.
Qed.

Lemma knd_open_vars_nil : forall K,
    knd_open_vars K nil = K.
Proof.
  intros.
  unfold knd_open_vars.
  apply knd_open_nil.
Qed.

Lemma knd_open_list_nil : forall Ks,
    knd_open_list Ks nil = Ks.
Proof.
  intros.
  induction Ks; simpl; auto.
  rewrite knd_open_nil.
  rewrite IHKs.
  auto.
Qed.

Lemma knd_open_vars_list_nil : forall Ks,
    knd_open_vars_list Ks nil = Ks.
Proof.
  intros.
  unfold knd_open_vars_list.
  apply knd_open_list_nil.
Qed.

(** Open on a kind is the identity. *)

Lemma knd_open_kind : forall K Us,
  kind K -> K = knd_open K Us.
Proof.
  introv Hk.
  induction Hk; simpl; auto.
  rewrite <- typ_open_type; auto.
  rewrite <- typ_open_type; auto.
Qed.

Lemma knd_open_kinds : forall Ks Us,
    kinds Ks -> Ks = knd_open_list Ks Us.
Proof.
  introv Hk.
  induction Hk; simpl; f_equal; auto using knd_open_kind.
Qed.

(** Length of kind list not affected by opening or substitution *)

Lemma length_knd_open_list : forall Us Ts,
    length Ts = length (knd_open_list Ts Us).
Proof.
  intros.
  unfold knd_open_list.
  rewrite List.map_length.
  reflexivity.
Qed.

Lemma length_knd_open_vars_list : forall Xs Ts,
    length Ts = length (knd_open_vars_list Ts Xs).
Proof.
  intros.
  unfold knd_open_vars_list.
  unfold knd_open_list.
  rewrite List.map_length.
  reflexivity.
Qed.

Lemma length_knd_subst_list : forall Xs Us Ks,
    length Ks = length (knd_subst_list Xs Us Ks).
Proof.
  intros.
  unfold knd_subst_list.
  rewrite List.map_length.
  reflexivity.
Qed.

(** Substitution for a fresh name is identity. *)

Lemma knd_subst_fresh : forall Xs Us K, 
  disjoint (knd_fv K) (from_list Xs) -> 
  knd_subst Xs Us K = K.
Proof.
  introv Hf.
  induction K; simpl in *; auto.
  rewrite typ_subst_fresh; auto.
  rewrite typ_subst_fresh; auto.
Qed.

Lemma knd_subst_list_fresh : forall Xs Us Ks,
  disjoint (knd_fv_list Ks) (from_list Xs) -> 
  knd_subst_list Xs Us Ks = Ks.
Proof.
  introv Hf.
  induction Ks; simpl in *; f_equal; auto using knd_subst_fresh.
Qed.

(** Substitution distributes on the open operation. *)

Lemma knd_subst_open : forall Xs Us K Ts,
    types Us -> 
    knd_subst Xs Us (knd_open K Ts)
    = knd_open (knd_subst Xs Us K) (typ_subst_list Xs Us Ts).
Proof.
  introv Ht.
  induction K; simpl in *; auto.
  rewrite typ_subst_open; auto.
  rewrite typ_subst_open; auto.
Qed.

Lemma knd_subst_list_open : forall Xs Us Ks Ts,
    types Us -> 
    knd_subst_list Xs Us (knd_open_list Ks Ts)
    = knd_open_list
        (knd_subst_list Xs Us Ks) (typ_subst_list Xs Us Ts).
Proof.
  introv Ht.
  induction Ks; simpl in *; f_equal; auto using knd_subst_open.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma knd_subst_open_vars : forall Xs Ys Us K, 
    disjoint (from_list Ys) (from_list Xs) ->
    types Us ->
    knd_subst Xs Us (knd_open_vars K Ys)
    = knd_open_vars (knd_subst Xs Us K) Ys.
Proof.
  introv Hf Ht.
  induction K; simpl; auto.
  rewrite typ_subst_open; auto.
  rewrite typ_subst_open; auto.
  rewrite typ_subst_fresh_list; auto.
  rewrite typ_fv_list_fvars; auto.
Qed.

Lemma knd_subst_list_open_vars : forall Xs Ys Us Ks, 
    disjoint (from_list Ys) (from_list Xs) ->
    types Us ->
    knd_subst_list Xs Us (knd_open_vars_list Ks Ys)
    = knd_open_vars_list (knd_subst_list Xs Us Ks) Ys.
Proof.
  introv Hf Ht.
  induction Ks; simpl in *; f_equal; auto. 
  rewrite knd_subst_open; auto.
  rewrite typ_subst_fresh_list; auto.
  rewrite typ_fv_list_fvars; auto.
Qed.

(** Opening up a kind K with a type U is the same as opening up K
    with a fresh name X and then substituting U for X. *)
Lemma knd_subst_intro : forall Xs Us K,
  fresh (knd_fv K) (length Us) Xs -> types Us ->
  knd_open K Us = knd_subst Xs Us (knd_open_vars K Xs).
Proof.
  introv Hf Ht.
  induction K; simpl in *; auto.
  rewrite typ_subst_intro with (Xs := Xs); auto.
  rewrite typ_subst_intro with (Xs := Xs); auto.
Qed.

Lemma knd_subst_list_intro : forall Xs Us Ks,
  fresh (knd_fv_list Ks) (length Us) Xs -> types Us ->
  knd_open_list Ks Us
  = knd_subst_list Xs Us (knd_open_vars_list Ks Xs).
Proof.
  introv Hf Ht.
  induction Ks; simpl in *; f_equal; auto.
  rewrite knd_subst_intro with (Xs := Xs); auto.
Qed.

Lemma knd_subst_nil : forall Xs Us K,
    Xs = nil \/ Us = nil ->
    knd_subst Xs Us K = K.
Proof.
  introv Heq.
  induction K; simpl; rewrite? typ_subst_nil; auto.
Qed.

Lemma knd_subst_list_nil : forall Xs Us Ks,
    Xs = nil \/ Us = nil ->
    knd_subst_list Xs Us Ks = Ks.
Proof.
  introv Heq.
  induction Ks; simpl; rewrite? knd_subst_nil; rewrite? IHKs; auto.
Qed.

(* *************************************************************** *)
(** ** Schemes *)

Lemma sch_arity_length : forall M,
    sch_arity M = length (sch_kinds M).
Proof.
  intros.
  destruct M as [Ks T].
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

Lemma sch_fv_kinds : forall M,
    subset (knd_fv_list (sch_kinds M)) (sch_fv M).
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
    eauto using knd_subst_list_fresh, typ_subst_fresh.
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
  rewrite knd_subst_list_nil; auto.
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
(** ** Bindings *)

Lemma bind_subst_nil : forall Xs Us B,
    Xs = nil \/ Us = nil ->
    bind_subst Xs Us B = B.
Proof.
  introv Heq.
  destruct B; simpl;
    rewrite? knd_subst_nil; rewrite? sch_subst_nil; auto.
Qed.

Lemma bind_subst_fresh : forall Xs Us B, 
  disjoint (bind_fv B) (from_list Xs) -> 
  bind_subst Xs Us B = B.
Proof.
  introv Hf.
  destruct B; simpls; f_equal; auto. 
  - apply knd_subst_fresh; auto.
  - apply sch_subst_fresh; auto.
Qed.

(* *************************************************************** *)
(** ** Environments *)

Lemma env_fv_empty :
  env_fv empty = \{}.
Proof.
  unfold env_fv, fv_in_values; rew_env_defs; simpl; reflexivity. 
Qed.  

Lemma env_fv_single : forall x v,
  env_fv (x ~ v) = bind_fv v.
Proof.
  intros.
  unfold env_fv, fv_in_values; rew_env_defs; simpl. 
  apply union_empty_r.
Qed.  

Lemma env_fv_concat : forall E F,
  env_fv (E & F) = env_fv E \u env_fv F.
Proof.
  intros.
  unfold env_fv, fv_in_values; rew_env_defs.
  rewrite LibList.map_app.
  rewrite LibList.fold_right_app.
  induction F.
  - simpl. symmetry. apply union_empty_r.
  - rewrite LibList.map_cons.
    simpl.
    rewrite union_comm_assoc.
    rewrite IHF.
    reflexivity.
Qed. 

Lemma env_fv_bind_knds : forall Xs Ks,
    length Xs = length Ks ->
    env_fv (bind_knds Xs Ks) = knd_fv_list Ks.
Proof.
  introv Hl.
  generalize dependent Ks.
  induction Xs; introv Hl; induction Ks; simpl;
    inversion Hl; subst; rewrite? env_fv_empty; auto.
  rewrite env_fv_concat.
  rewrite env_fv_single; simpl.
  f_equal; auto.
Qed.

Lemma env_fv_kinds : forall Xs M,
    length Xs = sch_arity M ->
    subset (env_fv (Xs ~::* M))
           (knd_fv_list (sch_kinds M) \u from_list Xs).
Proof.
  introv Hl.
  destruct M; unfold bind_sch_kinds; simpl in *.
  rewrite env_fv_bind_knds;
    try rewrite <- length_knd_open_vars_list;
    try rewrite Hl; auto.
  apply knd_open_vars_list_fv.
Qed.  

Lemma env_fv_bind_typs : forall xs Ms,
    length xs = length Ms ->
    env_fv (bind_typs xs Ms) = sch_fv_list Ms.
Proof.
  introv Hl.
  generalize dependent Ms.
  induction xs; introv Hl; induction Ms; simpl;
    inversion Hl; subst; rewrite? env_fv_empty; auto.
  rewrite env_fv_concat.
  rewrite env_fv_single; simpl.
  f_equal; auto.
Qed.

Hint Rewrite env_fv_empty env_fv_single env_fv_concat : rew_env_fv.

Lemma env_subst_nil : forall Xs Us E,
    Xs = nil \/ Us = nil ->
    env_subst Xs Us E = E.
Proof.
  introv Heq.
  unfold env_subst.
  induction E using env_ind;
    rewrite? map_empty; rewrite? map_push;
    rewrite? IHE; rewrite? bind_subst_nil; auto.
Qed.

Lemma env_subst_empty : forall Xs Us,
  env_subst Xs Us empty = empty.
Proof.
  intros.
  unfold env_subst.
  autorewrite with rew_env_map.
  reflexivity. 
Qed.  

Lemma env_subst_single : forall Xs Us x v,
  env_subst Xs Us (x ~ v) = (x ~ bind_subst Xs Us v).
Proof.
  intros.
  unfold env_subst.
  autorewrite with rew_env_map.
  reflexivity.
Qed.

Lemma env_subst_concat : forall Xs Us E F,
  env_subst Xs Us (E & F) = env_subst Xs Us E & env_subst Xs Us F.
Proof.
  intros.
  unfold env_subst.
  autorewrite with rew_env_map.
  reflexivity. 
Qed.

Lemma env_subst_knd : forall Zs Us E X K,
  env_subst Zs Us (E & X ~:: K)
  = env_subst Zs Us E & X ~:: knd_subst Zs Us K.
Proof.
  intros.
  unfold env_subst.
  autorewrite with rew_env_map.
  simpl.
  reflexivity.
Qed.

Lemma env_subst_typ : forall Zs Us E x M,
  env_subst Zs Us (E & x ~: M)
  = env_subst Zs Us E & x ~: sch_subst Zs Us M.
Proof.
  intros.
  unfold env_subst.
  autorewrite with rew_env_map.
  simpl.
  reflexivity.
Qed.

Lemma env_subst_bind_knds : forall Zs Us Xs Ks,
  env_subst Zs Us (bind_knds Xs Ks) =
  bind_knds Xs (knd_subst_list Zs Us Ks).
Proof.
  intros.
  generalize dependent Ks.
  induction Xs; intros; induction Ks; simpl;
    auto using env_subst_empty.
  rewrite env_subst_concat.
  unfold env_subst at 1.
  rewrite map_single.
  simpl.
  rewrite IHXs.
  reflexivity.
Qed.

Lemma env_subst_bind_sch_kinds : forall Zs Us Xs M,
  disjoint (from_list Xs) (from_list Zs) ->
  types Us ->
  env_subst Zs Us (Xs ~::* M) = Xs ~::* (sch_subst Zs Us M).
Proof.
  introv Hn Ht.
  destruct M as [Ks T].
  unfold bind_sch_kinds.
  simpl in *.
  rewrite env_subst_bind_knds.
  f_equal.
  rewrite knd_subst_list_open_vars; auto.
Qed.

Lemma env_subst_bind_typs : forall Zs Us xs Ms,
  env_subst Zs Us (bind_typs xs Ms) =
  bind_typs xs (sch_subst_list Zs Us Ms).
Proof.
  intros.
  generalize dependent Ms.
  induction xs; intros; induction Ms; simpl;
    auto using env_subst_empty.
  rewrite env_subst_concat.
  unfold env_subst at 1.
  rewrite map_single.
  simpl.
  rewrite IHxs.
  reflexivity.
Qed.

Hint Rewrite env_subst_empty env_subst_single env_subst_concat
  env_subst_bind_knds env_subst_bind_typs : rew_env_subst.

Hint Rewrite env_subst_bind_sch_kinds using auto
  : rew_env_subst.

Lemma env_dom_bind_knds : forall Xs Ks,
  length Ks = length Xs ->
  dom (bind_knds Xs Ks) = from_list Xs.
Proof.
  introv Hl.
  generalize dependent Ks.
  induction Xs; introv Hl; induction Ks; simpl; try discriminate.
  - rewrite from_list_nil.
    apply dom_empty.
  - autorewrite with rew_env_dom.
    rewrite from_list_cons.
    rewrite IHXs; autorewrite with rew_sch_arity; auto.
Qed.

Lemma env_dom_bind_sch_kinds : forall Xs M,
  sch_arity M = length Xs ->
  dom (Xs ~::* M) = from_list Xs.
Proof.
  introv Hl.
  destruct M as [Ks T].
  unfold bind_sch_kinds.
  simpl in *.
  rewrite length_knd_open_vars_list with (Xs := Xs) in Hl.
  remember (knd_open_vars_list Ks Xs) as Ks2.
  auto using env_dom_bind_knds.
Qed.

Lemma env_dom_bind_typs : forall xs Ms,
  length Ms = length xs ->
  dom (bind_typs xs Ms) = from_list xs.
Proof.
  introv Hl.
  generalize dependent Ms.
  induction xs; introv Hl; induction Ms; simpl; try discriminate.
  - rewrite from_list_nil.
    apply dom_empty.
  - autorewrite with rew_env_dom.
    rewrite from_list_cons.
    rewrite IHxs; autorewrite with rew_sch_arity; auto.
Qed.

Lemma env_dom_subst : forall Zs Us E,
    dom (env_subst Zs Us E) = dom E.
Proof.
  intros.
  induction E using env_ind;
    autorewrite with rew_env_subst rew_env_dom.
  - reflexivity.
  - rewrite IHE. reflexivity.
Qed.

Hint Rewrite env_dom_bind_knds env_dom_bind_sch_kinds
     env_dom_bind_typs env_dom_subst
  : rew_env_dom.

Lemma env_subst_fresh : forall Xs Us E, 
  disjoint (env_fv E) (from_list Xs) -> 
  env_subst Xs Us E = E.
Proof.
  introv Hf.
  induction E using env_ind;
    autorewrite with rew_env_subst rew_env_fv in *.
  - reflexivity.
  - rewrite bind_subst_fresh; auto.
    rewrite IHE; auto.
Qed.

Lemma env_subst_binds : forall X B E Zs Us,
    binds X B E ->
    binds X (bind_subst Zs Us B) (env_subst Zs Us E).
Proof.
  introv Hbd.
  induction E using env_ind.
  - apply binds_empty_inv in Hbd; contradiction.
  - destruct (binds_push_inv Hbd) as [[Hx Hb]|[Hx Hb]].
    + subst. autorewrite with rew_env_subst.
      apply binds_push_eq.
    + autorewrite with rew_env_subst.
      apply binds_push_neq; auto.
Qed.

Lemma env_subst_binds_knd : forall X K E Zs Us,
    binds X (bind_knd K) E ->
    binds X (bind_knd (knd_subst Zs Us K)) (env_subst Zs Us E).
Proof.
  introv Hbd.
  fold (bind_subst Zs Us (bind_knd K)).
  apply env_subst_binds.
  assumption.
Qed.

Lemma env_subst_binds_typ : forall x M E Zs Us,
    binds x (bind_typ M) E ->
    binds x (bind_typ (sch_subst Zs Us M)) (env_subst Zs Us E).
Proof.
  introv Hbd.
  fold (bind_subst Zs Us (bind_typ M)).
  apply env_subst_binds.
  assumption.
Qed.

Lemma no_term_bindings_empty :
    no_term_bindings empty.
Proof.
  unfold no_term_bindings.
  introv Hb.
  apply (binds_empty_inv Hb).
Qed.

Lemma no_term_bindings_concat : forall E F,
    no_term_bindings E ->
    no_term_bindings F ->
    no_term_bindings (E & F).
Proof.
  unfold no_term_bindings.
  introv Hn1 Hn2 Hb.
  specialize (Hn1 x M).
  specialize (Hn2 x M).
  destruct (binds_concat_inv Hb) as [Hb1 | [? Hb2]]; auto.
Qed.

Lemma no_term_bindings_kind : forall X K,
    no_term_bindings (X ~:: K).
Proof.
  unfold no_term_bindings.
  introv Hb.
  destruct (binds_single_inv Hb).
  discriminate.
Qed.

Lemma no_term_bindings_kinds : forall Xs Ks,
    no_term_bindings (bind_knds Xs Ks).
Proof.
  intros.
  generalize dependent Ks.
  induction Xs; intros; simpl.
  - apply no_term_bindings_empty.
  - induction Ks; simpl.
    + apply no_term_bindings_empty.
    + apply no_term_bindings_concat; auto.
      apply no_term_bindings_kind.
Qed.

Lemma no_term_bindings_sch_kinds : forall Xs M,
    no_term_bindings (Xs ~::* M).
Proof.
  intro Xs.
  destruct M as [Ks T].
  apply no_term_bindings_kinds.
Qed.

Hint Resolve no_term_bindings_empty no_term_bindings_concat
     no_term_bindings_kind no_term_bindings_kinds
     no_term_bindings_sch_kinds
  : no_term_bindings.

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

Lemma styp_fv_concat : forall E F,
  styp_fv (E & F) = styp_fv E \u styp_fv F.
Proof.
  intros.
  unfold styp_fv, fv_in_values; rew_env_defs.
  rewrite LibList.map_app.
  rewrite LibList.fold_right_app.
  induction F.
  - simpl. symmetry. apply union_empty_r.
  - rewrite LibList.map_cons.
    simpl.
    rewrite union_comm_assoc.
    rewrite IHF.
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

Lemma styp_subst_concat : forall Xs Us P Q,
  styp_subst Xs Us (P & Q) = styp_subst Xs Us P & styp_subst Xs Us Q.
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
