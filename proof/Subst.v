(************************************************
 *          Row Subtyping - Subst               *
 *                 Leo White                    *
 ************************************************)

(* Definitions of substitution functions and lemmas
   relating them to opening. *) 

Set Implicit Arguments.
Require Import List LibLN Disjoint Utilities Definitions
  Opening FreeVars Environments.

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
  | typ_or cs1 cs2 T1 T2 =>
      typ_or cs1 cs2 (typ_subst Zs Us T1)
             (typ_subst Zs Us T2)
  | typ_proj cs1 cs2 T1 =>
      typ_proj cs1 cs2 (typ_subst Zs Us T1)
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

(** ** Instantiating a scheme with types gives a type *)

Lemma scheme_instance_type : forall M Us,
    types Us -> length Us = sch_arity M ->
    scheme M ->
    type (instance M Us).
Proof.
  introv Hts Hl Hs.
  destruct Hs as [L ? Hs].
  destruct Hs as [? ? H].
  pick_freshes (sch_arity M) Xs.
  rewrite typ_subst_intro_instance with (Xs := Xs); auto.
  apply typ_subst_type; auto.
  assert (fresh L (sch_arity M) Xs) as Hf by auto.
  specialize (H Xs Hf).
  inversion H; subst.
  auto. 
Qed.

(* *************************************************************** *)
(** ** Ranges *)

Definition rng_subst Zs Us R :=
  Rng (typ_subst Zs Us (rng_lower R))
      (typ_subst Zs Us (rng_upper R))
      (rng_kind R).

Definition rng_subst_list Zs Us Rs :=
  List.map (fun R => rng_subst Zs Us R) Rs.

(** Length of range list not affected by substitution *)

Lemma length_rng_subst_list : forall Xs Us Rs,
    length Rs = length (rng_subst_list Xs Us Rs).
Proof.
  intros.
  unfold rng_subst_list.
  rewrite List.map_length.
  reflexivity.
Qed.

(** Kind of a range not affected by substitution *)

Lemma rng_kind_subst : forall Xs Us R,
  rng_kind R = rng_kind (rng_subst Xs Us R).
Proof.
  intros.
  induction R; simpl; auto.
Qed.

(** Kinds of a range list not affected by substitution *)

Lemma rngs_kinds_subst_list : forall Xs Us Rs,
  rngs_kinds Rs = rngs_kinds (rng_subst_list Xs Us Rs).
Proof.
  intros.
  induction Rs; simpl; auto.
  f_equal; auto using rng_kind_subst.
Qed.

(** Substitution for a fresh name is identity. *)

Lemma rng_subst_fresh : forall Xs Us R, 
  disjoint (rng_fv R) (from_list Xs) -> 
  rng_subst Xs Us R = R.
Proof.
  introv Hf.
  induction R; unfold rng_subst, rng_fv in *; simpl in *; auto.
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
  induction R; unfold rng_subst, rng_open; simpl in *; auto.
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
  induction R; unfold rng_subst, rng_open; simpl; auto.
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
  induction R; unfold rng_subst, rng_open, rng_fv in *;
    simpl in *; auto.
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
  induction R; unfold rng_subst; simpl; rewrite? typ_subst_nil; auto.
Qed.

Lemma rng_subst_list_nil : forall Xs Us Rs,
    Xs = nil \/ Us = nil ->
    rng_subst_list Xs Us Rs = Rs.
Proof.
  introv Heq.
  induction Rs; simpl; rewrite? rng_subst_nil; rewrite? IHRs; auto.
Qed.

(** Ranges are stable by type substitution *)

Lemma rng_subst_range : forall R Zs Us,
  types Us -> range (rng_subst Zs Us R) <-> range R.
Proof.
  introv Ht.
  split.
  - introv Hr.
    induction R; unfold rng_subst in Hr; simpl in Hr; auto.
    inversion Hr.
    rewrite typ_subst_type in *; auto.
  - introv Hr.
    induction Hr; unfold rng_subst; simpl; auto.
    apply range_c; rewrite ?typ_subst_type; auto.
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
(** ** Schemes *)

Definition sch_subst Zs Us M :=
  Sch
    (rng_subst_list Zs Us (sch_ranges M))
    (typ_subst Zs Us (sch_body M)).

Definition sch_subst_list Zs Us Ms :=
  List.map (fun M => sch_subst Zs Us M) Ms.

Lemma sch_subst_arity : forall X U M,
    sch_arity (sch_subst X U M) = sch_arity M.
Proof.
  intros.
  destruct M.
  simpl.
  apply map_length.
Qed.

Hint Rewrite sch_subst_arity : rew_sch_arity.

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

Lemma scheme_aux_subset : forall L1 L2 M,
    scheme_aux L1 M ->
    subset L1 L2 ->
    scheme_aux L2 M.
Proof.
  introv Hs Hsub.
  destruct Hs.
  eauto using fresh_subset.
Qed.

(** Schemes are stable by type substitution *)

Lemma sch_subst_scheme_aux : forall L M Zs Us,
    types Us -> subset (from_list Zs) L ->
    scheme_aux L (sch_subst Zs Us M) <-> scheme_aux L M.
Proof.
  introv Hu Hsub.
  split.
  - introv Hs.
    inversion Hs as [? ? H]; subst.
    apply scheme_aux_c.
    autorewrite with rew_sch_arity in *.
    introv Hf.
    assert (fresh L (sch_arity M) Xs) as Hf2 by auto.
    specialize (H Xs Hf2).
    inversion H as [? ? Hrs Ht]; subst.
    simpl in *.
    rewrite <- rng_subst_list_open_vars in Hrs; auto.
    rewrite rng_subst_range_list in Hrs; auto.
    rewrite <- sch_subst_instance_vars in Ht; auto.
    rewrite typ_subst_type in Ht; auto.
  - introv Hs.
    inversion Hs as [? ? H]; subst.
    apply scheme_aux_c.
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
    rewrite sch_subst_instance_vars in Ht; auto.
Qed.

Lemma sch_subst_scheme : forall M Zs Us,
    types Us -> scheme (sch_subst Zs Us M) <-> scheme M.
Proof.
  introv Hu.
  split.
  - introv Hs.
    inversion Hs as [L ? Hsa]; subst.
    apply scheme_c with (L := L \u (from_list Zs)).
    apply scheme_aux_subset
      with (L2 := L \u (from_list Zs)) in Hsa;
      auto using subset_union_weak_l.
    rewrite <- sch_subst_scheme_aux
      with (Zs := Zs) (Us := Us);
        auto using subset_union_weak_r.
  - introv Hs.
    inversion Hs as [L ? Hsa]; subst.
    apply scheme_c with (L := L \u from_list Zs).
    apply scheme_aux_subset
      with (L2 := L \u (from_list Zs)) in Hsa;
      auto using subset_union_weak_l.
    rewrite sch_subst_scheme_aux;
      auto using subset_union_weak_r.
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

(* *************************************************************** *)
(** ** Type Environments *)

Definition tenv_subst Zs Us E :=
  map (rng_subst Zs Us) E.

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

Lemma tenv_subst_type_environment_extension :
  forall E1 E2 E3 Xs Rs Us,
    types Us ->
    type_environment_extension (E1 & Xs ~* Rs & E2) E3 ->
    type_environment_extension (tenv_subst Xs Us (E1 & E2))
      (tenv_subst Xs Us E3).
Proof.
  introv Hts He.
  remember (E1 & Xs ~* Rs & E2) as E12.
  induction He; subst; autorewrite with rew_tenv_subst in *; auto.
  apply type_environment_extension_push;
    rewrite ?rng_subst_range;
      autorewrite with rew_tenv_dom; auto.
Qed. 

Lemma tenv_subst_type_environment : forall E1 E2 Xs Rs Us,
    types Us ->
    type_environment (E1 & Xs ~* Rs & E2) ->
    type_environment (tenv_subst Xs Us (E1 & E2)).
Proof.
  introv Hts He.
  apply type_environment_remove in He.
  remember (E1 & E2) as E12.
  clear HeqE12.
  induction He; autorewrite with rew_tenv_subst; auto.
  apply type_environment_extension_push;
    rewrite ?rng_subst_range;
      autorewrite with rew_tenv_dom; auto.
Qed. 

(* *************************************************************** *)
(** ** Environments *)

Definition env_subst Zs Us D :=
  map (sch_subst Zs Us) D.

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

Lemma env_dom_subst : forall Zs Us D,
    dom (env_subst Zs Us D) = dom D.
Proof.
  intros.
  induction D using env_ind;
    autorewrite with rew_env_subst rew_env_dom.
  - reflexivity.
  - rewrite IHD. reflexivity.
Qed.

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

(* *************************************************************** *)
(** ** Store types *)

Definition styp_subst Zs Us P :=
  map (typ_subst Zs Us) P.

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

Hint Rewrite styp_dom_subst : rew_styp_dom.

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

(* **************************************************** *)
(** ** Terms *)

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

Lemma trm_fv_list_fvars : forall xs,
    trm_fv_list (trm_fvars xs) = from_list xs.
Proof.
  induction xs; auto; simpl.
  rewrite from_list_cons.
  rewrite IHxs.
  reflexivity.
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

Lemma trm_subst_first_intro : forall x u us t,
    x \notin (trm_fv t \u trm_fv_list us) -> term u ->
    t ^^* (cons u us) =
    trm_subst_single x u (t ^^* (cons (trm_fvar x) us)).
Proof.
  introv Hn Ht.
  unfold trm_subst_single.
  rewrite trm_subst_open; auto.
  rewrite trm_subst_fresh; auto.
  simpl; case_var.
  rewrite trm_subst_fresh_list; auto.
Qed.

Lemma trm_subst_single_intro : forall x u t,
    x \notin (trm_fv t) -> term u ->
    t ^^ u = trm_subst_single x u (t ^ x).
Proof.
  introv Hn Ht.
  rewrite trm_subst_intro with (xs := x :: nil); auto using terms.
Qed.

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

