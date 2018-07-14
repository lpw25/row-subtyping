(************************************************
 *          Row Subtyping - Well-formedness     *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import List LibLN Cofinite Definitions Substitution.

(* *************************************************************** *)
(** ** Automation *)

Hint Constructors
  kind type scheme_vars term environment store store_type.

Hint Extern 1 (types _ _) => split; auto.

Tactic Notation "econstr" tactic(tac1) "then" tactic(tac2) :=
  try (econstructor; try (try tac1; eassumption); solve [tac2]).

Tactic Notation "econstr" tactic(tac) :=
  econstr idtac then tac.

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

Hint Resolve term_abs_body term_let_body
     term_match_body term_destruct_body.

(** Terms are stable by substitution *)

Lemma trm_subst_term : forall t z u,
  term u -> term t -> term ([z ~> u]t).
Proof.
  induction 2; simpls*.
  - case_var*.
  - apply_fresh term_abs as y. rewrite* trm_subst_open_var.
  - apply_fresh* term_let as y. rewrite* trm_subst_open_var.
  - apply_fresh* term_match as y; rewrite* trm_subst_open_var.
  - apply_fresh* term_destruct as y; rewrite* trm_subst_open_var.
Qed.

(** ** Opening a body with a term gives a term *)

Lemma trm_open_term : forall t u,
  term_body t -> term u -> term (t ^^ u).
Proof.
  intros. destruct H. pick_fresh y.
  rewrite (@trm_subst_intro y); auto.
  apply trm_subst_term; auto.
Qed.

Hint Resolve trm_open_term.

Lemma trm_open_term_var : forall t x,
  term_body t -> term (t ^ x).
Proof.
  introv Ht.
  apply trm_open_term; auto.
Qed.

Hint Resolve trm_open_term_var.

(* =============================================================== *)
(** * Properties of types *)

(** Types of fvars *)
Lemma types_fvars : forall Xs n,
    n = length Xs ->
    types n (typ_fvars Xs).
Proof.
  introv Hl.
  unfold types.
  split.
  - generalize dependent n.
    induction Xs; introv Hl; simpl in *; auto.
    destruct n; try discriminate.
    auto.
  - generalize dependent n.
    induction Xs; introv Hl; simpl in *; eauto.
Qed.

Hint Resolve types_fvars.
 
(** Types are stable by type substitution *)

Lemma typ_subst_type : forall T Z U,
  type U -> type (typ_subst Z U T) <-> type T.
Proof.
  introv Htu.
  split.
  - introv Ht.
    induction T; simpl in Ht; inversion Ht; auto.
  - introv Ht.
    induction Ht; simpls*. case_var*.
Qed.

(** Types are stable by iterated type substitution *)

Lemma typ_substs_types : forall Xs Us T,
  types (length Xs) Us ->
  type T ->
  type (typ_substs Xs Us T).
Proof.
  induction Xs; destruct Us; simpl; introv TU TT; auto.
  destruct TU. simpls. inversions H. inversions* H0.
  apply IHXs; auto.
  rewrite typ_subst_type; auto.
Qed.

(** List of types are stable by type substitution *)

Lemma typ_subst_type_list : forall Z U Ts,
  type U -> types (length Ts) Ts -> 
  types (length Ts) (List.map (typ_subst Z U) Ts).
Proof.
  introv Ht Hts.
  induction Ts; simpl in *; auto.
  rewrite types_cons in *.
  destruct Hts.
  split; auto.
  rewrite typ_subst_type; auto.
Qed.

(* =============================================================== *)
(** * Properties of kinds *)

(** Kinds are stable by type substitution *)

Lemma knd_subst_kind : forall K Z U,
  type U -> kind (knd_subst Z U K) <-> kind K.
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

(* =============================================================== *)
(** * Properties of schemes *)

Lemma scheme_empty_type : forall T,
    type T <-> scheme (sch_empty T).
Proof.
  split.
  - introv Ht.
    eexists \{}.
    simpl.
    introv Fr.
    fresh_length Fr as Hl.
    destruct Xs; try discriminate.
    auto.
  - introv [L Hs].
    simpl in Hs.
    specialize (Hs nil I).
    inversion Hs.
    auto.
Qed.

Hint Resolve -> scheme_empty_type.

(** Schemes are stable by type substitution *)

Lemma sch_subst_vars_type : forall M Xs Z U,
  fresh \{Z} (sch_arity M) Xs -> 
  type U ->
  scheme_vars (sch_subst Z U M) Xs <-> scheme_vars M Xs.
Proof.
  introv Hf Ht.
  split.
  - introv Hs.
    generalize dependent M.
    induction Xs; introv Hl Hs.
    + destruct M; simpl in Hs; inversion Hs; subst.
      apply scheme_vars_empty.
      rewrite <- typ_subst_type with (Z := Z) (U := U); auto.
    + { destruct M; simpl in Hs; inversion Hs; subst.
        apply scheme_vars_bind.
        - rewrite <- knd_subst_kind with (Z := Z) (U := U); auto.
        - destruct Hl.
          apply IHXs; autorewrite with rew_sch_arity; auto.
          rewrite <- sch_subst_open_var; auto. }
  - introv Hs.
    induction Hs; simpl.
    + apply scheme_vars_empty.
      rewrite typ_subst_type with (Z := Z) (U := U); auto.
    + { destruct Hf.
        autorewrite with rew_sch_arity in *.
        apply scheme_vars_bind. 
        - rewrite knd_subst_kind with (Z := Z) (U := U); auto.
        - rewrite sch_subst_open_var; auto. }
Qed.

Lemma sch_subst_type : forall M Z U,
    type U -> scheme (sch_subst Z U M) <-> scheme M.
Proof.
  introv Ht.
  split.
  - introv [L Hs].
    exists (L \u \{Z}). introv Hf.
    autorewrite with rew_sch_arity in *.
    rewrite <- sch_subst_vars_type with (Z := Z) (U := U); auto.
  - introv [L Hs].
    exists (\{Z} \u L \u (typ_fv U)). introv Hf.
    autorewrite with rew_sch_arity in *.
    apply sch_subst_vars_type; auto.
Qed.

(** ** Instantiating a scheme with types gives a type *)

Lemma scheme_vars_instance_type : forall M Xs,
  scheme_vars M Xs -> type (instance_vars M Xs).
Proof.
  unfold instance_vars.
  introv Hs.
  generalize dependent M.
  induction Xs; introv Hs; simpl.
  - inversion Hs; subst; auto.
  - inversion Hs; subst.
    unfold sch_open_var in *.
    auto.
Qed.

Lemma scheme_instance_type : forall M Us,
    types (sch_arity M) Us ->
    scheme M -> type (instance M Us).
Proof.
  introv Hts [L Hs].
  pick_freshes (sch_arity M) Xs.
  rewrite typ_substs_intro_instance with (Xs := Xs); auto.
  fresh_length Fr as Hl.
  rewrite Hl in *.
  apply typ_substs_types; auto.
  apply scheme_vars_instance_type; auto.
Qed.

Lemma scheme_bind_inv_sch : forall K M X,
    scheme (sch_bind K M) -> scheme (M ^ X).
Proof.
  introv [L Hs].
  pick_fresh Y.
  unfold sch_open_var.
  rewrite sch_subst_intro with (X := Y); auto.
  apply sch_subst_type; auto.
  exists (L \u \{Y}).
  introv Hf.
  specialize (Hs (Y :: Xs)).
  simpl in Hs.
  autorewrite with rew_sch_arity in Hf.
  assert (scheme_vars (sch_bind K M) (Y :: Xs)) as Hsb by auto.
  inversion Hsb; subst; auto.
Qed.  

Lemma scheme_bind_inv_knd : forall K M,
    scheme (sch_bind K M) -> kind K.
Proof.
  introv [L Hs].
  pick_freshes_gen L (sch_arity (sch_bind K M)) Xs.
  fresh_length Fr as Hl.
  specialize (Hs Xs Fr).
  inversion Hs.
  auto.
Qed.  

(* =============================================================== *)
(** * Properties of environment *)

Lemma ok_from_environment : forall E,
  environment E -> ok E.
Proof.
  introv He.
  induction He; auto. 
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

Lemma environment_retract : forall E F,
    environment (E & F) -> environment E.
Proof.
  introv He.
  induction F using env_ind;
    autorewrite with rew_env_concat in *; auto.
  remember (E & F & x ~ v) as G.
  destruct He.
  - destruct (empty_concat_inv HeqG) as [_ Hem].
    apply empty_single_inv in Hem.
    contradiction.
  - destruct (eq_push_inv HeqG) as [_ [_ Hem]].
    rewrite Hem in He.
    auto.
  - destruct (eq_push_inv HeqG) as [_ [_ Hem]].
    rewrite Hem in He.
    auto.
Qed.

Lemma env_subst_environment : forall X U E,
    type U ->
    environment E -> environment (env_subst X U E).
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

Lemma environment_kinds : forall E Xs M,
    environment E ->
    (fresh (dom E) (sch_arity M) Xs) ->
    scheme M ->
    environment (E & Xs ~::* M).
Proof.
  introv He Hf Hs.
  fresh_length Hf as Hl.
  rewrite <- (concat_empty_r E) in *.
  generalize dependent (@empty bind).
  generalize dependent M.
  induction Xs; intros M Hs Hl F He Hf; simpl.
  - autorewrite with rew_env_concat; auto.
  - destruct M.
    + autorewrite with rew_env_concat; auto.
    + { destruct Hf.
        rewrite concat_assoc.
        rewrite <- (concat_assoc E).
        apply IHXs.
        - apply scheme_bind_inv_sch with (K := k); auto.
        - simpl in Hl; autorewrite with rew_sch_arity; auto.
        - rewrite concat_assoc.
          apply environment_knd; auto.
          apply scheme_bind_inv_knd with (M := M).
          auto.
        - autorewrite with rew_env_dom in *.
          autorewrite with rew_sch_arity.
          auto. }
Qed.

Lemma environment_knd_inv : forall E X K,
    environment (E & X ~:: K) ->
    kind K /\ X # E.
Proof.
  introv He.
  remember (E & X ~:: K) as F eqn:Hf.
  destruct He.
  - apply empty_push_inv in Hf; contradiction.
  - destruct (eq_push_inv Hf) as [? [Hk ?]].
    inversion Hk.
    subst.
    auto.
  - destruct (eq_push_inv Hf) as [_ [Hk _]].
    discriminate.
Qed.

Lemma environment_typ_inv : forall E x M,
    environment (E & x ~: M) ->
    scheme M /\ x # E.
Proof.
  introv He.
  remember (E & x ~: M) as F eqn:Hf.
  destruct He.
  - apply empty_push_inv in Hf; contradiction.
  - destruct (eq_push_inv Hf) as [_ [Hm _]].
    discriminate.
  - destruct (eq_push_inv Hf) as [? [Hm ?]].
    inversion Hm.
    subst.
    auto.
Qed.

Lemma environment_knd_weakening : forall E F G X K,
    X # F ->
    environment (E & G & X ~:: K) ->
    environment (E & F & G) ->
    environment (E & F & G & X ~:: K).
Proof.
  introv Hin He1 He2.
  destruct (environment_knd_inv He1).
  auto.
Qed.

Lemma environment_typ_weakening : forall E F G x M,
    x # F ->
    environment (E & G & x ~: M) ->
    environment (E & F & G) ->
    environment (E & F & G & x ~: M).
Proof.
  introv Hin He1 He2.
  destruct (environment_typ_inv He1).
  auto.
Qed.

Lemma environment_kinds_weakening : forall E F G Xs M,
    fresh (dom F) (sch_arity M) Xs ->
    environment (E & G & Xs ~::* M) ->
    environment (E & F & G) ->
    environment (E & F & G & Xs ~::* M).
Proof.
  introv Hf He1 He2.
  fresh_length Hf as Hl.
  generalize dependent G.
  generalize dependent M.
  induction Xs; introv Hf Hl He1 He2; subst; simpl.
  - autorewrite with rew_env_concat; auto.
  - destruct M; simpl in Hl; try discriminate.
    simpl in He1.
    autorewrite with rew_env_concat in *.
    destruct Hf.
    inversion Hl.
    rewrite <- concat_assoc with (E := E & F).
    apply IHXs with (G := G & a ~:: k);
      autorewrite with rew_sch_arity;
      autorewrite with rew_env_dom;
      autorewrite with rew_env_concat; auto.
    apply environment_knd_weakening;
      eauto using environment_retract.
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

Lemma styp_subst_store_type : forall P Z U,
  type U -> store_type (styp_subst Z U P) <-> store_type P.
Proof.
  introv Ht.
  split.
  - introv Hs.
    induction P using env_ind; autorewrite with rew_styp_subst in Hs;
      auto.
    remember (styp_subst Z U P & x ~ typ_subst Z U v) as Q.
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

Inductive valid_kind_regular : env -> knd -> Prop :=
  | valid_kind_regular_type : forall E,
      valid_env_regular E ->
      environment E ->
      valid_kind_regular E knd_type
  | valid_kind_regular_row :  forall E cs,
      valid_env_regular E ->
      CSet.Nonempty cs ->
      environment E ->
      valid_kind_regular E (knd_row cs)
  | valid_kind_regular_range : forall E T1 T2,
      subtype_regular E T2 T1 CSet.universe ->
      environment E ->
      type T1 ->
      type T2 ->
      valid_kind_regular E (knd_range T1 T2)

with kinding_regular : env -> typ -> knd -> Prop :=
  | kinding_regular_var : forall E X K,
      valid_env_regular E ->
      binds X (bind_knd K) E ->
      environment E ->
      kind K ->
      kinding_regular E (typ_fvar X) K
  | kinding_regular_constructor : forall E c T cs,
      kinding_regular E T knd_type ->
      cs = CSet.singleton c ->
      environment E ->
      type T ->
      kinding_regular E (typ_constructor c T) (knd_row cs)
  | kinding_regular_or : forall E T1 T2 cs1 cs2 cs12,
      kinding_regular E T1 (knd_row cs1) ->
      kinding_regular E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      kinding_regular E (typ_or cs1 T1 cs2 T2) (knd_row cs12)
  | kinding_regular_proj : forall E T cs cs',
      kinding_regular E T (knd_row cs) ->
      CSet.Subset cs' cs ->
      CSet.Nonempty cs' ->
      environment E ->
      type T ->
      CSet.Nonempty cs ->
      kinding_regular E (typ_proj cs T cs') (knd_row cs')
  | kinding_regular_variant : forall E T,
      kinding_regular E T
        (knd_range (typ_top CSet.universe) (typ_bot CSet.universe)) ->
      environment E ->
      type T ->
      kinding_regular E (typ_variant T) knd_type
  | kinding_regular_arrow : forall E T1 T2,
      kinding_regular E T1 knd_type -> 
      kinding_regular E T2 knd_type -> 
      environment E ->
      type T1 ->
      type T2 ->
      kinding_regular E (typ_arrow T1 T2) knd_type
  | kinding_regular_ref : forall E T,
      kinding_regular E T knd_type ->
      environment E ->
      type T ->
      kinding_regular E (typ_ref T) knd_type
  | kinding_regular_unit : forall E,
      valid_env_regular E ->
      environment E ->
      kinding_regular E typ_unit knd_type
  | kinding_regular_top : forall E cs,
      valid_env_regular E ->
      CSet.Nonempty cs ->
      environment E ->
      kinding_regular E (typ_top cs) (knd_row cs)
  | kinding_regular_bot : forall E cs,
      valid_env_regular E ->
      CSet.Nonempty cs ->
      environment E ->
      kinding_regular E (typ_bot cs) (knd_row cs)
  | kinding_regular_meet : forall E T1 T2 cs,
      kinding_regular E T1 (knd_row cs) ->
      kinding_regular E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      kinding_regular E (typ_meet T1 T2) (knd_row cs)
  | kinding_regular_join : forall E T1 T2 cs,
      kinding_regular E T1 (knd_row cs) ->
      kinding_regular E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      kinding_regular E (typ_join T1 T2) (knd_row cs)
  | kinding_regular_range_subsumption : forall E T T1 T2 T1' T2',
      kinding_regular E T (knd_range T1 T2) ->
      subtype_regular E T1 T1' CSet.universe ->
      subtype_regular E T2' T2 CSet.universe ->
      environment E ->
      type T ->
      type T1 ->
      type T2 ->
      type T1' ->
      type T2' ->
      kinding_regular E T (knd_range T1' T2')

with valid_scheme_vars_regular : env -> sch -> list var -> Prop :=
  | valid_scheme_vars_regular_empty : forall E T,
      kinding_regular E T knd_type ->
      environment E ->
      type T ->
      valid_scheme_vars_regular E (sch_empty T) nil
  | valid_scheme_vars_regular_bind : forall X Xs E K M,
      valid_kind_regular E K ->
      valid_scheme_vars_regular (E & X ~:: K) (M ^ X) Xs ->
      environment E ->
      environment (E & X ~:: K) ->
      kind K ->
      scheme_vars (M ^ X) Xs ->
      scheme_vars (sch_bind K M) (X :: Xs) ->
      valid_scheme_vars_regular E (sch_bind K M) (X :: Xs)

with valid_scheme_regular : env -> sch -> Prop :=
  | valid_scheme_regular_c : forall E M L,
      (forall Xs,
          fresh L (sch_arity M) Xs ->
          valid_scheme_vars_regular E M Xs) ->
      environment E ->
      scheme M ->
      valid_scheme_regular E M

with valid_env_regular : env -> Prop :=
  | valid_env_regular_empty :
      valid_env_regular empty
  | valid_env_regular_kind : forall E X K,
      valid_env_regular E ->
      valid_kind_regular E K ->
      X # E ->
      environment E ->
      environment (E & X ~:: K) ->
      kind K ->
      valid_env_regular (E & X ~:: K)
  | valid_env_regular_type : forall E x M,
      valid_env_regular E ->
      valid_scheme_regular E M ->
      x # E ->
      environment E ->
      environment (E & x ~: M) ->
      scheme M ->
      valid_env_regular (E & x ~: M)

with type_equal_core_regular : env -> typ -> typ -> knd -> Prop :=
  | type_equal_core_regular_or_commutative :
      forall E T1 T2 cs1 cs2 cs12,
      kinding_regular E T1 (knd_row cs1) ->
      kinding_regular E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      type_equal_core_regular E
        (typ_or cs1 T1 cs2 T2) (typ_or cs2 T2 cs1 T1) (knd_row cs12)
  | type_equal_core_regular_or_associative :
      forall E T1 cs1 T2 cs2 T3 cs3 cs12 cs23 cs123,
      kinding_regular E T1 (knd_row cs1) ->
      kinding_regular E T2 (knd_row cs2) ->
      kinding_regular E T3 (knd_row cs3) ->
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
      type_equal_core_regular E
        (typ_or cs1 T1 cs23 (typ_or cs2 T2 cs3 T3))
        (typ_or cs12 (typ_or cs1 T1 cs2 T2) cs3 T3)
        (knd_row cs123)
  | type_equal_core_regular_or_bot : forall E cs1 cs2 cs12,
      valid_env_regular E ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type_equal_core_regular E
        (typ_or cs1 (typ_bot cs1) cs2 (typ_bot cs2)) (typ_bot cs12)
        (knd_row cs12)
  | type_equal_core_regular_or_top : forall E cs1 cs2 cs12,
      valid_env_regular E ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type_equal_core_regular E
        (typ_or cs1 (typ_top cs1) cs2 (typ_top cs2)) (typ_top cs12)
        (knd_row cs12)
  | type_equal_core_regular_or_meet_distribution :
      forall E T1 T2 T3 T4 cs1 cs2 cs12,
      kinding_regular E T1 (knd_row cs1) ->
      kinding_regular E T2 (knd_row cs2) ->
      kinding_regular E T3 (knd_row cs1) ->
      kinding_regular E T4 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      type T4 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      type_equal_core_regular E
        (typ_or cs1 (typ_meet T1 T3) cs2 (typ_meet T2 T4))
        (typ_meet (typ_or cs1 T1 cs2 T2) (typ_or cs1 T3 cs2 T4))
        (knd_row cs12)
  | type_equal_core_regular_or_join_distribution :
      forall E T1 T2 T3 T4 cs1 cs2 cs12,
      kinding_regular E T1 (knd_row cs1) ->
      kinding_regular E T2 (knd_row cs2) ->
      kinding_regular E T3 (knd_row cs1) ->
      kinding_regular E T4 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      type T4 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      type_equal_core_regular E
        (typ_or cs1 (typ_join T1 T3) cs2 (typ_join T2 T4))
        (typ_join (typ_or cs1 T1 cs2 T2) (typ_or cs1 T3 cs2 T4))
        (knd_row cs12)
  | type_equal_core_regular_or_proj : forall E T cs1 cs2 cs3 cs23,
      kinding_regular E T (knd_row cs1) ->
      CSet.Disjoint cs2 cs3 ->
      CSet.Subset cs2 cs1 ->
      CSet.Nonempty cs2 ->
      CSet.Subset cs3 cs1 ->
      CSet.Nonempty cs3 ->
      cs23 = CSet.union cs2 cs3 ->
      environment E ->
      type T ->
      CSet.Nonempty cs1 ->
      type_equal_core_regular E
        (typ_or cs2 (typ_proj cs1 T cs2) cs3 (typ_proj cs1 T cs3))
        (typ_proj cs1 T cs23)
        (knd_row cs23)
  | type_equal_core_regular_proj_id : forall E T cs,
      kinding_regular E T (knd_row cs) ->
      environment E ->
      type T ->
      CSet.Nonempty cs ->
      type_equal_core_regular E (typ_proj cs T cs) T (knd_row cs)
  | type_equal_core_regular_proj_compose : forall E T cs1 cs2 cs3,
      kinding_regular E T (knd_row cs1) ->
      CSet.Subset cs2 cs1 ->
      CSet.Subset cs3 cs2 ->
      CSet.Nonempty cs3 ->
      environment E ->
      type T ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      type_equal_core_regular E
        (typ_proj cs2 (typ_proj cs1 T cs2) cs3)
        (typ_proj cs1 T cs3)
        (knd_row cs3)
  | type_equal_core_regular_proj_or_l :
      forall E T1 T2 cs1 cs1' cs2 cs12,
      kinding_regular E T1 (knd_row cs1) ->
      kinding_regular E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      CSet.Subset cs1' cs1 ->
      CSet.Nonempty cs1' ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      type_equal_core_regular E
        (typ_proj cs12 (typ_or cs1 T1 cs2 T2) cs1')
        (typ_proj cs1 T1 cs1')
        (knd_row cs1')
  | type_equal_core_regular_proj_or_r :
      forall E T1 T2 cs1 cs2 cs2' cs12,
      kinding_regular E T1 (knd_row cs1) ->
      kinding_regular E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      CSet.Subset cs2' cs2 ->
      CSet.Nonempty cs2' ->
      cs12 = CSet.union cs1 cs2 ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      type_equal_core_regular E
        (typ_proj cs12 (typ_or cs1 T1 cs2 T2) cs2')
        (typ_proj cs2 T2 cs2')
        (knd_row cs2')
  | type_equal_core_regular_proj_or_both :
      forall E T1 T2 cs1 cs2 cs1' cs2' cs12 cs12',
      kinding_regular E T1 (knd_row cs1) ->
      kinding_regular E T2 (knd_row cs2) ->
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
      type_equal_core_regular E
        (typ_proj cs12 (typ_or cs1 T1 cs2 T2) cs12')
        (typ_or cs1' (typ_proj cs1 T1 cs1')
                cs2' (typ_proj cs2 T2 cs2'))
        (knd_row cs12')
  | type_equal_core_regular_proj_meet : forall E T1 T2 cs cs',
      kinding_regular E T1 (knd_row cs) ->
      kinding_regular E T2 (knd_row cs) ->
      CSet.Subset cs' cs ->
      CSet.Nonempty cs' ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      type_equal_core_regular E
        (typ_proj cs (typ_meet T1 T2) cs')
        (typ_meet (typ_proj cs T1 cs') (typ_proj cs T2 cs'))
        (knd_row cs')
  | type_equal_core_regular_proj_join : forall E T1 T2 cs cs',
      kinding_regular E T1 (knd_row cs) ->
      kinding_regular E T2 (knd_row cs) ->
      CSet.Subset cs' cs ->
      CSet.Nonempty cs' ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      type_equal_core_regular E
        (typ_proj cs (typ_join T1 T2) cs')
        (typ_join (typ_proj cs T1 cs') (typ_proj cs T2 cs'))
        (knd_row cs')
  | type_equal_core_regular_meet_commutative : forall E T1 T2 cs,
      kinding_regular E T1 (knd_row cs) ->
      kinding_regular E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      type_equal_core_regular E
        (typ_meet T1 T2) (typ_meet T2 T1) (knd_row cs)
  | type_equal_core_regular_meet_associative : forall E T1 T2 T3 cs,
      kinding_regular E T1 (knd_row cs) ->
      kinding_regular E T2 (knd_row cs) ->
      kinding_regular E T3 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      CSet.Nonempty cs ->
      type_equal_core_regular E
        (typ_meet T1 (typ_meet T2 T3))
        (typ_meet (typ_meet T1 T2) T3)
        (knd_row cs)
  | type_equal_core_regular_meet_identity : forall E T1 cs,
      kinding_regular E T1 (knd_row cs) ->
      environment E ->
      type T1 ->
      CSet.Nonempty cs ->
      type_equal_core_regular E
        (typ_meet T1 (typ_top cs)) T1 (knd_row cs)
  | type_equal_core_regular_meet_absorption : forall E T1 T2 cs,
      kinding_regular E T1 (knd_row cs) ->
      kinding_regular E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      type_equal_core_regular E
        (typ_meet T1 (typ_join T1 T2)) T1 (knd_row cs)
  | type_equal_core_regular_meet_distribution : forall E T1 T2 T3 cs,
      kinding_regular E T1 (knd_row cs) ->
      kinding_regular E T2 (knd_row cs) ->
      kinding_regular E T3 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      CSet.Nonempty cs ->
      type_equal_core_regular E
        (typ_meet T1 (typ_join T2 T3))
        (typ_join (typ_meet T1 T2) (typ_meet T1 T3))
        (knd_row cs)
  | type_equal_core_regular_join_commutative : forall E T1 T2 cs,
      kinding_regular E T1 (knd_row cs) ->
      kinding_regular E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      type_equal_core_regular E
        (typ_join T1 T2) (typ_join T2 T1) (knd_row cs)
  | type_equal_core_regular_join_associative : forall E T1 T2 T3 cs,
      kinding_regular E T1 (knd_row cs) ->
      kinding_regular E T2 (knd_row cs) ->
      kinding_regular E T3 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      CSet.Nonempty cs ->
      type_equal_core_regular E
        (typ_join T1 (typ_join T2 T3))
        (typ_join (typ_join T1 T2) T3)
        (knd_row cs)
  | type_equal_core_regular_join_identity : forall E T1 cs,
      kinding_regular E T1 (knd_row cs) ->
      environment E ->
      type T1 ->
      CSet.Nonempty cs ->
      type_equal_core_regular E
        (typ_join T1 (typ_bot cs)) T1 (knd_row cs)
  | type_equal_core_regular_join_absorption : forall E T1 T2 cs,
      kinding_regular E T1 (knd_row cs) ->
      kinding_regular E T2 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      type_equal_core_regular E
        (typ_join T1 (typ_meet T1 T2)) T1 (knd_row cs)
  | type_equal_core_regular_join_distribution : forall E T1 T2 T3 cs,
      kinding_regular E T1 (knd_row cs) ->
      kinding_regular E T2 (knd_row cs) ->
      kinding_regular E T3 (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      CSet.Nonempty cs ->
      type_equal_core_regular E
        (typ_join T1 (typ_meet T2 T3))
        (typ_meet (typ_join T1 T2) (typ_join T1 T3))
        (knd_row cs)

with type_equal_symm_regular : env -> typ -> typ -> knd -> Prop :=
  | type_equal_symm_regular_l : forall E T1 T2 K,
      type_equal_core_regular E T1 T2 K ->
      environment E ->
      type T1 ->
      type T2 ->
      kind K ->
      type_equal_symm_regular E T1 T2 K
  | type_equal_symm_regular_r : forall E T1 T2 K,
      type_equal_core_regular E T1 T2 K ->
      environment E ->
      type T1 ->
      type T2 ->
      kind K ->
      type_equal_symm_regular E T2 T1 K

with type_equal_cong_regular : env -> typ -> typ -> knd -> Prop :=
  | type_equal_cong_regular_constructor : forall E c T1 T1' cs,
      type_equal_cong_regular E T1 T1' knd_type ->
      cs = CSet.singleton c ->
      environment E ->
      type T1 ->
      type T1' ->
      type_equal_cong_regular E
        (typ_constructor c T1) (typ_constructor c T1')
        (knd_row cs)
  | type_equal_cong_regular_or_l : forall E T1 T1' T2 cs1 cs2 cs12,
      kinding_regular E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_cong_regular E T1 T1' (knd_row cs1) ->
      environment E ->
      type T1 ->
      type T1' ->
      type T2 ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      type_equal_cong_regular E
        (typ_or cs1 T1 cs2 T2) (typ_or cs1 T1' cs2 T2) (knd_row cs12)
  | type_equal_cong_regular_or_r : forall E T1 T2 T2' cs1 cs2 cs12,
      kinding_regular E T1 (knd_row cs1) ->
      CSet.Disjoint cs1 cs2 ->
      cs12 = CSet.union cs1 cs2 ->
      type_equal_cong_regular E T2 T2' (knd_row cs2) ->
      environment E ->
      type T1 ->
      type T2 ->
      type T2' ->
      CSet.Nonempty cs1 ->
      CSet.Nonempty cs2 ->
      type_equal_cong_regular E
        (typ_or cs1 T1 cs2 T2) (typ_or cs1 T1 cs2 T2') (knd_row cs12)
  | type_equal_cong_regular_proj : forall E T1 T1' cs1 cs2,
      CSet.Subset cs2 cs1 ->
      CSet.Nonempty cs2 ->
      type_equal_cong_regular E T1 T1' (knd_row cs1) ->
      environment E ->
      type T1 ->
      type T1' ->
      CSet.Nonempty cs1 ->
      type_equal_cong_regular E
        (typ_proj cs1 T1 cs2) (typ_proj cs1 T1' cs2) (knd_row cs2)
  | type_equal_cong_regular_arrow_l : forall E T1 T1' T2,
      kinding_regular E T2 knd_type ->
      type_equal_cong_regular E T1 T1' knd_type ->
      environment E ->
      type T1 ->
      type T1' ->
      type T2 ->
      type_equal_cong_regular E
        (typ_arrow T1 T2) (typ_arrow T1' T2) knd_type
  | type_equal_cong_regular_arrow_r : forall E T1 T2 T2',
      kinding_regular E T1 knd_type ->
      type_equal_cong_regular E T2 T2' knd_type ->
      environment E ->
      type T1 ->
      type T2 ->
      type T2' ->
      type_equal_cong_regular E
        (typ_arrow T1 T2) (typ_arrow T1 T2') knd_type
  | type_equal_cong_regular_ref : forall E T1 T1',
      type_equal_cong_regular E T1 T1' knd_type ->
      environment E ->
      type T1 ->
      type T1' ->
      type_equal_cong_regular E (typ_ref T1) (typ_ref T1') knd_type
  | type_equal_cong_regular_meet_l : forall E T1 T1' T2 cs,
      kinding_regular E T2 (knd_row cs) ->
      type_equal_cong_regular E T1 T1' (knd_row cs) ->
      environment E ->
      type T1 ->
      type T1' ->
      type T2 ->
      CSet.Nonempty cs ->
      type_equal_cong_regular E
        (typ_meet T1 T2) (typ_meet T1' T2) (knd_row cs)
  | type_equal_cong_regular_meet_r : forall E T1 T2 T2' cs,
      kinding_regular E T1 (knd_row cs) ->
      type_equal_cong_regular E T2 T2' (knd_row cs) -> 
      environment E ->
      type T1 ->
      type T2 ->
      type T2' ->
      CSet.Nonempty cs ->
      type_equal_cong_regular E
        (typ_meet T1 T2) (typ_meet T1 T2') (knd_row cs)
  | type_equal_cong_regular_join_l : forall E T1 T1' T2 cs,
      kinding_regular E T2 (knd_row cs) ->
      type_equal_cong_regular E T1 T1' (knd_row cs) ->
      environment E ->
      type T1 ->
      type T1' ->
      type T2 ->
      CSet.Nonempty cs ->
      type_equal_cong_regular E
        (typ_join T1 T2) (typ_join T1' T2) (knd_row cs)
  | type_equal_cong_regular_join_r : forall E T1 T2 T2' cs,
      kinding_regular E T1 (knd_row cs) ->
      type_equal_cong_regular E T2 T2' (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      type T2' ->
      CSet.Nonempty cs ->
      type_equal_cong_regular E
        (typ_join T1 T2) (typ_join T1 T2') (knd_row cs)
  | type_equal_cong_regular_symm : forall E T1 T1' K,
      type_equal_symm_regular E T1 T1' K ->
      environment E ->
      type T1 ->
      type T1' ->
      kind K ->
      type_equal_cong_regular E T1 T1' K

with type_equal_regular : env -> typ -> typ -> knd -> Prop :=
  | type_equal_regular_refl : forall E T K,
      kinding_regular E T K ->
      environment E ->
      type T ->
      kind K ->
      type_equal_regular E T T K
  | type_equal_regular_step : forall E T1 T2 T3 K,
      type_equal_cong_regular E T1 T2 K ->
      type_equal_regular E T2 T3 K ->
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      kind K ->
      type_equal_regular E T1 T3 K

with subtype_regular : env -> typ -> typ -> cset -> Prop :=
  | subtype_regular_c : forall E T1 T2 cs,
      type_equal_regular E T1 (typ_meet T1 T2) (knd_row cs) ->
      environment E ->
      type T1 ->
      type T2 ->
      CSet.Nonempty cs ->
      subtype_regular E T1 T2 cs.

Scheme valid_kind_regular_mutind :=
         Induction for valid_kind_regular Sort Prop
  with kinding_regular_mutind :=
         Induction for kinding_regular Sort Prop
  with valid_scheme_vars_regular_mutind :=
         Induction for valid_scheme_vars_regular Sort Prop
  with valid_scheme_regular_mutind :=
         Induction for valid_scheme_regular Sort Prop
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
       valid_scheme_vars_regular_mutind, valid_scheme_regular_mutind,
       valid_env_regular_mutind, type_equal_core_regular_mutind,
       type_equal_symm_regular_mutind, type_equal_cong_regular_mutind,
       type_equal_regular_mutind, subtype_regular_mutind.

Lemma valid_kind_regular_inv : forall E K,
    valid_kind_regular E K ->
    environment E /\ kind K.
Proof.
  introv Hv.
  destruct Hv; auto.
Qed.

Hint Constructors valid_kind_regular : valid_kind_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_kind_regular E _ |- _ =>
      apply (proj1 (valid_kind_regular_inv H))
  end : valid_kind_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : valid_kind_regular _ K |- _ =>
      apply (proj2 (valid_kind_regular_inv H))
  end : valid_kind_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : valid_kind_regular _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj2 (valid_kind_regular_inv H));
      inversion Hknd; assumption
  end : valid_kind_regular.

Lemma kinding_regular_inv : forall E T K,
    kinding_regular E T K ->
    environment E /\ type T /\ kind K.
Proof.
  introv Hk.
  destruct Hk; auto with csetdec.
Qed.

Hint Constructors kinding_regular : kinding_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : kinding_regular E _ _ |- _ =>
      apply (proj31 (kinding_regular_inv H))
  end : kinding_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : kinding_regular _ T _ |- _ =>
      apply (proj32 (kinding_regular_inv H))
  end : kinding_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : kinding_regular _ _ K |- _ =>
      apply (proj33 (kinding_regular_inv H))
  end : kinding_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : kinding_regular _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj33 (kinding_regular_inv H));
      inversion Hknd; assumption
  end : kinding_regular.

Lemma valid_scheme_vars_regular_inv : forall E M Xs,
    valid_scheme_vars_regular E M Xs ->
    environment E /\ scheme_vars M Xs.
Proof.
  introv Hs.
  destruct Hs; auto.
Qed.

Hint Constructors valid_scheme_vars_regular
  : valid_scheme_vars_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_scheme_vars_regular E _ _ |- _ =>
      apply (proj1 (valid_scheme_vars_regular_inv H))
  end : valid_scheme_vars_regular.

Hint Extern 1 (scheme_vars ?M ?Xs) =>
  match goal with
  | H : valid_scheme_vars_regular _ M Xs |- _ =>
      apply (proj2 (valid_scheme_vars_regular_inv H))
  end : valid_scheme_vars_regular.

Lemma valid_scheme_regular_inv : forall E M,
    valid_scheme_regular E M ->
    environment E /\ scheme M.
Proof.
  introv Hs.
  destruct Hs; auto.
Qed.

Hint Constructors valid_scheme_regular : valid_scheme_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_scheme_regular E _ |- _ =>
      apply (proj1 (valid_scheme_regular_inv H))
  end : valid_scheme_regular.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H : valid_scheme_regular _ M |- _ =>
      apply (proj2 (valid_scheme_regular_inv H))
  end : valid_scheme_regular.

Lemma valid_env_regular_inv : forall E,
    valid_env_regular E -> environment E.
Proof.
  introv He.
  destruct He; auto.
Qed.

Hint Constructors valid_env_regular : valid_env_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_env_regular E |- _ =>
      apply (valid_env_regular_inv H)
  end : valid_env_regular.

Lemma type_equal_core_regular_inv : forall E T1 T2 K,
    type_equal_core_regular E T1 T2 K ->
    environment E /\ type T1 /\ type T2 /\ kind K.
Proof.
  introv Hte.
  destruct Hte; subst; split; auto with csetdec.
Qed.

Hint Constructors type_equal_core_regular : type_equal_core_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_core_regular E _ _ _ |- _ =>
      apply (proj41 (type_equal_core_regular_inv H))
  end : type_equal_core_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_core_regular _ T _ _ |- _ =>
      apply (proj42 (type_equal_core_regular_inv H))
  | H : type_equal_core_regular _ _ T _ |- _ =>
      apply (proj43 (type_equal_core_regular_inv H))
  end : type_equal_core_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_core_regular _ _ _ K |- _ =>
      apply (proj44 (type_equal_core_regular_inv H))
  end : type_equal_core_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_core_regular _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_core_regular_inv H));
      inversion Hknd; assumption
  end : type_equal_core_regular.

Lemma type_equal_symm_regular_inv : forall E T1 T2 K,
    type_equal_symm_regular E T1 T2 K ->
    environment E /\ type T1 /\ type T2 /\ kind K.
Proof.
  introv Hte.
  destruct Hte; auto.
Qed.

Hint Constructors type_equal_symm_regular : type_equal_symm_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_symm_regular E _ _ _ |- _ =>
      apply (proj41 (type_equal_symm_regular_inv H))
  end : type_equal_symm_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_symm_regular _ T _ _ |- _ =>
      apply (proj42 (type_equal_symm_regular_inv H))
  | H : type_equal_symm_regular _ _ T _ |- _ =>
      apply (proj43 (type_equal_symm_regular_inv H))
  end : type_equal_symm_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_symm_regular _ _ _ K |- _ =>
      apply (proj44 (type_equal_symm_regular_inv H))
  end : type_equal_symm_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_symm_regular _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_symm_regular_inv H));
      inversion Hknd; assumption
  end : type_equal_symm_regular.

Lemma type_equal_cong_regular_inv : forall E T1 T2 K,
    type_equal_cong_regular E T1 T2 K ->
    environment E /\ type T1 /\ type T2 /\ kind K.
Proof.
  introv Hte.
  destruct Hte; split; auto with csetdec.
Qed.

Hint Constructors type_equal_cong_regular : type_equal_cong_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_cong_regular E _ _ _ |- _ =>
      apply (proj41 (type_equal_cong_regular_inv H))
  end : type_equal_cong_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_cong_regular _ T _ _ |- _ =>
      apply (proj42 (type_equal_cong_regular_inv H))
  | H : type_equal_cong_regular _ _ T _ |- _ =>
      apply (proj43 (type_equal_cong_regular_inv H))
  end : type_equal_cong_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_cong_regular _ _ _ K |- _ =>
      apply (proj44 (type_equal_cong_regular_inv H))
  end : type_equal_cong_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_cong_regular _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_cong_regular_inv H));
      inversion Hknd; assumption
  end : type_equal_cong_regular.

Lemma type_equal_regular_inv : forall E T1 T2 K,
    type_equal_regular E T1 T2 K ->
    environment E /\ type T1 /\ type T2 /\ kind K.
Proof.
  introv Hk.
  destruct Hk; auto.
Qed.

Hint Constructors type_equal_regular : type_equal_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_regular E _ _ _ |- _ =>
      apply (proj41 (type_equal_regular_inv H))
  end : type_equal_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_regular _ T _ _ |- _ =>
      apply (proj42 (type_equal_regular_inv H))
  | H : type_equal_regular _ _ T _ |- _ =>
      apply (proj43 (type_equal_regular_inv H))
  end : type_equal_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_regular _ _ _ K |- _ =>
      apply (proj44 (type_equal_regular_inv H))
  end : type_equal_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_regular _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_regular_inv H));
      inversion Hknd; assumption
  end : type_equal_regular.

Lemma subtype_regular_inv : forall E T1 T2 cs,
    subtype_regular E T1 T2 cs ->
    environment E /\ type T1 /\ type T2 /\ CSet.Nonempty cs.
Proof.
  introv Hk.
  destruct Hk; auto.
Qed.

Hint Constructors subtype_regular : subtype_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : subtype_regular E _ _ _ |- _ =>
      apply (proj41 (subtype_regular_inv H))
  end : subtype_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : subtype_regular _ T _ _ |- _ =>
      apply (proj42 (subtype_regular_inv H))
  | H : subtype_regular _ _ T _ |- _ =>
      apply (proj43 (subtype_regular_inv H))
  end : subtype_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : subtype_regular _ _ _ cs |- _ =>
      apply (proj44 (subtype_regular_inv H))
  end : subtype_regular.

Lemma regular_combined_kinding :
  (forall E K, valid_kind E K -> valid_kind_regular E K)
  /\ (forall E T K, kinding E T K -> kinding_regular E T K)
  /\ (forall E M Xs,
         valid_scheme_vars E M Xs -> valid_scheme_vars_regular E M Xs)
  /\ (forall E M, valid_scheme E M -> valid_scheme_regular E M)
  /\ (forall E, valid_env E -> valid_env_regular E)
  /\ (forall E T1 T2 K,
       type_equal_core E T1 T2 K -> type_equal_core_regular E T1 T2 K)
  /\ (forall E T1 T2 K,
       type_equal_symm E T1 T2 K -> type_equal_symm_regular E T1 T2 K)
  /\ (forall E T1 T2 K,
       type_equal_cong E T1 T2 K -> type_equal_cong_regular E T1 T2 K)
  /\ (forall E T1 T2 K,
       type_equal E T1 T2 K -> type_equal_regular E T1 T2 K)
  /\ (forall E T1 T2 cs,
       subtype E T1 T2 cs -> subtype_regular E T1 T2 cs).
Proof.
  apply combined_kinding_mutind; intros; subst;
    eauto with valid_kind_regular kinding_regular
      valid_scheme_vars_regular valid_scheme_regular
      valid_env_regular type_equal_core_regular
      type_equal_symm_regular type_equal_cong_regular
      type_equal_regular subtype_regular.
  - assert (environment E) by auto with valid_env_regular.
    assert (kind K) by (eapply kind_from_env; eassumption).
    auto with kinding_regular.
  - apply valid_scheme_regular_c with (L := L); try assumption.
    + pick_freshes_gen L (sch_arity M) Xs.
      assert (valid_scheme_vars_regular E M Xs) by auto.
      auto with valid_scheme_vars_regular.
    + exists L. intros.
      assert (valid_scheme_vars_regular E M Xs) by auto.
      auto with valid_scheme_vars_regular.
  - apply type_equal_core_regular_proj_compose;
      auto with kinding_regular csetdec.
  - assert (type (typ_meet T1 T2)) as Ht
      by auto with type_equal_regular.
    inversion Ht; subst.
    auto with subtype_regular type_equal_regular.
Qed.

Lemma unregular_combined_kinding :
  (forall E K, valid_kind_regular E K -> valid_kind E K)
  /\ (forall E T K, kinding_regular E T K -> kinding E T K)
  /\ (forall E M Xs,
         valid_scheme_vars_regular E M Xs -> valid_scheme_vars E M Xs)
  /\ (forall E M, valid_scheme_regular E M -> valid_scheme E M)
  /\ (forall E, valid_env_regular E -> valid_env E)
  /\ (forall E T1 T2 K,
       type_equal_core_regular E T1 T2 K -> type_equal_core E T1 T2 K)
  /\ (forall E T1 T2 K,
       type_equal_symm_regular E T1 T2 K -> type_equal_symm E T1 T2 K)
  /\ (forall E T1 T2 K,
       type_equal_cong_regular E T1 T2 K -> type_equal_cong E T1 T2 K)
  /\ (forall E T1 T2 K,
       type_equal_regular E T1 T2 K -> type_equal E T1 T2 K)
  /\ (forall E T1 T2 cs,
       subtype_regular E T1 T2 cs -> subtype E T1 T2 cs).
Proof.
  apply combined_kinding_regular_mutind; intros; subst; econstr auto.
Qed.

Lemma regular_valid_kind : forall E K,
    valid_kind E K -> valid_kind_regular E K.
Proof.
  pose regular_combined_kinding.
  tauto.
Qed.

Lemma unregular_valid_kind : forall T1 T2,
    valid_kind_regular T1 T2 -> valid_kind T1 T2.
Proof.
  pose unregular_combined_kinding.
  tauto.
Qed.

Hint Resolve unregular_valid_kind.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_kind E _ |- _ =>
      apply (proj1 (valid_kind_regular_inv
                      (regular_valid_kind H)))
  end : valid_kind_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : valid_kind _ K |- _ =>
      apply (proj2 (valid_kind_regular_inv
                      (regular_valid_kind H)))
  end : valid_kind_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : valid_kind _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj2 (valid_kind_regular_inv
                           (regular_valid_kind H)));
      inversion Hknd; assumption
  end : valid_kind_regular.

Lemma regular_kinding : forall E T K,
    kinding E T K -> kinding_regular E T K.
Proof.
  pose regular_combined_kinding.
  tauto.
Qed.

Lemma unregular_kinding : forall E T K,
    kinding_regular E T K -> kinding E T K.
Proof.
  pose unregular_combined_kinding.
  tauto.
Qed.

Hint Resolve unregular_kinding.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : kinding E _ _ |- _ =>
      apply (proj31 (kinding_regular_inv (regular_kinding H)))
  end : kinding_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : kinding _ T _ |- _ =>
      apply (proj32 (kinding_regular_inv (regular_kinding H)))
  end : kinding_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : kinding _ _ K |- _ =>
      apply (proj33 (kinding_regular_inv (regular_kinding H)))
  end : kinding_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : kinding _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj33 (kinding_regular_inv (regular_kinding H)));
      inversion Hknd; assumption
  end : kinding_regular.

Lemma regular_valid_scheme_vars : forall E M Xs,
    valid_scheme_vars E M Xs -> valid_scheme_vars_regular E M Xs.
Proof.
  pose regular_combined_kinding.
  tauto.
Qed.

Lemma unregular_valid_scheme_vars : forall E M Xs,
    valid_scheme_vars_regular E M Xs -> valid_scheme_vars E M Xs.
Proof.
  pose unregular_combined_kinding.
  tauto.
Qed.

Hint Resolve unregular_valid_scheme_vars.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_scheme_vars E _ _ |- _ =>
      apply (proj1 (valid_scheme_vars_regular_inv
                      (regular_valid_scheme_vars H)))
  end : valid_scheme_vars_regular.

Hint Extern 1 (scheme_vars ?M ?Xs) =>
  match goal with
  | H : valid_scheme_vars _ M Xs |- _ =>
      apply (proj2 (valid_scheme_vars_regular_inv
                      (regular_valid_scheme_vars H)))
  end : valid_scheme_vars_regular.

Lemma regular_valid_scheme : forall E M,
    valid_scheme E M -> valid_scheme_regular E M.
Proof.
  pose regular_combined_kinding.
  tauto.
Qed.

Lemma unregular_valid_scheme : forall E M,
    valid_scheme_regular E M -> valid_scheme E M.
Proof.
  pose unregular_combined_kinding.
  tauto.
Qed.

Hint Resolve unregular_valid_scheme.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_scheme E _ |- _ =>
      apply (proj1 (valid_scheme_regular_inv
                      (regular_valid_scheme H)))
  end : valid_scheme_regular.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H : valid_scheme _ M |- _ =>
      apply (proj2 (valid_scheme_regular_inv
                      (regular_valid_scheme H)))
  end : valid_scheme_regular.

Lemma regular_valid_env : forall E,
    valid_env E -> valid_env_regular E.
Proof.
  pose regular_combined_kinding.
  tauto.
Qed.

Lemma unregular_valid_env : forall E,
    valid_env_regular E -> valid_env E.
Proof.
  pose unregular_combined_kinding.
  tauto.
Qed.

Hint Resolve unregular_valid_env.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_env E |- _ =>
      apply (valid_env_regular_inv
               (regular_valid_env H))
  end : valid_env_regular.

Lemma regular_type_equal_core : forall E T1 T2 K,
    type_equal_core E T1 T2 K -> type_equal_core_regular E T1 T2 K.
Proof.
  pose regular_combined_kinding.
  tauto.
Qed.

Lemma unregular_type_equal_core : forall E T1 T2 K,
    type_equal_core_regular E T1 T2 K -> type_equal_core E T1 T2 K.
Proof.
  pose unregular_combined_kinding.
  tauto.
Qed.

Hint Resolve unregular_type_equal_core.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_core E _ _ _ |- _ =>
      apply (proj41 (type_equal_core_regular_inv
                       (regular_type_equal_core H)))
  end : type_equal_core_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_core _ T _ _ |- _ =>
      apply (proj42 (type_equal_core_regular_inv
                       (regular_type_equal_core H)))
  | H : type_equal_core _ _ T _ |- _ =>
      apply (proj43 (type_equal_core_regular_inv
                       (regular_type_equal_core H)))
  end : type_equal_core_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_core _ _ _ K |- _ =>
      apply (proj44 (type_equal_core_regular_inv
                       (regular_type_equal_core H)))
  end : type_equal_core_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_core _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_core_regular_inv
                            (regular_type_equal_core H)));
      inversion Hknd; assumption
  end : type_equal_core_regular.

Lemma regular_type_equal_symm : forall E T1 T2 K,
    type_equal_symm E T1 T2 K -> type_equal_symm_regular E T1 T2 K.
Proof.
  pose regular_combined_kinding.
  tauto.
Qed.

Lemma unregular_type_equal_symm : forall E T1 T2 K,
    type_equal_symm_regular E T1 T2 K -> type_equal_symm E T1 T2 K.
Proof.
  pose unregular_combined_kinding.
  tauto.
Qed.

Hint Resolve unregular_type_equal_symm.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_symm E _ _ _ |- _ =>
      apply (proj41 (type_equal_symm_regular_inv
                       (regular_type_equal_symm H)))
  end : type_equal_symm_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_symm _ T _ _ |- _ =>
      apply (proj42 (type_equal_symm_regular_inv
                       (regular_type_equal_symm H)))
  | H : type_equal_symm _ _ T _ |- _ =>
      apply (proj43 (type_equal_symm_regular_inv
                       (regular_type_equal_symm H)))
  end : type_equal_symm_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_symm _ _ _ K |- _ =>
      apply (proj44 (type_equal_symm_regular_inv
                       (regular_type_equal_symm H)))
  end : type_equal_symm_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_symm _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_symm_regular_inv
                            (regular_type_equal_symm H)));
      inversion Hknd; assumption
  end : type_equal_symm_regular.

Lemma regular_type_equal_cong : forall E T1 T2 K,
    type_equal_cong E T1 T2 K -> type_equal_cong_regular E T1 T2 K.
Proof.
  pose regular_combined_kinding.
  tauto.
Qed.

Lemma unregular_type_equal_cong : forall E T1 T2 K,
    type_equal_cong_regular E T1 T2 K -> type_equal_cong E T1 T2 K.
Proof.
  pose unregular_combined_kinding.
  tauto.
Qed.

Hint Resolve unregular_type_equal_cong.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal_cong E _ _ _ |- _ =>
      apply (proj41 (type_equal_cong_regular_inv
                       (regular_type_equal_cong H)))
  end : type_equal_cong_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_cong _ T _ _ |- _ =>
      apply (proj42 (type_equal_cong_regular_inv
                       (regular_type_equal_cong H)))
  | H : type_equal_cong _ _ T _ |- _ =>
      apply (proj43 (type_equal_cong_regular_inv
                       (regular_type_equal_cong H)))
  end : type_equal_cong_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_cong _ _ _ K |- _ =>
      apply (proj44 (type_equal_cong_regular_inv
                       (regular_type_equal_cong H)))
  end : type_equal_cong_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal_cong _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_cong_regular_inv
                            (regular_type_equal_cong H)));
      inversion Hknd; assumption
  end : type_equal_cong_regular.

Lemma regular_type_equal : forall E T1 T2 K,
    type_equal E T1 T2 K -> type_equal_regular E T1 T2 K.
Proof.
  pose regular_combined_kinding.
  tauto.
Qed.

Lemma unregular_type_equal : forall E T1 T2 K,
    type_equal_regular E T1 T2 K -> type_equal E T1 T2 K.
Proof.
  pose unregular_combined_kinding.
  tauto.
Qed.

Hint Resolve unregular_type_equal.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal E _ _ _ |- _ =>
      apply (proj41 (type_equal_regular_inv
                       (regular_type_equal H)))
  end : type_equal_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal _ T _ _ |- _ =>
      apply (proj42 (type_equal_regular_inv
                       (regular_type_equal H)))
  | H : type_equal _ _ T _ |- _ =>
      apply (proj43 (type_equal_regular_inv
                       (regular_type_equal H)))
  end : type_equal_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal _ _ _ K |- _ =>
      apply (proj44 (type_equal_regular_inv
                       (regular_type_equal H)))
  end : type_equal_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : type_equal _ _ _ (knd_row cs) |- _ =>
      let Hknd := fresh "Hknd" in
      assert (kind (knd_row cs)) as Hknd
        by apply (proj44 (type_equal_regular_inv
                            (regular_type_equal H)));
      inversion Hknd; assumption
  end : type_equal_regular.

Lemma regular_subtype : forall E T1 T2 K,
    subtype E T1 T2 K -> subtype_regular E T1 T2 K.
Proof.
  pose regular_combined_kinding.
  tauto.
Qed.

Lemma unregular_subtype : forall E T1 T2 K,
    subtype_regular E T1 T2 K -> subtype E T1 T2 K.
Proof.
  pose unregular_combined_kinding.
  tauto.
Qed.

Hint Resolve unregular_subtype.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : subtype E _ _ _ |- _ =>
      apply (proj41 (subtype_regular_inv
                       (regular_subtype H)))
  end : subtype_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : subtype _ T _ _ |- _ =>
      apply (proj42 (subtype_regular_inv
                       (regular_subtype H)))
  | H : subtype _ _ T _ |- _ =>
      apply (proj43 (subtype_regular_inv
                       (regular_subtype H)))
  end : subtype_regular.

Hint Extern 1 (CSet.Nonempty ?cs) =>
  match goal with
  | H : subtype _ _ _ cs |- _ =>
      apply (proj44 (subtype_regular_inv
                       (regular_subtype H)))
  end : subtype_regular.

Inductive valid_instance_regular : env -> list typ -> sch -> Prop :=
  | valid_instance_regular_empty : forall E T,
      kinding E T knd_type ->
      environment E ->
      type T ->
      types (sch_arity (sch_empty T)) nil ->
      valid_instance_regular E nil (sch_empty T)
  | valid_instance_regular_bind : forall E K M T Ts,
      kinding E T K ->
      valid_instance_regular E Ts (M ^^ T) ->
      environment E ->
      type T ->
      types (sch_arity M) Ts ->
      scheme (M ^^ T) ->
      kind K ->
      types (sch_arity (sch_bind K M)) (T :: Ts) ->
      valid_instance_regular E (T :: Ts) (sch_bind K M).

Lemma valid_instance_regular_inv : forall E Ts M,
    valid_instance_regular E Ts M ->
    environment E /\ types (sch_arity M) Ts /\ scheme M.
Proof.
  introv Hi.
  induction Hi; splits; auto.
  assert (scheme (M ^^ T)) as Hs by assumption.
  destruct Hs as [L Hs].
  pick_fresh_gen (L \u sch_fv M) Y.
  exists (L \u \{Y}).
  introv Hl.
  destruct Xs.
  + contradict Hl.
  + destruct Hl.
    apply scheme_vars_bind; auto.
    unfold sch_open_var.
    rewrite sch_subst_intro with (X := Y); auto.
    rewrite sch_subst_vars_type; autorewrite with rew_sch_arity; auto.
    autorewrite with rew_sch_arity in *.
    assert (scheme_vars (sch_open M T) Xs) as Hsv by auto.
    rewrite sch_subst_intro with (X := Y) in Hsv; auto.
    rewrite sch_subst_vars_type in Hsv;
      autorewrite with rew_sch_arity; auto.
Qed.

Hint Constructors valid_instance_regular : valid_instance_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_instance_regular E _ _ |- _ =>
      apply (proj31 (valid_instance_regular_inv H))
  end : valid_instance_regular.

Hint Extern 1 (types (sch_arity ?M) ?Ts) =>
  match goal with
  | H : valid_instance_regular _ Ts M |- _ =>
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
  induction Hi; auto with valid_instance_regular.
  - auto with valid_instance_regular kinding_regular.
  - assert (type T) by auto with kinding_regular.
    assert (types (sch_arity (sch_open M T)) Ts) as Hts
      by auto with valid_instance_regular.
    destruct Hts as [Hl Hts].
    apply valid_instance_regular_bind;
      auto with valid_instance_regular kinding_regular.
    + rewrite <- sch_open_arity with (U := T).
      auto with valid_instance_regular.
    + autorewrite with rew_sch_arity in Hl.
      split; simpl; auto.
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

Hint Extern 1 (types (sch_arity ?M) ?Ts) =>
  match goal with
  | H : valid_instance _ Ts M |- _ =>
      apply (proj32 (valid_instance_regular_inv
                       (regular_valid_instance H)))
  end : valid_instance_regular.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H : valid_instance_regular _ _ M |- _ =>
      apply (proj33 (valid_instance_regular_inv
                       (regular_valid_instance H)))
  end : valid_instance_regular.

Inductive valid_store_type_regular : env -> styp -> Prop :=
  | valid_store_type_regular_empty : forall E,
      valid_env E ->
      environment E ->
      valid_store_type_regular E empty
  | valid_store_type_regular_push : forall E P l T,
      valid_store_type_regular E P ->
      kinding E T knd_type ->
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
      types (sch_arity M) Us ->
      type T ->
      valid_env E ->
      valid_store_type E P ->
      binds x (bind_typ M) E -> 
      valid_instance E Us M ->
      type_equal E T (instance M Us) knd_type ->
      typing_regular E P (trm_fvar x) T
  | typing_regular_abs : forall L E P T1 T2 t1,
      kinding E T1 knd_type ->
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
  | typing_regular_let_val : forall M L E P T2 t1 t2,
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
      kinding E T1 (knd_range (typ_top CSet.universe) T2) ->
      subtype E
        (typ_constructor c T3)
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (CSet.singleton c) ->
      typing_regular E P t T3 ->
      typing_regular E P (trm_constructor c t) (typ_variant T1)
  | typing_regular_match : forall c L E P T1 T2 T3 T4 T5
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
      kinding E T1 (knd_range T2 (typ_bot CSet.universe)) ->
      kinding E T3 (knd_range (typ_top CSet.universe) T4) ->
      kinding E T5 (knd_range (typ_top CSet.universe) T6) ->
      subtype E
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (typ_constructor c T7)
        (CSet.singleton c) ->
      subtype E
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (typ_proj CSet.universe T4 (CSet.singleton c))
        (CSet.singleton c) ->
      subtype E
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
  | typing_regular_destruct : forall c L E P T1 T2 T3 T4 t1 t2,
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
      kinding E T1 (knd_range T2 (typ_bot CSet.universe)) ->
      subtype E
        (typ_proj CSet.universe T2 (CSet.singleton c))
        (typ_constructor c T3)
        (CSet.singleton c) ->
      subtype E
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
      kinding E T1 (knd_range (typ_bot CSet.universe)
                              (typ_bot CSet.universe)) ->
      kinding E T2 knd_type ->
      typing_regular E P t1 (typ_variant T1) ->
      typing_regular E P (trm_absurd t1) T2
  | typing_regular_unit : forall E P,
      environment E ->
      store_type P ->
      valid_env E ->
      valid_store_type E P ->
      typing_regular E P trm_unit typ_unit
  | typing_regular_loc : forall E P l T1 T2,
      environment E ->
      store_type P ->
      type T1 ->
      type T2 ->
      valid_env E ->
      valid_store_type E P ->
      binds l T1 P ->
      type_equal E T1 T2 knd_type ->
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
    assert (types (sch_arity M) Us)
      by auto with valid_instance_regular.   
    assert (type T)
      as Ht by auto with type_equal_regular.
    eauto with typing_regular.
  - pick_fresh_gen L x.
    assert (typing_regular (E & x ~: sch_empty T1) P (t1 ^ x) T2)
      by auto.
    apply typing_regular_abs with (L := L); auto with typing_regular.
    + eauto using environment_retract with typing_regular.
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
    + eauto using environment_retract with typing_regular.
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
  - apply typing_regular_unit;
      auto with valid_store_type_regular.
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
      value t ->
      value_regular (trm_constructor c t)
  | value_regular_abs : forall t,
      term_body t ->
      value_regular (trm_abs t)
  | value_regular_unit :
      value_regular trm_unit
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
  assert (term (trm_abs t)) as Ht by assumption.
  inversion Ht; subst.
  apply value_regular_abs; try assumption.
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
