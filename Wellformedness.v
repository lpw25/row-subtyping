(************************************************
 *          Row Subtyping - Well-formedness     *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import List LibLN Cofinite Definitions Substitution.

(* *************************************************************** *)
(** ** Automation *)

Hint Constructors kind type scheme_vars term environment.

Hint Unfold is_row_kind.

Hint Extern 1 (types _ _) => split; auto.

Hint Extern 1 (CSet.Equal _ _) => csetdec.
Hint Extern 1 (CSet.Subset _ _) => csetdec.
Hint Extern 1 (CSet.Empty _) => csetdec.
Hint Extern 1 (CSet.Nonempty _) => csetdec.
Hint Extern 1 (CSet.Universe _) => csetdec.
Hint Extern 1 (CSet.Nonuniverse _) => csetdec.
Hint Extern 1 (CSet.Disjoint _ _) => csetdec.

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
  type U -> type T -> type (typ_subst Z U T).
Proof.
  induction 2; simpls*. case_var*.
Qed.

(** Types are stable by iterated type substitution *)

Lemma typ_substs_types : forall Xs Us T,
  types (length Xs) Us ->
  type T ->
  type (typ_substs Xs Us T).
Proof.
  induction Xs; destruct Us; simpl; introv TU TT; auto.
  destruct TU. simpls. inversions H. inversions* H0.
  auto using typ_subst_type.
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
  split; auto using typ_subst_type.
Qed.

(* =============================================================== *)
(** * Properties of kinds *)

(** Kinds are stable by type substitution *)

Lemma knd_subst_kind : forall K Z U,
  type U -> kind K -> kind (knd_subst Z U K).
Proof.
  introv Ht Hk.
  induction Hk; simpl; auto using typ_subst_type.
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
  scheme_vars M Xs -> scheme_vars (sch_subst Z U M) Xs.
Proof.
  introv Hf Ht Hs.
  induction Hs; simpl; auto using typ_subst_type.
  destruct Hf.
  autorewrite with rew_sch_arity in *.
  apply scheme_bind; auto using knd_subst_kind.
  rewrite sch_subst_open_var; auto.
Qed.

Lemma sch_subst_type : forall M Z U,
    type U -> scheme M -> scheme (sch_subst Z U M).
Proof.
  introv Ht [L Hs].
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

Lemma env_subst_environment : forall X U E,
    type U ->
    environment E -> environment (env_subst X U E).
Proof.
  introv Ht He.
  induction He; autorewrite with rew_env_subst; auto.
  - apply environment_knd;
      auto using knd_subst_kind, env_subst_notin.
  - apply environment_typ;
      auto using sch_subst_type, env_subst_notin.
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

Lemma kind_from_env : forall E x K,
    environment E ->
    binds x (bind_knd K) E ->
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
(** * Regularity of judgments *)

Inductive type_equal_cong_regular : typ -> typ -> Prop :=
  | type_equal_cong_regular_core : forall T1 T1',
      type T1 ->
      type T1' ->
      type_equal_core T1 T1' ->
      type_equal_cong_regular T1 T1'
  | type_equal_cong_regular_constructor : forall c T1 T1',
      type T1 ->
      type T1' ->
      type_equal_cong_regular T1 T1' ->
      type_equal_cong_regular
        (typ_constructor c T1) (typ_constructor c T1')
  | type_equal_cong_regular_or_l : forall T1 T1' T2,
      type T1 ->
      type T1' ->
      type T2 ->
      type_equal_cong_regular T1 T1' ->
      type_equal_cong_regular (typ_or T1 T2) (typ_or T1' T2)
  | type_equal_cong_regular_or_r : forall T1 T2 T2',
      type T1 ->
      type T2 ->
      type T2' ->
      type_equal_cong_regular T2 T2' ->
      type_equal_cong_regular (typ_or T1 T2) (typ_or T1 T2')
  | type_equal_cong_regular_row : forall T1 T1',
      type T1 ->
      type T1' ->
      type_equal_cong_regular T1 T1' ->
      type_equal_cong_regular (typ_row T1) (typ_row T1')
  | type_equal_cong_regular_variant : forall T1 T1',
      type T1 ->
      type T1' ->
      type_equal_cong_regular T1 T1' ->
      type_equal_cong_regular (typ_variant T1) (typ_variant T1')
  | type_equal_cong_regular_arrow_l : forall T1 T1' T2,
      type T1 ->
      type T1' ->
      type T2 ->
      type_equal_cong_regular T1 T1' ->
      type_equal_cong_regular (typ_arrow T1 T2) (typ_arrow T1' T2)
  | type_equal_cong_regular_arrow_r : forall T1 T2 T2',
      type T1 ->
      type T2 ->
      type T2' ->
      type_equal_cong_regular T2 T2' ->
      type_equal_cong_regular (typ_arrow T1 T2) (typ_arrow T1 T2')
  | type_equal_cong_regular_meet_l : forall T1 T1' T2,
      type T1 ->
      type T1' ->
      type T2 ->
      type_equal_cong_regular T1 T1' ->
      type_equal_cong_regular (typ_meet T1 T2) (typ_meet T1' T2)
  | type_equal_cong_regular_meet_r : forall T1 T2 T2',
      type T1 ->
      type T2 ->
      type T2' ->
      type_equal_cong_regular T2 T2' -> 
      type_equal_cong_regular (typ_meet T1 T2) (typ_meet T1 T2')
  | type_equal_cong_regular_join_l : forall T1 T1' T2,
      type T1 ->
      type T1' ->
      type T2 ->
      type_equal_cong_regular T1 T1' ->
      type_equal_cong_regular (typ_join T1 T2) (typ_join T1' T2)
  | type_equal_cong_regular_join_r : forall T1 T2 T2',
      type T1 ->
      type T2 ->
      type T2' ->
      type_equal_cong_regular T2 T2' ->
      type_equal_cong_regular (typ_join T1 T2) (typ_join T1 T2').

Lemma type_equal_cong_regular_wellformed : forall T1 T2,
    type_equal_cong_regular T1 T2 ->
    type T1 /\ type T2.
Proof.
  introv Hte.
  destruct Hte; auto.
Qed.

Hint Constructors type_equal_cong_regular : type_equal_cong_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_cong_regular T _ |- _ =>
      apply (proj1 (type_equal_cong_regular_wellformed H))
  | H : type_equal_cong_regular _ T |- _ =>
      apply (proj2 (type_equal_cong_regular_wellformed H))
  end : type_equal_cong_regular.

Lemma regular_type_equal_cong : forall T1 T2,
    type T1 -> type T2 ->
    type_equal_cong T1 T2 -> type_equal_cong_regular T1 T2.
Proof.
  introv Ht1 Ht2 Hte.
  induction Hte;
    inversion Ht1; inversion Ht2; subst;
      auto with type_equal_cong_regular.
Qed.

Lemma regular_type_equal_cong_inv : forall T1 T2,
    type_equal_cong_regular T1 T2 -> type_equal_cong T1 T2.
Proof.
  introv Hte.
  induction Hte; auto using type_equal_cong.
Qed.

Inductive type_equal_symm_regular : typ -> typ -> Prop :=
  | type_equal_symm_regular_l : forall T1 T2,
      type T1 ->
      type T2 ->
      type_equal_cong_regular T1 T2 ->
      type_equal_symm_regular T2 T1
  | type_equal_symm_regular_r : forall T1 T2,
      type T1 ->
      type T2 ->
      type_equal_cong_regular T2 T1 ->
      type_equal_symm_regular T2 T1.

Lemma type_equal_symm_regular_wellformed : forall T1 T2,
    type_equal_symm_regular T1 T2 ->
    type T1 /\ type T2.
Proof.
  introv Hte.
  destruct Hte; auto.
Qed.

Lemma regular_type_equal_symm : forall T1 T2,
    type T1 -> type T2 ->
    type_equal_symm T1 T2 -> type_equal_symm_regular T1 T2.
Proof.
  introv Ht1 Ht2 Hte.
  induction Hte;
      auto using regular_type_equal_cong, type_equal_symm_regular.
Qed.

Lemma regular_type_equal_symm_inv : forall T1 T2,
    type_equal_symm_regular T1 T2 -> type_equal_symm T1 T2.
Proof.
  introv Hte.
  induction Hte;
    auto using regular_type_equal_cong_inv, type_equal_symm.
Qed.

Inductive kinding_regular : env -> typ -> knd -> Prop :=
  | kinding_regular_var : forall E X K,
      environment E ->
      kind K ->
      binds X (bind_knd K) E ->
      kinding_regular E (typ_fvar X) K
  | kinding_regular_constructor : forall E c T K,
      environment E ->
      type T ->
      kind K ->
      kinding_regular E T knd_type ->
      K = knd_row (CSet.singleton c) ->
      kinding_regular E (typ_constructor c T) K
  | kinding_regular_or : forall E T1 cs1 T2 cs2 K,
      environment E ->
      type T1 ->
      type T2 ->
      kind (knd_row cs1) ->
      kind (knd_row cs2) ->
      kind K ->
      kinding_regular E T1 (knd_row cs1) ->
      kinding_regular E T2 (knd_row cs2) ->
      CSet.Disjoint cs1 cs2 ->
      K = knd_row (CSet.union cs1 cs2) ->
      kinding_regular E (typ_or T1 T2) K
  | kinding_regular_row : forall E T K,
      environment E ->
      type T ->
      kind K ->
      kinding_regular E T (knd_row CSet.universe) ->
      K = knd_range T T ->
      kinding_regular E (typ_row T) K
  | kinding_regular_variant : forall E T T1 T2 K,
      environment E ->
      type T ->
      type T1 ->
      type T2 ->
      kind K ->
      kinding_regular E T (knd_range T1 T2) ->
      K = knd_type ->
      kinding_regular E (typ_variant T) K
  | kinding_regular_arrow : forall E T1 T2 K,
      environment E ->
      type T1 ->
      type T2 ->
      kind K ->
      kinding_regular E T1 knd_type -> 
      kinding_regular E T2 knd_type -> 
      K = knd_type ->
      kinding_regular E (typ_arrow T1 T2) K
  | kinding_regular_top : forall E cs K,
      environment E ->
      kind K ->
      CSet.Nonempty cs ->
      environment E ->
      K = knd_row cs ->
      kinding_regular E (typ_top cs) K
  | kinding_regular_bot : forall E cs K,
      environment E ->
      kind K ->
      CSet.Nonempty cs ->
      environment E ->
      K = knd_row cs ->
      kinding_regular E (typ_bot cs) K
  | kinding_regular_meet : forall E T1 T2 K,
      environment E ->
      type T1 ->
      type T2 ->
      kind K ->
      kinding_regular E T1 K ->
      kinding_regular E T2 K ->
      is_row_kind K ->
      kinding_regular E (typ_meet T1 T2) K
  | kinding_regular_join : forall E T1 T2 K,
      environment E ->
      type T1 ->
      type T2 ->
      kind K ->
      kinding_regular E T1 K ->
      kinding_regular E T2 K ->
      is_row_kind K ->
      kinding_regular E (typ_join T1 T2) K
  | kinding_regular_subsumption : forall E T T1 T2 T1' T2' K,
      environment E ->
      type T1 ->
      type T2 ->
      type T1' ->
      type T2' ->
      type T ->
      kind K ->
      kinding_regular E T (knd_range T1 T2) ->
      subtype E T1 T1' ->
      subtype E T2' T2 ->
      K = knd_range T1' T2' ->
      kinding_regular E T K.

Inductive type_equal_regular : env -> typ -> typ -> knd -> Prop :=
  | type_equal_regular_refl : forall E T K,
      environment E ->
      type T ->
      kind K ->
      kinding E T K ->
      type_equal_regular E T T K
  | type_equal_regular_step : forall E T1 T2 T3 K,
      environment E ->
      type T1 ->
      type T2 ->
      type T3 ->
      kind K ->
      kinding E T1 K ->
      type_equal_symm_regular T1 T2 ->
      type_equal_regular E T2 T3 K ->
      type_equal_regular E T1 T3 K.

Lemma kinding_regular_wellformed : forall E T K,
    kinding_regular E T K ->
    environment E /\ type T /\ kind K.
Proof.
  introv Hk.
  destruct Hk; auto.
Qed.

Hint Constructors kinding_regular : kinding_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : kinding_regular E _ _ |- _ =>
      apply (proj31 (kinding_regular_wellformed H))
  end : kinding_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : kinding_regular _ T _ |- _ =>
      apply (proj32 (kinding_regular_wellformed H))
  end : kinding_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : kinding_regular _ _ K |- _ =>
      apply (proj33 (kinding_regular_wellformed H))
  end : kinding_regular.

Lemma type_equal_regular_wellformed : forall E T1 T2 K,
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
      apply (proj41 (type_equal_regular_wellformed H))
  end : type_equal_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal_regular _ T _ _ |- _ =>
      apply (proj42 (type_equal_regular_wellformed H))
  | H : type_equal_regular _ _ T _ |- _ =>
      apply (proj43 (type_equal_regular_wellformed H))
  end : type_equal_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal_regular _ _ _ K |- _ =>
      apply (proj44 (type_equal_regular_wellformed H))
  end : type_equal_regular.

Lemma regular_kinding_type_equal :
  (forall E T K, kinding E T K -> kinding_regular E T K)
  /\ (forall E T1 T2 K,
       type_equal E T1 T2 K ->type_equal_regular E T1 T2 K).
Proof.
  apply kinding_type_equal_mutind;
    intros; subst; auto with kinding_regular type_equal_regular.
  - assert (kind K) by (eapply kind_from_env; eassumption).
    auto with kinding_regular.
  - assert (kind (knd_row cs1)) as Hk
        by auto with kinding_regular.
    inversion Hk; subst.
    apply kinding_regular_or with (cs1 := cs1) (cs2 := cs2);
      auto with kinding_regular.
  - assert (kind (knd_range T1 T2)) as Hk
      by auto with kinding_regular.
    inversion Hk.
    apply kinding_regular_variant with (T1 := T1) (T2 := T2);
      auto with kinding_regular.
  - assert (type (typ_meet T1 T1')) as Ht1
        by auto with type_equal_regular.
    inversion Ht1; subst.
    assert (type (typ_meet T2' T2)) as Ht2
        by auto with type_equal_regular.
    inversion Ht2; subst.
    apply kinding_regular_subsumption
      with (T1 := T1) (T2 := T2) (T1' := T1') (T2' := T2');
      unfold subtype; auto with kinding_regular.
  - apply type_equal_regular_step with (T2 := T2);
      auto using regular_type_equal_symm
        with kinding_regular type_equal_regular.
Qed.

Lemma regular_kinding : forall E T K,
    kinding E T K -> kinding_regular E T K.
Proof.
  destruct regular_kinding_type_equal.
  assumption.
Qed.

Lemma regular_kinding_inv : forall E T K,
    kinding_regular E T K -> kinding E T K.
Proof.
  introv Hk.
  induction Hk; eauto using kinding.
Qed.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : kinding E _ _ |- _ =>
      apply (proj31 (kinding_regular_wellformed (regular_kinding H)))
  end : kinding_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : kinding _ T _ |- _ =>
      apply (proj32 (kinding_regular_wellformed (regular_kinding H)))
  end : kinding_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : kinding _ _ K |- _ =>
      apply (proj33 (kinding_regular_wellformed (regular_kinding H)))
  end : kinding_regular.

Lemma regular_type_equal : forall E T1 T2 K,
    type_equal E T1 T2 K -> type_equal_regular E T1 T2 K.
Proof.
  destruct regular_kinding_type_equal.
  assumption.
Qed.

Lemma regular_type_equal_inv : forall E T1 T2 K,
    type_equal_regular E T1 T2 K -> type_equal E T1 T2 K.
Proof.
  introv Hte.
  induction Hte;
    eauto using type_equal, regular_type_equal_symm_inv.
Qed.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : type_equal E _ _ _ |- _ =>
      apply (proj41 (type_equal_regular_wellformed
                       (regular_type_equal H)))
  end : type_equal_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal _ T _ _ |- _ =>
      apply (proj42 (type_equal_regular_wellformed
                       (regular_type_equal H)))
  | H : type_equal _ _ T _ |- _ =>
      apply (proj43 (type_equal_regular_wellformed
                       (regular_type_equal H)))
  end : type_equal_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal _ _ _ K |- _ =>
      apply (proj44 (type_equal_regular_wellformed
                       (regular_type_equal H)))
  end : type_equal_regular.

Inductive valid_kind_regular : env -> knd -> Prop :=
  | valid_kind_regular_type : forall E,
      environment E ->
      valid_kind_regular E knd_type
  | valid_kind_regular_row :  forall E cs,
      environment E ->
      kind (knd_row cs) ->
      CSet.Nonempty cs ->
      valid_kind_regular E (knd_row cs)
  | valid_kind_regular_range : forall E T1 T2,
      environment E ->
      type T1 ->
      type T2 ->
      subtype E T2 T1 ->
      valid_kind_regular E (knd_range T1 T2).

Lemma valid_kind_regular_wellformed : forall E K,
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
      apply (proj1 (valid_kind_regular_wellformed H))
  end : valid_kind_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : valid_kind_regular _ K |- _ =>
      apply (proj2 (valid_kind_regular_wellformed H))
  end : valid_kind_regular.

Lemma regular_valid_kind : forall E K,
    valid_kind E K -> valid_kind_regular E K.
Proof.
  introv Hv.
  induction Hv; unfold subtype in *; auto using valid_kind_regular.
  - assert (type (typ_meet T2 T1)) as Ht
        by auto with type_equal_regular.
    inversion Ht.
    auto using valid_kind_regular with type_equal_regular.
Qed.

Lemma regular_valid_kind_inv : forall T1 T2,
    valid_kind_regular T1 T2 -> valid_kind T1 T2.
Proof.
  introv Hv.
  induction Hv;
    auto using valid_kind.
Qed.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : valid_kind E _ |- _ =>
      apply (proj1 (valid_kind_regular_wellformed
                      (regular_valid_kind H)))
  end : valid_kind_regular.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : valid_kind _ K |- _ =>
      apply (proj2 (valid_kind_regular_wellformed
                      (regular_valid_kind H)))
  end : valid_kind_regular.

Inductive kinding_scheme_vars_regular
  : env -> sch -> list var -> Prop :=
  | kinding_scheme_vars_regular_empty : forall E T,
      environment E ->
      type T ->
      scheme_vars (sch_empty T) nil ->
      kinding E T knd_type ->
      kinding_scheme_vars_regular E (sch_empty T) nil
  | kinding_scheme_vars_regular_bind : forall X Xs E K M,
      environment E ->
      environment (E & X ~:: K) ->
      kind K ->
      scheme_vars (M ^ X) Xs ->
      scheme_vars (sch_bind K M) (X :: Xs) ->
      valid_kind E K ->
      kinding_scheme_vars_regular (E & X ~:: K) (M ^ X) Xs ->
      kinding_scheme_vars_regular E (sch_bind K M) (X :: Xs).

Lemma kinding_scheme_vars_regular_wellformed : forall E M Xs,
    kinding_scheme_vars_regular E M Xs ->
    environment E /\ scheme_vars M Xs.
Proof.
  introv Hs.
  destruct Hs; auto.
Qed.

Hint Constructors kinding_scheme_vars_regular
  : kinding_scheme_vars_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : kinding_scheme_vars_regular E _ _ |- _ =>
      apply (proj1 (kinding_scheme_vars_regular_wellformed H))
  end : kinding_scheme_vars_regular.

Hint Extern 1 (scheme_vars ?M ?Xs) =>
  match goal with
  | H : kinding_scheme_vars_regular _ M Xs |- _ =>
      apply (proj2 (kinding_scheme_vars_regular_wellformed H))
  end : kinding_scheme_vars_regular.

Lemma regular_kinding_scheme_vars : forall E M Xs,
    kinding_scheme_vars E M Xs -> kinding_scheme_vars_regular E M Xs.
Proof.
  introv Hs.
  induction Hs.
  - auto with kinding_regular kinding_scheme_vars_regular.
  - apply kinding_scheme_vars_regular_bind;
      auto with kinding_scheme_vars_regular valid_kind_regular.
Qed.

Lemma regular_kinding_scheme_vars_inv : forall E M Xs,
    kinding_scheme_vars_regular E M Xs -> kinding_scheme_vars E M Xs.
Proof.
  introv Hs.
  induction Hs;
    auto using kinding_scheme_vars.
Qed.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : kinding_scheme_vars E _ _ |- _ =>
      apply (proj1 (kinding_scheme_vars_regular_wellformed
                      (regular_kinding_scheme_vars H)))
  end : kinding_scheme_vars_regular.

Hint Extern 1 (scheme_vars ?M ?Xs) =>
  match goal with
  | H : kinding_scheme_vars _ M Xs |- _ =>
      apply (proj2 (kinding_scheme_vars_regular_wellformed
                      (regular_kinding_scheme_vars H)))
  end : kinding_scheme_vars_regular.

Definition kinding_scheme_regular E M :=
  (exists L, forall Xs,
      fresh L (sch_arity M) Xs ->
      kinding_scheme_vars_regular E M Xs)
  /\ environment E /\ scheme M.

Lemma kinding_scheme_regular_wellformed : forall E M,
    kinding_scheme_regular E M ->
    environment E /\ scheme M.
Proof.
  introv [_ [He Hs]].
  split; assumption.
Qed.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : kinding_scheme_regular E _ |- _ =>
      apply (proj1 (kinding_scheme_regular_wellformed H))
  end : kinding_scheme_regular.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H : kinding_scheme_regular _ M |- _ =>
      apply (proj2 (kinding_scheme_regular_wellformed H))
  end : kinding_scheme_regular.

Lemma regular_kinding_scheme : forall E M,
    kinding_scheme E M -> kinding_scheme_regular E M.
Proof.
  introv [L Hs].
  splits.
  - exists L; intros Xs Fr.
    specialize (Hs Xs Fr).
    apply regular_kinding_scheme_vars.
    assumption.
  - pick_freshes_gen L (sch_arity M) Xs.
    specialize (Hs Xs Fr).
    apply regular_kinding_scheme_vars in Hs.
    auto with kinding_scheme_vars_regular.
  - exists L; intros Xs Fr.
    specialize (Hs Xs Fr).
    apply regular_kinding_scheme_vars in Hs.
    auto with kinding_scheme_vars_regular.
Qed.

Lemma regular_kinding_scheme_inv : forall E M,
    kinding_scheme_regular E M -> kinding_scheme E M.
Proof.
  introv [[L Hs] _].
  exists L; intros Xs Fr.
  specialize (Hs Xs Fr).
  apply regular_kinding_scheme_vars_inv.
  assumption.
Qed.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : kinding_scheme E _ |- _ =>
      apply (proj1 (kinding_scheme_regular_wellformed
                      (regular_kinding_scheme H)))
  end : kinding_scheme_regular.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H : kinding_scheme _ M |- _ =>
      apply (proj2 (kinding_scheme_regular_wellformed
                      (regular_kinding_scheme H)))
  end : kinding_scheme_regular.

Inductive kinding_instance_regular : env -> list typ -> sch -> Prop :=
  | kinding_instance_regular_empty : forall E T,
      types (sch_arity (sch_empty T)) nil ->
      kinding_instance_regular E nil (sch_empty T)
  | kinding_instance_regular_bind : forall E K M T Ts,
      types (sch_arity M) Ts ->
      types (sch_arity (sch_bind K M)) (T :: Ts) ->
      kinding E T K ->
      kinding_instance_regular E Ts (M ^^ T) ->
      kinding_instance_regular E (T :: Ts) (sch_bind K M).

Lemma kinding_instance_regular_wellformed : forall E Ts M,
    kinding_instance_regular E Ts M -> types (sch_arity M) Ts.
Proof.
  introv Hi.
  destruct Hi; auto.
Qed.

Hint Constructors kinding_instance_regular : kinding_instance_regular.

Hint Extern 1 (types (sch_arity ?M) ?Ts) =>
  match goal with
  | H : kinding_instance_regular _ Ts M |- _ =>
      apply (kinding_instance_regular_wellformed H)
  end : kinding_instance_regular.

Lemma regular_kinding_instance : forall E Ts M,
    kinding_instance E Ts M -> kinding_instance_regular E Ts M.
Proof.
  introv Hi.
  induction Hi; auto with kinding_instance_regular.
  - assert (type T) by auto with kinding_regular.
    assert (types (sch_arity (sch_open M T)) Ts) as Hts
      by auto with kinding_instance_regular.
    destruct Hts as [Hl Hts].
    apply kinding_instance_regular_bind; auto.
    + rewrite <- sch_open_arity with (U := T).
      auto with kinding_instance_regular.
    + autorewrite with rew_sch_arity in Hl.
      split; simpl; auto.
Qed.

Lemma regular_kinding_instance_inv : forall E Ts M,
    kinding_instance_regular E Ts M -> kinding_instance E Ts M.
Proof.
  introv Hi.
  induction Hi; auto using kinding_instance.
Qed.

Hint Extern 1 (types (sch_arity ?M) ?Ts) =>
  match goal with
  | H : kinding_instance _ Ts M |- _ =>
      apply (kinding_instance_regular_wellformed
               (regular_kinding_instance H))
  end : kinding_instance_regular.

Inductive kinding_env_regular : env -> Prop :=
  | kinding_env_regular_empty :
      kinding_env_regular empty
  | kinding_env_regular_kind : forall E X K,
      environment E ->
      environment (E & X ~:: K) ->
      kind K ->
      kinding_env_regular E ->
      valid_kind E K ->
      X # E ->
      kinding_env_regular (E & X ~:: K)
  | kinding_env_regular_type : forall E x M,
      environment E ->
      environment (E & x ~: M) ->
      scheme M ->
      kinding_env_regular E ->
      kinding_scheme E M ->
      x # E ->
      kinding_env_regular (E & x ~: M).

Lemma kinding_env_regular_wellformed : forall E,
    kinding_env_regular E -> environment E.
Proof.
  introv He.
  destruct He; auto.
Qed.

Hint Constructors kinding_env_regular : kinding_env_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : kinding_env_regular E |- _ =>
      apply (kinding_env_regular_wellformed H)
  end : kinding_env_regular.

Lemma regular_kinding_env : forall E,
    kinding_env E -> kinding_env_regular E.
Proof.
  introv He.
  induction He; auto with kinding_env_regular.
  - auto with kinding_env_regular valid_kind_regular.
  - auto with kinding_env_regular kinding_scheme_regular.
Qed.

Lemma regular_kinding_env_inv : forall E,
    kinding_env_regular E -> kinding_env E.
Proof.
  introv He.
  induction He; auto using kinding_env.
Qed.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : kinding_env E |- _ =>
      apply (kinding_env_regular_wellformed
               (regular_kinding_env H))
  end : kinding_env_regular.

Inductive typing_regular : env -> trm -> typ -> Prop :=
  | typing_regular_var : forall E x M Us,
      environment E ->
      scheme M ->
      types (sch_arity M) Us ->
      type (instance M Us) ->
      kinding_env E -> 
      binds x (bind_typ M) E -> 
      kinding_instance E Us M ->
      typing_regular E (trm_fvar x) (instance M Us)
  | typing_regular_abs : forall L E T1 T2 t1,
      environment E ->
      (forall x, x \notin L ->
         environment (E & x ~ bind_typ (sch_empty T1))) ->
      type T1 ->
      type T2 ->
      term_body t1 ->
      (forall x, x \notin L -> 
        typing_regular
          (E & x ~ bind_typ (sch_empty T1)) (t1 ^ x) T2) -> 
      typing_regular E (trm_abs t1) (typ_arrow T1 T2)
  | typing_regular_app : forall E S T t1 t2, 
      environment E ->
      type S ->
      type T ->
      term t1 ->
      term t2 ->
      typing_regular E t1 (typ_arrow S T) ->
      typing_regular E t2 S ->   
      typing_regular E (trm_app t1 t2) T
  | typing_regular_let : forall M L E T2 t1 t2,
      environment E ->
      (forall Xs, fresh L (sch_arity M) Xs ->
         environment (E & Xs ~::* M)) ->
      (forall x, x \notin L ->
         environment (E & x ~ (bind_typ M))) -> 
      type T2 ->
      (forall Xs, fresh L (sch_arity M) Xs ->
         type (instance_vars M Xs)) ->
      scheme M ->
      term t1 ->
      term_body t2 ->
      (forall Xs, fresh L (sch_arity M) Xs ->
         typing_regular
           (E & Xs ~::* M)
           t1 (instance_vars M Xs)) ->
      (forall x, x \notin L ->
         typing_regular (E & x ~ (bind_typ M)) (t2 ^ x) T2) -> 
      typing_regular E (trm_let t1 t2) T2
  | typing_regular_constructor : forall c E T1 T2 t,
      environment E ->
      type T1 ->
      type T2 ->
      term t ->
      kinding E T1
        (knd_range (typ_top CSet.universe)
                   (typ_or (typ_constructor c T2)
                           (typ_bot (CSet.cosingleton c)))) ->
      typing_regular E t T2 ->
      typing_regular E (trm_constructor c t) (typ_variant T1)
  | typing_regular_match : forall c L E T1 T2 T3 T4 T5
                          T6 T7 t1 t2 t3,
      environment E ->
      (forall x, x \notin L ->
         environment (E & x ~: (sch_empty (typ_variant T5)))) ->
      (forall y, y \notin L -> 
         environment (E & y ~: (sch_empty (typ_variant T6)))) ->
      type T1 ->
      type T2 ->
      type T3 ->
      type T4 ->
      type T5 ->
      type T6 ->
      type T7 ->
      term t1 ->
      term_body t2 ->
      term_body t3 ->
      kinding E T1
        (knd_range (typ_or (typ_constructor c T2)
                           (typ_top (CSet.cosingleton c)))
                   (typ_bot CSet.universe)) ->
      kinding E T1 (knd_range (typ_or T3 T4)
                              (typ_bot CSet.universe)) ->
      kinding E T5
              (knd_range (typ_top CSet.universe)
                         (typ_or T3
                                 (typ_bot (CSet.cosingleton c)))) ->
      kinding E T6
              (knd_range (typ_top CSet.universe)
                         (typ_or (typ_bot (CSet.singleton c))
                                 T4)) ->
      typing_regular E t1 (typ_variant T1) ->
      (forall x, x \notin L ->
         typing_regular (E & x ~: (sch_empty (typ_variant T5)))
                (t2 ^ x) T7) ->
      (forall y, y \notin L -> 
         typing_regular (E & y ~: (sch_empty (typ_variant T6)))
                (t3 ^ y) T7) ->
      typing_regular E (trm_match t1 c t2 t3) T7
  | typing_regular_destruct : forall c L E T1 T2 T3 t1 t2,
      environment E ->
      (forall x, x \notin L ->
         environment (E & x ~: (sch_empty T2))) ->
      type T1 ->
      type T2 ->
      type T3 ->
      term t1 ->
      term_body t2 ->
      kinding E T1
        (knd_range (typ_or (typ_constructor c T2)
                           (typ_bot (CSet.cosingleton c)))
                   (typ_bot CSet.universe)) ->
      typing_regular E t1 (typ_variant T1) ->
      (forall x, x \notin L ->
         typing_regular (E & x ~: (sch_empty T2))
                (t2 ^ x) T3) ->
      typing_regular E (trm_destruct t1 c t2) T3
  | typing_regular_absurd : forall E T1 T2 t1,
      environment E ->
      type T1 ->
      type T2 ->
      term t1 ->
      kinding E T1 (knd_range (typ_bot CSet.universe)
                              (typ_bot CSet.universe)) ->
      kinding E T2 knd_type ->
      typing_regular E t1 (typ_variant T1) ->
      typing_regular E (trm_absurd t1) T2.

Lemma typing_regular_wellformed : forall E t T,
    typing_regular E t T ->
      environment E /\ term t /\ type T.
Proof.
  introv Ht.
  induction Ht; auto.
Qed.

Hint Constructors typing_regular : typing_regular.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : typing_regular E _ _ |- _ =>
      apply (proj31 (typing_regular_wellformed H))
  end : typing_regular.

Hint Extern 1 (term ?t) =>
  match goal with
  | H : typing_regular _ t _ |- _ =>
      apply (proj32 (typing_regular_wellformed H))
  end : typing_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : typing_regular _ _ T |- _ =>
      apply (proj33 (typing_regular_wellformed H))
  end : typing_regular.

Lemma regular_typing : forall E t T,
    typing E t T -> typing_regular E t T.
Proof.
  introv Ht.
  induction Ht.
  - assert (environment E)
      by auto with kinding_env_regular.
    assert (scheme M)
      by (eapply scheme_from_env; eassumption).
    assert (types (sch_arity M) Us)
      by auto with kinding_instance_regular.   
    assert (type (instance M Us))
      by auto using scheme_instance_type.
    auto with typing_regular.
  - pick_fresh_gen L x.
    assert (typing_regular (E & x ~: sch_empty T1) (t1 ^ x) T2)
      by auto.
    apply typing_regular_abs with (L := L); auto with typing_regular.
    + eauto using environment_retract with typing_regular.
    + intros y Hn.
      assert (typing_regular (E & y ~: sch_empty T1) (t1 ^ y) T2)
        by auto.
      auto with typing_regular.
    + rewrite scheme_empty_type.
      eauto using scheme_from_env with typing_regular.
    + exists L.
      intros y Hny.
      assert (typing_regular (E & y ~: sch_empty T1) (t1 ^ y) T2)
        by auto.
      auto with typing_regular.
  - assert (type (typ_arrow S T)) as Hta
      by auto with typing_regular.
    inversion Hta; subst.
    eauto with typing_regular.
  - pick_freshes_gen L (sch_arity M) Xs.
    assert (typing_regular (E & Xs ~::* M) t1 (instance_vars M Xs))
      by auto.
    pick_fresh_gen L x.
    assert (typing_regular (E & x ~: M) (t2 ^ x) T2) by auto.
    apply typing_regular_let with (M := M) (L := L);
      auto with typing_regular.
    + eauto using environment_retract with typing_regular.
    + intros Ys Hf.
      assert (typing_regular (E & Ys ~::* M) t1 (instance_vars M Ys))
        by auto.
      auto with typing_regular.
    + intros y Hn.
      assert (typing_regular (E & y ~: M) (t2 ^ y) T2)
        by auto.
      auto with typing_regular.
    + intros Ys Hl.
      assert (typing_regular (E & Ys ~::* M) t1 (instance_vars M Ys))
        by auto.
      auto with typing_regular.
    + eauto using scheme_from_env with typing_regular.
    + exists L.
      intros y Hny.
      assert (typing_regular (E & y ~: M) (t2 ^ y) T2)
        by auto.
      auto with typing_regular.
  - apply typing_regular_constructor with (T2 := T2);
      auto with typing_regular kinding_regular.
  - assert
      (kind (knd_range
               (typ_or (typ_constructor c T2)
                       (typ_top (CSet.cosingleton c)))
               (typ_bot CSet.universe))) as Hk1
        by auto with kinding_regular.
    assert
      (kind (knd_range (typ_or T3 T4) (typ_bot CSet.universe))) as Hk2
      by auto with kinding_regular.
    pick_fresh_gen L x.
    assert
      (typing_regular (E & x ~: sch_empty (typ_variant T5)) 
         (t2 ^ x) T7) by auto.
    apply typing_regular_match
      with (L := L) (T1 := T1) (T2 := T2) (T3 := T3)
           (T4 := T4) (T5 := T5) (T6 := T6);
      auto with typing_regular kinding_regular.
    + intros y Hny.
      assert
        (typing_regular (E & y ~: sch_empty (typ_variant T5)) 
                        (t2 ^ y) T7)
        by auto.
      auto with typing_regular.
    + intros y Hny.
      assert
        (typing_regular (E & y ~: sch_empty (typ_variant T6)) 
                        (t3 ^ y) T7)
        by auto.
      auto with typing_regular.
    + inversion Hk1; subst.
      assert (type
                (typ_or (typ_constructor c T2)
                        (typ_top (CSet.cosingleton c)))) as Hto
          by assumption.
      inversion Hto; subst.
      assert (type (typ_constructor c T2)) as Htc by assumption.
      inversion Htc; auto.
    + inversion Hk2; subst.
      assert (type (typ_or T3 T4)) as Hto by assumption.
      inversion Hto; auto.
    + inversion Hk2; subst.
      assert (type (typ_or T3 T4)) as Hto by assumption.
      inversion Hto; auto.
    + exists L.
      intros y Hny.
      assert
        (typing_regular (E & y ~: sch_empty (typ_variant T5)) 
                        (t2 ^ y) T7)
        by auto.
      auto with typing_regular.
    + exists L.
      intros y Hny.
      assert
        (typing_regular (E & y ~: sch_empty (typ_variant T6)) 
                        (t3 ^ y) T7)
        by auto.
      auto with typing_regular.
  - assert (type (typ_variant T1)) as Htv
      by auto with typing_regular.
    inversion Htv; subst.
    pick_fresh_gen L x.
    assert (typing_regular (E & x ~: sch_empty T2) (t2 ^ x) T3)
      by auto.
    apply typing_regular_destruct
      with (L := L) (T1 := T1) (T2 := T2);
      auto with typing_regular.
    + intros y Hfy.
      assert (typing_regular (E & y ~: sch_empty T2) (t2 ^ y) T3)
        by auto.
      auto with typing_regular.
    + rewrite scheme_empty_type.
      eauto using scheme_from_env with typing_regular.
    + exists L.
      intros y Hny.
      assert
        (typing_regular (E & y ~: sch_empty T2) (t2 ^ y) T3)
        by auto.
      auto with typing_regular.
  - apply typing_regular_absurd with (T1 := T1);
      auto with typing_regular kinding_regular.
Qed.

Lemma regular_typing_inv : forall E t T,
    typing_regular E t T -> typing E t T.
Proof.
  introv Ht.
  induction Ht; eauto using typing.
Qed.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H : typing E _ _ |- _ =>
      apply (proj31 (typing_regular_wellformed (regular_typing H)))
  end : typing_regular.

Hint Extern 1 (term ?t) =>
  match goal with
  | H : typing _ t _ |- _ =>
      apply (proj32 (typing_regular_wellformed (regular_typing H)))
  end : typing_regular.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : typing _ _ T |- _ =>
      apply (proj33 (typing_regular_wellformed (regular_typing H)))
  end : typing_regular.

Inductive value_regular : trm -> Prop :=
  | value_regular_constructor : forall c t,
      term t ->
      value t ->
      value_regular (trm_constructor c t)
  | value_regular_abs : forall t,
      term_body t ->
      value_regular (trm_abs t).

Lemma value_regular_wellformed : forall t,
    value_regular t -> term t.
Proof.
  introv Hv.
  induction Hv; auto.
Qed.

Hint Constructors value_regular : value_regular.

Hint Extern 1 (term ?t) =>
  match goal with
  | H : value_regular t |- _ =>
      apply (value_regular_wellformed H)
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

Lemma regular_value_inv : forall t,
    value_regular t -> value t.
Proof.
  introv Hv.
  induction Hv; auto using value.
Qed.

Hint Extern 1 (term ?t) =>
  match goal with
  | H : value t |- _ =>
      apply (value_regular_wellformed (regular_value H))
  end : value_regular.

Inductive red_regular : trm -> trm -> Prop :=
  | red_regular_let : forall t1 t2, 
      term t1 ->
      term_body t2 ->
      value t1 -> 
      red_regular (trm_let t1 t2) (t2 ^^ t1)
  | red_regular_let_1 : forall t1 t1' t2, 
      term t1 ->
      term t1' ->
      term_body t2 ->
      red_regular t1 t1' -> 
      red_regular (trm_let t1 t2) (trm_let t1' t2)
  | red_regular_app_1 : forall t1 t1' t2,
      term t1 ->
      term t1' ->
      term t2 ->
      red_regular t1 t1' -> 
      red_regular (trm_app t1 t2) (trm_app t1' t2)
  | red_regular_app_2 : forall t1 t2 t2', 
      term t1 ->
      term t2 ->
      term t2' ->
      value t1 ->
      red_regular t2 t2' ->
      red_regular (trm_app t1 t2) (trm_app t1 t2')
  | red_regular_app_3 : forall t1 t2, 
      term t2 ->
      term_body t1 ->
      value t2 ->  
      red_regular (trm_app (trm_abs t1) t2) (t1 ^^ t2)
  | red_regular_constructor : forall c t t',
      term t ->
      term t' ->
      red_regular t t' ->
      red_regular (trm_constructor c t) (trm_constructor c t')
  | red_regular_match_1 : forall c t1 t1' t2 t3,
      term t1 ->
      term t1' ->
      term_body t2 ->
      term_body t3 ->
      red_regular t1 t1' ->
      red_regular (trm_match t1 c t2 t3) (trm_match t1' c t2 t3)
  | red_regular_match_2 : forall c1 c2 t1 t2 t3,
      term t1 ->
      term_body t2 ->
      term_body t3 ->
      c1 = c2 ->
      value (trm_constructor c1 t1) ->
      red_regular (trm_match (trm_constructor c1 t1) c2 t2 t3)
          (t2 ^^ (trm_constructor c1 t1))
  | red_regular_match_3 : forall c1 c2 t1 t2 t3,
      term t1 ->
      term_body t2 ->
      term_body t3 ->
      c1 <> c2 ->
      value (trm_constructor c1 t1) ->
      red_regular (trm_match (trm_constructor c1 t1) c2 t2 t3)
          (t3 ^^ (trm_constructor c1 t1))
  | red_regular_destruct_1 : forall c t1 t1' t2,
      term t1 ->
      term t1' ->
      term_body t2 ->
      red_regular t1 t1' ->
      red_regular (trm_destruct t1 c t2) (trm_destruct t1' c t2)
  | red_regular_destruct_2 : forall c1 c2 t1 t2,
      term t1 ->
      term_body t2 ->
      c1 = c2 ->
      value (trm_constructor c1 t1) ->
      term_body t2 ->
      red_regular (trm_destruct (trm_constructor c1 t1) c2 t2)
          (t2 ^^ t1).

Lemma red_regular_wellformed : forall t1 t2,
    red_regular t1 t2 -> term t1 /\ term t2.
Proof.
  introv Hv.
  induction Hv; auto.
Qed.

Hint Constructors red_regular : red_regular.

Hint Extern 1 (term ?t) =>
  match goal with
  | H : red_regular t _ |- _ =>
      apply (proj1 (red_regular_wellformed H))
  | H : red_regular _ t |- _ =>
      apply (proj2 (red_regular_wellformed H))
  end : red_regular.

Lemma regular_red : forall t1 t2,
    red t1 t2 -> red_regular t1 t2.
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
Qed.

Lemma regular_red_inv : forall t1 t2,
    red_regular t1 t2 -> red t1 t2.
Proof.
  introv Hr.
  induction Hr; auto using red.
Qed.

Hint Extern 1 (term ?t) =>
  match goal with
  | H : red t _ |- _ =>
      apply (proj1 (red_regular_wellformed (regular_red H)))
  | H : red _ t |- _ =>
      apply (proj2 (red_regular_wellformed (regular_red H)))
  end : red_regular.
