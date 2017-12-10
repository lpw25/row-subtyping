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

(* =============================================================== *)
(** * Properties of types *)

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
(** * Regularity of type equality and kinding judgments *)

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

(* Isomorphic to kinding, but including proofs of well-formedness *) 
Inductive kinding_regular : env -> typ -> knd -> Prop :=
  | kinding_regular_var : forall E X K,
      environment E ->
      kind K ->
      type (typ_fvar X) ->
      binds X (bind_knd K) E ->
      kinding_regular E (typ_fvar X) K
  | kinding_regular_constructor : forall E c T K,
      environment E ->
      type T ->
      type (typ_constructor c T) ->
      kind knd_type ->
      kind K ->
      kinding_regular E T knd_type ->
      K = knd_row (CSet.singleton c) ->
      kinding_regular E (typ_constructor c T) K
  | kinding_regular_or : forall E T1 cs1 T2 cs2 K,
      environment E ->
      type T1 ->
      type T2 ->
      type (typ_or T1 T2) ->
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
      type (typ_row T) ->
      kind (knd_row CSet.universe) ->
      kind K ->
      kinding_regular E T (knd_row CSet.universe) ->
      K = knd_range T T ->
      kinding_regular E (typ_row T) K
  | kinding_regular_variant : forall E T T1 T2 K,
      environment E ->
      type T ->
      type (typ_variant T) ->
      kind (knd_range T1 T2) ->
      kind K ->
      kinding_regular E T (knd_range T1 T2) ->
      K = knd_type ->
      kinding_regular E (typ_variant T) K
  | kinding_regular_arrow : forall E T1 T2 K,
      environment E ->
      type T1 ->
      type T2 ->
      type (typ_arrow T1 T2) ->
      kind knd_type ->
      kind K ->
      kinding_regular E T1 knd_type -> 
      kinding_regular E T2 knd_type -> 
      K = knd_type ->
      kinding_regular E (typ_arrow T1 T2) K
  | kinding_regular_top : forall E cs K,
      environment E ->
      type (typ_top cs) ->
      kind K ->
      CSet.Nonempty cs ->
      environment E ->
      K = knd_row cs ->
      kinding_regular E (typ_top cs) K
  | kinding_regular_bot : forall E cs K,
      environment E ->
      type (typ_bot cs) ->
      kind K ->
      CSet.Nonempty cs ->
      environment E ->
      K = knd_row cs ->
      kinding_regular E (typ_bot cs) K
  | kinding_regular_meet : forall E T1 T2 K,
      environment E ->
      type T1 ->
      type T2 ->
      type (typ_meet T1 T2) ->
      kind K ->
      kinding_regular E T1 K ->
      kinding_regular E T2 K ->
      is_row_kind K ->
      kinding_regular E (typ_meet T1 T2) K
  | kinding_regular_join : forall E T1 T2 K,
      environment E ->
      type T1 ->
      type T2 ->
      type (typ_join T1 T2) ->
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
      kind (knd_range T1 T2) ->
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
  - apply kinding_regular_variant with (T1 := T1) (T2 := T2);
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

Lemma regular_type_equal : forall E T1 T2 K,
    type_equal E T1 T2 K -> type_equal_regular E T1 T2 K.
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

Lemma regular_type_equal_inv : forall E T1 T2 K,
    type_equal_regular E T1 T2 K -> type_equal E T1 T2 K.
Proof.
  introv Hte.
  induction Hte;
    eauto using type_equal, regular_type_equal_symm_inv.
Qed.

Inductive valid_kind_regular : env -> knd -> Prop :=
  | valid_kind_regular_type : forall E,
      environment E ->
      kind knd_type ->
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
      kind (knd_range T1 T2) ->
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
  - assert
      (type_equal_regular E T2 (typ_meet T2 T1)
                          (knd_row CSet.universe))
      by auto using regular_type_equal.
    assert (type (typ_meet T2 T1)) as Ht
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

Inductive kinding_scheme_vars_regular
  : env -> sch -> list var -> Prop :=
  | kinding_scheme_vars_regular_empty : forall E T,
      environment E ->
      type T ->
      kind knd_type ->
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
  - assert (kinding_regular E T knd_type)
      by auto using regular_kinding.
    auto with kinding_regular kinding_scheme_vars_regular.
  - assert (valid_kind_regular E K)
      by auto using regular_valid_kind.
    apply kinding_scheme_vars_regular_bind;
      auto with kinding_scheme_vars_regular valid_kind_regular.
Qed.

Lemma regular_kinding_scheme_vars_inv : forall E M Xs,
    kinding_scheme_vars_regular E M Xs -> kinding_scheme_vars E M Xs.
Proof.
  introv Hs.
  induction Hs;
    auto using kinding_scheme_vars.
Qed.

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
  - assert (valid_kind_regular E K)
      by auto using regular_valid_kind.
    auto with kinding_env_regular valid_kind_regular.
  - assert (kinding_scheme_regular E M)
      by auto using regular_kinding_scheme.
    auto with kinding_env_regular kinding_scheme_regular.
Qed.

Lemma regular_kinding_env_inv : forall E,
    kinding_env_regular E -> kinding_env E.
Proof.
  introv He.
  induction He; auto using kinding_env.
Qed.

(* =============================================================== *)
(** * Properties of judgments *)

(* *************************************************************** *)
(** ** Regularity of relations *)

(** A kinding relation is restricted to well-formed objects. *)

Lemma kinding_regular : forall E T K,
  kinding E T K -> environment E /\ type T /\ kind K.
Proof.
  split; induction H; subst;
    intuition eauto using kind_from_env with constrs.
  - inversion H3.
    inversion H5.
    auto with constrs.
Qed.

Lemma kindings_regular : forall E n Ts Ks,
  kindings E n Ts Ks ->
  environment E /\ types n Ts /\ kinds n Ks.
Proof.
  split; induction* H.
  split.
  - split.
    + simpl.
      f_equal.
      destruct IHkindings as [[Hl Ht] Hk]; auto.
    + lets [_ [Ht Hk]] : (kinding_regular H).
      lets [[_ Hts] Hks] : IHkindings.
      apply* Forall_cons.
  - split.
    + simpl.
      f_equal.
      destruct IHkindings as [_ [Hl Hks]]; auto.
    + destruct IHkindings as [_ [Hl Hks]]; auto.
      lets [_ [Ht Hk]] : (kinding_regular H).
      apply* Forall_cons.
Qed.  

Lemma kindings_length : forall E n Ts Ks,
    kindings E n Ts Ks ->
    length Ts = n /\ length Ks = n.
Proof.
  intros.
  induction H; simpl; iauto.
Qed.

Lemma kinding_body_regular : forall E n Ks T,
    kinding_body E n Ks T ->
    environment E /\ kinds n Ks /\ type_body n T.
Proof.
  introv H.
  destruct H as [L H].
  splits.
  - pick_freshes n Xs.
    destruct H with Xs as [_ Hk]; auto.
    eapply kinding_regular in Hk; auto.
    destruct* Hk.
  - pick_freshes n Xs.
    destruct H with Xs as [Hkd _]; auto.
  - exists_fresh Xs Hf.
    destruct H with Xs as [_ Hk]; auto.
    eapply kinding_regular in Hk; auto.
    destruct* Hk.
Qed.

Lemma kinding_scheme_regular : forall E M,
    kinding_scheme E M -> environment E /\ scheme M.
Proof.
  introv Hks.
  destruct (kinding_body_regular Hks) as [He [Hk Ht]].
  split; auto.
  split; auto.
Qed.

Lemma kinding_env_regular : forall E,
    kinding_env E -> environment E.
Proof.
  introv H.
  induction* H.
  apply* environment_typ.
  apply kinding_scheme_regular in H0.
  iauto.
Qed.

(* Automation of kinding regularity lemmas *)

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : kinding _ _ K |- _ =>
      apply (proj33 (kinding_regular H))
  | H1 : environment ?E, H2 : binds _ (bind_knd K) ?E |- _ =>
      apply (kind_from_env H1 H2)
  | H1 : kinding_env ?E, H2 : binds _ (bind_knd K) ?E |- _ =>
      apply (kind_from_env (kinding_env_regular H1) H2)
  end.

Hint Extern 1 (type ?T) =>
  match goal with
  | H: kinding _ T _ |- _ =>
      apply (proj32 (kinding_regular H))
  end.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H: kinding_scheme _ M |- _ =>
      apply (proj2 (kinding_scheme_regular H))
  | H1 : environment ?E, H2 : binds _ (bind_typ M) ?E |- _ =>
      apply (scheme_from_env H1 H2)
  | H1 : kinding_env ?E, H2 : binds _ (bind_typ M) ?E |- _ =>
      apply (scheme_from_env (kinding_env_regular H1) H2)
end.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H: kinding_env E |- _ =>
      apply (kinding_env_regular H)
  | H: kinding E _ _ |- _ =>
      apply (proj31 (kinding_regular H))
  | H: kindings E _ _ _ |- _ =>
      apply (proj31 (kindings_regular H))
  | H: kinding_body E _ _ _ |- _ =>
      apply (proj31 (kinding_body_regular H))
  | H: kinding_scheme E _ |- _ =>
      apply (proj1 (kinding_scheme_regular H))
  end.

Hint Extern 1 (environment (?E & ?F)) =>
  match goal with
  | H: environment (E & _ & F) |- _ =>
      apply (environment_concat_inv H)
  end.

Hint Extern 1 (kinds ?n ?Ks) =>
  match goal with
  | H: kindings _ n _ Ks |- _ =>
      apply (proj33 (kindings_regular H))
  | H : kinding_body _ n Ks _ |- _ =>
      apply (proj32 (kinding_body_regular H))
  end.

Hint Extern 1 (types ?n ?Ts) =>
  match goal with
  | H: kindings _ n Ts _ |- _ =>
      apply (proj32 (kindings_regular H))
  end.

Hint Extern 1 (type_body ?n ?T) =>
  match goal with
  | H: kinding_body _ n _ T |- _ =>
      apply (proj33 (kinding_body_regular H))
  end.

Ltac invert_kind_rec Hs :=
  try match goal with
  | [ H : kind (knd_row _) |- _ ] =>
    let b := inList H Hs in
    match b with
    | true => fail 1
    | false =>
      try invert_kind_rec (H, Hs);
      inversion H
    end
  | [ H : kinding _ _ (knd_row ?cs) |- _ ] =>
    let b := inList H Hs in
    match b with
    | true => fail 1
    | false =>
      try invert_kind_rec (H, Hs);
      let Hk := fresh "Hk" in
      assert (kind (knd_row cs))
        as Hk by (apply (proj33 (kinding_regular H)));
      inversion Hk
    end
  end.

Ltac invert_kind :=
  invert_kind_rec tt;
  subst.

Ltac invert_type_rec Hs :=
  try match goal with
  | [ H : type (typ_constructor _ _)  |- _ ] =>
    invert_type_rec_body H Hs
  | [ H : type (typ_or _ _)  |- _ ] =>
    invert_type_rec_body H Hs
  | [ H : type (typ_variant _ _)  |- _ ] =>
    invert_type_rec_body H Hs
  | [ H : type (typ_arrow _ _)  |- _ ] =>
    invert_type_rec_body H Hs
  | [ H : type (typ_meet _ _)  |- _ ] =>
    invert_type_rec_body H Hs
  | [ H : type (typ_join _ _)  |- _ ] =>
    invert_type_rec_body H Hs
  end

with invert_type_rec_body H Hs :=
  let b := inList H Hs in
  match b with
  | true => fail 1
  | false =>
    try invert_type_rec (H, Hs);
    inversion H
  end.

Ltac invert_type :=
  invert_type_rec tt;
  subst.

Lemma type_equal_step_regular : forall E T1 T2,
  type_equal_step E T1 T2 ->
  environment E ->
  (type T1 -> type T2) /\ (type T2 -> type T1).
Proof.
  introv Hs.
  induction Hs; intuition auto;
    match goal with
    | [ |- type _ ] =>
      subst;
      invert_type;
      invert_type;
      subst;
      auto
    end.
Qed.

(** Type equality preserves regularity *)

Lemma type_equal_regular : forall E T1 T2 K,
  type_equal E T1 T2 K ->
  environment E /\ type T1 /\ type T2 /\ kind K.
Proof.
  introv He.
  induction He; intuition auto.
  - destruct (type_equal_step_regular H); auto.
  - destruct (type_equal_step_regular H); auto.
Qed.

Lemma subtype_regular : forall E T1 T2,
    subtype E T1 T2 -> environment E /\ type T1 /\ type T2.
Proof.
  introv Hs.
  destruct (type_equal_regular Hs) as [ He [ _ [ Ht Hk ] ] ].
  inversion* Ht.
Qed.

(* Automation of equality regularity lemmas *)

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal _ _ _ K |- _ =>
      apply (proj44 (type_equal_regular H))
  end.

Hint Extern 1 (type ?T) =>
  match goal with
  | H: type_equal _ T _ _ |- _ =>
      apply (proj42 (type_equal_regular H))
  | H: type_equal _ _ T _ |- _ =>
      apply (proj43 (type_equal_regular H))
  | H: subtype _ T _ |- _ =>
      apply (proj32 (subtype_regular H))
  | H: subtype _ _ T |- _ =>
      apply (proj33 (subtype_regular H))
  end.

Hint Extern 1 (environment ?E) =>
  match goal with
  | H: type_equal E _ _ _ |- _ =>
      apply (proj41 (type_equal_regular H))
  | H: subtype E _ _ |- _ =>
      apply (proj31 (subtype_regular H))
  end.

Hint Extern 1 (environment (?E & environment_subst ?X ?T ?F)) =>
  match goal with
  | H1: environment (E & X ~:: ?K & F), H2: kinding E T ?K |- _ =>
      apply (environment_subst_inv_r X
               (environment_concat_inv H1)
               (proj32 (kinding_regular H2)))
  | H1: environment (E & X ~:: ?K & F), H2: type_equal E T T ?K |- _ =>
      apply (environment_subst_inv_r X
               (environment_concat_inv H1)
               (proj41 (type_equal_regular H2)))
  | H1: environment (E & X ~:: _ & F), H2: type T |- _ =>
      apply (environment_subst_inv_r X (environment_concat_inv H1) H2)
  | H1: environment (E & F), H2: type T |- _ =>
      apply (environment_subst_inv_r X H1 H2)
  end.

(** A typing relation is restricted to well-formed objects. *)

Lemma typing_regular : forall E e T,
  typing E e T -> environment E /\ term e /\ type T.
Proof.
  splits 3.
  - induction* H.
    pick_freshes (sch_arity M) Xs.
    eapply environment_concat_inv_l.
    apply* H0.
  - induction H; eauto.
  - induction* H.
    inversion* IHtyping1.
Qed.

Lemma typing_scheme_regular : forall E e M,
    typing_scheme E e M -> environment E /\ term e /\ scheme M.
Proof.
  unfold typing_scheme.
  introv [Hks [L Ht]].
  splits*.
  - pick_freshes (sch_arity M) Xs.
    eapply typing_regular in Ht; auto.
    eapply environment_concat_inv_l; iauto.
  - pick_freshes (sch_arity M) Xs.
    eapply typing_regular in Ht; iauto.
  - unfold scheme, type_body.
    split*.
    exists L.
    introv Hf.
    eapply typing_regular in Ht; iauto.
Qed.

(** Automation of typing regularity lemma *)

Hint Extern 1 (environment ?E) =>
  match goal with
  | H: typing E _ _ |- _ =>
      apply (proj31 (typing_regular H))
  | H: typing_scheme E _ _ |- _ =>
      apply (proj31 (typing_scheme_regular H))
  end.

Hint Extern 1 (term ?e) =>
  match goal with
  | H: typing _ e _ |- _ =>
      apply (proj32 (typing_regular H))
  | H: typing_scheme _ e _ |- _ =>
      apply (proj32 (typing_scheme_regular H))
  end.

Hint Extern 1 (type ?T) =>
  match goal with
  | H: typing _ _ T |- _ =>
      apply (proj33 (typing_regular H))
  end.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H: typing_scheme _ _ M |- _ =>
      apply (proj33 (typing_scheme_regular H))
  end.

(** The value predicate is restricted to well-formed terms. *)

Lemma value_regular : forall e,
  value e -> term e.
Proof.
  introv Hv.
  induction* Hv.
Qed.

Hint Resolve value_regular.

(** A reduction relation is restricted to well-formed terms. *)

Lemma red_regular : forall e e',
  red e e' -> term e /\ term e'.
Proof.
  introv Hr.
  induction Hr; iauto.
  inversion* H0.
Qed.

Hint Extern 1 (term ?t) =>
  match goal with
  | H: red t _ |- _ => apply (proj1 (red_regular H))
  | H: red _ t |- _ => apply (proj2 (red_regular H))
  end.