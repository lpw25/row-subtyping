(************************************************
 *          Row Subtyping - Well-formedness     *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import List LibLN Definitions Substitution.

(* *************************************************************** *)
(** ** Automation *)

Hint Constructors kind type scheme_vars term environment.

Hint Unfold is_row_kind.

Hint Extern 1 (types _ _) => split; auto.

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

Lemma ok_from_environment : forall E,
  environment E -> ok E.
Proof.
  introv He.
  induction He; auto. 
Qed.

Hint Resolve ok_from_environment.

Lemma scheme_from_env : forall E x M,
    environment E ->
    binds x (bind_typ M) E ->
    scheme M.
Proof.
  introv He Hb.
  induction E using env_ind; rew_env_concat.
  - false (binds_empty_inv Hb).
  - destruct (binds_push_inv Hb)
      as [ [ Hvar Hbind ] | [ Hvar Hbind ] ].
    + { subst.
        inversion He.
        - false (empty_push_inv H0).
        - destruct (eq_push_inv H) as [_ [Heq _]].
          false Heq.
        - destruct (eq_push_inv H) as [_ [Heq _]].
          inversion Heq.
          subst*. }
    + eapply IHE; auto.
Qed.

Lemma kind_from_env : forall E x K,
    environment E ->
    binds x (bind_knd K) E ->
    kind K.
Proof.
  introv He Hb.
  induction E using env_ind; rew_env_concat.
  - false (binds_empty_inv Hb).
  - destruct (binds_push_inv Hb)
      as [ [ Hvar Hbind ] | [ Hvar Hbind ] ].
    + { subst.
        inversion He.
        - false (empty_push_inv H0).
        - destruct (eq_push_inv H) as [_ [Heq _]].
          inversion Heq.
          subst*.
        - destruct (eq_push_inv H) as [_ [Heq _]].
          false Heq. }
    + eapply IHE; auto.
Qed.

Lemma kinds_from_env : forall E Xs Ks,
    environment (E & Xs ~::* Ks) ->
    length Xs = length Ks ->
    kinds (length Ks) Ks.
Proof.
  introv He Hl.
  split*.
  gen Xs.
  induction Ks; introv He Hl; auto.
  destruct Xs; tryfalse.
  rew_kinds in He.
  inversion He.
  - apply empty_push_inv in H0.
    tryfalse.
  - destruct (eq_push_inv H) as [? [Hb ?]].
    inversion Hb.
    inversion Hl.
    subst.
    eauto.
  - destruct (eq_push_inv H) as [_ [Hb _]].
    tryfalse.
Qed.

Hint Rewrite in_empty in_singleton in_union : rew_in.

Tactic Notation "rew_in" :=
  autorewrite with rew_in.

Tactic Notation "rew_in" "in" hyp(H) :=
  autorewrite with rew_in in H.

Lemma typ_fv_open_vars : forall T Xs X,
    X \in typ_fv T ->
    X \in typ_fv (typ_open_vars T Xs).
Proof.
  introv Hfv.
  unfold typ_open_vars, typ_fvars.
  induction T;
    simpl; simpl in Hfv; rew_in; rew_in in Hfv; iauto.
Qed.

Lemma kinding_closed : forall E T K X,
    kinding E T K ->
    X \in typ_fv T ->
    X \in dom E.
Proof.
  introv Hk Hfv.
  induction Hk; simpl in Hfv; rew_in in Hfv; iauto.
  subst.
  eapply get_some_inv.
  apply H0.
Qed.

Lemma kinding_scheme_closed : forall E M X,
    kinding_scheme E M ->
    X \in sch_fv M ->
    X \in dom E.
Proof.
  introv Hks Hfv.
  unfold kinding_scheme, kinding_body in Hks.
  unfold sch_fv in Hfv.
  destruct Hks as [L Hk].
  pick_freshes (sch_arity M) Xs.
  destruct Hk with Xs as [_ Hkk]; auto.
  eapply kinding_closed with (X := X) in Hkk; auto.
  - rewrite dom_concat in Hkk.
    rew_in in Hkk.
    destruct* Hkk.
    rewrite dom_map in H.
    rewrite dom_singles in H.
    + assert (fresh \{X} (sch_arity M) Xs) by auto.
      eapply fresh_single_notin in H; auto.
      tryfalse.
    + apply fresh_length in Fr.
      unfold sch_arity in Fr.
      rewrite! liblist_length_eq_length.
      auto.
  - apply* typ_fv_open_vars.
Qed.

Lemma kinding_env_closed : forall E X,
    kinding_env E ->
    X \in env_fv E ->
    X \in dom E.
Proof.
  introv Hk Hfv.
  induction Hk.
  - rewrite env_fv_empty in Hfv.
    rew_in in Hfv.
    iauto.
  - rewrite env_fv_push_inv in Hfv.
    rewrite dom_push.
    rew_in.
    right.
    rew_in in Hfv.
    destruct* Hfv.
  - rewrite env_fv_push_inv in Hfv.
    rewrite dom_push.
    rew_in.
    right.
    rew_in in Hfv.
    destruct* Hfv.
    simpl in H1.
    apply kinding_scheme_closed with M; auto.
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