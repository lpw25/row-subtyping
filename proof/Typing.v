(************************************************
 *           Row Subtyping - Typing             *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import LibLN Utilities Cofinite Disjoint Definitions
        Opening FreeVars Environments Subst Wellformedness
        Weakening Substitution Kinding Subtyping Inversion Coercible.

(* *************************************************************** *)
(** Valid bindings *)

Lemma valid_scheme_from_valid_env : forall X v E D M,
    valid_env v E D ->
    binds X M D ->
    valid_scheme v E M.
Proof.
  introv He Hb.
  induction He.
  - apply binds_empty_inv in Hb; contradiction.
  - destruct (binds_push_inv Hb) as [[Hx Hbnd]|[Hx Hbnd]];
      subst; auto.
Qed.

(* ****************************************************** *)
(** ** Environment extension by ranges of a valid scheme *)

Lemma valid_tenv_extension_valid_scheme : forall v L E Xs M,
    valid_scheme_aux v L E M ->
    fresh L (sch_arity M) Xs ->
    valid_tenv_extension v E (Xs ~: M).
Proof.
  introv Hs Hf.
  destruct Hs as [? ? ? ? Hs].
  specialize (Hs Xs Hf).
  inversion Hs; subst.
  assumption.
Qed.

Lemma valid_tenv_push_ranges : forall v L E Xs M,
    valid_tenv v E ->
    valid_scheme_aux v L E M ->
    fresh L (sch_arity M) Xs ->
    valid_tenv v (E & Xs ~: M).
Proof.
  introv Ht Hs Hf.
  eauto using valid_tenv_extend,
    valid_tenv_extension_valid_scheme.
Qed.

(* ****************************************************** *)
(** ** Induction scheme with valid environments *)

Record typing_with_envs v E D P t T :=
  typing_with_envs_c
    { He : valid_tenv v E;
      Hd : valid_env v E D;
      Hp : valid_store_type E P;
      Ht : typing v E D P t T; }.

Hint Constructors typing_with_envs.

Lemma typing_with_envs_ind :
  forall (C : version -> tenv -> env -> styp ->
              trm -> typ -> Prop),
    (forall (E : tenv) (D : env) (P : styp) 
            (t : trm) (T1 T2 : typ),
        valid_tenv version_row_subtyping E ->
        valid_tenv_extension version_row_subtyping E empty ->
        valid_env version_row_subtyping E D ->
        valid_store_type E P ->
        typing version_row_subtyping E D P t T1 ->
        C version_row_subtyping E D P t T1 ->
        type_equal version_row_subtyping
                   E empty nil nil T1 T2 knd_type ->
        C version_row_subtyping E D P t T2) ->
    (forall (E : tenv) (D : env) (P : styp) 
            (t : trm) (T1 T2 : typ),
        valid_tenv version_full_subtyping E ->
        valid_tenv_extension version_full_subtyping E empty ->
        valid_env version_full_subtyping E D ->
        valid_store_type E P ->
        typing version_full_subtyping E D P t T1 ->
        C version_full_subtyping E D P t T1 ->
        subtype version_full_subtyping
                E empty nil nil T1 T2 knd_type ->
        C version_full_subtyping E D P t T2) ->
    (forall (v : version) (E : tenv)
            (D : LibEnv.env sch) (P : styp) 
            (x : var) (M : sch) (T1 : typ) 
            (Us : list typ),
        valid_tenv v E ->
        valid_tenv_extension v E empty ->
        valid_env v E D ->
        valid_store_type E P ->
        binds x M D ->
        valid_instance v E Us M ->
        T1 = instance M Us ->
        C v E D P (trm_fvar x) T1) ->
    (forall (L : fset var) (v : version) 
            (E : tenv) (D : LibEnv.env sch) 
            (P : styp) (T1 T2 : typ) (t1 : trm),
        valid_tenv v E ->
        valid_tenv_extension v E empty ->
        valid_env v E D ->
        valid_store_type E P ->
        kinding E empty T1 knd_type ->
        (forall x : var,
            x \notin (L \u dom D) ->
            typing v E (D & x ~ sch_empty T1) P (t1 ^ x) T2) ->
        (forall x : var,
            x \notin (L \u dom D) ->
            C v E (D & x ~ sch_empty T1) P (t1 ^ x) T2) ->
        C v E D P (trm_abs t1) (typ_arrow T1 T2)) ->
    (forall (v : version) (E : tenv) 
            (P : styp) (D : env) (T1 T2 : typ) 
            (t1 t2 : trm),
        valid_tenv v E ->
        valid_tenv_extension v E empty ->
        valid_env v E D ->
        valid_store_type E P ->
        typing v E D P t1 (typ_arrow T1 T2) ->
        C v E D P t1 (typ_arrow T1 T2) ->
        typing v E D P t2 T1 ->
        C v E D P t2 T1 -> C v E D P (trm_app t1 t2) T2) ->
    (forall (L : vars) (M : sch) (v : version)
            (E : tenv) (D : env) (P : styp) 
            (T2 : typ) (t1 t2 : trm),
        valid_tenv v E ->
        valid_tenv_extension v E empty ->
        valid_env v E D ->
        valid_store_type E P ->
        value t1 ->
        valid_scheme_aux v L E M ->
        (forall Xs : list var,
            fresh L (sch_arity M) Xs ->
            typing v (E & Xs ~: M) D P t1
                   (instance_vars M Xs)) ->
        (forall Xs : list var,
            fresh L (sch_arity M) Xs ->
            C v (E & Xs ~: M) D P t1 (instance_vars M Xs)) ->
        (forall x : var,
            x \notin (L \u dom D) ->
            typing v E (D & x ~ M) P (t2 ^ x) T2) ->
        (forall x : var,
            x \notin (L \u dom D) ->
            C v E (D & x ~ M) P (t2 ^ x) T2) ->
        C v E D P (trm_let t1 t2) T2) ->
    (forall (L : fset var) (v : version) 
            (E : tenv) (D : env) (P : styp) 
            (T1 T2 : typ) (t1 t2 : trm),
        valid_tenv v E ->
        valid_tenv_extension v E empty ->
        valid_env v E D ->
        valid_store_type E P ->
        kinding E empty T1 knd_type ->
        typing v E D P t1 T1 ->
        C v E D P t1 T1 ->
        (forall x : var,
            x \notin (L \u dom D) ->
            typing v E (D & x ~ sch_empty T1) P (t2 ^ x) T2) ->
        (forall x : var,
            x \notin (L \u dom D) ->
            C v E (D & x ~ sch_empty T1) P (t2 ^ x) T2) ->
        C v E D P (trm_let t1 t2) T2) ->
    (forall (c : CSet.MSet.elt) (v : version) 
            (E : tenv) (D : env) (P : styp) 
            (T1 T2 : typ) (t : trm),
        valid_tenv v E ->
        valid_tenv_extension v E empty ->
        valid_env v E D ->
        valid_store_type E P ->
        typing v E D P t T1 ->
        C v E D P t T1 ->
        subtype v E empty nil nil (typ_constructor c T1)
                (typ_proj CSet.universe (CSet.singleton c) T2)
                (knd_row (CSet.singleton c)) ->
        C v E D P (trm_constructor c t) (typ_variant T2)) ->
    (forall (L : fset var) (c : CSet.MSet.elt)
            (v : version) (E : tenv) (D : env) 
            (P : styp) (T1 T2 T3 T4 : typ) 
            (t1 t2 t3 : trm),
        valid_tenv v E ->
        valid_tenv_extension v E empty ->
        valid_env v E D ->
        valid_store_type E P ->
        typing v E D P t1 (typ_variant T1) ->
        C v E D P t1 (typ_variant T1) ->
        subtype v E empty nil nil
                (typ_proj CSet.universe (CSet.singleton c) T1)
                (typ_proj CSet.universe (CSet.singleton c) T2)
                (knd_row (CSet.singleton c)) ->
        subtype v E empty nil nil
                (typ_proj CSet.universe (CSet.cosingleton c) T1)
                (typ_proj CSet.universe (CSet.cosingleton c) T3)
                (knd_row (CSet.cosingleton c)) ->
        (forall x : var,
            x \notin (L \u dom D) ->
            typing v E (D & x ~ sch_empty (typ_variant T2)) P
                   (t2 ^ x) T4) ->
        (forall x : var,
            x \notin (L \u dom D) ->
            C v E (D & x ~ sch_empty (typ_variant T2)) P
              (t2 ^ x) T4) ->
        (forall y : var,
            y \notin (L \u dom D) ->
            typing v E (D & y ~ sch_empty (typ_variant T3)) P
                   (t3 ^ y) T4) ->
        (forall y : var,
            y \notin (L \u dom D) ->
            C v E (D & y ~ sch_empty (typ_variant T3)) P
              (t3 ^ y) T4) ->
        C v E D P (trm_match t1 c t2 t3) T4) ->
    (forall (L : fset var) (c : CSet.MSet.elt)
            (v : version) (E : tenv) (D : env) 
            (P : styp) (T1 T2 T3 : typ) 
            (t1 t2 : trm),
        valid_tenv v E ->
        valid_tenv_extension v E empty ->
        valid_env v E D ->
        valid_store_type E P ->
        typing v E D P t1 (typ_variant T1) ->
        C v E D P t1 (typ_variant T1) ->
        subtype v E empty nil nil
                (typ_proj CSet.universe (CSet.singleton c) T1)
                (typ_constructor c T2)
                (knd_row (CSet.singleton c)) ->
        subtype v E empty nil nil
                (typ_proj CSet.universe (CSet.cosingleton c) T1)
                (typ_bot (knd_row (CSet.cosingleton c)))
                (knd_row (CSet.cosingleton c)) ->
        (forall x : var,
            x \notin (L \u dom D) ->
            typing v E (D & x ~ sch_empty T2) P (t2 ^ x) T3) ->
        (forall x : var,
            x \notin (L \u dom D) ->
            C v E (D & x ~ sch_empty T2) P (t2 ^ x) T3) ->
        C v E D P (trm_destruct t1 c t2) T3) ->
    (forall (v : version) (E : tenv) 
            (D : env) (P : styp) (T1 T2 : typ) 
            (t1 : trm),
        valid_tenv v E ->
        valid_tenv_extension v E empty ->
        valid_env v E D ->
        valid_store_type E P ->
        typing v E D P t1 (typ_variant T1) ->
        C v E D P t1 (typ_variant T1) ->
        subtype v E empty nil nil T1 (typ_bot knd_row_all)
                knd_row_all ->
        kinding E empty T2 knd_type ->
        C v E D P (trm_absurd t1) T2) ->
    (forall (L : fset var) (v : version) 
            (E : tenv) (D : LibEnv.env sch) 
            (P : styp) (T1 T2 : typ) (t1 : trm),
        valid_tenv v E ->
        valid_tenv_extension v E empty ->
        valid_env v E D ->
        valid_store_type E P ->
        kinding E empty T1 knd_type ->
        kinding E empty T2 knd_type ->
        (forall x y : var,
            x \notin (L \u dom D) ->
            y \notin (L \u dom D \u \{ x}) ->
            typing v E
                   (D & x ~ sch_empty (typ_arrow T1 T2) &
                    y ~ sch_empty T1) P
                   (t1 ^* y :: (x :: nil)%list) T2) ->
        (forall x y : var,
            x \notin (L \u dom D) ->
            y \notin (L \u dom D \u \{ x}) ->
            C v E
              (D & x ~ sch_empty (typ_arrow T1 T2) &
               y ~ sch_empty T1) P
              (t1 ^* y :: (x :: nil)%list) T2) ->
        C v E D P (trm_fix t1) (typ_arrow T1 T2)) ->
    (forall (v : version) (E : tenv) 
            (D : env) (P : styp),
        valid_tenv v E ->
        valid_tenv_extension v E empty ->
        valid_env v E D ->
        valid_store_type E P ->
        C v E D P trm_unit typ_unit) ->
    (forall (v : version) (E : tenv) 
            (D : env) (P : styp) (T1 T2 : typ) 
            (t1 t2 : trm),
        valid_tenv v E ->
        valid_tenv_extension v E empty ->
        valid_env v E D ->
        valid_store_type E P ->
        typing v E D P t1 T1 ->
        C v E D P t1 T1 ->
        typing v E D P t2 T2 ->
        C v E D P t2 T2 ->
        C v E D P (trm_prod t1 t2) (typ_prod T1 T2)) ->
    (forall (v : version) (E : tenv) 
            (D : env) (P : styp) (T1 T2 : typ) 
            (t1 : trm),
        valid_tenv v E ->
        valid_tenv_extension v E empty ->
        valid_env v E D ->
        valid_store_type E P ->
        typing v E D P t1 (typ_prod T1 T2) ->
        C v E D P t1 (typ_prod T1 T2) ->
        C v E D P (trm_fst t1) T1) ->
    (forall (v : version) (E : tenv) 
            (D : env) (P : styp) (T1 T2 : typ) 
            (t1 : trm),
        valid_tenv v E ->
        valid_tenv_extension v E empty ->
        valid_env v E D ->
        valid_store_type E P ->
        typing v E D P t1 (typ_prod T1 T2) ->
        C v E D P t1 (typ_prod T1 T2) ->
        C v E D P (trm_snd t1) T2) ->
    (forall (v : version) (E : tenv) 
            (D : env) (P : LibEnv.env typ) 
            (l : var) (T1 : typ),
        valid_tenv v E ->
        valid_tenv_extension v E empty ->
        valid_env v E D ->
        valid_store_type E P ->
        binds l T1 P -> C v E D P (trm_loc l) (typ_ref T1)) ->
    (forall (v : version) (E : tenv) 
            (D : env) (P : styp) (t1 : trm) 
            (T1 : typ),
        valid_tenv v E ->
        valid_tenv_extension v E empty ->
        valid_env v E D ->
        valid_store_type E P ->
        typing v E D P t1 T1 ->
        C v E D P t1 T1 ->
        C v E D P (trm_ref t1) (typ_ref T1)) ->
    (forall (v : version) (E : tenv) 
            (D : env) (P : styp) (t1 : trm) 
            (T1 : typ),
        valid_tenv v E ->
        valid_tenv_extension v E empty ->
        valid_env v E D ->
        valid_store_type E P ->
        typing v E D P t1 (typ_ref T1) ->
        C v E D P t1 (typ_ref T1) ->
        C v E D P (trm_get t1) T1) ->
    (forall (v : version) (E : tenv) 
            (D : env) (P : styp) (t1 t2 : trm) 
            (T1 : typ),
        valid_tenv v E ->
        valid_tenv_extension v E empty ->
        valid_env v E D ->
        valid_store_type E P ->
        typing v E D P t1 (typ_ref T1) ->
        C v E D P t1 (typ_ref T1) ->
        typing v E D P t2 T1 ->
        C v E D P t2 T1 ->
        C v E D P (trm_set t1 t2) typ_unit) ->
    forall (v : version) (E : tenv) 
           (D : env) (P : styp) (t : trm) 
           (T : typ),
      typing_with_envs v E D P t T ->
      C v E D P t T.
Proof.
  introv H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
  introv H11 H12 H13 H14 H15 H16 H17 H18 H19 H20.
  introv Htwe.
  destruct Htwe as [He Hd Hp Ht].
  induction Ht;
    [> apply H1 with (T1 := T1) | apply H2 with (T1 := T1)
     | apply H3 with (M := M) (Us := Us) | apply H4 with (L := L)
     | apply H5 with (T1 := T1) | apply H6 with (L := L) (M := M)
     | apply H7 with (L := L) (T1 := T1) | apply H8 with (T1 := T1)
     | apply H9 with (L := L) (T1 := T1) (T2 := T2) (T3 := T3)
     | apply H10 with (L := L) (T1 := T1) (T2 := T2)
     | apply H11 with (T1 := T1) | apply H12 with (L := L)
     | apply H13 | apply H14 | apply H15 with (T2 := T2)
     | apply H16 with (T1 := T1) | apply H17 | apply H18
     | apply H19 | apply H20 with (T1 := T1) ];
    clear H1 H2 H3 H4 H5 H6 H7 H8 H9 H10
          H11 H12 H13 H14 H15 H16 H17 H18 H19 H20;
    auto.
  - auto using valid_scheme_empty_of_kinding.
  - introv Hf.
    assert (valid_tenv v (E & Xs ~: M)) by
      eauto using valid_tenv_push_ranges.
    auto using valid_env_weakening_l,
      valid_store_type_weakening_l with wellformed.
  - eauto.
  - auto using valid_scheme_empty_of_kinding.
  - assert (valid_tenv_extension v E empty) by auto.
    auto using valid_scheme_empty_of_kinding with kinding.
  - assert (valid_tenv_extension v E empty) by auto.
    auto using valid_scheme_empty_of_kinding with kinding.
  - assert (valid_tenv_extension v E empty) by auto.
    auto using valid_scheme_empty_of_kinding with kinding.
  - auto 7 using valid_scheme_empty_of_kinding,
      kinding_concat_empty.
Qed.

Ltac induction_with_envs Ht He Hd Hp :=
  let Htwe := fresh "Htwe" in
  let Heq := fresh "Heq" in
  remember (typing_with_envs_c He Hd Hp Ht) as Htwe eqn:Heq;
  clear Ht He Hd Hp Heq;
  induction Htwe using typing_with_envs_ind.

(* ****************************************************** *)
(** ** Valid output *)

Lemma output_typing : forall v E D P t T,
    typing v E D P t T ->
    valid_tenv v E ->
    valid_env v E D ->
    valid_store_type E P ->
    kinding E empty T knd_type.
Proof.
  introv Ht He Hd Hp.
  induction_with_envs Ht He Hd Hp;
    auto with kinding fresh.
  - subst; apply kinding_instance with (v := v);
      eauto using valid_scheme_from_valid_env
        with wellformed.
  - constructor; autorewrite with rew_env_concat;
      auto with fresh.
  - constructor; autorewrite with rew_env_concat;
      eauto using kinding_from_valid_store_type.
Qed.    

(* ****************************************************** *)
(** ** Typing inversions *)

Ltac solve_inv_body H coercible T :=
  let Hc := fresh "Hc" in
  introv Hc; intros;
  inversion Hc; subst;
  eapply H;
    try solve [apply coercible; transitivity T; eauto];
    eauto.

Ltac solve_inv :=
  let Ht := fresh "Ht" in
  let He := fresh "He" in
  let Hd := fresh "Hd" in
  let Hp := fresh "Hp" in
  let Hq := fresh "Hq" in
  let t := fresh "t" in
  introv Ht He Hd Hp Hq;
  match type of Ht with
  | typing _ _ _ _ ?tm _ =>
    remember tm as t
  end;
  apply output_typing in Ht as Hk; auto;
  induction_with_envs Ht He Hd Hp; inversion Heqt; subst;
  [> match goal with
     | IH : _ = _ -> kinding _ empty ?Tt knd_type -> _ -> ?R
       |- ?R =>
       apply IH; auto with kinding;
       solve_inv_body Hq coercible_row Tt
     end
  |  match goal with
     | IH : _ = _ -> kinding _ empty ?Tt knd_type -> _ -> ?R
       |- ?R =>
       apply IH; auto with kinding;
       solve_inv_body Hq coercible_full Tt
     end
  |  eauto 6 using coercible_refl ].

Lemma typing_var_inv : forall v E D P x T (C : Prop),
    typing v E D P (trm_fvar x) T ->
    valid_tenv v E ->
    valid_env v E D ->
    valid_store_type E P ->
    (forall M T1 Us,
      coercible v E T1 T ->
      typing v E D P (trm_fvar x) T1 ->
      binds x M D -> 
      valid_instance v E Us M ->
      T1 = instance M Us ->
      C) ->
    C.
Proof. solve_inv. Qed.

Lemma typing_abs_inv : forall v E D P t1 T (C : Prop),
    typing v E D P (trm_abs t1) T ->
    valid_tenv v E ->
    valid_env v E D ->
    valid_store_type E P ->
    (forall L T1 T2,
        coercible v E (typ_arrow T1 T2) T ->
        typing v E D P (trm_abs t1) (typ_arrow T1 T2) ->
        kinding E empty T1 knd_type ->
        (forall x, x \notin (L \u dom D) -> 
          typing v E (D & x ~ sch_empty T1) P (t1 ^ x) T2) -> 
      C) ->
    C.
Proof. solve_inv. Qed.

Lemma typing_app_inv : forall v E D P t1 t2 T (C : Prop),
    typing v E D P (trm_app t1 t2) T ->
    valid_tenv v E ->
    valid_env v E D ->
    valid_store_type E P ->
    (forall T1 T2,
      coercible v E T2 T ->
      typing v E D P (trm_app t1 t2) T2 ->
      typing v E D P t1 (typ_arrow T1 T2) ->
      typing v E D P t2 T1 ->   
      C) ->
    C.
Proof. solve_inv. Qed.

Lemma typing_let_inv : forall v E D P t1 t2 T (C : Prop),
    typing v E D P (trm_let t1 t2) T ->
    valid_tenv v E ->
    valid_env v E D ->
    valid_store_type E P ->
    (forall L M T2,
      coercible v E T2 T ->
      typing v E D P (trm_let t1 t2) T2 ->
      value t1 ->
      valid_scheme_aux v L E M ->
      (forall Xs,
          fresh L (sch_arity M) Xs ->
          typing v
            (E & Xs ~: M) D P
            t1 (instance_vars M Xs)) ->
      (forall x,
          x \notin (L \u dom D) ->
          typing v E (D & x ~ M) P (t2 ^ x) T2) ->
      C) ->
    (forall L T1 T2,
        coercible v E T2 T ->
        typing v E D P (trm_let t1 t2) T2 ->
        typing v E D P t1 T1 ->
        (forall x,
            x \notin (L \u dom D) ->
            typing v E (D & x ~ sch_empty T1) P (t2 ^ x) T2) ->
        C) ->
    C.
Proof.
  introv Ht He Hd Hp Hq1 Hq2.
  remember (trm_let t1 t2) as t.
  apply output_typing in Ht as Hk; auto.
  induction_with_envs Ht He Hd Hp; inversion Heqt; subst.
  - apply IHHtwe; auto with kinding.
    + solve_inv_body Hq1 coercible_row T2.
    + solve_inv_body Hq2 coercible_row T1.
  - apply IHHtwe; auto with kinding.
    + solve_inv_body Hq1 coercible_full T2.
    + solve_inv_body Hq2 coercible_full T1.
  - eapply Hq1 with (T3 := T2) (L := L);
      try apply coercible_refl;
      try eapply typing_let_val with (L := L \u dom D);
      eauto using valid_scheme_aux_subset,
        subset_union_weak_l.
  - eapply Hq2 with (T3 := T2) (L := L);
      try apply coercible_refl;
      try eapply typing_let with (L := L \u dom D);
      eauto using valid_scheme_aux_subset,
        subset_union_weak_l.
Qed.

Lemma typing_constructor_inv : forall v E D P c t1 T (C : Prop),
    typing v E D P (trm_constructor c t1) T ->
    valid_tenv v E ->
    valid_env v E D ->
    valid_store_type E P ->
    (forall T1 T2,
      coercible v E (typ_variant T2) T ->
      typing v E D P (trm_constructor c t1) (typ_variant T2) ->
      typing v E D P t1 T1 ->
      subtype v E empty nil nil
        (typ_constructor c T1)
        (typ_proj CSet.universe (CSet.singleton c) T2)
        (knd_row (CSet.singleton c)) ->
      C) ->
    C.
Proof. solve_inv. Qed.

Lemma typing_match_inv :
  forall v E D P t1 c t2 t3 T (C : Prop),
    typing v E D P (trm_match t1 c t2 t3) T ->
    valid_tenv v E ->
    valid_env v E D ->
    valid_store_type E P ->
    (forall L T1 T2 T3 T4,
      coercible v E T4 T ->
      typing v E D P (trm_match t1 c t2 t3) T4 ->
      typing v E D P t1 (typ_variant T1) ->
      subtype v E empty nil nil
        (typ_proj CSet.universe (CSet.singleton c) T1)
        (typ_proj CSet.universe (CSet.singleton c) T2)
        (knd_row (CSet.singleton c)) ->
      subtype v E empty nil nil
        (typ_proj CSet.universe (CSet.cosingleton c) T1)
        (typ_proj CSet.universe (CSet.cosingleton c) T3)
        (knd_row (CSet.cosingleton c)) ->
      (forall x, x \notin L ->
         typing v E (D & x ~ (sch_empty (typ_variant T2))) P
                (t2 ^ x) T4) ->
      (forall y, y \notin L -> 
         typing v E (D & y ~ (sch_empty (typ_variant T3))) P
                (t3 ^ y) T4) ->
      C) ->
    C.
Proof. solve_inv. Qed.

Lemma typing_destruct_inv :
  forall v E D P t1 c t2 T (C : Prop),
    typing v E D P (trm_destruct t1 c t2) T ->
    valid_tenv v E ->
    valid_env v E D ->
    valid_store_type E P ->
    (forall L T1 T2 T3,
      coercible v E T3 T ->
      typing v E D P (trm_destruct t1 c t2) T3 ->
      typing v E D P t1 (typ_variant T1) ->
      subtype v E empty nil nil
        (typ_proj CSet.universe (CSet.singleton c) T1)
        (typ_constructor c T2)
        (knd_row (CSet.singleton c)) ->
      subtype v E empty nil nil
        (typ_proj CSet.universe (CSet.cosingleton c) T1)
        (typ_bot (knd_row (CSet.cosingleton c)))
        (knd_row (CSet.cosingleton c)) ->
      (forall x, x \notin L ->
         typing v E (D & x ~ (sch_empty T2)) P
                (t2 ^ x) T3) ->
      C) ->
    C.
Proof. solve_inv. Qed.

Lemma typing_absurd_inv :
  forall v E D P t1 T (C : Prop),
    typing v E D P (trm_absurd t1) T ->
    valid_tenv v E ->
    valid_env v E D ->
    valid_store_type E P ->
    (forall T1 T2,
      coercible v E T2 T ->
      typing v E D P (trm_absurd t1) T2 ->
      typing v E D P t1 (typ_variant T1) ->
      subtype v E empty nil nil
        T1 (typ_bot knd_row_all) knd_row_all ->
      kinding E empty T2 knd_type ->
      C) ->
    C.
Proof. solve_inv. Qed.

Lemma typing_fix_inv :
  forall v E D P t1 T (C : Prop),
    typing v E D P (trm_fix t1) T ->
    valid_tenv v E ->
    valid_env v E D ->
    valid_store_type E P ->
    (forall L T1 T2,
      coercible v E (typ_arrow T1 T2) T ->
      typing v E D P (trm_fix t1) (typ_arrow T1 T2) ->
      kinding E empty T1 knd_type ->
      kinding E empty T2 knd_type ->
      (forall x y,
          x \notin L -> y \notin (L \u \{x}) ->
          typing
            v E (D & x ~ sch_empty (typ_arrow T1 T2)
                 & y ~ sch_empty T1)
            P (t1 ^* (cons y (cons x nil))) T2) -> 
      C) ->
    C.
Proof. solve_inv. Qed.

Lemma typing_unit_inv :
  forall v E D P T (C : Prop),
    typing v E D P trm_unit T ->
    valid_tenv v E ->
    valid_env v E D ->
    valid_store_type E P ->
    (coercible v E typ_unit T ->
     typing v E D P trm_unit typ_unit ->
     C) ->
    C.
Proof. solve_inv. Qed.

Lemma typing_prod_inv :
  forall v E D P t1 t2 T (C : Prop),
    typing v E D P (trm_prod t1 t2) T ->
    valid_tenv v E ->
    valid_env v E D ->
    valid_store_type E P ->
    (forall T1 T2,
      coercible v E (typ_prod T1 T2) T ->
      typing v E D P (trm_prod t1 t2) (typ_prod T1 T2) ->
      typing v E D P t1 T1 ->
      typing v E D P t2 T2 ->
      C) ->
    C.
Proof. solve_inv. Qed.

Lemma typing_fst_inv :
  forall v E D P t1 T (C : Prop),
    typing v E D P (trm_fst t1) T ->
    valid_tenv v E ->
    valid_env v E D ->
    valid_store_type E P ->
    (forall T1 T2,
      coercible v E T1 T ->
      typing v E D P (trm_fst t1) T1 ->
      typing v E D P t1 (typ_prod T1 T2) ->
      C) ->
    C.
Proof. solve_inv. Qed.

Lemma typing_snd_inv :
  forall v E D P t1 T (C : Prop),
    typing v E D P (trm_snd t1) T ->
    valid_tenv v E ->
    valid_env v E D ->
    valid_store_type E P ->
    (forall T1 T2,
      coercible v E T2 T ->
      typing v E D P (trm_snd t1) T2 ->
      typing v E D P t1 (typ_prod T1 T2) ->
      C) ->
    C.
Proof. solve_inv. Qed.

Lemma typing_loc_inv :
  forall v E D P l T (C : Prop),
    typing v E D P (trm_loc l) T ->
    valid_tenv v E ->
    valid_env v E D ->
    valid_store_type E P ->
    (forall T1,
      coercible v E (typ_ref T1) T ->
      typing v E D P (trm_loc l) (typ_ref T1) ->
      binds l T1 P ->
      C) ->
    C.
Proof. solve_inv. Qed.

Lemma typing_ref_inv :
  forall v E D P t1 T (C : Prop),
    typing v E D P (trm_ref t1) T ->
    valid_tenv v E ->
    valid_env v E D ->
    valid_store_type E P ->
    (forall T1,
      coercible v E (typ_ref T1) T ->
      typing v E D P (trm_ref t1) (typ_ref T1) ->
      typing v E D P t1 T1 ->
      C) ->
    C.
Proof. solve_inv. Qed.

Lemma typing_get_inv :
  forall v E D P t1 T (C : Prop),
    typing v E D P (trm_get t1) T ->
    valid_tenv v E ->
    valid_env v E D ->
    valid_store_type E P ->
    (forall T1,
      coercible v E T1 T ->
      typing v E D P (trm_get t1) T1 ->
      typing v E D P t1 (typ_ref T1) ->
      C) ->
    C.
Proof. solve_inv. Qed.

Lemma typing_set_inv :
  forall v E D P t1 t2 T (C : Prop),
    typing v E D P (trm_set t1 t2) T ->
    valid_tenv v E ->
    valid_env v E D ->
    valid_store_type E P ->
    (forall T1,
      coercible v E typ_unit T ->
      typing v E D P (trm_set t1 t2) typ_unit ->
      typing v E D P t1 (typ_ref T1) ->
      typing v E D P t2 T1 ->
      C) ->
    C.
Proof. solve_inv. Qed.

Ltac invert_typing Ht He Hd Hp :=
  match type of Ht with
  | typing _ _ _ _ (trm_fvar _) _ =>
    apply (typing_var_inv Ht He Hd Hp); intros
  | typing _ _ _ _ (trm_abs _) _ =>
    apply (typing_abs_inv Ht He Hd Hp); intros
  | typing _ _ _ _ (trm_app _ _) _ =>
    apply (typing_app_inv Ht He Hd Hp); intros
  | typing _ _ _ _ (trm_let _ _) _ =>
    apply (typing_let_inv Ht He Hd Hp); intros
  | typing _ _ _ _ (trm_constructor _ _) _ =>
    apply (typing_constructor_inv Ht He Hd Hp); intros
  | typing _ _ _ _ (trm_match _ _ _ _) _ =>
    apply (typing_match_inv Ht He Hd Hp); intros
  | typing _ _ _ _ (trm_destruct _ _ _) _ =>
    apply (typing_destruct_inv Ht He Hd Hp); intros
  | typing _ _ _ _ (trm_absurd _) _ =>
    apply (typing_absurd_inv Ht He Hd Hp); intros
  | typing _ _ _ _ (trm_fix _) _ =>
    apply (typing_fix_inv Ht He Hd Hp); intros
  | typing _ _ _ _ trm_unit _ =>
    apply (typing_unit_inv Ht He Hd Hp); intros
  | typing _ _ _ _ (trm_prod _ _) _ =>
    apply (typing_prod_inv Ht He Hd Hp); intros
  | typing _ _ _ _ (trm_fst _) _ =>
    apply (typing_fst_inv Ht He Hd Hp); intros
  | typing _ _ _ _ (trm_snd _) _ =>
    apply (typing_snd_inv Ht He Hd Hp); intros
  | typing _ _ _ _ (trm_loc _) _ =>
    apply (typing_loc_inv Ht He Hd Hp); intros
  | typing _ _ _ _ (trm_ref _) _ =>
    apply (typing_ref_inv Ht He Hd Hp); intros
  | typing _ _ _ _ (trm_get _) _ =>
    apply (typing_get_inv Ht He Hd Hp); intros
  | typing _ _ _ _ (trm_set _ _) _ =>
    apply (typing_set_inv Ht He Hd Hp); intros
  end.

(* ****************************************************** *)
(** ** Typing empty scheme *)

Lemma typing_scheme_empty : forall v E D P t T,
    typing v E D P t T <-> typing_scheme v E D P t (sch_empty T).
Proof.
  split; introv Ht.
  - apply typing_scheme_c with (L := \{}).
    intros Xs Hf.
    apply fresh_zero in Hf; subst.
    rewrite instance_vars_empty_nil.
    unfold sch_empty, bind_sch_ranges; simpl.
    apply valid_tenv_extension_and_typing_c;
      autorewrite with rew_env_concat; auto.   
  - remember (sch_empty T) as M.
    destruct Ht; subst.
    assert
      (valid_tenv_extension_and_typing v E
        (nil ~: sch_empty T) D P t (instance_vars (sch_empty T) nil))
      as Hv by auto.
    rewrite instance_vars_empty_nil in Hv.
    unfold sch_empty, bind_sch_ranges in Hv; simpl in Hv.
    inversion Hv; subst.
    autorewrite with rew_env_concat in *.
    auto.
Qed.

Lemma typing_scheme_c' : forall L v E M D P t,
    valid_scheme_aux v L E M ->
    (forall Xs : list var,
         fresh L (sch_arity M) Xs ->
         typing v (E & Xs ~: M) D P t
           (instance_vars M Xs)) ->
    typing_scheme v E D P t M.
Proof.
  introv Hs Ht.
  apply typing_scheme_c with (L := L).
  introv Hf.
  destruct Hs as [? ? ? ? Hs].
  specialize (Hs Xs Hf).
  specialize (Ht Xs Hf).
  inversion Hs; subst.
  auto.
Qed.  

Lemma typing_trm_subst_empty : forall v E D1 D2 x P s t T1 T2,
    typing v E (D1 & x ~ sch_empty T2 & D2) P t T1 ->
    type_environment E ->
    environment (D1 & x ~ sch_empty T2 & D2) ->
    store_type P ->
    typing v E (D1 & D2) P s T2 ->
    typing v E (D1 & D2) P (trm_subst (x::nil) (s::nil) t) T1.
Proof.
  introv Ht1 He Hd Hp Ht2.
  apply typing_trm_subst with (Ms := cons (sch_empty T2) nil);
    simpl; autorewrite with rew_env_concat; auto.
  apply typing_schemes_cons; auto.
  rewrite <- typing_scheme_empty; auto.
Qed.

Lemma typing_trm_subst_empty_l : forall v E D x P s t T1 T2,
    typing v E (D & x ~ sch_empty T2) P t T1 ->
    type_environment E ->
    environment (D & x ~ sch_empty T2) ->
    store_type P ->
    typing v E D P s T2 ->
    typing v E D P (trm_subst (x::nil) (s::nil) t) T1.
Proof.
  introv Ht He Hd Hp Hts.
  rewrite <- concat_empty_r with (E := D).
  rewrite <- concat_empty_r
    with (E := D & x ~ sch_empty T2) in Ht, Hd.
  rewrite <- concat_empty_r with (E := D) in Hts.
  eauto using typing_trm_subst_empty.
Qed.

Lemma typing_trm_subst_empty2 : forall v E D1 D2 x y P s r t T1 T2 T3,
    typing v E
      (D1 & x ~ sch_empty T2 & y ~ sch_empty T3 & D2) P t T1 ->
    type_environment E ->
    environment (D1 & x ~ sch_empty T2 & y ~ sch_empty T3 & D2) ->
    store_type P ->
    typing v E (D1 & D2) P s T2 ->
    typing v E (D1 & D2) P r T3 ->
    typing v E (D1 & D2) P
      (trm_subst (cons y (x::nil)) (cons r (s::nil)) t) T1.
Proof.
  introv Ht1 He Hd Hp Ht2 Ht3.
  apply typing_trm_subst
    with (Ms := cons (sch_empty T3) (cons (sch_empty T2) nil));
    simpl; autorewrite with rew_env_concat; auto.
  apply typing_schemes_cons.
  - rewrite <- typing_scheme_empty; auto.
  - apply typing_schemes_cons; auto.
    rewrite <- typing_scheme_empty; auto.
Qed.

Lemma typing_trm_subst_empty2_l : forall v E D x y P s r t T1 T2 T3,
    typing v E (D & x ~ sch_empty T2 & y ~ sch_empty T3) P t T1 ->
    type_environment E ->
    environment (D & x ~ sch_empty T2 & y ~ sch_empty T3) ->
    store_type P ->
    typing v E D P s T2 ->
    typing v E D P r T3 ->
    typing v E D P
      (trm_subst (cons y (x::nil)) (cons r (s::nil)) t) T1.
Proof.
  introv Ht1 He Hd Hp Ht2 Ht3.
  rewrite <- concat_empty_r with (E := D).
  rewrite <- concat_empty_r
    with (E := D & x ~ sch_empty T2 & y ~ sch_empty T3) in Ht1, Hd.
  rewrite <- concat_empty_r with (E := D) in Ht2, Ht3.
  eauto using typing_trm_subst_empty2.
Qed.

(* ****************************************************** *)
(** ** Extending the store *)

Lemma typing_extend_store_type : forall v E D P P' t T,
    typing v E D P t T ->
    type_environment E ->
    extends P P' ->
    valid_store_type E P' ->
    typing v E D P' t T.
Proof.
  introv Ht He Hex Hs.
  induction Ht; eauto.
  - apply typing_let_val with (L := L \u dom E) (M := M);
      eauto using valid_scheme_aux_subset, subset_union_weak_l.
    introv Hf.
    assert (type_environment (E & Xs ~: M))
      by (apply type_environment_push_ranges with L;
            auto with wellformed).
    auto using valid_store_type_weakening_l.
Qed.

Lemma typing_store_ref : forall v E D V P l t T,
    typing_store v E D V P ->
    type_environment E ->
    l # P ->
    valid_store_type E P ->
    kinding E empty T knd_type ->
    typing v E D P t T ->
    typing_store v E D (V & l ~ t) (P & l ~ T).
Proof.
  introv Hs Hn Hv He Hk Ht.
  destruct Hs.
  apply typing_store_c.
  intro l'.
  case_if_eq l l'.
  - eauto using typing_store_loc_bound,
      typing_extend_store_type.   
  - assert (typing_store_loc l' v E D V P) as Hsl
      by auto.
    destruct Hsl.
    + auto using typing_store_loc_fresh.
    + eapply typing_store_loc_bound;
        eauto using typing_extend_store_type.
Qed.

Lemma typing_store_set : forall v E D V P l t T,
    typing_store v E D V P ->
    type_environment E ->
    binds l T P ->
    valid_store_type E P ->
    kinding E empty T knd_type ->
    typing v E D P t T ->
    typing_store v E D (V & l ~ t) P.
Proof.
  introv Hs Hb Hv He Ht Hk.
  destruct Hs.
  apply typing_store_c.
  intro l'.
  case_if_eq l l'.
  - eauto using typing_store_loc_bound,
      typing_extend_store_type.   
  - assert (typing_store_loc l' v E D V P) as Hsl
      by auto.
    destruct Hsl.
    + auto using typing_store_loc_fresh.
    + eapply typing_store_loc_bound;
        eauto using typing_extend_store_type.
Qed.

(* *************************************************************** *)
(** Value inversions *)

Lemma invert_value_variant :
  forall v E D P t T1 (C : Prop),
    value t ->
    typing v E D P t (typ_variant T1) ->
    valid_tenv v E ->
    valid_env v E D ->
    valid_store_type E P ->
    (forall c t1, t = trm_constructor c t1 -> value t1 -> C) ->
    C.
Proof.
  introv Hv Ht He Hd Hp Hq.
  inversion Hv; subst; invert_typing Ht He Hd Hp.
  - eauto.
  - exfalso; eauto using invert_coercible_arrow_variant.
  - exfalso; eauto using invert_coercible_arrow_variant.
  - exfalso; eauto using invert_coercible_unit_variant.
  - exfalso; eauto using invert_coercible_prod_variant.
  - exfalso; eauto using invert_coercible_ref_variant.
Qed.

Lemma invert_value_arrow :
  forall v E D P t T1 T2 (C : Prop),
    value t ->
    typing v E D P t (typ_arrow T1 T2) ->
    valid_tenv v E ->
    valid_env v E D ->
    valid_store_type E P ->
    (forall t1, t = trm_abs t1 -> C) ->
    (forall t1, t = trm_fix t1 -> C) ->
    C.
Proof.
  introv Hv Ht He Hd Hp Hq1 Hq2.
  inversion Hv; subst; invert_typing Ht He Hd Hp.
  - exfalso; eauto using invert_coercible_variant_arrow.
  - eauto.
  - eauto.
  - exfalso; eauto using invert_coercible_unit_arrow.
  - exfalso; eauto using invert_coercible_prod_arrow.
  - exfalso; eauto using invert_coercible_ref_arrow.
Qed.

Lemma invert_value_unit :
  forall v E D P t (C : Prop),
    value t ->
    typing v E D P t typ_unit ->
    valid_tenv v E ->
    valid_env v E D ->
    valid_store_type E P ->
    (t = trm_unit -> C) ->
    C.
Proof.
  introv Hv Ht He Hd Hp Hq.
  inversion Hv; subst; invert_typing Ht He Hd Hp.
  - exfalso; eauto using invert_coercible_variant_unit.
  - exfalso; eauto using invert_coercible_arrow_unit.
  - exfalso; eauto using invert_coercible_arrow_unit.
  - eauto.
  - exfalso; eauto using invert_coercible_prod_unit.
  - exfalso; eauto using invert_coercible_ref_unit.
Qed.

Lemma invert_value_prod :
  forall v E D P t T1 T2 (C : Prop),
    value t ->
    typing v E D P t (typ_prod T1 T2) ->
    valid_tenv v E ->
    valid_env v E D ->
    valid_store_type E P ->
    (forall t1 t2,
        t = trm_prod t1 t2 -> value t1 -> value t2 -> C) ->
    C.
Proof.
  introv Hv Ht He Hd Hp Hq.
  inversion Hv; subst; invert_typing Ht He Hd Hp.
  - exfalso; eauto using invert_coercible_variant_prod.
  - exfalso; eauto using invert_coercible_arrow_prod.
  - exfalso; eauto using invert_coercible_arrow_prod.
  - exfalso; eauto using invert_coercible_unit_prod.
  - eauto.
  - exfalso; eauto using invert_coercible_ref_prod.
Qed.

Lemma invert_value_ref :
  forall v E D P t T1 (C : Prop),
    value t ->
    typing v E D P t (typ_ref T1) ->
    valid_tenv v E ->
    valid_env v E D ->
    valid_store_type E P ->
    (forall l, t = trm_loc l -> C) ->
    C.
Proof.
  introv Hv Ht He Hd Hp Hq.
  inversion Hv; subst; invert_typing Ht He Hd Hp.
  - exfalso; eauto using invert_coercible_variant_ref.
  - exfalso; eauto using invert_coercible_arrow_ref.
  - exfalso; eauto using invert_coercible_arrow_ref.
  - exfalso; eauto using invert_coercible_unit_ref.
  - exfalso; eauto using invert_coercible_prod_ref.
  - eauto.
Qed.
