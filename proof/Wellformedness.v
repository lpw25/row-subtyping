(************************************************
 *          Row Subtyping - Well-formedness     *
 *                 Leo White                    *
 ************************************************)

(* Well-formedness of judgement subjects and outputs *)

Set Implicit Arguments.
Require Import List LibLN Cofinite Disjoint Utilities
        Definitions Opening FreeVars Environments Subst.

(* ****************************************************** *)

(* Subjects *)

Lemma wellformed_kinding : forall E1 E2 T K,
    kinding E1 E2 T K -> type T.
Proof.
  introv Hk.
  induction Hk; auto.
Qed.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : kinding _ _ T _ |- _ =>
      apply (wellformed_kinding H)
  end : wellformed.

Lemma wellformed_kindings : forall E1 E2 Ts Ks,
    kindings E1 E2 Ts Ks -> types Ts.
Proof.
  introv Hks.
  induction Hks; auto with wellformed.
Qed.

Hint Extern 1 (types ?Ts) =>
  match goal with
  | H : kindings _ _ Ts _ |- _ =>
      apply (wellformed_kindings H)
  end : wellformed.

Lemma kindings_length : forall E1 E2 Ts Ks,
  kindings E1 E2 Ts Ks ->
  length Ts = length Ks.
Proof.
  introv Hks.
  induction Hks; simpl; auto.
Qed.

Lemma wellformed_type_equal_both : forall v E1 E2 T1 T2 K,
    type_equal v E1 E2 T1 T2 K ->
    type_environment E1 ->
    type_environment_extension E1 E2 ->
    type T1 /\ type T2.
Proof.
  introv Hte He1 He2.
  induction Hte;
    repeat
      match goal with
      | [ IH : type_environment E1 ->
               type_environment_extension E1 E2 -> _ |- _ ] =>
        specialize (IH He1 He2)
      end;
    repeat
      match goal with
      | [ IH : type_environment (E1 & E2) ->
        type_environment_extension (E1 & E2) empty -> _ |- _ ] =>
        assert (type_environment (E1 & E2)) as He3 by
          auto using type_environment_extend;
        assert (type_environment_extension (E1 & E2) empty)
          as He4 by auto;
        specialize (IH He3 He4)
      end;
    intuition eauto
      using type_from_tenv_lower, type_from_tenv_upper
      with wellformed.
Qed.

Lemma wellformed_type_equal_1 : forall v E1 E2 T1 T2 K,
    type_equal v E1 E2 T1 T2 K ->
    type_environment E1 ->
    type_environment_extension E1 E2 ->
    type T1.
Proof.
  introv Hte He1 He2.
  destruct (wellformed_type_equal_both Hte He1 He2).
  assumption.
Qed.

Lemma wellformed_type_equal_2 : forall v E1 E2 T1 T2 K,
    type_equal v E1 E2 T1 T2 K ->
    type_environment E1 ->
    type_environment_extension E1 E2 ->
    type T2.
Proof.
  introv Hte He1 He2.
  destruct (wellformed_type_equal_both Hte He1 He2).
  assumption.
Qed.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : type_equal _ ?E1 ?E2 T _ _,
    He1 : type_environment ?E1,
    He2 : type_environment_extension ?E1 ?E2 |- _ =>
      apply (wellformed_type_equal_1 H He1 He2)
  | H : type_equal _ ?E1 ?E2 _ T _,
    He1 : type_environment ?E1,
    He2 : type_environment_extension ?E1 ?E2 |- _ =>
      apply (wellformed_type_equal_2 H He1 He2)
  end : wellformed.

Lemma wellformed_subtype_1 : forall v E1 E2 T1 T2 K,
    subtype v E1 E2 T1 T2 K ->
    type_environment E1 ->
    type_environment_extension E1 E2 ->
    type T1.
Proof.
  introv Hs He1 He2.
  unfold subtype in Hs.
  auto with wellformed.
Qed.

Lemma wellformed_subtype_2 : forall v E1 E2 T1 T2 K,
    subtype v E1 E2 T1 T2 K ->
    type_environment E1 ->
    type_environment_extension E1 E2 ->
    type T2.
Proof.
  introv Hs He1 He2.
  unfold subtype in Hs.
  assert (type (typ_meet T1 T2)) as Ht
    by auto with wellformed.
  inversion Ht; auto.
Qed.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : subtype _ ?E1 ?E2 T _ _,
    He1 : type_environment ?E1,
    He2 : type_environment_extension ?E1 ?E2 |- _ =>
      apply (wellformed_subtype_1 H He1 He2)
  | H : subtype _ ?E1 ?E2 _ T _,
    He1 : type_environment ?E1,
    He2 : type_environment_extension ?E1 ?E2 |- _ =>
      apply (wellformed_subtype_2 H He1 He2)
  end : wellformed.

Lemma wellformed_valid_range: forall v E1 E2 R,
    valid_range v E1 E2 R -> range R.
Proof.
  introv Hr.
  induction Hr; auto with wellformed.
Qed.

Hint Extern 1 (range ?R) =>
  match goal with
  | H : valid_range _ _ _ R |- _ =>
      apply (wellformed_valid_range H)
  end : wellformed.

Lemma wellformed_valid_tenv_rec: forall v E1 E2 E3,
    valid_tenv_rec v E1 E2 E3 -> type_environment_extension E1 E2.
Proof.
  introv He.
  induction He; auto with wellformed.
Qed.

Hint Extern 1 (type_environment_extension ?E1 ?E2) =>
  match goal with
  | H : valid_tenv_rec _ E1 E2 _ |- _ =>
      apply (wellformed_valid_tenv_rec H)
  end : wellformed.

Lemma wellformed_valid_tenv_extension: forall v E1 E2,
    valid_tenv_extension v E1 E2 -> type_environment_extension E1 E2.
Proof.
  introv He.
  unfold valid_tenv_extension in He.
  auto with wellformed.
Qed.

Hint Extern 1 (type_environment_extension ?E1 ?E2) =>
  match goal with
  | H : valid_tenv_extension _ E1 E2 |- _ =>
      apply (wellformed_valid_tenv_extension H)
  end : wellformed.

Lemma wellformed_valid_tenv: forall v E,
    valid_tenv v E -> type_environment E.
Proof.
  introv He.
  unfold valid_tenv in He.
  unfold type_environment.
  auto with wellformed.
Qed.

Hint Extern 1 (type_environment ?E) =>
  match goal with
  | H : valid_tenv _ E |- _ =>
      apply (wellformed_valid_tenv H)
  end : wellformed.

Hint Extern 1 (type_environment (?E1 & ?E2)) =>
  match goal with
  | H1 : valid_tenv _ E1, H2 : valid_tenv_extension _ E1 E2 |- _ =>
      apply
        (type_environment_extend
           (wellformed_valid_tenv H1)
           (wellformed_valid_tenv_extension H2))
  end : wellformed.

Lemma wellformed_valid_tenv_extension_and_type_1 :
  forall v E1 E2 T,
  valid_tenv_extension_and_type v E1 E2 T ->
  type_environment_extension E1 E2.
Proof.
  introv He.
  destruct He.
  auto with wellformed.
Qed.

Hint Extern 1 (type_environment_extension ?E1 ?E2) =>
  match goal with
  | H : valid_tenv_extension_and_type _ E1 E2 _ |- _ =>
      apply (wellformed_valid_tenv_extension_and_type_1 H)
  end : wellformed.

Lemma wellformed_valid_tenv_extension_and_type_2 :
  forall v E1 E2 T,
  valid_tenv_extension_and_type v E1 E2 T ->
  type T.
Proof.
  introv He.
  destruct He.
  auto with wellformed.
Qed.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : valid_tenv_extension_and_type _ _ _ T |- _ =>
      apply (wellformed_valid_tenv_extension_and_type_2 H)
  end : wellformed.

Lemma wellformed_valid_scheme_aux: forall v L E M,
    valid_scheme_aux v L E M -> scheme_aux L M.
Proof.
  introv Hs.
  destruct Hs as [v L E M Hs].
  apply scheme_aux_c.
  introv Hf.
  specialize (Hs Xs Hf).
  apply ranges_and_type_c; auto with wellformed.
  assert (type_environment_extension E (Xs ~: M)) as He
    by auto with wellformed.
  destruct M; unfold bind_sch_ranges in *; simpl in *.
  apply type_environment_singles_inv_ranges
    with (E := E) (Xs := Xs); auto.
  rewrite rng_open_vars_list_length.
  fresh_length Hf as Hl.
  auto.
Qed.

Hint Extern 1 (scheme_aux ?L ?M) =>
  match goal with
  | H : valid_scheme_aux _ L _ M |- _ =>
      apply (wellformed_valid_scheme_aux H)
  end : wellformed.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H : valid_scheme_aux _ _ _ M |- _ =>
      apply (scheme_c (wellformed_valid_scheme_aux H))
  end : wellformed.

Lemma wellformed_valid_scheme: forall v E M,
    valid_scheme v E M -> scheme M.
Proof.
  introv Hs.
  destruct Hs as [L v E M Hs].
  apply scheme_c with L.
  auto with wellformed.
Qed.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H : valid_scheme _ _ M |- _ =>
      apply (wellformed_valid_scheme H)
  end : wellformed.

Lemma wellformed_valid_schemes: forall v E Ms,
    valid_schemes v E Ms -> schemes Ms.
Proof.
  introv Hs.
  induction Hs; auto with wellformed.
Qed.

Hint Extern 1 (schemes ?Ms) =>
  match goal with
  | H : valid_schemes _ _ Ms |- _ =>
      apply (wellformed_valid_schemes H)
  end : wellformed.

Lemma wellformed_ranging: forall v E1 E2 T R,
    ranging v E1 E2 T R -> type T.
Proof.
  introv Hr.
  induction Hr; auto with wellformed.
Qed.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : ranging _ _ _ T _ |- _ =>
      apply (wellformed_ranging H)
  end : wellformed.

Lemma wellformed_rangings: forall v E1 E2 Ts Rs,
    rangings v E1 E2 Ts Rs -> types Ts.
Proof.
  introv Hr.
  induction Hr; auto with wellformed.
Qed.

Lemma rangings_length: forall v E1 E2 Ts Rs,
    rangings v E1 E2 Ts Rs -> length Ts = length Rs.
Proof.
  introv Hr.
  induction Hr; simpl; auto.  
Qed.

Hint Extern 1 (types ?Ts) =>
  match goal with
  | H : rangings _ _ _ Ts _ |- _ =>
      apply (wellformed_rangings H)
  end : wellformed.

Lemma wellformed_valid_instance: forall v E Ts M,
    valid_instance v E Ts M -> types Ts.
Proof.
  introv Hi.
  destruct Hi; auto with wellformed.
Qed.

Lemma valid_instance_length: forall v E Ts M,
    valid_instance v E Ts M ->
    length Ts = sch_arity M.
Proof.
  introv Hi.
  destruct Hi; subst.
  destruct M; simpl in *.
  rewrite <- rng_open_list_length with (Us := Ts).
  eauto using rangings_length.
Qed.

Hint Extern 1 (types ?Ts) =>
  match goal with
  | H : valid_instance _ ?E Ts _ |- _ =>
      apply (wellformed_valid_instance H)
  end : wellformed.

Lemma wellformed_valid_env: forall v E D,
    valid_env v E D -> environment D.
Proof.
  introv He.
  induction He; auto with wellformed.
Qed.

Hint Extern 1 (environment ?D) =>
  match goal with
  | H : valid_env _ _ D |- _ =>
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

Lemma wellformed_typing: forall v E D P t T,
    typing v E D P t T -> term t.
Proof.
  introv Ht.
  induction Ht; eauto with wellformed.
Qed.

Hint Extern 1 (term ?t) =>
  match goal with
  | H : typing _ _ _ _ t _ |- _ =>
      apply (wellformed_typing H)
  end : wellformed.

Lemma wellformed_valid_tenv_extension_and_typing_1:
  forall v E1 E2 D P t T,
    valid_tenv_extension_and_typing v E1 E2 D P t T ->
    type_environment_extension E1 E2.
Proof.
  introv Hv.
  destruct Hv; auto with wellformed.
Qed.

Hint Extern 1 (type_environment_extension ?E1 ?E2) =>
  match goal with
  | H : valid_tenv_extension_and_typing _ E1 E2 _ _ _ _ |- _ =>
      apply (wellformed_valid_tenv_extension_and_typing_1 H)
  end : wellformed.

Lemma wellformed_valid_tenv_extension_and_typing_2:
  forall v E1 E2 D P t T,
    valid_tenv_extension_and_typing v E1 E2 D P t T ->
    term t.
Proof.
  introv Hv.
  destruct Hv; auto with wellformed.
Qed.

Hint Extern 1 (term ?t) =>
  match goal with
  | H : valid_tenv_extension_and_typing _ _ _ _ _ t _ |- _ =>
      apply (wellformed_valid_tenv_extension_and_typing_2 H)
  end : wellformed.

Lemma wellformed_typing_scheme: forall v E D P t M,
    typing_scheme v E D P t M -> term t.
Proof.
  introv Hs.
  induction Hs; spec_fresh; auto with wellformed.
Qed.

Hint Extern 1 (term ?t) =>
  match goal with
  | H : typing_scheme _ _ _ _ t _ |- _ =>
      apply (wellformed_typing_scheme H)
  end : wellformed.

Lemma wellformed_typing_schemes: forall v E D P ts Ms,
    typing_schemes v E D P ts Ms -> terms ts.
Proof.
  introv Hs.
  induction Hs; auto with wellformed.
Qed.

Hint Extern 1 (terms ?ts) =>
  match goal with
  | H : typing_schemes _ _ _ _ ts _ |- _ =>
      apply (wellformed_typing_schemes H)
  end : wellformed.

Lemma typing_schemes_length : forall v E D P ts Ms,
  typing_schemes v E D P ts Ms ->
  length ts = length Ms.
Proof.
  introv Hss.
  induction Hss; simpl; auto.
Qed.

(* Outputs *)

Lemma wellformed_output_kinding : forall E1 E2 T K,
  kinding E1 E2 T K ->
  type_environment E1 ->
  type_environment_extension E1 E2 ->
  kind K.
Proof.
  introv Hk He1 He2.
  induction Hk; subst; auto with csetdec.
  - eauto using kind_from_tenv. 
  - specialize (IHHk1 He1 He2).
    specialize (IHHk2 He1 He2).
    inversion IHHk1; inversion IHHk2; subst.
    auto with csetdec.
Qed.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : kinding ?E1 ?E2 _ K,
    He1 : type_environment ?E1,
    He2 : type_environment_extension ?E1 ?E2 |- _ =>
      apply (wellformed_output_kinding H He1 He2)
  | H : kinding ?E1 ?E2 _ K,
    He1 : valid_tenv _ ?E1,
    He2 : valid_tenv_extension _ ?E1 ?E2 |- _ =>
      apply (wellformed_output_kinding H
               (wellformed_valid_tenv He1)
               (wellformed_valid_tenv_extension He2))
  | H : kinding (?E1 & ?E2) empty _ K,
    He1 : valid_tenv _ ?E1,
    He2 : valid_tenv_extension _ ?E1 ?E2 |- _ =>
      apply (wellformed_output_kinding H
               (type_environment_extend
                  (wellformed_valid_tenv He1)
                  (wellformed_valid_tenv_extension He2))
               (@type_environment_extension_empty (E1 & E2)))
  end : wellformed.

Lemma wellformed_output_kindings : forall E1 E2 Ts Ks,
  kindings E1 E2 Ts Ks ->
  type_environment E1 ->
  type_environment_extension E1 E2 ->
  kinds Ks.
Proof.
  introv Hk He.
  induction Hk; eauto using wellformed_output_kinding.
Qed.

Hint Extern 1 (kinds ?Ks) =>
  match goal with
  | H : kindings ?E1 ?E2 _ Ks,
    He1 : type_environment ?E1,
    He2 : type_environment_extension ?E1 ?E2 |- _ =>
      apply (wellformed_output_kindings H He1 He2)
  | H : kindings ?E1 ?E2 _ Ks,
    He1 : valid_tenv _ ?E1,
    He2 : valid_tenv_extension _ ?E1 ?E2 |- _ =>
      apply (wellformed_output_kindings H
               (wellformed_valid_tenv He1)
               (wellformed_valid_tenv_extension He2))
  | H : kindings (?E1 & ?E2) empty _ Ks,
    He1 : valid_tenv _ ?E1,
    He2 : valid_tenv_extension _ ?E1 ?E2 |- _ =>
      apply (wellformed_output_kindings H
               (type_environment_extend
                  (wellformed_valid_tenv He1)
                  (wellformed_valid_tenv_extension He2))
               (@type_environment_extension_empty (E1 & E2)))
  end : wellformed.

Lemma wellformed_output_type_equal : forall v E1 E2 T1 T2 K,
  type_equal v E1 E2 T1 T2 K ->
  type_environment E1 ->
  type_environment_extension E1 E2 ->
  kind K.
Proof.
  introv Hte He1 He2.
  induction Hte; auto with wellformed.
  - eauto using kind_from_tenv.
  - eauto using kind_from_tenv.
  - auto with csetdec.
  - assert (kind (knd_row cs1)) as Hk1 by auto.
    assert (kind (knd_row cs2)) as Hk2 by auto.
    inversion Hk1; inversion Hk2; subst.
    auto with csetdec.
Qed.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : type_equal _ ?E1 ?E2 _ _ K,
    He1 : type_environment ?E1,
    He2 : type_environment_extension ?E1 ?E2 |- _ =>
      apply (wellformed_output_type_equal H He1 He2)
  | H : type_equal _ ?E1 ?E2 _ _ K,
    He1 : valid_tenv _ ?E1,
    He2 : valid_tenv_extension _ ?E1 ?E2 |- _ =>
      apply (wellformed_output_type_equal H
               (wellformed_valid_tenv He1)
               (wellformed_valid_tenv_extension He2))
  | H : type_equal _ (?E1 & ?E2) empty _ _ K,
    He1 : valid_tenv _ ?E1,
    He2 : valid_tenv_extension _ ?E1 ?E2 |- _ =>
      apply (wellformed_output_type_equal H
               (type_environment_extend
                  (wellformed_valid_tenv He1)
                  (wellformed_valid_tenv_extension He2))
               (@type_environment_extension_empty (E1 & E2)))
  end : wellformed.

Lemma wellformed_output_subtype : forall v E1 E2 T1 T2 K,
  subtype v E1 E2 T1 T2 K ->
  type_environment E1 ->
  type_environment_extension E1 E2 ->
  kind K.
Proof.
  introv Hs He1 He2.
  unfold subtype in Hs.
  auto with wellformed.
Qed.

Hint Extern 1 (kind ?K) =>
  match goal with
  | H : subtype _ ?E1 ?E2 _ _ K,
    He1 : type_environment ?E1,
    He2 : type_environment_extension ?E1 ?E2 |- _ =>
      apply (wellformed_output_subtype H He1 He2)
  | H : subtype _ ?E1 ?E2 _ _ K,
    He1 : valid_tenv _ ?E1,
    He2 : valid_tenv_extension _ ?E1 ?E2 |- _ =>
      apply (wellformed_output_subtype H
               (wellformed_valid_tenv He1)
               (wellformed_valid_tenv_extension He2))
  | H : subtype _ (?E1 & ?E2) empty _ _ K,
    He1 : valid_tenv _ ?E1,
    He2 : valid_tenv_extension _ ?E1 ?E2 |- _ =>
      apply (wellformed_output_subtype H
               (type_environment_extend
                  (wellformed_valid_tenv He1)
                  (wellformed_valid_tenv_extension He2))
               (@type_environment_extension_empty (E1 & E2)))
  end : wellformed.

Lemma wellformed_output_typing : forall v E D P t T,
  typing v E D P t T ->
  type_environment E ->
  environment D ->
  store_type P ->
  type T.
Proof.
  introv Ht He Hd Hp.
  assert (type_environment_extension E empty) by auto.
  induction Ht; auto with wellformed.
  - subst.
    apply scheme_instance_type;
      eauto using scheme_from_env, valid_instance_length
        with wellformed.
  - pick_fresh x; assert (x \notin L) by auto.
    eauto with wellformed.
  - assert (type (typ_arrow T1 T2)) as Ht by auto.
    inversion Ht; auto.
  - pick_fresh x; assert (x \notin L) by auto.
    eauto with wellformed.
  - pick_fresh x; assert (x \notin L) by auto.
    eauto with wellformed.
  - assert
      (type (typ_proj CSet.universe (CSet.singleton c) T2))
      as Ht2 by auto with wellformed.
    inversion Ht2; auto.
  - assert
      (type (typ_proj CSet.universe (CSet.singleton c) T2))
      as Ht2 by auto with wellformed.
    inversion Ht2; subst.
    pick_fresh x; assert (x \notin L) by auto.
    eauto with wellformed.
  - assert (type (typ_constructor c T2))
      as Ht2 by auto with wellformed.
    inversion Ht2; subst.
    pick_fresh x; assert (x \notin L) by auto.
    eauto with wellformed.
  - assert (type (typ_prod T1 T2)) as Ht2 by auto.
    inversion Ht2; auto.
  - assert (type (typ_prod T1 T2)) as Ht2 by auto.
    inversion Ht2; auto.
  - eauto using type_from_store_type.
  - assert (type (typ_ref T1)) as Ht2 by auto.
    inversion Ht2; auto.
Qed.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : typing _ ?E ?D ?P _ T,
    He : type_environment ?E,
    Hd : environment ?D,
    Hp : store_type ?P |- _ =>
      apply (wellformed_output_typing H He Hd Hp)
  | H : typing _ ?E ?D ?P _ T,
    He : valid_tenv _ ?E,
    Hd : valid_env _ _ ?D,
    Hp : valid_store_type _ ?P |- _ =>
      apply (wellformed_output_typing H
               (wellformed_valid_tenv He)
               (wellformed_valid_env Hd)
               (wellformed_valid_store_type Hp))
  end : wellformed.

Lemma wellformed_output_valid_tenv_extension_and_typing :
  forall v E1 E2 D P t T,
    valid_tenv_extension_and_typing v E1 E2 D P t T ->
    type_environment E1 ->
    environment D ->
    store_type P ->
    type T.
Proof.
  introv Hv He Hd Hp.
  assert (type_environment_extension E1 E2)
    by auto with wellformed.
  assert (type_environment (E1 & E2))
    by auto using type_environment_extend.
  destruct Hv; auto with wellformed.
Qed.

Hint Extern 1 (type ?T) =>
  match goal with
  | H : valid_tenv_extension_and_typing _ ?E _ ?D ?P _ T,
    He : type_environment ?E,
    Hd : environment ?D,
    Hp : store_type ?P |- _ =>
      apply (wellformed_output_valid_tenv_extension_and_typing
               H He Hd Hp)
  | H : valid_tenv_extension_and_typing _ ?E _ ?D ?P _ T,
    He : valid_tenv _ ?E,
    Hd : valid_env _ _ ?D,
    Hp : valid_store_type _ ?P |- _ =>
      apply (wellformed_output_valid_tenv_extension_and_typing
               H (wellformed_valid_tenv He)
               (wellformed_valid_env Hd)
               (wellformed_valid_store_type Hp))
  end : wellformed.

Lemma wellformed_output_typing_scheme : forall v E D P t M,
    typing_scheme v E D P t M ->
    type_environment E ->
    environment D ->
    store_type P ->
    scheme M.
Proof.
  introv Ht He Hd Hp.
  destruct Ht.
  apply scheme_c with (L := L).
  apply scheme_aux_c.
  intros Xs Hf.
  fresh_length Hf as Hl.
  assert (valid_tenv_extension_and_typing v E
            (Xs ~: M) D P t (instance_vars M Xs)) as Hv by auto.
  inversion Hv; subst.
  apply ranges_and_type_c; auto with wellformed.
  apply type_environment_ranges_inv_ranges with E;
    auto with wellformed.
Qed.

Hint Extern 1 (scheme ?M) =>
  match goal with
  | H : typing_scheme _ ?E ?D ?P _ M,
    He : type_environment ?E,
    Hd : environment ?D,
    Hp : store_type ?P |- _ =>
      apply (wellformed_output_typing_scheme
               H He Hd Hp)
  | H : typing_scheme _ ?E ?D ?P _ M,
    He : valid_tenv _ ?E,
    Hd : valid_env _ _ ?D,
    Hp : valid_store_type _ ?P |- _ =>
      apply (wellformed_output_typing_scheme
               H (wellformed_valid_tenv He)
               (wellformed_valid_env Hd)
               (wellformed_valid_store_type Hp))
  end : wellformed.
