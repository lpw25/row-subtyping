(************************************************
 *           Row Subtyping - Typing             *
 *                 Leo White                    *
 ************************************************)

Set Implicit Arguments.
Require Import LibLN Cofinite Definitions
        Substitution Wellformedness Kinding.

Hint Constructors typing.

Lemma valid_scheme_empty : forall E T,
    kinding E T knd_type ->
    valid_scheme E (sch_empty T).
Proof.
  introv Hk.
  apply valid_scheme_c with (L := \{}).
  introv Hf.
  fresh_length Hf as Hl.
  destruct Xs; try discriminate; auto.
Qed.

Lemma typing_weakening : forall E F G t T,
    typing (E & G) t T ->
    valid_env (E & F & G) ->
    typing (E & F & G) t T.
Proof.
  introv Ht Hv.
  apply validated_typing in Ht.
  remember (E & G) as EG.
  generalize dependent E.
  generalize dependent G.
  generalize dependent F.
  induction Ht; introv Heq Hv; subst;
    eauto using valid_instance_weakening, binds_weakening,
                kinding_weakening, subtype_weakening
          with valid_env_regular.    
  - apply typing_abs with (L := L \u dom E0 \u dom F \u dom G);
      auto using kinding_weakening.
    intros x Hn.
    assert (valid_env (E0 & F & G & x ~: sch_empty T1))
      as He by auto using valid_env_type_weakening.
    rewrite <- concat_assoc.
    rewrite <- concat_assoc in He.
    auto using concat_assoc.
  - apply typing_let
      with (M := M) (L := L \u dom E0 \u dom F \u dom G).
    + intros Xs Hl.
      assert (valid_env (E0 & F & G & Xs ~::* M))
        as He by auto using valid_env_kinds_weakening.
      rewrite <- concat_assoc.
      rewrite <- concat_assoc in He.
      auto using concat_assoc.
    + intros x Hl.
      assert (valid_env (E0 & F & G & x ~: M))
        as He by auto using valid_env_type_weakening.
      rewrite <- concat_assoc.
      rewrite <- concat_assoc in He.
      auto using concat_assoc.
  - apply typing_match
      with (L := L \u dom E0 \u dom F \u dom G)
           (T1 := T1) (T2 := T2) (T3 := T3) (T4 := T4)
           (T5 := T5) (T6 := T6) (T7 := T7);
      auto using kinding_weakening, subtype_weakening.
    + intros x Hn.
      assert
        (valid_env (E0 & F & G & x ~: sch_empty (typ_variant T3)))
        as He by auto using valid_env_type_weakening.
      rewrite <- concat_assoc.
      rewrite <- concat_assoc in He.
      auto using concat_assoc.
    + intros y Hn.
      assert
        (valid_env (E0 & F & G & y ~: sch_empty (typ_variant T5)))
        as He by auto using valid_env_type_weakening.
      rewrite <- concat_assoc.
      rewrite <- concat_assoc in He.
      auto using concat_assoc.
  - apply typing_destruct
      with (L := L \u dom E0 \u dom F \u dom G)
           (T1 := T1) (T2 := T2) (T3 := T3);
      auto using kinding_weakening, subtype_weakening.
    intros x Hn.
    assert
      (valid_env (E0 & F & G & x ~: sch_empty T3))
      as He by auto using valid_env_type_weakening.
    rewrite <- concat_assoc.
    rewrite <- concat_assoc in He.
    auto using concat_assoc.
Qed.

Lemma typing_weakening_l : forall E F t T,
    typing E t T ->
    valid_env (E & F) ->
    typing (E & F) t T.
Proof.
  introv Ht Hv.
  rewrite <- concat_empty_r with (E := E & F).
  apply typing_weakening; rewrite concat_empty_r; assumption.
Qed.

Lemma typing_typ_subst : forall E F X K S t T,
    typing (E & X ~:: K & F) t T ->
    kinding E S K ->
    typing (E & env_subst X S F) t (typ_subst X S T).
Proof.
  introv Ht Hk.
  remember (E & X ~:: K & F) as EXF.
  generalize dependent E.
  generalize dependent F.
  induction Ht; introv Heq Hk; subst; eauto.
  - apply typing_var
        with (M := sch_subst X S M)
             (Us := (List.map (typ_subst X S) Us));
      eauto using valid_env_typ_subst, valid_instance_typ_subst,
                  sch_subst_instance, binds_typ_typ_subst
            with kinding_regular.
  - apply typing_abs with (L := L \u \{X} \u dom E0 \u dom F);    
      fold (knd_subst X S knd_type);
      eauto using kinding_typ_subst.
    introv Hn.
    rewrite <- sch_subst_empty.
    rewrite <- concat_assoc.
    rewrite <- env_subst_typ.
    auto using concat_assoc.
  - apply typing_let
      with (L := L \u \{X} \u dom E0 \u dom F) (M := sch_subst X S M).
    + introv Hf.
      autorewrite with rew_sch_arity in Hf.
      fresh_length Hf as Hl.
      rewrite <- env_subst_bind_knds;
        autorewrite with rew_env_dom; auto with kinding_regular.
      rewrite <- concat_assoc.
      rewrite <- env_subst_concat.
      unfold instance_vars.
      rewrite <- typ_subst_fresh_typ_fvars
        with (X := X) (U := S); auto.
      rewrite <- sch_subst_instance; auto with kinding_regular.
      eauto using concat_assoc.
    + introv Hn.
      rewrite <- concat_assoc.
      rewrite <- env_subst_typ.
      auto using concat_assoc.
  - apply typing_constructor
      with (T2 := typ_subst X S T2) (T3 := typ_subst X S T3).
    + fold (knd_subst X S (knd_range (typ_top CSet.universe) T2)).