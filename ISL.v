From iris.bi Require Import bi.
Require Export lang.

Delimit Scope S with S.

Definition iProp := mem → Prop.

Definition iEntails (P Q : iProp) : Prop := ∀ m, P m → Q m.
Definition iEmp : iProp := λ m, m = ∅.
Definition iPoints (l : nat) (v : val) : iProp := λ m, m = {[ l := (Value v) ]}.
Definition iNegPoints (l : nat) : iProp := λ m, m = {[ l := Reserved ]}.
Definition iSep (P Q : iProp) : iProp := λ m, ∃ m1 m2, P m1 ∧ Q m2 ∧ m = m1 ∪ m2 ∧ m1 ##ₘ m2 .
Definition iWand (P Q : iProp) : iProp := λ m, ∀ m', m ##ₘ m' → P m' → Q (m' ∪ m).
Definition iAnd (P Q : iProp) : iProp := λ m, P m ∧ Q m.
Definition iOr (P Q : iProp) : iProp := λ m, P m ∨ Q m.
Definition iForall {A} (P : A → iProp) : iProp := λ m, ∀ x, P x m.
Definition iExists {A} (P : A → iProp) : iProp := λ m, ∃ x, P x m.
Definition iPure (φ : Prop) : iProp := λ m, φ ∧ m = ∅.
Definition iOwn (m : mem) : iProp := λ m', m' = m.

Notation "P ⊢ Q" := (iEntails P%S Q%S) (at level 99, Q at level 200).
Notation "P ∗ Q" := (iSep P%S Q%S) (at level 80, right associativity) : S.
Notation "P ∧ Q" := (iAnd P%S Q%S) (at level 80, right associativity) : S.
Notation "P ∨ Q" := (iOr P%S Q%S) (at level 85, right associativity) : S.
Notation "l ↦ v" := (iPoints l v) (at level 20) : S.
Notation "l ↦ ⊥" := (iNegPoints l) (at level 20) : S.
Notation "'emp'" := iEmp : S.
Notation "P -∗ Q" := (iWand P%S Q%S) (at level 99, Q at level 200, right associativity) : S.
Notation "⌜ p ⌝" := (iPure p) (at level 1, p at level 200) : S.
Notation "∀ x1 .. xn , P" :=
  (iForall (fun x1 => .. (iForall (fun xn => P%S)) ..))
  (at level 200, x1 binder, xn binder, right associativity) : S.
Notation "∃ x1 .. xn , P" :=
  (iExists (fun x1 => .. (iExists (fun xn => P%S)) ..))
  (at level 200, x1 binder, xn binder, right associativity) : S.

Ltac iUnfold := unfold iEmp, iNegPoints, iPoints, iSep, iWand, iForall, iExists, iPure, iEntails, iAnd, iOr in *.

Section seplogic.

  Ltac duh := iUnfold;
    naive_solver (
      rewrite ?map_union_assoc ?left_id ?right_id;
      simplify_map_eq;
      try apply map_union_comm;
      solve_map_disjoint).

  (* The following lemma statements are from Robbert's exercises *)

  Lemma iEntails_refl P : P ⊢ P.
  Proof. duh. Qed.

  Lemma iEntails_trans P Q R : (P ⊢ Q) → (Q ⊢ R) → (P ⊢ R).
  Proof. duh. Qed.

  Lemma iSep_mono_l P1 P2 Q : (P1 ⊢ P2) → P1 ∗ Q ⊢ P2 ∗ Q.
  Proof. duh. Qed.

  Lemma iSep_comm P Q : P ∗ Q ⊢ Q ∗ P.
  Proof. duh. Qed.

  Lemma iSep_assoc P Q R : P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R.
  Proof. duh. Qed.

  Lemma iSep_emp_l P : P ⊢ emp ∗ P.
  Proof. duh. Qed.

  Lemma iSep_emp_l_inv P : emp ∗ P ⊢ P.
  Proof. duh. Qed.

  Lemma iWand_intro_r P Q R : (P ∗ Q ⊢ R) → P ⊢ Q -∗ R.
  Proof. duh. Qed.

  Lemma iWand_elim P Q : P ∗ (P -∗ Q) ⊢ Q.
  Proof. duh. Qed.

  Lemma iAnd_intro (P Q R : iProp) : (R ⊢ P) → (R ⊢ Q) → R ⊢ P ∧ Q.
  Proof. duh. Qed.

  Lemma iAnd_elim_l (P Q : iProp) : P ∧ Q ⊢ P.
  Proof. duh. Qed.

  Lemma iAnd_elim_r (P Q : iProp) : P ∧ Q ⊢ Q.
  Proof. duh. Qed.

  Lemma iOr_intro_l (P Q : iProp) : P ⊢ P ∨ Q.
  Proof. duh. Qed.

  Lemma iOr_intro_r (P Q : iProp) : Q ⊢ P ∨ Q.
  Proof. duh. Qed.

  Lemma iOr_elim (P Q R : iProp) : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R.
  Proof. duh. Qed.

  Lemma iForall_intro {A} P (Q : A → iProp) : (∀ x, P ⊢ Q x) → (P ⊢ ∀ x, Q x).
  Proof. duh. Qed.

  Lemma iForall_elim {A} (P : A → iProp) x : (∀ z, P z) ⊢ P x.

  Proof. duh. Qed.
  Lemma iExists_intro {A} (P : A → iProp) x : P x ⊢ ∃ z, P z.
  Proof. duh. Qed.

  Lemma iExists_elim {A} (P : A → iProp) Q :  (∀ x, P x ⊢ Q) → (∃ z, P z) ⊢ Q.
  Proof. duh. Qed.

  Lemma iSep_emp_r P : P ⊢ P ∗ emp.
  Proof. duh. Qed.

  Lemma iSep_emp_r_inv P : P ∗ emp ⊢ P.
  Proof. duh. Qed.

  Lemma iSep_mono_r P Q1 Q2 : (Q1 ⊢ Q2) → P ∗ Q1 ⊢ P ∗ Q2.
  Proof. duh. Qed.

  Lemma iSep_mono P1 P2 Q1 Q2 : (P1 ⊢ P2) → (Q1 ⊢ Q2) → P1 ∗ Q1 ⊢ P2 ∗ Q2.
  Proof. duh. Qed.

  Lemma iSep_assoc' P Q R : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R).
  Proof. intros ? (? & ? & (? & ? & ?) & ?); repeat eexists; duh. Qed.

  Lemma iWand_intro_l P Q R : (Q ∗ P ⊢ R) → P ⊢ Q -∗ R.
  Proof. duh. Qed.

  Lemma iExist_sep {A} (P : A → iProp) Q : (∃ x, P x) ∗ Q ⊢ ∃ x, P x ∗ Q.
  Proof. duh. Qed.

  Lemma iPure_intro (φ : Prop) : φ → emp ⊢ ⌜ φ ⌝.
  Proof. duh. Qed.

  Lemma iPure_elim (φ : Prop) P Q : (φ → P ⊢ Q) → ⌜ φ ⌝ ∗ P ⊢ Q.
  Proof. duh. Qed.

  Lemma iPure_elim' (φ : Prop) Q : (φ → emp ⊢ Q) → ⌜ φ ⌝ ⊢ Q.
  Proof. duh. Qed.

End seplogic.



Definition post (e : expr) (P : iProp) (v : option val) : iProp :=
  λ m', ∀ mf, m' ##ₘ mf → (∃ m e', m ##ₘ mf ∧ P m ∧ steps e (m ∪ mf) e' (m' ∪ mf) ∧ is_error_or_val v e' (m' ∪ mf)).

Section primitive_post_rules.

  Lemma post_mono P R Q e v:
    (P ⊢ Q) → (R ⊢ post e P v) → (R ⊢ post e Q v).
  Proof.
    intros ??HP????. edestruct HP; naive_solver.
  Qed.

  Lemma post_frame P Q e v :
    Q ∗ post e P v ⊢ post e (Q ∗ P) v.
  Proof.
    iUnfold.
    intros mT (m & m' & Hq & Hwp & -> & Hdisj) mf Hdisj'.
    edestruct (Hwp (m ∪ mf)) as (m0&e0&?&?&?&?); first solve_map_disjoint.
    exists (m0 ∪ m), e0.
    split_and!;[|eexists _,_;split_and!|..]; eauto;
    try solve_map_disjoint; rewrite ?(map_union_comm m m') -?assoc_L; eauto.
    apply map_union_comm. solve_map_disjoint.
  Qed.

  Lemma post_val v (Q : val -> iProp) :
    (Q v) ⊢ post (EVal v) (Q v) (Some v).
  Proof.
    iUnfold. intros ???. repeat eexists; eauto using steps_refl.
  Qed.

  Lemma post_ctxS E e P v w :
    post (fill E (EVal w)) (post e P (Some w)) v ⊢ post (fill E e) P v.
  Proof.
    intros m H mf Hdisj.
    specialize (H mf Hdisj) as (?&?&Hdisj'&H'&?&?).
    specialize (H' mf Hdisj') as (?&?&?&?&?&?).
    destruct v; asimpl;
    eauto 10 using steps_trans, steps_context.
  Qed.

  Lemma post_ctxN E e P:
    post e P None ⊢ post (fill E e) P None.
  Proof.
    intros m H mf Hdisj.
    specialize (H mf Hdisj) as (?&?&?&?&?&?).
    simpl. eauto 8 using steps_context, is_error_fill.
  Qed.


  Definition pure_step (e e' : expr) := ∀ h,  step e h e' h.

  Lemma post_pure_step e e' P v :
    pure_step e e' → post e' P v ⊢ post e P v.
  Proof.
    intros pure m H mf Hdisj.
    specialize (H mf Hdisj) as (?&?&?&?&?&?).
    eauto 8 using steps_step.
  Qed.


  Definition no_step e := ¬ is_val e ∧ ∀ e' m m', ¬ step e m e' m'.

  Lemma post_no_step P e :
    no_step e -> P ⊢ post e P None.
  Proof.
    intros [] m Pm mf Hdisj.
    repeat eexists; eauto using steps.
  Qed.

  Lemma no_step_EError : no_step EError.
  Proof.
    split; eauto using step_error.
  Qed.

  Lemma post_error P :
    P ⊢ post EError P None.
  Proof.
    eapply post_no_step, no_step_EError.
  Qed.

  Lemma post_alloc1 v l :
    l ↦ v ⊢ post (EAlloc (EVal v)) emp (Some (VLoc l)).
  Proof.
    iUnfold.
    intros ?->. eexists _,_.
    split_and!;[|done|..|done].
    + solve_map_disjoint.
    + rewrite left_id_L. apply step_once.
      apply step_single.
      rewrite -insert_union_singleton_l.
      constructor. intros ??HH.
      specialize (H l). revert H.
      rewrite HH lookup_singleton //.
  Qed.

  Lemma post_alloc2 l v:
    l ↦ v ⊢ post (EAlloc (EVal v)) (l ↦ ⊥) (Some (VLoc l)).
  Proof.
    intros m H mf Hdisj.
    exists {[ l := Reserved ]}, (EVal (VLoc l)).
    split.
    - (* l is not in mf so we are ok but we have to go through the disjoint definition *)
      apply map_disjoint_spec.
      intros.
      unfold iPoints in H.
      apply lookup_singleton_Some in H0 as []; asimpl.
      assert (mf !! i = None). { solve_map_disjoint. } simplify_eq.
    - repeat split; try done.
      unfold iPoints in H. subst.
      rewrite <- (insert_singleton l Reserved (Value v)).
      apply step_once.
      rewrite <- (insert_union_l {[l:=Reserved]} mf l (Value v)).
      apply step_alloc.
      unfold valid_alloc.
      rewrite lookup_union lookup_singleton. intros.
      destruct (mf !! l); simpl in *; simplify_eq; eauto.
  Qed.

  Lemma post_freeS l v:
    l ↦ ⊥ ⊢ post (EFree (EVal (VLoc l))) (l ↦ v) (Some VUnit).
  Proof.
    intros m H mf Hdisj.
    exists (<[ l := (Value v) ]> m), (EVal VUnit). iUnfold. subst.
    split_and!; rewrite ?insert_singleton; simpl; try solve_map_disjoint.
    apply step_once.
    erewrite <- (insert_singleton _ _ Reserved), <-insert_union_l.
    eapply step_free. exists v.
    apply lookup_union_Some_l, lookup_insert.
  Qed.

  Lemma post_freeN l:
    l ↦ ⊥ ⊢ post (EFree (EVal (VLoc l))) (l ↦ ⊥) None.
  Proof.
    intros m H mf Hdisj.
    eexists _,_.
    split_and!;eauto with astep.
    split; auto.
    intros e' m' Hstep.
    apply step_free_inv in Hstep as (? & ? & []). iUnfold. subst.
    apply lookup_union_Some in H1 as []; eauto.
    + apply lookup_singleton_Some in H as []. asimpl.
    + specialize (Hdisj l). rewrite H in Hdisj.
      rewrite lookup_singleton in Hdisj. by asimpl.
  Qed.

  Lemma post_loadS l v:
    l ↦ v ⊢ post (ELoad (EVal (VLoc l))) (l ↦ v) (Some v).
  Proof.
    intros m H mf Hdisj.
    exists m, (EVal v). simpl.
    split_and!; eauto.
    iUnfold. subst.
    apply step_once, step_load, lookup_union_Some_l, lookup_singleton.
  Qed.

  Lemma post_loadN l:
    iNegPoints l ⊢ post (ELoad (EVal (VLoc l))) (iNegPoints l) None.
  Proof.
    intros m H mf Hdisj.
    eexists _,_.
    split_and!; eauto with astep. simpl.
    split; auto. iUnfold. subst.
    intros e  m' Hstep.
    apply step_load_inv in Hstep as ( v & ( -> & Hm & _)).
    apply lookup_union_Some in Hm as []; auto.
    + rewrite lookup_singleton in H. asimpl.
    + specialize (Hdisj l). rewrite H in Hdisj.
      rewrite lookup_singleton in Hdisj. by asimpl.
  Qed.

  Lemma post_storeS l v v':
    (l ↦ v') ⊢ post (EStore (EVal (VLoc l)) (EVal v')) (l ↦ v) (Some VUnit).
  Proof.
    intros m H mf Hdisj.
    exists (<[ l := Value v ]> m), (EVal VUnit). iUnfold. subst.
    rewrite !insert_singleton.
    split_and!;simpl;eauto.
    + solve_map_disjoint.
    + eapply step_once. apply step_single.
      erewrite <-(insert_singleton _ _ (Value v')), <-insert_union_l.
      econstructor. apply lookup_union_Some_l, lookup_singleton.
  Qed.

  Lemma post_storeN l v:
    (l ↦ ⊥) ⊢ post (EStore (EVal (VLoc l)) (EVal v)) (l ↦ ⊥) None.
  Proof.
    intros m H mf Hdisj.
    eexists _,_; split_and!; eauto with astep. simpl. iUnfold.
    split; auto.
    intros e' m' Hstep.
    erewrite step_store_inv in Hstep.
    destruct Hstep as (w & lookup_some & unit & final_heap).
    erewrite lookup_union_Some_l in lookup_some.
    2: { unfold iNegPoints in H. subst m. apply lookup_singleton. }
    discriminate.
  Qed.

End primitive_post_rules.


Section derived_post_rules.

  Lemma post_let_step s e2 v x P:
    post (subst s v e2) P x ⊢ post (ELet s (EVal v) e2) P x.
  Proof.
    apply post_pure_step. intro m.
    eauto using post_pure_step, step_single, head_step.
  Qed.

  Lemma post_seqS e1 e2 P w v:
    post e2 (post e1 P (Some w)) v ⊢ post (ESeq e1 e2) P v.
  Proof.
    intros m H.
    rewrite <-fill_seq.
    eapply post_ctxS.
    simpl.
    intros mf Hdisj.
    destruct (H mf) as (m' &e' & H' & Hdisj' & Hsteps & Hval); auto.
    eauto 8 with astep.
  Qed.

  Lemma post_seqN e1 e2 P:
    post e1 P None ⊢ post (ESeq e1 e2) P None.
  Proof.
    intros m H.
    rewrite <- fill_seq.
    apply post_ctxN.
    assumption.
  Qed.

  Lemma post_if_true t e1 e2 P v:
    post e1 (post t P (Some (VBool true))) v ⊢ post (EIf t e1 e2) P v.
  Proof.
    intros m H.
    rewrite <- fill_if.
    eapply post_ctxS.
    simpl fill.
    intros mf Hdisj.
    specialize (H mf) as (m' & e' & H' & Hdisj' & Hsteps & H);
    eauto 10 using steps_trans, steps_if_true.
  Qed.

  Lemma post_if_false t e1 e2 P v:
    post e2 (post t P (Some (VBool false))) v ⊢ post (EIf t e1 e2) P v.
  Proof.
    intros m H.
    rewrite <- fill_if.
    eapply post_ctxS.
    simpl fill.
    intros mf Hdisj.
    specialize (H mf) as (m' & e' & H' & Hdisj' & Hsteps & H);
    eauto 10 using steps_trans, steps_if_false.
  Qed.

  Lemma post_while t e P v:
    post (EIf t (ESeq e (EWhile t e)) (EVal VUnit)) P v ⊢ post (EWhile t e) P v.
  Proof.
    iUnfold.
    intros m H.
    intros mf Hdisj.
    specialize (H mf Hdisj) as (m' & e' & Hdisj' & H' & Hsteps & H).
    eauto 8 with astep.
  Qed.

  Lemma post_op op v1 v2 v P:
    eval_bin_op op v1 v2 = Some v →
    P ⊢ post (EOp op (EVal v1) (EVal v2)) P (Some v).
  Proof.
    intros Hop m HP mf Hdisj.
    repeat eexists; eauto with astep.
  Qed.

  Lemma post_amb P n :
    P ⊢ post EAmb P (Some (VNat n)).
  Proof.
    intros ????. eexists _,_. split_and!; simpl; eauto.
    eauto with astep.
  Qed.

End derived_post_rules.

Section hoare.

  (* the incorrectness triple is valid if for any state describe by (Q v)
    we can reach it from a state in P after executing P under final value v.

    Point wise entailment here represents the subset relation so (Q v) ⊂ post e P v

    NB this is still correct for Q v = false as no heap satisfies false *)
  Definition hoare (P : iProp) (e : expr) (Q : val -> iProp) : Prop :=
    ∀ v, (Q v) ⊢ (post e P (Some v)).

  Definition hoare_err (P : iProp) (e : expr) (Q : iProp) : Prop :=
    Q ⊢ (post e P None).

  Notation "{{ P }} e {{ v , Q }}" := (hoare P%S e (λ v, Q%S))
    (at level 20, e, P at level 200, Q at level 200, only parsing).

  Notation "{{ P }} e {{ERR: Q }}" := (hoare_err P%S e Q%S)
    (at level 20, e, P at level 200, Q at level 200, only parsing).


  Definition hoare' (P : iProp) (e : expr) (Q : val -> iProp) : Prop :=
    ∀ v m', Q v m' -> ∃ (m : mem) e', P m ∧ steps e m e' m' ∧ is_error_or_val (Some v) e' m'.

  Lemma hoare_hoare' P e Q :
    hoare P e Q -> hoare' P e Q.
  Proof.
    intros H???. edestruct H as (?&?&?&?&?&?);[eauto|apply map_disjoint_empty_r|].
    eexists _,_. rewrite !right_id_L in H3. split_and!; eauto.
  Qed.

  Definition hoare_err' (P : iProp) (e : expr) (Q : iProp) : Prop :=
    ∀ m', Q m' -> ∃ (m : mem) e', P m ∧ steps e m e' m' ∧ is_error_or_val None e' m'.

  Lemma hoare_err_hoare_err' P e Q :
    hoare_err P e Q -> hoare_err' P e Q.
  Proof.
    intros H??. edestruct H as (?&?&?&?&?&?);[eauto|apply map_disjoint_empty_r|].
    eexists _,_. rewrite !right_id_L in H3,H4. split_and!; eauto.
  Qed.

  Lemma hoare_alloc1 v :
    {{ emp }} (EAlloc (EVal v)) {{ r, ∃ l, ⌜ r = VLoc l ⌝  ∗ l ↦ v }}.
  Proof.
    intros v'.
    eapply iExists_elim.
    intros l.
    eapply iPure_elim.
    intros ->.
    eapply post_alloc1.
  Qed.

  Lemma hoare_alloc2 l v :
    {{ l ↦ ⊥ }} (EAlloc (EVal v)) {{ r, ⌜ r = VLoc l ⌝ ∗ l ↦ v }}.
  Proof.
    intros v'.
    eapply iPure_elim.
    intros ->.
    eapply post_alloc2.
  Qed.

  Lemma hoare_amb n :
    {{ emp }} EAmb {{ v, ⌜ v = VNat n ⌝ }}.
  Proof.
    intros v.
    eapply iPure_elim'.
    intros ->.
    eapply post_amb.
  Qed.

  Lemma hoare_disj P1 P2 Q1 Q2 e :
    {{ P1 }} e {{ v, Q1 v }} ->
    {{ P2 }} e {{ v, Q2 v }} ->
    {{ P1 ∨ P2 }} e {{ v, Q1 v ∨ Q2 v }}.
  Proof.
    unfold hoare.
    intros H1 H2 v. specialize (H1 v). specialize (H2 v).
    eapply iOr_elim.
    + eapply post_mono. eapply iOr_intro_l. done.
    + eapply post_mono. eapply iOr_intro_r. done.
  Qed.

  Lemma hoare_exists {A} (P : A -> iProp) Q e :
    (∀ x, {{ (P x) }} e {{ v, Q x v }}) -> {{ ∃ x, P x }} e {{ v, ∃ x, Q x v }}.
  Proof.
    unfold hoare. eauto using post_mono, iExists_intro, iExists_elim.
  Qed.

  Lemma hoare_error P Q :
    {{ P }} EError {{ERR: Q }}.
  Proof.
  Admitted.

  Lemma hoare_let : True. Proof. done. Qed.
  Lemma hoare_while : True. Proof. done. Qed.
  Lemma hoare_seqS : True. Proof. done. Qed.
  Lemma hoare_seqN : True. Proof. done. Qed.
  Lemma hoare_cons : True. Proof. done. Qed.
  Lemma hoare_frame : True. Proof. done. Qed.
  Lemma hoare_freeS : True. Proof. done. Qed.
  Lemma hoare_freeN : True. Proof. done. Qed.
  Lemma hoare_loadS : True. Proof. done. Qed.
  Lemma hoare_loadN : True. Proof. done. Qed.
  Lemma hoare_storeS : True. Proof. done. Qed.
  Lemma hoare_storeN : True. Proof. done. Qed.
  Lemma hoare_op : True. Proof. done. Qed.
  Lemma hoare_pure_step : True. Proof. done. Qed.
  Lemma hoare_val : True. Proof. done. Qed.
  Lemma hoare_ctxS : True. Proof. done. Qed.
  Lemma hoare_ctxN : True. Proof. done. Qed.
  Lemma hoare_if_true : True. Proof. done. Qed.
  Lemma hoare_if_false : True. Proof. done. Qed.

End hoare.
(* this is about evaluation of pure expressions *)

(*

Question: which of these do we want?

[P] e [v. Q v]_ERROR :=  (∃ h h' e', P h ∧ step e h e' h' ∧ is_stuck e') ∨ (∀ v h', Q v h' → ∃ h, P h ∧ step e h (EVal v) h')

[P] e []_ERROR := ∃ h h' e', P h ∧ steps e h e' h' ∧ is_stuck e'

[P] e [v. Q v] := ∀ v h', Q v h' → exist h, P h ∧ steps e h (EVal v) h'

Questions:
- [x] Maybe we only want #1 and #2, because #1 is weaker than #3, so it's easier to prove, but proving #1 is always sufficient, because if we are in the left disjunct, then we already proved our end goal. Question: is this reasoning correct?
- [x] Maybe we want #2 and #3, because that's what they do in the paper. Question: is that correct?
- Why does the paper care about the final heap state if there is already an error?
- Which proof rules are valid for the #1,#2,#3?
- Edoardo's questions...

Plan:
- [x] Try to answer the questions and add more questions
- [x] Prove that the push_back example has an error
- [x] Define #1,#2,#3 in Coq, define under-approximation triples [P] e []_ERROR, [P] e [v. Q v] and define [P] e [v. Q v]_ERROR using these primitives
- [x] Define mfresh and prove that it gives something fresh
- [x] Get unicode working in emacs: https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/editor.md
- [x] finish the proof that client has an error according to #2
  + [x] map_alter must have a theorem for union of maps, look it up -> insert
- [x] start working on the assertion language
  + [x] separating conjunction
  + [x] separating implication
  + [x] points to
  + [x] pure
  + [x] forall
  + [x] exists
- [x] Make iError also have a frame
- [x] State the rule for wp while
- [x] Prove the rule for wp while
- [x] Think about combining iReaches/iError
- [x] Delete the iReaches stuff
- [x] Change definition of is_error to use step instead of head_step
- [ ] Create a document with all the primitive rules that you have proved
- [ ] Write down the intuitive meaning of the wp/ewp and entailment
        What does wp e P v mean?
        What does Q ⊢ wp e P v mean?
        (jules: reachable P e v ⊣ Q)
- [x] Prove the admitted rules for ∨ and ∧
- [x] Refactor ewp/wp to use this option
- [x] Define Hoare triples in terms of wp/ewp
- [x] Think about negative points to / the two alloc rules
- [x] Clean up the rules, delete any rules that are subsumed by the ctx rules
- [ ] Put all the rules for the Hoare triples from the paper as lemmas in that file (Admitted)
- [ ] Think about which additional rules for wp/ewp we need to prove all the rules in the paper using those lemmas
- [ ] Prove all the rules in the paper using the rules for wp/ewp
- [ ] Clean up the file, remove unused definitions
- [ ] Think about which rules can be derived from other rules, and put them in a separate section and prove them in terms of the other rules
- [ ] Prove the examples from the paper incorrect using the post rules, and using the hoare rules
- [ ] Write thesis
- [ ] In the ISL paper can they prove this program can error
  ```
  x = alloc(3)
  y = alloc(3)
  if(x != y) then foo: Error
  ```
- [ ] Completeness theorem (?)

*)
