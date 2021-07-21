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
Definition iTrue : iProp := λ m , True.
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

Ltac iUnfold := unfold iEmp, iNegPoints, iPoints, iSep, iWand, iForall, iExists, iPure, iEntails, iAnd, iOr, iTrue in *.

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


Lemma head_step_frame_equiv e m e' m' :
  head_step e m e' m' <-> ∀ mf, m' ##ₘ mf -> head_step e (m ∪ mf) e' (m' ∪ mf).
Proof.
  split.
  - intros. destruct H; rewrite -?insert_union_l; try econstructor; eauto;
    try apply lookup_union_Some_l; eauto.
    intros ??. apply H.
    rewrite lookup_union in H1.
    assert (mf !! l = None) by solve_map_disjoint.
    rewrite H2 in H1.
    destruct (m !! l); by asimpl.
  - intros. specialize (H ∅). rewrite !right_id in H.
    apply H. solve_map_disjoint.
Qed.

Lemma step_frame_equiv e m e' m' :
  step e m e' m' <-> ∀ mf, m' ##ₘ mf -> step e (m ∪ mf) e' (m' ∪ mf).
Proof.
  split.
  - intros []. rewrite ->head_step_frame_equiv in H.
    eauto using step.
  - intros. specialize (H _ (map_disjoint_empty_r _)).
    by rewrite !right_id_L in H.
Qed.

Lemma step_heap_mono e m e' m' x :
  step e m e' m' -> m' ##ₘ x -> m ##ₘ x.
Proof.
  intros []?. destruct H; solve_map_disjoint.
Qed.

Lemma steps_heap_mono e m e' m' x :
  steps e m e' m' -> m' ##ₘ x -> m ##ₘ x.
Proof.
  induction 1; eauto using step_heap_mono.
Qed.

Lemma steps_frame_equiv e m e' m' :
  steps e m e' m' <-> ∀ mf, m' ##ₘ mf -> steps e (m ∪ mf) e' (m' ∪ mf).
Proof.
  split.
  - induction 1; eauto using steps.
    intros.
    assert (m2 ##ₘ mf). { eapply steps_heap_mono; eauto. }
    rewrite ->step_frame_equiv in H.
    eapply steps_step; eauto.
  - intros. specialize (H _ (map_disjoint_empty_r _)).
    by rewrite !right_id_L in H.
Qed.

Definition post (e : expr) (P : iProp) (v : option val) : iProp :=
  λ m', ∀ mf, m' ##ₘ mf → (∃ m e', m ##ₘ mf ∧ P m ∧ steps e (m ∪ mf) e' (m' ∪ mf) ∧ is_error_or_val v e' (m' ∪ mf)).

Definition post' (e : expr) (P : iProp) (v : option val) : iProp :=
  λ m', ∃ m e', P m ∧ steps e m e' m' ∧ is_error_or_val v e' m'.

Lemma post_post' e P v m' :
  post e P v m' <-> post' e P v m'.
Proof.
  split.
  - intros ?. specialize (H ∅).
    edestruct H as (? & ? & ? & ? & ? & ?); first solve_map_disjoint.
    rewrite !right_id_L in H2,H3.
    eexists _,_; eauto.
  - intros ???. edestruct H as (? & ? & ? & ? & ?).
    eexists _,_. split_and!;[|done|..];eauto using steps_heap_mono.
    rewrite ->steps_frame_equiv in H2. eauto.
    destruct v; simpl in *; eauto. unfold is_error in *.
    destruct H3. split; eauto.
    intros ???. eapply H4.
    (* Theorem is false for v = None!!! *)
Abort.


Section primitive_post_rules.

  Lemma post_trivial P e v:
    ⌜ False ⌝ ⊢ post e P v.
  Proof.
    intros m H.
    exfalso.
    destruct H.
    done.
  Qed.

  Lemma post_mono P Q R e v:
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

  (* the wand impose a constraint on the extensions of the initial heap
    P -∗ Q h means that this is a heap h such that if we extend it with a heap
    h' satisfying P then h ∗ h' satisfies Q.

   In Iris the WAND rule is (∀ v, Φ v -∗ Ψ v) ∗ wp e Φ ⊢ wp e Ψ
   so we have to adapt to that. We would like to reason about
   the initial set of heaps though so instead of having Φ, Ψ : val → iProp
   we are going to have Φ, Ψ : iProp and our rule translates to
   (Φ -∗ Ψ) ∗ post e Φ v ⊢ post e Ψ v

   Interesting enough I have not used the post_mono here or other primitive rules
   except for the wand elimination
  *)
  Lemma post_wand P R e v :
    (P -∗ R) ∗ post e P v ⊢ post e R v.
  Proof.
    intros m (m1 & m2 & Hm1 & Hm2 & Hm & Hdisj).
    intros mf Hdisj_mf.
    erewrite (symmetry_iff map_disjoint m1 m2)  in Hdisj.
    specialize (Hm2 (m1 ∪ mf)) as (m2' & e' & Hdisj' & Hm2' & Hsteps & H).
    - apply map_disjoint_union_r_2.
      + assumption.
      + subst m.
        erewrite map_disjoint_union_l in Hdisj_mf.
        destruct Hdisj_mf as [Hdisj_mf_m1 Hdisj_mf_m2].
        assumption.
    - exists (m2' ∪ m1), e'.
      erewrite map_disjoint_union_r in Hdisj'.
      destruct Hdisj' as [? ?].
      split.
      + apply map_disjoint_union_l_2.
        * assumption.
        * subst m.
          erewrite map_disjoint_union_l in Hdisj_mf.
          destruct Hdisj_mf as [Hdisj_mf_m1 Hdisj_mf_m2].
          assumption.
      + split.
        * eapply iWand_elim.
          exists m2', m1.
          split; eauto.
        * rewrite map_union_comm in Hm.
          split.
          -- rewrite -> 2 (assoc_L _ _) in Hsteps.
             rewrite <- Hm in Hsteps.
             assumption.
          -- rewrite assoc_L in H.
             rewrite <- Hm in H.
             assumption.
          -- rewrite (symmetry_iff map_disjoint m1 m2).
             done.
  Qed.

  (* Now on the Iris from the ground up we have seen that the weakest precondition rule
     for the wand and the rule for monotonicity implies the framing so let's try
     and do that also here *)
  Lemma wand_implies_framing P Q e v :
    Q ∗ post e P v ⊢ post e (Q ∗ P) v.
  Proof.
    eapply iEntails_trans.
    2: {
      eapply post_wand.
    }
    apply iSep_mono.
    2: {
      apply iEntails_refl.
    }
    eapply iWand_intro_r.
    eapply iEntails_refl.
  Qed.

  Lemma post_val v Q :
    Q ⊢ post (EVal v) Q (Some v).
  Proof.
    iUnfold. intros ???. repeat eexists; eauto using steps_refl.
  Qed.

  (* I think this is the closest I can get to wp_bind  as the result assertion
     Q must also reference the value w we will use in the substitution *)
  Lemma post_bind E e P Q v w:
    (Q w v ⊢ post (fill E (EVal w)) (post e P (Some w)) (Some v)) →
    (Q w v ⊢ post (fill E e) P (Some v)).
  Proof.
    intros?????.
    specialize (H m H0 mf H1) as (?&?&?&?&?&?).
    specialize (H2 mf H) as (?&?&?&?&?&?).
    asimpl.
    eauto 10 using steps_trans, steps_context.
  Qed.

  (* We can recover the other context rule by the post_mono;

     (post e P (Some w)) ⊢ Φ w →
     post (fill E (EVal w)) (Φ w) v ⊢ post (fill E e) P v.
*)
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

  Lemma post_ctxS' E e Φ P v w:
    ⌜ Φ w ⌝ ∗ post (fill E (EVal w)) (post e P (Some w)) v ⊢ post (fill E e) P v.
  Proof.
    apply iPure_elim.
    intro.
    apply post_ctxS.
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
    l↦ ⊥ ⊢ post (ELoad (EVal (VLoc l))) (l ↦ ⊥) None.
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
    eapply iEntails_trans.
    eapply (post_pure_step (ESeq (EVal w) e2)).
    intro. eauto using step_single, head_step.
    rewrite <- ! fill_seq.
    eapply post_ctxS.
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
    eapply iEntails_trans.
    eapply (post_pure_step (EIf (EVal (VBool true)) e1 e2)).
    intro. eauto using step_single, head_step.
    rewrite <- ! fill_if.
    eapply post_ctxS.
  Qed.

  Lemma post_if_false t e1 e2 P v:
    post e2 (post t P (Some (VBool false))) v ⊢ post (EIf t e1 e2) P v.
  Proof.
    eapply iEntails_trans.
    eapply (post_pure_step (EIf (EVal (VBool false)) e1 e2)).
    intro. eauto using step_single, head_step.
    rewrite <- ! fill_if.
    eapply post_ctxS.
  Qed.

  Lemma post_while t e P v:
    post (EIf t (ESeq e (EWhile t e)) (EVal VUnit)) P v ⊢ post (EWhile t e) P v.
  Proof.
    apply post_pure_step.
    intro. eauto using step_single, head_step.
  Qed.

  Lemma post_op op v1 v2 v P:
    eval_bin_op op v1 v2 = Some v →
    P ⊢ post (EOp op (EVal v1) (EVal v2)) P (Some v).
  Proof.
    intros H m HP mf Hdisj.
    repeat eexists; eauto with astep.
  Qed.

  Lemma pure_step_amb n : pure_step EAmb (EVal $ VNat n).
  Proof.
    intro. eauto with astep.
  Qed.

  Lemma post_amb P n :
    P ⊢ post EAmb P (Some (VNat n)).
  Proof.
    eapply iEntails_trans.
    2: { eauto using post_pure_step, (pure_step_amb n). }
    apply post_val.
  Qed.

  Lemma no_step_EError : no_step EError.
  Proof.
    split; eauto using step_error.
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
    ∀ v m', Q v m' → ∃ (m : mem) e', P m ∧ steps e m e' m' ∧ is_error_or_val (Some v) e' m'.

  Lemma hoare_hoare' P e Q :
    hoare P e Q → hoare' P e Q.
  Proof.
    intros H???. edestruct H as (?&?&?&?&?&?);[eauto|apply map_disjoint_empty_r|].
    eexists _,_. rewrite !right_id_L in H3. split_and!; eauto.
  Qed.

  Definition hoare_err' (P : iProp) (e : expr) (Q : iProp) : Prop :=
    ∀ m', Q m' → ∃ (m : mem) e', P m ∧ steps e m e' m' ∧ is_error_or_val None e' m'.

  Lemma hoare_err_hoare_err' P e Q :
    hoare_err P e Q → hoare_err' P e Q.
  Proof.
    intros H??. edestruct H as (?&?&?&?&?&?);[eauto|apply map_disjoint_empty_r|].
    eexists _,_. rewrite !right_id_L in H3,H4. split_and!; eauto.
  Qed.

  Definition hoare_alt (P : iProp) (e : expr) (v : val) (Q : iProp) : Prop :=
    Q ⊢ (post e P (Some v)).

  (* Doing the rules in this style would work too, and maybe that's indeed nicer *)
  Lemma hoare_alloc1_alt l v :
    hoare_alt emp%S (EAlloc (EVal v)) (VLoc l) (l ↦ v)%S.
  Proof.
    eapply post_alloc1.
  Qed.

  Lemma hoare_trivial P e:
    {{ P }} e {{ r, ⌜ False ⌝ }}.
  Proof.
    intro.
    apply iPure_elim'.
    intro.
    exfalso.
    assumption.
  Qed.

  Lemma hoare_trivialN P e:
    {{ P }} e {{ERR: ⌜ False ⌝ }}.
  Proof.
    intro.
    apply iPure_elim'.
    intro.
    exfalso.
    assumption.
  Qed.

  Lemma hoare_alloc1 l v:
    {{ emp }} (EAlloc (EVal v)) {{ r, ⌜ r = VLoc l ⌝ ∗ l ↦ v }}.
  Proof.
    intro v'.
    apply iPure_elim.
    intros ->.
    apply post_alloc1.
  Qed.

  Lemma hoare_alloc1' v :
    {{ emp }} (EAlloc (EVal v)) {{ r, ∃ l, ⌜ r = VLoc l ⌝ ∗ l ↦ v }}.
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

  Lemma hoare_amb' :
    {{ emp }} EAmb {{ v, ∃ n, ⌜ v = VNat n ⌝ }}.
  Proof.
    intros v.
    eapply iExists_elim.
    intros x.
    apply hoare_amb.
  Qed.

  Lemma hoare_exists {A} P (Q : A → val → iProp) e :
    {{ P }} e {{ v, ∃ x, Q x v }} ↔ ∀ x, {{ P }} e {{ v, Q x v }}.
  Proof.
    split.
    - intro.
      (* H can be rephrased as "all memories described by (λ v : val, (∃ x: A, Q x v))
         are reachable from P". Now the ∀ m, ∃ x can be changed to a universal
         quantification in front, as in our goal.

         This is because for any x that does not satisfy (Q x v) the statement is _false_
         hence the set of memories described is ∅ and triples such as {{ P }} C {{ ∅ }}
         are always valid.
       *)
      intros x v m HQ.
      apply (H v).
      exists x.
      auto.
    - intros H v m HQ.
      destruct HQ as (x & HQ).
      apply (H x v m HQ).
  Qed.

  Lemma hoare_disj P1 P2 Q1 Q2 e :
    {{ P1 }} e {{ v, Q1 v }} →
    {{ P2 }} e {{ v, Q2 v }} →
    {{ P1 ∨ P2 }} e {{ v, Q1 v ∨ Q2 v }}.
  Proof.
    unfold hoare.
    intros H1 H2 v. specialize (H1 v). specialize (H2 v).
    eapply iOr_elim.
    + eapply post_mono. eapply iOr_intro_l. done.
    + eapply post_mono. eapply iOr_intro_r. done.
  Qed.

  Lemma hoare_exists_forallS {A} P (Q : A -> val -> iProp) e :
    (∀ x, {{ P }} e {{ v, Q x v }}) ↔ {{ P }} e {{ v, ∃ x, Q x v }}.
  Proof.
    unfold hoare.
    split; intro.
    - auto using iExists_elim.
    - intros.
      eapply iEntails_trans.
      2: { apply H. }
      eapply iEntails_trans.
      2: { apply iExists_intro. }
      intros m HQ.
      eassumption.
  Qed.

  Lemma hoare_exists_forallN {A} (P : iProp) e (Q : A → iProp):
    (∀ x, {{ P }} e {{ERR: Q x }}) ↔ {{ P }} e {{ERR: ∃ x, Q x }}.
  Proof.
    unfold hoare_err.
    split; intro.
    - auto using iExists_elim.
    - intros.
      eapply iEntails_trans.
      2: { apply H. }
      eapply iEntails_trans.
      2: { apply iExists_intro. }
      intros m HQ.
      eassumption.
  Qed.

  Lemma hoare_cons (P : iProp) (Q : val → iProp) (P' : iProp) e (Q' : val → iProp) :
    (P ⊢ P') →
    (∀ v, (Q' v) ⊢ (Q v)) →
    {{ P }} e {{ v, Q v }} →
    {{ P' }} e {{ v, Q' v }}.
  Proof.
    intros.
    intro v.
    specialize (H0 v).
    eapply iEntails_trans.
    eassumption.
    eapply iEntails_trans.
    apply H1.
    eapply post_mono.
    eassumption.
    apply iEntails_refl.
  Qed.

  Lemma hoare_consN (P P': iProp) e (Q Q' : iProp) :
    (P ⊢ P') →
    (Q' ⊢ Q) →
    {{ P }} e {{ERR: Q}} →
    {{ P' }} e {{ERR: Q'}}.
  Proof.
    intros.
    unfold hoare_err in *.
    eapply iEntails_trans.
    apply H0.
    eapply post_mono.
    apply H.
    assumption.
  Qed.

  Lemma hoare_frame_l R P Q e:
    {{ P }} e {{ v,  Q  v }} →
    {{ R ∗ P }} e {{v, R ∗ Q v}}.
  Proof.
    unfold hoare.
    intros.
    eapply iEntails_trans.
    apply iSep_mono_r.
    apply H.
    apply post_frame.
  Qed.

  Lemma hoare_frame_lN R P Q e:
    {{ P }} e {{ERR: Q }} →
    {{ R ∗ P }} e {{ERR: R ∗ Q }}.
  Proof.
    unfold hoare_err.
    intros.
    eapply iEntails_trans.
    apply iSep_mono_r.
    apply H.
    apply post_frame.
  Qed.

  Lemma hoare_introS (Φ : val → Prop) P e Q:
    (∀ v, Φ v → {{ P }} e {{ r, Q r }}) → {{ P }} e {{ r, ⌜ Φ r ⌝ ∗ Q r}}.
  Proof.
    intros.
    unfold hoare in *.
    eauto using iPure_elim.
  Qed.

  Lemma hoare_introN (Φ : Prop) P e Q:
    (Φ → {{ P }} e {{ERR: Q}}) → {{ P }} e {{ERR: ⌜ Φ ⌝ ∗ Q }}.
  Proof.
    intros.
    unfold hoare_err in *.
    eauto using iPure_elim.
  Qed.

  Lemma hoare_freeS l v:
    {{ l ↦ v }} EFree(EVal(VLoc l)) {{ v, ⌜ v = VUnit ⌝ ∗ l ↦ ⊥ }}.
  Proof.
    unfold hoare.
    intros.
    apply iPure_elim.
    intros ->.
    apply post_freeS.
  Qed.

  Lemma hoare_freeN l :
    {{ l ↦ ⊥ }} EFree(EVal(VLoc l)) {{ERR: l ↦ ⊥ }}.
  Proof.
    apply post_freeN.
  Qed.

  Lemma hoare_loadS l w:
    {{ l ↦ w}} ELoad(EVal(VLoc l)) {{ v, ⌜ v = w ⌝ ∗ l ↦ w }}.
  Proof.
    unfold hoare.
    intros.
    apply iPure_elim.
    intros ->.
    apply post_loadS.
  Qed.

  Lemma hoare_loadN l:
    {{ l ↦ ⊥ }} ELoad(EVal(VLoc l)) {{ERR: l ↦ ⊥ }}.
  Proof.
    apply post_loadN.
  Qed.

  Lemma hoare_storeS l v v':
    {{ l ↦ v}} EStore (EVal (VLoc l)) (EVal v') {{ r, ⌜ r = VUnit ⌝ ∗ l ↦ v' }}.
  Proof.
    unfold hoare.
    intros.
    apply iPure_elim.
    intros ->.
    apply post_storeS.
  Qed.

  Lemma hoare_storeN l v:
    {{ l ↦ ⊥ }} EStore (EVal (VLoc l)) (EVal v) {{ERR: l ↦ ⊥ }}.
  Proof.
    apply post_storeN.
  Qed.

  Lemma hoare_val v: {{ emp }} (EVal v) {{ r, ⌜ r = v ⌝ }}.
  Proof.
    intro. apply iPure_elim'. intros ->. apply post_val.
  Qed.

  Lemma hoare_ctxS E Φ v P' P e Q:
    {{ P }} e {{r, ⌜ Φ r ⌝ ∗ P' r }} →
    {{ ⌜ Φ v ⌝ ∗ P' v }} (fill E (EVal v)) {{ r, Q r}} →
    {{ P }} (fill E e) {{ r, Q r }}.
  Proof.
    intros HP H.
    unfold hoare in *.
    intro.
    eapply iEntails_trans.
    2: { apply post_ctxS. }
    eapply post_mono.
    - apply HP.
    - eapply post_mono.
      2: { apply H. }
      apply iEntails_refl.
  Qed.

  Lemma hoare_ctxS' E v P' P e Q:
    {{ P }} e {{ r,  ⌜ r = v ⌝ ∗ P' r }} →
    {{ P' v }} (fill E (EVal v)) {{ r, Q r}} →
    {{ P }} (fill E e) {{ r, Q r }}.
  Proof.
    intros HP H.
    eapply (hoare_ctxS E (λ r: val,  r = v) v P' P e Q).
    eassumption.
    eapply hoare_cons.
    - eapply iEntails_trans.
      + apply (iSep_emp_l (P' v)).
      + apply iSep_mono_l.
        apply iPure_intro.
        reflexivity.
    - intro. apply iEntails_refl.
    - eauto.
  Qed.

  Lemma hoare_ctxS_iris E P' P e Q:
    {{ P }} e {{ r, P' r}} →
    (∀ v, {{ P' v }} (fill E (EVal v)) {{ r, Q r}}) →
    {{ P }} (fill E e) {{ r, Q r }}.
  Proof.
    intros HP H.
    unfold hoare.
    intro.
    eapply iEntails_trans.
    2: { apply post_ctxS. }
    unfold hoare in *.
    eapply post_mono.
    - apply HP.
    - apply (H v).
  Qed.

  Lemma hoare_ctxS_iris' E P' P e Q v:
    {{ P }} e {{ r, P' r }} →
    (∀ w, {{ P' w }} (fill E (EVal w)) {{ r, Q w r}}) →
    {{ P }} (fill E e) {{ r, Q v r }}.
  Proof.
    intros.
    specialize (H0 v).
    unfold hoare in *.
    intro.
    eapply iEntails_trans.
    2:{ apply post_ctxS. }
    eapply iEntails_trans.
    - apply H0.
    - eapply post_mono.
      + apply H.
      + apply iEntails_refl.
  Qed.

  Lemma hoare_ctxSN_iris' E P' P e Q v:
    {{ P }} e {{ r, P' r }} →
    (∀ w, {{ P' w }} (fill E (EVal w)) {{ERR: Q w}}) →
    {{ P }} (fill E e) {{ERR: Q v}}.
  Proof.
    intros.
    specialize (H0 v).
    unfold hoare in *.
    intro.
    eapply iEntails_trans.
    2:{ apply post_ctxS. }
    eapply iEntails_trans.
    - apply H0.
    - eapply post_mono.
      + apply H.
      + apply iEntails_refl.
  Qed.

  Lemma hoare_ctxSN E P' v P e Q:
    {{ P }} e {{ r,  ⌜ r = v ⌝ ∗ P' r }} →
    {{ P' v }} (fill E (EVal v)) {{ERR: Q }} →
    {{ P }} (fill E e) {{ERR: Q }}.
  Proof.
    intros HP H.
    unfold hoare.
    intro.
    eapply iEntails_trans.
    2: { apply post_ctxS. }
    unfold hoare in *.
    eapply post_mono.
    - apply HP.
    - eapply post_mono.
      2: { apply H. }
      eapply iEntails_trans.
      apply iSep_emp_l.
      apply iSep_mono.
      apply iPure_intro.
      reflexivity.
      apply iEntails_refl.
  Qed.

  Lemma hoare_ctxN E P e e' Q:
   (fill E e) = e' →
   {{ P }} e {{ERR: Q}} →
   {{ P }} e' {{ERR: Q }}.
  Proof.
    intros.
    unfold hoare_err in *.
    eapply iEntails_trans.
    apply H0.
    subst e'.
    apply post_ctxN.
  Qed.

  Section CTX.
    (* Here we have presented 3 versions of the context rule where one would have done.
       
       Why is this? Can we have a general context rule that would imply the others?

       In  hoare_ctxS' we are required to be explicit about the resulting value v of the
       inner computation.

       {{ P }} e {{ r,  ⌜ r = v ⌝ ∗ P' r }} →
       {{ P' v }} (fill E (EVal v)) {{ r, Q r}} →
       {{ P }} (fill E e) {{ r, Q r }}.
       
       In hoare_ctxS_iris instead we are not, the universal quantification on the value
       filling the hole of the context guarantees us that any value will do.
       
       {{ P }} e {{ r, P' r}} →
       (∀ v, {{ P' v }} (fill E (EVal v)) {{ r, Q r}}) →
       {{ P }} (fill E e) {{ r, Q r }}.

       This rule though is not what we would expect for incorrectness logic.
       Consider this context K ≝ let x = ⬜ in if x ≥ 1 then x else error.

       We know that K[n] has valid triples {{ n ∈ N }} K[n] {{ r, r ≥ 1 }}
       and {{ n ∈ N }} K[n] {{ERR: n = 0}} but using this second rule we cannot
       prove the first triple.
       
       The result assertion r ≥ 1 cannot be reached when we substitute n = 0
       in the context and thefere it's not true that the intermediate triple
       (∀ v, {{ P' v }} (fill E (EVal v)) {{ r, Q r}}) holds.

       This has happened because there can be two triples for the same program,
       one for correct termination and one for erroneous but we can only express
       this rule for a ``same kind combination''.

       While this rule is sound it is overly restrictive and does not yield the
       desired results for programs that may fault.

       It is true thought that we could restrict the triples for K to be
       {{ n ≥ 1 }} K[n] {{ r, r ≥ 1 }} and {{ n = 0 }} K[n] {{ERR: n = 0}}
       like we would do in correctness logic but this still does not make
       the rule perform as expected.

       We are now required to prove (∀ n, {{ n ≥ 1 }} K[n] {{ r, r ≥ 1 }})
       which means to also prove that the triple
       {{ 0 ≥ 1 }} K[0] {{ r, r ≥ 1 }} holds.

       This triple is though not provable in incorrectness logic as the
       presumption 0 ≥ 1 ⊢ False. As there is no state satisfying the presumption
       assertion the triple cannot hold. The rule is then not usable and must be changed.
       
       The alternative that can make this work is to also have the result assertion
       use the value w to constrain it in the same way the presumption n ≥ 1 would do in
       correctness logic. This is a logical consequence of the {{ P }} e {{ r, False }}
       triple be the vacuous one. We can recover the idea of controlling which values
       w we will allow in our context by having Q w r ⊢ False when w is not accepted.

       {{ P }} e {{ r, P' r }} →
       (∀ w, {{ P' w }} (fill E (EVal w)) {{ r, Q w r}}) →
       {{ P }} (fill E e) {{ r, Q v r }}.

       This means that now the assertion (∀ w, {{ P' w }} (fill E (EVal w)) {{ r, Q w r}})
       is provable and we can recover the Iris context rule.

       {{ P }} e {{ r, r ∈ N }} →
       ∀ w, {{ w ∈ N }} K[w] {{ r, r ≥ 1 ∧ w ≥ 1 }} →
       {{ P }} K[e] {{ r, r ≥ 1 ∧ v ≥ 1 }}

       This leaves us with a universally quantified variable v which is not bound in the
       result assertion of our K[e] program. This inconvenience is required to recover
       the Iris rule.

       Another important point is that both the hoare_ctx rule and the hoare_ctxS_iris'
       rule share this universally quantified v but the position in which is used is
       different.

       We can now prove that the hoare_ctx using the hoare_ctxS_iris'.
     *)

    Lemma iris_to_ctxS E (Φ : val → Prop) P' P e Q v:
      {{ P }} e {{ r, ⌜ Φ r ⌝ ∗ P' r }} →
      {{ ⌜ Φ v ⌝ ∗ P' v }} (fill E (EVal v)) {{ r, Q r }} →
      {{ P }} (fill E e) {{ r , Q r }}.
    Proof.
      intros.
      eapply hoare_cons.
      - apply iEntails_refl.
      - (* thanks to the v we can always introduce v = v as part of the
           result assertion which means we can later on use it to constrain
           the value w with the hoare_ctxS_iris' rule *)
        intro.
        eapply iEntails_trans.
        apply iSep_emp_l.
        apply iSep_mono.
        apply (iPure_intro (v = v)).
        reflexivity.
        apply iEntails_refl.
      - eapply (hoare_ctxS_iris'
                E
                (λ r, ⌜ Φ r ⌝ ∗ P' r)
                P
                e
                (λ w, λ r, ⌜ w = v ⌝ ∗ Q r)
                v
             )%S.
        + assumption.
        + intro.
          apply hoare_introS.
          intros.
          rewrite H1.
          assumption.
    Qed.

    Lemma iris_to_ctxSN E P' v P e Q:
      {{ P }} e {{ r, ⌜ r = v ⌝ ∗ P' r }} →
      {{ P' v }} (fill E (EVal v)) {{ERR: Q }}→
      {{ P }} (fill E e) {{ERR: Q }}.
    Proof.
      intros.
       eapply hoare_consN.
      - apply iEntails_refl.
      - (* thanks to the v we can always introduce v = v as part of the
           result assertion which means we can later on use it to constrain
           the value w with the hoare_ctxS_iris' rule *)
        intro.
        eapply iEntails_trans.
        apply iSep_emp_l.
        apply iSep_mono.
        apply (iPure_intro (v = v)).
        reflexivity.
        apply iEntails_refl.
      - eapply (hoare_ctxSN_iris'
                  E
                  (λ r, ⌜ r = v ⌝ ∗ P' r)
                  P
                  e
                  (λ r, ⌜ r = v ⌝ ∗ Q)
                  v)%S.
        + assumption.
        + intros.
          apply hoare_introN.
          intros.
          rewrite H1.
          (* here the problem is I can't take things out of the presumption,
             unless I can rewrite everything in wand form and this should be way
             faster instead. *)
          unfold hoare_err in *.
          intros ????.
          specialize (H0 m H2 mf H3) as [m' [e' (? & ? & ? & ?)]].
          exists m', e'.
          split; auto.
          split.
          * exists ∅, m'; split; auto.
            iUnfold; split; auto.
            split; auto.
            split.
            -- rewrite left_id_L. reflexivity.
            -- apply map_disjoint_empty_l.
          * split; auto.
    Qed.    
    
  End CTX.

  Lemma hoare_pure_step e' P e Q:
    pure_step e e' →
    {{ P }} e' {{ r, Q r }} →
    {{ P }} e  {{ r, Q r }}.
  Proof.
    intros.
    unfold hoare in *.
    intros.
    eapply iEntails_trans.
    apply H0.
    eauto using post_pure_step.
  Qed.

  Lemma hoare_pure_stepN (P : iProp) (e e' : expr) (Q : iProp):
    pure_step e e' → {{ P }} e' {{ERR: Q }} → {{ P }} e {{ERR: Q }}.
  Proof.
    intro.
    unfold hoare_err.
    eauto using post_pure_step, iEntails_trans, iEntails_refl.
  Qed.

  Lemma hoare_no_step e P:
    no_step e → {{ P }} e {{ERR: P}}.
  Proof.
    intros.
    apply post_no_step.
    assumption.
  Qed.

  (* Derived rules *)
  Lemma hoare_let P' v P Q e1 e2 s:
    {{ P }} e1 {{ r, ⌜ r = v ⌝ ∗ P' r }} →
    {{ P' v }} (subst s v e2) {{ r, Q r }} →
    {{ P }} ELet s e1 e2 {{ r, Q r }}.
  Proof.
    intros H0 H1.
    eapply (hoare_ctxS' [(LetCtx s e2)]).
    eassumption.
    simpl.
    eapply hoare_pure_step.
    - intro. eauto with astep.
    - assumption.
  Qed.

  Lemma hoare_letN P' P Q s e1 e2 v:
    {{ P }} e1 {{ r, ⌜ r = v ⌝ ∗ P' r }} →
    {{ P' v }} (subst s v e2) {{ERR: Q }} →
    {{ P }} (ELet s e1 e2) {{ERR: Q}}.
  Proof.
    intros H0 H1.
    eapply (hoare_ctxSN [(LetCtx s e2)]).
    eassumption.
    simpl.
    eapply hoare_pure_stepN.
    - intro. eauto with astep.
    - assumption.
  Qed.

  Lemma hoare_while P e Q t:
    {{ P }} EIf t (ESeq e (EWhile t e)) (EVal (VUnit)) {{ r, Q }} →
    {{ P }} EWhile t e {{ r, Q }}.
  Proof.
    unfold hoare.
    intros H v.
    eapply iEntails_trans.
    apply H.
    apply post_while.
  Qed.

  Lemma hoare_whileN P e Q t:
    {{ P }} EIf t (ESeq e (EWhile t e)) (EVal (VUnit)) {{ERR: Q }} →
    {{ P }} EWhile t e {{ERR: Q }}.
  Proof.
    unfold hoare_err.
    intros H.
    eapply iEntails_trans.
    apply H.
    apply post_while.
  Qed.

  Lemma hoare_seqS R P Q e1 e2 v:
    {{ P }} e1 {{ r, ⌜ r = v ⌝ ∗ R r }} →
    {{ R v }} e2 {{ r, Q r }} →
    {{ P }} (ESeq e1 e2) {{ r, Q r }}.
  Proof.
    intros.
    eapply (hoare_ctxS' [(SeqCtx e2)]); eauto.
    simpl.
    eapply hoare_pure_step.
    2: { eauto. }
    intro.
    eauto with astep.
  Qed.

  Lemma hoare_seqS' R P Q e1 e2:
    {{ P }} e1 {{ r, R }} →
    {{ R }} e2 {{ r, Q r }} →
    {{ P }} (ESeq e1 e2) {{ r, Q r }}.
  Proof.
    intros.
    eapply (hoare_ctxS_iris [(SeqCtx e2)] (λ _, R) P e1 Q); eauto.
    - intro.
      simpl.
      eapply hoare_pure_step.
      2: { eauto. }
      intro.
      eauto with astep.
  Qed.

  Lemma haore_seqN P Q e1 e2:
    {{ P }} e1 {{ERR: Q}} →
    {{ P }} ESeq e1 e2 {{ERR: Q }}.
  Proof.
    intros.
    eapply (hoare_ctxN  [(SeqCtx e2)]); eauto.
  Qed.

  Lemma hoare_seqSN R P Q e1 e2 v:
    {{ P }} e1 {{ r , ⌜ r = v ⌝ ∗ R r }} →
    {{ R v }} e2 {{ERR: Q }} →
    {{ P }} ESeq e1 e2 {{ERR: Q }}.
  Proof.
    intros.
    eapply (hoare_ctxSN [(SeqCtx e2)]); eauto.
    simpl.
    eapply hoare_pure_stepN.
    intro. eauto with astep.
    auto.
  Qed.

  Lemma hoare_op op v1 v2 v P:
    eval_bin_op op v1 v2 = Some v →
    {{ P }} (EOp op (EVal v1) (EVal v2)) {{ r, ⌜ r = v ⌝ ∗ P }}.
  Proof.
    unfold hoare.
    intros.
    apply iPure_elim.
    intros ->.
    auto using  post_op.
  Qed.

  Lemma hoare_if_true P' P Q t e1 e2:
    {{ P }} t {{ r, ⌜ r = VBool true ⌝ ∗ P' r }} →
    {{ P' (VBool true) }} e1 {{ r, Q r }} →
    {{ P }} EIf t e1 e2 {{ r, Q r }}.
  Proof.
    intros.
    eapply (hoare_ctxS' [(IfCtx e1 e2)]); eauto.
    simpl.
    eapply hoare_pure_step.
    - intro. eauto with astep.
    - assumption.
  Qed.

  Lemma hoare_if_trueN P' P Q t e1 e2:
    {{ P }} t {{ r, ⌜ r = VBool true ⌝ ∗ P' r }} →
    {{ P' (VBool true) }} e1 {{ERR: Q }} →
    {{ P }} EIf t e1 e2 {{ERR: Q }}.
  Proof.
    intros.
    eapply (hoare_ctxSN [(IfCtx e1 e2)]); eauto.
    - eapply hoare_pure_stepN; simpl.
      intro. eauto with astep.
      eassumption.
  Qed.

  Lemma hoare_if_false P' P Q t e1 e2:
    {{ P }} t {{ r, ⌜ r = VBool false ⌝ ∗ P' r }} →
    {{ P' (VBool false) }} e2 {{ r, Q r }} →
    {{ P }} EIf t e1 e2 {{ r, Q r }}.
  Proof.
    intros.
    eapply (hoare_ctxS' [(IfCtx e1 e2)]); eauto.
    simpl.
    eapply hoare_pure_step.
    - intro. eauto with astep.
    - assumption.
  Qed.

  Lemma hoare_if_falseN P' P Q t e1 e2:
    {{ P }} t {{ r, ⌜ r = VBool false ⌝ ∗ P' r }} →
    {{ P' (VBool false) }} e2 {{ERR: Q }} →
    {{ P }} EIf t e1 e2 {{ERR: Q }}.
  Proof.
    intros.
    eapply (hoare_ctxSN [(IfCtx e1 e2)]); eauto.
    - eapply hoare_pure_stepN; simpl.
      intro. eauto with astep.
      eassumption.
  Qed.

  Lemma hoare_error P:
    {{ P }} EError {{ERR: P }}.
  Proof.
    eauto using hoare_no_step, no_step_EError.
  Qed.

  Lemma hoare_frame_r R P Q e:
    {{ P }} e {{ r, Q r }} →
    {{ P ∗ R }} e {{ r, Q r ∗ R }}.
  Proof.
    intros.
    eapply hoare_cons.
    apply iSep_comm.
    intro.
    apply iSep_comm.
    simpl.
    eauto using hoare_frame_l.
  Qed.

  Lemma hoare_frame_rN R P Q e:
    {{ P }} e {{ERR: Q }} →
    {{ P ∗ R }} e {{ERR: Q ∗ R }}.
  Proof.
    intros.
    eapply hoare_consN.
    apply iSep_comm.
    intro.
    apply iSep_comm.
    simpl.
    eauto using hoare_frame_lN.
  Qed.

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
- [x] Create a document with all the primitive rules that you have proved
- [x] Write down the intuitive meaning of the wp/ewp and entailment
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
