From iris.bi Require Import bi.
Require Export lang.

(* now that we have the starting point of our operational semantic
   I can focus on what it means for an expression to be an error.
   All our examples are syntactically correct (or should be) and
   the types check out so we are referring to be _semantically
   correct_ (?). The usage of resources in our program is correct
   if we can always reduce an expression to a value so any
   expression that does not reduce to a value will contain
   a resource error or an **error** form.
 *)

Definition is_val e :=
  match e with
  | EVal _ => true
  | _ => false
  end.

(* our expression is an error when we cannot step anymore in the reduction *)
Definition is_error e h := not (is_val e) ∧ ∀ e' h', not (step e h e' h').

Lemma head_step_fill_item_val a e e' h h' :
  head_step (fill_item a e) h e' h' → is_val e.
Proof.
  destruct a; simpl; intros H; inversion H; done.
Qed.

Lemma fill_item_eq_val a1 a2 e1 e2 :
  fill_item a1 e1 = fill_item a2 e2 →
  e1 = e2 ∨ is_val e1 ∨ is_val e2.
Proof.
  destruct a1,a2; simpl; intro; simplify_eq; eauto.
Qed.

Lemma head_step_not_val e1 e2 h1 h2 :
  head_step e1 e2 h1 h2 → is_val e1 → False.
Proof.
  intros Hs?. by inversion Hs; subst.
Qed.

Lemma is_val_fill e E :
  is_val (fill E e) → is_val e.
Proof.
  destruct E; eauto. by destruct c.
Qed.

Lemma fill_item_not_val e a :
  ¬ is_val (fill_item a e).
Proof.
  destruct a; eauto.
Qed.

Lemma is_error_fill_item e h a :
  is_error e h → is_error (fill_item a e) h.
Proof.
  intros [Hv Hs].
  split; eauto using fill_item_not_val.
  intros e' h' H. inversion H. clear H. subst.
  induction E; simpl in *. subst.
  - eauto using head_step_fill_item_val.
  - apply fill_item_eq_val in H0 as [|[]];
    eauto using is_val_fill, head_step_not_val.
    subst. eapply Hs. constructor. done.
Qed.

Lemma is_error_fill e h E :
  is_error e h → is_error (fill E e) h.
Proof.
  induction E; simpl; eauto using is_error_fill_item.
Qed.

Example simple_error := is_error EError ∅.

Lemma our_first_error : simple_error.
Proof.
  unfold simple_error.
  split.
  - auto.
  - intros.
    unfold not.
    intro.
    (* now we got a proof of head_step for an expression EError
       which is not a thing in our operational semantic; the contradiction
       must come from there.
     *)
    inversion H.
    (* the inversion left us with an _unknown_ context E to work with
       but we still have the restriction that fill E e1 = EError; this
       only makes sense when E = [] and e1 = EError *)
    destruct E.
    * simpl in *; subst; inversion H1.
    * destruct c; simpl in *; discriminate.
Qed.

Lemma resource_error l: is_error (EFree (EVal (VLoc l))) ∅.
Proof.
  split; [auto|].
  intros ???H.
  erewrite step_free_inv in H.
  destruct H as (_ & lookup & _).
  rewrite lookup_empty in lookup.
  auto.
Qed.

(* Now that we have found what it means for an expression to be an error
   we can move on to whole programs that contain an error.

   An expression may reduce to many values and it's not just non determinism
   but control structures such _if_ and _while_. The idea we are after is that
   we need to prove something may error and we encode it as _there is one reduction
   path leading us to an error_.

   The alternative is that forall paths there is no error so we can now
   also describe correctness.
 *)
Definition contains_error e h := ∃ e' h', steps e h e' h' ∧ is_error e' h'.

Definition amb_bool := (EOp EqOp EAmb (EVal (VNat 0))).

Lemma amb_is_ambiguous (b : bool) (m : mem) : steps amb_bool m (EVal (VBool b)) m.
Proof.
  unfold amb_bool.
  eapply steps_step.
  rewrite <- fill_op_l.
  constructor.
  apply (Amb_headstep m (if b then 0 else 1)).
  rewrite fill_op_l.
  apply steps_single.
  destruct b; auto using head_step.
Qed.


Example may_error := (EIf amb_bool EError (EVal VUnit)).

Lemma may_error_contains_error : ∀ m,  contains_error may_error m.
Proof.
  unfold contains_error, may_error, amb_bool.
  intros.
  eexists EError, m.
  split.
  - apply (steps_step
             m m m
             (EIf (EOp EqOp EAmb (EVal (VNat 0))) EError (EVal VUnit))
             (EIf (EOp EqOp (EVal (VNat 0)) (EVal (VNat 0))) EError (EVal VUnit))).
    + change (EIf (EOp EqOp EAmb (EVal (VNat 0))) EError (EVal VUnit)) with
          (fill [(IfCtx EError (EVal VUnit)); (OpCtxL EqOp (EVal (VNat 0)))] EAmb).
      change (EIf (EOp EqOp (EVal (VNat 0)) (EVal (VNat 0))) EError (EVal VUnit)) with
          (fill [(IfCtx EError (EVal VUnit)); (OpCtxL EqOp (EVal (VNat 0)))] (EVal (VNat 0))).
      constructor.
      constructor.
    + apply (steps_step
             m m m
             (EIf (EOp EqOp (EVal (VNat 0)) (EVal (VNat 0))) EError (EVal VUnit))
             (EIf (EVal (VBool true)) EError (EVal VUnit))).
      * change (EIf (EOp EqOp (EVal (VNat 0)) (EVal (VNat 0))) EError (EVal VUnit)) with
            (fill [(IfCtx EError (EVal VUnit))] (EOp EqOp (EVal (VNat 0)) (EVal (VNat 0)))).
        change (EIf (EVal (VBool true)) EError (EVal VUnit)) with
            (fill [(IfCtx EError (EVal VUnit))] (EVal (VBool true))).
        constructor.
        constructor.
        simpl.
        reflexivity.
      * apply steps_if_true.
  - unfold is_error.
    split; auto.
    intros.
    intro.
    inversion H.
    destruct E; simpl in *.
    + subst.
      inversion H1.
    + destruct c; simpl in *; discriminate || auto.
Qed.

(* if an error state is reachable in a sub-expression then we might get lucky *)
Lemma contains_error_mono e e' h h' :
  steps e h e' h' → contains_error e' h' → contains_error e h.
Proof.
  intros.
  unfold contains_error in *.
  destruct H0. destruct H0. destruct H0.
  eexists x, x0.
  split; auto.
  eapply steps_mono; eassumption.
Qed.

Definition will_error (P : mem → Prop) (e : expr) := ∃ h h' e', P h ∧ steps e h e' h' ∧ is_error e' h'.

(* Notation "[[ P ]] e [[error]]" := (will_error P e). *)

Definition reaches (P : mem → Prop) (e : expr) (Q : val → mem → Prop) :=
  ∀ v h', Q v h' → ∃ h, P h ∧ steps e h (EVal v) h'.

Notation "[ P ] e [[ v , Q ]]" := (reaches P e (fun v => Q)).

Definition iEmpty (m : mem) := empty = m.

Example b := ([ iEmpty ] amb_bool [[ x , iEmpty ]]).

Definition under_approximation (P : mem → Prop) (e : expr) (Q : val → mem → Prop) :=
  will_error P e ∨ reaches P e Q.

Lemma client_can_error : will_error iEmpty client.
Proof.
  unfold will_error, client.
  exists empty.
  (* {[ 0 := (VNat 0) ]} ∪ {[ 1 := (VLoc 0) ]} ∪ {[ 2 := (VNat 42) ]}. *)
  exists ({[ 1 := (VLoc 2) ]} ∪ {[ 2 := (VNat 42) ]}).
  exists (EStore (EVal (VLoc 0)) (EVal (VNat 88))).
  split; [done |].
  split.
  - eapply steps_mono.
    eapply steps_let_val'.
    + apply steps_single.
      apply (Alloc_headstep ∅ (VNat 0) 0).
      auto using lookup_nil.
    + rewrite insert_empty.
      simpl subst.
      eapply steps_mono.
      eapply steps_let_val'.
      * apply steps_single.
        apply (Alloc_headstep {[0:= (VNat 0)]} (VLoc 0) 1).
        eapply lookup_insert_None; eauto using lookup_nil.
      * simpl subst.
        rewrite insert_union_singleton_l.
        eapply steps_mono.
        eapply steps_let_val'.
        -- apply steps_single.
           econstructor.
           eapply lookup_union_Some; auto.
           rewrite map_disjoint_singleton_l. auto using lookup_singleton_None.
        -- simpl subst.
           eapply steps_seq_val'.
           ++ eapply steps_mono.
              eapply steps_let_val'.
              ** apply steps_single.
                 apply (Amb_headstep ({[1 := VLoc 0]} ∪ {[0 := VNat 0]}) 1).
              ** simpl subst.
                 eapply steps_mono.
                 apply steps_if_false'.
                 --- auto using steps_single, head_step.
                 --- eapply steps_mono. apply steps_let_val'.
                     +++ auto using steps_single, head_step.
                     +++ simpl subst.
                         eapply steps_seq_val'.
                         *** auto using steps_single, head_step.
                         *** eapply steps_mono.
                             ---- apply steps_let_val'.
                                  apply steps_single.
                                  rewrite delete_union.
                                  rewrite delete_singleton.
                                  rewrite delete_singleton_ne; auto.
                                  rewrite map_union_empty.
                                  auto using (Alloc_headstep {[1 := VLoc 0]} (VNat 42) 2), lookup_singleton_ne.
                             ---- simpl subst.
                                  apply steps_single.
                                  auto using head_step.
           ++ rewrite insert_commute; eauto.
              rewrite insert_singleton.
              rewrite insert_union_singleton_r.
              2: { rewrite lookup_singleton_ne; eauto. }
              eapply steps_refl.
  - unfold is_error.
    split.
    + auto.
    + intros.
      intro.
      erewrite step_store_inv in H. destruct H as (lookup_h & _ & _).
      apply lookup_h.
      apply lookup_union_None; auto using lookup_singleton_ne.
Qed.

Definition iProp := mem → Prop.
Definition iEmp : iProp := λ m, m = ∅.
Definition iPoints (l : nat) (v : val) : iProp := λ m, m = {[ l := v ]}.
Definition iNegPoints (l : nat) : iProp := λ m, m !! l = None.
Definition iSep (P Q : iProp) : iProp := λ m, ∃ m1 m2, P m1 ∧ Q m2 ∧ m = m1 ∪ m2 ∧ m1 ##ₘ m2 .
Definition iWand (P Q : iProp) : iProp := λ m, ∀ m', m ##ₘ m' → P m' → Q (m' ∪ m).
Definition iForall {A} (P : A → iProp) : iProp := λ m, ∀ x, P x m.
Definition iExists {A} (P : A → iProp) : iProp := λ m, ∃ x, P x m.
Definition iPure (φ : Prop) : iProp := λ m, φ ∧ m = ∅.
Definition iEntails (P Q : iProp) : Prop := ∀ m, P m → Q m.
Definition iOwn (m : mem) : iProp := λ m', m' = m.

Notation "P ⊢ Q" := (iEntails P Q) (at level 99, Q at level 200).
Notation "P ∗ Q" := (iSep P Q) (at level 80, right associativity).
Notation "l ↦ v" := (iPoints l v) (at level 20).
Notation "'emp'" := iEmp.
Notation "P -∗ Q" := (iWand P Q) (at level 99, Q at level 200, right associativity).
Notation "⌜ p ⌝" := (iPure p) (at level 1, p at level 200).
Notation "'All' x1 .. xn , P" :=
  (iForall (fun x1 => .. (iForall (fun xn => P)) ..))
  (at level 200, x1 binder, xn binder, right associativity).
Notation "'Ex' x1 .. xn , P" :=
  (iExists (fun x1 => .. (iExists (fun xn => P)) ..))
  (at level 200, x1 binder, xn binder, right associativity).


Ltac iUnfold := unfold iEmp, iPoints, iSep, iWand, iForall, iExists, iPure, iEntails.
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

Lemma iForall_intro {A} P (Q : A → iProp) : (∀ x, P ⊢ Q x) → (P ⊢ All x, Q x).
Proof. duh. Qed.

Lemma iForall_elim {A} (P : A → iProp) x : (All z, P z) ⊢ P x.
Proof. duh. Qed.

Lemma iExist_intro {A} (P : A → iProp) x : P x ⊢ Ex z, P z.
Proof. duh. Qed.

Lemma iExist_elim {A} (P : A → iProp) Q :  (∀ x, P x ⊢ Q) → (Ex z, P z) ⊢ Q.
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

Lemma iExist_sep {A} (P : A → iProp) Q : (Ex x, P x) ∗ Q ⊢ Ex x, P x ∗ Q.
Proof. duh. Qed.

Lemma iPure_intro (φ : Prop) : φ → emp ⊢ ⌜ φ ⌝.
Proof. duh. Qed.

Lemma iPure_elim (φ : Prop) P Q : (φ → P ⊢ Q) → ⌜ φ ⌝ ∗ P ⊢ Q.
Proof. duh. Qed.

(*
  It's not very clear to me how to write those as iProps.
  The iReaches seems plausible to me, but iError IDK.
  Maybe will_error should just be a Prop?
  Maybe it should have a postcondition like in the paper?
  Maybe you can take a look at how they do a complete proof using the rules in the paper.
  Maybe that can be used to figure out how to do it using an analogue of WP in incorrectness logic.
 *)

(* The path from the lectures does not work as we _need_ P here (in wp)
   and definining hoare as P ⊢ wp P e Q obviously does not make all that sense;
   this is why we need to figure out an alternative of WP in incorrectness logic.

   Moreover we have to show that framing here happens in the reverse direction;
   for any frame mf in our _result_ the same frame must happen in the _assume_
   along with the correct anti-frame.
 *)

Definition wp (e : expr) (P : iProp) (v : val) : iProp :=
(* first attempt:  notice how we have the _disjoint_ predicate on the first
   this makes it possible to compose more _wp_ in the context while this one
   does not work.
*)
  λ m', ∀ mf, m' ##ₘ mf → (∃ m, m ##ₘ mf ∧ P m ∧ steps e (m ∪ mf) (EVal v) (m' ∪ mf)).
(*
   The important part of this is the m ##ₘ mf as it says there exists
   an anti-frame from which to start
 *)

(* fo there _error path_ we can mirror the definition but there are caveats
   that are implicit and I would like to point out.
   - asking m' ##ₘ mf → is_error e' (m' ∪ mf) is to have the _footprint_ of e be out of mf
*)
Definition ewp (e : expr) (P : iProp) : iProp :=
  λ m', ∀ mf, m' ##ₘ mf → (∃ m e', m ##ₘ mf ∧ P m ∧ steps e (m ∪ mf) e' (m' ∪ mf) ∧ is_error e' (m' ∪ mf)).

Lemma wp_frame P Q e v :
  Q ∗ wp e P v ⊢ wp e (Q ∗ P) v.
Proof.
  iUnfold.
  intros mT (m & m' & Hq & Hwp & -> & Hdisj) mf Hdisj'.
  unfold wp in *.
  edestruct (Hwp (m ∪ mf)) as (m0 & Hdisj'' & Hp & Hsteps).
  { solve_map_disjoint. }
  exists (m0 ∪ m).
  split. { solve_map_disjoint. }
  split. {
    do 2 eexists.
    split; first done.
    split; first done.
    split. { rewrite map_union_comm; solve_map_disjoint. }
    solve_map_disjoint.
  }
  rewrite !assoc in Hsteps.
  replace (m ∪ m') with (m' ∪ m); first done.
  rewrite map_union_comm; solve_map_disjoint.
Qed.

Lemma ewp_frame P Q e:
  Q ∗ ewp e P ⊢ ewp e (Q ∗ P).
Proof.
  iUnfold.
  intros mT (m & m' & Hq & Hewp & -> & Hdisj) mf Hdisj'.
  unfold ewp in *.
  assert (m' ##ₘ (m ∪ mf)).
  { solve_map_disjoint. }
  specialize (Hewp (m ∪ mf) H) as (m'' & e' & Hdisj'' & Hp & Hsteps & Herror).
  (* now in Hsteps we see that the frame contains the heap m satisfying Q
     but because of being disjoing we are gonna rewrite things to make Hsteps
     satisfy our goal *)
  exists (m ∪ m''), e'.
  split. solve_map_disjoint.
  split.
  exists m, m''; split; auto.
  split; auto.
  split; auto.
  solve_map_disjoint.
  rewrite ! map_union_assoc in Hsteps Herror.
  split.
  - rewrite (map_union_comm m'' m) in Hsteps.
    rewrite (map_union_comm m' m) in Hsteps.
    assumption.
    do 2 solve_map_disjoint.
    eapply map_disjoint_weaken_r.
    eassumption.
    apply map_union_subseteq_l.
  - rewrite (map_union_comm m m'); auto.
Qed.

(* the incorrectness triple is valid if for any state describe by (Q v)
   we can reach it from a state in P after executing P under final value v.

   Point wise entailment here represents the subset relation so (Q v) ⊂ wp e P v

   NB this is still correct for Q v = false as no heap satisfies false *)
Definition hoare (P : iProp) (e : expr) (Q : val -> iProp) v : Prop :=
  (Q v) ⊢ (wp e P v).

Lemma wp_val v (Q : val -> iProp) :
  (Q v) ⊢ wp (EVal v) (Q v) v.
Proof.
  iUnfold.
  intros.
  unfold wp.
  intros.
  eexists m.
  split; auto using steps_refl.
Qed.

(* how does this work with reducing anywhere in an expression? *)

Lemma wp_ctx E e P v w :
  wp (fill E (EVal w)) (wp e P w) v ⊢ wp (fill E e) P v.
Proof.
  unfold iEntails.
  intros.
  intros mf Hdisj.
  unfold wp in H at 1.
  specialize (H mf Hdisj) as (m' & Hdisj' & H' & Hsteps').
  specialize (H' mf Hdisj') as (m'' & Hdisj'' & H'' & Hsteps'').
  exists m''.
  split; auto.
  split; auto.
  eapply steps_mono.
  - apply steps_context.
    eassumption.
  - assumption.
Qed.


Lemma ewp_ctx E e P w:
  ewp (fill E (EVal w)) (wp e P w) ⊢ ewp (fill E e) P.
Proof.
  unfold iEntails.
  intros.
  intros mf Hdisj.
  specialize (H mf Hdisj) as (m' & e' & Hdisj' & H' & Hsteps' & Herror).
  specialize (H' mf Hdisj') as (m'' & Hdisj'' & H'' & Hsteps'').
  exists m'', e'.
  split; auto.
  split; auto.
  split; auto.
  eapply steps_mono.
  - apply steps_context.
    eassumption.
  - assumption.
Qed.

Lemma ewp_ctx' E e P:
  ewp e P ⊢ ewp (fill E e) P.
Proof.
  intros m H.
  intros mf Hdisj.
  specialize (H mf Hdisj) as (m' & e' & Hdisj' & H' & Hsteps' & Herror).
  exists m', (fill E e').
  split; auto.
  split; auto.
  split.
  - eapply steps_context; auto.
  - unfold is_error in *.
    destruct Herror as (not_a_value & cant_step).
    split.
    + induction E.
      * simpl; auto.
      * admit.
    + admit.
Admitted.

Lemma wp_let x v w e1 e2 P :
  wp (subst x w e2) (wp e1 P w) v ⊢ wp (ELet x e1 e2) P v.
Proof.
  intros m H.
  rewrite <- fill_let.
  eapply wp_ctx.
  simpl fill.
  intros mf Hdisj.
  destruct (H mf) as (m' & H' & Hdisj' & Hsteps); auto.
  exists m'.
  split; eauto.
  split; eauto.
  eapply steps_mono.
  - apply steps_let_val'.
    apply steps_refl.
  - auto.
Qed.

Lemma ewp_let x w e1 e2 P :
  ewp (subst x w e2) (wp e1 P w) ⊢ ewp (ELet x e1 e2) P.
Proof.
  intros m H.
  rewrite <- fill_let.
  eapply ewp_ctx.
  simpl fill.
  intros mf Hdisj.
  specialize (H mf Hdisj) as (m' & e' & Hdisj' & H & Hsteps & Herror).
  exists m', e'.
  split; auto.
  split; eauto.
  split.
  - eapply steps_mono.
    apply steps_let_val'.
    apply steps_refl.
    assumption.
  - assumption.
Qed.

Lemma wp_seq e1 e2 P w v:
  wp e2 (wp e1 P w) v ⊢ wp (ESeq e1 e2) P v.
Proof.
  intros m H.
  rewrite <- fill_seq.
  eapply wp_ctx.
  simpl fill.
  intros mf Hdisj.
  destruct (H mf) as (m' & H' & Hdisj' & Hsteps); auto.
  exists m'.
  split; eauto.
  split; eauto.
  eapply steps_mono.
  - apply steps_seq_val.
    apply steps_refl.
  - assumption.
Qed.

Lemma ewp_seq e1 e2 P:
  ewp e1 P ⊢ ewp (ESeq e1 e2) P.
Proof.
  intros m H.
  rewrite <- fill_seq.
  eapply ewp_ctx.
  simpl fill.
  intros mf Hdisj.
  specialize (H mf Hdisj) as (m' & e' & Hdisj' & H & Hsteps & Herror).
  exists m', e'.
  split; auto.
  split; eauto.
  admit.
Admitted.

Lemma ewp_seq' e1 e2 P w:
  ewp e2 (wp e1 P w) ⊢ ewp (ESeq e1 e2) P.
Proof.
  intros m H.
  rewrite <- fill_seq.
  eapply ewp_ctx.
  simpl fill.
  intros mf Hdisj.
  specialize (H mf Hdisj) as (m' & e' & Hdisj' & H & Hsteps & Herror).
  exists m', e'.
  split; auto.
  split; eauto.
  split; eauto using steps_seq_val.
Qed.

Lemma wp_if_true t e1 e2 P v:
  wp e1 (wp t P (VBool true)) v ⊢ wp (EIf t e1 e2) P v.
Proof.
  intros m H.
  rewrite <- fill_if.
  eapply wp_ctx.
  simpl fill.
  intros mf Hdisj.
  destruct (H mf) as (m' & H' & Hdisj' & Hsteps); auto.
  exists m'.
  split; eauto.
  split; eauto.
  eapply steps_mono; auto using steps_if_true.
Qed.

Lemma ewp_if_true t e1 e2 P:
  ewp e1 (wp t P (VBool true)) ⊢ ewp (EIf t e1 e2) P.
Proof.
  intros m H.
  rewrite <- fill_if.
  eapply ewp_ctx.
  simpl fill.
  intros mf Hdisj.
  specialize (H mf Hdisj) as (m' & e' & Hdisj' & H & Hsteps & Herror).
  exists m', e'.
  split; eauto.
  split; eauto.
  split; auto.
  eauto using steps_mono, steps_if_true.
Qed.

Lemma wp_if_false t e1 e2 P v:
  wp e2 (wp t P (VBool false)) v ⊢ wp (EIf t e1 e2) P v.
Proof.
  intros m H.
  rewrite <- fill_if.
  eapply wp_ctx.
  simpl fill.
  intros mf Hdisj.
  destruct (H mf) as (m' & H' & Hdisj' & Hsteps); auto.
  exists m'.
  split; eauto.
  split; eauto.
  eapply steps_mono; auto using steps_if_false.
Qed.

Lemma ewp_if_false t e1 e2 P:
  ewp e2 (wp t P (VBool false)) ⊢ ewp (EIf t e1 e2) P.
Proof.
  intros m H.
  rewrite <- fill_if.
  eapply ewp_ctx.
  simpl fill.
  intros mf Hdisj.
  specialize (H mf Hdisj) as (m' & e' & Hdisj' & H & Hsteps & Herror).
  exists m', e'.
  split; eauto.
  split; eauto.
  split; auto.
  eauto using steps_mono, steps_if_false.
Qed.

Lemma wp_while t e P v:
  wp (EIf t (ESeq e (EWhile t e)) (EVal VUnit)) P v ⊢ wp (EWhile t e) P v.
Proof.
  iUnfold.
  intros m H.
  intros mf Hdisj.
  specialize (H mf Hdisj) as (m' & Hdisj' & H' & Hsteps).
  exists m'.
  split; auto.
  split; auto.
  eapply steps_step.
  - rewrite <- (fill_empty_context (EWhile t e)).
    do 2 constructor.
  - auto using fill_empty_context.
Qed.

Lemma ewp_while t e P:
  ewp (EIf t (ESeq e (EWhile t e)) (EVal VUnit)) P ⊢ ewp (EWhile t e) P.
Proof.
  intros m H.
  intros mf Hdisj.
  specialize (H mf Hdisj) as (m' & t' & Hdisj' & H' & Hsteps & Herror).
  exists m', t'.
  split; auto.
  split; auto.
  split; auto.
  eapply steps_step.
  - rewrite <- (fill_empty_context (EWhile t e)).
    do 2 constructor.
  - auto using fill_empty_context.
Qed.

(* as the binary operations we have are all pure we don't care about the state of the heap
   but only when we sum values instead of expression *)
Lemma wp_op op v1 v2 v P:
  eval_bin_op op v1 v2 = Some v →
  P ⊢ wp (EOp op (EVal v1) (EVal v2)) P v.
Proof.
  intros Hop m HP mf Hdisj.
  exists m.
  split; auto.
  split; auto.
  eauto using steps_single, head_step.
Qed.

Lemma wp_error P :
  P ⊢ ewp EError P.
Proof.
  iUnfold.
  intros m Hp mf Hdisj.
  exists m, EError.
  split; auto.
  split; auto.
  split; auto using steps_refl.
  split; auto.
  intros e' m' H.
  inversion H.
  destruct E; simpl in *; discriminate || auto.
  - subst. inversion H1.
  - destruct c; simpl in *; discriminate || auto.
Qed.


Fail Lemma wp_alloc v P :
  iPure True ⊢ Ex l, P ∧ (fun m => m !! l = None) ∧ wp (EAlloc (EVal v)) P (VLoc l).

Lemma wp_alloc_neg l v P :
  iNegPoints l ⊢ wp (EAlloc (EVal v)) P (VLoc l).
Proof.
Admitted.

(* Maybe this is not necessary, subsumed by wp_ctx *)
Lemma wp_alloc_ctx e P l v:
  wp (EAlloc (EVal v)) (wp e P v) (VLoc l) ⊢ wp (EAlloc e) P (VLoc l).
Proof.
  intros m H mf Hdisj.
  specialize (H mf Hdisj) as (m' & Hdisj' & H & Hsteps').
  (* now it is implicit that m = <[l:v]> m' and the frame does not change
     as we are inserting in m ∪ mf but we only do it on the left
     thanks to insert_union_l *)
  specialize (H mf Hdisj') as (m'' & Hdisj'' & H & Hsteps'').
  exists m''.
  split; auto.
  split; auto.
  (* now to finally use the steps_alloc_val we have to prove
     m ∪ mf = <[l:=v]> (m' ∪ mf) = (<[l:=v]> m) ∪ mf which lies
     somewhere in the Hsteps' but for that we can make a lemma.
  *)
  eapply steps_mono.
  rewrite <- fill_alloc.
  eapply steps_context. eassumption.
  rewrite fill_alloc.
  assumption.
Qed.

Definition e := EAlloc (EVal (VNat 5)).
Lemma bar : iPure True ⊢ wp e emp (VLoc 0).
Proof.
  eapply iEntails_trans.
Admitted.

(* this should be doable with contains_error *)
Lemma ewp_alloc e P:
  ewp (EAlloc e) (ewp e P) ⊢ ewp (EAlloc e) P.
Proof.
Admitted.

(* this does not make much sense now as it describes resource exhaustion, in our
   assumptions there is no way to run out of cells to allocate.
*)
Lemma ewp_alloc' e P v:
  ewp (EAlloc (EVal v)) (wp e P v) ⊢ ewp (EAlloc e) P.
Proof.
Admitted.

Lemma wp_free e P l:
  wp (EFree (EVal l)) (wp e P l) VUnit ⊢ wp (EFree e) P VUnit.
Proof.
  intros m H mf Hdisj.
  specialize (H mf Hdisj) as (m' & Hdisj' & H & Hsteps).
  specialize (H mf Hdisj') as (m'' & Hdisj'' & H & Hsteps').
  exists m''.
  split; auto.
  split; auto.
  eapply steps_mono.
  rewrite <- fill_free.
  eapply steps_context.
  eassumption.
  rewrite fill_free.
  assumption.
Qed.

Lemma ewp_free e P l:
  ewp (EFree (EVal l)) (wp e P l) ⊢ ewp (EFree e) P.
Proof.
Admitted.

Lemma wp_store_val e P l v:
  wp (EStore (EVal l) (EVal v)) (wp e P v) VUnit ⊢
     wp (EStore (EVal l) e) P VUnit.
Proof.
  intros m H mf Hdisj.
  specialize (H mf Hdisj) as (m' & Hdisj' & H & Hsteps).
  specialize (H mf Hdisj') as (m'' & Hdisj'' & H & Hsteps').
  exists m''.
  split; auto.
  split; auto.
  eapply steps_mono.
  rewrite <- fill_store_r.
  eapply steps_context.
  eassumption.
  rewrite fill_store_r.
  assumption.
Qed.

Lemma ewp_store_val e P l v:
  ewp (EStore (EVal l) (EVal v)) (wp e P v) ⊢
     ewp (EStore (EVal l) e) P.
Proof.
Admitted.

Lemma wp_store_loc e P l v:
  wp (EStore (EVal l) (EVal v)) (wp e P l) VUnit ⊢
     wp (EStore e (EVal v)) P VUnit.
Proof.
  intros m H mf Hdisj.
  specialize (H mf Hdisj) as (m' & Hdisj' & H & Hsteps).
  specialize (H mf Hdisj') as (m'' & Hdisj'' & H & Hsteps').
  exists m''.
  split; auto.
  split; auto.
  eapply steps_mono.
  rewrite <- fill_store_l.
  eapply steps_context.
  eassumption.
  rewrite fill_store_l.
  assumption.
Qed.

Lemma ewp_store_loc e P l v:
  ewp (EStore (EVal l) (EVal v)) (wp e P l) ⊢
     ewp (EStore e (EVal v)) P.
Proof.
Admitted.

Lemma wp_load e P l v:
  wp (ELoad (EVal l)) (wp e P l) v ⊢
     wp (ELoad e) P v.
Proof.
  intros m H mf Hdisj.
  specialize (H mf Hdisj) as (m' & Hdisj' & H & Hsteps).
  specialize (H mf Hdisj') as (m'' & Hdisj'' & H & Hsteps').
  exists m''.
  split; auto.
  split; auto.
  eapply steps_mono.
  rewrite <- fill_load.
  eapply steps_context.
  eassumption.
  rewrite fill_load.
  assumption.
Qed.

Lemma ewp_load e P l:
  ewp (ELoad (EVal l)) (wp e P l) ⊢
     ewp (ELoad e) P.
Proof.
Admitted.

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
- [ ] Change definition of is_error to use step instead of head_step
- [ ] Create a new file in which we define Hoare triples in terms of wp/ewp
  ```
  Definition reaches (P : iProp) (e : expr) (Q : val → iProp) :=
    ∀ v, iEntails (Q v) (wp P e v).

  Definition has_error e := ∃ m, iOwn m ⊢ ewp emp e.
  ```
- [ ] Put all the rules for the Hoare triples from the paper as lemmas in that file (Admitted)
- [ ] Think about which additional rules for wp/ewp we need to prove all the rules in the paper using those lemmas
- [ ] Prove all the rules in the paper using the rules for wp/ewp
- [ ] Think about negative points to / the two alloc rules
- [ ] Clean up the rules, delete any rules that are subsumed by the ctx rules
- [ ] In the ISL paper can they prove this program can error
  ```
  x = alloc(3)
  y = alloc(3)
  if(x != y) then foo: Error
  ```


*)
