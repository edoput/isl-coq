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

(* to unify the two definitions of wp/ewp later on we rely on this new predicate *)
Definition is_error_or_val (v : option val) (e : expr) (m : mem): Prop :=
  match v with
  | None => is_error e m
  | Some v => e = EVal v
end.

(* is_error relies on _step_ to say that an expression does not step
   but we only have an operational semantic for not stepping that works
   on head_step instead.

   This section is about lifting this idea of non stepping to expressions
   reducing in contexes.
*)

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

(* finally we can now start messing around with our definitions
   and prove that some expressions will error *)

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

(* and we can get errors also from using resources wrongly *)

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

(* the EAmb expression will only give us natural values but we are gonna use it
   to express non determinism by reducing in IfCtx
*)
Definition amb_bool := (EOp EqOp EAmb (EVal (VNat 0))).

(* and finally prove that we can always get any two booleans *)
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

(* now this example may error if the test evaluates to true *)
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

(* m' satisfies this predicate only if there exists m ∈ P such that m' is reachable while executing
   program e starting from m.

   As a program might error we encode this choice with the optional end value v; Some v encodes
   that the computation ended with value v while None encodes the fact that we are stuck in an
   error. *)
Definition post (e : expr) (P : iProp) (v : option val) : iProp :=
  λ m', ∀ mf, m' ##ₘ mf → (∃ m e', m ##ₘ mf ∧ P m ∧ steps e (m ∪ mf) e' (m' ∪ mf) ∧ is_error_or_val v e' (m' ∪ mf)).


Definition iEmp : iProp := λ m, m = ∅.
Definition iPoints (l : nat) (v : val) : iProp := λ m, m = {[ l := v ]}.
Definition iNegPoints (l : nat) : iProp := λ m, m !! l = None.
Definition iSep (P Q : iProp) : iProp := λ m, ∃ m1 m2, P m1 ∧ Q m2 ∧ m = m1 ∪ m2 ∧ m1 ##ₘ m2 .
Definition iWand (P Q : iProp) : iProp := λ m, ∀ m', m ##ₘ m' → P m' → Q (m' ∪ m).
Definition iAnd (P Q : iProp) : iProp := λ m, P m ∧ Q m.
Definition iOr (P Q : iProp) : iProp := λ m, P m ∨ Q m.
Definition iForall {A} (P : A → iProp) : iProp := λ m, ∀ x, P x m.
Definition iExists {A} (P : A → iProp) : iProp := λ m, ∃ x, P x m.
Definition iPure (φ : Prop) : iProp := λ m, φ ∧ m = ∅.
Definition iEntails (P Q : iProp) : Prop := ∀ m, P m → Q m.
Definition iOwn (m : mem) : iProp := λ m', m' = m.

Notation "P ⊢ Q" := (iEntails P Q) (at level 99, Q at level 200).
Notation "P ∗ Q" := (iSep P Q) (at level 80, right associativity).
Notation "P ∧ Q" := (iAnd P Q) (at level 80, right associativity).
Notation "P ∨ Q" := (iOr P Q) (at level 85, right associativity).
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


Ltac iUnfold := unfold iEmp, iPoints, iSep, iWand, iForall, iExists, iPure, iEntails, iAnd, iOr.
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


(* as we are working in incorrectness logic there is a shift in which relation there
   is between the presume P and the result Q of a triple.

   In incorrectness logic a triple [P]C[Q]is true when the post(C)P over approximate Q
   while for any over approximation logic the triple {P}C{Q} is true when post(C)P is a
   under approximation of Q.

   This inversion of the _subset of_ changes the entailment order: IL triples [P]C[Q] are expressed
   as Q ⊢ post(C)P while correctness triples {P}C{Q} are expressed as post(C)P ⊢ Q.

   For IL triples then the post(C)P set over approximates the set Q and this means that
   for any m ∈ Q there exists a m' ∈ P such that (m', m) ∈ [C].
 *)

(* The path from the lectures does not work as we _need_ P here (in wp)
   and definining hoare as P ⊢ wp P e Q obviously does not make all that sense;
   this is why we need to figure out an alternative of WP in incorrectness logic.

   Moreover we have to show that framing here happens in the reverse direction;
   for any frame mf in our _result_ the same frame must happen in the _assume_
   along with the correct anti-frame.
 *)

(* if we increase the set of initial states then we still cover all the final states *)
Lemma post_mono_presume P R e v:
  (P ⊢ R) → post e P v ⊢ post e R v.
Proof.
  intro.
  intros m HP.
  intros mf Hdisj.
  specialize (HP mf Hdisj) as (m' & e' & Hdisj' & HP & Hsteps).
  exists m', e'.
  eauto.
Qed.

(* if we shrink the set of final heap states then we still cover them all *)
Lemma post_mono_result P Q R e v:
  (R ⊢ Q) → (Q ⊢ post e P v) → (R ⊢ post e P v).
Proof.
  intros H HQ m HR.
  specialize (HQ m (H m HR)).
  assumption.
Qed.

Lemma post_disj_presume P Q R e v:
  (Q ⊢ post e P v) → (Q ⊢ post e R v) → (Q ⊢ post e (P ∨ R) v).
Proof.
  intros HP HR m HQ mf Hdisj.
  specialize (HP m HQ mf Hdisj) as (m' & e' & Hdisj' & HP & Hsteps).
  exists m', e'.
  split. assumption.
  split. apply iOr_intro_l. assumption.
  assumption.
Qed.

Lemma post_disj_result P Q R e v:
  (Q ⊢ post e P v) → (R ⊢ post e P v) → (Q ∨ R) ⊢ post e P v.
Proof.
  intros HQ HR m H.
  destruct H; auto using HQ, HR.
Qed.

Lemma post_frame P Q e v :
  Q ∗ post e P v ⊢ post e (Q ∗ P) v.
Proof.
  iUnfold.
  intros mT (m & m' & Hq & Hwp & -> & Hdisj) mf Hdisj'.
  unfold post in *.
  edestruct (Hwp (m ∪ mf)) as (m0 & e0 & Hdisj'' & Hp & Hsteps).
  { solve_map_disjoint. }
  exists (m0 ∪ m), e0.
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

(* the incorrectness triple is valid if for any state describe by (Q v)
   we can reach it from a state in P after executing P under final value v.

   Point wise entailment here represents the subset relation so (Q v) ⊂ wp e P v

   NB this is still correct for Q v = false as no heap satisfies false *)
Definition hoare (P : iProp) (e : expr) (Q : val -> iProp) v : Prop :=
  (Q v) ⊢ (post e P (Some v)).

Definition hoare_err (P Q : iProp) (e : expr) : Prop :=
  Q ⊢ (post e P None).

Lemma post_val v (Q : val -> iProp) :
  (Q v) ⊢ post (EVal v) (Q v) (Some v).
Proof.
  iUnfold.
  intros.
  intros mf Hdisj.
  eexists m, (EVal v).
  split; auto.
  split; auto.
  split; auto using steps_refl.
  simpl.
  reflexivity.
Qed.

(* how does this work with reducing anywhere in an expression? *)

Lemma post_ctx E e P v w :
  post (fill E (EVal w)) (post e P (Some w)) v ⊢ post (fill E e) P v.
Proof.
  intros m H mf Hdisj.
  specialize (H mf Hdisj) as (m' & e' & Hdisj' & H' & Hsteps' & Herror').
  specialize (H' mf Hdisj') as (m'' & e'' & Hdisj'' & H'' & Hsteps'' & Herror'').
  destruct v; simpl in *; subst.
  - exists m'', (EVal v).
    split; auto.
    split; auto.
    split; auto.
    eapply steps_mono.
    + apply steps_context.
      eassumption.
    + assumption.
  - exists m'', e'.
    split; auto.
    split; auto.
    split; auto.
    eapply steps_mono.
    + apply steps_context.
      eassumption.
    + assumption.
Qed.

Lemma post_ctx' E e P:
  post e P None ⊢ post (fill E e) P None.
Proof.
  intros m H mf Hdisj.
  specialize (H mf Hdisj) as (m' & e' & Hdisj' & H' & Hsteps' & Herror).
  simpl in *.
  exists m', (fill E e').
  split; auto.
  split; auto.
  eauto using steps_context, is_error_fill.
Qed.

Lemma post_load l v:
  l ↦ v ⊢ post (ELoad (EVal (VLoc l))) (l ↦ v) (Some v).
Proof.
  intros m H mf Hdisj.
  exists m, (EVal v).
  split; auto.
  split; auto.
  split.
  eapply steps_step.
  - apply step_load.
    apply lookup_union_Some_l.
    unfold iPoints in H.
    subst.
    apply lookup_singleton.
  - apply steps_refl.
  - simpl; reflexivity.
Qed.

Lemma post_load_err l:
  iNegPoints l ⊢ post (ELoad (EVal (VLoc l))) (iNegPoints l) None.
Proof.
  intros m H mf Hdisj.
  exists m, (ELoad (EVal (VLoc l))).
  split; auto.
  split; auto.
  split.
  - apply steps_refl.
  - simpl.
    unfold is_error.
    split; auto.
    intros e  m' Hstep.
    erewrite step_load_inv in Hstep.
    destruct Hstep as ( v & ( -> & Hm & _)).
    unfold iNegPoints in H.
    rewrite * lookup_union_Some in Hm by assumption.
    destruct Hm as [Hlookup_m | Hlookup_mf].
    + rewrite H in Hlookup_m.
      discriminate.
    + admit.
Admitted.
    
Lemma post_let x v w e1 e2 P :
  post (subst x w e2) (post e1 P (Some w)) v ⊢ post (ELet x e1 e2) P v.
Proof.
  intros m H.
  rewrite <- fill_let.
  eapply post_ctx.
  simpl fill.
  intros mf Hdisj.
  destruct (H mf) as (m' & e' & H' & Hdisj' & Hsteps & Hval); auto.
  exists m', e'.
  split; eauto.
  split; eauto.
  split; eauto.
  eapply steps_mono.
  - apply steps_let_val'.
    apply steps_refl.
  - auto.
Qed.

Lemma wp_seq e1 e2 P w v:
  post e2 (post e1 P (Some w)) v ⊢ post (ESeq e1 e2) P v.
Proof.
  intros m H.
  rewrite <- fill_seq.
  eapply post_ctx.
  simpl fill.
  intros mf Hdisj.
  destruct (H mf) as (m' &e' & H' & Hdisj' & Hsteps & Hval); auto.
  exists m', e'.
  split; eauto.
  split; eauto.
  split; eauto.
  eapply steps_mono.
  - apply steps_seq_val.
    apply steps_refl.
  - auto.
Qed.

Lemma post_if_true t e1 e2 P v:
  post e1 (post t P (Some (VBool true))) v ⊢ post (EIf t e1 e2) P v.
Proof.
  intros m H.
  rewrite <- fill_if.
  eapply post_ctx.
  simpl fill.
  intros mf Hdisj.
  specialize (H mf) as (m' & e' & H' & Hdisj' & Hsteps & H); auto.
  exists m', e'.
  split; eauto.
  split; eauto.
  split; eauto.
  eapply steps_mono; auto using steps_if_true.
Qed.

Lemma post_if_false t e1 e2 P v:
  post e2 (post t P (Some (VBool false))) v ⊢ post (EIf t e1 e2) P v.
Proof.
  intros m H.
  rewrite <- fill_if.
  eapply post_ctx.
  simpl fill.
  intros mf Hdisj.
  specialize (H mf) as (m' & e' & H' & Hdisj' & Hsteps & H); auto.
  exists m', e'.
  split; eauto.
  split; eauto.
  split; eauto.
  eapply steps_mono; auto using steps_if_false.
Qed.

Lemma wp_while t e P v:
  post (EIf t (ESeq e (EWhile t e)) (EVal VUnit)) P v ⊢ post (EWhile t e) P v.
Proof.
  iUnfold.
  intros m H.
  intros mf Hdisj.
  specialize (H mf Hdisj) as (m' & e' & Hdisj' & H' & Hsteps & H).
  exists m', e'.
  split; eauto.
  split; eauto.
  split; eauto.
  eapply steps_step.
  - rewrite <- (fill_empty_context (EWhile t e)).
    do 2 constructor.
  - auto using fill_empty_context.
Qed.


(* as the binary operations we have are all pure we don't care about the state of the heap
   but only when we sum values instead of expression *)
Lemma post_op op v1 v2 v P:
  eval_bin_op op v1 v2 = Some v →
  P ⊢ post (EOp op (EVal v1) (EVal v2)) P (Some v).
Proof.
  intros Hop m HP mf Hdisj.
  exists m, (EVal v).
  split; eauto.
  split; eauto.
  split; eauto.
  eauto using steps_single, head_step.
  simpl; auto.
Qed.

Lemma post_error P :
  P ⊢ post EError P None.
Proof.
  iUnfold.
  intros m Hp mf Hdisj.
  exists m, EError.
  split; auto.
  split; auto.
  split; auto using steps_refl.
  split; auto.
  intros e' m' H.
  apply <- step_error. eassumption.
Qed.


Fail Lemma wp_alloc v P :
  iPure True ⊢ Ex l, P ∧ (fun m => m !! l = None) ∧ wp (EAlloc (EVal v)) P (VLoc l).

Lemma wp_alloc e P l v:
  wp (EAlloc (EVal v)) (wp e P v) (VLoc l) ⊢ wp (EAlloc e) P (VLoc l).
Proof.
  rewrite <- fill_alloc.
  rewrite <- fill_alloc at 1.
  apply wp_ctx.
Qed.

Definition e := EAlloc (EVal (VNat 5)).
Lemma bar : iPure True ⊢ wp e emp (VLoc 0).
Proof.
  eapply iEntails_trans.
Admitted.

(* this does not make much sense now as it describes resource exhaustion, in our
   assumptions there is no way to run out of cells to allocate.
*)
Lemma ewp_alloc e P v:
  ewp (EAlloc (EVal v)) (wp e P v) ⊢ ewp (EAlloc e) P.
Proof.
  rewrite <- fill_alloc.
  rewrite <- fill_alloc at 1.
  apply ewp_ctx.
Qed.

(* this should be doable with contains_error *)
Lemma ewp_alloc' e P:
  (ewp e P) ⊢ ewp (EAlloc e) P.
Proof.
  intros m H.
  rewrite <- fill_alloc.
  apply ewp_ctx'.
  assumption.
Qed.

Lemma wp_free e P l:
  wp (EFree (EVal l)) (wp e P l) VUnit ⊢ wp (EFree e) P VUnit.
Proof.
  rewrite <- fill_free.
  rewrite <- fill_free at 1.
  apply wp_ctx.
Qed.

Lemma ewp_free e P l:
  ewp (EFree (EVal l)) (wp e P l) ⊢ ewp (EFree e) P.
Proof.
  rewrite <- fill_free.
  rewrite <- fill_free at 1.
  apply ewp_ctx.
Qed.

Lemma wp_store_val e P l v:
  wp (EStore (EVal l) (EVal v)) (wp e P v) VUnit ⊢
     wp (EStore (EVal l) e) P VUnit.
Proof.
  rewrite <- fill_store_r.
  rewrite <- fill_store_r at 1.
  apply wp_ctx.
Qed.

Lemma ewp_store_val e P l v:
  ewp (EStore (EVal l) (EVal v)) (wp e P v) ⊢
     ewp (EStore (EVal l) e) P.
Proof.
  rewrite <- fill_store_r.
  rewrite <- fill_store_r at 1.
  apply ewp_ctx.
Qed.

Lemma wp_store_loc e P l v:
  wp (EStore (EVal l) (EVal v)) (wp e P l) VUnit ⊢
     wp (EStore e (EVal v)) P VUnit.
Proof.
  rewrite <- fill_store_l.
  rewrite <- fill_store_l at 1.
  apply wp_ctx.
Qed.

Lemma ewp_store_loc e P l v:
  ewp (EStore (EVal l) (EVal v)) (wp e P l) ⊢
     ewp (EStore e (EVal v)) P.
Proof.
  rewrite <- fill_store_l.
  rewrite <- fill_store_l at 1.
  apply ewp_ctx.
Qed.

Lemma wp_load e P l v:
  wp (ELoad (EVal l)) (wp e P l) v ⊢
     wp (ELoad e) P v.
Proof.
  rewrite <- fill_load.
  rewrite <- fill_load at 1.
  apply wp_ctx.
Qed.

Lemma ewp_load e P l:
  ewp (ELoad (EVal l)) (wp e P l) ⊢
     ewp (ELoad e) P.
Proof.
  rewrite <- fill_load.
  rewrite <- fill_load at 1.
  apply ewp_ctx.
Qed.

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
- [ ] Prove the admitted rules for ∨ and ∧
- [ ] Refactor ewp/wp to use this option
- [ ] Define Hoare triples in terms of wp/ewp
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
