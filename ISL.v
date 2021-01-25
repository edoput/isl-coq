From stdpp Require Export gmap.
From iris.bi Require Import bi.

Require Export Arith String List Omega.
Export ListNotations.

Inductive val : Type :=
| VUnit : val
| VBool : bool → val
| VNat : nat → val
| VLoc : nat → val.

Inductive bin_op : Type :=
  | PlusOp | MinusOp | LeOp | LtOp | EqOp.

Inductive expr : Type :=
| EVar : string → expr
| EVal : val → expr
| ELet : string → expr → expr → expr
| ESeq : expr → expr → expr
| EOp : bin_op → expr → expr → expr
| EIf : expr → expr → expr → expr
| EWhile: expr → expr → expr
| EAlloc : expr → expr
| EFree : expr → expr
| ELoad : expr → expr
| EStore : expr → expr → expr
(* new *)
| EAmb : expr
| EError : expr.

(* in this example v is a (EVal (VLoc n))
   describing in the location in the heap where
   we will find a second location. In C parlance
   this would be a
   v ** int so a pointer to a vector of integers.

   In our case the underlying vector is just one cell
   so we can free and allocate just one to simulate
   a use after free bug later on.
 *)

Definition push_back : expr → expr :=
  fun v =>
    (ELet "z" EAmb
          (EIf (EOp EqOp (EVar "z") (EVal (VNat 0)))
               (EVal VUnit)
               (ELet "y" (ELoad v) (* now y points to the underlying array *)
                     (ESeq (EFree (EVar "y"))
                           (ELet "y" (EAlloc (EVal (VNat 42)))
                                 (EStore v (EVar "y"))))))).

Example example_push_back := push_back (EVal (VLoc 0)).
Check example_push_back.
Print example_push_back.
Compute example_push_back.

(* client is where we will trigger the use-after-free
   error as we get a hold of a location that might be
   deallocated
 *)
Definition client : expr :=
    (ELet "w" (EAlloc (EVal (VNat 0)))
          (ELet "v" (EAlloc (EVar "w"))

    (ELet "x" (ELoad (EVar "v"))
          (ESeq (push_back (EVar "v")) (* here the underlying storage for v might be moved *)
                (EStore (EVar "x") (EVal (VNat 88))))))). (* so using the previous location might fault *)

(* now that the syntax is defined and I have written
   down the examples from the paper the semantics of this
   language is the next step; Robbert _stressed_ that we should
   give up on the big_step semantic and just focus on the
   small step one so that later on we can write down the Hoare
   triples using the small step.
 *)

(* ## Semantics of operators *)
Definition eval_bin_op (op : bin_op) (v1 v2 : val) : option val :=
  match op, v1, v2 with
  | PlusOp, VNat n1, VNat n2 => Some (VNat (n1 + n2))
  | MinusOp, VNat n1, VNat n2 => Some (VNat (n1 - n2))
  | LeOp, VNat n1, VNat n2 => Some (VBool (Nat.leb n1 n2))
  | LtOp, VNat n1, VNat n2 => Some (VBool (Nat.ltb n1 n2))
  | EqOp, VNat n1, VNat n2 => Some (VBool (Nat.eqb n1 n2))
  | EqOp, VBool n1, VBool n2 => Some (VBool (Bool.eqb n1 n2))
  | EqOp, VUnit, VUnit => Some (VBool true) (* new *)
  | EqOp, VLoc l1, VLoc l2 => Some (VBool (Nat.eqb l1 l2)) (* new *)
  | _, _, _ => None
  end.

(* ## Substitution *)
Fixpoint subst (x : string) (w : val) (e : expr) : expr :=
  match e with
  | EAmb => EAmb (* new *)
  | EVal v => EVal v
  | EVar y => if string_dec x y then EVal w else EVar y
  | ELet y e1 e2 =>
     if string_dec x y
     then ELet y (subst x w e1) e2
     else ELet y (subst x w e1) (subst x w e2)
  | ESeq e1 e2 => ESeq (subst x w e1) (subst x w e2)
  | EOp op e1 e2 => EOp op (subst x w e1) (subst x w e2)
  | EIf e1 e2 e3 => EIf (subst x w e1) (subst x w e2) (subst x w e3)
  | EWhile e1 e2 => EWhile (subst x w e1) (subst x w e2)
  | EAlloc e => EAlloc (subst x w e)
  | EFree e => EFree (subst x w e)
  | ELoad e => ELoad (subst x w e)
  | EStore e1 e2 => EStore (subst x w e1) (subst x w e2)
  | EError => EError
  end.

(* our previous map definition was from nat to val so we might as well continue like this.
   The API for maps is defined in the stdpp documenation here https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.base.html#lab27
   and it boils down to

   Class Lookup (K A M : Type) := lookup: K → M → option A.
   Notation "m !! i" := (lookup i m) (at level 20) : stdpp_scope.

   Class SingletonM K A M := singletonM: K → A → M.
   Notation "{[ k := a ]}" := (singletonM k a) (at level 1) : stdpp_scope.

   Class Insert (K A M : Type) := insert: K → A → M → M.
   Notation "<[ k := a ]>" := (insert k a)
            (at level 5, right associativity, format "<[ k := a ]>") : stdpp_scope.

   Class Delete (K M : Type) := delete: K → M → M.

   Class Alter (K A M : Type) := alter: (A → A) → K → M → M.
 *)

(* Q: To keep track of the resources used and the underlying values we will never
   delete from this map but only alter the values to be None on delete.
 *)
Notation mem := (gmap nat val).

Definition memfresh (m : mem) : nat := fresh (dom (gset nat) m).

Lemma memfresh_is_fresh m : lookup (memfresh m) m = None.
Proof.
  unfold memfresh.
  apply not_elem_of_dom.
  apply is_fresh.
Qed.


Inductive head_step : expr → mem → expr → mem → Prop :=
  | Let_headstep m y e2 v1 :
     head_step (ELet y (EVal v1) e2) m (subst y v1 e2) m
  | Seq_headstep m e2 v1 :
     head_step (ESeq (EVal v1) e2) m e2 m
  | If_headstep_true m e2 e3 :
     head_step (EIf (EVal (VBool true)) e2 e3) m e2 m
  | If_headstep_false m e2 e3 :
     head_step (EIf (EVal (VBool false)) e2 e3) m e3 m
  | While_headstep m e1 e2 :
     head_step (EWhile e1 e2) m (EIf e1 (ESeq e2 (EWhile e1 e2)) (EVal VUnit)) m
  | Op_headstep m op v1 v2 v :
     eval_bin_op op v1 v2 = Some v →
     head_step (EOp op (EVal v1) (EVal v2)) m (EVal v) m
  | Alloc_headstep m v l:
     lookup l m = None →
     head_step (EAlloc (EVal v)) m (EVal (VLoc l)) (insert l v m)
  | Free_headstep m l :
     lookup l m <> None →
     head_step (EFree (EVal (VLoc l))) m (EVal VUnit) (delete l m)
  | Load_headstep m l v :
     lookup l m = (Some v) →
     head_step (ELoad (EVal (VLoc l))) m (EVal v) m
  | Store_headstep m l v :
     lookup l m <> None →
     head_step (EStore (EVal (VLoc l)) (EVal v)) m (EVal VUnit) (<[ l := v ]> m)
  (* new : the ambiguos expression reduces to any natural number *)
  | Amb_headstep m (n : nat):
     head_step EAmb m (EVal (VNat n)) m.

(* there is no reduction for incorrect expressions because we want to treat
   _stuck_ expressions as errors. This means that the **error** expression
   will not have a reduction for example but at the same time, if you cannot
   provide a proof that mlookup m l <> None then you cannot reduce
   EFree (EVal (VLoc l)) as it would be an error.
 *)

Lemma Alloc_fresh_headstep m l v:
      l = (memfresh m) →
      head_step (EAlloc (EVal v)) m (EVal (VLoc l)) (insert l v m).
Proof.
  intros ->.
  econstructor.
  apply memfresh_is_fresh.
  Qed.

Create HintDb head_step.
Hint Constructors head_step : head_step.

Inductive ctx_item : Type :=
  | LetCtx : string → expr → ctx_item
  | SeqCtx : expr → ctx_item
  | OpCtxL : bin_op → expr → ctx_item
  | OpCtxR : bin_op → val → ctx_item
  | IfCtx : expr → expr → ctx_item
  | AllocCtx : ctx_item
  | FreeCtx : ctx_item
  | LoadCtx : ctx_item
  | StoreCtxL : expr → ctx_item
  | StoreCtxR : val → ctx_item.

Notation ctx := (list ctx_item).

Definition fill_item (E : ctx_item) (e : expr) : expr :=
  match E with
  | LetCtx s e2 => ELet s e e2
  | SeqCtx e2 => ESeq e e2
  | OpCtxL op e2 => EOp op e e2
  | OpCtxR op v1 => EOp op (EVal v1) e
  | IfCtx e2 e3 => EIf e e2 e3
  | AllocCtx => EAlloc e
  | FreeCtx => EFree e
  | LoadCtx => ELoad e
  | StoreCtxL e2 => EStore e e2
  | StoreCtxR v1 => EStore (EVal v1) e
  end.

Fixpoint fill (E : ctx) (e : expr) : expr :=
  match E with
  | nil => e
  | E1 :: E2 => fill_item E1 (fill E2 e)
  end.

Inductive step : expr → mem → expr → mem → Prop :=
  | do_step E m1 m2 e1 e2 :
     head_step e1 m1 e2 m2 →
     step (fill E e1) m1 (fill E e2) m2.

(* Let's look at some automation for goals of shape step L m L' m' *)

(* the default is to use an empty context as (fill [] e) = e *)

Lemma fill_empty_context e : (fill [] e) = e.
Proof. auto. Qed.

Create HintDb step.
(* but for more specialized forms we can keep going *)

Lemma fill_let s e1 e2 : (fill [(LetCtx s e2)] e1) = (ELet s e1 e2).
Proof. auto. Qed.

Hint Extern 10 (step (ELet _ _ _) _ (ELet _ _ _) _) => rewrite <- 2 ! fill_let; econstructor : step.

(* let's try our automation *)
Lemma foo s : step (ELet s (EOp PlusOp (EVal (VNat 1)) (EVal (VNat 1)))
                            (EVar s)) empty
                   (ELet s (EVal (VNat 2)) (EVar s)) empty.
Proof.
  debug eauto with step head_step.
Qed.

Lemma fill_if t e1 e2 : (fill [(IfCtx e1 e2)] t) = (EIf t e1 e2).
Proof. auto. Qed.

Lemma fill_seq e1 e2 : (fill [(SeqCtx e2)] e1) = (ESeq e1 e2).
Proof. auto. Qed.

Lemma fill_op_l f e1 e2 : (fill [(OpCtxL f e2)] e1) = (EOp f e1 e2).
Proof. auto. Qed.

Lemma fill_alloc e : (fill [AllocCtx] e) = (EAlloc e).
Proof. auto. Qed.

Inductive steps : expr → mem → expr → mem → Prop :=
  | steps_refl m e :
     steps e m e m
  | steps_step m1 m2 m3 e1 e2 e3 :
     step e1 m1 e2 m2 →
     steps e2 m2 e3 m3 →
     steps e1 m1 e3 m3.

Lemma steps_single e e' m m' : head_step e m e' m' → steps e m e' m'.
Proof.
  intros.
  eapply steps_step.
  rewrite <- (fill_empty_context e).
  econstructor.
  eassumption.
  rewrite fill_empty_context.
  apply steps_refl.
Qed.

(* composing 0+ steps still yields 0+ steps *)
Lemma steps_mono e e' e'' h h' h'':
  steps e h e' h' → steps e' h' e'' h'' → steps e h e'' h''.
Proof.
  intros.
  induction H, H0; eauto using steps.
Qed.

(* now everything is nice and dandy and we can compose things nicely
   but I cannot take a steps reduction and shove it somewhere in the AST;
   steps reduction always start at the top of the AST. This is a limitation
   because during my proof construction I need to reason about sub-expressions
   and eventually construct a bigger reduction from a smaller reduction, e.g.
   for a If expression I cannot say much until I reason about the test but
   I can only manipulate a steps expression at the top node, the If.
 *)

Lemma context_composition e E E': fill E (fill E' e) = fill (E ++ E') e.
Proof.
  induction E.
  - auto using app_nil_l, fill_empty_context.
  - simpl. apply f_equal. assumption.
Qed.

Lemma step_context e e' m m' E :
  step e m e' m' → step (fill E e) m (fill E e') m'.
Proof.
  intro.
  destruct H.
  rewrite -> 2 context_composition.
  constructor.
  assumption.
Qed.

Lemma steps_context e e' h h' E :
  steps e h e' h' → steps (fill E e) h (fill E e') h'.
Proof.
  intro.
  induction H.
  constructor.
  eapply (steps_mono (fill E e1) (fill E e2) (fill E e3) m1 m2 m3).
  - econstructor.
    eauto using step_context.
    apply steps_refl.
  - assumption.
Qed.

(* very good now we can reduce left and right with as many steps as we may need
   so here are some nice reduction we might need from now on *)
Lemma steps_if_true e1 e2 m : steps (EIf (EVal (VBool true)) e1 e2) m e1 m.
Proof.
  econstructor.
  rewrite <- (fill_empty_context (EIf (EVal (VBool true)) e1 e2)).
  constructor.
  eauto using head_step.
  rewrite fill_empty_context.
  constructor.
Qed.

Lemma steps_if_true' t e1 e2 m : steps t m (EVal (VBool true)) m →
                                 steps (EIf t e1 e2) m e1 m.
Proof.
  intro.
  apply (steps_mono (EIf t e1 e2) (EIf (EVal (VBool true)) e1 e2) e1 m m m).
  - rewrite <- 2 fill_if; apply steps_context; assumption.
  - apply steps_if_true.
Qed.

Lemma steps_if_false e1 e2 m : steps (EIf (EVal (VBool false)) e1 e2) m e2 m.
Proof.
  econstructor.
  rewrite <- (fill_empty_context (EIf (EVal (VBool false)) e1 e2)).
  constructor.
  eauto using head_step.
  rewrite fill_empty_context.
  constructor.
Qed.

Lemma steps_if_false' t e1 e2 m : steps t m (EVal (VBool false)) m →
                                 steps (EIf t e1 e2) m e2 m.
Proof.
  intro.
  apply (steps_mono (EIf t e1 e2) (EIf (EVal (VBool false)) e1 e2) e2 m m m).
  - rewrite <- 2 fill_if; apply steps_context; assumption.
  - apply steps_if_false.
Qed.

(* as long as there is no errors when evaluating the binding [(s e1)] then
   we know that the value of v can be substituted along in expression e2 *)
Lemma steps_let_val e m s (v : val):
  steps (ELet s (EVal v) e) m (subst s v e) m.
Proof.
  - econstructor.
    rewrite <- (fill_empty_context (ELet s (EVal v) e)).
    do 2 econstructor.
    rewrite fill_empty_context.
    econstructor.
Qed.

Lemma steps_let_val' e1 e2 m m' s (v : val):
  steps e1 m (EVal v) m' → steps (ELet s e1 e2) m (subst s v e2) m'.
Proof.
  intro.
  apply (steps_mono (ELet s e1 e2) (ELet s (EVal v) e2) (subst s v e2) m m' m').
  - rewrite <- 2 fill_let; apply steps_context; assumption.
  - apply steps_let_val.
Qed.

Lemma steps_seq_val e e' v m m':
  steps e m e' m' → steps (ESeq (EVal v) e) m e' m'.
Proof.
  econstructor.
  rewrite <- (fill_empty_context (ESeq (EVal v) e)).
  econstructor.
  eauto with head_step.
  rewrite fill_empty_context.
  assumption.
Qed.

Lemma steps_seq_val' e e' e'' m m' m'' (v : val):
  steps e m (EVal v) m' → steps e' m' e'' m'' → steps (ESeq e e') m e'' m''.
Proof.
  intros.
  apply (steps_mono (ESeq e e') (ESeq (EVal v) e') e'' m m' m'').
  - rewrite <- 2 fill_seq; apply steps_context; assumption.
  - auto using steps_seq_val.
Qed.


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


(* This is our first attempt. an expression is an error when it's not
   a value and cannot be reduced anymore *)
Definition is_error e h := not (is_val e) ∧ ∀ e' h', not (head_step e h e' h').


Example simple_error := is_error EError ∅.

Lemma our_first_error : simple_error.
Proof.
  unfold simple_error, is_error.
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
Qed.

Lemma resource_error l: is_error (EFree (EVal (VLoc l))) ∅.
Proof.
  split; [auto|].
  intros ???H.
  inversion H.
  by rewrite lookup_empty in H1.
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
      inversion H.
      apply H5.
      apply lookup_union_None.
      split; apply lookup_singleton_ne; auto.
Qed.

Definition iProp := mem → Prop.
Definition iEmp : iProp := λ m, m = ∅.
Definition iPoints (l : nat) (v : val) : iProp := λ m, m = {[ l := v ]}.
Definition iSep (P Q : iProp) : iProp := λ m, ∃ m1 m2, P m1 ∧ Q m2 ∧ m = m1 ∪ m2 ∧ m1 ##ₘ m2 .
Definition iWand (P Q : iProp) : iProp := λ m, ∀ m', m ##ₘ m' → P m' → Q (m' ∪ m).
Definition iForall {A} (P : A → iProp) : iProp := λ m, ∀ x, P x m.
Definition iExists {A} (P : A → iProp) : iProp := λ m, ∃ x, P x m.
Definition iPure (φ : Prop) : iProp := λ m, φ ∧ m = ∅.
Definition iEntails (P Q : iProp) : Prop := ∀ m, P m → Q m.

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
  Intuitively, (iReaches P e v) means that:
    "There is a heap in P that makes e evaluate to v and the current heap."
*)
Definition iReaches (P : iProp) (e : expr) (v : val) : iProp :=
  λ m', ∃ m, P m ∧ steps e m (EVal v) m'.

Definition reaches' (P : iProp) (e : expr) (Q : val → iProp) :=
    ∀ v, iEntails (Q v) (iReaches P e v).

Lemma reaches_reaches' P e Q :
  reaches P e Q ↔ reaches' P e Q.
Proof. reflexivity. Qed.

Definition iError (P : iProp) (e : expr) : iProp :=
  λ m', ∃ m e', P m ∧ steps e m e' m' ∧ is_error e' m'.

Definition will_error' (P : iProp) (e : expr) :=
  ∃ m', iError P e m'.

Lemma will_error_will_error' P e :
  will_error P e ↔ will_error' P e.
Proof. split; intros (m1 & m2 & ?); by exists m2,m1. Qed.

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
  λ m', ∀ mf, m' ##ₘ mf → (∃ m, m ##ₘ mf ∧ P m ∧ steps e m (EVal v) m').
(*
   The important part of this is the m ##ₘ mf as it says there exists
   an anti-frame from which to start
*)

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

(* Lemma wp_while *)

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

Lemma wp_error v :
  ⌜ true ⌝ ⊢ wp EError ⌜ true ⌝ v.
Proof.
  intros m H mf Hdisj.
  exists m.
  split; auto.
  split; auto.
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
- [ ] finish the proof that client has an error according to #2
  + [ ] map_alter must have a theorem for union of maps, look it up
- [x] start working on the assertion language
  + [x] separating conjunction
  + [x] separating implication
  + [x] points to
  + [x] pure
  + [x] forall
  + [x] exists
- try to define the proof rules for ISL using the assertion language we have
  + CONS
  + SEQ
  + DISJ
  + more to come
- prove the proof rules sound
- figure out how to write the ISL Hoare triples in WP-style

*)
