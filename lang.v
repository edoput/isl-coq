From stdpp Require Export gmap.

(* A little expression language with naturals, booleans and heap
   locations for primitive values along with a small step semantic
   to reason about heap primitives. *)

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


(* The small step semantic gets in the way during longer proofs 
   and we need to define reductions not in head position anyway. *)


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


(* This lifts the head reductions to the rest of the AST by using
   the _empty context_ `[]` as a hole to fill and by using the other
   context items as the AST containing the hole *)

Inductive step : expr → mem → expr → mem → Prop :=
  | do_step E m1 m2 e1 e2 :
     head_step e1 m1 e2 m2 →
     step (fill E e1) m1 (fill E e2) m2.


(* Any expression can be the target of a _rewrite_ and these list makes
   it a little simpler on the typing. *)

Lemma fill_empty_context e : (fill [] e) = e.
Proof. auto. Qed.

Lemma step_single e e' m m':
  head_step e m e' m' → step e m e' m'.
Proof.
  intro.
  rewrite <- (fill_empty_context e).
  rewrite <- (fill_empty_context e').
  auto using step.
Qed.

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

Lemma step_prefix e e' m m':
  step e m e' m' ↔ ∃ E e1 e2, (fill E e1) = e ∧ (fill E e2) = e' ∧ step e1 m e2 m'.
Proof.
  split.
  - intro.
    inversion H.
    exists E, e1, e2; do 2 split; auto.
    auto using step_single.
  - intro. (* as (E & e1 & e2 & H).*)
    destruct H as (E & e1 & e2 & He1 & He2 & H).
    subst.
    auto using step_context.
Qed.
    
(* later on we can define is_error as an expression that does not step anymore
   and to actually get to prove errors about resources we need some lemmas
   to discharge this to assumptions on the heaps *)
Lemma step_alloc v l m:
      m !! l = None ↔ step (EAlloc (EVal v)) m (EVal (VLoc l)) (<[l:=v]> m).
Proof.
  split.
  - intro.
    change (EAlloc (EVal v)) with (fill []  (EAlloc (EVal v))).
    change (EVal (VLoc l)) with (fill [] (EVal (VLoc l))).
    econstructor.
    constructor.
    assumption.
  - intro.
    inversion H.
    destruct E.
    + rewrite fill_empty_context in *; subst.
      inversion H3.
      assumption.
    + simpl in *.
      destruct c; simpl in *; discriminate.
Qed.

Lemma step_alloc_inv e v m m':
  step (EAlloc (EVal v)) m e m' ↔ ∃ l, e = (EVal (VLoc l)) ∧ m !! l = None ∧ m' = <[l:=v]> m.
Proof.
  split; intro.
  - inversion H.
    destruct E.
    + simpl in *; subst.
      inversion H1.
      exists l.
      split; auto.
    + destruct c; simpl in *; discriminate || auto.
      * inversion H0.
        destruct E; simpl in *.
        subst e1.
        inversion H1.
        destruct c; simpl in *; discriminate.
  - destruct H as (loc & value & precondition & final_heap).
    subst.
    apply step_single.
    auto using head_step.
Qed.

Lemma step_free l m:
  m !! l ≠ None ↔ step (EFree (EVal (VLoc l))) m (EVal VUnit) (delete l m).
Proof.
  split.
  - intro.
    change (EFree (EVal (VLoc l))) with (fill [] (EFree (EVal (VLoc l)))).
    change (EVal VUnit) with (fill [] (EVal VUnit)).
    econstructor.
    constructor.
    assumption.
  - intro.
    inversion H.
    destruct E.
    + rewrite fill_empty_context in *; subst.
      inversion H3.
      assumption.
    + simpl in *.
      destruct c; simpl in *; discriminate.
Qed.

Lemma step_free_inv e l m m':
  step (EFree (EVal (VLoc l))) m e m' ↔ e = (EVal VUnit) ∧ m !! l ≠ None ∧ m' = delete l m.
Proof.
  split.
  - intro.
    inversion H.
    destruct E; simpl in *.
    + subst.
      inversion H1.
      split; auto.
    + destruct c; simpl in *; discriminate || auto.
      * inversion H0.
        destruct E; simpl in *; discriminate || auto.
        subst.
        inversion H1.
        destruct c; simpl in *; discriminate || auto.
  - intro.
    destruct H as (value & precondition & final).
    subst.
    apply step_single.
    constructor.
    assumption.
Qed.

Lemma step_load l v m:
  m !! l = Some(v) ↔ step (ELoad (EVal (VLoc l))) m (EVal v) m.
Proof.
  split.
  - intro.
    change (ELoad (EVal (VLoc l))) with (fill [] (ELoad (EVal (VLoc l)))).
    change (EVal v) with (fill [] (EVal v)).
    econstructor.
    constructor.
    assumption.
  - intro.
    inversion H.
    destruct E.
    + rewrite fill_empty_context in *; subst.
      inversion H3.
      assumption.
    + simpl in *.
      destruct c; simpl in *; discriminate.
Qed.

Lemma step_load_inv e l m m':
  step (ELoad (EVal (VLoc l))) m e m' ↔ ∃ v, e = (EVal v) ∧ m !! l = Some(v) ∧ m' = m.
Proof.
Admitted.

Lemma step_store l v m:
  m !! l ≠ None ↔ step (EStore (EVal (VLoc l)) (EVal v)) m (EVal VUnit) (<[l:=v]> m).
Proof.
  split.
  - intro.
    change (EStore (EVal (VLoc l)) (EVal v)) with (fill [] (EStore (EVal (VLoc l)) (EVal v))).
    change (EVal VUnit) with (fill [] (EVal VUnit)).
    econstructor.
    econstructor.
    assumption.
  - intro.
    inversion H.
    destruct E.
    + rewrite fill_empty_context in *; subst.
      inversion H3.
      assumption.
    + simpl in *.
      destruct c; simpl in *; discriminate || auto.
Qed.

Lemma step_store_inv l v e m m':
  step (EStore (EVal (VLoc l)) (EVal v)) m e m' ↔ m !! l ≠ None ∧ e = (EVal VUnit) ∧ m' = (<[l:=v]> m).
Proof.
Admitted.

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

Lemma fill_free e : (fill [FreeCtx] e) = (EFree e).
Proof. auto. Qed.

Lemma fill_load e : (fill [LoadCtx] e) = (ELoad e).
Proof. auto. Qed.

Lemma fill_store_l e1 e2 : (fill [StoreCtxL e2] e1) = (EStore e1 e2).
Proof. auto. Qed.

Lemma fill_store_r l e : (fill [StoreCtxR l] e) = (EStore (EVal l) e).
Proof. auto. Qed.

(* Now for the last part of our reductions we lift the _(one) step_
   relation between expressions to a zero or more _steps_ relation. *)

Inductive steps : expr → mem → expr → mem → Prop :=
  | steps_refl m e :
     steps e m e m
  | steps_step m1 m2 m3 e1 e2 e3 :
     step e1 m1 e2 m2 →
     steps e2 m2 e3 m3 →
     steps e1 m1 e3 m3.

(* It did not make sense to have this as a constructor of _steps_ 
   but having it is a _quality of life improvement_. *)
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

(* Now there are two _kind_ of multiple steps reduction that we might
   like to prove; one reduces to an _ composite expression_ and the other reduces to
   a _value expression_. The value expression is the result of the program
execution and the composite expression is just any intermediate step which is not a value; in any case we might want to compose more reductions into one and this makes it possible.

   Moreover as the only constructors for _steps_ are the _0 step_ and the _put one more step in front_ this is a quality of life improvement. *)

(* composing 0+ steps still yields 0+ steps *)
Lemma steps_mono e e' e'' h h' h'':
  steps e h e' h' → steps e' h' e'' h'' → steps e h e'' h''.
Proof.
  intros.
  induction H, H0; eauto using steps.
Qed.

(* But even with this _steps_mono_ lemma there are still some improvements we can have. steps mono cannot help us reducing an expression to a value in a let expression binding without applying it more than twice so here are some more lemmas about multiple steps reductions happening in your AST with a hole. *)

(* steps *)

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

Lemma steps_alloc_val e m m' v l:
  m' !! l = None →
  steps e m (EVal v) m' → steps (EAlloc e) m (EVal (VLoc l)) (<[l:=v]> m').
Proof.
  intros U H.
  eapply steps_mono.
  rewrite <- fill_alloc.
  eapply steps_context.
  eassumption.
  rewrite fill_alloc.
  auto using steps_single with head_step.
Qed.

Lemma steps_free_val e m m' l:
  m' !! l ≠ None →
  steps e m (EVal (VLoc l)) m' → steps (EFree e) m (EVal VUnit) (delete l m').
Proof.
  intros U H.
  eapply steps_mono.
  rewrite <- fill_free.
  eapply steps_context.
  eassumption.
  rewrite fill_free.
  auto using steps_single with head_step.
Qed.

Lemma steps_load_val e m m' l v:
  m' !! l = Some(v) →
  steps e m (EVal (VLoc l)) m' → steps (ELoad e) m (EVal v) m'.
Proof.
  intros U H.
  eapply steps_mono.
  rewrite <- fill_load.
  eapply steps_context.
  eassumption.
  rewrite fill_load.
  auto using steps_single with head_step.
Qed.

Lemma steps_store_val e e' m m' m'' l v:
  m'' !! l ≠ None →
  steps e m (EVal (VLoc l)) m' →
  steps e' m' (EVal v) m'' →
  steps (EStore e e') m (EVal VUnit) (<[l:=v]> m'').
Proof.
  intros U Hl Hr.
  eapply steps_mono.
  rewrite <- fill_store_l.
  eapply steps_context.
  eassumption.
  rewrite fill_store_l.
  eapply steps_mono.
  rewrite <- fill_store_r.
  eapply steps_context.
  eassumption.
  rewrite fill_store_r.
  auto using steps_single with head_step.
Qed.
