From iris.proofmode Require Import tactics.
Ltac asimpl := simpl in *; simplify_eq.
Ltac inv H := inversion H; clear H; asimpl.

(* A little expression language with naturals, booleans and heap
   locations for primitive values along with a small step semantic
   to reason about heap primitives. *)

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
  | EAmb : expr
  | EError : expr.


(* now that the syntax is defined and I have written
   down the examples from the paper the semantics of this
   language is the next step; Robbert _stressed_ that we should
   give up on the big_step semantic and just focus on the
   small step one so that later on we can write down the Hoare
   triples using the small step.
 *)

(* ## Semantics of operators *)
Definition eval_bin_op (op : bin_op) (v₁ v₂ : val) : option val :=
  match op, v₁, v₂ with
  | PlusOp, VNat n₁, VNat n₂ => Some (VNat (n₁ + n₂))
  | MinusOp, VNat n₁, VNat n₂ => Some (VNat (n₁ - n₂))
  | LeOp, VNat n₁, VNat n₂ => Some (VBool (Nat.leb n₁ n₂))
  | LtOp, VNat n₁, VNat n₂ => Some (VBool (Nat.ltb n₁ n₂))
  | EqOp, VNat n₁, VNat n₂ => Some (VBool (Nat.eqb n₁ n₂))
  | EqOp, VBool n₁, VBool n₂ => Some (VBool (Bool.eqb n₁ n₂))
  | EqOp, VUnit, VUnit => Some (VBool true) (* new *)
  | EqOp, VLoc l₁, VLoc l₂ => Some (VBool (Nat.eqb l₁ l₂)) (* new *)
  | _, _, _ => None
  end.

(* ## Substitution *)
Fixpoint subst (x : string) (w : val) (e : expr) : expr :=
  match e with
  | EAmb => EAmb (* new *)
  | EVal v => EVal v
  | EVar y => if string_dec x y then EVal w else EVar y
  | ELet y e₁ e₂ =>
     if string_dec x y
     then ELet y (subst x w e₁) e₂
     else ELet y (subst x w e₁) (subst x w e₂)
  | ESeq e₁ e₂ => ESeq (subst x w e₁) (subst x w e₂)
  | EOp op e₁ e₂ => EOp op (subst x w e₁) (subst x w e₂)
  | EIf e₁ e₂ e3 => EIf (subst x w e₁) (subst x w e₂) (subst x w e3)
  | EWhile e₁ e₂ => EWhile (subst x w e₁) (subst x w e₂)
  | EAlloc e => EAlloc (subst x w e)
  | EFree e => EFree (subst x w e)
  | ELoad e => ELoad (subst x w e)
  | EStore e₁ e₂ => EStore (subst x w e₁) (subst x w e₂)
  | EError => EError
  end.

Inductive either :=
  | Value: val → either
  | Reserved : either.

Notation mem := (gmap nat either).

(* a valid allocation cell is one where there is no current Value *)
Definition valid_alloc (m : mem) (l : nat) := ∀ e, m !! l = Some e → e = Reserved.

Definition memfresh (m : mem) : nat := fresh (dom (gset nat) m).

Lemma memfresh_is_fresh m : lookup (memfresh m) m = None.
Proof.
  unfold memfresh. apply not_elem_of_dom, is_fresh.
Qed.

Inductive head_step : expr → mem → expr → mem → Prop :=
  | Let_headstep (m : mem) (y : string) (e : expr) (v : val):
     head_step (ELet y (EVal v) e) m (subst y v e) m
  | Seq_headstep (m : mem) (e : expr) (v : val):
     head_step (ESeq (EVal v) e) m e m
  | If_headstep_true (m : mem) (e₂ e₃ : expr):
     head_step (EIf (EVal (VBool true)) e₂ e₃) m e₂ m
  | If_headstep_false (m : mem) (e₂ e₃ : expr):
     head_step (EIf (EVal (VBool false)) e₂ e₃) m e₃ m
  | While_headstep (m : mem) (e₁ e₂ : expr):
     head_step (EWhile e₁ e₂) m (EIf e₁ (ESeq e₂ (EWhile e₁ e₂)) (EVal VUnit)) m
  | Op_headstep (m : mem) (op : bin_op) (v v₁ v₂ : val) :
     eval_bin_op op v₁ v₂ = Some v →
     head_step (EOp op (EVal v₁) (EVal v₂)) m (EVal v) m
  | Alloc_headstep (m : mem) (v : val) (l: nat):
     valid_alloc m l →
     head_step (EAlloc (EVal v)) m (EVal (VLoc l)) (<[ l := (Value v) ]> m)
  | Free_headstep (m : mem) (v : val) (l : nat):
     m !! l = Some (Value v) →
     head_step (EFree (EVal (VLoc l))) m (EVal VUnit) (<[l := Reserved ]> m)
  | Load_headstep (m : mem) (v : val) (l : nat):
     m !! l = Some (Value v) →
     head_step (ELoad (EVal (VLoc l))) m (EVal v) m
  | Store_headstep (m : mem) (v w : val) (l : nat):
     m !! l = Some (Value w) →
     head_step (EStore (EVal (VLoc l)) (EVal v)) m (EVal VUnit) (<[ l := (Value v) ]> m)
  | Amb_headstep (m : mem) (n : nat):
     head_step EAmb m (EVal (VNat n)) m.

(* there is no reduction for incorrect expressions because we want to treat
   _stuck_ expressions as errors. This means that the **error** expression
   will not have a reduction for example but at the same time, if you cannot
   provide a proof that mlookup m l <> None then you cannot reduce
   EFree (EVal (VLoc l)) as it would be an error.
 *)

Lemma Alloc_fresh_headstep (m : mem) (v : val) (l : nat):
  l = memfresh m →
  head_step (EAlloc (EVal v)) m (EVal (VLoc l)) (<[ l := (Value v)]> m).
Proof.
  intros ->.
  econstructor.
  unfold valid_alloc.
  intros e H.
  rewrite memfresh_is_fresh in H.
  discriminate.
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

Definition fill_item (K : ctx_item) (e : expr) : expr :=
  match K with
  | LetCtx s eₖ => ELet s e eₖ
  | SeqCtx eₖ => ESeq e eₖ
  | OpCtxL op eₖ => EOp op e eₖ
  | OpCtxR op v₁ => EOp op (EVal v₁) e
  | IfCtx e₂ e₃ => EIf e e₂ e₃
  | AllocCtx => EAlloc e
  | FreeCtx => EFree e
  | LoadCtx => ELoad e
  | StoreCtxL eₖ => EStore e eₖ
  | StoreCtxR v => EStore (EVal v) e
  end.

Fixpoint fill (K : ctx) (e : expr) : expr :=
  match K with
  | nil => e
  | K₁ :: K₂ => fill_item K₁ (fill K₂ e)
  end.


(* This lifts the head reductions to the rest of the AST by using
   the _empty context_ `[]` as a hole to fill and by using the other
   context items as the AST containing the hole *)

Inductive step : expr → mem → expr → mem → Prop :=
  | do_step (K : ctx) (m₁ m₂ : mem) (e₁ e₂ : expr) :
     head_step e₁ m₁ e₂ m₂ →
     step (fill K e₁) m₁ (fill K e₂) m₂.


(* Any expression can be the target of a _rewrite_ and these list makes
   it a little simpler on the typing. *)

Lemma fill_empty_context (e : expr) : (fill [] e) = e.
Proof. auto. Qed.

Lemma step_single (e e' : expr) (m m' : mem):
  head_step e m e' m' → step e m e' m'.
Proof.
  intro.
  rewrite <- (fill_empty_context e).
  rewrite <- (fill_empty_context e').
  auto using step.
Qed.

Lemma context_composition (e : expr) (K₁ K₂ : ctx) : fill K₁ (fill K₂ e) = fill (K₁ ++ K₂) e.
Proof.
  induction K₁.
  - auto using app_nil_l, fill_empty_context.
  - simpl. by f_equal.
Qed.

Lemma step_context (e e' : expr) (m m' : mem) (K : ctx) :
  step e m e' m' → step (fill K e) m (fill K e') m'.
Proof.
  intros [].
  rewrite !context_composition.
  auto using step.
Qed.

Lemma step_prefix (e e' : expr) (m m' : mem):
  step e m e' m' ↔ ∃ K e₁ e₂, fill K e₁ = e ∧ fill K e₂ = e' ∧ step e₁ m e₂ m'.
Proof.
  split.
  - intro. inv H. repeat eexists; eauto using step_single.
  - naive_solver (auto using step_context).
Qed.

Lemma step_error (e : expr) (m m' : mem):
  ¬ step EError m e m'.
Proof.
  intro. inv H. destruct K;[inv H1|destruct c;discriminate].
Qed.

(* later on we can define is_error as an expression that does not step anymore
   and to actually get to prove errors about resources we need some lemmas
   to discharge this to assumptions on the heaps *)

Lemma step_alloc (v :val) (l : nat) (m : mem) :
  step (EAlloc (EVal v)) m (EVal (VLoc l)) (<[l:= Value v]> m) ↔ valid_alloc m l.
Proof.
  split; intro H.
  - inv H.
    destruct K; asimpl.
    + by inv H3.
    + destruct c; asimpl.
  - apply step_single. by constructor.
Qed.

Lemma step_alloc_inv (e : expr) (v : val) (m m' : mem):
  step (EAlloc (EVal v)) m e m' ↔ ∃ l, e = (EVal (VLoc l)) ∧ valid_alloc m l ∧ m' = <[l := Value v]> m.
Proof.
  split; intro.
  - inv H. destruct K.
    + inv H1. eauto.
    + destruct c; asimpl. destruct K; asimpl; first inv H1.
      destruct c; asimpl.
  - destruct H as (? & -> & ? & ->).
    eauto using step_single, head_step.
Qed.

Lemma step_free (l : nat) (m : mem):
 step (EFree (EVal (VLoc l))) m (EVal VUnit) (<[l := Reserved ]> m) ↔ ∃ v, m !! l = (Some (Value v)).
Proof.
  split; intro.
  - inv H. destruct K; asimpl. inv H3. eauto. destruct c; asimpl.
  - destruct H. eauto using step_single, head_step.
Qed.

Lemma step_free_inv (e : expr) (l : nat) (m m': mem):
  step (EFree (EVal (VLoc l))) m e m' ↔ ∃ v, e = (EVal VUnit) ∧ m !! l = (Some (Value v)) ∧ m' = <[ l := Reserved ]> m.
Proof.
  split.
  - intro. inv H. destruct K; asimpl.
    + inv H1. eauto.
    + destruct c; asimpl. destruct K; asimpl. inv H1. destruct c; asimpl.
  - intros [v [-> [Hlookup ->]]].
    apply step_free; eauto.
Qed.

Lemma step_load (l : nat) (v : val)  (m : mem):
  step (ELoad (EVal (VLoc l))) m (EVal v) m ↔  m !! l = Some (Value v).
Proof.
  split; intro.
  - inv H. destruct K; asimpl. by inv H3. destruct c; asimpl.
  - eauto using step_single, head_step.
Qed.

Lemma step_load_inv (e : expr) (l : nat) (m m': mem):
  step (ELoad (EVal (VLoc l))) m e m' ↔ ∃ v, e = (EVal v) ∧ m !! l = (Some (Value v)) ∧ m' = m.
Proof.
  split.
  - intro. inv H. destruct K; asimpl.
    + inv H1. eauto.
    + destruct c; asimpl. destruct K; asimpl. inv H1. destruct c; asimpl.
  - intros [v [-> [Hlookup ->]]].
    apply step_load; auto.
Qed.

Lemma step_store (l : nat) (v : val) (m : mem):
  step (EStore (EVal (VLoc l)) (EVal v)) m (EVal VUnit) (<[l:= (Value v)]> m) ↔ ∃ w, m !! l = Some (Value w).
Proof.
  split; intro.
  - inv H. destruct K; asimpl. inv H3. eauto. destruct c; asimpl.
  - destruct H. eauto using head_step, step_single.
Qed.

Lemma step_store_inv (l : nat) (v : val) (e : expr) (m m' : mem):
  step (EStore (EVal (VLoc l)) (EVal v)) m e m' ↔ ∃ w, m !! l = (Some (Value w)) ∧ e = (EVal VUnit) ∧ m' = (<[l:= (Value v)]> m).
Proof.
   split.
  - intro. inv H.
    + destruct K; asimpl. { inv H1. eauto. }
      destruct c; asimpl. destruct K; asimpl. inv H1. destruct c; asimpl.
      destruct K; asimpl. inv H1. destruct c; asimpl.
  - intros [w (Hlookup & -> & ->)].
    apply step_store; eauto.
Qed.

Lemma fill_let (s : string) (e₁ e₂ : expr) : (fill [(LetCtx s e₂)] e₁) = (ELet s e₁ e₂).
Proof. auto. Qed.

Lemma fill_if (t e₁ e₂  : expr): (fill [(IfCtx e₁ e₂)] t) = (EIf t e₁ e₂).
Proof. auto. Qed.

Lemma fill_seq (e₁ e₂ : expr) : (fill [(SeqCtx e₂)] e₁) = (ESeq e₁ e₂).
Proof. auto. Qed.

Lemma fill_op_l (op : bin_op) (e₁ e₂ : expr) : (fill [(OpCtxL op e₂)] e₁) = (EOp op e₁ e₂).
Proof. auto. Qed.

Lemma fill_alloc (e : expr) : (fill [AllocCtx] e) = (EAlloc e).
Proof. auto. Qed.

Lemma fill_free (e : expr) : (fill [FreeCtx] e) = (EFree e).
Proof. auto. Qed.

Lemma fill_load (e : expr) : (fill [LoadCtx] e) = (ELoad e).
Proof. auto. Qed.

Lemma fill_store_l (e₁ e₂ : expr) : (fill [StoreCtxL e₂] e₁) = (EStore e₁ e₂).
Proof. auto. Qed.

Lemma fill_store_r (l : val) (e : expr): (fill [StoreCtxR l] e) = (EStore (EVal l) e).
Proof. auto. Qed.

(* Now for the last part of our reductions we lift the _(one) step_
   relation between expressions to a zero or more _steps_ relation. *)

Inductive steps : expr → mem → expr → mem → Prop :=
  | steps_refl m e :
     steps e m e m
  | steps_step m₁ m₂ m₃ e₁ e₂ e₃ :
     step e₁ m₁ e₂ m₂ →
     steps e₂ m₂ e₃ m₃ →
     steps e₁ m₁ e₃ m₃.

Lemma step_once (e₁ e₂ : expr) (m₁ m₂ : mem) :
  step e₁ m₁ e₂ m₂ -> steps e₁ m₁ e₂ m₂.
Proof.
  eauto using steps_step, steps_refl.
Qed.

(* It did not make sense to have this as a constructor of _steps_
   but having it is a _quality of life improvement_. *)
Lemma steps_single (e e' : expr) ( m m' : mem) : head_step e m e' m' → steps e m e' m'.
Proof.
  eauto using step_single, steps.
Qed.

(* Now there are two _kind_ of multiple steps reduction that we might
   like to prove; one reduces to an _ composite expression_ and the other reduces to
   a _value expression_. The value expression is the result of the program
execution and the composite expression is just any intermediate step which is not a value; in any case we might want to compose more reductions into one and this makes it possible.

   Moreover as the only constructors for _steps_ are the _0 step_ and the _put one more step in front_ this is a quality of life improvement. *)

(* composing 0+ steps still yields 0+ steps *)
Lemma steps_trans (e e' e'' : expr) (h h' h'' : mem):
  steps e h e' h' → steps e' h' e'' h'' → steps e h e'' h''.
Proof.
  intros. induction H, H0; eauto using steps.
Qed.

(* But even with this _steps_trans_ lemma there are still some improvements we can have. steps trans cannot help us reducing an expression to a value in a let expression binding without applying it more than twice so here are some more lemmas about multiple steps reductions happening in your AST with a hole. *)

(* steps *)

Lemma steps_context (K : ctx) (e e' : expr) (h h' : mem):
  steps e h e' h' → steps (fill K e) h (fill K e') h'.
Proof.
  induction 1; eauto using steps_trans, step_context, steps.
Qed.

Inductive is_ctx : list ctx_item -> Prop :=
  | is_LetCtx s e : is_ctx [LetCtx s e]
  | is_IfCtx e₁ e₂ : is_ctx [IfCtx e₁ e₂]
  | is_SeqCtx e : is_ctx [SeqCtx e]
  | is_OpCtxL e₁ e₂ : is_ctx [OpCtxL e₁ e₂]
  | is_AllocCtx : is_ctx [AllocCtx]
  | is_FreeCtx : is_ctx [FreeCtx]
  | is_LoadCtx : is_ctx [LoadCtx]
  | is_StoreCtxL e : is_ctx [StoreCtxL e]
  | is_StoreCtxR e : is_ctx [StoreCtxR e].

Lemma steps_contexta (K : ctx) (e e' : expr) (h h' : mem) (e₁ e₂ : expr) :
  is_ctx K → e₁ = fill K e → e₂ = fill K e' → steps e h e' h' → steps e₁ h e₂ h'.
Proof. intros ? -> ->. apply steps_context. Qed.

Create HintDb astep.
Hint Resolve step_single : astep.
Hint Resolve steps_contexta : astep.
Hint Constructors head_step : astep.
Hint Constructors steps : astep.
Hint Constructors is_ctx : astep.

Lemma steps_if_true (e₁ e₂ : expr) (m : mem) : steps (EIf (EVal (VBool true)) e₁ e₂) m e₁ m.
Proof.
  eauto with astep.
Qed.

Lemma steps_if_true' (t e₁ e₂ : expr) (m : mem) :
  steps t m (EVal (VBool true)) m →
  steps (EIf t e₁ e₂) m e₁ m.
Proof.
  eauto using steps_trans with astep.
Qed.

Lemma steps_if_false (e₁ e₂ : expr) (m : mem) : steps (EIf (EVal (VBool false)) e₁ e₂) m e₂ m.
Proof.
  eauto with astep.
Qed.

Lemma steps_if_false' (t e₁ e₂ : expr) (m : mem) :
  steps t m (EVal (VBool false)) m →
  steps (EIf t e₁ e₂) m e₂ m.
Proof.
  eauto using steps_trans with astep.
Qed.

(* as long as there is no errors when evaluating the binding [(s e₁)] then
   we know that the value of v can be substituted along in expression e₂ *)
Lemma steps_let_val (e : expr) (m : mem) (s : string) (v : val):
  steps (ELet s (EVal v) e) m (subst s v e) m.
Proof.
  eauto with astep.
Qed.

Lemma steps_let_val' (e₁ e₂ : expr) (m m' : mem) (s : string) (v : val):
  steps e₁ m (EVal v) m' → steps (ELet s e₁ e₂) m (subst s v e₂) m'.
Proof.
  intro.
  eapply steps_trans. eapply steps_contexta; [eapply is_LetCtx|..]; eauto.
  simpl. eauto with astep.
Qed.

Lemma steps_seq_val (e e' : expr) (v : val) (m m' : mem):
  steps e m e' m' → steps (ESeq (EVal v) e) m e' m'.
Proof.
  eauto with astep.
Qed.

Lemma steps_seq_val' (e e' e'' : expr) (m m' m'' : mem) (v : val):
  steps e m (EVal v) m' → steps e' m' e'' m'' → steps (ESeq e e') m e'' m''.
Proof.
  intros.
  apply (steps_trans (ESeq e e') (ESeq (EVal v) e') e'' m m' m'').
  - eauto with astep.
  - eauto with astep.
Qed.

Lemma steps_alloc_val (e : expr) (m m' : mem) (v : val) (l : nat):
  valid_alloc m' l →
  steps e m (EVal v) m' → steps (EAlloc e) m (EVal (VLoc l)) (<[l:=(Value v)]> m').
Proof.
  intros U H.
  eapply steps_trans.
  rewrite <- fill_alloc.
  eapply steps_context.
  eassumption.
  eauto with astep.
Qed.

Lemma steps_free_val (e : expr) (m m' : mem) (l : nat) (v : val):
   m' !! l = Some (Value v) →
  steps e m (EVal (VLoc l)) m' → steps (EFree e) m (EVal VUnit) (<[ l := Reserved ]> m').
Proof.
  intros U H.
  eapply steps_trans.
  rewrite <- fill_free.
  eapply steps_context.
  eassumption.
  eauto with astep.
Qed.

Lemma steps_load_val (e : expr) (m m' : mem) (l : nat) (v : val):
  m' !! l = Some (Value v) →
  steps e m (EVal (VLoc l)) m' → steps (ELoad e) m (EVal v) m'.
Proof.
  intros U H.
  eapply steps_trans.
  rewrite <- fill_load.
  eapply steps_context.
  eassumption.
  eauto with astep.
Qed.

Lemma steps_store_val (e e' : expr) (m m' m'' : mem) (l : nat) (v w : val):
  m'' !! l = Some (Value w) →
  steps e m (EVal (VLoc l)) m' →
  steps e' m' (EVal v) m'' →
  steps (EStore e e') m (EVal VUnit) (<[l:= (Value v)]> m'').
Proof.
  intros U Hl Hr.
  eapply steps_trans.
  rewrite <- fill_store_l.
  eapply steps_context.
  eassumption.
  rewrite fill_store_l.
  eapply steps_trans.
  rewrite <- fill_store_r.
  eapply steps_context.
  eassumption.
  rewrite fill_store_r.
  eauto using steps_single with head_step.
Qed.


Definition is_val (e : expr) :=
  match e with
  | EVal _ => true
  | _ => false
  end.

(* our expression is an error when we cannot step anymore in the reduction *)
Definition is_error (e : expr) (m : mem) := not (is_val e) ∧ ∀ e' m', not (step e m e' m').

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

Lemma head_step_fill_item_val (K : ctx_item) (e e' : expr) (m m' : mem) :
  head_step (fill_item K e) m e' m' → is_val e.
Proof.
  destruct K; simpl; intros H; inversion H; done.
Qed.

Lemma fill_item_eq_val (k₁ k₂: ctx_item) (e₁ e₂ : expr) :
  fill_item k₁ e₁ = fill_item k₂ e₂ →
  e₁ = e₂ ∨ is_val e₁ ∨ is_val e₂.
Proof.
  destruct k₁,k₂ ; simpl; intro; simplify_eq; eauto.
Qed.

Lemma head_step_not_val (e₁ e₂ : expr) (m₁ m₂ : mem) :
  head_step e₁ m₁ e₂ m₂ → is_val e₁ → False.
Proof.
  intros Hs?. by inversion Hs; subst.
Qed.

Lemma is_val_fill (e : expr) (K : ctx) :
  is_val (fill K e) → is_val e.
Proof.
  destruct K; eauto. by destruct c.
Qed.

Lemma fill_item_not_val (e : expr) (a : ctx_item) :
  ¬ is_val (fill_item a e).
Proof.
  destruct a; eauto.
Qed.

Lemma is_error_fill_item (e : expr) (h : mem) (a : ctx_item) :
  is_error e h → is_error (fill_item a e) h.
Proof.
  intros [Hv Hs].
  split; eauto using fill_item_not_val.
  intros e' h' H. inversion H. clear H. subst.
  induction K; simpl in *. subst.
  - eauto using head_step_fill_item_val.
  - apply fill_item_eq_val in H0 as [|[]];
    eauto using is_val_fill, head_step_not_val.
    subst. eapply Hs. constructor. done.
Qed.

Lemma is_error_fill (e : expr) (h : mem) (E : ctx) :
  is_error e h → is_error (fill E e) h.
Proof.
  induction E; simpl; eauto using is_error_fill_item.
Qed.
