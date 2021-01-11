From stdpp Require Export gmap.

Require Export Arith String List Omega.
Export ListNotations.

Inductive val : Type :=
| VUnit : val
| VBool : bool -> val
| VNat : nat -> val
| VLoc : nat -> val.

Inductive bin_op : Type :=
  | PlusOp | MinusOp | LeOp | LtOp | EqOp.

Inductive expr : Type :=
| EVar : string -> expr
| EVal : val -> expr
| ELet : string -> expr -> expr -> expr
| ESeq : expr -> expr -> expr
| EOp : bin_op -> expr -> expr -> expr
| EIf : expr -> expr -> expr -> expr
| EWhile: expr -> expr -> expr
| EAlloc : expr -> expr
| EFree : expr -> expr
| ELoad : expr -> expr
| EStore : expr -> expr -> expr
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

Definition push_back : expr -> expr :=
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
Definition client : expr -> expr :=
  fun v =>
    (ELet "x" (ELoad v)
          (ESeq (push_back v) (* here the underlying storage for v might be moved *)
                (EStore (EVar "x") (EVal (VNat 88))))). (* so using the previous location might fault *)

Example example_client := client (EVal (VLoc 0)).
Check example_client.
Print example_client.
Compute example_client.


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

(* Our new heap model is still missing one operation we rely on, _mfresh_,
   to give us a location which is fresh and does not alias any previous one.

   Robbert also suggested to make the allocation non-deterministic to make
   it impossible to free a cell, invalidating the location, and immediately
   after allocate the same cell.
*)

Inductive head_step : expr -> mem -> expr -> mem -> Prop :=
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
     eval_bin_op op v1 v2 = Some v ->
     head_step (EOp op (EVal v1) (EVal v2)) m (EVal v) m
  | Alloc_headstep m v l:
     lookup l m = None ->
     head_step (EAlloc (EVal v)) m (EVal (VLoc l)) (insert l v m)
  | Free_headstep m l :
     lookup l m <> None ->
     head_step (EFree (EVal (VLoc l))) m (EVal VUnit) (delete l m)
  | Load_headstep m l v :
     lookup l m = (Some v) ->
     head_step (ELoad (EVal (VLoc l))) m (EVal v) m
  | Store_headstep m l v :
     lookup l m <> None ->
     head_step (EStore (EVal (VLoc l)) (EVal v)) m (EVal VUnit) (alter (fun _ => v) l m)
  (* new : the ambiguos expression reduces to any natural number *)
  | Amb_headstep m (n : nat):
     head_step EAmb m (EVal (VNat n)) m.

(* there is no reduction for incorrect expressions because we want to treat
   _stuck_ expressions as errors. This means that the **error** expression
   will not have a reduction for example but at the same time, if you cannot
   provide a proof that mlookup m l <> None then you cannot reduce
   EFree (EVal (VLoc l)) as it would be an error.
 *)

Create HintDb head_step.
Hint Constructors head_step : head_step.

Inductive ctx_item : Type :=
  | LetCtx : string -> expr -> ctx_item
  | SeqCtx : expr -> ctx_item
  | OpCtxL : bin_op -> expr -> ctx_item
  | OpCtxR : bin_op -> val -> ctx_item
  | IfCtx : expr -> expr -> ctx_item
  | AllocCtx : ctx_item
  | FreeCtx : ctx_item
  | LoadCtx : ctx_item
  | StoreCtxL : expr -> ctx_item
  | StoreCtxR : val -> ctx_item.

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

Inductive step : expr -> mem -> expr -> mem -> Prop :=
  | do_step E m1 m2 e1 e2 :
     head_step e1 m1 e2 m2 ->
     step (fill E e1) m1 (fill E e2) m2.

Inductive steps : expr -> mem -> expr -> mem -> Prop :=
  | steps_refl m e :
     steps e m e m
  | steps_step m1 m2 m3 e1 e2 e3 :
     step e1 m1 e2 m2 ->
     steps e2 m2 e3 m3 ->
     steps e1 m1 e3 m3.


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
Definition is_error e h := not (is_val e) /\ forall e' h', not (head_step e h e' h').


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
   we can move on to whole programs that contain an error
 *)
Definition contains_error e h := exists e' h', steps e h e' h' /\ is_error e' h'.

Example may_error :=
  (EIf (EOp EqOp EAmb (EVal (VNat 0)))
       EError
       (EVal VUnit)).

Lemma may_error_contains_error : forall m,  contains_error may_error m.
Proof.
  unfold contains_error, may_error.
  intros.
  eexists EError, m.
Admitted.


Lemma foo (xs : list nat) :
   1 + max_list xs ∉ xs.
Proof.
   assert (∀ x, x ∈ xs -> x < 1 + max_list xs).
   {
      intros x Hx.
      assert (x <= max_list xs); [|lia].
      apply max_list_elem_of_le. done.
   }
   intros Hin.
   specialize (H _ Hin). lia.
Qed.