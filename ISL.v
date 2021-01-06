Require Export map.

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
