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