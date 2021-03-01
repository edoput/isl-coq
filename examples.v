Require Export lang.
Require Export ISL.

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



Lemma client_can_error : will_error iEmpty client.
Proof.
  unfold will_error, client.
  exists empty.
  (* {[ 0 := (VNat 0) ]} ∪ {[ 1 := (VLoc 0) ]} ∪ {[ 2 := (VNat 42) ]}. *)
  exists ({[ 0 := Reserved ]} ∪ {[ 1 := (Value (VLoc 2)) ]} ∪ {[ 2 := (Value (VNat 42)) ]}).
  exists (EStore (EVal (VLoc 0)) (EVal (VNat 88))).
  split; [done |].
  split.
  - eapply steps_trans.
    eapply steps_let_val'.
    + apply steps_single.
      apply (Alloc_headstep ∅ (VNat 0) 0).
      unfold valid_alloc.
      intros e H.
      exfalso.
      eapply lookup_empty_is_Some.
      eexists e.
      eauto.
    + rewrite insert_empty.
      simpl subst.
      eapply steps_trans.
      eapply steps_let_val'.
      * apply steps_single.
        apply (Alloc_headstep {[0:= (Value (VNat 0))]} (VLoc 0) 1).
        unfold valid_alloc.
        rewrite lookup_singleton_ne.
        discriminate.
        auto.
      * simpl subst.
        rewrite insert_union_singleton_l.
        eapply steps_trans.
        eapply steps_let_val'.
        -- apply steps_single.
           econstructor.
           eapply lookup_union_Some; auto.
           rewrite map_disjoint_singleton_l. auto using lookup_singleton_None.
        -- simpl subst.
           eapply steps_seq_val'.
           ++ eapply steps_trans.
              eapply steps_let_val'.
              ** apply steps_single.
                 apply (Amb_headstep ({[1 := (Value (VLoc 0))]} ∪ {[0 := (Value (VNat 0))]}) 1).
              ** simpl subst.
                 eapply steps_trans.
                 apply steps_if_false'.
                 --- eauto using steps_single, head_step.
                 --- eapply steps_trans. apply steps_let_val'.
                     +++ eauto using steps_single, head_step.
                     +++ simpl subst.
                         eapply steps_seq_val'.
                         *** eauto using steps_single, head_step.
                         *** eapply steps_trans.
                             ---- apply steps_let_val'.
                                  apply steps_single.
                                  rewrite insert_union_r.
                                  rewrite insert_singleton.
                                  apply (Alloc_headstep ({[1 := Value (VLoc 0)]} ∪ {[0 := Reserved]}) (VNat 42) 2).
                                  unfold valid_alloc.
                                  intros.
                                  erewrite lookup_union_Some in H.
                                  destruct H as [H | H]; rewrite lookup_singleton_ne in H; discriminate.
                                  solve_map_disjoint.
                                  auto using lookup_singleton_ne.
                             ---- simpl subst.
                                  apply steps_single.
                                  eauto using head_step.
           ++ rewrite insert_commute; eauto.
              rewrite insert_union_l.
              rewrite insert_union_singleton_r.
              rewrite insert_singleton.
              assert (
                  ({[1 := Value (VLoc 2)]} ∪ {[0 := Reserved]} : mem)
                  =
                  ({[0 := Reserved]} ∪ {[1 := Value (VLoc 2)]})
              ).
              { admit. }
              assert (
                  ({[1 := Value (VLoc 2)]} ∪ {[0 := Reserved]} ∪ {[2 := Value (VNat 42)]}: mem)
                  =
                  ({[0 := Reserved]} ∪ {[1 := Value (VLoc 2)]} ∪ {[2 := Value (VNat 42)]})
              ).
              { admit. }
              rewrite H0.
              apply steps_refl.
              rewrite lookup_union_None.
              split; simpl_map; reflexivity.
  - unfold is_error.
    split.
    + auto.
    + intros.
      intro.
      erewrite step_store_inv in H. destruct H as (w & lookup_h & _ & _).
      do 2 erewrite lookup_union_Some in lookup_h.
      destruct lookup_h as [ [a|b] | c].
      * rewrite lookup_singleton in a.
        discriminate.
      * rewrite lookup_singleton_ne in b.
        discriminate.
        auto.
      * rewrite lookup_singleton_ne in c.
        discriminate.
        auto.
      * solve_map_disjoint.
      * solve_map_disjoint.
      * solve_map_disjoint.
Admitted.


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
     destruct H as (v & _ & lookup & _).
     rewrite lookup_empty in lookup.
     discriminate.
   Qed.

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
  destruct b; eauto using head_step.
Qed.
