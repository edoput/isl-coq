Require Import String.
Open Scope string_scope.
Require Export lang.
From iris.bi Require Import bi.
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

 Definition push_back : expr → expr := λ v,
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

(*
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
 *)

(* Finally we can prove the same incorrectness specifications using the fancier rules *)
Lemma simple_error':
  hoare_err iEmp EError iEmp.
Proof.
  apply hoare_error.
Qed.

Lemma double_free l:
  hoare_err (iNegPoints l) (EFree (EVal (VLoc l))) (iNegPoints l).
Proof.
  apply hoare_freeN.
Qed.

Lemma double_free' l v:
  hoare_err (iPoints l v) (ESeq (EFree (EVal (VLoc l))) (EFree (EVal (VLoc l)))) (iNegPoints l).
Proof.
  eapply hoare_seqSN.
  eapply hoare_freeS.
  apply hoare_freeN.
Qed.

Lemma push_back_ok v a: hoare (∃ b,  v ↦ (VLoc a) ∗ a ↦ b)%S (push_back (EVal (VLoc v))) (λ r, ⌜ r = VUnit ⌝ ∗ ∃ a' b, v ↦ (VLoc a') ∗ a' ↦ b ∗ a ↦ ⊥ )%S.
Proof.
Admitted.

Lemma client_error: hoare_err iEmp client ( 0 ↦ ⊥ ∗ 1 ↦ (VLoc 2) ∗ 2 ↦ VNat 42)%S.
Proof.
  unfold client.
  eapply hoare_letN.
  - eapply (hoare_alloc1 0).
  - simpl.
    eapply (hoare_letN (λ l, 1 ↦ (VLoc 0) ∗ 0 ↦ (VNat 0)))%S.
    + eapply hoare_cons.
      apply iSep_emp_l_inv.
      intro. apply iSep_assoc.
      simpl.
      eapply hoare_frame_r.
      eapply (hoare_alloc1 1).
    + simpl.
      eapply hoare_consN.
      apply iSep_comm. apply iEntails_refl.
      eapply (hoare_letN (λ v, 0 ↦ VNat 0 ∗ 1 ↦ VLoc 0)%S).
      * eapply hoare_cons.
        apply iEntails_refl.
        intro. eapply iEntails_trans.
        apply iSep_comm.
        apply iSep_assoc'.
        apply hoare_frame_l.
        eapply hoare_cons. apply iEntails_refl.
        intro. apply iSep_comm. simpl.
        apply hoare_loadS.
      * simpl.
        eapply (hoare_seqSN (0 ↦ VNat 0 ∗ 1 ↦ VLoc 0)%S (λ l, 0 ↦ ⊥ ∗ 1 ↦ VLoc 2 ∗ 2 ↦ VNat 42)%S ).
        -- eapply hoare_let.
           ++ eapply hoare_cons.
              apply iSep_emp_r_inv. intro.
              apply iSep_comm. simpl.
              apply (hoare_frame_l (0 ↦ VNat 0 ∗ 1 ↦ VLoc 0))%S.
              apply (hoare_amb 1).
           ++ simpl.
              eapply hoare_if_false.
              ** eapply hoare_pure_step.
                 intro. eauto with astep.
                 simpl.
                 eapply hoare_cons.
                 apply iSep_emp_r_inv.
                 intro. apply iSep_comm. simpl.
                 apply (hoare_frame_l (0 ↦ VNat 0 ∗ 1 ↦ VLoc 0)%S).
                 apply hoare_val.
              ** simpl.
                 eapply (hoare_let (λ r, 0 ↦ VNat 0 ∗ 1 ↦ VLoc 0))%S.
                 --- eapply hoare_cons.
                     apply iEntails_refl.
                     intro. eapply iEntails_trans.
                     apply iSep_comm.  apply iSep_assoc'. simpl.
                     apply hoare_frame_l.
                     eapply hoare_cons.
                     apply iEntails_refl.
                     intro. apply iSep_comm. simpl.
                     apply hoare_loadS.
                 --- simpl.
                     eapply (hoare_seqS
                               (λ l, 0 ↦ ⊥ ∗ 1 ↦ VLoc 0)
                               (0 ↦ VNat 0 ∗ 1 ↦ VLoc 0))%S.
                     +++ eapply hoare_cons.
                         apply iEntails_refl.
                         intro. apply iSep_assoc. simpl.
                         apply hoare_frame_r.
                         apply hoare_freeS.
                     +++ eapply (hoare_let (λ l, 0 ↦ ⊥ ∗ 1 ↦ VLoc 0 ∗ 2 ↦ VNat 42))%S.
                         *** eapply hoare_cons.
                             eapply iEntails_trans.
                             2: { apply iSep_emp_r_inv. }
                             apply iSep_assoc.
                             intro.
                             eapply iEntails_trans.
                             apply iSep_comm.
                             eapply iEntails_trans.
                             apply iSep_assoc'.
                             apply iEntails_refl.
                             eapply (hoare_frame_l (0 ↦ ⊥))%S.
                             eapply hoare_cons.
                             apply iEntails_refl.
                             intro. apply iSep_assoc'. simpl.
                             apply hoare_frame_l.
                             eapply hoare_cons.
                             apply iEntails_refl.
                             intro. apply iSep_comm. simpl.
                             apply (hoare_alloc1 2).
                         *** simpl.
                             eapply hoare_cons.
                             apply iSep_assoc'.
                             intro.
                             eapply iEntails_trans.
                             apply iSep_assoc.
                             apply iSep_assoc.
                             apply hoare_frame_r.
                             eapply hoare_cons.
                             apply iEntails_refl.
                             intro.
                             eapply iEntails_trans.
                             apply iSep_assoc'.
                             eapply iEntails_trans.
                             apply iSep_comm.
                             apply iSep_assoc'. simpl.
                             apply hoare_frame_l.
                             eapply hoare_cons.
                             apply iEntails_refl.
                             intro. apply iSep_comm.
                             apply hoare_storeS.
        -- eapply hoare_consN.
           ++ apply iSep_comm.
           ++ apply iSep_comm.
           ++ apply hoare_frame_lN.
              apply hoare_storeN.
Qed.


Lemma distinct l l' v v' :
  l ↦ v ∗ l' ↦ v' ⊢ ⌜ l ≠ l' ⌝ ∗ iTrue.
Proof.
  intros m H.
  destruct H as (m1 & m2 & H1 & H2 & H & Hdisj).
  exists ∅, (m1 ∪ m2).
  split; eauto.
  - apply iPure_intro.
    + intro.
      iUnfold.
      eapply map_disjoint_spec.
      * eassumption.
      * subst m1.
        apply lookup_singleton.
      * subst m2.
        subst l.
        apply lookup_singleton.
    + reflexivity.
  - split; eauto.
    unfold iTrue.
    auto.
    + split; eauto.
      * rewrite left_id_L.
        assumption.
      * rewrite map_disjoint_union_r.
        split; apply map_disjoint_empty_l.
Qed.

Example pointers_are_distinct := (ELet "x" (EAlloc (EVal (VNat 3)))
                                          (ELet "y" (EAlloc (EVal (VNat 3)))
                                                (EIf (EOp EqOp (EVar "x") (EVar "y"))
                                                     (EVal VUnit)
                                                     EError))).


Lemma pointer_errors : hoare_err (emp)%S pointers_are_distinct (∃ x y, x ↦ (VNat 3) ∗ y ↦ (VNat 3))%S.
Proof.
  rewrite <- hoare_exists_forallN.
  intro n.
  rewrite <- hoare_exists_forallN.
  intro m.
  unfold pointers_are_distinct.
  (* the way to prove this error is that we are going to allocate stuff and the
     allocation will give us distinct pointers whose values will be substituted
     in the if expression and we gonna fault.
   *)
  eapply hoare_letN.
  - apply (hoare_alloc1 n).
  - simpl.
    eapply (hoare_letN (λ l, n ↦ VNat 3 ∗ m ↦ VNat 3)%S).
    + eapply hoare_cons.
      * apply iSep_emp_r_inv.
      * intro.
        eapply iEntails_trans.
        apply iSep_comm.
        apply iSep_assoc'.
      * simpl.
        eapply (hoare_frame_l (n ↦ VNat 3)%S).
        eapply hoare_cons.
        -- apply iEntails_refl.
        -- intro. apply iSep_comm.
        -- simpl.
           apply (hoare_alloc1 m).
    + simpl.
      apply (hoare_ctxSN [(IfCtx (EVal VUnit) EError)] (λ r, n ↦ VNat 3 ∗ m ↦ VNat 3)%S (VBool false)).
      * destruct (Nat.eq_dec n m).
        -- eapply hoare_cons.
             ++ apply iEntails_refl.
             ++ intro.
                eapply iEntails_trans.
                ** apply iSep_mono.
                   --- apply iEntails_refl.
                   --- apply distinct.
                ** apply iEntails_refl.
             ++ simpl.
                intros v h H.
                destruct H as (_ & _ & _ & (_ & _ & (H & _) & _) & _ & _).
                exfalso.
                auto.
        -- eapply hoare_pure_step.
           ++ intro. eauto with astep.
           ++ eapply hoare_cons.
              ** apply iSep_emp_l_inv.
              ** intro. apply iEntails_refl.
              ** apply hoare_frame_r.
                 apply Nat.eqb_neq in n0.
                 rewrite n0.
                 apply hoare_val.
      * simpl.
        eapply hoare_pure_stepN.
        -- intro. eauto with astep.
        -- apply hoare_frame_lN.
           eapply hoare_consN.
           ++ apply iSep_emp_r_inv.
           ++ apply iSep_emp_r.
           ++ apply hoare_frame_lN.
              apply hoare_error.
Qed.

Section RandomFree.

  (* in this section we are going to prove the two specs for a program
     that will free a location l. The location is not specified and though
     it is not random we have no knowledge on it.

     The objective here is to show that for the same presumption ∃ x y, x ↦ v ∗ y ↦ ⊥
     we can have two incorrectness specification.

     Moreover it also shows that any constraint on the location l should be
     put in the result assertion instead of the presumption.

     Instead of using the full ∃ x y, x ↦ v ∗ y ↦ ⊥ presumption we are going
     to frame them as our location l will be in one of the two singletons at a time

     {{ ∃ x y, x ↦ v ∗ y ↦ ⊥ }} free l {{ r . ∃ x y, x ↦ ⊥ ∗ y ↦ ⊥ ∗ ⌜ x = l ⌝ }}
     {{ ∃ x y, x ↦ v ∗ y ↦ ⊥ }} free l {{ERR: ∃ x y, x ↦ v ∗ y ↦ ⊥ ∗ ⌜ y = l ⌝ }}

     As we can see both triples will have a pure assertion ⌜ ? = l ⌝ and without
     that we cannot make. free l only steps through safely if x = l and will error
     if y = l.

     We cannot make with only ∃ x, x ↦ v because free l needs l ↦ ⊥ to fail and
     in ISL the negative heap assertion cannot be inferred from just ∃ x, x ↦ v.

     Though we are not gonna prove these complete triples because we will frame them.

     In the first triple we frame y ↦ ⊥ and in the second we frame x ↦ v.
   *)

Lemma random_free_safe v l:
  (* here we left out the ∃ y, y ↦ ⊥ as we framed it *)
  hoare (∃ x, x ↦ v)%S (EFree (EVal (VLoc l))) (λ r: val, ∃ x, ⌜ x = l ⌝ ∗ ⌜ r = VUnit ⌝ ∗ x ↦ ⊥)%S.
Proof.
  rewrite <- hoare_exists_forallS.
  intro.
  apply hoare_introS.
  intros.
  subst x.
  eapply (hoare_cons (l ↦ v))%S.
  - apply (iExists_intro l (λ r : nat, r ↦ v))%S.
  -  intro. apply iEntails_refl.
  - simpl.
    apply hoare_freeS.
Qed.

Lemma random_free_err l:
  (* if before we framed the x ↦ ⊥ now we can frame the x ↦ v *)
  hoare_err (∃ x, x ↦ ⊥)%S (EFree (EVal (VLoc l))) (∃ x, ⌜ x = l ⌝ ∗ x ↦ ⊥)%S.
  (* why the x = l in the result assertion? incorrectness triples here have
     a frame backing definition so we cannot realy prove there will be an error
     if our x ≠ l. Then a frame might have a l ↦ v or l ↦ ⊥ assertion. *)
Proof.
  rewrite <- hoare_exists_forallN.
  intro.
  apply hoare_introN.
  intros.
  eapply hoare_consN.
  - apply (iExists_intro x).
  - apply iEntails_refl.
  - subst x.
    apply hoare_freeN.
Qed.

End RandomFree.

Section DoubleFree.

  (* In this section we will look at a double-free error for the program

     e :=
       let x = ref 10 in
         if amb = 0 then
            free x
         else
            ()
         ;
         free x

    this program might error but can also step through safely

    the two triples we are interested in proving are

    {{ emp }} e {{ x. ∃ l, x = VUnit ∗ l ↦ ⊥ }}
    {{ emp }} e {{ERR: ∃ l, l ↦ ⊥ }}

*)

Definition e :=
  (ELet "x" (EAlloc (EVal (VNat 10)))
                      (ESeq
                         (EIf (EOp EqOp (EAmb) (EVal (VNat 0)))
                              (EFree (EVar "x"))
                              (EVal (VUnit)))
                         (EFree (EVar "x")))).

Lemma e_safe :
  hoare (emp)%S e (λ v : val, ∃ l, ⌜ v = VUnit ⌝ ∗ l ↦ ⊥)%S.
Proof.
  unfold e.
  rewrite <- hoare_exists_forallS.
  intro.
  eapply (hoare_let
            (λ r : val, ∃ x, ⌜ r = (VLoc x) ⌝ ∗ x ↦ VNat 10)
         (* here I can specify the existential variable value *)
            (VLoc x)
         )%S.
  - apply hoare_introS; intros.
    apply hoare_alloc1'.
  - simpl.
    eapply hoare_seqS.
    + (* in the first part of our sequence we take the false continuation *)
      eapply (hoare_if_false
                (λ r, ∃ x0, ⌜ VLoc x = VLoc x0 ⌝ ∗ x0 ↦ (VNat 10))
             )%S.
      * eapply hoare_cons.
        -- apply iSep_emp_l_inv.
        -- intro; apply iEntails_refl.
        -- simpl.
           apply hoare_frame_r.
           eapply (hoare_ctxS' [OpCtxL EqOp (EVal (VNat 0))] (VNat 1) (λ _, emp))%S.
           ++ eapply hoare_cons.
              ** apply iEntails_refl.
              ** intro. apply iSep_emp_r_inv.
              ** apply hoare_amb.
           ++ simpl.
              eapply hoare_cons.
              ** apply iEntails_refl.
              ** intro.
                 apply iSep_emp_r.
              ** simpl.
                 apply hoare_op.
                 auto.
      * instantiate (1 := (λ _, ∃ x0 : nat, ⌜ VLoc x = VLoc x0 ⌝ ∗ x0 ↦ VNat 10)%S).
        eapply hoare_cons.
        -- apply iSep_emp_l_inv.
        -- intro; apply iEntails_refl.
        -- simpl.
           apply hoare_frame_r.
           apply hoare_val.
    + simpl.
      eapply hoare_cons.
      * apply iExists_intro.
      * intro. apply iEntails_refl.
      * instantiate (1 := x).
        eapply hoare_cons.
        -- eapply iEntails_trans.
           2: { apply iSep_mono.
                ++ auto using iPure_intro.
                ++ apply iEntails_refl.
           }
           apply iSep_emp_l.
        -- intro. apply iEntails_refl.
        -- simpl.
           apply hoare_freeS.
Qed.

Lemma e_err:
  hoare_err (emp)%S e (∃ l, l ↦ ⊥)%S.
Proof.
  rewrite <- hoare_exists_forallN.
  intro.
  unfold e.
  eapply hoare_letN.
  - eapply (hoare_alloc1 x).
  - simpl.
    eapply (hoare_seqSN (λ r : val, x ↦ ⊥))%S.
    + eapply hoare_if_true.
      * eapply (hoare_ctxS [(OpCtxL EqOp (EVal (VNat 0)))]).
        eapply (hoare_cons
                  (emp ∗ x ↦ VNat 10)
                  (λ r : val, ⌜ r = VNat 0 ⌝ ∗ x ↦ VNat 10)
               )%S.
        -- apply iSep_emp_l_inv.
        -- intro.
           apply iEntails_refl.
        -- apply hoare_frame_r.
           apply hoare_amb.
        -- simpl.
           eapply (hoare_cons
                     (emp ∗ x ↦ VNat 10)
                     (λ r: val, ⌜ r = VBool true ⌝ ∗ x ↦ VNat 10)
                  )%S.
           ++ apply iSep_mono.
              apply iPure_intro.
              reflexivity.
              apply iEntails_refl.
           ++ intro.
              apply iEntails_refl.
           ++ apply hoare_frame_r.
              eapply hoare_pure_step.
              intro.
              eauto with astep.
              simpl.
              apply hoare_val.
      * simpl.
        apply hoare_freeS.
   + apply hoare_freeN.
Qed.

End DoubleFree.
Section BIND.

  (* let's do the easy things first: optctx *)

  Definition sum_ctx := [OpCtxL PlusOp (EVal (VNat 1))].

  Lemma reachable m:
    (hoare emp (fill sum_ctx (EVal m)) (λ v : val, ∃ n, ⌜ v = VNat n ⌝ ∗ ⌜ n > 0 ⌝))%S.
  Proof.
    apply hoare_exists_forallS.
    intro.
    simpl.
    eapply hoare_cons.
    - apply iEntails_refl.
    - intros.
      eapply iEntails_trans.
      + apply iSep_comm.
      + eapply iEntails_trans.
        * apply iSep_emp_r.
        * apply iSep_assoc'.
    - simpl.
      apply hoare_introS; intros.
      apply hoare_op.
      (* here is the first hiccup; without having m be a natural number I can't go on *)
  Admitted.
  (* In this section we explore the BIND rule for ISL and what kind of triple we can prove *)

  (*
    Our context is K ≝ let x = ⬜ in if 1 ≤ x then x else error
    and we are going to prove the triples
    {{ emp }} K[n] {{ r, ⌜ r = n ⌝ ∗ ⌜ 1 ≤ n ⌝ }}
   *)
  Definition K := [LetCtx "x" (EIf (EOp LeOp (EVal (VNat 1)) (EVar "x")) (EVar "x") (EError))].

  
  Lemma safe_number n:
    hoare (emp)%S (fill K (EVal (VNat n))) (λ r, ⌜ r = (VNat n) ⌝ ∗ ⌜ 1 ≤ n⌝)%S.
  Proof.
    eapply (hoare_ctxS_iris' K
                             (λ r, ⌜ r = VNat n ⌝)
                             emp
                             (EVal (VNat n))
                             (λ v, λ r, ⌜ r = VNat n ⌝ ∗ ⌜ 1 ≤ n⌝)
                             (VNat n))%S.
    - apply hoare_val.
    - intro.
      simpl.
      eapply (hoare_let
                (λ r, emp)
                ⌜ w = VNat n ⌝
                (λ r : val, (⌜ r = VNat n ⌝ ∗ ⌜ 1 ≤ n ⌝))
                (EVal w)
                (EIf (EOp LeOp (EVal (VNat 1)) (EVar "x")) (EVar "x") (EError))
                "x"
                (VNat n)
             )%S.
      + admit. (* the assertion must change place from presumption to result so I can use hoare_intro *)
      + simpl.
        eapply hoare_cons.
        * apply iEntails_refl.
        * intro.
          apply iSep_comm.
        * simpl.
          apply hoare_introS.
          intros.
          eapply (hoare_if_true (λ r, emp))%S.
          -- apply hoare_op.
             admit. (* here it's just a matter of proving result for eval_bin_op *)
          -- apply hoare_val.
  Admitted.

  Lemma unsafe_number n:
    hoare_err (emp)%S (fill K (EVal (VNat n))) ( ⌜ n < 1⌝)%S.
  Proof.
    eapply hoare_consN.
    - apply iEntails_refl.
    - apply iSep_emp_r.
    - apply hoare_introN.
      intro.
      simpl.
      eapply (hoare_letN (λ r, emp))%S.
      + eapply hoare_cons.
        * apply iEntails_refl.
        * intro.
          apply iSep_emp_r_inv.
        * simpl.
          apply hoare_val.
      + simpl.
        eapply (hoare_if_falseN (λ r, emp))%S.
        * apply hoare_op.
          admit. (* again just a matter of proving results about eval_bin_op *)
        * eauto using hoare_no_step, no_step_EError.
  Admitted.

End BIND.
