Require Import String.
Open Scope string_scope.
Require Export lang.
From iris.bi Require Import bi.
Require Export ISL.


Definition push_back : expr → expr := λ v,
    (ELet "z" EAmb
          (EIf (EOp EqOp (EVar "z") (EVal (VNat 0)))
               (EVal VUnit)
               (ELet "old" (ELoad v) (* now y points to the underlying array *)
                     (ELet "new" (EAlloc (ELoad (EVar "old"))) (* copy the value *)
                           (ESeq (EFree (EVar "old"))
                                 (EStore v (EVar "new"))))))).


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

Lemma push_back_ok v a b: hoare (v ↦ (VLoc a) ∗ a ↦ b)%S (push_back (EVal (VLoc v))) (λ r, ∃ a', @[ r = VUnit ] ∗ v ↦ (VLoc a') ∗ a' ↦ b ∗ a ↦ ⊥ )%S.
Proof.
  apply hoare_exists_forallS; intros.
  unfold push_back.
  eapply hoare_let.
  - eapply hoare_consS.
    + apply iSep_emp_l_inv.
    + intros. apply iEntails_refl.
    + simpl.
      apply (hoare_frame_r (v ↦ VLoc a ∗ a ↦ b) emp (λ v1 : val, @[ v1 = (VNat 1) ]))%S.
      apply hoare_amb.
  - simpl.
    eapply hoare_if_false.
    + eapply hoare_consS.
      * apply iSep_emp_l_inv.
      * intros. apply iEntails_refl.
      * simpl.
        apply (hoare_frame_r (v ↦ VLoc a ∗ a ↦ b) emp (λ v1 : val, (@[ v1 = VBool false])))%S.
        apply hoare_op.
        simpl.
        reflexivity.
    + simpl.
      eapply (hoare_let (λ r: val, v ↦ VLoc a ∗ a ↦ b))%S.
      * eapply (hoare_consS (v ↦ (VLoc a) ∗a ↦ b)
                            (λ r, @[r = (VLoc a)] ∗ v ↦ (VLoc a) ∗ (a ↦ b)))%S.
        -- eapply iEntails_trans.
           ++ apply iSep_comm.
           ++ apply iSep_comm.
        -- intros. apply iEntails_refl.
        -- eapply hoare_consS.
           ++ apply iEntails_refl.
           ++ intro. apply iSep_assoc.
           ++ simpl. apply hoare_frame_r. apply hoare_loadS.
      * simpl.
        apply (hoare_let (λ r : val, x ↦ b ∗ a ↦ b ∗ v ↦ (VLoc a)) (VLoc x))%S.
        -- eapply hoare_consS.
           ++ apply iSep_comm.
           ++ intro.
              ** eapply iEntails_trans.
                 --- apply iSep_assoc.
                 --- apply iSep_assoc.
           ++ simpl.
              eapply hoare_frame_r.
              eapply (hoare_ctxS' [(AllocCtx)])%S.
              apply (hoare_loadS a b).
              simpl.
              eapply hoare_consS.
              ** apply iSep_emp_l_inv.
              ** intro.
                 apply iEntails_refl.
              ** simpl. apply hoare_frame_r.
                 apply hoare_alloc.
        -- simpl.
           eapply (hoare_seqS (λ r: val, a ↦ ⊥ ∗ x ↦ b ∗ v ↦ VLoc a) VUnit)%S.
           ++ eapply (hoare_consS ((a ↦ b ) ∗ x ↦ b ∗ v ↦ VLoc a)
                                  (λ r: val, (λ r : val, @[r=VUnit] ∗ a ↦ ⊥) r ∗ (x ↦ b ∗ v ↦ VLoc a)))%S.
              ** eapply iEntails_trans.
                 --- apply iSep_assoc.
                 --- eapply iEntails_trans.
                     +++ apply iSep_mono_l. apply iSep_comm.
                     +++ apply iSep_assoc'.
              ** intro. apply iSep_assoc.
              ** eapply hoare_frame_r.
                 apply hoare_freeS.
           ++ eapply hoare_consS.
              ** apply iSep_comm.
              ** intro. eapply iEntails_trans. apply iSep_assoc. apply iSep_assoc.
              ** simpl. apply hoare_frame_r.
                 eapply hoare_consS.
                 --- apply iSep_comm.
                 --- intro. apply iEntails_refl.
                 --- simpl.
                     apply hoare_frame_r.
                     apply hoare_storeS.
Qed.



Lemma client_error: hoare_err iEmp client ( 0 ↦ ⊥ ∗ 1 ↦ (VLoc 2) ∗ 2 ↦ VNat 42)%S.
Proof.
  unfold client.
  eapply hoare_letN.
  - eapply (hoare_alloc1 0).
  - simpl.
    eapply (hoare_letN (λ l, 1 ↦ (VLoc 0) ∗ 0 ↦ (VNat 0)))%S.
    + eapply hoare_consS.
      apply iSep_emp_l_inv.
      intro. apply iSep_assoc.
      simpl.
      eapply hoare_frame_r.
      eapply (hoare_alloc1 1).
    + simpl.
      eapply hoare_consN.
      apply iSep_comm. apply iEntails_refl.
      eapply (hoare_letN (λ v, 0 ↦ VNat 0 ∗ 1 ↦ VLoc 0)%S).
      * eapply hoare_consS.
        apply iEntails_refl.
        intro. eapply iEntails_trans.
        apply iSep_comm.
        apply iSep_assoc'.
        apply hoare_frame_l.
        eapply hoare_consS. apply iEntails_refl.
        intro. apply iSep_comm. simpl.
        apply hoare_loadS.
      * simpl.
        eapply (hoare_seqSN (λ l, 0 ↦ ⊥ ∗ 1 ↦ VLoc 2 ∗ 2 ↦ VNat 42)%S ).
        -- eapply hoare_let.
           ++ eapply hoare_consS.
              apply iSep_emp_r_inv. intro.
              apply iSep_comm. simpl.
              apply (hoare_frame_l (0 ↦ VNat 0 ∗ 1 ↦ VLoc 0))%S.
              apply (hoare_amb 1).
           ++ simpl.
              eapply hoare_if_false.
              ** eapply hoare_pure_step.
                 intro. eauto with astep.
                 simpl.
                 eapply hoare_consS.
                 apply iSep_emp_r_inv.
                 intro. apply iSep_comm. simpl.
                 apply (hoare_frame_l (0 ↦ VNat 0 ∗ 1 ↦ VLoc 0)%S).
                 apply hoare_val.
              ** simpl.
                 eapply (hoare_let (λ r, 0 ↦ VNat 0 ∗ 1 ↦ VLoc 0))%S.
                 --- eapply hoare_consS.
                     apply iEntails_refl.
                     intro. eapply iEntails_trans.
                     apply iSep_comm.  apply iSep_assoc'. simpl.
                     apply hoare_frame_l.
                     eapply hoare_consS.
                     apply iEntails_refl.
                     intro. apply iSep_comm. simpl.
                     apply hoare_loadS.
                 --- simpl.
                     eapply (hoare_seqS
                               (λ l, 0 ↦ ⊥ ∗ 1 ↦ VLoc 0)
                               (0 ↦ VNat 0 ∗ 1 ↦ VLoc 0))%S.
                     +++ eapply hoare_consS.
                         apply iEntails_refl.
                         intro. apply iSep_assoc. simpl.
                         apply hoare_frame_r.
                         apply hoare_freeS.
                     +++ eapply (hoare_let (λ l, 0 ↦ ⊥ ∗ 1 ↦ VLoc 0 ∗ 2 ↦ VNat 42))%S.
                         *** eapply hoare_consS.
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
                             eapply hoare_consS.
                             apply iEntails_refl.
                             intro. apply iSep_assoc'. simpl.
                             apply hoare_frame_l.
                             eapply hoare_consS.
                             apply iEntails_refl.
                             intro. apply iSep_comm. simpl.
                             apply (hoare_alloc1 2).
                         *** simpl.
                             eapply hoare_consS.
                             apply iSep_assoc'.
                             intro.
                             eapply iEntails_trans.
                             apply iSep_assoc.
                             apply iSep_assoc.
                             apply hoare_frame_r.
                             eapply hoare_consS.
                             apply iEntails_refl.
                             intro.
                             eapply iEntails_trans.
                             apply iSep_assoc'.
                             eapply iEntails_trans.
                             apply iSep_comm.
                             apply iSep_assoc'. simpl.
                             apply hoare_frame_l.
                             eapply hoare_consS.
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
    + eapply hoare_consS.
      * apply iSep_emp_r_inv.
      * intro.
        eapply iEntails_trans.
        apply iSep_comm.
        apply iSep_assoc'.
      * simpl.
        eapply (hoare_frame_l (n ↦ VNat 3)%S).
        eapply hoare_consS.
        -- apply iEntails_refl.
        -- intro. apply iSep_comm.
        -- simpl.
           apply (hoare_alloc1 m).
    + simpl.
      apply (hoare_ctxSN [(IfCtx (EVal VUnit) EError)] (λ r, n ↦ VNat 3 ∗ m ↦ VNat 3)%S (VBool false)).
      * destruct (Nat.eq_dec n m).
        -- eapply hoare_consS.
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
           ++ eapply hoare_consS.
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
  eapply (hoare_consS (l ↦ v))%S.
  - apply (iExists_intro (λ r : nat, r ↦ v))%S.
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
  - apply (iExists_intro (λ x, x ↦ ⊥))%S.
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
      * eapply hoare_consS.
        -- apply iSep_emp_l_inv.
        -- intro; apply iEntails_refl.
        -- simpl.
           apply hoare_frame_r.
           eapply (hoare_ctxS' [OpCtxL EqOp (EVal (VNat 0))] (VNat 1) (λ _, emp))%S.
           ++ eapply hoare_consS.
              ** apply iEntails_refl.
              ** intro. apply iSep_emp_r_inv.
              ** apply hoare_amb.
           ++ simpl.
              eapply hoare_consS.
              ** apply iEntails_refl.
              ** intro.
                 apply iSep_emp_r.
              ** simpl.
                 apply hoare_op.
                 auto.
      * instantiate (1 := (λ _, ∃ x0 : nat, ⌜ VLoc x = VLoc x0 ⌝ ∗ x0 ↦ VNat 10)%S).
        eapply hoare_consS.
        -- apply iSep_emp_l_inv.
        -- intro; apply iEntails_refl.
        -- simpl.
           apply hoare_frame_r.
           apply hoare_val.
    + simpl.
      eapply hoare_consS.
      * apply iExists_intro.
      * intro. apply iEntails_refl.
      * instantiate (1 := x).
        eapply hoare_consS.
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
        eapply (hoare_consS
                  (emp ∗ x ↦ VNat 10)
                  (λ r : val, ⌜ r = VNat 0 ⌝ ∗ x ↦ VNat 10)
               )%S.
        -- apply iSep_emp_l_inv.
        -- intro.
           apply iEntails_refl.
        -- apply hoare_frame_r.
           apply hoare_amb.
        -- simpl.
           eapply (hoare_consS
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
    eapply hoare_consS.
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
                (VNat n))%S.
      + admit. (* the assertion must change place from presumption to result so I can use hoare_intro *)
      + simpl.
        eapply hoare_consS.
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
      + eapply hoare_consS.
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
