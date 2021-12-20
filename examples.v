Require Import String.
Open Scope string_scope.
Require Export lang.
From iris.bi Require Import bi.
Require Export ISL.


Definition push_back (v : expr): expr :=
    (ELet "z" EAmb
          (EIf (EOp EqOp (EVar "z") (EVal (VNat 0)))
               (EVal VUnit)
               (ELet "old" (ELoad v)
                     (ELet "new" (EAlloc (ELoad (EVar "old")))
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

Lemma client_error: hoare_err iEmp client (1 ↦ (VLoc 2) ∗ 0 ↦ ⊥ ∗ 2 ↦ VNat 0)%S.
Proof.
  unfold client.
  (* we first apply hoare_let 3 times *)
  (* let w = ref 0 *)
  eapply (hoare_letN (λ v, 0 ↦ (VNat 0)) (VLoc 0))%S.
  - apply hoare_alloc.
  - simpl.
    (* let v = ref w *)
    eapply (hoare_letN (λ l, 1 ↦ (VLoc 0) ∗ 0 ↦ (VNat 0)) (VLoc 1))%S.
    + (* ref w*)
      eapply hoare_consS.
      * apply iSep_emp_l_inv.
      * intro. apply iSep_assoc.
      * simpl.
        apply hoare_frame_r.
        apply hoare_alloc.
    + simpl.
      (* let x = ! v *)
      eapply (hoare_letN (λ v, 1 ↦ VLoc 0 ∗ 0 ↦ VNat 0) (VLoc 0))%S.
      * (* TODO *)
        eapply hoare_consS.
        -- apply iEntails_refl.
        -- intro.
           apply iSep_assoc.
        -- simpl.
           apply hoare_frame_r.
           apply hoare_loadS.
      * simpl.
        eapply (hoare_seqSN (λ l, 0 ↦ ⊥ ∗ 1 ↦ VLoc 2 ∗ 2 ↦ VNat 0) VUnit)%S.
        (* push_back, unfortunately I cannot use the previous lemma *)
        -- eapply (hoare_let (λ v, 1 ↦ VLoc 0 ∗ 0 ↦ VNat 0) (VNat 1))%S.
           ++ eapply hoare_consS.
              ** apply iSep_emp_l_inv.
              ** intro.  apply iEntails_refl.
              ** simpl.
                 apply hoare_frame_r.
                 apply hoare_amb.
           ++ simpl.
              eapply (hoare_if_false (λ v, 1 ↦ VLoc 0 ∗ 0 ↦ VNat 0))%S.
              ** eapply hoare_pure_step.
                 --- intro. eauto with astep.
                 --- simpl.
                     eapply hoare_consS.
                     +++ apply iSep_emp_l_inv.
                     +++ intro. apply iEntails_refl.
                     +++ simpl.
                         apply hoare_frame_r.
                         apply hoare_val.
              ** eapply (hoare_let (λ r, 1 ↦ VLoc 0 ∗ 0 ↦ VNat 0) (VLoc 0))%S.
                 --- eapply hoare_consS.
                     +++ apply iEntails_refl.
                     +++ intro. apply iSep_assoc.
                     +++ simpl.
                         apply hoare_frame_r.
                         apply  hoare_loadS.
                 --- simpl.
                     eapply (hoare_consS (0 ↦ VNat 0 ∗ 1 ↦ VLoc 0))%S.
                     +++ apply iSep_comm.
                     +++ intro. apply iEntails_refl.
                     +++ eapply (hoare_let (λ v,2 ↦ VNat 0 ∗ 0 ↦ VNat 0 ∗ 1 ↦ VLoc 0) (VLoc 2))%S.
                         *** eapply (hoare_ctxS' [AllocCtx] (VNat 0) (λ v, 0 ↦ VNat 0 ∗ 1 ↦ VLoc 0))%S.
                             ---- eapply hoare_consS.
                                  ++++ apply iEntails_refl.
                                  ++++ intro. apply iSep_assoc.
                                  ++++ simpl.
                                       apply hoare_frame_r.
                                       apply hoare_loadS.
                             ---- simpl.
                                  eapply hoare_consS.
                                  ++++ apply iSep_emp_l_inv.
                                  ++++ intro. apply iSep_assoc.
                                  ++++ simpl.
                                       apply hoare_frame_r.
                                       apply hoare_alloc.

                         *** simpl.
                             eapply (hoare_seqS (λ v, 2 ↦ VNat 0 ∗ 0 ↦ ⊥ ∗ 1 ↦ VLoc 0) (VUnit))%S.
                             ---- eapply hoare_consS.
                                  ++++ apply iSep_assoc'.
                                  ++++ intro.
                                       eapply iEntails_trans.
                                       **** apply iSep_mono_r.
                                            apply iSep_assoc.
                                       **** apply iSep_assoc.
                                  ++++ simpl.
                                       apply hoare_frame_r.
                                       eapply (hoare_consS (0 ↦ VNat 0 ∗ 2 ↦ VNat 0)
                                                           (λ r, (@[ r = VUnit ] ∗ 0 ↦ ⊥) ∗ 2 ↦ VNat 0)
                                              )%S.
                                       **** apply iSep_comm.
                                       **** intro.
                                            eapply iEntails_trans.
                                            2: { apply iSep_assoc. }
                                            apply iSep_mono_r.
                                            apply iSep_comm.
                                       **** apply hoare_frame_r.
                                            apply hoare_freeS.
                             ---- eapply (hoare_consS (1 ↦ VLoc 0 ∗ 0 ↦ ⊥ ∗ 2 ↦ VNat 0)
                                                      (λ r, (@[ r = VUnit] ∗ 1 ↦ VLoc 2) ∗ 0 ↦ ⊥ ∗ 2 ↦ VNat 0))%S.
                                  ++++ eapply iEntails_trans.
                                       **** apply iSep_assoc.
                                       **** eapply iEntails_trans.
                                            apply iSep_comm.
                                            apply iSep_mono_r.
                                            apply iSep_comm.
                                  ++++ intro.
                                       eapply iEntails_trans.
                                       2:{ apply iSep_assoc. }
                                       apply iSep_mono_r.
                                       eapply iEntails_trans.
                                       **** apply iSep_assoc.
                                       **** eapply iEntails_trans.
                                            2:{ apply iSep_assoc'. }
                                            apply iSep_mono_l.
                                            apply iSep_comm.
                                  ++++ apply hoare_frame_r.
                                       apply hoare_storeS.
        -- eapply hoare_consN.
           ++ apply iEntails_refl.
           ++ eapply iEntails_trans.
              apply iSep_assoc.
              eapply iEntails_trans.
              ** apply iSep_mono_l.
                 apply iSep_comm.
              ** apply iSep_assoc'.
           ++ apply hoare_frame_rN.
              apply hoare_storeN.
Qed.


Lemma client_unsafe:
  unsafe client.
Proof.
  eapply soundness.
  2:{ eapply hoare_consN.
      3:{ apply client_error. }
      - intros ??. unfold iTrue. done.
      - apply iEntails_refl.
  }
  unfold inhabited.
  exists {[ 1 := (Value (VLoc 2)) ; 0 := Reserved ; 2 := (Value (VNat 0)) ]}.
  exists {[ 1 := (Value (VLoc 2)) ]}, {[ 0 := Reserved ; 2 := (Value (VNat 0)) ]}.
  split.
  - done.
  - split.
    exists {[ 0:= Reserved ]}, {[ 2 := Value (VNat 0) ]}.
    + split.
      done.
      split.
      * done.
      * split.
        -- rewrite <- insert_union_singleton_l.
           reflexivity.
        -- solve_map_disjoint.
    + split.
      * rewrite <- insert_union_singleton_l.
        reflexivity.
      * solve_map_disjoint.
Qed.

Print Assumptions client_unsafe.

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
  hoare (∃ x, x ↦ v)%S (EFree (EVal (VLoc l))) (λ r: val, ∃ x, @[ x = l ] ∗ @[ r = VUnit ] ∗ x ↦ ⊥)%S.
Proof.
  rewrite <- hoare_exists_forallS.
  intro.
  apply hoare_introS.
  intros.
  subst x.
  eapply (hoare_consS (l ↦ v))%S.
  - apply (iExists_intro (λ r : nat, r ↦ v) l)%S.
  -  intro. apply iEntails_refl.
  - simpl.
    apply hoare_freeS.
Qed.

Lemma random_free_err l:
  (* if before we framed the x ↦ ⊥ now we can frame the x ↦ v *)
  hoare_err (∃ x, x ↦ ⊥)%S (EFree (EVal (VLoc l))) (∃ x, @[ x = l ] ∗ x ↦ ⊥)%S.
  (* why the x = l in the result assertion? incorrectness triples here have
     a frame backing definition so we cannot realy prove there will be an error
     if our x ≠ l. Then a frame might have a l ↦ v or l ↦ ⊥ assertion. *)
Proof.
  rewrite <- hoare_exists_forallN.
  intro.
  apply hoare_introN.
  intros.
  eapply hoare_consN.
  - apply (iExists_intro (λ x, x ↦ ⊥) x)%S.
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
  hoare (emp)%S e (λ v : val, ∃ l, @[ v = VUnit ] ∗ l ↦ ⊥)%S.
Proof.
  unfold e.
  rewrite <- hoare_exists_forallS.
  intro.
  eapply (hoare_let
            (λ r : val, ∃ x, @[ r = (VLoc x) ] ∗ x ↦ VNat 10)
         (* here I can specify the existential variable value *)
            (VLoc x)
         )%S.
  - apply hoare_introS; intros.
    apply hoare_exists_forallS.
    intro.
    apply hoare_alloc.
  - simpl.
    eapply hoare_seqS.
    + (* in the first part of our sequence we take the false continuation *)
      eapply (hoare_if_false
                (λ r, ∃ x0, @[ VLoc x = VLoc x0 ] ∗ x0 ↦ (VNat 10))
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
              apply hoare_op.
              simpl. auto.
      * instantiate (1 := (λ _, ∃ x0 : nat, @[ VLoc x = VLoc x0 ] ∗ x0 ↦ VNat 10)%S).
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
  - eapply (hoare_alloc x).
  - simpl.
    eapply (hoare_seqSN (λ r : val, x ↦ ⊥))%S.
    + eapply hoare_if_true.
      * eapply (hoare_ctxS [(OpCtxL EqOp (EVal (VNat 0)))]).
        eapply (hoare_consS
                  (emp ∗ x ↦ VNat 10)
                  (λ r : val, @[ r = VNat 0 ] ∗ x ↦ VNat 10)
               )%S.
        -- apply iSep_emp_l_inv.
        -- intro.
           apply iEntails_refl.
        -- apply hoare_frame_r.
           apply hoare_amb.
        -- simpl.
           eapply (hoare_consS
                     (emp ∗ x ↦ VNat 10)
                     (λ r: val, @[ r = VBool true ] ∗ x ↦ VNat 10)
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
