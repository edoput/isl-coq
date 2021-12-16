Require Import String.
Open Scope string_scope.
Require Export lang.
From iris.bi Require Import bi.
Require Export ISL.


Definition push_back (v : expr): expr :=
    (ELet "z" EAmb
          (EIf (EOp EqOp (EVar "z") (EVal (VNat 0)))
               (EVal VUnit)
               (ELet "old" (ELoad v) (* now y points to the underlying array *)
                     (ELet "new" (EAlloc (ELoad (EVar "old"))) (* copy the value *)
                           (ESeq (EFree (EVar "old"))
                                 (EStore v (EVar "new"))))))).
Arguments push_back _ : simpl never.

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
