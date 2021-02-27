Lemma post_alloc l v:
  l ↦ v ⊢ post (EAlloc (EVal v)) (λ m, m !! l = None) (Some (VLoc l)).
Proof.
  intros m H mf Hdisj.
  exists (delete l m), (EVal (VLoc l)).
  split.
  solve_map_disjoint.
  simpl_map. split. auto.
  split.
  - apply step_once.
    unfold iPoints in H.
    subst m.
    rewrite delete_singleton.
    rewrite <- insert_union_singleton_l.
    rewrite left_id_L.
    apply step_alloc.
    unfold valid_alloc.
    intros e H0.
    exfalso.
    eapply map_disjoint_spec.
    eassumption.
    apply lookup_singleton.
    eassumption.
  - simpl.
    reflexivity.
Qed.

Lemma post_free_err l:
  iUnallocated l ⊢ post (EFree (EVal (VLoc l))) (iUnallocated l) None.
Proof.
Admitted.

Lemma post_load_err l:
  iUnallocated l ⊢ post (ELoad (EVal (VLoc l))) (iUnallocated l) None.
Proof.
Admitted.

Lemma post_store_err l v:
  (iUnallocated l) ⊢ post (EStore (EVal (VLoc l)) (EVal v)) (iUnallocated l) None.
Proof.
Admitted.

