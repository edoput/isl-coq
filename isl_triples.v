Require Export ISL.

(* In the original IL and ISL papers the authors use a statement language
   and express their proof rules as Hoare triples. In this work we have
   changed the language to an expression language and defined a _weakest
   precondition_ style for incorrectness triples.

   This part is about binding the original rules with our triples
   and show that our approach is at least as strong as the original.

   There are minor differences in the languages values as we still don't
   have a _null_ value for locations as our assumption is that _alloc
   never fails_ and always returns a _fresh location_ that is not
   in use.
*)


(*
  These are the rules from the original ISL paper

  ASSIGN ∅ ⊢ [x=x']x:=e[ok:x=e[x'/x]]

  is replaced by shadowing in a let-binding; x:=e assumes the name x exists already
  and has value x', the new value will be the value of e which we compute as e[x'/x]

  (let (EVar "x") e body) reduces as follows; given steps e m v m' then we have
  steps (let (EVar "x") e body) m (subst (EVar "x") v body) m' replacing
  each instance of (EVar "x") with v (up to another let binding).

  HAVOC ∅ ⊢ [x=x']x:=*[ok:x=v]

  ASSUME ∅ ⊢ [emp]assume(B)[ok:B]

  ERROR ∅ ⊢ [emp]L:error[er(L):emp]

  SEQ1
  ∅ ⊢ [p]C₁[er(L):q]
  ------------------
  ∅ ⊢ [p]C₁;C₂[er(L):q]

  SEQ2
  ∅ ⊢ [p]C₁[ok:r] ∅ ⊢ [r]C₂[𝜖:q]
  ------------------------------
  ∅ ⊢ [p]C₁;C₂[𝜖:q]

  LOOP1
  ∅ ⊢ [p]C*[ok:p]

  LOOP2
  ∅ ⊢ [p]C*;C[𝜖:q]
  ----------------
  ∅ ⊢ [p]C*[𝜖:q]

  CHOICE
  ∅ ⊢ [p]Cᵢ[𝜖:q] i ∈ {1,2}
  -----------------------
  ∅ ⊢ [p]C₁+C₂[𝜖:q]

  EXIST
  ∅ ⊢ [p]C[𝜖:q] x ∉ fv(C)
  -----------------------
  ∅ ⊢ [∃x.p]C[𝜖:∃x.q]

  CONS
  p' → p   ∅ ⊢ [p']C[𝜖:q']   q → q'
  ---------------------------------
        ∅ ⊢ [p]C[𝜖:q]

  DISJ
  ∅ ⊢ [p₁]C[𝜖:q₁]  ∅ ⊢[p₂]C[𝜖:q₂]
  -------------------------------
   ∅ ⊢ [p₁ ∨ p₂]C[𝜖: q₁ ∨ q₂]

  SUBST
  ∅ ⊢ [p]C[𝜖:q]   y ∉ fv(p,C,q)
  -----------------------------
  ∅ ⊢ [p[y/x]]C[y/x][𝜖:q[x/y]]

  LOCAL
  ∅ ⊢ [p]C[𝜖:q]
  -------------
  ∅ ⊢ [∃x.p] local x in C[𝜖:∃x.q]

  FRAME
  ∅ ⊢ [p]C[𝜖:q]   mod(C) ∩ fv(r) = ∅
  ----------------------------------
  ∅ ⊢ [p ∗ r]C[𝜖:q ∗ r]

  ALLOC1
  ∅ ⊢ [x=x'] x:=alloc() [ok:x → _]
  
  ALLOC2
  ∅ ⊢ [x=x' ∗ y ↛ _] x:=alloc() [ok: x=y ∗ y → _]

  FREE
  ∅ ⊢ [x ↦ e] L:free(x) [ok: x ̸↦_]

  FREEER
  ∅ ⊢ [x ̸↦ _] L:free(x) [er(L): x̸↦ _]
  
  FREENUL
  ∅ ⊢ [x=null] L:free(x) [er(L): x = null]

  LOAD
  ∅ ⊢ [x=x' ∗ y ↦ e] L:x:=[y] [ok:x=e[x'/x] ∗ y ↦ e[x'/x]]

  LOADER
  ∅ ⊢ [y ̸ ↦ _] L:x:=[y] [er(L): y ̸ ↦ _]

  LOADNULL
  ∅ ⊢ [y = null] L:x=[y] [er(L): y=null]

  STORE
  ∅ ⊢ [x ↦ e] L:[x]:=y  [ok:x ↦ y]

  STOREER
  ∅ ⊢ [x ̸ ↦ _] L:[x]:=y [er(L): x ̸ ↦ _]

  STORENULL
  ∅ ⊢ [y = null] L:[x]:=y [er(L): y=null]
*)

(* Let's start proving them *)

(* All the triples in the ISL paper are about the language
   _builtin operations_ and we had to adapt them to fit
   our expression language. This also means that most of the rules
   are about _one single step_ of the computation but there
   are some that require more than one step to actually compute
   so we can't really use our _step_ relation and we have to
   use _steps_.
 *)

(*
  SEQ1
  ∅ ⊢ [p]C₁[er(L):q]
  ------------------
  ∅ ⊢ [p]C₁;C₂[er(L):q]
 *)

Definition hoare_isl (P: iProp) (e : expr) (Q : val → iProp) : Prop :=
  ∀ v m, (Q v) m → ∃ m', (P m') ∧ steps e m' (EVal v) m.

Definition hoare_err (P: iProp) (e : expr) (Q: val → iProp) : Prop :=
  ∀ v m', (Q v) m' → ∃ m e', (P m) ∧ steps e m e' m' ∧ is_error e' m'.

Lemma happy_equiv (P : iProp) (e : expr) (Q : val → iProp) v:
  hoare_isl P e Q ↔ ((Q v) ⊢ wp e P v).
Proof.
Admitted.

Lemma error_equiv (P : iProp) (e : expr) (Q: val → iProp)
  hoare_error P e Q
λ m, (∀ v, (Q v) m → ∃ m', (P m') ∧ steps e m' (EVal v) m).

(∀ v, (Q v) ⊢ ∃ m', (P m') ∧ steps e m' (EVal v))
  
  Defition hoare_err (P : iProp) (e : expr) (
    
    hoare_isl P e (Q v) ↔ ((Q v) ⊢ wp e P v)
    hoare_err P e (Q v) ↔ ((Q v) ⊢ ewp e P)
                          
Lemma 
