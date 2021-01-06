Require Export Arith String List Omega.
Export ListNotations.
Global Generalizable All Variables.

(* # Advanced data structures *)
(* ## Finite maps *)
(*
In the last part of this course we will look into a way of representing finite
maps (aka finite partial functions) from natural numbers to elements of some
type `A`. This means that we want to define a type `map A` and the following
operations:

  mlookup : map A -> nat -> option A
  mempty : map A
  msingleton : nat -> A -> map A
  minsert : nat -> A -> map A -> map A
  mdelete : nat -> map A -> map A

These operations should enjoy their expected properties, for example:

  mlookup (minsert i y m) i = Some y
  i <> j -> mlookup (minsert i y m) j = mlookup m j

The naive way of encoding finite maps is by means of association lists, i.e. as
lists of key value lists. In Coq that would be:
*)

Definition assoc_list (A : Type) : Type := list (prod nat A).

Print prod.
(*
Inductive prod (A B : Type) : Type :=
  | pair : A -> B -> A * B
*)

Print list.
(*
Inductive list (A : Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A
*)

(*
However, this encoding is not ideal, and suffers from some problems. First of
all, the same finite maps can be represented by different association lists.
For example, the map `0 |-> a, 3 |-> b` can be represented by the following
association lists:

  [(0,a); (3,b)]
  [(3,b); (0,a)]

This situation is not desired, since it means that the following property does
_not_ hold:

  m1 = m2 <-> forall i, mlookup m1 i = mlookup m2 i

To see that it does not hold, take

  m1 = [(0,a); (3,b)]
  m2 = [(3,b); (0,a)]

Now it is clear to see that the property does not hold.

Similarly, another issue of the representation through association lists is that
the same key could appear multiple times in the same association list, e.g.:

  [(0,a); (0,b)]

When implementing `mlookup` we have to make an arbitrary choice with key/value
pair to pick. Also, other operations get a bit tricky on how to consider
duplicate key pairs.

So, a natural question comes up:

  Can we represent finite maps in a different way so that these problems
  fo not occur?

As we will see, the answer is "yes". To get there, let's first take a look at
another attempt:
*)

Definition map_raw (A : Type) := list (option A).

Print option.
(*
Inductive option (A : Type) : Type :=
  | Some : A -> option A
  | None : option A
*)

(*
The idea of this representation is that at each index `i` of the list we have
`Some a` iff `i |-> a` is in the map, and use `None`s for unused positions. For
example, we represent the map `0 |-> a, 3 |-> b` as 

  [Some a; None; None; Some b]

With the above representation of finite maps in hand, we can now define the
lookup function as:
*)

Fixpoint mlookup_raw {A} (m : map_raw A) (i : nat) : option A :=
  match m with
  | nil => None
  | x :: m =>
     match i with
     | 0 => x
     | S i => mlookup_raw m i
     end
  end.

(*
This new representation solves the problem of duplicate keys value pairs, simply
because at each position in the list, there can be at most one value. However,
this representation still suffers from the problem that there are duplicate
representations of the same map. For example, the map in the previous example
could also be represented by:

  [Some a; None; None; Some b; None]
  [Some a; None; None; Some b; None; None]

So, in order to have the property

  m1 = m2 <-> forall i, mlookup m1 i = mlookup m2 i

We have to make sure that there is no sequence of `None`s at the end of the
list. We will do this by considering the "subtype of `raw_map`s that do not have
a sequence of `None`s at the end". But how to represent subtypes in Coq? As
we will see below, we do this as follows:

1. Define a predicate that carved out the _well-formed_ `raw_map`s, i.e. those
   that do not have a sequence of `None`s at the end.
2. Construct the subtype of _well-formed` `raw_map`s.

Before going into details about the second point, we will first define the
well-formedness predicate. For reasons that will become apparent later, we do
this by defining a Boolean function `map_wf`:
*)

Definition is_Some {A} (x : option A) : bool :=
  match x with
  | Some _ => true
  | None => false
  end.

Fixpoint map_wf {A} (may_be_nil : bool) (m : map_raw A) : bool :=
  match m with
  | [] => may_be_nil
  | x :: m => map_wf (is_Some x) m
  end.

(*
We use the parameter `may_be_nil` to keep track of whether the previous element
was a `Some`. Only if that is the case, the list may be `nil`.

Now, to define our actual `map` type, we want to consider the elements of type
`map_raw` that are well-formed. We achieve this by defining a dependently typed
record that consists of:

- The raw map `m : map_raw`
- A proof that the raw map `m` is well-formed.

The second becomes part is a bit more subtle. We have defined the well-formedness
redicate as a Boolean function, whereas proofs in Coq as of type `Prop`. To
make things work, we thus need to turn the Boolean into a `Prop`. We do this by
defining a function `is_True : bool -> Prop`:
*)

Coercion is_True (b : bool) : Prop :=
  if b then True else False.

(*
The keyword `Coercion` is used to instruct Coq to automatically insert the
function whenever it sees a `bool` but needs a `Prop`. We can now for example
write things like:
*)

Check (true : Prop).
Check (true /\ 0 = 0).

(*
When we instruct Coq to display coercions (by setting `Set Printing Coercions`),
we see that the above terms actually expand to:

  is_True true : Prop
  is_True true /\ 0 = 0

With the coercion `is_True` in hand, we can now define the dependently typed
record as follows:
*)

Record map (A : Type) := make_map {
  map_car : map_raw A;
  map_prf : map_wf true map_car
}.

(*
Now let is take a look at the record `map` that we have just defined. As part of
this, we get a constructor:

  make_map : forall (A : Type) (m : map_raw A), map_wf true m -> map A

And two projections to get out the raw map and the proof, respectively:

  map_car : forall (A : Type), map A -> map_raw A
  map_prf : forall (A : Type) (m : map A), map_wf true (map_car A m)

The following commands make sure that the type argument `A` becomes implicit,
so that we do not have to write it explicitly all the time.
*)
Arguments make_map {_} _ _.
Arguments map_car {_} _.
Arguments map_prf {_} _.

(*
With the projection `map_car` in hands, it is straightforward to lift the
function `mlookup_raw` to the record `map` of raw maps together with a proof of
well-formedness: we just project out the raw map:
*)
Definition mlookup {A} (m : map A) (i : nat) : option A :=
  mlookup_raw (map_car m) i.

(*
Now that we have the type of maps defined, and the basic operation for looking
up elements in place, we will start by proving the desired property:

  (forall i, mlookup m1 i = mlookup m2 i) -> m1 = m2

We will do this in two stages:

1. Lemma `map_raw_eq`: Prove that for any `m1 m2 : raw_map A` we have

     map_wf b m1 ->
     map_wf b m2 ->
     (forall i, mlookup_raw m1 i = mlookup_raw m2 i) ->
     m1 = m2

2. Lemma `map_eq`: Show that the desired property follows from (1).
*)

(*
Stage 1: We prove the property by induction on one of the raw maps, followed by
a case distinction on the other. We can pick either `m1` or `m2` for the
induction, because the choice does not really matter by symmetry, after all.

For the base cases, we will first prove the helper lemma `map_wf_nil` as below.
This lemma states that whenever we have a well-formed raw map, and looking up
always yields `None`, then the raw map should be nil. This property is proven
by induction.
*)
Lemma map_wf_nil {A} (b : bool) (m : map_raw A) :
  map_wf b m ->
  (forall i, mlookup_raw m i = None) ->
  m = [].
Proof. 
  revert b. induction m as [|x m2 IH]; intros b Hwf Hlookup; simpl in *.
  - reflexivity.
  - assert (m2 = []).
    { apply (IH (is_Some x)). apply Hwf. intros i. apply (Hlookup (S i)). }
    subst m2.
    assert (x = None).
    { apply (Hlookup 0). }
    subst x.
    simpl in *.
    destruct Hwf.
Qed.

(*
We can now prove the actual property for raw maps. Remember to use the above
helper lemma in the base cases.
*)
Lemma map_raw_eq {A} (b : bool) (m1 m2 : map_raw A) :
  map_wf b m1 ->
  map_wf b m2 ->
  (forall i, mlookup_raw m1 i = mlookup_raw m2 i) -> m1 = m2.
Proof.
  revert b m2.
  induction m1 as [|x m1 IH]; intros b m2 Hm1 Hm2 Hlookup.
  - symmetry. apply (map_wf_nil b).
    + apply Hm2.
    + simpl in *. intros i. symmetry. apply Hlookup.
  - destruct m2 as [|y m2].
    + apply (map_wf_nil b). assumption. assumption.
    + assert (x = y).
      { apply (Hlookup 0). }
      subst. simpl in *. f_equal.
      apply (IH (is_Some y)). assumption. assumption.
      intros i. apply (Hlookup (S i)).
Qed.

(*
Stage 2: We will prove the property for maps, that is:

  (forall i, mlookup m1 i = mlookup m2 i) -> m1 = m2

Unfortunately, even while having the helping lemma `map_raw_eq` that we just
proved at hand, this direction still does not follow immediately. The problem
is that maps are essentially tuples

  m : raw_map A
  H : is_True (map_car true m)

Now if we want to establish that two maps `(m1,H1)` and `(m2,H2)` are equal, we
do not just have to show that the underlying raw maps `m1` and `m2` are equal
(which we obtain from `map_raw_eq`), but we also have to show that the proofs
`H1` and `H2` are equal. So, concretely, after using the equality that `m1` and
`m2` are equal, we have to show that given:

  m1 : map_raw A
  H1 : is_True (map_car true m1)
  H2 : is_True (map_car true m1)

We have to show `H1 = H2`. Intuitively, this may sound obvious, but it is not.
As you will see in the Homotopy Type Theory lectures, the property below, which
is typically refered to as _proof irrelevance_ does in general not hold:

  forall (P : Prop) (H1 H2 : P), H1 = H2

Fortunately, in our case we are lucky, we are not considering an arbitrary
proposition `P`, but something of the shape `is_True b`. Due to that, we can
actually prove this property by making a case analysis on `b`:
*)
Lemma is_True_proof_irrel (b : bool) (H1 H2 : is_True b) :
  H1 = H2.
Proof.
  destruct b; simpl in *.
  - (* Now we `H1, H2 : True`. By a simple case analysis, we can show that
    each proof of `True` is equal to `I`, the constructor of `True`. By
    Curry-Howard, think of `True` as the unit type, and indeed, the only
    constructor of the unit type is `tt`. *)
    destruct H1. destruct H2. reflexivity.
  - (* Now we have `H1, H2 : False`. This is a contradiction. *)
    destruct H1.
Qed.

(*
The desired property, but written as a bi-implication so that we also have the
opposite direction. Note that the opposite direction of is trivial: we rewrite
the equality and use reflexivity.
*)
Lemma map_eq {A} (m1 m2 : map A) :
  m1 = m2 <-> forall i, mlookup m1 i = mlookup m2 i.
Proof.
  split.
  - intros ->. reflexivity.
  - unfold mlookup. intros Hlookup.
    destruct m1 as [m1 H1], m2 as [m2 H2]; simpl in *.
    assert (m1 = m2).
    { apply (map_raw_eq true). apply H1. apply H2. apply Hlookup. }
    subst m2.
    f_equal. apply is_True_proof_irrel.
Qed.

(*
So, the take home message is that when we want to represent subtypes and have
sensible results for equality we should:

1. Define a Boolean-valued predicate that expresses well-formedness.
2. Define a dependently typed record that includes a proof of well-formedness.

The use of a Boolean-valued well-formedness predicate is crucial: it ensures that
any any two proofs of the well-formedness property are equal, as we have proven
in the lemma `is_True_proof_irrel`. *)

(*
## Operations on maps

We will now proceed to define all of the map operations, namely:

  mempty : map A
  msingleton : nat -> A -> map A
  minsert : nat -> A -> map A -> map A
  mdelete : nat -> map A -> map A

The definitions of all of these operations proceeds in the following way:

1. Define the operation on raw maps.
2. Prove that the operation on raw maps preserves well-formedness.
3. Lift the operation from raw maps to maps.
4. Prove the desired properties involving `mlookup_raw` on raw maps.
5. Lift those properties to a version involving `mlookup`.
*)

(* ## The empty map *)

Definition mempty_raw {A} : map_raw A := nil.

Lemma mempty_raw_wf {A} : map_wf true (@mempty_raw A).
Proof. simpl. constructor. Qed.

Definition mempty {A} : map A := make_map mempty_raw mempty_raw_wf.

Lemma mempty_raw_lookup {A} (i : nat) : mlookup_raw (@mempty_raw A) i = None.
Proof. simpl. reflexivity. Qed.

Lemma mempty_lookup {A} (i : nat) : mlookup (@mempty A) i = None.
Proof. unfold mlookup, mempty, map_car. apply mempty_raw_lookup. Qed.

(* ## The singleton operation *)

Fixpoint msingleton_raw {A} (i : nat) (y : A) : map_raw A :=
  match i with
  | 0 => [Some y]
  | S i => None :: msingleton_raw i y
  end.

(* ### Exercise *)
(*
Prove the properties of `msingleton` below.
*)
Lemma msingleton_raw_wf {A} (b : bool) (i : nat) (y : A) :
  map_wf b (msingleton_raw i y).
Proof. revert A b y.
       induction i.
       - simpl. auto.
       - destruct b; simpl; apply IHi. 
Qed.

Definition msingleton {A} (i : nat) (x : A) : map A :=
  make_map (msingleton_raw i x) (msingleton_raw_wf true i x).

Lemma msingleton_raw_lookup {A} (i : nat) (y : A) :
  mlookup_raw (msingleton_raw i y) i = Some y.
Proof.
  revert A y.
  induction i.
  - simpl. reflexivity.
  - simpl. assumption.
Qed.


Lemma msingleton_raw_lookup_ne {A} (i j : nat) (y : A) :
  i <> j -> mlookup_raw (msingleton_raw i y) j = None.
Proof.
  revert j y.
  induction i.
  + intros.
    destruct j.
    * exfalso. apply H. reflexivity.
    * simpl. reflexivity.
  + intros.
    destruct j.
    * simpl in *. reflexivity.
    * simpl. apply IHi.
      unfold not.
      intro.
      subst i.
      apply H.
      reflexivity.
Qed.      
      
Lemma msingleton_lookup {A} (i : nat) (y : A) :
  mlookup (msingleton i y) i = Some y.
Proof.
  unfold msingleton, mlookup. simpl.
  apply msingleton_raw_lookup.
Qed.

Lemma msingleton_lookup_ne {A} (i j : nat) (y : A) :
  i <> j -> mlookup (msingleton i y) j = None.
Proof.
  unfold msingleton, mlookup. simpl. 
  apply msingleton_raw_lookup_ne.
Qed.  

(* ## The insert operation *)

Fixpoint minsert_raw {A} (i : nat) (y : A) (m : map_raw A) {struct m} : map_raw A :=
  match m with
  | [] => msingleton_raw i y
  | x :: m =>
    match i with
    | 0 => Some y :: m
    | S i => x :: minsert_raw i y m
    end
  end.

Lemma wf_mono {A} (b: bool) (m : map_raw A) :
  map_wf b m -> map_wf true m.
Proof.
  revert b.
  induction m.
  - intros.
    destruct b.
    + assumption.
    + exfalso. simpl in H. assumption.
  - intros.
    + destruct a.
      simpl in *. assumption.
      simpl in *. assumption.
Qed.

(* ### Exercise *)
(*
Prove the properties of `minsert` below.
*)
Lemma minsert_raw_wf {A} (b : bool) (i : nat) (y : A) (m : map_raw A) :
  map_wf b m -> map_wf b (minsert_raw i y m).
Proof.
  revert b i y.
  induction m.
  - intros. simpl. apply msingleton_raw_wf.
  - intros.
    destruct a.
    + destruct i.
      * simpl in *. assumption.
      * simpl in *. apply IHm. assumption.
    + destruct i.
      * simpl in *. eapply wf_mono. exact H.
      * simpl in *. apply IHm. assumption.
Qed.        
      
Definition minsert {A} (i : nat) (x : A) (m : map A) : map A :=
  match m with
  | make_map m Hm => make_map (minsert_raw i x m) (minsert_raw_wf true i x m Hm)
  end.

Lemma minsert_raw_lookup {A} (i : nat) (y : A) (m : map_raw A) :
  mlookup_raw (minsert_raw i y m) i = Some y.
Proof.
  revert m y.
  induction i.
  - intros.
    destruct m.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - intros.
    destruct m.
    + simpl. apply msingleton_lookup.
    + simpl. apply IHi.
Qed.

Lemma minsert_raw_lookup_ne {A} (i j : nat) (y : A) (m : map_raw A) :
  i <> j ->
  mlookup_raw (minsert_raw i y m) j = mlookup_raw m j.
Proof.
  revert m y.
  induction i.
  - intros.
    destruct m.
    + simpl minsert_raw.
      destruct j.
      * elim H. reflexivity.
      * simpl. reflexivity.
    + destruct j.
      * elim H. reflexivity.
      * simpl. reflexivity.
  - intros .
    destruct j, m.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. apply msingleton_raw_lookup_ne.
      intro.
      elim H. f_equal. assumption. (* JULES: discuss about primitive inequality; previously omega *)
    + simpl.
      Restart.
      revert i j.
      induction m.
  -  intros. simpl. apply msingleton_lookup_ne. assumption.
  - intros.
    destruct i, j.
    + elim H. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. apply IHm. omega.
Qed.     
      
      
Lemma minsert_lookup {A} (i : nat) (y : A) (m : map A) :
  mlookup (minsert i y m) i = Some y.
Proof.
  revert i y m.
  induction m.
  unfold mlookup, minsert, map_car.
  apply minsert_raw_lookup.
Qed.      

Lemma minsert_lookup_ne {A} (i j : nat) (y : A) (m : map A) :
  i <> j ->
  mlookup (minsert i y m) j = mlookup m j.
Proof.
  revert i j y m.
  induction m.
  unfold mlookup, minsert, map_car.
  apply minsert_raw_lookup_ne.
Qed.

(* ## The delete operation *)
Fixpoint mcons {A} (x : option A) (m : map_raw A) : map_raw A :=
  match x with
  | None =>
     match m with
     | [] => []
     | _ => None :: m
     end
  | _ => x :: m
  end.

Fixpoint mdelete_raw {A} (i : nat) (m : map_raw A) {struct m} : map_raw A :=
  match m with
  | [] => []
  | x :: m =>
    match i with
    | 0 => mcons None m
    | S i => mcons x (mdelete_raw i m)
    end
  end.

Lemma mcons_lookup_0 {A} (x : option A) (m : map_raw A) :
  mlookup_raw (mcons x m) 0 = x.
Proof. destruct x, m; reflexivity. Qed.

Lemma mcons_lookup_S {A} (x : option A) (m : map_raw A) (i : nat) :
  mlookup_raw (mcons x m) (S i) = mlookup_raw m i.
Proof. destruct x, m; reflexivity. Qed.

Arguments mcons : simpl never.
(* The `Arguments`command with the `simpl never` flag makes sure that `simpl`
does not unfold `mcons`. This will make some proofs easier, as we rather rewrite
using the lemmas `mcons_lookup_0` and `mcons_lookup_S` to avoid matches to
appear in the goal. *)

Lemma mcons_wf {A} (b : bool) (x : option A) (m : map_raw A) :
  map_wf b m -> map_wf b (mcons x m).
Proof. destruct m, x; simpl; auto. Qed.

(* ### Exercise *)
(*
Prove the properties of `mdelete` below.
*)
Lemma mdelete_raw_wf {A} (b : bool) (i : nat) (m : map_raw A) :
  map_wf b m -> map_wf true (mdelete_raw i m).
Proof.
  revert b i.
  induction m.
  - intros. simpl. auto.
  - intros. destruct i.
    + simpl. apply mcons_wf.
      destruct a.
      * simpl in H. assumption.
      * simpl in H. eapply wf_mono. exact H.
    + simpl. apply mcons_wf. eapply IHm.
      destruct a.
      * simpl in H. exact H.
      * simpl in H. eapply wf_mono. exact H.
Qed.       
      
Definition mdelete {A} (i : nat) (m : map A) : map A :=
  match m with
  | make_map m Hm => make_map (mdelete_raw i m) (mdelete_raw_wf true i m Hm)
  end.

Lemma mdelete_raw_lookup {A} (i : nat) (m : map_raw A) :
  mlookup_raw (mdelete_raw i m) i = None.
Proof.
  revert m.
  induction i.
  - intro.
    destruct m.
    + simpl. reflexivity.
    + simpl. apply mcons_lookup_0.
  - intro.
    destruct m.
    + simpl. reflexivity.
    + simpl. rewrite mcons_lookup_S.
      apply IHi.
Qed.

Lemma mdelete_raw_lookup_ne {A} (i j : nat) (m : map_raw A) :
  i <> j ->
  mlookup_raw (mdelete_raw i m) j = mlookup_raw m j.
Proof.
  revert m.
  induction i.
  - intros.
    destruct m.
    + simpl. reflexivity.
    + destruct j.
      * elim H. reflexivity.
      * simpl. apply mcons_lookup_S.
  - intros.
    (* to be able to reuse the mcons lemma we have to do a case distinction on m *)
    destruct m.
    (* now eventually I have to use the induction hypothesis *)
    + simpl. reflexivity.
      (* but destructing  j will not yeild a IH that I can use later on
    + destruct j.
      * simpl. apply mcons_lookup_0.
      * simpl mdelete_raw.
        rewrite mcons_lookup_S.
       *)
    + simpl mdelete_raw.
      destruct j.
      * simpl. apply mcons_lookup_0.
      * rewrite mcons_lookup_S. simpl mlookup_raw.
        Restart.
        revert i j.
        induction m.
  - intros.
    simpl. reflexivity.
  - intros.
    destruct i, j.
    + elim H. reflexivity.
    + simpl. apply mcons_lookup_S.
    + simpl. apply mcons_lookup_0.
    + simpl. rewrite mcons_lookup_S.
      apply IHm. omega. (* again here I should be able to prove S i <> S j |- i <> j *)
Qed.

Lemma mdelete_lookup {A} (i : nat) (m : map A) :
  mlookup (mdelete i m) i = None.
Proof.
  revert i m.
  induction m.
  unfold mlookup, mdelete, map_car.
  apply mdelete_raw_lookup.
Qed.

Lemma mdelete_lookup_ne {A} (i j : nat) (m : map A) :
  i <> j ->
  mlookup (mdelete i m) j = mlookup m j.
Proof.
  revert i m.
  induction m.
  unfold mlookup, mdelete, map_car.
  apply mdelete_raw_lookup_ne.
Qed.

Definition mfresh_raw {A} (m : map_raw A) : nat := length m.

Definition mfresh {A} (m : map A) : nat := mfresh_raw (map_car m).

(* ### Exercise *)
(*
Prove the following lemmas.
*)
Definition mfresh_lookup_raw {A} (m : map_raw A) :
  mlookup_raw m (mfresh_raw m) = None.
Proof.
  induction m.
  - simpl. reflexivity.
  - simpl. assumption.
Qed.


Definition mfresh_lookup {A} (m : map A) : mlookup m (mfresh m) = None.
Proof.
  destruct m. unfold mlookup. simpl.
  unfold mfresh. simpl. apply mfresh_lookup_raw.
Qed.

Lemma munion_lookup_inv_l {A} (m1 m2 : map A) x:
  mlookup (munion m1 m2) x = None -> mlookup m1 x = None.
Proof.
  intros.
  rewrite munion_lookup in H.
  destruct (mlookup m1 x).
  + discriminate.
  + simpl in H. reflexivity.
Qed.


Lemma munion_lookup_inv_r {A} (m1 m2 : map A) x:
  mlookup (munion m1 m2) x = None -> mlookup m2 x = None.
Proof.
  intros.
  rewrite munion_lookup in H.
  destruct (mlookup m1 x).
  + discriminate.
  + simpl in H. assumption.
Qed.

Lemma mfresh_lookup_r {A} (m mf : map A):
      mlookup mf (mfresh (munion m mf)) = None.
Proof.
  eapply munion_lookup_inv_r.
  eapply mfresh_lookup.
Qed.

Lemma mfresh_lookup_l {A} (m mf : map A):
      mlookup m (mfresh (munion m mf)) = None.
Proof.
  eapply munion_lookup_inv_l.
  eapply mfresh_lookup.
Qed.


Lemma mfresh_disjoint_r {A} (m mf: map A) v:
  mdisjoint (msingleton (mfresh (munion m mf)) v) mf.
Proof.
  apply mdisjoint_singleton.
  apply mfresh_lookup_r.
Qed.

Lemma mfresh_disjoint_l {A} (m mf: map A) v:
  mdisjoint (msingleton (mfresh (munion m mf)) v) m.
Proof.
  apply mdisjoint_singleton.
  apply mfresh_lookup_l.
Qed.

(* what happens when free is called on one of two disjoint memories? *)
(* we only need one lemma here because we can only free memory in m *)
Lemma mdelete_disjoint {A} (m mf : map A) l:
  mdisjoint m mf -> mdisjoint (mdelete l m) mf.
Proof.
  intros.
  unfold mdisjoint.
  intros.
  destruct (Nat.eq_dec l i).
  - subst l.
    left. apply mdelete_lookup.
  - destruct (H i) as [Hm | Hmf].
    + left. rewrite mdelete_lookup_ne; auto.
    + auto.
Qed.

Lemma mdelete_inv {A} (m : map A) l:
    mlookup m l = None -> (mdelete l m) = m.
Proof.
  intro.
  apply map_eq.
  intro.
  destruct (Nat.eq_dec l i).
  - subst l.
    rewrite mdelete_lookup. symmetry. assumption.
  - rewrite mdelete_lookup_ne. reflexivity. assumption.
Qed.

Lemma disjoint_r_some {A} (m mf : map A) l v:
  mlookup (munion m mf) l = Some(v) ->
  mdisjoint m mf -> mlookup m l = None -> mlookup mf l = Some(v).
Admitted.

Lemma disjoint_r_none {A} (m mf : map A) l v:
  mlookup (munion m mf) l = Some(v) ->
  mdisjoint m mf -> mlookup m l = Some(v) -> mlookup mf l = None.
Proof.
  intros.
  specialize (H0 l).
  destruct H0.
  + rewrite H1 in H0. discriminate.
  + assumption.
Qed.

Lemma disjoint_l_some {A} (m mf : map A) l v:
  mlookup (munion m mf) l = Some(v) ->
  mdisjoint m mf -> mlookup mf l = None -> mlookup m l = Some(v).
Admitted.


Lemma disjoint_l_none {A} (m mf : map A) l v:
  mlookup (munion m mf) l = Some(v) ->
  mdisjoint m mf -> mlookup mf l = Some(v) -> mlookup m l = None.
Proof.
  intros.
  specialize (H0 l).
  destruct H0.
  + assumption.
  + rewrite H1 in H0. discriminate.
Qed.
