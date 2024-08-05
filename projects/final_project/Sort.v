(** * Sort: Insertion Sort *)

(** Sorting can be done in expected O(N log N) time by various
    algorithms (quicksort, mergesort, heapsort, etc.).  But for
    smallish inputs, a simple quadratic-time algorithm such as
    insertion sort can actually be faster.  It's certainly easier to
    implement -- and to verify. *)

(** If you don't recall insertion sort or haven't seen it in
    a while, see Wikipedia or read any standard textbook; for example:

    - Sections 2.0 and 2.1 of _Algorithms, Fourth Edition_, by
      Sedgewick and Wayne, Addison Wesley 2011; or

    - Section 2.1 of _Introduction to Algorithms, 3rd Edition_, by
      Cormen, Leiserson, and Rivest, MIT Press 2009. *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From VFA Require Import Perm.

(* ################################################################# *)
(** * The Insertion-Sort Program *)

(** Insertion sort is usually presented as an imperative program
    operating on arrays.  But it works just as well as a functional
    program operating on linked lists. *)

(* [insert i l] inserts [i] into its sorted place in list [l].
   Precondition: [l] is sorted. *)
Fixpoint insert (i : nat) (l : list nat) :=
  match l with
  | [] => [i]
  | h :: t => if i <=? h then i :: h :: t else h :: insert i t
  end.

Fixpoint sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert h (sort t)
  end.

Example sort_pi :
  sort [3;1;4;1;5;9;2;6;5;3;5]
  = [1;1;2;3;3;4;5;5;5;6;9].
Proof. simpl. reflexivity. Qed.

(** What Sedgewick/Wayne and Cormen/Leiserson/Rivest don't acknowlege
    is that the arrays-and-swaps model of sorting is not the only one
    in the world.  We are writing _functional programs_, where our
    sequences are (typically) represented as linked lists, and where
    we do _not_ destructively splice elements into those lists. *)

(** As usual with functional lists, the output of [sort] may share
    memory with the input.  For example: *)

Compute insert 7 [1; 3; 4; 8; 12; 14; 18].
(* = [1; 3; 4; 7; 8; 12; 14; 18] *)

(** The tail of this list, [12 :: 14 :: 18 :: []], is not disturbed or
    rebuilt by the [insert] algorithm.  The head [1 :: 3 :: 4 :: 7 :: ...]
    contains new nodes constructed by [insert].  The first three nodes
    of the old list, [1 :: 3 :: 4 :: ...], will likely be
    garbage-collected if no other data structure is still pointing at
    them.  Thus, in this typical case,

     - Time cost = 4X

     - Space cost = (4-3)Y = Y

    where X and Y are constants, independent of the length of the
    tail.  The value Y is the number of bytes in one list node: 2 to 4
    words, depending on how the implementation handles
    constructor-tags.  We write (4-3) to indicate that four list nodes
    are constructed, while three list nodes become eligible for
    garbage collection.

    We will not prove such things about the time and space cost, but
    they are true anyway, and we should keep them in consideration. *)

(* ################################################################# *)
(** * Specification of Correctness *)

(** A sorting algorithm must rearrange the elements into a list
    that is totally ordered. There are many ways we might express that
    idea formally in Coq.  One is with an inductively-defined
    relation that says: *)

(** - The empty list is sorted.

    - Any single-element list is sorted.

    - For any two adjacent elements, they must be in the proper order. *)

Inductive sorted : list nat -> Prop :=
| sorted_nil :
    sorted []
| sorted_1 : forall x,
    sorted [x]
| sorted_cons : forall x y l,
    x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Hint Constructors sorted : core.

(** This definition might not be the most obvious. Another
    definition, perhaps more familiar, might be: for any two elements
    of the list (regardless of whether they are adjacent), they should
    be in the proper order.  Let's try formalizing that.

    We can think in terms of indices into a list [lst], and say: for
    any valid indices [i] and [j], if [i < j] then [index lst i <=
    index lst j], where [index lst n] means the element of [lst] at
    index [n].  Unfortunately, formalizing this idea becomes messy,
    because any Coq function implementing [index] must be total: it
    must return some result even if the index is out of range for the
    list.  The Coq standard library contains two such functions: *)

Check nth : forall A : Type, nat -> list A -> A -> A.
Check nth_error : forall A : Type, list A -> nat -> option A.

(** These two functions ensure totality in different ways:

    - [nth] takes an additional argument of type [A] --a _default_
      value-- to be returned if the index is out of range, whereas

    - [nth_error] returns [Some v] if the index is in range and [None]
      --an error-- otherwise.

    If we use [nth], we must ensure that indices are in range: *)

Definition sorted'' (al : list nat) := forall i j,
    i < j < length al ->
    nth i al 0 <= nth j al 0.

(** The choice of default value, here 0, is unimportant, because it
    will never be returned for the [i] and [j] we pass.

    If we use [nth_error], we must add additional antecedents: *)

Definition sorted' (al : list nat) := forall i j iv jv,
    i < j ->
    nth_error al i = Some iv ->
    nth_error al j = Some jv ->
    iv <= jv.

(** Here, the validity of [i] and [j] are implicit in the fact
    that we get [Some] results back from each call to [nth_error]. *)

(** All three definitions of sortedness are reasonable.  In practice,
    [sorted'] is easier to work with than [sorted''] because it
    doesn't need to mention the [length] function. And [sorted] is
    easiest, because it doesn't need to mention indices. *)

(** Using [sorted], we specify what it means to be a correct sorting
    algorthm: *)

Definition is_a_sorting_algorithm (f: list nat -> list nat) := forall al,
    Permutation al (f al) /\ sorted (f al).

(** Function [f] is a correct sorting algorithm if [f al] is
    [sorted] and is a permutation of its input. *)

(* ################################################################# *)
(** * Proof of Correctness *)

(** In the following exercises, you will prove the correctness of
    insertion sort. *)

(** **** Exercise: 3 stars, standard (insert_sorted) *)

(* Prove that insertion maintains sortedness. Make use of tactic
   [bdestruct], defined in [Perm]. *)

Lemma insert_sorted:
  forall a l, sorted l -> sorted (insert a l).
Proof.
  intros a l S. induction S; simpl.
  - apply sorted_1.
  - bdestruct (a <=? x).
    + auto.
    + apply sorted_cons.
        * lia.
        * auto.
  - bdestruct (a <=? x).
    + auto.
    + simpl in IHS. bdestruct (a <=? y).
        * apply sorted_cons.
            -- lia.
            -- auto.
        * apply sorted_cons.
            -- lia.
            -- apply IHS. 
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (sort_sorted) *)

(** Using [insert_sorted], prove that insertion sort makes a list
    sorted. *)

Theorem sort_sorted: forall l, sorted (sort l).
Proof.
    intros. induction l.
    - auto.
    - apply insert_sorted. auto. 
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (insert_perm) *)

(** The following lemma will be useful soon as a helper. Take
    advantage of helpful theorems from the [Permutation] library. *)

Lemma insert_perm: forall x l,
    Permutation (x :: l) (insert x l).
Proof.
    intros. induction l.
    - auto.
    - simpl. bdestruct (x <=? a).
        + apply Permutation_refl.
        + apply perm_trans with (a :: x :: l).
            * apply perm_swap.
            * apply perm_skip. apply IHl.
Qed.

(** **** Exercise: 3 stars, standard (sort_perm) *)

(** Prove that [sort] is a permutation, using [insert_perm]. *)

Theorem sort_perm: forall l, Permutation l (sort l).
Proof.
    intros. induction l.
    - auto.
    - simpl. apply perm_trans with (a :: sort l).
        + apply perm_skip. apply IHl.
        + apply insert_perm.
Qed.

(** **** Exercise: 1 star, standard (insertion_sort_correct) *)

(** Finish the proof of correctness! *)

Theorem insertion_sort_correct:
    is_a_sorting_algorithm sort.
Proof.
    split.
    - apply sort_perm.
    - apply sort_sorted. 
Qed.

(* ################################################################# *)
(** * Validating the Specification (Advanced) *)

(** You can prove that a program satisfies a specification, but how
    can you prove you have the right specification?  Actually, you
    cannot.  The specification is an informal requirement in your
    mind.  As Alan Perlis quipped, "One can't proceed from the
    informal to the formal by formal means."

    But one way to build confidence in a specification is to state it
    in two different ways, then prove they are equivalent. *)

Lemma nth_error_nil:
    forall A (ls: list A) i, ls = [] -> nth_error ls i = None.
Proof. 
    intros. rewrite H. destruct i. reflexivity. reflexivity.
Qed.

(** **** Exercise: 4 stars, advanced (sorted_sorted') *)
Lemma sorted_sorted': forall al, sorted al -> sorted' al.
(** Hint: Instead of doing induction on the list [al], do induction on
    the sortedness of [al]. This proof is a bit tricky, so you may
    have to think about how to approach it, and try out one or two
    different ideas.*)
Proof.
    assert (N1: forall A (x:A) y i, nth_error [x] i = Some y -> x = y /\ i = 0).
        { intros. split. destruct i. 
        - simpl in *. inv H. reflexivity.
        - simpl in *. rewrite nth_error_nil in H. discriminate. reflexivity.
        - destruct i. reflexivity. simpl in *. rewrite nth_error_nil in H. discriminate. reflexivity. }
    intros. induction H; unfold sorted'. 
    - intros. rewrite nth_error_nil in H0. discriminate. reflexivity.
    - intros. apply N1 in H0, H1. lia.
    - inv H0.
        + intros. destruct i; destruct j; try lia; simpl in *.
            * apply N1 in H2. inv H1. lia.
            * apply N1 in H1, H2. lia.
        + intros. destruct i; destruct j; try lia; simpl in *.
            * destruct j. 
                { simpl in *. inv H1. inv H2. lia. }
                { assert (forall k kv, nth_error (y0 :: l0) k = Some kv -> y <= kv).
                { intros. unfold sorted' in IHsorted. apply IHsorted with 0 (S k). lia. 
                    auto. simpl. apply H5. } 
                simpl in H2. apply H5 in H2. inv H1. lia. }
            * apply Nat.succ_lt_mono in H0. unfold sorted' in IHsorted. 
                apply IHsorted with i j; assumption.
Qed.

(** **** Exercise: 3 stars, advanced (sorted'_sorted) *)
Lemma sorted'_sorted : forall al, sorted' al -> sorted al.
(** Here, you can't do induction on the sortedness of the list,
    because [sorted'] is not an inductive predicate. But the proof
    is less tricky than the previous. *)
Proof.
    intros. unfold sorted' in H. induction al.
        - apply sorted_nil.
        - destruct al.
          + apply sorted_1.
          + apply sorted_cons.
            * apply H with (i:= 0) (j:= 1); try lia; simpl; reflexivity.
            * apply IHal. intros. apply H with (i := S i) (j := S j).
              -- lia.
              -- simpl. rewrite  H1. reflexivity.
              -- simpl. rewrite H2. reflexivity.
(* intros al H.
  induction al as [| a [| b t] IH].
  - apply sorted_nil.
  - apply sorted_1.
  - apply sorted_cons.
    + apply (H 0 1 a b). lia.
        * simpl. reflexivity.
        * simpl. reflexivity.
    + apply IH. intros i j iv jv Hlt Hnth1 Hnth2.
      apply (H (S i) (S j) iv jv). lia.
        * simpl. apply Hnth1.
        * simpl. apply Hnth2. *)
Qed.

(* ################################################################# *)
(** * Proving Correctness from the Alternative Spec (Optional) *)

(** Depending on how you write the specification of a program, it can
    be harder or easier to prove correctness.  We saw that predicates
    [sorted] and [sorted'] are equivalent.  It is significantly
    harder, though, to prove correctness of insertion sort directly
    from [sorted'].

    Give it a try!  The best proof we know of makes essential use of
    the auxiliary lemma [nth_error_insert], so you may want to prove
    that first.  And some other auxiliary lemmas may be needed too.
    But maybe you will find a simpler appraoch!

    DO NOT USE [sorted_sorted'], [sorted'_sorted], [insert_sorted], or
    [sort_sorted] in these proofs.  That would defeat the purpose! *)

(** **** Exercise: 5 stars, standard, optional (insert_sorted') *)

Lemma nth_error_insert : forall l a i iv,
    nth_error (insert a l) i = Some iv ->
    a = iv \/ exists i', nth_error l i' = Some iv.
Proof.
    intros. generalize dependent i.
    induction l; simpl; intros.
    - destruct i.
        + left. inversion H. reflexivity.
        + simpl in H. destruct i; discriminate H.
    - bdestruct (a <=? a0).
        + destruct i; inversion H.
            * left. reflexivity.
            * right. exists i. reflexivity.
        + destruct i; inversion H.
            * right. exists 0. reflexivity.
            * destruct (IHl _ H2) as [Ha | [i' H']].
                -- left. assumption. 
                -- right. exists (S i'). simpl. rewrite H'. rewrite H2. reflexivity. 
Qed.


(* ---------------- *)


(* Lemma insert_sorted':
  forall a l, sorted' l -> sorted' (insert a l).
Proof.
  intros a l Hsorted'.
  unfold sorted' in *.
  intros i j iv jv Hlt Hiv Hjv.
  apply nth_error_insert in Hiv as [Ha | [i' Hi']].
  - (* Case: iv = a *)
    subst iv.
    destruct (nth_error_insert l a j jv Hjv) as [Hb | [j' Hj']].
    + (* Subcase: jv = a *)
      subst jv. lia.
    + (* Subcase: jv is in the original list *)
      unfold sorted' in Hsorted'.
      specialize (Hsorted' i j).
      assert (i < j) by lia.
      apply Hsorted' in H; try assumption.
  - (* Case: iv is in the original list *)
    destruct (nth_error_insert l a j jv Hjv) as [Hb | [j' Hj']].
    + (* Subcase: jv = a *)
      subst jv.
      unfold sorted' in Hsorted'.
      specialize (Hsorted' i' j').
      assert (i' < j') by lia.
      apply Hsorted' in H; try assumption.
    + (* Subcase: jv is in the original list *)
      unfold sorted' in Hsorted'.
      specialize (Hsorted' i' j').
      assert (i' < j') by lia.
      apply Hsorted' in H; try assumption.
Qed. *)

(* Lemma insert_sorted':
  forall a l, sorted' l -> sorted' (insert a l).
Proof.
  intros a l Hsorted. (* Assume l is sorted according to sorted' *)
  unfold sorted'. (* Unfold the definition of sorted' *)
  intros i j iv jv Hlt Hiv Hjv. (* Introduce indices and values *)

  (* Apply nth_error_insert to both indices i and j *)
  apply nth_error_insert in Hiv. (* iv can be a or some element from l *)
  apply nth_error_insert in Hjv. (* jv can be a or some element from l *)

  (* Analyze the cases for iv and jv based on nth_error_insert results *)
  destruct Hiv as [Hiv_eq | [i' Hiv']]; (* Either iv = a or iv is from the original list l *)
  destruct Hjv as [Hjv_eq | [j' Hjv']]. (* Either jv = a or jv is from the original list l *)

  - (* Case: iv = a and jv = a *)
    subst. lia. (* Both are equal, trivially ordered *)

  - assert (a <= jv).
    { apply Hsorted with (i := i) (j := j); try lia.
      - assumption. (* The hypothesis Hlt ensures the indices i and j' respect order *)
      - simpl. rewrite Hiv'. reflexivity.
    }
    lia.

  - (* Case: iv from l and jv = a *)
    subst. (* Substitute a for jv *)
    assert (iv <= a).
    { apply Hsorted with (i := i') (j := j); try lia.
      - simpl. rewrite Hjv'. reflexivity.
      - assumption.
    }
    lia.

  - (* Case: iv from l and jv from l *)
    apply Hsorted with (i := i') (j := j'); try lia.
    - assumption.
    - assumption.
Qed. *)


(* Lemma insert_sorted' :
  forall a l, sorted' l -> sorted' (insert a l).
Proof.
  intros a l Hsorted'.
  unfold sorted' in *.
  intros i j iv jv Hlt Hnth1 Hnth2.

  (* Apply nth_error_insert to handle the case analysis *)
  apply nth_error_insert in Hnth1.
  - (* Case: i corresponds to the inserted element a *) (* iv is a *)
    apply nth_error_insert in Hnth2.
    +  
    + (* Subcase: j corresponds to some element in l *)
      (* Apply sorted' to i = 0, j' *)
      apply Hsorted' with (i := 0) (j := j') in Hnth1'; try lia.
      simpl in Hnth1'.
      exact Hnth1'.

  - (* Case: i corresponds to some element in l *)
    apply nth_error_insert in Hnth2 as [Ha' | [j' Hnth2']].
    + (* Subcase: j corresponds to the inserted element a *)
      subst jv. (* jv is a *)
      (* Compare iv (from i') with a *)
      apply Hsorted' with (i := i') (j := 0) in Hnth1'; try lia.
      simpl in Hnth1'.
      exact Hnth1'.
      
    + (* Subcase: j corresponds to some element in l *)
      (* Both i and j refer to elements in l *)
      apply Hsorted' with (i := i') (j := j') in Hnth1'; try assumption.
      lia. (* iv <= jv as sorted' l *)
Qed. *)



(* Lemma insert_sorted':
  forall a l, sorted' l -> sorted' (insert a l).
Proof.
  intros.
  unfold sorted' in *.
  intros.

  (* Case analysis based on whether i and j fall within the length of l or not *)
  destruct (le_lt_dec i (length l)) as [Hile | Hilt].
  - (* Case 1: i < length l *)
    destruct (le_lt_dec j (length l)) as [Hjle | Hjlt].
    + s lia.(* Case 1a: j < length l *)
      apply nth_error_insert in H1.
      apply nth_error_insert in H2.
      destruct H1 as [Hia | [i' Hith]].
      * (* Subcase: i corresponds to the inserted element *)
        destruct (lt_dec i (length l)).
        -- (* i < length l *) 
           rewrite <- Hia. 
           apply H in H2. 
           apply Hjth.
        -- (* This case is impossible because i < length l by assumption *)
           discriminate.
      * (* Subcase: i corresponds to some element in l *)
        destruct Hjth as [Hjb | [j' Hjth]].
        -- (* Case: j corresponds to the inserted element *)
           rewrite Hjth. 
           apply Hsorted in Hith. 
           apply Hith.
        -- (* Case: j corresponds to some element in l *)
           apply Hsorted with (i := i') (j := j').
           -- apply Hilt.
           -- apply Hjlt.
    + (* Case 1b: j >= length l *)
      destruct (lt_dec j (length l)).
      * (* This case is impossible because j >= length l *)
        discriminate.
      * (* If j is out of bounds, then j should be >= length l *)
        destruct (lt_dec i (length l)).
        -- (* i < length l *)
           apply Hsorted with (i := i) (j := j).
           -- apply Hile.
           -- apply Hjlt.
        -- (* This case is impossible because i >= length l by assumption *)
           discriminate.
  - (* Case 2: i >= length l *)
    destruct (lt_dec j (length l)).
    + (* Case 2a: j < length l *)
      (* This is a contradiction because i >= length l implies j cannot be less than length l *)
      discriminate.
    + (* Case 2b: j >= length l *)
      apply Hsorted with (i := i) (j := j).
      -- apply Hilt.
      -- apply Hjlt.
Qed. *)




(* Lemma insert_sorted':
  forall a l, sorted' l -> sorted' (insert a l).
Proof.
  intros.
  unfold sorted'. (* Unfold the definition of sorted'. *)
  intros. (* Introduce variables for indices and values. *)
  apply nth_error_insert in H1.
  apply nth_error_insert in H2.
  destruct H1 as [H1 | [i' H1]].
  - (* Case: a = iv *)
    destruct H2 as [H2 | [j' H2]].
    + (* Subcase: a = jv *)
      lia.
    +
     (* Substitute a for iv *)
    assert (Hlen : i < j).
    { lia. }
    specialize (H i j a jv Hlen eq_refl Hjv).
    lia. (* Use the sorted' property for l *)
     (* Subcase: exists j', nth_error l j' = Some jv *)
      destruct (lt_dec i j').
      * (* i' < j *)
        assert (Hlen : i < j').
        { lia. }
        specialize (H i j' a jv Hlen eq_refl H2).

        specialize (H 0 j' a jv).
        lia.
      * (* i' >= j *)
        lia.
  - (* Case: exists i', nth_error l i' = Some iv *)
    destruct Hjv as [Hjv | [j' Hjv]].
    + (* Subcase: a = jv *)
      subst. lia.
    + (* Subcase: exists j', nth_error l j' = Some jv *)
      specialize (H i' j' iv jv Hi Hiv Hjv).
      lia.
Qed. *)




(* Lemma Forall_nth:
  forall {A: Type} (P: A -> Prop) d (al: list A),
    Forall P al <-> (forall i, i < length al -> P (nth i al d)).
Proof.
  intros. split; intro H.
  - induction H.
    + intros. simpl in H. lia. 
    + intros. destruct i.
      * assumption.
      * apply IHForall. simpl in H0. simpl in H1. lia.
  - induction al as [| a al' IH].
    + constructor. 
    + constructor.
      * apply (H 0). simpl. lia.
      * apply IH. intros. apply (H (S i)). simpl. lia.
Qed. *)

(* Lemma insert_sorted':
  forall a l, sorted' l -> sorted' (insert a l).
Proof.
  unfold sorted'.
  induction l; intros.
  - simpl. intros. destruct i, j; try lia. simpl in *. rewrite nth_error_nil in H2. inversion H2. reflexivity. simpl in *. rewrite nth_error_nil in *; try inversion H2; reflexivity.
  - intros. destruct i, j.
    + lia.
    + simpl. bdestruct (a <=? a0).
      * destruct j; simpl in *.
        -- apply le_trans with (m := a0); auto.
        -- apply (H 0 (S j)). simpl. lia.
      * assert (Forall (fun n => a0 <= n) l).
        {
          rewrite Forall_nth. intros. apply (H (S i)). simpl. lia.
        }
        assert (Forall (fun n => a0 <= n) (a :: l)).
        {
          constructor; auto. lia.
        }
        assert (Forall (fun n => a0 <= n) (insert a l)).
        {
          apply Forall_perm with (a :: l).
          apply insert_perm. assumption.
        }
        rewrite Forall_nth in H4.
        apply H4. simpl in H0. lia.
    + lia.
    + simpl. simpl in H0.
      bdestruct (a <=? a0).
      * apply H. simpl. simpl in H0. lia.
      * apply IHl. simpl in H0; lia.
        intros. apply (H (S i0) (S j0)). simpl. lia.
Qed. *)


(* Lemma insert_sorted':
  forall a l, sorted' l -> sorted' (insert a l).
Proof.
  intros a l H_sorted'. unfold sorted' in *.
  intros i j iv jv Hlt Hnth_i Hnth_j.
  assert (Hnth_i_insert: a = iv \/ exists i', nth_error l i' = Some iv).
  { apply nth_error_insert with (i := i). assumption. }
  assert (Hnth_j_insert: a = jv \/ exists j', nth_error l j' = Some jv).
  { apply nth_error_insert with (i := j). assumption. }
  destruct Hnth_i_insert as [Hi_eq | [i' Hi_l]].
  - destruct Hnth_j_insert as [Hj_eq | [j' Hj_l]].
    + subst. lia.
    + subst. apply nth_error_insert with (i := 0) in Hnth_i. apply H_sorted' with (i := 0) (j := j').
      * lia.
      * reflexivity.
      * assumption.
  - destruct Hnth_j_insert as [Hj_eq | [j' Hj_l]].
    + subst. apply H_sorted' with (i := i') (j := 0).
      * simpl. lia.
      * assumption.
      * reflexivity.
    + apply H_sorted' with (i := i') (j := j').
      * assumption.
      * assumption.
      * assumption.
Qed. *)


(* Lemma insert_sorted':
  forall a l, sorted' l -> sorted' (insert a l).
Proof.
  intros.
  unfold sorted' in *.
  intros.
  apply nth_error_insert in H1, H2.
  destruct H1.
  - destruct H2.
    + subst. reflexivity.
    + subst. apply H with (i := 0) (j := S j); auto.
        * destruct j; lia.
        * apply H2 with (i' := 0). 
  - destruct Hnth_j as [Hj | [j' Hj']].
    + subst. apply Nat.le_trans with (m := iv).
      * apply Hsorted' with (i := i') (j := i); auto. lia.
      * auto.
    + apply Hsorted' with (i := i') (j := j'); auto. lia.
Qed. *)

(* Lemma insert_sorted':
  forall a l, sorted' l -> sorted' (insert a l).
Proof.
  intros.
  induction l.
  - simpl. unfold sorted'.
    intros.
    destruct i, j; simpl in *.
    + inversion H1. inversion H2.
      subst. reflexivity.
    + destruct j; discriminate H2.
    + destruct i; discriminate H1.
    + destruct j; discriminate H2.
  - simpl. bdestruct (a <=? a0).
    + unfold sorted'. intros i j iv jv H_lt H_i H_j.
      destruct i, j; simpl in *; try lia.
      * inversion H_i; subst. clear H_i.
        simpl in H_j. injection H_j as H_j. subst.
        apply (less_than_all_sorted a a0 l' H_sorted' H_sorted' j jv).
        assumption.
      * simpl in H_i. destruct j; discriminate H_j.
      * simpl in *.
        apply (H_sorted' i j iv jv); try lia.
    + intros i j iv jv H_lt H_i H_j.
      destruct i, j; simpl in *; try lia.
        inversion H_i. inversion H_j. subst. reflexivity.
        inversion H_i; subst. clear H_i.
        simpl in H_j. injection H_j as H_j. subst.
        apply (less_than_insert_to_tail _ _ _ H_sorted' H_sorted' j jv).
        simpl in H_i. destruct j; discriminate H_j.
        apply IHl.
        apply sorted_tail in H_sorted'.
        apply (H_sorted' i j iv jv); try lia.
Qed. *)

(* Lemma less_than_all_sorted :
  forall (a b : nat) (l : list nat),
    sorted' (b :: l) ->
    a <= b ->
    (forall i, nth_error (b :: l) i = Some a -> a <= b).
Proof.
  intros a b l Hsorted Hle.
  unfold sorted' in Hsorted.
  intros i Hnth.
  destruct i.
  - simpl in Hnth.
    destruct (nth_error (b :: l) 0) eqn:H0.
    + inversion Hnth. reflexivity.
    + inversion Hnth. reflexivity.
  - simpl in Hnth.
    destruct (nth_error l (i - 1)) eqn:Hnth_l; lia. 
Qed. *)


(* Lemma insert_sorted':
  forall a l, sorted' l -> sorted' (insert a l).
Proof.
  intros.
  induction l as [| a0 l' IHl'].
  - unfold sorted'. intros.
    destruct i; destruct j; try lia.
    + simpl in H1. inversion H1. simpl in H2. rewrite nth_error_nil in H2. discriminate H2. reflexivity.
    + simpl in H1. rewrite nth_error_nil in H1. discriminate H1. reflexivity.
  - simpl. bdestruct (a <=? a0).
    + unfold sorted'. intros.
      destruct i; destruct j; try lia.
      * simpl in H2, H3. 
        destruct (nth_error (a0 :: l') j) eqn:Hi.
        -- destruct (nth_error (a0 :: l') j) eqn: Hj.
           ++ inversion H1. inversion H2. subst. apply (less_than_all_sorted iv a0 l' H H0 jv).
           ++ apply (less_than_all_sorted iv a0 l' H0 Hj H1).
        -- apply (less_than_all_sorted iv a0 l' H0 Hj H1).
      * apply sorted_tail in H. 
        apply IHl' in H.
        apply (H i j iv jv); lia.
    + unfold sorted'. intros i j iv jv H0 H1 H2.
      destruct i; destruct j; try lia.
      * simpl in H1. 
        destruct (nth_error (a0 :: l') i) eqn: Hi.
        -- destruct (nth_error (a0 :: l') j) eqn: Hj.
           ++ apply (less_than_insert_to_tail _ _ _ H H0 j jv Hj).
           ++ apply (less_than_insert_to_tail _ _ _ H H0 j jv Hj).
        -- apply (less_than_insert_to_tail _ _ _ H H0 j jv Hj).
      * apply sorted_tail in H. 
        apply IHl' in H.
        apply (H i j iv jv); lia.
Qed. *)


(* Lemma insert_sorted':
  forall a l, sorted' l -> sorted' (insert a l).
Proof.
  intros a l Hsorted.
  unfold sorted' in *.
  induction l as [| h t IH].
  - simpl. intros i j iv jv Hlt Hnth1 Hnth2.
    destruct i; simpl in Hnth1; inversion Hnth1.
    destruct j; simpl in Hnth2; inversion Hnth2.
    simpl in Hlt. lia. rewrite nth_error_nil in H1. inversion H1. reflexivity. 
    rewrite nth_error_nil in H0. inversion H0. reflexivity. 

  - simpl. bdestruct (a <=? h).
    + intros i j iv jv Hlt Hnth1 Hnth2.
      destruct i, j; simpl in *; try lia.
      * inversion Hnth1; inversion Hnth2; subst; try lia.
      * inversion Hnth1; subst; simpl in Hnth2.
        apply nth_error_Some_length in Hnth2.
        specialize (Hsorted 0 (j - 1) h jv).
        assert (Hj : S j - 1 = j). { lia. }
        rewrite Hj in Hsorted.
        apply Hsorted; try lia; simpl; auto.
      * inversion Hnth2.
      * simpl in Hnth1, Hnth2.
        specialize (IH i j iv jv Hlt Hnth1 Hnth2).
        apply IH.

    + intros i j iv jv Hlt Hnth1 Hnth2.
      destruct i, j; simpl in *; try lia.
      * inversion Hnth1; inversion Hnth2; subst; lia.
      * inversion Hnth1; subst; simpl in Hnth2.
        destruct j; inversion Hnth2; subst.
        apply Hsorted with (i := 0) (j := 0); simpl; auto; lia.
        apply Hsorted with (i := 0) (j := j); auto; lia.
      * inversion Hnth2.
      * simpl in Hnth1, Hnth2.
        specialize (IH i j iv jv Hlt Hnth1 Hnth2).
        apply IH.
Qed. *)


(* Lemma insert_sorted':
  forall a l, sorted' l -> sorted' (insert a l).
Proof.
    intros.
    induction l.
    - simpl.
        unfold sorted'.
        intros.
        destruct i; destruct j.
        + simpl in *. inversion H1. inversion H2. rewrite <- H4. rewrite <- H5. reflexivity.
        + simpl in *. destruct j; discriminate H2.
        + simpl in *. destruct i; discriminate H1.
        + simpl in *. destruct j; discriminate H2.
    - simpl. bdestruct (a <=? a0).
        + unfold sorted'.
            intros.
            destruct i; destruct j; try lia.
            * simpl in H1.
Qed. *)

(* ---------------- *)


Lemma lt_all_sorted: forall x y l,
    x <= y -> sorted' (y :: l) -> 
    forall i iv, nth_error (y :: l) i = Some iv -> x <= iv.
Proof.
    intros.
    unfold sorted' in H0.
    induction i.
    - simpl. injection H1 as H1. subst. assumption.
    - assert (y <= iv). {apply (H0 0 (S i) y iv).
        + lia.
        + reflexivity.
        + apply H1. }
        lia.
Qed.



Lemma remove_head_from_sorted'_is_sorted':
    forall x l, sorted' (x :: l) -> sorted' l.
Proof.
    unfold sorted'.
    intros.
    apply H with (i := S i) (j := S j).
    - lia.
    - simpl. apply H1. 
    - simpl. apply H2.  
Qed.



Lemma remove_second_from_sorted'_is_sorted': forall v v' l, sorted' (v :: v' :: l) -> sorted' (v :: l).
Proof.
    unfold sorted'. 
    intros.
    destruct i; destruct j.
    - lia.
    - simpl in *. injection H1 as H1; subst. apply (H 0 (S (S j)) iv jv).
        + lia.
        + reflexivity.
        + simpl. apply H2.
    - lia.
    - simpl in *.
        apply (H (S (S i)) (S (S j)) iv jv).
        + lia.
        + simpl. apply H1.
        + simpl. apply H2.
Qed.



Lemma lt_insert: forall l v a,
    sorted' (v :: l) -> a > v -> 
    forall i v', nth_error (insert a l) i = Some v' -> (v <= v').
Proof.
    intro l.
    induction l; simpl; intros.
    - destruct i; simpl in H1.
        + injection H1 as H1; subst. lia.
        + destruct i; discriminate H1.
    - bdestruct (a0 <=? a).
        + destruct i; simpl in H1.
            * injection H1 as H1; subst. lia.
            * apply (lt_all_sorted v a l) with i.
                -- lia.
                -- apply remove_head_from_sorted'_is_sorted' in H. apply H.
                -- apply H1.
        + destruct i; simpl in H1.
            * injection H1 as H1; subst.
                apply (H 0 1 v v').
                -- lia.
                -- reflexivity.
                -- reflexivity.
            * apply (IHl v a0) with i.
                -- apply (remove_second_from_sorted'_is_sorted' _ _ _ H).
                -- assumption.
                -- apply H1.
Qed.


Lemma insert_sorted':
    forall a l, sorted' l -> sorted' (insert a l).
Proof.
    intros.
    induction l.
    - simpl. unfold sorted'. intros. 
    destruct i; destruct j; try lia; simpl in *; destruct j; discriminate H2.
    - simpl. bdestruct (a <=? a0).
        + unfold sorted'.
            intros.
            destruct i; destruct j; try lia.
            * simpl in *. injection H2 as H2. subst.
                apply (lt_all_sorted iv a0 l H0 H j). apply H3.
            * simpl in *. apply (H i j iv jv).
                -- lia.
                -- apply H2.
                -- apply H3.
        + unfold sorted'. intros.
            destruct i; destruct j; try lia.
            * simpl in *. injection H2 as H2; subst.
                apply (lt_insert _ _ _ H H0 j jv H3).
            * simpl in *. apply remove_head_from_sorted'_is_sorted' in H.
                apply IHl in H. apply (H i j iv jv).
                -- lia.
                -- apply H2.
                -- apply H3.
Qed.


Theorem sort_sorted': forall l, sorted' (sort l).
Proof.
  induction l.
  - unfold sorted'. intros. destruct i; inv H0.
  - simpl. apply insert_sorted'. auto.
Qed.

(** If you complete the proofs above, you will note that the proof of
    [insert_sorted] is relatively easy compared to the proof of
    [insert_sorted'], even though [sorted al <-> sorted' al].  So,
    suppose someone asked you to prove [sort_sorted'].  Instead of
    proving it directly, it would be much easier to design predicate
    [sorted], then prove [sort_sorted] and [sorted_sorted'].

    The moral of the story is therefore: _Different formulations of
    the functional specification can lead to great differences in the
    difficulty of the correctness proofs_. *)


(* 2023-08-23 11:34 *)
