(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             Ralph Matthes [+]                              *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                             [+] Affiliation IRIT -- CNRS   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega.

Require Import wf_utils lazy_list fifo.

Set Implicit Arguments.

(* We provide an implementation of FIFO as a triple of lazy lists 
   satisfying the axioms in fifo_axm.v *)

Module FIFO_3llists <: FIFO.

Section fifo_three_lazy_lists.

  (** From "Simple and Efficient Purely Functional Queues and Deques" by Chris Okasaki 
          Journal of Functional Programming 5(4):583-592

      this implements and prove the spec from page 587 with lazy lists (llist)
      with invariant (l,r,l') : llength l' + llength r = llength l


      let rec llist_rotate l r a := match r with
        | lcons y r -> match l with
          | lnil      -> lcons y a
          | lcons x l -> lcons x (llist_rotate l' r' (lcons y a))

      let fifo_3q_nil = (lnil,lnil,lnil)

      let fifo_3q_make l r l' = match l' with
        | lnil       -> let l' = llist_rotate l r lnil in (l',lnil,l')
        | lcons _ l' -> (l, r, l')

      let fifo_3q_enq (l,r,l') x = fifo_3q_make l (lcons x r) l'

      let fifo_3q_deq (lcons x l,r,l') = (x,fifo_3q_make l r l')

      let fifo_3q_void (l,r,n) = l = lnil

    *)

  Variable X : Type.

  Implicit Types (l r : llist X).

  Let Q_spec (c : llist X * llist X * llist X) :=
    match c with (l,r,l') => llength l' + llength r = llength l end.

  Definition fifo := sig Q_spec.

  Implicit Types (q : fifo) (x : X).

  Definition f2l : fifo -> list X.
  Proof.
    intros (((l,r),l') & H).
    exact (llist_list l ++ rev (llist_list r)).
  Defined.

  Definition empty : { q | f2l q = nil }.
  Proof.
    assert (H : Q_spec (lnil,lnil,lnil)).
    { red; rewrite llength_nil; auto. }
    exists (exist _ _ H).
    unfold f2l; simpl.
    rewrite llist_list_nil; auto.
  Defined.

  Definition make l r l' : llength l' + llength r = 1 + llength l -> { m | llist_list l ++ rev (llist_list r) = f2l m }.
  Proof.
    induction l' as [ | x l'' _ ] using llist_rect; intros E.
    + rewrite llength_nil in E; simpl in E.
      set (l'' := @llist_rotate _ l r lnil E).
      assert (H : Q_spec (l'',lnil,l'')).
      { red; unfold l''.
        rewrite llist_rotate_length, llength_nil; omega. }
      exists (exist _ _ H).
      unfold Q_spec; simpl.
      rewrite llist_list_nil.
      unfold l''.
      rewrite llist_rotate_eq, llist_list_nil.
      repeat rewrite <- app_nil_end; trivial.
    + assert (H : Q_spec (l,r,l'')).
      { red; rewrite llength_cons in E; omega. }
      exists (exist _ _ H).
      unfold Q_spec; simpl; auto.
  Defined.

  Definition enq : forall q x, { q' | f2l q' = f2l q ++ x :: nil }.
  Proof.
    intros (((l,r),l') & H) x.
    refine (let (m,Hm) := @make l (lcons x r) l' _ in _).
    + red in H; rewrite llength_cons; omega.
    + exists m.
      simpl; rewrite <- Hm.
      rewrite llist_list_cons, app_ass; simpl; auto.
  Defined.

  Definition deq : forall q, f2l q <> nil -> { c : X * fifo | let (x,q') := c in f2l q = x::f2l q' }.
  Proof.
    intros (((l,r),l') & H); revert H; simpl.
    induction l as [ | x l _ ] using llist_rect.
    + induction r as [ | y r _ ] using llist_rect; intros H1 H2; exfalso.
      * destruct H2; rewrite llist_list_nil; auto.
      * rewrite llength_cons,llength_nil in H1; omega.
    + intros H1 H2.
      refine (let (m,Hm) := @make l r l' _ in _).
      * rewrite llength_cons in H1; omega.
      * exists (x,m).
        rewrite llist_list_cons; simpl; f_equal; auto.
  Defined.

  Definition void : forall q, { b : bool | b = true <-> f2l q = nil }.
  Proof.
    intros (((l,r),l') & H).
    induction l as [ | x l _ ] using llist_rect; red in H.
    + exists true; simpl.
      split; auto; intros _.
      induction r as [ | y r _ ] using llist_rect.
      * rewrite llist_list_nil; auto.
      * rewrite llength_cons, llength_nil in H; simpl in H; omega.
    + exists false; simpl.
      split; try discriminate.
      rewrite llist_list_cons; discriminate.
  Defined.

End fifo_three_lazy_lists.

End FIFO_3llists.



