(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             Ralph Matthes [+]                              *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                             [*] Affiliation IRIT -- CNRS   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega.

Require Import wf_utils llist.

Set Implicit Arguments.

Section fifo_props.

  Variables  (X Q : Type) (fifo_list : Q -> list X) 
                          (fifo_nil : Q)
                          (fifo_enq : Q -> X -> Q)
                          (fifo_deq : forall q, fifo_list q <> nil -> X * Q)
                          (fifo_void : Q -> bool).

  Definition fifo_nil_prop := fifo_list fifo_nil = nil.
  Definition fifo_enq_prop := forall q x, fifo_list (fifo_enq q x) = fifo_list q ++ x :: nil.
  Definition fifo_deq_prop := forall q Hq, let (x,q') := @fifo_deq q Hq in fifo_list q = x::fifo_list q'.
  Definition fifo_void_prop := forall q, fifo_void q = true <-> fifo_list q = nil.

  Definition fifo_props := fifo_nil_prop /\ fifo_enq_prop /\ fifo_deq_prop /\ fifo_void_prop.

End fifo_props.

Record fifo (X : Type) := {
  queue :> Type;
  fifo_list : queue -> list X; 
  fifo_nil : queue; 
  fifo_enq : queue -> X -> queue;
  fifo_deq : forall q, fifo_list q <> nil -> X * queue;
  fifo_void : queue -> bool;
  fifo_nil_spec : fifo_nil_prop fifo_list fifo_nil;
  fifo_enq_spec : fifo_enq_prop fifo_list fifo_enq;
  fifo_deq_spec : fifo_deq_prop fifo_list fifo_deq;
  fifo_void_spec : fifo_void_prop fifo_list fifo_void;
}.

Arguments fifo_list { X f }.
Arguments fifo_nil { X f }.
Arguments fifo_enq { X f }.
Arguments fifo_deq { X f }.
Arguments fifo_void { X f }.

Section fifo_trivial.

  Variable X : Type.

  Implicit Type q : list X.

  Let Q := list X.
  Let fifo_list q := q.
  Let fifo_nil := @nil X.
  Let fifo_enq q x := q++x::nil.
  Let fifo_deq q (Hq : fifo_list q <> nil) : X * Q.
  Proof.
    revert Hq.
    refine (match q with nil => _ | x::q => fun _ => (x,q) end).
    intros []; reflexivity.
  Defined.
  
  Let fifo_void q: bool:=  match q with nil => true | _ => false end.

  Definition fifo_trivial : fifo X.
  Proof.
    exists Q fifo_list fifo_nil fifo_enq fifo_deq fifo_void; red; auto.
    intros [ | ] Hq; simpl; auto; destruct Hq; reflexivity.
    intros [ | ]; simpl; split; auto; discriminate.
  Defined.

End fifo_trivial.

Section rev_linear.

  Variable (X : Type).
  Implicit Type (l m : list X).

  Fixpoint rev' l m :=
    match m with
      | nil  => l
      | x::m => rev' (x::l) m
    end.

  Let rev'_spec l m : rev' l m = rev m ++ l.
  Proof.
    revert l; induction m as [ | x m IHm ]; simpl; intros l; auto.
    rewrite IHm, app_ass; auto.
  Qed.

  Definition rev_linear l: list X := rev' nil l.

  Fact rev_linear_spec l : rev_linear l = rev l.
  Proof.
    unfold rev_linear; rewrite rev'_spec, <- app_nil_end; auto.
  Qed.

End rev_linear.

Section fifo_two_lists.

  Variable X : Type.

  Definition fifo_2l := (list X * list X)%type.
  Notation Q := fifo_2l.

  Implicit Type q : Q.

  Definition fifo_2l_list q := let (l,r) := q in l++rev r.

  Definition fifo_2l_nil : Q := (nil,nil).
  Definition fifo_2l_nil_spec : fifo_nil_prop fifo_2l_list fifo_2l_nil.
  Proof. red; auto. Qed.

  Definition fifo_2l_enq q x := let (l,r) := q in (l,x::r).
  Definition fifo_2l_enq_spec : fifo_enq_prop fifo_2l_list fifo_2l_enq.
  Proof. intros (l,r) x; simpl; rewrite app_ass; auto. Qed.

  Section deq.

    (* Beware that the extracted code loops forever if q = (nil,nil) 
       which is not problematic with the guard fifo_2l_list q <> nil
       but this is an interesting example of extraction of a partial
       function ... 

       let rec deq = function (l,r) -> 
         match l with 
           | nil  => deq (rev r,nil)
           | x::l => (x,(l,r)
         end

       *)

    Let fifo_2l_deq_rec q : fifo_2l_list q <> nil -> { c : X * Q | let (x,q') := c in fifo_2l_list q = x::fifo_2l_list q' }.
    Proof.
      induction on q as fifo_deq with measure (length (fst q)+2*length (snd q)); intros Hq.
      refine (match q as q' return q = q' -> _ with 
        | (nil,r)   => fun E  => let (res,Hres) := fifo_deq (rev_linear r,nil) _ _ in exist _ res _
        | (x::l,r)  => fun _  => exist _ (x,(l,r)) _
      end eq_refl); subst; simpl in * |- *; trivial.
      + rewrite rev_linear_spec, rev_length.
        destruct r; simpl; try omega; destruct Hq; trivial.
      + rewrite rev_linear_spec, <- app_nil_end; trivial.
      + destruct res; rewrite <- Hres, rev_linear_spec, <- app_nil_end; trivial.
    Qed.

    Definition fifo_2l_deq q Hq := proj1_sig (fifo_2l_deq_rec q Hq).
    Definition fifo_2l_deq_spec : fifo_deq_prop fifo_2l_list fifo_2l_deq.
    Proof. intros q Hq; apply (proj2_sig (fifo_2l_deq_rec q Hq)). Qed.

  End deq.
  
  Definition fifo_2l_void q: bool :=
    match q with (nil,nil) => true | _ => false end.
  Definition fifo_2l_void_spec : fifo_void_prop fifo_2l_list fifo_2l_void.
  Proof.
    intros ([ | x l],[ | y r]); simpl; split; auto; try discriminate.
    generalize (rev r); clear r; intros [ | ]; discriminate.
  Qed.

  Hint Resolve fifo_2l_nil_spec fifo_2l_enq_spec fifo_2l_deq_spec fifo_2l_void_spec.

  Theorem fifo_2l_spec : fifo_props fifo_2l_list fifo_2l_nil fifo_2l_enq fifo_2l_deq fifo_2l_void.
  Proof. red; auto. Qed.

  Definition fifo_two_lists : fifo X.
  Proof.
    exists Q fifo_2l_list fifo_2l_nil fifo_2l_enq fifo_2l_deq fifo_2l_void; apply fifo_2l_spec; auto.
  Defined.

End fifo_two_lists.

Arguments fifo_2l_nil {X}.

Section fifo_two_lazy_lists.

  (** From "Simple and Efficient Purely Functional Queues and Deques" by Chris Okasaki 

      this implements and prove the spec from page 587 with lazy lists (llist)
      with invariant (l,r,n) : n + llength r = llength l

      let fifo_2q_nil = (lnil,lnil,0)

      let fifo_2q_make l r = function
        | O   -> (llist_rotate l r lnil, lnil, llength l + llength r) 
        | S n -> (l, r, n)

      let fifo_2q_enq (l,r,n) x = fifo_2q_make l (lcons x r) n

      let fifo_2q_deq (lcons x l,r,n) = (x,fifo_2q_make l r n)

      let fifo_2q_void (l,r,n) = l = lnil

    *)

  Variable X : Type.

  Implicit Types (l r : llist X).

  Let Q_spec (c : llist X * llist X * nat) :=
    match c with (l,r,n) => exists Hl Hr, n + lfin_length r Hr = lfin_length l Hl end.

  Definition fifo_2q_list : sig Q_spec -> list X.
  Proof.
    intros (((l,r),n) & H).
    refine (llist_list l _ ++ rev (llist_list r _));
    destruct H as (? & ? & _); assumption.
  Defined.

  Definition fifo_2q_nil : sig Q_spec.
  Proof. 
    exists (lnil,lnil,0), (lfin_lnil _), (lfin_lnil _); simpl.
    rewrite lfin_length_fix_0; auto.
  Defined.

  Fact fifo_2q_nil_spec : fifo_nil_prop fifo_2q_list fifo_2q_nil.
  Proof. 
    unfold fifo_nil_prop, fifo_2q_list, fifo_2q_nil.
    repeat rewrite lfin_length_fix_0; trivial.
  Qed.

  Definition fifo_2q_make l r n : (exists Hl Hr, n + lfin_length r Hr = 1 + lfin_length l Hl) -> sig Q_spec.
  Proof.
    destruct n as [ | n ]; intros E.
    + assert (Hl' : lfin l) by (destruct E as (? & ? & _); assumption).
      assert (Hr' : lfin r) by (destruct E as (? & ? & _); assumption).
      assert (E' : lfin_length r Hr' = 1 + lfin_length l Hl').
      { destruct E as (Hl & Hr & E).
        rewrite (lfin_length_eq _ Hr), (lfin_length_eq _ Hl); auto. }
      refine (exist _ (llist_rotate (@lfin_lnil _) E', lnil,lfin_length l Hl'+lfin_length r Hr') _); simpl.
      exists (lfin_rotate _ _ (@lfin_lnil _) E'), (@lfin_lnil _).
      rewrite llist_rotate_length; auto.
    + exists (l,r,n); destruct E as (Hl & Hr & Hn); exists Hl, Hr; omega.
  Defined.

  Hint Resolve  llist_list_eq.

  Fact fifo_2q_make_spec l r n Hl Hr H : llist_list l Hl ++ rev (llist_list r Hr) = fifo_2q_list (@fifo_2q_make l r n H).
  Proof.
    destruct H as (Hl' & Hr' & Hn).
    unfold fifo_2q_list, fifo_2q_make; destruct n as [ | n ].
    + rewrite (llist_rotate_eq _ _ (@lfin_lnil _) _).
      repeat rewrite llist_list_fix_0; simpl.
      repeat rewrite <- app_nil_end; repeat (f_equal; auto).
    + repeat (f_equal; auto).
  Qed.

  Definition fifo_2q_enq (q : sig Q_spec) (x : X) : sig Q_spec.
  Proof.
    destruct q as (((l,r),n) & H).
    apply (@fifo_2q_make l (lcons x r) n).
    destruct H as (Hl & Hr & Hn).
    exists Hl, (lfin_lcons _ Hr).
    rewrite lfin_length_fix_1, (lfin_length_eq _ Hr); omega.
  Defined.

  Fact fifo_2q_enq_spec : fifo_enq_prop fifo_2q_list fifo_2q_enq.
  Proof.
    unfold fifo_enq_prop, fifo_2q_enq.
    intros  (((l,r),n) & Hl & Hr & Hn) x.
    rewrite <- (@fifo_2q_make_spec _ _ _ Hl (lfin_lcons x Hr)).
    unfold fifo_2q_list. 
    rewrite llist_list_fix_1, app_ass; trivial.
  Qed.

  Definition fifo_2q_deq q : fifo_2q_list q <> nil -> X * sig Q_spec.
  Proof.
    destruct q as (((l,r),n) & H); revert H.
    refine (match l with 
      | lnil      => fun H1 H2 => _
      | lcons x l => fun H1 H2 => (x,@fifo_2q_make l r n _)
    end).
    + exfalso.
      destruct H1 as (Hl & Hr & Hn).
      unfold fifo_2q_list in H2.
      destruct r.
      * do 2 rewrite llist_list_fix_0 in H2; destruct H2; trivial.
      * rewrite lfin_length_fix_1, lfin_length_fix_0 in Hn; omega.
    + destruct H1 as (Hl & Hr & Hn).
      exists (lfin_inv Hl), Hr.
      rewrite Hn, lfin_length_fix_1; auto.
  Defined.

  Fact fifo_2q_deq_spec : fifo_deq_prop fifo_2q_list fifo_2q_deq.
  Proof.
    unfold fifo_deq_prop, fifo_2q_deq.
    intros  ((([ | x l],r),n) & Hl & Hr & H) Hq.
    + exfalso.
      unfold fifo_2q_list in Hq.
      destruct r.
      * do 2 rewrite llist_list_fix_0 in Hq; destruct Hq; trivial.
      * rewrite lfin_length_fix_1, lfin_length_fix_0 in H; omega.
    + rewrite <- (@fifo_2q_make_spec _ _ _ (lfin_inv Hl) Hr).
      unfold fifo_2q_list.
      rewrite llist_list_fix_1; auto.
  Qed.

  Definition fifo_2q_void : sig Q_spec -> bool.
  Proof.
    intros ((([ | x l],r),n) & H).
    + exact true.
    + exact false.
  Defined.
  
  Fact fifo_2q_void_spec : fifo_void_prop fifo_2q_list fifo_2q_void.
  Proof.
    unfold fifo_void_prop, fifo_2q_list, fifo_2q_void.
    intros ((([ | x l],r),n) & Hl & Hr & Hn).
    + split; auto; intros _. 
      rewrite llist_list_fix_0.
      destruct r.
      * rewrite llist_list_fix_0; auto.
      * rewrite lfin_length_fix_0, lfin_length_fix_1 in Hn; omega.
    + split; try discriminate.
      rewrite llist_list_fix_1; discriminate.
  Qed.

End fifo_two_lazy_lists.

Recursive Extraction fifo_2q_nil fifo_2q_enq fifo_2q_deq fifo_2q_void.


