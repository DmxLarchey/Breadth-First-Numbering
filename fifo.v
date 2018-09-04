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
  Q :> Type;
  fifo_list : Q -> list X; 
  fifo_nil : Q; 
  fifo_enq : Q -> X -> Q;
  fifo_deq : forall q, fifo_list q <> nil -> X * Q;
  fifo_void : Q -> bool;
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

  Let rev_aux : list X -> list X -> list X :=
    fix loop l m { struct m } :=
      match m with
        | nil  => l
        | x::m => loop (x::l) m
      end.

  Let rev_aux_spec l m : rev_aux l m = rev m ++ l.
  Proof.
    revert l; induction m as [ | x m IHm ]; simpl; intros l; auto.
    rewrite IHm, app_ass; auto.
  Qed.

  Definition rev_linear l: list X := rev_aux nil l.

  Fact rev_linear_spec l : rev_linear l = rev l.
  Proof.
    unfold rev_linear; rewrite rev_aux_spec, <- app_nil_end; auto.
  Qed.

End rev_linear.

Section fifo_two_lists.

  Variable X : Type.

  Definition fifo_2l := (list X * list X)%type.
  Notation Q := fifo_2l.

  Implicit Type q : Q.

  Definition fifo_2l_list q := let (l,r) := q in l++rev r.
  Definition fifo_2l_nil : Q := (nil,nil).
  Definition fifo_2l_enq q x := let (l,r) := q in (l,x::r).

  Let fifo_2l_deq_rec q (Hq : fifo_2l_list q <> nil) : { c : X * Q | let (x,q') := c in fifo_2l_list q = x::fifo_2l_list q' }.
  Proof.
    revert Hq; induction on q as fifo_deq with measure (length (fst q)+2*length (snd q)); intros Hq.
    refine (match q as q' return q = q' -> _ with 
      | (nil,r)   => fun E  => let (res,Hres) := fifo_deq (rev_linear r,nil) _ _ in exist _ res _
      | (x::l,r)  => fun _  => exist _ (x,(l,r)) _
    end eq_refl).
    + subst; simpl.
      rewrite rev_linear_spec, rev_length.
      simpl in Hq; destruct r; simpl; try omega; destruct Hq; trivial.
    + subst; simpl in Hq |- *.
      rewrite rev_linear_spec, <- app_nil_end; auto.
    + subst; destruct res as (x,q').
      rewrite <- Hres; simpl.
      rewrite rev_linear_spec, <- app_nil_end; trivial.
    + subst; trivial.
  Qed.

  Definition fifo_2l_deq q Hq := proj1_sig (fifo_2l_deq_rec q Hq).
  
  Definition fifo_2l_void q: bool :=
    match q with (nil,nil) => true | _ => false end.

  Definition fifo_2l_nil_spec : fifo_nil_prop fifo_2l_list fifo_2l_nil.
  Proof. red; auto. Qed.

  Definition fifo_2l_enq_spec : fifo_enq_prop fifo_2l_list fifo_2l_enq.
  Proof. intros (l,r) x; simpl; rewrite app_ass; auto. Qed.

  Definition fifo_2l_deq_spec : fifo_deq_prop fifo_2l_list fifo_2l_deq.
  Proof. intros q Hq; apply (proj2_sig (fifo_2l_deq_rec q Hq)). Qed.

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

Recursive Extraction fifo_two_lists.

Section fifo_two_lazy_lists.

  (** From "Simple and Efficient Purely Functional Queues and Deques" by Chris Okasaki *)

  Variable X : Type.

 
  


End fifo_two_lazy_lists.

