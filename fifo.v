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

Require Import List.

Set Implicit Arguments.

Record fifo (X : Type) := {
  Q :> Type;
  fifo_list : Q -> list X; 
  fifo_nil : Q; 
  fifo_enq : Q -> X -> Q;
  fifo_deq : forall q, fifo_list q <> nil -> X * Q;
  fifo_void : Q -> bool;
  fifo_nil_spec : fifo_list fifo_nil = nil;
  fifo_enq_spec : forall q x, fifo_list (fifo_enq q x) = fifo_list q ++ x :: nil;
  fifo_deq_spec : forall q Hq, let (x,q') := @fifo_deq q Hq in fifo_list q = x::fifo_list q';
  fifo_void_spec : forall q, fifo_void q = true <-> fifo_list q = nil
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
    exists Q fifo_list fifo_nil fifo_enq fifo_deq fifo_void; auto.
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

  Implicit Type q : (list X * list X).

  Let Q := (list X * list X)%type.
  Let fifo_list q := let (l,r) := q in r++rev l.
  Let fifo_nil : Q := (nil,nil).
  Let fifo_enq q x := let (l,r) := q in (x::l,r).
  Let fifo_deq q (Hq : fifo_list q <> nil) : X * Q.
  Proof.
    revert Hq.
    refine (match q with 
      | (l,x::r)  => fun _ => (x,(l,r))
      | (l,nil)   => match rev_linear l as rl return rev_linear l = rl -> _ with
        | nil   => fun H E => _
        | x::rl => fun _ _ => (x,(nil,rl))
      end eq_refl
    end).
    rewrite rev_linear_spec in H.
    destruct E; auto.
  Defined.
  
  Let fifo_void q: bool :=
    match q with (nil,nil) => true | _ => false end.

  Definition fifo_two_lists : fifo X.
  Proof.
    exists Q fifo_list fifo_nil fifo_enq fifo_deq fifo_void; auto.
    + intros (l,r) x; simpl; rewrite app_ass; auto.
    + intros (l,[ | x r]); simpl; auto.
      rewrite rev_linear_spec.
      generalize (rev l); clear l; intros [ | x rl ].
      * intros []; reflexivity.
      * intros _; apply app_nil_end.
    + intros (l,r); simpl.
      destruct l as [ | x l ].
      * destruct r; simpl; split; auto; discriminate.
      * simpl. destruct r; destruct (rev l); split; discriminate.
  Defined.

End fifo_two_lists.

Section fifo_two_lazy_lists.

End fifo_two_lazy_lists.
