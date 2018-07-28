(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** Binary trees *)

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
  
  Let fifo_void q :=  match q with nil => true | _ => false end.

  Definition fifo_trivial : fifo X.
  Proof.
    exists Q fifo_list fifo_nil fifo_enq fifo_deq fifo_void; auto.
    intros [ | ] Hq; simpl; auto; destruct Hq; reflexivity.
    intros [ | ]; simpl; split; auto; discriminate.
  Defined.

End fifo_trivial.