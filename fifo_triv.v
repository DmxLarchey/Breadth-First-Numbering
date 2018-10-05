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

Require Import List Extraction.

Set Implicit Arguments.

(* We provide a trivial implementation of FIFO as lists 
   satisfying the axioms in fifo_axm.v *)

Section fifo_triv.

  Variable X : Type.

  Definition fifo := list X.

  Implicit Type q : fifo.

  Definition fifo_list : fifo -> list X:= fun x => x.
  
  Definition fifo_nil : { q | fifo_list q = nil }.
  Proof. exists nil; trivial. Defined.

  Definition fifo_enq q x : { q' | fifo_list q' = fifo_list q ++ x :: nil }.
  Proof. exists (q++x::nil); trivial. Defined.
 
  Definition fifo_deq q : fifo_list q <> nil -> { c : X * fifo | let (x,q') := c in fifo_list q = x::fifo_list q' }.
  Proof.
    refine (match q with nil => _ | x::q => fun _ => exist _ (x,q) _ end); trivial.
    intros []; reflexivity.
  Defined.

  Definition fifo_void q : { b : bool | b = true <-> fifo_list q = nil }.
  Proof.
    exists (match q with nil => true | _ => false end).
    destruct q; split; try tauto; discriminate.
  Defined.
  
End fifo_triv.

Arguments fifo_nil {X}.
Arguments fifo_deq {X}.




