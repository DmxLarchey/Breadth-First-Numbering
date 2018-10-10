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
Require Import fifo_intf.

Set Implicit Arguments.

(* We provide a trivial implementation of FIFO as lists 
   satisfying the axioms in fifo_axm.v *)

Module FIFO_triv <: FIFO.

Section fifo_triv.

  Variable X : Type.

  Definition fifo := list X.

  Implicit Type q : fifo.

  Definition tolist : fifo -> list X := fun x => x.
  
  Definition empty : { q | tolist q = nil }.
  Proof. exists nil; trivial. Defined.

  Definition enq q x : { q' | tolist q' = tolist q ++ x :: nil }.
  Proof. exists (q++x::nil); trivial. Defined.
 
  Definition deq q : tolist q <> nil -> { c : X * fifo | let (x,q') := c in tolist q = x::tolist q' }.
  Proof.
    refine (match q with nil => _ | x::q => fun _ => exist _ (x,q) _ end); trivial.
    intros []; reflexivity.
  Defined.

  Definition void q : { b : bool | b = true <-> tolist q = nil }.
  Proof.
    exists (match q with nil => true | _ => false end).
    destruct q; split; try tauto; discriminate.
  Defined.
  
End fifo_triv.

End FIFO_triv.


