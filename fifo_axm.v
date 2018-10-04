(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List.

Set Implicit Arguments.

(* We provide an axiomatized form of FIFO implementation 

   This can be realized by fifo_2l or fifo_3q 
*)

Parameters (fifo      : Type -> Type) 
           (fifo_list : forall X, fifo X -> list X)
           (fifo_nil  : forall X, { q : fifo X | fifo_list q = nil })
           (fifo_enq  : forall X q x, { q' : fifo X | fifo_list q' = fifo_list q ++ x :: nil })
           (fifo_deq  : forall X q, @fifo_list X q <> nil -> { c : X * fifo X | let (x,q') := c in fifo_list q = x::fifo_list q' })
           (fifo_void : forall X q, { b : bool | b = true <-> @fifo_list X q = nil }).

Arguments fifo_nil {X}.
Arguments fifo_deq {X}.
