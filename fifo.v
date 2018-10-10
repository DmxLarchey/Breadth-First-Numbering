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

Require Import bt List.

Set Implicit Arguments.

Module Type FIFO.

  Parameters (fifo    : Type -> Type)
             (tolist  : forall X, fifo X -> list X)
             (empty   : forall X, { q : fifo X | tolist q = nil })
             (enq     : forall X q x, { q' : fifo X | tolist q' = tolist q ++ x :: nil })
             (deq     : forall X q, @tolist X q <> nil -> { c : X * fifo X | let (x,q') := c in tolist q = x::tolist q' })
             (void    : forall X q, { b : bool | b = true <-> @tolist X q = nil }).

  Notation fifo_lsum := ((fun X (q : fifo (bt X)) => lsum (tolist q)) _).

End FIFO.
