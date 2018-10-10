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


(*

(** implementation based on a list *)

Extraction Inline fifo_triv.fifo fifo_triv.fifo_list fifo_triv.fifo_nil
                  fifo_triv.fifo_enq fifo_triv.fifo_deq fifo_triv.fifo_void.

(** implementation based on two lists *)

Extraction Inline fifo_2lists.fifo fifo_2lists.fifo_list fifo_2lists.fifo_nil
                  fifo_2lists.fifo_enq fifo_2lists.fifo_deq fifo_2lists.fifo_void.


Extraction Inline fifo_3llists.fifo fifo_3llists.fifo_list fifo_3llists.fifo_nil
                  fifo_3llists.fifo_enq fifo_3llists.fifo_deq fifo_3llists.fifo_void.


(** now the redundant module that cannot serve for program extraction *)
Module FIFO_axm <: FIFO.

  Definition fifo := fifo_axm.fifo.
  Definition tolist := fifo_axm.fifo_list.
  Definition empty := @fifo_axm.fifo_nil.
  Definition enq := fifo_axm.fifo_enq.
  Definition deq := @fifo_axm.fifo_deq.
  Definition void := fifo_axm.fifo_void.

End FIFO_axm.

*)
