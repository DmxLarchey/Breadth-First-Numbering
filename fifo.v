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

Require Import bt.

Require Export fifo_axm.
(* Require Export fifo_triv. *)
(* Require Export fifo_2lists. *)
(* Require Export fifo_3llists. *)

Notation fifo_lsum := ((fun X (q : fifo (bt X)) => lsum (fifo_list q)) _).