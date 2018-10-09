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
Require Import fifo_mod fifo_triv fifo_2lists fifo_3llists.
Require Import bt bft bft_fifo.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Module bft_fifo_trivial := bft_fifo (fifo_trivial).
Module bft_fifo_2lists := bft_fifo (fifo_two_lists).
Module bft_fifo_3llists := bft_fifo (fifo_three_llists).

Definition mybft := bft_fifo fifo_triv.

Check mybft.

Recursive Extraction mybft.

(*

Recursive Extraction bft_fifo_trivial bft_fifo_2lists bft_fifo_3llists.

Check bft_fifo_trivial.bft_fifo_spec.
Check bft_fifo_2lists.bft_fifo_spec.
Check bft_fifo_3llists.bft_fifo_spec.

*)