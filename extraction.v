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
Require Export bt fifo bft bft_fifo bfn_fifo bfr_fifo.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Module BFT_triv := BFT_FIFO FIFO_triv.
Module BFN_triv := BFN_FIFO FIFO_triv.
Module BFR_triv := BFR_FIFO FIFO_triv.

Module BFT_2lists := BFT_FIFO FIFO_2lists.
Module BFN_2lists := BFN_FIFO FIFO_2lists.
Module BFR_2lists := BFR_FIFO FIFO_2lists.

Module BFT_3llists := BFT_FIFO FIFO_3llists.
Module BFN_3llists := BFN_FIFO FIFO_3llists.
Module BFR_3llists := BFR_FIFO FIFO_3llists.

(** the following does not yield executable extracted programs *)
Module BFT_axm := BFT_FIFO FIFO_axm.
Module BFN_axm := BFN_FIFO FIFO_axm.
Module BFR_axm := BFR_FIFO FIFO_axm.


Recursive Extraction BFT_triv.bft_fifo
                     BFN_triv.bfn_fifo
                     BFR_triv.bfr_fifo.

Recursive Extraction BFT_2lists.bft_fifo
                     BFN_2lists.bfn_fifo
                     BFR_2lists.bfr_fifo.

Recursive Extraction BFT_3llists.bft_fifo
                     BFN_3llists.bfn_fifo
                     BFR_3llists.bfr_fifo.

Recursive Extraction BFT_axm.bft_fifo
                     BFN_axm.bfn_fifo
                     BFR_axm.bfr_fifo.

