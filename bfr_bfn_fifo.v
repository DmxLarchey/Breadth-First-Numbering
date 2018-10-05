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

(** BFN (Breadth-First Numbering) is a particular instance of 
    BFR (Breadth-First Reconstruction)   *)

Require Import List Arith Omega Extraction.
Require Import list_utils wf_utils.
Require Import bt fifo bft bfn_fifo bfr_fifo.

Set Implicit Arguments.

Theorem bfr_bfn_fifo X (t : bt X) : bfn_fifo t = bfr_fifo t (seq_an 0 (m_bt t)) (eq_sym (seq_an_length _ _)).
Proof.
  apply bft_std_inj.
  * apply bt_eq_trans with (s := t).
    + apply bt_eq_sym, bfn_fifo_spec_1.
    + apply bfr_fifo_spec_1.
  * rewrite bfr_fifo_spec_2, bfn_fifo_spec_3; trivial.
Qed.
