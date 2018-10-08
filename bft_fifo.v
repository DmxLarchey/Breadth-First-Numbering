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

Require Import List Arith Omega Extraction.

Require Import list_utils wf_utils. 
Require Import bt bft fifo.

Set Implicit Arguments.

Module BFT_FIFO (M: FIFO).

  Export M.

  Section bft_fifo.
  Variable (X : Type).

  Implicit Type p : fifo (bt X). 

  Definition bft_fifo_f p : { l | l = bft_f (fifo_list p) }.
  Proof.
    induction on p as bft_fifo_f with measure (fifo_lsum p).

    refine (let (b,Hb) := fifo_void p in _).
    revert Hb; refine (match b with 
      | true  => fun Hp 
      => exist _ nil _
      | false => fun Hp 
      => let (c,Hc) := @fifo_deq _ p _ 
         in _
    end). 
    all: cycle 2. (* We queue 2 POs *)
    revert Hc; refine (match c with (t,q) => _ end); clear c.
    refine (match t with
      | leaf x => fun Hq 
      => let (r,Hr) := bft_fifo_f q _ 
         in  exist _ (x::r) _
      | node a x b => fun Hq 
      => let (r,Hr) := fifo_enq q a    in
         let (s,Hs) := fifo_enq r b    in
         let (t,Ht) := bft_fifo_f s _
         in  exist _ (x::t) _
    end); simpl in Hq.
    all: cycle 4. (* We queue 4 POs *)

    (* And now, we show POs *)
   
    * rewrite (proj1 Hp); auto.
      rewrite bft_f_fix_0; reflexivity.
    * intros H; apply Hp in H; discriminate.
    * rewrite Hq; simpl; auto.
    * rewrite Hr, Hq.
      rewrite bft_f_fix_3; simpl.
      do 2 f_equal; apply app_nil_end.
    * rewrite Hs, Hr, Hq; simpl.
      do 2 rewrite lsum_app; simpl; omega.
    * rewrite Ht, Hs, Hr, Hq.
      rewrite app_ass; simpl.
      rewrite bft_f_fix_3, bft_f_fix_1; simpl.
      rewrite bft_f_fix_1; auto.
  Defined.

  Let bft_fifo_full t : { l : list X | l = bft t }.
  Proof.
    refine (
      let (q0,H0) := @fifo_nil _   in
      let (q1,H1) := fifo_enq q0 t in
      let (l,Hl)  := bft_fifo_f q1   
      in  exist _ l _).
    rewrite Hl, H1, H0; reflexivity.
  Qed. 

  Definition bft_fifo t := proj1_sig (bft_fifo_full t).

  Fact bft_fifo_spec t : bft_fifo t = bft t.
  Proof. apply (proj2_sig (bft_fifo_full t)). Qed.

End bft_fifo.

Check bft_fifo.
Check bft_fifo_spec.

End BFT_FIFO.
