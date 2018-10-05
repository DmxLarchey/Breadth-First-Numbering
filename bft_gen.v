(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega Extraction.
Require Import list_utils wf_utils bt bft fifo_axm.

Set Implicit Arguments.

Local Definition fifo_sum { X } (q : fifo (bt X)) := lsum (fifo_list q). 

Section bft_gen.

  Variable (X : Type).

  Notation fifo_X := (fifo (bt X)).

  Implicit Type (p : fifo_X). 

  Definition bft_gen_f p : { l | l = bft_f (fifo_list p) }.
  Proof.
    induction on p as bft_gen_f with measure (fifo_sum p).

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
      => let (r,Hr) := bft_gen_f q _ 
         in  exist _ (x::r) _
      | node a x b => fun Hq 
      => let (r,Hr) := fifo_enq q a    in
         let (s,Hs) := fifo_enq r b    in
         let (t,Ht) := bft_gen_f s _
         in  exist _ (x::t) _
    end); simpl in Hq.
    all: cycle 4. (* We queue 4 POs *)

    (* And now, we show POs *)
   
    * rewrite (proj1 Hp); auto.
      rewrite bft_f_fix_0; reflexivity.
    * intros H; apply Hp in H; discriminate.
    * unfold fifo_sum; rewrite Hq; simpl; auto.
    * rewrite Hr, Hq.
      rewrite bft_f_fix_3; simpl.
      do 2 f_equal; apply app_nil_end.
    * unfold fifo_sum. 
      rewrite Hs, Hr, Hq; simpl.
      do 2 rewrite lsum_app; simpl; omega.
    * rewrite Ht, Hs, Hr, Hq.
      rewrite app_ass; simpl.
      rewrite bft_f_fix_3, bft_f_fix_1; simpl.
      rewrite bft_f_fix_1; auto.
  Defined.

  Let bft_gen_full t : { l : list X | l = bft t }.
  Proof.
    refine (
      let (q0,H0) := @fifo_nil _   in
      let (q1,H1) := fifo_enq q0 t in
      let (l,Hl)  := bft_gen_f q1   
      in  exist _ l _).
    rewrite Hl, H1, H0; reflexivity.
  Qed. 

  Definition bft_gen t := proj1_sig (bft_gen_full t).

  Fact bft_gen_spec t : bft_gen t = bft t.
  Proof. apply (proj2_sig (bft_gen_full t)). Qed.

End bft_gen.

Recursive Extraction bft_gen.

Check bft_gen.
Check bft_gen_spec.
