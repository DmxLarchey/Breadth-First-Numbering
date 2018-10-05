(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega Extraction.
Require Import list_utils wf_utils bt bft.

Set Implicit Arguments.

Parameters (fifo      : Type -> Type) 
           (fifo_list : forall X, fifo X -> list X)
           (fifo_nil  : forall X, { q : fifo X | fifo_list q = nil })
           (fifo_enq  : forall X q x, { q' : fifo X | fifo_list q' = fifo_list q ++ x :: nil })
           (fifo_deq  : forall X q, @fifo_list X q <> nil -> { c : X * fifo X | let (x,q') := c in fifo_list q = x::fifo_list q' })
           (fifo_void : forall X q, { b : bool | b = true <-> @fifo_list X q = nil }).

Section bft_gen.

  Let fifo_sum { X } (q : fifo (bt X)): nat := lsum (fifo_list q).

  Variable (X : Type).

  Notation fX := (fifo (bt X)). 

  Definition bft_gen_f (p : fX) : { l : list X | l = bft_f (fifo_list p) }.
  Proof.
    induction on p as bft_gen_f with measure (fifo_sum p).

    refine (let (b,Hb) := fifo_void p in _).
    revert Hb; refine (match b with 
      | true  => fun Hp 
      => exist _ nil _
      | false => fun Hp 
      => let (d1,Hd1) := @fifo_deq _ p _ 
         in _
    end). 
    all: cycle 2. (* We queue 2 POs *)
    revert Hd1; refine (match d1 with
      | (leaf x    , p1) => fun Hp1 
      => let (q1,Hq1) := bft_gen_f p1 _ 
         in  exist _ (x::q1) _
      | (node a x b, p1) => fun Hp1 
      => let (p2,Hp2) := fifo_enq p1 a                  in
         let (p3,Hp3) := fifo_enq p2 b                  in
         let (q,Hq)   := bft_gen_f p3 _  
         in  exist _ (x::q) _
    end); simpl in Hp1.
    all: cycle 4. (* We queue 4 POs *)

    (* And now, we show POs *)
   
    * rewrite (proj1 Hp); auto.
      rewrite bft_f_fix_0; reflexivity.
    * intros H; apply Hp in H; discriminate.
    * unfold fifo_sum; rewrite Hp1; simpl; auto.
    * rewrite Hq1, Hp1.
      rewrite bft_f_fix_3; simpl.
      do 2 f_equal; apply app_nil_end.
    * unfold fifo_sum. 
      rewrite Hp3, Hp2, Hp1; simpl.
      do 2 rewrite lsum_app; simpl; omega.
    * rewrite Hq, Hp3, Hp2, Hp1.
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
