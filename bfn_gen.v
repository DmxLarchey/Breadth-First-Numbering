(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** Extraction of breadth-first numbering algorithm from Coq to Ocaml 

       see http://okasaki.blogspot.com/2008/07/breadth-first-numbering-algorithm-in.html
       and https://www.westpoint.edu/eecs/SiteAssets/SitePages/Faculty%20Publication%20Documents/Okasaki/jfp95queue.pdf
       and https://www.cs.cmu.edu/~rwh/theses/okasaki.pdf
       and https://www.westpoint.edu/eecs/SiteAssets/SitePages/Faculty%20Publication%20Documents/Okasaki/icfp00bfn.pdf

*)

Require Import List Arith Omega Extraction.
Require Import list_utils wf_utils bt bft fifo_axm.

Set Implicit Arguments.

Local Definition fifo_sum { X } (q : fifo (bt X)) := lsum (fifo_list q). 

Section bfn.

  Variable (X : Type).

  Notation fX := (fifo (bt X)). 
  Notation fN := (fifo (bt nat)).

  (* the forest (list of bt nat) is a breadth first numbering from n if
     its breadth first traversal yields [n;n+1;....;m[ for some m
   *)

  Definition is_bfn_from n l := is_seq_from n (bft_f l).

  (* Breath First Numbering: maps a forest X to a forest nat such that
          1) the two forests are of the same shape
          2) the result is a breadth first numbering from n

     Beware that the output is a reversed queue compared to the input
   *)

  Definition bfn_gen_f n (p : fX) : { q : fN | fifo_list p ~lt rev (fifo_list q) /\ is_bfn_from n (rev (fifo_list q)) }.
  Proof.
    induction on n p as bfn_gen_f with measure (fifo_sum p).

    refine (let (b,Hb) := fifo_void p in _).
    revert Hb; refine (match b with 
      | true  => fun Hp 
      => let (q,Hq) := @fifo_nil _ 
         in exist _ q _
      | false => fun Hp 
      => let (d1,Hd1) := @fifo_deq _ p _ 
         in _
    end). 
    all: cycle 2. (* We queue 2 POs *)
    revert Hd1; refine (match d1 with
      | (leaf x    , p1) => fun Hp1 
      => let (q,Hq)   := bfn_gen_f (S n) p1 _           in
         let (q1,Hq1) := fifo_enq q (leaf n) 
         in  exist _ q1 _
      | (node a x b, p1) => fun Hp1 
      => let (p2,Hp2) := fifo_enq p1 a                  in
         let (p3,Hp3) := fifo_enq p2 b                  in
         let (q,Hq)   := bfn_gen_f (S n) p3 _           in 
         let (d2,Hd2) := @fifo_deq _ q _ 
         in  _
    end); simpl in Hp1.
    all: cycle 4. (* We queue 4 POs *)
    revert Hd2; refine (match d2 with (u,q1) => _ end); intros Hq1.
    refine (let (d3,Hd3) := @fifo_deq _ q1 _ in _).
    all: cycle 1. (* We queue 1 PO *) 
    revert Hd3; refine (match d3 with 
      | (v,q2) => fun Hq2 
      => let (q3,Hq3) := fifo_enq q2 (node v n u)
         in  exist _ q3 _
    end); simpl in Hq2, Hq3.
    all: cycle 1. (* We queue 1 PO *) 

    (* And now, we show POs *)
   
    * apply proj1 in Hp; rewrite Hp, Hq; split; simpl; auto.
      red; rewrite bft_f_fix_0; simpl; auto.
    * intros H; apply Hp in H; discriminate.
    * unfold fifo_sum; rewrite Hp1; simpl; omega.
    * destruct Hq as (H5 & H6).
      rewrite Hp1, Hq1; split; auto.
      + rewrite rev_app_distr; simpl; auto.
      + rewrite rev_app_distr; simpl; red.
        rewrite bft_f_fix_3; simpl; rewrite <- app_nil_end; auto.
    * unfold fifo_sum. 
      rewrite Hp3, Hp2, app_ass; simpl.
      rewrite lsum_app, Hp1; simpl; omega.
    * apply proj1, Forall2_rev in Hq; intros H; revert Hq.
      rewrite H, Hp3, Hp2, app_ass; simpl.
      rewrite rev_app_distr; simpl.
      intros G; apply Forall2_length in G; discriminate.
    * apply proj1, Forall2_rev in Hq; intros H; revert Hq.
      rewrite Hq1, H, Hp3, Hp2, app_ass; simpl.
      rewrite rev_app_distr; simpl.
      intros G; apply Forall2_length in G; discriminate.
    * destruct Hq as (H5,H6).
      rewrite Hp3, Hp2, Hq1, Hq2 in H5. 
      repeat (rewrite app_ass in H5; simpl in H5).
      apply Forall2_2snoc_inv in H5.
      destruct H5 as (G1 & G2 & H5).
      rewrite Hq1, Hq2 in H6; simpl in H6; rewrite app_ass in H6; simpl in H6.
      unfold is_bfn_from in H6 |- *.
      rewrite Hp1, Hq3, rev_app_distr; simpl.
      rewrite bft_f_fix_3; simpl; split; auto.
  Defined.

  Section bfn.

    Let bfn_full (t : bt X) : { t' | t ~t t' /\ is_seq_from 0 (bft_std t') }.
    Proof.
      refine (let (p,Hp) := @fifo_nil _   in
              let (q,Hq) := fifo_enq p t  in 
              let (r,Hr) := bfn_gen_f 0 q in
              let (d1,Hd1) := @fifo_deq _ r _ 
              in _).
      all: cycle 1. (* We queue 1 PO *) 
      revert Hd1; refine (match d1 with (x,q1) => fun Hq1 => exist _ x _ end); simpl in Hq1.
      all: cycle 1. (* We queue 1 PO *) 

      + intros H; rewrite Hq, Hp, H in Hr.
        apply proj1 in Hr; inversion Hr.

      + rewrite Hq, Hp in Hr. 
        destruct Hr as (H1 & H2).
        rewrite <- bft_std_eq_bft.
        rewrite Hq1 in H1; simpl in H1.
        apply Forall2_snoc_inv with (l := nil) in H1.
        destruct H1 as (G1 & H1).
        apply Forall2_nil_inv_right in H1.
        apply f_equal with (f := @rev _) in H1.
        rewrite rev_involutive in H1; simpl in H1.
        rewrite Hq1, H1 in H2; simpl in H2.
        auto.
    Qed.

    Definition bfn_gen t := proj1_sig (bfn_full t).

    Fact bfn_gen_spec_1 t : t ~t bfn_gen t.
    Proof. apply (proj2_sig (bfn_full t)). Qed.

    Fact bfn_gen_spec_2 t : exists n, bft_std (bfn_gen t) = seq_an 0 n.
    Proof. apply is_seq_from_spec, (proj2_sig (bfn_full t)). Qed.

  End bfn.

End bfn.

Recursive Extraction bfn_gen.

Check bfn_gen.
Check bfn_gen_spec_1.
Check bfn_gen_spec_2.
