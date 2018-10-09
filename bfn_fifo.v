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

(** Extraction of breadth-first numbering algorithm from Coq to Ocaml 

       see http://okasaki.blogspot.com/2008/07/breadth-first-numbering-algorithm-in.html
       and https://www.westpoint.edu/eecs/SiteAssets/SitePages/Faculty%20Publication%20Documents/Okasaki/jfp95queue.pdf
       and https://www.cs.cmu.edu/~rwh/theses/okasaki.pdf
       and https://www.westpoint.edu/eecs/SiteAssets/SitePages/Faculty%20Publication%20Documents/Okasaki/icfp00bfn.pdf

*)

(** We exploit the following equations from bft_forest to 
    get an efficient implementation with queues ... this
    corresponds to bftrav' in Okazaki's paper

    See bft_forest.v for the proofs 

    Corollary bft_f_fix_oka_0 : bft_f nil = nil.
    Corollary bft_f_fix_oka_1 x l : bft_f (leaf x::l) = x::bft_f l.
    Corollary bft_f_fix_oka_2 a x b l : bft_f (node a x b::l) = x::bft_f (l++a::b::nil).

*)

Require Import List Arith Omega Extraction.

Require Import list_utils wf_utils bt fifo bft_forest bft_std.

Set Implicit Arguments.

Module BFN_FIFO (M: FIFO).

Export M.

Section bfn_fifo.

  Variable (X : Type).

  (* the forest (list of bt nat) is a breadth first numbering from n if
     its breadth first traversal yields [n;n+1;....;m[ for some m
   *)

  Definition is_bfn_from n l := is_seq_from n (bft_f l).

  (* Breath First Numbering: maps a forest X to a forest nat such that
          1) the two forests are of the same shape
          2) the result is a breadth first numbering from n

     Beware that the output is a reversed queue compared to the input
   *)

  (** We decompose the proof into Computational Content (CC) and 
      Proof Obligations (PO) using the handy refine tactic leaving 
      holes for PO which are thus postponed after CC.

      The intended extraction is:

      let rec bfn_f n p =
        if fifo_void p then fifo_nil
        else let c,p1 = fifo_deq p 
             in match c with
               | Leaf _
              -> fifo_enq (bfn_f (1+n) p1) (Leaf u)
               | Node (a, _, b)
              -> let u,q1 = fifo_deq (bfn_f (1+n) (fifo_enq (fifo_enq p1 a) b))     in
                 let v,q2 = fifo_deq q1 
                 in fifo_enq q2 (Node (v, n, u))

      Hence the CC should be something like 

      refine (
        let (b,Hb) := fifo_void p 
        in match b with 
          | true  
          => let (q,Hq) := @fifo_nil _
             in exist _ q _
          | false 
          => let (d1,Hd1) := fifo_deq p _ 
             in match d1 with
               | (leaf x    , p1) 
               => let (q,Hq) := bfn_f (S n) p1 _          in
                  let (q1,Hq1) := fifo_enq q (leaf n) 
                  in exist _ q1 _
               | (node a x b, p1) => fun Hp1 
               => let (p2,Hp2)     := fifo_enq p1 a    in
                  let (p3,Hp3)     := fifo_enq p2 b    in
                  let (q,Hq)       := bfn_f (S n) p3 _ in
                  let ((u,q1),Hq1) := fifo_deq q _     in
                  let ((v,q2),Hq2) := fifo_deq q1 _    in
                  let (q3,Hq3)     := fifo_enq q2 (node v n u)
                  in  exist _ q3 _
             end
        end)

      But this does not work well because for instance the b in Hb is
      not decomposed into either true or false with the subsequent 
      match b with ... end. We need to implement some kind of dependent
      pattern matching which involves a more subtle approach

      The structure of this proof is the following:

      We use a series of refine to specify the CC and PO is  
      postponed after the full CC is given using cycle tactics
      to reorder goals and to keep CC goals upfront.

      At some point, we need pattern matching to decompose 
      term in hypotheses as well as in the conclusion. The
      simplest way to do it is to revert the hypothesis in 
      the conclusion before the match and then intro it in 
      the different match branches where the matched term 
      has been decomposed. This corresponds to dependent
      pattern-matching but hand-writting dependent pattern-
      matching in refines is much more complicated/verbose 
      than just

      revert Hq; refine (match q with ... => ... end); intros Hq

      By postponing PO, we let the CC to develop itself in the 
      first branch

    *)

  Implicit Type p : fifo (bt X).

  Definition bfn_fifo_f n p : { q | tolist p ~lt rev (tolist q) /\ is_bfn_from n (rev (tolist q)) }.
  Proof.
    induction on n p as bfn_fifo_f with measure (fifo_lsum p).

    refine (let (b,Hb) := void p in _).
    revert Hb; refine (match b with 
      | true  => fun Hp 
      => let (q,Hq) := @empty _ 
         in exist _ q _
      | false => fun Hp 
      => let (d1,Hd1) := @deq _ p _ 
         in _
    end). 
    all: cycle 2. (* We queue 2 POs *)
    revert Hd1; refine (match d1 with
      | (leaf x    , p1) => fun Hp1 
      => let (q,Hq)   := bfn_fifo_f (S n) p1 _     in
         let (q1,Hq1) := enq q (leaf n) 
         in  exist _ q1 _
      | (node a x b, p1) => fun Hp1 
      => let (p2,Hp2) := enq p1 a                  in
         let (p3,Hp3) := enq p2 b                  in
         let (q,Hq)   := bfn_fifo_f (S n) p3 _     in 
         let (d2,Hd2) := @deq _ q _ 
         in  _
    end); simpl in Hp1.
    all: cycle 4. (* We queue 4 POs *)
    revert Hd2; refine (match d2 with (u,q1) => _ end); intros Hq1.
    refine (let (d3,Hd3) := @deq _ q1 _ in _).
    all: cycle 1. (* We queue 1 PO *) 
    revert Hd3; refine (match d3 with 
      | (v,q2) => fun Hq2 
      => let (q3,Hq3) := enq q2 (node v n u)
         in  exist _ q3 _
    end); simpl in Hq2, Hq3.
    all: cycle 1. (* We queue 1 PO *) 

    (* And now, we show POs *)
   
    * apply proj1 in Hp; rewrite Hp, Hq; split; simpl; auto.
      red; rewrite bft_f_fix_oka_0; simpl; auto.
    * intros H; apply Hp in H; discriminate.
    * rewrite Hp1; simpl; omega.
    * destruct Hq as (H5 & H6).
      rewrite Hp1, Hq1; split; auto.
      + rewrite rev_app_distr; simpl; auto.
      + rewrite rev_app_distr; simpl; red.
        rewrite bft_f_fix_oka_1; simpl; auto.
    * rewrite Hp3, Hp2, app_ass; simpl.
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
      rewrite bft_f_fix_oka_2; simpl; auto.
  Defined.

  Section bfn.

    Implicit Type (t : bt X).

    Let bfn_fifo_full t : { t' | t ~t t' /\ is_seq_from 0 (bft_forest t') }.
    Proof.
      refine (let (p,Hp) := @empty _       in
              let (q,Hq) := enq p t        in 
              let (r,Hr) := bfn_fifo_f 0 q in
              let (d1,Hd1) := @deq _ r _ 
              in _).
      all: cycle 1. (* We queue 1 PO *) 
      revert Hd1; refine (match d1 with (x,q1) => fun Hq1 => exist _ x _ end); simpl in Hq1.
      all: cycle 1. (* We queue 1 PO *) 

      * intros H; rewrite Hq, Hp, H in Hr.
        apply proj1 in Hr; inversion Hr.
      * rewrite Hq, Hp in Hr. 
        destruct Hr as (H1 & H2).
        rewrite Hq1 in H1; simpl in H1.
        apply Forall2_snoc_inv with (l := nil) in H1.
        destruct H1 as (G1 & H1).
        apply Forall2_nil_inv_right in H1.
        apply f_equal with (f := @rev _) in H1.
        rewrite rev_involutive in H1; simpl in H1.
        rewrite Hq1, H1 in H2; simpl in H2.
        auto.
    Qed.

    Definition bfn_fifo t := proj1_sig (bfn_fifo_full t).

    Fact bfn_fifo_spec_1 t : t ~t bfn_fifo t.
    Proof. apply (proj2_sig (bfn_fifo_full t)). Qed.

    Fact bfn_fifo_spec_2 t : exists n, bft_std (bfn_fifo t) = seq_an 0 n.
    Proof. 
      apply is_seq_from_spec.
      rewrite <- bft_forest_eq_bft_std. 
      apply (proj2_sig (bfn_fifo_full t)). 
    Qed.

    Corollary bfn_fifo_spec_3 t : bft_std (bfn_fifo t) = seq_an 0 (m_bt t).
    Proof.
      destruct (bfn_fifo_spec_2 t) as (n & Hn).
      rewrite Hn.
      apply f_equal with (f := @length _) in Hn.
      rewrite seq_an_length, bft_std_length in Hn.
      generalize (bfn_fifo_spec_1 t); intros E.
      apply bt_eq_m in E.
      rewrite <- Hn, <- E; trivial.
    Qed.

  End bfn.

End bfn_fifo.

Check bfn_fifo.
Check bfn_fifo_spec_1.
Check bfn_fifo_spec_2.
Check bfn_fifo_spec_3.

End BFN_FIFO.
