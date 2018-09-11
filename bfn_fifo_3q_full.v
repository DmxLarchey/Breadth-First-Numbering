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
Require Import list_utils wf_utils bt bft fifo.

Set Implicit Arguments.

Section seq_an.

  (* seq_an a n = [a;a+1;...;a+(n-1)] *)

  Fixpoint seq_an a n : list nat :=
    match n with
      | 0    => nil
      | S n  => a::seq_an (S a) n
    end.

  Fact seq_an_length a n : length (seq_an a n) = n.
  Proof. revert a; induction n; simpl; intros; f_equal; auto. Qed.

  Fact seq_an_spec a n x : In x (seq_an a n) <-> a <= x < a+n.
  Proof. 
    revert x a; induction n as [ | n IHn ]; intros x a; simpl;
      [ | rewrite IHn ]; omega.
  Qed.

  Fixpoint is_seq_from n (l : list nat) { struct l }: Prop :=
    match l with  
      | nil  => True
      | x::l => n = x /\ is_seq_from (S n) l
    end.

  Theorem is_seq_from_spec a l : is_seq_from a l <-> exists n, l = seq_an a n.
  Proof.
    revert a; induction l as [ | x l IH ]; intros a; simpl.
    + split; auto; exists 0; auto.
    + rewrite IH; split.
      * intros (? & n & Hn); subst x; exists (S n); subst; auto.
      * intros ([ | n ] & ?); subst; try discriminate.
        simpl in H; inversion H; subst; split; auto.
        exists n; auto.
  Qed.

End seq_an.

Section bfn.

  Let fifo_3q_sum { X } (q : fifo_3q (bt X)) := lsum (fifo_3q_list q). 

  Variable (X : Type).

  Notation fX := (fifo_3q (bt X)). 
  Notation fN := (fifo_3q (bt nat)).

  (* the forest (list of bt nat) is a breadth first numbering from n if
     its breadth first traversal yields [n;n+1;....;m[ for some m
   *)

(*
  Let fX_spec := fifo_3q_spec (bt X).
  Let fN_spec := fifo_3q_spec (bt nat).

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
        if q_void p then q_nil
        else let c,p1 = fifo_3q_deq p 
             in match c with
               | Leaf _
              -> q_enq (bfn_f (1+n) p1) (Leaf u)
               | Node (a, _, b)
              -> let u,q1 = q_deq (bfn_f (1+n) (q_enq (q_enq p1 a) b))     in
                 let v,q2 = q_deq q1 
                 in q_enq q2 (Node (v, n, u))

      Hence the CC should be something like 

      refine (
        let (b,Hb) := fifo_3q_void_full p 
        in match b with 
          | true  
          => let (q,Hq) := @fifo_3q_nil _
             in exist _ q _
          | false 
          => let (d1,Hd1) := fifo_3q_deq_full p _ 
             in match d1 with
               | (leaf x    , p1) 
               => let (q,Hq) := bfn_3q_f (S n) p1 _          in
                  let (q1,Hq1) := fifo_3q_enq_full q (leaf n) 
                  in exist _ q1 _
               | (node a x b, p1) => fun Hp1 
               => let (p2,Hp2)     := fifo_3q_enq_full p1 a    in
                  let (p3,Hp3)     := fifo_3q_enq_full p2 b    in
                  let (q,Hq)       := bfn_3q_f (S n) p3 _      in
                  let ((u,q1),Hq1) := fifo_3q_deq_full q _     in
                  let ((v,q2),Hq2) := fifo_3q_deq_full q1 _    in
                  let (q3,Hq3)     := fifo_3q_enq_full q2 (node v n u)
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

      Also, using fully specified terms like fifo_3q_enq_full 
      instead of the pair fifo_3q_enq/fifo_3q_enq_spec allows
      use to avoid generalizing fifo_3q_enq_spec before the
      next pattern matching.

    *)

  Definition bfn_3q_f n (p : fX) : { q : fN | fifo_3q_list p ~lt rev (fifo_3q_list q) /\ is_bfn_from n (rev (fifo_3q_list q)) }.
  Proof.
    induction on n p as bfn_3q_f with measure (fifo_3q_sum p).

    refine (let (b,Hb) := fifo_3q_void_full p in _).
    revert Hb; refine (match b with 
      | true  => fun Hp 
      => let (q,Hq) := @fifo_3q_nil_full _ 
         in exist _ q _
      | false => fun Hp 
      => let (d1,Hd1) := fifo_3q_deq_full p _ 
         in _
    end). 
    all: cycle 2. (* We queue 2 POs *)
    revert Hd1; refine (match d1 with
      | (leaf x    , p1) => fun Hp1 
      => let (q,Hq)   := bfn_3q_f (S n) p1 _ in  
         let (q1,Hq1) := fifo_3q_enq_full q (leaf n) 
         in exist _ q1 _
      | (node a x b, p1) => fun Hp1 
      => let (p2,Hp2) := fifo_3q_enq_full p1 a    in
         let (p3,Hp3) := fifo_3q_enq_full p2 b    in
         let (q,Hq)   := bfn_3q_f (S n) p3 _ in
         let (d2,Hd2) := fifo_3q_deq_full q _ 
         in  _
    end); simpl in Hp1.
    all: cycle 4. (* We queue 4 POs *)
    revert Hd2; refine (match d2 with (u,q1) => _ end); intros Hq1.
    refine (let (d3,Hd3) := fifo_3q_deq_full q1 _ in _).
    all: cycle 1. (* We queue 1 PO *) 
    revert Hd3; refine (match d3 with 
      | (v,q2) => fun Hq2 
      => let (q3,Hq3) := fifo_3q_enq_full q2 (node v n u)
         in  exist _ q3 _
    end); simpl in Hq2, Hq3.
    all: cycle 1. (* We queue 1 PO *) 

    (* And now, we show POs *)
   
    * apply proj1 in Hp; rewrite Hp, Hq; split; simpl; auto.
      red; rewrite bft_f_fix_0; simpl; auto.
    * intros H; apply Hp in H; discriminate.
    * unfold fifo_3q_sum; rewrite Hp1; simpl; omega.
    * destruct Hq as (H5 & H6).
      rewrite Hp1, Hq1.
      subst; split; auto.
      + rewrite rev_app_distr; simpl; auto.
      + rewrite rev_app_distr; simpl; red.
        rewrite bft_f_fix_3; simpl; rewrite <- app_nil_end; auto.
    * unfold fifo_3q_sum. 
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

    Let bfn_3q_full (t : bt X) : { t' | t ~t t' /\ is_seq_from 0 (bft_std t') }.
    Proof.
      refine (match @bfn_3q_f 0 (fifo_3q_enq fifo_3q_nil t) with 
        | exist _ q Hq => let (d1,Hd1) := fifo_3q_deq_full q _ in _ 
      end).
      all: cycle 1. (* We queue 1 PO *) 
      revert Hd1; refine (match d1 with (x,q1) => fun Hq1 => exist _ x _ end); simpl in Hq1.
      all: cycle 1. (* We queue 1 PO *) 

      + intros H; rewrite fifo_3q_enq_spec, fifo_3q_nil_spec, H in Hq.
        apply proj1 in Hq; inversion Hq.

      + rewrite fifo_3q_enq_spec, fifo_3q_nil_spec in Hq; destruct Hq as (H1 & H2).
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

    Definition bfn_3q t := proj1_sig (bfn_3q_full t).

    Fact bfn_3q_spec_1 t : t ~t bfn_3q t.
    Proof. apply (proj2_sig (bfn_3q_full t)). Qed.

    Fact bfn_3q_spec_2 t : exists n, bft_std (bfn_3q t) = seq_an 0 n.
    Proof. apply is_seq_from_spec, (proj2_sig (bfn_3q_full t)). Qed.

  End bfn.

End bfn.

(* Notice that fifo_3q_deq is extracted to a function that loops forever
   if the input is the empty queue, ie does not following the spec *)

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Recursive Extraction bfn_3q.

Check bfn_3q.
Check bfn_3q_spec_1.
Check bfn_3q_spec_2.
             

