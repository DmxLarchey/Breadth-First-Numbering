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

  (** The structure of this proof is the following:

      We use refine to specify the computational content and
      proof obligations are solved inside { }.

      At some point, we need pattern matching to decompose 
      term in hypotheses as well as in the conclusion. The
      simplest way to do it is to revert the hypothesis in 
      the conclusion before the match and intro it in the
      different match branches. This corresponds to dependent
      pattern matching but hand-writting it in refines is
      much more complicated than

      revert Hq; refine (match q with ... => ... end); intros Hq

      By solving proof obligations in {}, we let the computational 
      content to develop itself in the main branch

      Also, using fully specified terms fifo_3q_*_full also
      use to avoid generalizing fifo_3q_*_spec before the
      next pattern matching

    *)

  Definition bfn_3q_f n (p : fX) : { q : fN | fifo_3q_list p ~lt rev (fifo_3q_list q) /\ is_bfn_from n (rev (fifo_3q_list q)) }.
  Proof.
    induction on n p as bfn_3q_f with measure (fifo_3q_sum p).

    refine (let (b,Hb) := fifo_3q_void_full p in _);
    revert Hb; refine (match b with 
      | true  => fun Hp => exist _ fifo_3q_nil _
      | false => fun Hp => let (d1,Hd1) := fifo_3q_deq_full p _ in _
    end).
 
    { apply proj1 in Hp; rewrite Hp, fifo_3q_nil_spec; split; simpl; auto.
      red; rewrite bft_f_fix_0; simpl; auto. }
    { intros H; apply Hp in H; discriminate. }

    revert Hd1; refine (match d1 with
      | (leaf x    , p1) => fun Hp1 => let (q,Hq) := bfn_3q_f (S n) p1 _ 
                                       in  exist _ (fifo_3q_enq q (leaf n)) _
      | (node a x b, p1) => fun Hp1 => let (q,Hq) := bfn_3q_f (S n) (fifo_3q_enq (fifo_3q_enq p1 a) b) _ in 
                                       let (d2,Hd2) := fifo_3q_deq_full q _ 
                                       in  _
    end); simpl in Hp1.

    { unfold fifo_3q_sum; rewrite Hp1; simpl; omega. }
    { destruct Hq as (H5 & H6).
      rewrite Hp1, fifo_3q_enq_spec.
      subst; split; auto.
      + rewrite rev_app_distr; simpl; auto.
      + rewrite rev_app_distr; simpl; red.
        rewrite bft_f_fix_3; simpl; rewrite <- app_nil_end; auto. }
    { unfold fifo_3q_sum. 
      rewrite fifo_3q_enq_spec, fifo_3q_enq_spec, app_ass; simpl.
      rewrite lsum_app, Hp1; simpl; omega. }
    { apply proj1, Forall2_rev in Hq; intros H; revert Hq.
      rewrite H, fifo_3q_enq_spec, fifo_3q_enq_spec, app_ass; simpl.
      rewrite rev_app_distr; inversion 1. }

    revert Hd2; refine (match d2 with (u,q1) => _ end); intros Hq1;
    refine (let (d3,Hd3) := fifo_3q_deq_full q1 _ in _).

    { apply proj1, Forall2_rev in Hq; intros H; revert Hq.
      rewrite Hq1, H, fifo_3q_enq_spec, fifo_3q_enq_spec, app_ass; simpl.
      rewrite rev_app_distr; simpl. 
      inversion 1; inversion H6. }

    revert Hd3; refine (match d3 with 
      | (v,q2) => fun Hq2 => let (q3,Hq3) := fifo_3q_enq_full q2 (node v n u)
                             in  exist _ q3 _
    end); simpl in Hq2, Hq3.

    { destruct Hq as (H5,H6).
      rewrite fifo_3q_enq_spec, fifo_3q_enq_spec, Hq1, Hq2 in H5. 
      repeat (rewrite app_ass in H5; simpl in H5).
      apply Forall2_2snoc_inv in H5.
      destruct H5 as (G1 & G2 & H5).
      rewrite Hq1, Hq2 in H6; simpl in H6; rewrite app_ass in H6; simpl in H6.
      unfold is_bfn_from in H6 |- *.
      rewrite Hp1, Hq3, rev_app_distr; simpl.  
      rewrite bft_f_fix_3; simpl; split; auto. }
  Defined.

  Section bfn.

    Let bfn_3q_full (t : bt X) : { t' | t ~t t' /\ is_seq_from 0 (bft_std t') }.
    Proof.
      refine (match @bfn_3q_f 0 (fifo_3q_enq fifo_3q_nil t) with 
        | exist _ q Hq => let (d1,Hd1) := fifo_3q_deq_full q _ in _ 
      end).

      { intros H; rewrite fifo_3q_enq_spec, fifo_3q_nil_spec, H in Hq.
        apply proj1 in Hq; inversion Hq. }

      revert Hd1; refine (match d1 with (x,q1) => fun Hq1 => exist _ x _ end); simpl in Hq1.

      { rewrite fifo_3q_enq_spec, fifo_3q_nil_spec in Hq; destruct Hq as (H1 & H2).
        rewrite <- bft_std_eq_bft.
        rewrite Hq1 in H1; simpl in H1.
        apply Forall2_snoc_inv with (l := nil) in H1.
        destruct H1 as (G1 & H1).
        apply Forall2_nil_inv_right in H1.
        apply f_equal with (f := @rev _) in H1.
        rewrite rev_involutive in H1; simpl in H1.
        rewrite Hq1, H1 in H2; simpl in H2.
        auto. }
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
             

