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

  Variable (fifo      : Type -> Type) 
           (fifo_list : forall X, fifo X -> list X)
           (fifo_nil  : forall X, fifo X)
           (fifo_enq  : forall X, fifo X -> X -> fifo X)
           (fifo_deq  : forall X q, @fifo_list X q <> nil -> X * fifo X)
           (fifo_void : forall X, fifo X -> bool)
           (fifo_nil_spec  : forall X, fifo_nil_prop (@fifo_list X) (fifo_nil X))
           (fifo_enq_spec  : forall X, fifo_enq_prop (@fifo_list X) (@fifo_enq X)) 
           (fifo_deq_spec  : forall X, fifo_deq_prop (@fifo_list X) (@fifo_deq X)) 
           (fifo_void_spec : forall X, fifo_void_prop (@fifo_list X) (@fifo_void X)).

  Let fifo_sum { X } (q : fifo (bt X)) := lsum (fifo_list q). 

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
    refine (match fifo_void p as b return fifo_void p = b -> _ with
      | true  => fun H1 => exist _ (@fifo_nil _) _
      | false => fun H1 => _
    end eq_refl).
    { apply fifo_void_spec in H1.
      rewrite H1, fifo_nil_spec; split; simpl; auto.
      red; rewrite bft_f_fix_0; simpl; auto. }
    assert (fifo_list p <> nil) as H2.
    { intro E; apply fifo_void_spec in E; rewrite E in H1; discriminate. }
    refine (match fifo_deq H2 as k return fifo_deq H2 = k -> _ with
      | (leaf x ,p') => _
      | (node a x b, p') => _
    end eq_refl); intros H3.
    + generalize (fifo_deq_spec H2); rewrite H3; intros H4.
      refine (let (q,Hq) := bfn_gen_f (S n) p' _ in exist _ (fifo_enq q (leaf n)) _).
      { unfold fifo_sum; rewrite H4; simpl; omega. }
      destruct Hq as (H5 & H6).
      rewrite H4, fifo_enq_spec.
      subst; split; auto.
      rewrite rev_app_distr; simpl; auto.
      rewrite rev_app_distr; simpl; red.
      rewrite bft_f_fix_3; simpl; rewrite <- app_nil_end; auto.
    + generalize (fifo_deq_spec H2); rewrite H3; intros H4.
      refine (let (q,Hq) := bfn_gen_f (S n) (fifo_enq (fifo_enq p' a) b) _ in _).
      { unfold fifo_sum. 
        rewrite fifo_enq_spec, fifo_enq_spec, app_ass; simpl.
        rewrite lsum_app, H4; simpl; omega. }
      destruct Hq as (H5 & H6).
      rewrite fifo_enq_spec, fifo_enq_spec, app_ass in H5; simpl in H5.
      assert (2 <= length (fifo_list q)) as H7.
      { apply Forall2_length in H5.
        rewrite app_length, rev_length in H5.
        simpl in H5; omega. }
      assert (fifo_list q <> nil) as H8.
      { revert H7; destruct (fifo_list q); simpl; try discriminate; intro; omega. } 
      generalize (fifo_deq_spec H8).
      refine (match fifo_deq H8 with (u,q') => _ end); intros H9.
      assert (fifo_list q' <> nil) as H10.
      { revert H7; rewrite H9; destruct (fifo_list q'); simpl; try discriminate; intro; omega. }
      generalize (fifo_deq_spec H10).
      refine (match fifo_deq H10 with (v,q'') => _ end); intros H11.
      exists (fifo_enq q'' (node v n u)).
      rewrite H4, fifo_enq_spec, rev_app_distr; simpl.
      rewrite H9, H11 in H5; simpl in H5; rewrite app_ass in H5; simpl in H5.
      rewrite H9, H11 in H6; simpl in H6; rewrite app_ass in H6; simpl in H6.
      unfold is_bfn_from in H6 |- *.
      apply Forall2_2snoc_inv in H5.
      destruct H5 as (G1 & G2 & H5).
      rewrite bft_f_fix_3; simpl; split; auto.
  Defined.

  Section bfn.

    Let bfn_full (t : bt X) : { t' | t ~t t' /\ is_seq_from 0 (bft_std t') }.
    Proof.
      refine (match @bfn_gen_f 0 (fifo_enq (@fifo_nil _) t) with exist _ q Hq => _ end).
      rewrite fifo_enq_spec, fifo_nil_spec in Hq; simpl in Hq.
      destruct Hq as (H1 & H2).
      assert (fifo_list q <> nil) as H3.
      { apply Forall2_length in H1; rewrite rev_length in H1.
        destruct (fifo_list q); discriminate. }
      generalize (fifo_deq_spec H3).
      refine (match fifo_deq H3 with (x,q') => _ end); intros H4.
      exists x.
      rewrite <- bft_std_eq_bft.
      rewrite H4 in H1; simpl in H1.
      apply Forall2_snoc_inv with (l := nil) in H1.
      destruct H1 as (G1 & H1).
      apply Forall2_nil_inv_right in H1.
      apply f_equal with (f := @rev _) in H1.
      rewrite rev_involutive in H1; simpl in H1.
      rewrite H4, H1 in H2; simpl in H2.
      auto.
    Qed.

    Definition bfn_gen t := proj1_sig (bfn_full t).

    Fact bfn_gen_spec_1 t : t ~t bfn_gen t.
    Proof. apply (proj2_sig (bfn_full t)). Qed.

    Fact bfn_gen_spec_2 t : exists n, bft_std (bfn_gen t) = seq_an 0 n.
    Proof. apply is_seq_from_spec, (proj2_sig (bfn_full t)). Qed.

  End bfn.

End bfn.

(* Notice that fifo_2l_deq is extracted to a function that loops forever
   if the input is the empty queue, ie does not following the spec *)

Recursive Extraction bfn_gen.

Check bfn_gen.
Check bfn_gen_spec_1.
Check bfn_gen_spec_2.

Section bfn_2q.

  Variable X : Type.

  Definition bfn_2q := @bfn_gen _ _ _ _ _ _ fifo_2q_nil_spec fifo_2q_enq_spec fifo_2q_deq_spec fifo_2q_void_spec X.

  Definition bfn_2q_spec_1 t : t ~t bfn_2q t.
  Proof. apply bfn_gen_spec_1. Qed.

  Definition bfn_2q_spec_2 t : exists n, bft_std (bfn_2q t) = seq_an 0 n.
  Proof. apply bfn_gen_spec_2. Qed.

End bfn_2q.

Extraction Inline bfn_gen.
Recursive Extraction bfn_2q.

Check bfn_2q.
Check bfn_2q_spec_1.
Check bfn_2q_spec_2.

