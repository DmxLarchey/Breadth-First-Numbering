(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega Extraction.
Require Import list_utils wf_utils bt bft bft_spec bft_inj fifo_axm bfn_gen.

Set Implicit Arguments.

Section bfr_3q.

  Let fifo_3q_sum { X } (q : fifo_3q (bt X)) := lsum (fifo_3q_list q). 

  Variable (X Y : Type).

  Notation fX := (fifo_3q (bt X)).
  Notation fY := (fifo_3q (bt Y)).

  Fixpoint bfr_3q_f (p : fX) (ll : list Y) { struct ll } : 
            fifo_3q_sum p = length ll
         -> { q : fY | fifo_3q_list p ~lt rev (fifo_3q_list q) 
                    /\ bft_f (rev (fifo_3q_list q)) = ll }.
  Proof.
    unfold fifo_3q_sum in *.
    refine (match ll with 
      | nil   => fun Hll => let (q,Hq)   := @fifo_3q_nil_full _ 
                            in  exist _ q _
      | y::mm => fun Hll => let (d1,Hd1) := fifo_3q_deq_full p _ 
                            in  _
    end).
    all: cycle 2.
    revert Hd1; refine (match d1 with (t,p1) => _ end); intros Hp1.
    rewrite Hp1 in Hll; simpl in Hll; clear d1.
    revert Hll Hp1; refine (match t with 
      | leaf x     => fun Hll Hp1 => let (q,Hq)   := bfr_3q_f p1 mm _ in 
                                     let (q1,Hq1) := fifo_3q_enq_full q (leaf y) 
                                     in  exist _ q1 _
      | node a x b => fun Hll Hp1 => let (p2,Hp2) := fifo_3q_enq_full p1 a    in
                                     let (p3,Hp3) := fifo_3q_enq_full p2 b    in
                                     let (q,Hq)   := bfr_3q_f p3 mm _         in  
                                     let (d2,Hd2) := fifo_3q_deq_full q _     in _
    end); auto.
    all: cycle 3.
    revert Hd2; refine (match d2 with 
      | (u,q1) => fun Hd2 => let (d3,Hd3) := fifo_3q_deq_full q1 _ 
                             in  _ 
    end).
    all: cycle 1.
    revert Hd3; refine (match d3 with
      | (v,q2) => fun Hd3 => let (q3,Hq3) := fifo_3q_enq_full q2 (node v y u) 
                             in  exist _ q3 _
    end).
    all: cycle 1.

    * revert Hll; rewrite Hq; simpl.
      generalize (fifo_3q_list p).
      intros [ | [] ? ]; simpl; try discriminate.
      split; auto.
      rewrite bft_f_fix_0; auto.
    * intros E; rewrite E in Hll; discriminate.
    * destruct Hq as (Hq2 & Hq3).
      rewrite Hp1, Hq1, rev_app_distr; split; simpl; auto.
      rewrite bft_f_fix_3, <- app_nil_end, Hq3; auto.
    * rewrite Hp3, Hp2; repeat rewrite lsum_app; simpl in Hll |- *; omega.
    * destruct Hq as (Hq_1 & Hq_2); 
      apply Forall2_rev in Hq_1; rewrite rev_involutive in Hq_1.
      intros H; rewrite H, Hp3, rev_app_distr in Hq_1; inversion Hq_1.
    * destruct Hq as (Hq_1 & Hq_2).
      apply Forall2_rev in Hq_1; rewrite rev_involutive in Hq_1.
      intros H; rewrite Hd2, H, Hp3, Hp2 in Hq_1. 
      repeat rewrite rev_app_distr in Hq_1.
      inversion Hq_1.
      inversion H5.
    * destruct Hq as (Hq_1 & Hq_2).
      apply Forall2_rev in Hq_1; rewrite rev_involutive in Hq_1.
      simpl in *.
      rewrite Hp1, Hq3, rev_app_distr; simpl.
      rewrite Hp3, Hp2, Hd2, Hd3 in Hq_1.
      repeat rewrite rev_app_distr in Hq_1.
      simpl in Hq_1.
      apply Forall2_cons_inv in Hq_1; destruct Hq_1 as (Hq_3 & Hq_1).
      apply Forall2_cons_inv in Hq_1; destruct Hq_1 as (Hq_4 & Hq_1).
      apply Forall2_rev in Hq_1.
      rewrite rev_involutive in Hq_1.
      split; auto.
      rewrite bft_f_fix_3; simpl; f_equal.
      rewrite <- Hq_2, Hd2, Hd3; f_equal; simpl.
      rewrite app_ass; auto.
  Defined.
  
  Section bfr.

    Let bfr_3q_full (t : bt X) (l : list Y) : m_bt t = length l -> { t' | t ~t t' /\ bft_std t' = l }.
    Proof.
      intros H.
      refine (match @bfr_3q_f (fifo_3q_enq fifo_3q_nil t) l _ with 
        | exist _ q Hq => let (d1,Hd1) := fifo_3q_deq_full q _ in _ 
      end).
      all: cycle 2.
      revert Hd1; refine(match d1 with
        | (t',q') => fun Hd1 => exist _ t' _
      end).
      all: cycle 1.

      + unfold fifo_3q_sum; rewrite fifo_3q_enq_spec, fifo_3q_nil_spec; simpl; omega.
      + intros E; rewrite E in Hq; apply proj2 in Hq; simpl in Hq.
        rewrite bft_f_fix_0 in Hq; subst.
        generalize (m_bt_ge_1 t); simpl in *; omega.
      + destruct Hq as (Hq_1 & Hq_2); simpl in Hd1.
        apply Forall2_rev in Hq_1.
        rewrite fifo_3q_enq_spec, fifo_3q_nil_spec, rev_involutive, Hd1 in Hq_1; simpl in Hq_1.
        apply Forall2_cons_inv in Hq_1.
        destruct Hq_1 as (Hq_3 & Hq_1).
        apply Forall2_nil_inv_right in Hq_1.
        split; auto.
        rewrite Hd1, Hq_1 in Hq_2.
        simpl in Hq_2.
        rewrite <- bft_std_eq_bft; auto.
    Qed.

    Definition bfr_3q t l H := proj1_sig (bfr_3q_full t l H).

    Fact bfr_3q_spec_1 t l H : t ~t bfr_3q t l H.
    Proof. apply (proj2_sig (bfr_3q_full t l H)). Qed.

    Fact bfr_3q_spec_2 t l H : bft_std (bfr_3q t l H) = l.
    Proof. apply (proj2_sig (bfr_3q_full t l H)). Qed.

  End bfr.

End bfr_3q.

(** BFN (Breadth-First Numbering) is a particular instance of 
    BFR (Breadth-First Reconstruction)   *)

Theorem bfr_bfn_3q X (t : bt X) : bfn_3q t = bfr_3q t (seq_an 0 (m_bt t)) (eq_sym (seq_an_length _ _)).
Proof.
  apply bft_std_inj.
  * apply bt_eq_trans with (s := t).
    + apply bt_eq_sym, bfn_3q_spec_1.
    + apply bfr_3q_spec_1.
  * rewrite bfr_3q_spec_2, bfn_3q_spec_3; trivial.
Qed.

(* Notice that fifo_3q_deq is extracted to a function that loops forever
   if the input is the empty queue, ie does not following the spec *)

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Recursive Extraction bfr_3q.

Check bfr_3q.
Check bfr_3q_spec_1.
Check bfr_3q_spec_2.
Check bfr_bfn_3q.
             

