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

Require Import List Arith Omega Wellfounded Extraction.
Require Import list_utils wf_utils zip bt bft_std bft_forest.

Set Implicit Arguments.

Section breadth_first_numbering_by_levels.

  Notation subtrees := (flat_map (@subt _)).

  Fixpoint forest_children {X} ll : nat * list (bt X) :=
    match ll with 
      | nil   => (0,nil)
      | t::l => let (n,ch) := forest_children l in
      match t with
        | leaf x     => (S n,ch)
        | node a x b => (S n,a::b::ch)
      end
    end.

(*
  Fact forest_children_eq X ll : let (n,ch) := @forest_children X ll in ch = subtrees ll /\ 2*n = length ch. 
  Proof. 
    induction ll as [ | [ x | a x b ] ll IH ]; simpl; auto; 
    destruct (forest_children ll) as (n,ch); auto.
    destruct IH as (? & IH); subst; split; auto; simpl; omega.
  Qed.
*)

  Context (X : Type).
 
  Implicit Type (t : bt X) (l m ll : list (bt X)).

  Fixpoint forest_rebuild i (ts : list (bt X)) cs :=
    match ts with 
      | nil => nil
      | leaf _ :: ts => leaf i :: forest_rebuild (S i) ts cs
      | node _ _ _ :: ts =>
      match cs with
        | a :: b :: cs => node a i b :: forest_rebuild (S i) ts cs
        | _ => nil
      end
    end.

  Fact forest_rebuild_bt_eq i j ts cs : forest_rebuild i ts cs ~lt forest_rebuild j ts cs.
  Proof.
    revert i j cs; induction ts as [ | [ x | a x b ] ts IH ]; intros i j cs; simpl.
    + constructor.
    + constructor; auto.
    + destruct cs as [ | u [ | v ? ] ]; simpl; auto.
      constructor; auto; constructor; apply bt_eq_refl.
  Qed.

  Definition is_bfn_from n k := is_seq_from n (bft_f k).

  Lemma forest_rebuild_spec i ts cs :
                               cs ~lt subtrees ts 
                            -> is_bfn_from (length ts + i) cs 
                            -> ts ~lt forest_rebuild i ts cs
                            /\ is_bfn_from i (forest_rebuild i ts cs).
  Proof.
    revert i cs.
    induction on ts as IH with measure (lsum ts).
    revert ts IH; intros [ | [ x | a x b ] ts ] IH; simpl; intros i cs H1 H2.
    + split; auto; red; rewrite bft_f_fix_0; red; auto.
    + destruct (IH ts) with (i := S i) (cs := cs) as (H3 & H4); auto.
      { rewrite plus_comm; simpl; rewrite plus_comm; auto. }
      split.
      * repeat (constructor; auto).
      * red; rewrite bft_f_fix_oka_1; simpl; split; auto.
    + destruct cs as [ | u cs ]; try (inversion H1; fail).
      apply Forall2_cons_inv in H1; destruct H1 as (H3 & H1).
      destruct cs as [ | v cs ]; try (inversion H1; fail).
      apply Forall2_cons_inv in H1; destruct H1 as (H4 & H1).
      red in H2.
      destruct (IH (ts++a::b::nil)) with (i := S i) (cs := cs++u::v::nil).
      * rewrite lsum_app; simpl; omega.
      * rewrite subtrees_app.
        apply Forall2_app; auto.
        

(*      change (u::v::cs) with ((u::v::nil)++cs) in H2. *)
      do 2 (rewrite bft_f_fix_4 in H2; simpl in H2).
      destruct H2 as (H5 & H6 & H2).
      split.
      Focus 2.
      red.
      rewrite bft_f_fix_oka_2.
      split; auto.
    Admitted.

End breadth_first_numbering_by_levels.
