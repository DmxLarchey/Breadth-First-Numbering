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
 
  Implicit Type (t : bt X) (l m ll ts : list (bt X)).

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

  (** cs ~lt subtrees ts is a clear precondition for forest_rebuilt to 
      work correctly *)

  Fact forest_rebuild_app i ts1 ts2 cs :
          cs ~lt subtrees (ts1++ts2) 
       -> exists cs1 cs2, 
          cs = cs1 ++cs2
       /\ forest_rebuild i (ts1++ts2) cs = forest_rebuild i ts1 cs1 
                                        ++ forest_rebuild (length ts1+i) ts2 cs2.
  Proof.
    revert i cs; induction ts1 as [ | [ x | u x v ] ts1 IH ]; intros i cs H; simpl.
    + exists nil, cs; auto.
    + simpl in H.
      destruct (IH (S i) cs H) as (cs1 & cs2 & H1 & H2).
      exists cs1, cs2; split; auto.
      rewrite H2; do 3 f_equal; omega.
    + simpl in H.
      destruct cs as [ | a [ | b cs' ] ].
      - inversion H.
      - apply Forall2_cons_inv, proj2 in H.
        inversion H.
      - apply Forall2_cons_inv in H; destruct H as (H1 & H).
        apply Forall2_cons_inv in H; destruct H as (H2 & H).
        destruct (IH (S i) cs' H) as (cs1 & cs2 & H3 & H4).
        exists (a::b::cs1), cs2; split.
        * subst; auto.
        * rewrite H4; simpl.
          do 3 f_equal; omega.
  Qed.

  Definition is_bfn_from n k := is_seq_from n (bft_f k).

  Lemma forest_rebuild_spec i ts cs :
                               subtrees ts ~lt cs
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
        
    Admitted.

    Fixpoint bfn_f_level i l : { r | l ~lt r /\ is_bfn_from i r }.
    Proof.
      induction on i l as loop with measure (lsum l).
      case_eq l.
      + intros E.
        exists nil; split.
        * constructor.
        * red; rewrite bft_f_fix_0; red; auto.
      + intros b l' E; rewrite <- E.
        destruct (loop (length l+i) (subtrees l)) as (r' & H1 & H2).
        { destruct (subtrees_dec l); auto; subst; discriminate. }
        exists (forest_rebuild i l r').
        apply forest_rebuild_spec; auto.
    Defined.

End breadth_first_numbering_by_levels.

Extraction bfn_f_level.
