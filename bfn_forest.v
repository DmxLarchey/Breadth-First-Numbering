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

(** Extraction of a breadth-first traversal from Coq to Ocaml 

   open List;;

   type 'a bt = Leaf of 'a | Node of 'a bt * 'a * 'a bt;;

   let root t = match t with Leaf x -> x  | Node (_,x,_) -> x;;
   let subt t = match t with Leaf x -> [] | Node (a,x,b) -> [a;b];;

   (* forest_decomp ll = (map root ll, flat_map subt ll) *)

   let rec forest_decomp = function
     | []   -> ([], [])
     | t::l -> let ro,sf = forest_decomp l 
               in match t with
                    | Leaf x         -> (x::ro,sf)
                    | Node (a, x, b) -> (x::ro,a::b::sf)

   let rec bft_f = function 
     | [] -> []
     | _  -> let ro,st = forest_decomp u in ro @ bft_f st

   let bft_forest t = bft_f (t::nil)

*)

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
        | leaf x     => (n,ch)
        | node a x b => (S n,a::b::ch)
      end
    end.

  Fact forest_children_eq X ll : let (n,ch) := @forest_children X ll in ch = subtrees ll /\ 2*n = length ch. 
  Proof. 
    induction ll as [ | [ x | a x b ] ll IH ]; simpl; auto; 
    destruct (forest_children ll) as (n,ch); auto.
    destruct IH as (? & IH); subst; split; auto; simpl; omega.
  Qed.

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

  Fact forest_rebuild_spec i ts cs : 
        (exists n ls, ts ~lt ls /\ (n,cs) = forest_children ls /\ is_bfn_from (i+n) cs)  
     -> ts ~lt forest_rebuild i ts cs /\ is_bfn_from i (forest_rebuild i ts cs).
  Proof.
    revert i cs.
    induction ts as [ | [ x | a x b ] ts IH ]; intros i cs (n & ls & H1 & H2 & H3); simpl.
    + split; auto; red; rewrite bft_f_fix_0; simpl; auto.
    + destruct ls as [ | t ls ]; try (inversion H1; fail).
      apply Forall2_cons_inv in H1.
      destruct H1 as (H1 & H4).
      destruct t as [ u | ]; try (inversion H1; fail); clear H1. 
      simpl in H2.
      case_eq (forest_children ls); intros x1 y1 E.
      rewrite E in H2; inversion H2; subst x1 y1; clear H2.
      destruct (IH i cs) as (H5 & H6).
      { exists n, ls; auto. }
      split.
      * constructor.
        - constructor.
        - apply lbt_eq_trans with (1 := H5), forest_rebuild_bt_eq.
      * red; rewrite bft_f_fix_oka_1; simpl; split; auto. 
          
    Admitted.

End breadth_first_numbering_by_levels.
