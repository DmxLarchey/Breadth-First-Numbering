(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** Extraction of a breadth-first search and breadth-first numbering algorithms 
    from Coq to Ocaml 

       see http://okasaki.blogspot.com/2008/07/breadth-first-numbering-algorithm-in.html
       and https://www.westpoint.edu/eecs/SiteAssets/SitePages/Faculty%20Publication%20Documents/Okasaki/jfp95queue.pdf
       and https://www.cs.cmu.edu/~rwh/theses/okasaki.pdf
       and https://www.westpoint.edu/eecs/SiteAssets/SitePages/Faculty%20Publication%20Documents/Okasaki/icfp00bfn.pdf

*)

(* open List;;

   type 'a bt = Leaf of 'a | Node of 'a bt * 'a * 'a bt;;

   let root t = match t with Leaf x -> x | Node (_,x,_) -> x;;

   let rec subt ll =
     match ll with
       | []                 -> []
       | Leaf _       :: ll -> subt ll
       | Node (a,_,b) :: ll -> a :: b :: subt ll;;

  let rec niveaux ll =
    match ll with
      | [] -> []
      | _  -> map root ll :: niveaux (subt ll);;


  let rec list2bt x ll =
    match ll with
      | []    -> Leaf 0
      | y::ll -> Node (Leaf y,x,list2bt x ll);;

  niveaux [Node (Leaf 1,2,Leaf 3)];;
  niveaux [list2bt 0 [1;2;3;4;5]];;

*)

Require Import List Arith Omega Wellfounded.

Set Implicit Arguments.

Section measure_rect.

  Variables (X : Type) (m : X -> nat) (P : X -> Type)
            (HP : forall x, (forall y, m y < m x -> P y) -> P x).

  Let R x y := m x < m y.

  Fact Acc_measure : well_founded R.
  Proof. unfold R; apply wf_inverse_image, lt_wf. Qed.

  Theorem measure_rect : forall x, P x.
  Proof.
    intros x; generalize (Acc_measure x); revert x.
    refine (fix loop x (H : Acc R x) { struct H } : P x := @HP x (fun y Hy => loop y _)).
    destruct H as [ H ]; apply H; trivial.
  Qed.

End measure_rect.

Section Forall2.

  Variables (X Y : Type) (R : X -> Y -> Prop).

  Fact Forall2_length l m : Forall2 R l m -> length l = length m.
  Proof. induction 1; simpl; f_equal; auto. Qed.

  Fact Forall2_nil_inv_right l : Forall2 R nil l -> l = nil.
  Proof. inversion 1; auto. Qed.

  Fact Forall2_cons_inv x l y m : Forall2 R (x::l) (y::m) -> R x y /\ Forall2 R l m.
  Proof. inversion 1; auto. Qed.

  Fact Forall2_app_inv l1 l2 m1 m2 : length l1 = length m1
                                  -> Forall2 R (l1++l2) (m1++m2)
                                  -> Forall2 R l1 m1 /\ Forall2 R l2 m2.
  Proof.
    revert m1; induction l1 as [ | x l1 IH ]; intros [ | y m1 ]; 
      try discriminate; simpl; intros H1 H2; auto.
    apply Forall2_cons_inv in H2.
    destruct H2; destruct (IH m1); auto.
  Qed.

End Forall2.
