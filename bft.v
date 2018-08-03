(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** Extraction of a breadth-first traversal from Coq to Ocaml 

   open List;;

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
Require Import utils bt.

Set Implicit Arguments.

Section breadth_first_traversal.

  Context (X : Type).
 
  Implicit Type (t : bt X) (l ll : list (bt X)).

  (* This is the standard/obvious specification of breadth-first traversal *)

  Fixpoint niveaux_tree t : list (list X) :=
    match t with 
      | leaf x     => (x::nil) :: nil
      | node a x b => (x::nil) :: zip (@app _) (niveaux_tree a) (niveaux_tree b)
    end.
    
  Definition bft_std t : list X := concat (niveaux_tree t).

  Fixpoint subt ll : list (bt X) :=
    match ll with
      | nil              => nil
      | leaf _     :: ll => subt ll
      | node a _ b :: ll => a :: b :: subt ll
    end.
    
  Fact subt_app l m : subt (l++m) = subt l ++ subt m.
  Proof. induction l as [ | [ | ] ]; simpl; repeat f_equal; auto. Qed.

  (* The measure of the size of a forest on which most complicated inductions are based *) 

  Definition lsum := fold_right (fun t y => m_bt t + y) 0.

  Fact lsum_app l m : lsum (l++m) = lsum l + lsum m.
  Proof. induction l; simpl; omega. Qed.

  Fact subt_dec ll : ll = nil \/ lsum (subt ll) < lsum ll.
  Proof.
    induction ll as [ | [|] ]; simpl; auto;
      right; destruct IHll; subst; simpl; auto; omega.
  Qed.

  Fact subt_le ll : lsum (subt ll) <= lsum ll.
  Proof. destruct (subt_dec ll); subst; simpl; omega. Qed.
  
  (* The specification of 
  
      let rec niveaux ll =
        match ll with
          | [] -> []
          | _  -> map root ll :: niveaux (subt ll);;

     as a graph *)

  Inductive g_niv : list (bt X) -> list (list X) -> Prop :=
    | in_gn_0 : g_niv nil nil
    | in_gn_1 : forall l p, l <> nil -> g_niv (subt l) p -> g_niv l (map root l :: p).
    
  Ltac mysolve := try match goal with H: ?x <> ?x |- _ => destruct H; reflexivity end.

  Fact g_niv_fun l m1 m2 : g_niv l m1 -> g_niv l m2 -> m1 = m2.
  Proof.
    intros H; revert H m2.
    induction 1 as [ | l m1 H1 H2 IH2 ]; intros m2 H3; inversion H3; auto; subst; mysolve.
    f_equal; apply IH2; trivial.
  Qed.
    
  Fact g_niv_app l rl m rm : g_niv l rl -> g_niv m rm -> g_niv (l++m) (zip (@app _) rl rm).
  Proof.
    intros H1; revert H1 m rm.
    induction 1 as [ | l rl H1 H2 IH2 ]; simpl; auto.
    induction 1 as [ | m rm H3 H4 IH4 ]; simpl; auto.
    * rewrite <- app_nil_end; constructor; auto.
    * rewrite <- map_app; constructor.
      + destruct l; try discriminate.
        destruct H1; auto.
      + rewrite subt_app; apply IH2; auto.
  Qed. 

  (* We show that niveaux_tree satisfies g_niv *)

  Fact g_niv_tree t : g_niv (t::nil) (niveaux_tree t).
  Proof.
    induction t as [ x | a Ha x b Hb ].
    * constructor 2; try discriminate.
      constructor.
    * simpl; constructor 2; try discriminate.
      apply (g_niv_app Ha Hb).
  Qed.
  
  (* We reify the graph g_niv using well-founded 
     induction directly (instead of using measure_rect)
  
     This one extracts to the exact same Ocaml algo
     than advertised in the opening comments *)

  Section niveaux_rec.

    Let R x y := lsum x < lsum y.

    Let niveaux_rec : forall ll, Acc R ll -> sig (g_niv ll).
    Proof.
      refine (fix loop ll T { struct T } := 
        match ll as l return ll = l -> sig (g_niv l) with
          | nil  => fun _ => exist _ nil _
          | t::l => fun E => 
            let (r,Hr) := loop (subt ll) _
            in               exist _ (map root ll :: r) _
        end eq_refl).
      1,2 : cycle 1. 
      * destruct T as [ T ]; apply T; red.
        destruct (subt_dec ll); auto.
        subst; discriminate.
      * constructor.
      * rewrite <- E.
        constructor; auto.
        subst; discriminate.
    Qed.

    Definition niveaux ll : list (list X) := proj1_sig (@niveaux_rec ll (Acc_measure _ _)).
 
    Fact niveaux_spec ll : g_niv ll (niveaux ll).
    Proof. apply (proj2_sig _). Qed.

    Hint Resolve niveaux_spec.

    Fact niveaux_fix_0 : niveaux nil = nil.
    Proof. apply g_niv_fun with nil; auto; constructor. Qed.

    Fact niveaux_fix_1 ll : ll <> nil -> niveaux ll = map root ll :: niveaux (subt ll).
    Proof. intro; apply g_niv_fun with ll; auto; constructor; auto. Qed.
  
  End niveaux_rec.
  
  Fact niveaux_eq_niveaux_tree t : niveaux (t::nil) = niveaux_tree t.
  Proof.
    apply g_niv_fun with (t::nil).
    + apply niveaux_spec.
    + apply g_niv_tree.
  Qed.

  (* Breadth first traversal of a forest *)

  Definition bft_f l := concat (niveaux l).

  (* Efficient breadth first traversal of a tree *)

  Definition bft t := bft_f (t::nil).

  (* bft is extensionally equal to bft_std *)
  
  Theorem bft_std_eq_bft t : bft t = bft_std t.
  Proof. unfold bft_std, bft, bft_f; f_equal; apply niveaux_eq_niveaux_tree. Qed.

  (* Now important fixpoint equations of bft_f *)

  Fact bft_f_fix_0 : bft_f nil = nil.
  Proof. unfold bft_f; rewrite niveaux_fix_0; auto. Qed. 

  Section bft_f_fix_1.

    (** The identity   bft_f (l++m) = map root l ++ bft_f (m++subt l)   is critical
        to show the correctness of Breadth First Numbering *)

    (* The induction is a bit complex here because l and m alternate in the proof *)

    Let cnsapp_rec n : forall l m, lsum (l++m) < n -> concat (niveaux (l++m)) = map root l ++ concat (niveaux (m++subt l)).
    Proof.
      induction n as [ | n IHn ]; simpl; intros l m H; try omega.
      destruct l as [ | [ x | a x b ] l ].
      + rewrite <- app_nil_end; auto.
      + rewrite niveaux_fix_1; try discriminate; simpl; f_equal.
        rewrite map_app, <- app_assoc; f_equal.
        rewrite IHn, <- subt_app; auto.
        apply lt_S_n, le_lt_trans with (2 := H).
        simpl; repeat rewrite lsum_app.
        generalize (subt_le l); omega.
      + simpl; rewrite niveaux_fix_1; try discriminate.
        simpl; f_equal; rewrite map_app, <- app_assoc; f_equal.
        rewrite IHn, subt_app; auto.
        apply lt_S_n, le_lt_trans with (2 := H).
        simpl; repeat rewrite lsum_app; simpl.
        generalize (subt_le l); omega.
    Qed.

    Lemma bft_f_fix_1 l m : bft_f (l++m) = map root l ++ bft_f (m++subt l).
    Proof. apply cnsapp_rec with (1 := le_refl _). Qed.

  End bft_f_fix_1.

  Corollary bft_f_fix_2 l : bft_f l = map root l ++ bft_f (subt l).
  Proof. rewrite (app_nil_end l) at 1; apply bft_f_fix_1. Qed.

  Corollary bft_f_fix_3 x l : bft_f (x::l) = root x :: bft_f (l++subt (x::nil)).
  Proof. apply bft_f_fix_1 with (l := _::nil). Qed.

End breadth_first_traversal.

Require Import Extraction.
Recursive Extraction bft_std bft.

Check bft_std_eq_bft.
