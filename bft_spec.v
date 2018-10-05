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


Require Import List Arith Omega Wellfounded Permutation.
Require Import list_utils wf_utils bt zip sorted increase bft.

Set Implicit Arguments.

Section bt_branches.

  Variable X : Type.

  Implicit Types (l : list bool) (ll: list(list bool)) (t : bt X).

  (* Depth first traversal, VERY standard algo *)

  Fixpoint dft_std t : list X :=
    match t with 
      | leaf x => x::nil
      | node u x v => x::dft_std u++dft_std v
    end.

  Fact dft_std_length t : length (dft_std t) = m_bt t.
  Proof. induction t; simpl; repeat rewrite app_length; omega. Qed.

  (* The tree branches by Depth First Traversal *)

  Fixpoint dft_br t : list (list bool) :=
    nil::match t with 
           | leaf _     => nil
           | node u _ v => map (cons false) (dft_br u) ++ map (cons true) (dft_br v)
         end.

  (* dft_br corresponds to dft_std *)

  Theorem dft_br_std t : Forall2 (bt_path_node t) (dft_br t) (dft_std t).
  Proof.
    induction t as [ | ? Hu ? ? Hv ]; simpl; repeat constructor.
    apply Forall2_app; apply Forall2_map_left; [ revert Hu | revert Hv ];
      apply Forall2_mono; constructor; auto.
  Qed.

  (* number of branches equals size of tree *)

  Fact dft_br_length t : length (dft_br t) = m_bt t.
  Proof. rewrite (Forall2_length (dft_br_std t)), dft_std_length; trivial. Qed.

  (* dft_br lists the branches of t *)

  Fact dft_br_spec l t : In l (dft_br t) <-> btb t l.
  Proof.
    split.
    + intros Hl; rewrite btb_spec.
      destruct Forall2_In_inv_left with (1 := dft_br_std t) (2 := Hl) as (x & ? & ?).
      exists x; auto.
    + induction 1 as [ [] | | ]; simpl; auto; right; apply in_or_app;
        [ left | right ]; apply in_map; auto.
   Qed.

  Corollary dft_br_spec_1 t : Forall (btb t) (dft_br t).
  Proof. rewrite Forall_forall; intro; apply dft_br_spec. Qed.

  (* the branches of t in dft_br t are sorted according to lb_lex *)

  Fact dft_br_sorted t : sorted lb_lex (dft_br t).
  Proof.
    induction t; simpl.
    + do 2 constructor.
    + constructor.
      * apply Forall_app; rewrite Forall_forall; intro; 
          rewrite in_map_iff; intros (? & ? & ?); subst; constructor.
      * apply sorted_app.
        - intros ? ?; do 2 rewrite in_map_iff.
          intros (? & ? & ?) (? & ? & ?); subst; constructor.
        - apply sorted_map; auto; constructor; auto.
        - apply sorted_map; auto; constructor; auto.
  Qed.

  (* Now niveaux and then Breadth first traversal *)

  Fixpoint niveaux_br (t : bt X) : list (list (list bool)) :=
    match t with 
      | leaf _     => (nil::nil) :: nil
      | node a _ b => (nil::nil) :: zip (@app _) (map (map (cons false)) (niveaux_br a))
                                                 (map (map (cons true))  (niveaux_br b))
    end.

  Lemma niveaux_br_niveaux t : Forall2 (Forall2 (bt_path_node t)) (niveaux_br t) (niveaux t).
  Proof.
    induction t as [ | ? Hu ? ? Hv ]; simpl; repeat constructor.
    apply Forall2_zip_app; apply Forall2_map_left;
      [ revert Hu | revert Hv ]; apply Forall2_mono;
      intros ? ? G; apply Forall2_map_left; revert G;
      apply Forall2_mono; constructor; auto.
  Qed.

  Lemma niveaux_br_spec_0 l t : btb t l -> In l (concat (niveaux_br t)).
  Proof.
    induction 1 as [ t | | ].
    + apply in_concat_iff; exists (nil::nil); destruct t; simpl; auto.
    + simpl; right; apply In_concat_zip_app_left; rewrite <- map_concat; apply in_map; assumption.
    + simpl; right; apply In_concat_zip_app_right; rewrite <- map_concat; apply in_map; assumption.
  Qed. 

  Corollary niveaux_br_spec_1 t : forall l ll, In l ll -> In ll (niveaux_br t) -> btb t l.
  Proof.
    intros l ll H1 H2.
    destruct Forall2_In_inv_left with (1 := niveaux_br_niveaux t) (2 := H2) as (? & ? & H3).
    destruct Forall2_In_inv_left with (1 := H3) (2 := H1) as (? & ? & ?).
    apply btb_spec; firstorder.
  Qed.
  
  Fact niveaux_br_increase t : increase (fun n ll => Forall (fun l => length l = n) ll) 0 (niveaux_br t).
  Proof.
    induction t as [ | u Hu x v Hv ]; simpl.
    + do 2 constructor; auto.
    + constructor.
      * constructor; auto.
      * apply zip_increase.
        1: intros; apply Forall_app; auto.
        1,2 : apply map_increase; try assumption; 
            intros ? ? G; apply Forall_map; simpl;
            revert G; apply Forall_impl; intros; omega.
  Qed.

  Fact niveaux_br_sorted t : Forall (sorted lb_lex) (niveaux_br t).
  Proof.
    induction t as [ x | u Hu x v Hv ]; simpl.
    + repeat constructor.
    + constructor.
      * repeat constructor.
      * apply zip_monotone.
        - apply Forall_map; revert Hu; apply Forall_impl.
          intros; apply sorted_map; auto.
          intros; constructor; auto.
        - apply Forall_map; revert Hv; apply Forall_impl.
          intros; apply sorted_map; auto.
          intros; constructor; auto.
        - rewrite Forall_forall in Hu, Hv.
          intros ? ?; do 2 rewrite in_map_iff;
            intros (? & ? & ?) (? & ? & ?); subst.
          apply sorted_app.
          ++ intros ? ?; do 2 rewrite in_map_iff;
             intros (? & ? & ?) (? & ? & ?); subst; constructor.
          ++ apply sorted_map; auto; intros; constructor; auto.
          ++ apply sorted_map; auto; intros; constructor; auto.
  Qed.

  Definition bft_br t : list (list bool) := concat (niveaux_br t).

  (* bft_br corresponds to bft_std *)

  Theorem bft_br_std t : Forall2 (bt_path_node t) (bft_br t) (bft_std t).
  Proof. apply Forall2_concat, niveaux_br_niveaux. Qed.

  (* bft_br contains the branches of t *)

  Fact bft_br_spec l t : In l (bft_br t) <-> btb t l.
  Proof.
    unfold bft_br; split.
    + rewrite in_concat_iff; intros (? & H1 & H2); revert H1 H2; apply niveaux_br_spec_1.
    + apply niveaux_br_spec_0.
  Qed.

  Hint Resolve niveaux_br_increase niveaux_br_sorted.

  (* The list of branches generated by bft_br is sorted according to bft_order *)

  Theorem bft_br_sorted t : sorted bft_order (bft_br t).
  Proof.
    apply concat_sorted with (P := fun n ll => Forall (fun l => length l = n) ll) (n := 0); auto.
    + intros i j x l y m; do 2 rewrite Forall_forall; intros H1 H2 H3 H4 H5.
      apply H2 in H4; apply H3 in H5; left; omega.
    + generalize (niveaux_br_sorted t).
      do 2 rewrite Forall_forall.
      intros H l Hl; generalize (H _ Hl).
      apply sorted_mono.
      intros x y H1 H2 H3; right; split; auto.
      generalize (niveaux_br_increase t); intros H4.
      apply increase_inv with (2 := Hl) in H4.
      destruct H4 as (k & _ & H4).
      rewrite Forall_forall in H4.
      repeat rewrite H4; auto.
  Qed.

  Hint Resolve dft_br_sorted bft_br_sorted lb_lex_irrefl bft_order_irrefl.

  (* dft_br and bft_br compute the same list of branches ... up to permutation *)

  Theorem bft_br_dft_br t : dft_br t ~p bft_br t.
  Proof.
    apply sorted_perm with (R := lb_lex) (S := bft_order); auto.
    intro; rewrite dft_br_spec, bft_br_spec; tauto.
  Qed.

  Corollary bft_br_length t : length (bft_br t) = m_bt t.
  Proof. rewrite <- (Permutation_length (bft_br_dft_br t)); apply dft_br_length. Qed. 

  Corollary bft_std_length t : length (bft_std t) = m_bt t.
  Proof.
    generalize (bft_br_std t); intros H.
    apply Forall2_length in H.
    rewrite <- H, bft_br_length; trivial.
  Qed.

End bt_branches.

Check dft_br_spec.
Check dft_br_length.
Check dft_br_sorted.
Check dft_br_std.

Check bft_br_spec.
Check bft_br_length.
Check bft_br_sorted.
Check bft_br_std.

Check bft_br_dft_br.