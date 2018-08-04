(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)


Require Import List Arith Omega Wellfounded.
Require Import utils bt bft.

Set Implicit Arguments.

Section bt_branches.

  Variable X : Type.

  (* The tree branches by Depth First Traversal *)

  Fixpoint dft_std (t : bt X) :=
    match t with 
      | leaf x => x::nil
      | node u x v => x::dft_std u++dft_std v
    end.

  Fixpoint dft_br (t : bt X) : list (list bool) :=
    nil::match t with 
           | leaf _     => nil
           | node u _ v => map (cons false) (dft_br u) ++ map (cons true) (dft_br v)
         end.

  (* branches t included in btb _ t *)

  Fact dft_br_spec_1 t : Forall (btb t) (dft_br t).
  Proof.
    induction t as [ x | u Hu x v Hv ].
    + do 2 constructor.
    + simpl; constructor.
      * constructor.
      * apply Forall_app; apply Forall_map; [ revert Hu | revert Hv ]; 
          apply Forall_impl; auto.
  Qed.

  (* dft_br contains the branches of t *)

  Fact dft_br_spec l t : btb t l <-> In l (dft_br t).
  Proof.
    split.
    + induction 1 as [ t | l u x v H IH | m u x v H IH ]; simpl.
      * destruct t; simpl; auto.
      * right; apply in_or_app; left; apply in_map; auto.
      * right; apply in_or_app; right; apply in_map; auto.
    + revert l; apply Forall_forall, dft_br_spec_1.
  Qed.

  (* number of branches equals size of tree *)

  Fact dft_br_spec_2 t : length (dft_br t) = m_bt t.
  Proof. induction t; simpl; auto; rewrite app_length; repeat rewrite map_length; omega. Qed.

  (* the branches of t in dft_br t are sorted according to lb_lex *)

  Fact dft_br_spec_3 t : sorted lb_lex (dft_br t).
  Proof.
    induction t as [ x | u Hu x v Hv ]; simpl.
    + do 2 constructor.
    + constructor.
      * apply Forall_app; rewrite Forall_forall; intros y; rewrite in_map_iff; intros (z & ? & H); subst y; constructor.
      * apply sorted_app.
        - intros a b; do 2 rewrite in_map_iff.
          intros (r & ? & H1) (s & ? & H2); subst a b; constructor.
        - apply sorted_map; auto; constructor; auto.
        - apply sorted_map; auto; constructor; auto.
  Qed.

  (* dft_br corresponds to dft_std *)

  Fact dft_br_spec_4 t : Forall2 (bt_path_node t) (dft_br t) (dft_std t).
  Proof.
    induction t as [ x | u Hu x v Hv ]; simpl; repeat constructor.
    apply Forall2_app; apply Forall2_map_left; [ revert Hu | revert Hv ];
      apply Forall2_mono; constructor; auto.
  Qed.

  Fixpoint niveaux_br (t : bt X) : list (list (list bool)) :=
    match t with 
      | leaf _     => (nil::nil) :: nil
      | node a _ b => (nil::nil) :: zip (@app _) (map (map (cons false)) (niveaux_br a))
                                                 (map (map (cons true))  (niveaux_br b))
    end.

  Fact niveaux_br_spec_1 t : forall l ll, In l ll -> In ll (niveaux_br t) -> btb t l.
  Proof.
    induction t as [ x | u Hu x v Hv ]; simpl; intros l ll H1 H2.
    * destruct H2 as [ | [] ]; subst.
      destruct H1 as [ | [] ]; subst; constructor.
    * destruct H2 as [ | H2 ]; subst.
      + destruct H1 as [ | [] ]; subst; constructor.
      + rewrite zip_spec in H2.
        destruct H2 as [ (m1 & m2 & _ & H3)
                     | [ (m1 & m2 & _ & H3) 
                       | (l1 & a & l2 & m1 & b & m2 & H2 & H3 & H4 & H5) ] ].
        - apply split_In, in_map_iff in H3.
          destruct H3 as (ll1 & H3 & H4); subst.
          apply in_map_iff in H1.
          destruct H1 as (l1 & ? & H1); subst.
          constructor; apply Hv with (2 := H4); auto.
        - apply split_In, in_map_iff in H3.
          destruct H3 as (ll1 & H3 & H4); subst.
          apply in_map_iff in H1.
          destruct H1 as (l1 & ? & H1); subst.
          constructor; apply Hu with (2 := H4); auto.
        - apply split_In, in_map_iff in H3.
          apply split_In, in_map_iff in H4.
          destruct H3 as (ll1 & ? & H3); subst.
          destruct H4 as (ll2 & ? & H4); subst.
          apply in_app_or in H1.
          destruct H1 as [ H1 | H1 ]; apply in_map_iff in H1;
            destruct H1 as (l3 & ? & H1); subst.
          ** constructor; apply Hu with (2 := H3); auto.
          ** constructor; apply Hv with (2 := H4); auto.
  Qed.

  Fact niveaux_br_spec_0 l t : btb t l -> exists ll, In l ll /\ In ll (niveaux_br t).
  Proof.
    induction 1 as [ t | l u x v H (ll & H1 & H2) | m u x v H (mm & H1 & H2) ].
    + exists (nil::nil); destruct t; simpl; auto.
    + apply in_split in H2.
      destruct H2 as (u1 & u2 & H2).
      destruct (list_length_split (length u1) (niveaux_br v))
        as [ (v1 & [ | mm v2 ] & H3 & H4) | H3 ].
      - exists (map (cons false) ll); simpl; split.
        * apply in_map_iff; exists l; auto.
        * right; apply zip_spec.
          right; left; exists (map (map (cons false)) u1), (map (map (cons false)) u2).
          repeat rewrite map_length.
          rewrite H2, map_app, H3, <- app_nil_end, H4; simpl; auto.
      - exists (map (cons false) ll++map (cons true) mm); simpl; split.
        * apply in_or_app; left; apply in_map_iff; exists l; auto.
        * right; apply zip_spec; right; right.
          exists (map (map (cons false)) u1), (map (cons false) ll), (map (map (cons false)) u2),
                 (map (map (cons true)) v1), (map (cons true) mm), (map (map (cons true)) v2); repeat split; auto.
          ++ rewrite H2, map_app; auto.
          ++ rewrite H3, map_app; auto.
          ++ rewrite map_length, map_length; auto.
      - exists  (map (cons false) ll); simpl; split.
        * apply in_map_iff; exists l; auto.
        * right; rewrite H2, map_app; apply zip_app_left.
          ++ do 2 rewrite map_length; auto.
          ++ apply in_map; simpl; auto.
    + apply in_split in H2.
      destruct H2 as (v1 & v2 & H2).
      destruct (list_length_split (length v1) (niveaux_br u))
        as [ (u1 & [ | ll u2 ] & H3 & H4) | H3 ].
      - exists (map (cons true) mm); simpl; split.
        * apply in_map_iff; exists m; auto.
        * right; apply zip_spec.
          left; exists (map (map (cons true)) v1), (map (map (cons true)) v2).
          repeat rewrite map_length.
          rewrite H2, map_app, H3, <- app_nil_end, H4; simpl; auto.
      - exists (map (cons false) ll++map (cons true) mm); simpl; split.
        * apply in_or_app; right; apply in_map_iff; exists m; auto.
        * right; apply zip_spec; right; right.
          exists (map (map (cons false)) u1), (map (cons false) ll), (map (map (cons false)) u2),
                 (map (map (cons true)) v1), (map (cons true) mm), (map (map (cons true)) v2); repeat split; auto.
          ++ rewrite H3, map_app; auto.
          ++ rewrite H2, map_app; auto.
          ++ rewrite map_length, map_length; auto.
      - exists  (map (cons true) mm); simpl; split.
        * apply in_map_iff; exists m; auto.
        * right; rewrite H2, map_app; apply zip_app_right.
          ++ do 2 rewrite map_length; auto.
          ++ apply in_map; simpl; auto.
  Qed.

  Fact niveaux_br_spec l t : btb t l <-> exists ll, In l ll /\ In ll (niveaux_br t).
  Proof.
    split.
    + apply niveaux_br_spec_0.
    + intros (ll & H1 & H2); revert H1 H2; apply niveaux_br_spec_1.
  Qed.
  
  Fact niveaux_br_spec_2 t : increase (fun n ll => Forall (fun l => length l = n) ll) 0 (niveaux_br t).
  Proof.
    induction t as [ x | u Hu x v Hv ]; simpl.
    + do 2 constructor; auto.
    + constructor.
      * constructor; auto.
      * apply zip_increase.
        - intros; apply Forall_app; auto.
        - apply map_increase; auto. 
          intros l ll H; apply Forall_map; simpl.
          revert H; apply Forall_impl; intros; omega.
        - apply map_increase; auto. 
          intros l ll H; apply Forall_map; simpl.
          revert H; apply Forall_impl; intros; omega.
  Qed.

  Fact niveaux_br_spec_3 t : Forall (sorted lb_lex) (niveaux_br t).
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
          intros ? ?; do 2 rewrite in_map_iff.
          intros (l & ? & H1) (m & ? & H2); subst.
          apply sorted_app.
          ++ intros c d; do 2 rewrite in_map_iff.
             intros (r & ? & ?) (s & ? & ?); subst; constructor.
          ++ apply sorted_map; auto.
             intros; constructor; auto.
          ++ apply sorted_map; auto.
             intros; constructor; auto.
  Qed. 

  Definition bft_br t : list (list bool) := concat (niveaux_br t).

  (* bft_br contains the branches of t *)

  Fact bft_br_spec_1 l t : In l (bft_br t) <-> btb t l.
  Proof. unfold bft_br; rewrite niveaux_br_spec, in_concat_iff; tauto. Qed.
 
  Hint Resolve niveaux_br_spec_2.

  (* The list of branches generated by bft_br is sorted according to bft_order *)

  Theorem bft_br_spec_2 t : sorted bft_order (bft_br t).
  Proof.
    apply concat_sorted with (P := fun n ll => Forall (fun l => length l = n) ll) (n := 0); auto.
    + intros i j x l y m; do 2 rewrite Forall_forall; intros H1 H2 H3 H4 H5.
      apply H2 in H4; apply H3 in H5.
      left; omega.
    + generalize (niveaux_br_spec_3 t).
      do 2 rewrite Forall_forall.
      intros H l Hl; generalize (H _ Hl).
      apply sorted_mono.
      intros x y H1 H2 H3; right; split; auto.
      generalize (niveaux_br_spec_2 t); intros H4.
      apply increase_inv with (2 := Hl) in H4.
      destruct H4 as (k & _ & H4).
      rewrite Forall_forall in H4.
      repeat rewrite H4; auto.
  Qed.

  Fixpoint in_bt (x : X) t :=
    match t with
      | leaf y => x = y
      | node u y v => x = y \/ in_bt x u \/ in_bt x v
    end.

  Hint Resolve btb_inv_1  btb_inv_2.

  Fixpoint btb_node (l : list bool) t : option X :=
    match l with
      | nil  => Some (root t)
      | b::l => match t with 
        | leaf _     => None
        | node u _ v => btb_node l (if b then v else u)
      end
    end.

  Fact btbn_fix_0 t : btb_node nil t = Some (root t).
  Proof. auto. Qed.

  Fact btbn_fix_1 b l x : btb_node (b::l) (leaf x) = None.
  Proof. auto. Qed.

  Fact btbn_fix_2 l u x v : btb_node (false::l) (node u x v) = btb_node l u.
  Proof. auto. Qed.

  Fact btbn_fix_3 l u x v : btb_node (true::l) (node u x v) = btb_node l v.
  Proof. auto. Qed.

  (* each node corresponding to a branch is in the tree *)

  Fact btbn_spec l t x : btb_node l t = Some x -> in_bt x t.
  Proof.
    revert t x.
    induction l as [ | [] ]; intros [|] ?; simpl; try discriminate.
    + inversion 1; auto.
    + inversion 1; auto.
    + intros G; apply IHl in G; tauto.
    + intros G; apply IHl in G; tauto.
  Qed.

  (* each value in a tree corresponds to some node of a branch *)

  Fact in_bt_inv x t : in_bt x t -> exists l, btb_node l t = Some x.
  Proof.
    induction t as [ y | u Hu y v Hv ]; simpl.
    + intros []; exists nil; auto.
    + intros [ [] | [ H | H ] ].
      - exists nil; auto.
      - destruct (Hu H) as (l & H1); subst; exists (false::l); auto.
      - destruct (Hv H) as (l & H1); subst; exists (true::l); auto.
  Qed.

  Fact niveaux_br_spec_4 t : map (map (@Some _)) (niveaux_tree t) = map (map (fun l => btb_node l t)) (niveaux_br t).
  Proof.
    induction t as [ x | u Hu x v Hv ]; simpl; f_equal; auto.
    rewrite map_zip with (h := @app _).
    2: intros; apply map_app.
    rewrite map_zip with (h := @app _).
    2: intros; apply map_app.
    rewrite Hu, Hv; repeat rewrite map_map; f_equal;
    apply map_ext; intros; rewrite map_map; apply map_ext; intros; simpl; auto.
  Qed.

  Fact niveaux_br_spec_5 t : Forall2 (Forall2 (bt_path_node t)) (niveaux_br t) (niveaux_tree t).
  Proof.
    induction t as [ x | u Hu x v Hv ]; simpl; repeat constructor.
    apply Forall2_zip_app; apply Forall2_map_left.
    + revert Hu; apply Forall2_mono.
      intros ? ? H; apply Forall2_map_left; revert H.
      apply Forall2_mono; constructor; auto.
    + revert Hv; apply Forall2_mono.
      intros ? ? H; apply Forall2_map_left; revert H.
      apply Forall2_mono; constructor; auto.
  Qed.

  (* The list of nodes computed by bft_std is the direct map of the sorted list of branches,
     according to the bft_order *)

  Theorem bft_br_spec_3 t : map (@Some _) (bft_std t) = map (fun l => btb_node l t) (bft_br t).
  Proof. unfold bft_std, bft_br; rewrite map_concat, map_concat, niveaux_br_spec_4; auto. Qed.

  (* bft_br corresponds to bft_std *)

  Theorem bft_br_spec_4 t : Forall2 (bt_path_node t) (bft_br t) (bft_std t).
  Proof. apply Forall2_concat, niveaux_br_spec_5. Qed.
 
End bt_branches.

Check dft_br_spec.
Check dft_br_spec_3.
Check dft_br_spec_4.

Check bft_br_spec_1.
Check bft_br_spec_2.
Check bft_br_spec_4.