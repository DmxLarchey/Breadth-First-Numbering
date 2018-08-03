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

Section sorted.

  Variable (X : Type) (R : X -> X -> Prop).

  Inductive sorted : list X -> Prop :=
    | in_sorted_0 : sorted nil
    | in_sorted_1 : forall x l, Forall (R x) l -> sorted l -> sorted (x::l).

  Fact sorted_app l m : (forall x y, In x l -> In y m -> R x y) -> sorted l -> sorted m -> sorted (l++m).
  Proof.
    intros H H1 Hm; revert H1 H.
    induction 1 as [ | x l H1 H2 IH2 ]; intros H3; simpl; auto.
    constructor.
    + apply Forall_app; auto.
      apply Forall_forall; intros; apply H3; simpl; auto.
    + apply IH2; intros; apply H3; simpl; auto.
  Qed.

End sorted.

Section increase.
 
  Variable (X : Type) (P : nat -> X -> Prop).

  Inductive increase : nat -> list X -> Prop :=
    | in_increase_0 : forall n, increase n nil
    | in_increase_1 : forall n x l, P n x -> increase (S n) l -> increase n (x::l).

  Section zip.

     Variable (f : X -> X -> X) (Hf : forall n x y, P n x -> P n y -> P n (f x y)).

     Fact zip_increase l m n : increase n l -> increase n m -> increase n (zip f l m).
     Proof.
       intros H; revert H m.
       induction 1 as [ n | n x l H1 H2 IH2 ]; simpl; intros m Hm; auto.
       destruct m as [ | y m ]; simpl.
       * constructor; auto.
       * constructor; inversion Hm; auto.
     Qed.

  End zip.

  Section map.

    Variable (f : X -> X) (Hf : forall n x, P n x -> P (S n) (f x)).

    Fact map_increase n l : increase n l -> increase (S n) (map f l).
    Proof. induction 1; simpl; constructor; auto. Qed.

  End map.

End increase.

Section bt_branches.

  Variable X : Type.

  Unset Elimination Schemes.

  Inductive btb : list bool -> bt X -> Prop :=
    | in_btb_0 : forall t, btb nil t
    | in_btb_1 : forall l u x v, btb l u -> btb (false::l) (node u x v)
    | in_btb_2 : forall l u x v, btb l v -> btb (true::l)  (node u x v).

  Set Elimination Schemes.

  Scheme btb_ind := Induction for btb Sort Prop.

  Hint Constructors btb.

  Fact btb_inv_1 l u x v : btb (false::l) (node u x v) -> btb l u.
  Proof. inversion 1; trivial. Defined.

  Fact btb_inv_2 l u x v : btb (true::l) (node u x v) -> btb l v.
  Proof. inversion 1; trivial. Defined.

  Hint Resolve btb_inv_1  btb_inv_2.

  Fixpoint btb_node l t (D : btb l t) { struct l } : X.
  Proof.
    refine (match l as l' return l = l' -> _ with
      | nil   => fun _ => root t
      | b::l' => match t as t' return t = t' -> _ with 
        | leaf _     => fun E1 E2 => _
        | node u _ v => fun E1 E2 => btb_node l' (if b then v else u) _
      end eq_refl
    end eq_refl).
    + exfalso; subst; inversion D.
    + subst; destruct b; revert D; (apply btb_inv_1 || apply btb_inv_2).
  Defined.

  Arguments btb_node : clear implicits.
 
  Fact btbn_fix_0 t D : btb_node nil t D = root t.
  Proof. auto. Qed.

  Fact btbn_fix_1 l u x v D : btb_node (false::l) (node u x v) D = btb_node l u (btb_inv_1 D).
  Proof. auto. Qed.

  Fact btbn_fix_2 l u x v D : btb_node (true::l) (node u x v) D = btb_node l v (btb_inv_2 D).
  Proof. auto. Qed.

  (* The tree branches by Depth First Search *)

  Fixpoint dfs_br (t : bt X) : list (list bool) :=
    nil::match t with 
           | leaf _     => nil
           | node u _ v => map (cons false) (dfs_br u) ++ map (cons true) (dfs_br v)
         end.

  (* branches t included in btb _ t *)

  Fact dfs_br_spec_1 t : Forall (fun l => btb l t) (dfs_br t).
  Proof.
    induction t as [ x | u Hu x v Hv ].
    + do 2 constructor.
    + simpl; constructor.
      * constructor.
      * apply Forall_app; apply Forall_map; [ revert Hu | revert Hv ]; 
          apply Forall_impl; auto.
  Qed.

  (* number of branches equals size of tree *)

  Fact dfs_br_spec_2 t : length (dfs_br t) = m_bt t.
  Proof. induction t; simpl; auto; rewrite app_length; repeat rewrite map_length; omega. Qed.

  Fixpoint in_bt (x : X) t :=
    match t with
      | leaf y => x = y
      | node u y v => x = y \/ in_bt x u \/ in_bt x v
    end.

  (* each node corresponding to a branch is in the tree *)

  Fact btbn_spec l t D : in_bt (btb_node l t D) t.
  Proof.
    revert t D.
    induction l as [ | [] ]; intros [|] D; 
      try (simpl; auto; fail); inversion D.
  Qed.

  (* each value in a tree corresponds to some node of a branch *)

  Fact in_bt_inv x t : in_bt x t -> exists l D, x = btb_node l t D.
  Proof.
    induction t as [ y | u Hu y v Hv ]; simpl.
    + intros []; exists nil, (in_btb_0 _); auto.
    + intros [ [] | [ H | H ] ].
      - exists nil, (in_btb_0 _); auto.
      - destruct (Hu H) as (l & D & H1); subst.
        exists (false::l), (in_btb_1 _ _ D); auto.
      - destruct (Hv H) as (l & D & H1); subst.
        exists (true::l), (in_btb_2 _ _ D); auto.
  Qed.

  Inductive lb_lex : list bool -> list bool -> Prop :=
    | in_lb_0 : forall l, lb_lex nil l
    | in_lb_1 : forall l m, lb_lex (false::l) (true::m)
    | in_lb_2 : forall b l m, lb_lex l m -> lb_lex (b::l) (b::m).

  Fact lb_lex_refl l : lb_lex l l.
  Proof. induction l; constructor; auto. Qed.

  Fact lb_lex_trans l m k : lb_lex l m -> lb_lex m k -> lb_lex l k.
  Proof.
    intros H; revert H k.
    induction 1 as [ l | l m | b l m H IH ]; intros k H1.
    + constructor.
    + inversion H1; constructor.
    + inversion H1; constructor; auto.
  Qed.

  Fact lb_lex_antisym l m : lb_lex l m -> lb_lex m l -> l = m.
  Proof. induction 1; inversion 1; f_equal; auto. Qed.

  Definition lb_lex_dec l m : { lb_lex l m } + { lb_lex m l }.
  Proof.
    revert m; induction l as [ | [] l IHl ]; intros m.
    + left; constructor.
    + destruct m as [ | [] m ].
      * right; constructor.
      * destruct (IHl m); [ left | right ]; constructor; auto.
      * right; constructor.
    + destruct m as [ | [] m ].
      * right; constructor.
      * left; constructor.
      * destruct (IHl m); [ left | right ]; constructor; auto.
  Qed.

  (* The Breadth First Search order between bt branches *)

  Definition bft_order l m := length l < length m \/ length l = length m /\ lb_lex l m.

  Fact bft_order_refl l : bft_order l l.
  Proof. right; split; auto; apply lb_lex_refl. Qed.

  Fact bft_order_antisym l m :  bft_order l m ->  bft_order m l -> l = m.
  Proof.
    intros [ | [] ] [ | [] ]; try omega.
    apply lb_lex_antisym; auto.
  Qed.

  Fact bft_order_trans l m k : bft_order l m -> bft_order m k -> bft_order l k.
  Proof.
    intros [ | [] ] [ | [] ]; try (left; omega).
    right; split; try omega.
    apply lb_lex_trans with m; auto.
  Qed.
 
  Definition bft_order_dec l m : { bft_order l m } + { bft_order m l }.
  Proof.
    destruct (le_lt_dec (length l) (length m)).
    2: right; left; auto.
    destruct (le_lt_dec (length m) (length l)).
    2: left; left; auto.
    destruct (lb_lex_dec l m).
    * left; right; split; auto; omega.
    * right; right; split; auto; omega.
  Qed.

  Fixpoint niveaux_br (t : bt X) : list (list (list bool)) :=
    match t with 
      | leaf _     => (nil::nil) :: nil
      | node a _ b => (nil::nil) :: zip (@app _) (map (map (cons false)) (niveaux_br a))
                                                 (map (map (cons true))  (niveaux_br b))
    end.

  Fact niveaux_br_spec_1 t : forall l ll, In l ll -> In ll (niveaux_br t) -> btb l t.
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
      * 
  Admitted. 

  Definition bft_br t : list (list bool) := concat (niveaux_br t).

  Fact bft_br_spec_1 t : forall l, In l (bft_br t) -> btb l t.
  Proof.
    unfold bft_br; intros l; rewrite in_concat_iff.
    intros (ll & H1 & H2); apply niveaux_br_spec_1 with ll; auto.
  Qed.

  Fixpoint list_in_map U V (P : U -> Prop) (f : forall u, P u -> V) (l : list U) : 
               (forall x, In x l -> P x) -> list V.
  Proof.
    refine (match l with
      | nil  => fun _ => nil
      | x::l => fun H => f x _ :: @list_in_map _ _ P f l _
    end).
    + intros; apply H; left; trivial.
    + intros; apply H; right; trivial.
  Defined.
 
  Fact bft_br_spec_2 t : bft_std t = list_in_map _ (fun l H => btb_node l t H) _ (bft_br_spec_1 t).
  Proof.
    unfold bft_std.
    induction t; simpl; auto; f_equal.
    
    SearchAbout [ flat_map ].



  

 




  
End bt_branches.