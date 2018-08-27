(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** Binary trees *)

Require Import Arith Omega List.

Set Implicit Arguments.

Section bt.

  Variable X : Type.

  Inductive bt := leaf : X -> bt | node : bt -> X -> bt -> bt.

  Definition root t :=
    match t with 
      | leaf x     => x
      | node _ x _ => x
    end.

  (** measure: number of constructors *)
  Fixpoint m_bt t : nat :=
    match t with 
      | leaf _     => 1
      | node a _ b => 1 + m_bt a + m_bt b
    end.

  (* A branch is a list of left/right Boolean choices *)

  Unset Elimination Schemes.

  (* The branches that correspond to a node in a binary tree *)

  (** [false] for the left subtree, [true] for the right subtree *)
  Inductive btb : bt -> list bool -> Prop :=
    | in_btb_0 : forall t, btb t nil
    | in_btb_1 : forall l u x v, btb u l -> btb (node u x v) (false::l) 
    | in_btb_2 : forall l u x v, btb v l -> btb (node u x v) (true::l).

  Set Elimination Schemes.

  Scheme btb_ind := Induction for btb Sort Prop.

  Hint Constructors btb.

  Fact btb_inv_1 l u x v : btb (node u x v) (false::l) -> btb u l.
  Proof. inversion 1; trivial. Defined.

  Fact btb_inv_2 l u x v : btb (node u x v) (true::l) -> btb v l.
  Proof. inversion 1; trivial. Defined.

  (* The partial functional map from a branch to the value of that node *)

  Inductive bt_path_node : bt -> list bool -> X -> Prop :=
    | in_bpn_0 : forall t, bt_path_node t nil (root t)
    | in_bpn_1 : forall l u x v r, bt_path_node u l r -> bt_path_node (node u x v) (false::l) r
    | in_bpn_2 : forall l u x v r, bt_path_node v l r -> bt_path_node (node u x v) (true::l) r.

  Fact bt_path_node_fun t l x y :  bt_path_node t l x ->  bt_path_node t l y -> x = y.
  Proof. induction 1; inversion 1; auto. Qed.

  (* A branch has a value through bt_path_node iff it is a branch of the tree *)

  Fact btb_spec l t : btb t l <-> exists x, bt_path_node t l x.
  Proof.
    split.
    + induction 1 as [ t | l u x v _ (y & Hy) | l u x v _ (y & Hy) ].
      * exists (root t); constructor.
      * exists y; constructor; auto.
      * exists y; constructor; auto.
    + intros (r & H); revert H.
      induction 1; constructor; auto.
  Qed.

End bt.

Arguments root {X}.
Arguments m_bt {X}.

Hint Constructors btb.

Section branch_orders.

  (** We define two total and decidable strict orders on branches
        <l : for lexicographic order corresponding to DFT
        <b : for length then lexico corresponding to BFT

    *)

  Reserved Notation "x '<l' y" (at level 70, no associativity).
  Reserved Notation "x '<b' y" (at level 70, no associativity).

  (* The Depth First Traversal order between bt branches 

     The order is the lexicographic product where left (false)
     is less than right (true)

   *)

  Inductive lb_lex : list bool -> list bool -> Prop :=
    | in_lb_0 : forall b l, nil <l b::l
    | in_lb_1 : forall l m, false::l <l true::m
    | in_lb_2 : forall b l m, l <l m -> b::l <l b::m
  where "x <l y" := (lb_lex x y).

  Fact lb_lex_irrefl l : ~ l <l l.
  Proof. 
    assert (forall l m, l <l m -> l <> m) as H.
    { induction 1; try discriminate; inversion 1; tauto. }
    intros H1; apply (H _ _ H1); reflexivity.
  Qed.

  Fact lb_lex_trans l m k : l <l m -> m <l k -> l <l k.
  Proof.
    intros H; revert H k.
    induction 1; inversion 1; constructor; auto.
  Qed. 

  Definition lb_lex_dec l m : { l <l m } + { l = m } + { m <l l }.
  Proof.
    revert m; induction l as [ | [] l IHl ]; intros [ | [] m ].
    + tauto.
    + do 2 left; constructor.
    + do 2 left; constructor.
    + right; constructor.
    + destruct (IHl m) as [ [ ? | ? ] | ? ].
      * do 2 left; constructor; auto.
      * subst; left; right; auto.
      * right; constructor; auto.  
    + right; constructor.
    + right; constructor.
    + do 2 left; constructor.
    + destruct (IHl m) as [ [ ? | ? ] | ? ].
      * do 2 left; constructor; auto.
      * subst; left; right; auto.
      * right; constructor; auto.
   Qed.

  (* The Breadth First Traversal order between bt branches 

     Shorter branches are first and two branches of the 
     same length are sorted lexicographically 
 
   *)

  Definition bft_order l m := length l < length m 
                           \/ length l = length m /\ l <l m.

  Notation "l <b m" := (bft_order l m).

  Fact bft_order_irrefl l : ~ l <b l.
  Proof. 
    intros [ H | (_ & H) ]; revert H.
    + apply lt_irrefl.
    + apply lb_lex_irrefl.
  Qed.

  Fact bft_order_trans l m k : l <b m -> m <b k -> l <b k.
  Proof.
    intros [ | [] ] [ | [] ]; try (left; omega).
    right; split; try omega.
    apply lb_lex_trans with m; assumption.
  Qed.
 
  Definition bft_order_dec l m : { l <b m } + { l = m } + { m <b l }.
  Proof.
    destruct (le_lt_dec (length l) (length m)).
    2: right; left; auto.
    destruct (le_lt_dec (length m) (length l)).
    2: do 3 left; auto.
    destruct (lb_lex_dec l m) as [[|]|].
    + do 2 left; right; split; auto; omega.
    + tauto.
    + do 2 right; split; auto; omega.
  Qed.

End branch_orders.

(** Equivalence between trees and forests, same structure,
    only the values of nodes differ *)

Reserved Notation "x '~t' y" (at level 70, no associativity).
Reserved Notation "x '~lt' y" (at level 70, no associativity).

Section bt_eq.

  Variable (X Y : Type).

  Inductive bt_eq : bt X -> bt Y -> Prop :=
    | in_bt_eq_0 : forall x y, leaf x ~t leaf y
    | in_bt_eq_1 : forall x a b y c d, a ~t c -> b ~t d -> node a x b ~t node c y d
  where "x ~t y" := (bt_eq x y).

  Fact bt_eq_m t1 t2 : t1 ~t t2 -> m_bt t1 = m_bt t2.
  Proof. induction 1; simpl; f_equal; auto. Qed.

End bt_eq.

Arguments bt_eq {X Y}.

Notation "x ~t y" := (bt_eq x y).
Notation "l ~lt m" := (Forall2 bt_eq l m).

Hint Constructors bt_eq.


