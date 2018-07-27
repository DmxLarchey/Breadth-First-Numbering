(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** Binary trees *)

Require Import List.

Set Implicit Arguments.

Section bt.

  Variable X : Type.

  Inductive bt := leaf : X -> bt | node : bt -> X -> bt -> bt.

  Definition root t :=
    match t with 
      | leaf x     => x
      | node _ x _ => x
    end.

  Fixpoint m_bt t :=
    match t with 
      | leaf _     => 1
      | node a _ b => 1 + m_bt a + m_bt b
    end.

End bt.

Arguments root {X}.
Arguments m_bt {X}.

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
