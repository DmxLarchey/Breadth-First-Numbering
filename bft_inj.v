(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega Wellfounded Permutation.
Require Import list_utils wf_utils bt bft.

Set Implicit Arguments.

Section bft_inj.

  Variable X : Type.

  Implicit Types (l : list (bt X)) (t : bt X).

  Theorem bft_f_inj l m : l ~lt m -> bft_f l = bft_f m -> l = m.
  Proof.
    induction on l m as IH with measure (lsum (l++m)).
    revert l m IH; intros [ | t1 l ] [ | t2 m ] IH H; try (inversion H; fail); auto.
    Forall2 inv H as H12.
    repeat rewrite bft_f_fix_3.
    destruct t1 as [ x | a1 x b1 ]; destruct t2 as [ y | a2 y b2 ]; try (inversion H12; fail); simpl.
    + intros E; inversion E; f_equal.
      repeat rewrite <- app_nil_end in *.
      apply IH; auto.
      repeat rewrite lsum_app; simpl; omega.
    + apply bt_eq_node_inv in H12; destruct H12 as [ Ha Hb ].
      intros E; injection E; clear E; intros E ?; subst.
      apply IH in E.
      * apply f_equal with (f := @rev _) in E.
        repeat rewrite rev_app_distr in E; simpl in E.
        inversion E; subst; f_equal.
        rewrite <- (rev_involutive l), <- (rev_involutive m).
        f_equal; trivial.
      * repeat rewrite lsum_app; simpl; omega.
      * apply Forall2_app; auto.
  Qed.

  Corollary bft_inj t1 t2 : t1 ~t t2 -> bft t1 = bft t2 -> t1 = t2.
  Proof.
    unfold bft.
    intros H1 H2. 
    apply bft_f_inj in H2; auto.
    inversion H2; auto.
  Qed.

  Corollary bft_std_inj t1 t2 : t1 ~t t2 -> bft_std t1 = bft_std t2 -> t1 = t2.
  Proof. do 2 rewrite <- bft_std_eq_bft; apply bft_inj. Qed.

End bft_inj.