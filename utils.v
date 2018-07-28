(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

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

  Fact Forall2_rev l m : Forall2 R l m -> Forall2 R (rev l) (rev m).
  Proof. induction 1; simpl; auto; apply Forall2_app; simpl; auto. Qed.
 
  Fact Forall2_app_inv l1 l2 m1 m2 : length l1 = length m1
                                  -> Forall2 R (l1++l2) (m1++m2)
                                  -> Forall2 R l1 m1 /\ Forall2 R l2 m2.
  Proof.
    revert m1; induction l1 as [ | x l1 IH ]; intros [ | y m1 ]; 
      try discriminate; simpl; intros H1 H2; auto.
    apply Forall2_cons_inv in H2.
    destruct H2; destruct (IH m1); auto.
  Qed.

  Fact Forall2_snoc_inv l x m y : Forall2 R (l++x::nil) (m++y::nil) -> R x y /\ Forall2 R l m.
  Proof.
    intros H.
    apply Forall2_rev in H.
    rewrite rev_app_distr, rev_app_distr in H; simpl in H.
    apply Forall2_cons_inv in H; destruct H as [ H1 H ]; split; auto.
    rewrite <- (rev_involutive l), <- (rev_involutive m); apply Forall2_rev; auto.
  Qed.

  Fact Forall2_2snoc_inv l a b m u v : Forall2 R (l++a::b::nil) (m++u::v::nil) 
                                    -> R a u /\ R b v /\ Forall2 R l m.
  Proof.
    replace (l++a::b::nil) with ((l++a::nil)++b::nil) by (rewrite app_ass; auto).
    replace (m++u::v::nil) with ((m++u::nil)++v::nil) by (rewrite app_ass; auto).
    intros H.
    apply Forall2_snoc_inv in H; destruct H as (H1 & H).
    apply Forall2_snoc_inv in H; tauto.
  Qed.
   
End Forall2.

Tactic Notation "Forall2" "inv" hyp(H) "as" ident(E) :=
  match type of H with
    | Forall2 _ nil _ => apply Forall2_nil_inv_right in H; rename H into E
    | Forall2 _ (_::_) (_::_) => apply Forall2_cons_inv in H; destruct H as [ E H ]
    | Forall2 _ (_++_::nil) (_++_::nil) => apply Forall2_snoc_inv in H; destruct H as [ E H ]
    | Forall2 _ (_++_) (_++_) => apply Forall2_app_inv in H; [ destruct H as [ E H ] | ]
  end.
