(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega Wellfounded Extraction.

Set Implicit Arguments.

Section measure_rect.

  Variable (X : Type) (m : X -> nat) (P : X -> Type)
           (HP : forall x, (forall y, m y < m x -> P y) -> P x).

  Let R x y := m x < m y.

  Fact Acc_measure : well_founded R.
  Proof. unfold R; apply wf_inverse_image, lt_wf. Qed.

  Theorem measure_rect x : P x.
  Proof.
    cut (Acc R x).
    + revert x.
      exact (fix loop x Hx { struct Hx } := @HP x (fun y Hy => loop y (Acc_inv Hx Hy))).
    + apply Acc_measure.
  Qed.

End measure_rect.

Section measure_double_rect.

  Variable (X Y : Type) (m : X -> Y -> nat) (P : X -> Y -> Type)
           (HP : forall x y, (forall x' y', m x' y' < m x y -> P x' y') -> P x y).

  Let R c d := m (fst c) (snd c) < m (fst d) (snd d).

  Theorem measure_double_rect x y : P x y.
  Proof.
    cut (Acc R (x,y)).
    + revert x y.
      refine (fix loop x y H { struct H } := @HP x y (fun x' y' H' => loop x' y' (Acc_inv H _))).
      apply H'.
    + unfold R; apply wf_inverse_image, lt_wf.
  Qed.

End measure_double_rect.

Tactic Notation "measure" "induction" "on" hyp(x) "with" uconstr(f) :=
  pattern x; revert x; apply measure_rect with (m := fun x => f).

Tactic Notation "double" "measure" "induction" "on" hyp(x) hyp(y) "with" uconstr(f) :=
  pattern x, y; revert x y; apply measure_double_rect with (m := fun x y => f).

Extraction Inline measure_rect measure_double_rect.
