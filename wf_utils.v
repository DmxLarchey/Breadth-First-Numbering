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

  Variable (X : Type) (m : X -> nat) (P : X -> Type).

  Let R x y := m x < m y.

  Fact Acc_measure : well_founded R.
  Proof. unfold R; apply wf_inverse_image, lt_wf. Qed.

  Theorem measure_rect : 
        (forall x, (forall y, m y < m x -> P y) -> P x) 
     -> (forall x,                                 P x).
  Proof.
    intros HP x.
    cut (Acc R x).
    + revert x.
      exact (fix loop x Hx { struct Hx } := @HP x (fun y Hy => loop y (Acc_inv Hx Hy))).
    + apply Acc_measure.
  Defined.

End measure_rect.

Section measure_double_rect.

  Variable (X Y : Type) (m : X -> Y -> nat) (P : X -> Y -> Type).

  Let R c d := m (fst c) (snd c) < m (fst d) (snd d).

  Theorem measure_double_rect : 
        (forall x y, (forall x' y', m x' y' < m x y -> P x' y') -> P x y)
     -> (forall x y,                                               P x y).
  Proof.
    intros HP x y.
    cut (Acc R (x,y)).
    + revert x y.
      refine (fix loop x y H { struct H } := @HP x y (fun x' y' H' => loop x' y' (Acc_inv H _))).
      apply H'.
    + unfold R; apply wf_inverse_image, lt_wf.
  Defined.

End measure_double_rect.

(*
Tactic Notation "measure" "induction" "on" hyp(x) "with" uconstr(f) "as" ident(IH) :=
  pattern x; revert x; apply measure_rect with (m := fun x => f); intros x IH.

Tactic Notation "double" "measure" "induction" "on" hyp(x) hyp(y) "with" uconstr(f) "as" ident(IH) :=
  pattern x, y; revert x y; apply measure_double_rect with (m := fun x y => f); intros x y IH.
*)

(* Tactic Notation "induction" "on" hyp(x) "as" ident(IH) "with" "measure" uconstr(f) :=
   pattern x; revert x; apply measure_rect with (m := fun x => f); intros x IH. *)

(* Tactic Notation "induction" "on" hyp(x) hyp(y) "as" ident(IH) "with" "measure" uconstr(f) :=
   pattern x, y; revert x y; apply measure_double_rect with (m := fun x y => f); intros x y IH. *)

Extraction Inline measure_rect measure_double_rect.

(** Solved the parasitic let/in issue with measure_rect with the horrible Ltac
    hack that constructs the fixpoint and then hides it *)

Tactic Notation "induction" "on" hyp(x) "as" ident(IH) "with" "measure" uconstr(f) :=
  let m := fresh "measure" in let R := fresh "relation" in let l := fresh "loop" in
  let u := fresh "u" in let Hu := fresh "Hu" in let v := fresh "v" in let Hv := fresh "Hv" 
  in match type of x with ?tx => set (m := (f : tx -> nat)) end; 
     set (R x y := m x < m y);
     refine ((fix l u (Hu : Acc R u) { struct Hu } := _) x _);
     [ pattern u;
       match goal with |- ?t _ => assert (forall v, R v u -> t v) as IH end;
       [ intros v Hv; apply (l v), (Acc_inv Hu), Hv 
       | unfold R, m in *; clear m R Hu l x; rename u into x ]
     | unfold R; apply wf_inverse_image, lt_wf ].

Tactic Notation "induction" "on" hyp(x) hyp(y) "as" ident(IH) "with" "measure" uconstr(f) :=
  let m := fresh "measure" in let R := fresh "relation" in let l := fresh "loop" in
  let u := fresh "u" in let u' := fresh x in let Hu := fresh "Hu" in 
  let v := fresh "v" in let v' := fresh y in let Hv := fresh "Hv" 
  in match type of x with ?tx => 
       match type of y with ?ty => set (m := (f : tx -> ty -> nat)) end end; 
     set (R u v := m (fst u) (snd u) < m (fst v) (snd v)); unfold fst, snd in R;
     refine ((fix l u v (Hu : Acc R (u,v)) { struct Hu } := _) x y _);
     [ pattern u, v;
       match goal with |- ?t _ _ => assert (forall u' v', R (u',v') (u,v) -> t u' v') as IH end;
       [ intros u' v' Hv; apply (l u' v'), (Acc_inv Hu), Hv 
       | unfold R, m in *; clear m R Hu l x y; rename u into x; rename v into y ]
     | unfold R; apply wf_inverse_image, lt_wf ].

