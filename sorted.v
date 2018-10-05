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

Require Import list_utils php.

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

  Variable (f : X -> X) (Hf : forall x y, R x y -> R (f x) (f y)).

  Fact sorted_map l : sorted l -> sorted (map f l).
  Proof.
    induction 1 as [ | x l H1 H2 IH2 ]; simpl; constructor; auto.
    apply Forall_forall.
    rewrite Forall_forall in H1.
    intros y; rewrite in_map_iff.
    intros (? & ? & ?); subst; auto.
  Qed.

End sorted.

Fact sorted_mono X (R S : X -> X -> Prop) l : (forall x y, In x l -> In y l -> R x y -> S x y) -> sorted R l -> sorted S l.
Proof.
  intros H1 H2; revert H2 H1.
  induction 1 as [ | x l H1 H2 IH2 ]; intros H3.
  + constructor.
  + constructor.
    * revert H1; do 2 rewrite Forall_forall.
      intros H1 y Hy; apply H3; simpl; auto.
    * apply IH2; intros ? ? ? ?; apply H3; simpl; auto.
Qed.

Section sorted_no_dup.
 
  Variables (X : Type) (R : X -> X -> Prop) (HR : forall x, ~ R x x).

  Lemma sorted_no_dup l : sorted R l -> ~ list_has_dup l.
  Proof.
    induction 1 as [ | x l H1 H2 IH2 ]; intros H.
    + inversion H.
    + apply list_hd_cons_inv in H.
      destruct H as [ H | H ]; try tauto.
      rewrite Forall_forall in H1; firstorder.
  Qed.

End sorted_no_dup.

Section no_dup_sorted_with_ineq.

  Variables (X : Type).
  
  Let R := fun (x y: X) => x <> y.

  (** for this specific relation, not having duplicates is equivalent to being sorted: *)

  Lemma no_dup_sorted_with_ineq l: sorted R l <-> ~ list_has_dup l.
  Proof.
    split.
    * apply sorted_no_dup; intros ? []; trivial.
    * induction l as [ | x l IHl].
      - constructor.
      - intros H; constructor.
        + rewrite Forall_forall.
          intros y Hy ?; subst.
          apply H.
          constructor 1; trivial.
        + apply IHl; contradict H.
          constructor 2; trivial.
  Qed.

End no_dup_sorted_with_ineq.

Section sorted_perm.

  Variables (X : Type) (R S : X -> X -> Prop) (l m : list X) (Hlm : forall x, In x l <-> In x m).

  Section sorted_perm_aux.
  
    Hypothesis (Hl : ~ list_has_dup l) (Hm : ~ list_has_dup m).

    Hint Resolve Permutation_sym.

    (* length_le_and_incl_implies_dup_or_perm is from the proof of the PHP, see php.v
       I know, I should find a better name ...
     *)

    Lemma sorted_perm_aux : l ~p m.
    Proof.
      destruct (le_lt_dec (length l) (length m)).
      + destruct (@length_le_and_incl_implies_dup_or_perm _ l m); auto; try tauto; intro; apply Hlm.
      + destruct (@length_le_and_incl_implies_dup_or_perm _ m l); auto; try tauto; try omega; intro; apply Hlm.
    Qed.

  End sorted_perm_aux.

  Hypothesis (HR : forall x, ~ R x x) (HS : forall x, ~ S x x)
             (Hl : sorted R l) (Hm : sorted S m).

  Hint Resolve sorted_no_dup.

  Theorem sorted_perm : l ~p m.
  Proof. apply sorted_perm_aux; eauto. Qed.

End sorted_perm.
