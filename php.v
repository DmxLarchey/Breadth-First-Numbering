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

Require Import Arith Omega List Permutation.

Require Import list_utils wf_utils.

Set Implicit Arguments.

Section pigeon_list.

  Variable (X : Type).

  Implicit Types (l m : list X).
  
  Inductive list_has_dup : list X -> Prop :=
    | in_list_hd0 : forall l x, In x l -> list_has_dup (x::l)
    | in_list_hd1 : forall l x, list_has_dup l -> list_has_dup (x::l).
  
  Fact list_hd_cons_inv x l : list_has_dup (x::l) -> In x l \/ list_has_dup l.
  Proof. inversion 1; subst; auto. Qed.
  
  Fact list_has_dup_app_left l m : list_has_dup m -> list_has_dup (l++m).
  Proof. induction l; simpl; auto; constructor 2; auto. Qed.
  
  Fact list_has_dup_app_right l m : list_has_dup l -> list_has_dup (l++m).
  Proof. 
    induction 1; simpl.
    + constructor 1; apply in_or_app; left; auto.
    + constructor 2; auto.
  Qed.

  Fact perm_list_has_dup l m : l ~p m -> list_has_dup l -> list_has_dup m.
  Proof.
    induction 1 as [ | x l m H1 IH1 | x y l | ]; auto; 
      intros H; apply list_hd_cons_inv in H.
    + destruct H as [ H | H ].
      * apply Permutation_in with (1 := H1) in H.
        apply in_list_hd0; auto.
      * apply in_list_hd1; auto.
    + destruct H as [ [ H | H ] | H ]; subst.
      * apply in_list_hd0; left; auto.
      * apply in_list_hd1, in_list_hd0; auto.
      * apply list_hd_cons_inv in H.
        destruct H as [ H | H ].
        - apply in_list_hd0; right; auto.
        - do 2 apply in_list_hd1; auto.
  Qed.

  Fact list_has_dup_eq_duplicates m: list_has_dup m <-> exists x aa bb cc, m = aa++x::bb++x::cc.
  Proof.
    split.
    + induction 1 as [ m x Hm | m x _ IHm ].
      - apply in_split in Hm.
        destruct Hm as (bb & cc & Hm).
        exists x, nil, bb, cc; subst; auto.
      - destruct IHm as (y & aa & bb & cc & IHm).
        exists y, (x::aa), bb, cc; subst; auto.
    + intros (x & aa & bb & cc & Hm).
      subst m.
      apply list_has_dup_app_left.
      constructor 1; apply in_or_app; right.
      constructor 1; reflexivity.
  Qed.

  Fact repeat_choice_two x m : (forall a, In a m -> a = x) -> (exists m', m = x::x::m') \/ m = nil \/ m = x::nil.
  Proof.
    intros H.
    destruct m as [ | a [ | b m ] ].
    + right; left; auto.
    + right; right; rewrite (H a); auto; left; auto.
    + left; rewrite (H a), (H b); simpl; auto; exists m; auto.
  Qed.

  Fact incl_right_cons_incl_or_lhd_or_perm m x l : 
       incl m (x::l) -> incl m l 
                     \/ list_has_dup m 
                     \/ exists m', m ~p x::m' /\ incl m' l.
  Proof.
    intros H.
    apply incl_cons_rinv in H.
    destruct H as (m1 & m2 & H1 & H2 & H3).
    destruct (repeat_choice_two _ H2) as [ (m3 & H4) | [ H4 | H4 ] ]; 
      subst m1; simpl in H1; clear H2.
    + apply Permutation_sym in H1.
      right; left.
      apply perm_list_has_dup with (1 := H1).
      apply in_list_hd0; left; auto.
    + left; apply perm_incl_left with (1 := H1); auto.
    + right; right.
      exists m2; auto.
  Qed.
 
  Lemma length_le_and_incl_implies_dup_or_perm l :  
               forall m, length l <= length m 
                      -> incl m l 
                      -> list_has_dup m \/ m ~p l.
  Proof.
    induction on l as IHl with measure (length l).
    destruct l as [ | x l ].
    + intros [ | y ] _ H.
      * right; auto.
      * destruct (H y); simpl; auto.
    + intros [ | y m ] H1 H2; simpl in H1; try omega.
      apply le_S_n in H1.
      apply incl_cons_linv in H2. 
      destruct H2 as [ [ H3 | H3 ] H4 ].
      * subst y.
        apply incl_right_cons_choose in H4.
        destruct H4 as [ H4 | H4 ].
        - left; apply in_list_hd0; auto.
        - destruct IHl with (3 := H4); auto.
          left; apply in_list_hd1; auto.
      * apply incl_right_cons_incl_or_lhd_or_perm in H4.
        destruct H4 as [ H4 | [ H4 | (m' & H4 & H5) ] ].
        - destruct IHl with (3 := H4) as [ H5 | H5 ]; auto.
          ++ left; apply in_list_hd1; auto.
          ++ left; apply in_list_hd0; revert H3.
             apply Permutation_in, Permutation_sym; auto.
        - left; apply in_list_hd1; auto.
        - apply Permutation_sym in H4.
          apply perm_in_head in H3.
          destruct H3 as (l' & Hl').
          apply perm_incl_right with (1 := Hl'), 
                incl_right_cons_choose in H5.
          destruct H5 as [ H5 | H5 ].
          ++ left; apply in_list_hd0, Permutation_in with (1 := H4); right; auto.
          ++ { apply IHl in H5.
               + destruct H5 as [ H5 | H5 ].
                 * left; apply perm_list_has_dup in H4; apply in_list_hd1; auto.
                 * right.
                    apply Permutation_trans with (y::x::m').
                    - apply perm_skip, Permutation_sym; auto.
                    - apply Permutation_trans with (1 := perm_swap _ _ _),
                            perm_skip, Permutation_sym,
                            Permutation_trans with (1 := Hl'),
                            perm_skip, Permutation_sym; auto.
               + apply Permutation_length in Hl'; simpl in Hl' |- *; omega.
               + apply Permutation_length in Hl'.
                 apply Permutation_length in H4.
                 simpl in Hl', H4; omega. }
  Qed.

  Theorem finite_pigeon_hole l m : 
         length l < length m 
      -> incl m l 
      -> exists x aa bb cc, m = aa++x::bb++x::cc.
  Proof.
    intros H1 H2; apply list_has_dup_eq_duplicates.
    destruct (@length_le_and_incl_implies_dup_or_perm l m) as [ | H3 ]; auto;
      [ | apply Permutation_length in H3 ]; omega.
  Qed.

End pigeon_list.
