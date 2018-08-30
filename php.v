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

  Fact repeat_choice_two x m : Forall (eq x) m -> (exists m', m = x::x::m') \/ m = nil \/ m = x::nil.
  Proof.
    intros H.
    destruct m as [ | a [ | b m ] ]; auto.
    + inversion H; subst; auto.
    + rewrite Forall_forall in H.
      rewrite <- (H a), <- (H b); simpl; auto; left; exists m; auto.
  Qed.

  (* If m in included in x::l then 
       a) either m is included in l
       b) or m has a duplicate (x but that does not matter here)
       c) or m is permutable with x::m' with m' included in l
   *)

  Fact incl_right_cons_incl_or_lhd_or_perm m x l : 
       incl m (x::l) -> incl m l 
                     \/ list_has_dup m 
                     \/ exists m', m ~p x::m' /\ incl m' l.
  Proof.
    intros H.
    apply incl_cons_rinv in H.
    destruct H as (m1 & m2 & H1 & H2 & H3).
    destruct (repeat_choice_two H2) as [ (?&?) | [|] ]; 
      subst m1; simpl in H1; clear H2.
    + right; left; apply perm_list_has_dup with (1 := Permutation_sym H1), in_list_hd0; left; auto.
    + left; revert H1 H3; apply perm_incl_left.
    + firstorder.
  Qed.

  Fact incl_left_right_php x l y m : incl (y::m) (x::l) -> list_has_dup (y::m)
                                                        \/ x = y  /\ incl m l
                                                        \/ In y l /\ incl m l
                                                        \/ In y l /\ exists m', m ~p x::m' /\ incl m' l.
  Proof.
    intros H; apply incl_left_right_cons in H.
    destruct H as [ (? & ?) | [ (? & ?) | (H1 & H2) ] ]; subst; auto.
    + left; apply in_list_hd0; auto.
    + apply incl_right_cons_incl_or_lhd_or_perm in H2; firstorder.
      left; apply in_list_hd1; auto.
  Qed.

  (** length_le_and_incl_implies_dup_or_perm is a generalisation of the PHP
      for which the inductive case works w/o needing decidable equality  

      But I know, I should find a better name for it ...

      If  m is longer than l 
      and m is (set) included in l
      then either it has a duplicate 
               or it is permutable with l

      The proof is by measure induction on length l
   *)

  Lemma length_le_and_incl_implies_dup_or_perm l m :  
            length l <= length m 
         -> incl m l 
         -> list_has_dup m \/ m ~p l.
  Proof.
    revert m; induction on l as IHl with measure (length l); revert l IHl.
    intros [ | x l ] IHl [ | y m ]; simpl; intros H1 H2; auto; try omega;
      try (destruct (H2 y); simpl; auto; fail).
    apply le_S_n in H1.
    apply incl_left_right_php in H2.
    destruct H2 as [  H2 
                 | [ (H2 & H3) 
                 | [ (H2 & H3) 
                   | (H2 & m' & H3 & H4) ] ] ]; auto; try subst y.
    * destruct IHl with (3 := H3); auto.
      left; apply in_list_hd1; auto.
    * destruct IHl with (3 := H3); auto.
      + left; apply in_list_hd1; auto.
      + left; apply in_list_hd0; revert H2.
        apply Permutation_in, Permutation_sym; auto.
    * apply perm_in_head in H2; destruct H2 as (l' & Hl').
      apply Permutation_sym in H3.
      apply perm_incl_right with (1 := Hl'), 
            incl_right_cons_choose in H4.
      destruct H4 as [ H4 | H4 ].
      + left; apply in_list_hd0, Permutation_in with (1 := H3); right; auto.
      + destruct IHl with (3 := H4) as [ H5 | H5 ].
        - apply Permutation_length in Hl'; simpl in Hl' |- *; omega.
        - apply Permutation_length in Hl'.
          apply Permutation_length in H3.
          simpl in Hl', H3; omega.
        - left; apply perm_list_has_dup in H3; apply in_list_hd1; auto.
        - { right; apply Permutation_trans with (y::x::m').
            + apply perm_skip, Permutation_sym; auto.
            + apply Permutation_trans with (1 := perm_swap _ _ _),
                    perm_skip, Permutation_sym,
                    Permutation_trans with (1 := Hl'),
                    perm_skip, Permutation_sym; auto. }
  Qed.

  (** If  m is strictly longer than l 
      and m is (set) included in l
      then either it has a duplicate 

      This proof does not require weakly decidable equality
      and it does not find where is the duplicate
    *)

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
