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

  Context  {X : Type} (m : X -> nat) (P : X -> Type)
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

Section length_split.

  Variable (X : Type).
  Implicit Type (ll : list X).

  Fact list_length_split n ll : { l : _ & { r | ll = l++r /\ length l = n } } + { length ll < n }.
  Proof.
    revert ll; induction n as [ | n IHn ].
    + left; exists nil, ll; auto.
    + intros [ | x ll ].
      * right; simpl; omega.
      * destruct (IHn ll) as [ (l & r & H1 & H2) | H1 ].
        - left; exists (x::l), r; split; subst; auto.
        - right; simpl; omega.
  Qed.

End length_split.

Section zip.

  Variable (X : Type) (f : X -> X -> X).

  Fixpoint zip l m : list X :=
    match l, m with
      | nil,  _    => m
      | _,    nil  => l
      | x::l, y::m => f x y :: zip l m
    end.

  Fact zip_fix_1 l : zip l nil = l.
  Proof. destruct l; auto. Qed.

  Fact zip_app l1 l2 m1 m2 : length l1 = length m1 -> zip (l1++l2) (m1++m2) = zip l1 m1 ++ zip l2 m2.
  Proof.
    revert m1; induction l1 as [| ? ? IH]; intros [|]; simpl; auto; try discriminate; intros; f_equal; apply IH; omega.
  Qed.

  Fact zip_app_left l1 l2 m x : length m < length l1 -> In x l2 -> In x (zip (l1++l2) m).
  Proof.
    revert m; induction l1 as [ | y l1 IH ]; intros [ | z m ]; simpl; try omega.
    + right; apply in_or_app; simpl; auto.
    + intros H1 H2; right; apply IH; auto; omega.
  Qed.

  Fact zip_app_right l m1 m2 x : length l < length m1 -> In x m2 -> In x (zip l (m1++m2)).
  Proof.
    revert m1; induction l as [ | y l IH ]; intros [ | z m1 ]; simpl; try omega.
    + right; apply in_or_app; simpl; auto.
    + intros H1 H2; right; apply IH; auto; omega.
  Qed.

  Fact zip_spec l m c : In c (zip l m) <-> (exists m1 m2, length l <= length m1 /\ m = m1++c::m2)
                                        \/ (exists l1 l2, length m <= length l1 /\ l = l1++c::l2)
                                        \/ (exists l1 x l2 m1 y m2, c = f x y /\ l = l1++x::l2 /\ m = m1++y::m2 /\ length l1 = length m1). 
  Proof.
    split.
    + revert m; induction l as [ | x l IHl ]; simpl; intros m H.
      * apply in_split in H; destruct H as (m1 & m2 & ?); subst.
        left; exists m1, m2; split; auto; omega.
      * destruct m as [ | y m ]; destruct H as [ H | H ].
        - right; left; subst; exists nil, l; auto.
        - apply in_split in H; destruct H as (l1 & l2 & ?); subst.
          right; left; exists (x::l1), l2; split; auto; simpl; omega.
        - subst; right; right; exists nil, x, l, nil, y, m; simpl; auto.
        - destruct (IHl _ H) as [ (m1 & m2 & H1 & H2) 
                              | [ (l1 & l2 & H1 & H2) 
                                | (l1 & a & l2 & m1 & b & m2 & H1 & H2 & H3 & H4) ] ].
          ++ left; subst; exists (y::m1), m2; simpl; split; auto; omega.
          ++ right; left; subst; exists (x::l1), l2; simpl; split; auto; omega.
          ++ right; right; subst; exists (x::l1), a, l2, (y::m1), b, m2; simpl; auto.
    + intros [ (m1 & m2 & H1 & H2) 
           | [ (l1 & l2 & H1 & H2) 
             | (l1 & a & l2 & m1 & b & m2 & H1 & H2 & H3 & H4) ] ]; subst.
      * revert m1 H1; induction l as [ | x l IHl ]; simpl; intros m H1.
        - apply in_or_app; simpl; auto.
        - destruct m; simpl in H1 |- *; try omega.
          right; apply IHl; omega.
      * revert l1 H1; induction m as [ | y m IHm ]; simpl; intros l H1.
        - rewrite zip_fix_1; apply in_or_app; simpl; auto.
        - destruct l; simpl in H1 |- *; try omega.
          right; apply IHm; omega.
      * revert m1 H4; induction l1; simpl; intros [] H1; simpl; try discriminate; auto.
  Qed.

  Variable (P : X -> Prop).

  Fact zip_monotone l m : Forall P l -> Forall P m -> (forall x y, In x l -> In y m -> P (f x y)) -> Forall P (zip l m).
  Proof. intros H; revert H m; do 2 (induction 1; simpl; auto). Qed.

End zip.

Section app.

  Variable X : Type.

  Fact split_In ll l (x : X) r : ll = l++x::r -> In x ll.
  Proof. intros; subst; apply in_or_app; simpl; auto. Qed.

  Fact in_concat_iff ll (x : X) : In x (concat ll) <-> exists l, In x l /\ In l ll.
  Proof.
    split.
    * induction ll as [ | l ll IH ]; simpl.
      - tauto.
      - intros H; apply in_app_or in H.
        destruct H as [ H | H ].
        + exists l; split; auto.
        + destruct IH as (l1 & ? & ?); auto; exists l1; auto.
   * intros (l & H1 & H2).
     apply in_split in H2.
     destruct H2 as (ll1 & ll2 & ?); subst.
     rewrite concat_app; apply in_or_app; simpl; right.
     apply in_or_app; simpl; auto.
  Qed.

End app.

Section Forall.

  Variable (X : Type) (R : X -> Prop).

  Fact Forall_app l m : Forall R l -> Forall R m -> Forall R (l++m).
  Proof. induction 1; simpl; auto. Qed.

  Fact Forall_map Y f l : Forall (fun y : Y => R (f y)) l -> Forall R (map f l).
  Proof. induction 1; constructor; auto. Qed.

End Forall.

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
