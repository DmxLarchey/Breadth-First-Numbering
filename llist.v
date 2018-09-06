(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             Ralph Matthes [+]                              *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                             [*] Affiliation IRIT -- CNRS   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega Wellfounded Extraction.

Set Implicit Arguments.

Section llist.

  (* G54DTP Dependently Typed Programming.
    Introduction to coinductive types.
    Venanzio Capretta, March 2011.
  *)

  Variable X : Type.

  CoInductive llist : Type :=
    | lnil: llist
    | lcons: X -> llist -> llist.

  (* We must define an explicit unfold operation. *)

  Definition lunfold (l : llist) : llist :=
    match l with
      | lnil => lnil
      | lcons a l' => lcons a l'
    end.
 
  (* The next function unfolds a lazy list several times:
     the natural number n says how many.
  *)

  Fixpoint lunfold_many (l:llist) n : llist :=
    match n with
      | O    => l
      | S n => match l with
          | lnil      => lnil
          | lcons a l => lcons a (lunfold_many l n)
          end
    end.

  (* We can prove that the unfolding is equal to the original list. *)

  Lemma lunfold_many_eq: forall n (l:llist), l = lunfold_many l n.
  Proof.
    induction n as [ | n IHn ].
    + reflexivity.
    + intros [ | x l ].
      * reflexivity.
      * simpl; f_equal; auto.
  Qed.

  (* Every finite list can be transformed into a lazy list. *)

  Fixpoint list_llist (l: list X) : llist :=
    match l with
      | nil  => lnil
      | a::l => lcons a (list_llist l)
    end.
    
  Fact list_llist_inj l m : list_llist l = list_llist m -> l = m.
  Proof.
    revert m; induction l as [ | x l IHl ]; intros [ | y m ]; auto; try discriminate.
    simpl; intros H; inversion H; f_equal; auto.
  Qed.
    
  Inductive lfin : llist -> Prop :=
    | lfin_lnil :  lfin lnil
    | lfin_lcons : forall a l, lfin l -> lfin (lcons a l).
    
  Fact lfin_inv a l : lfin (lcons a l) -> lfin l.
  Proof. inversion 1; assumption. Defined.

  Fact lfin_list_llist l : lfin (list_llist l).
  Proof. induction l; simpl; constructor; trivial. Qed.

  Section llist_list.

    Let llist_list_rec : forall l, lfin l -> { m | l = list_llist m }.
    Proof.
      refine (fix loop l Hl { struct Hl } := 
        match l as l' return lfin l' -> { m | l' = list_llist m } with
          | lnil      => fun H => exist _ nil _
          | lcons x l => fun H => let (r,Hr) := loop l _ in exist _ (x::r) _
        end Hl); subst; trivial.
      inversion H; trivial.
    Qed.
  
    Definition llist_list l (Hl: lfin l): list X := proj1_sig (@llist_list_rec l Hl).
  
    Fact llist_list_spec l (Hl: lfin l) : l = list_llist (@llist_list l Hl).
    Proof. apply (proj2_sig (@llist_list_rec l Hl)). Qed.

  End llist_list.
  
  Arguments llist_list : clear implicits.

  Fact llist_list_eq l (H1 H2: lfin l) : @llist_list l H1 = @llist_list l H2.
  Proof.
    apply list_llist_inj; do 2 rewrite <- llist_list_spec; reflexivity.
  Qed.

  Fact llist_list_fix_0 H : llist_list lnil H = nil.
  Proof.
    generalize (llist_list_spec H); simpl.
    generalize (llist_list _ H).
    intros [|]; try discriminate; auto.
  Qed.
  
  Fact llist_list_fix_1 x l H : llist_list (lcons x l) H = x::llist_list l (lfin_inv H).
  Proof.
    generalize (llist_list_spec H); simpl.
    generalize (llist_list _ H).
    intros [|]; try discriminate.
    simpl.
    intros G; inversion G; f_equal; auto.
    apply list_llist_inj; rewrite <- H2.
    apply llist_list_spec.
  Qed.

  Definition lfin_length l (Hl: lfin l) := length (llist_list l Hl).

  Arguments lfin_length : clear implicits.

  Fact lfin_length_eq l (H1 H2: lfin l) : lfin_length l H1 = lfin_length l H2.
  Proof. unfold lfin_length; f_equal; apply llist_list_eq. Qed.
  
  Fact lfin_length_fix_0 H : lfin_length lnil H = 0.
  Proof. unfold lfin_length; rewrite llist_list_fix_0; auto. Qed.
  
  Fact lfin_length_fix_1 x l H : lfin_length (lcons x l) H = S (lfin_length l (lfin_inv H)).
  Proof. unfold lfin_length; rewrite llist_list_fix_1; auto. Qed.
  
End llist.

Arguments lnil {X}.
Arguments llist_list {X}.
Arguments lfin_length {X}.

Section Append.

  Variable (X : Type).
  
  Implicit Type (l m : llist X).

  Section def.

    Let llist_app_rec : forall l m (Hl : lfin l) (Hm : lfin m), { k | k = list_llist (llist_list _ Hl ++ llist_list _ Hm) }.
    Proof.
      refine (fix loop l m Hl Hm { struct Hl } := _).
      revert Hl; refine (match l with 
        | lnil      => fun _  => exist _ m _
        | lcons x l => fun Hl => let (r,Hr) := loop l m (lfin_inv Hl) Hm in exist _ (lcons x r) _
      end).
      + rewrite llist_list_fix_0; simpl; apply llist_list_spec.
      + rewrite llist_list_fix_1; simpl; f_equal; assumption.
    Qed.

    Definition llist_app l m Hl Hm: llist X := proj1_sig (@llist_app_rec l m Hl Hm).

    Fact llist_app_spec l m Hl Hm : @llist_app l m Hl Hm = list_llist (llist_list _ Hl ++ llist_list _ Hm).
    Proof. apply (proj2_sig (@llist_app_rec l m Hl Hm)). Qed.

  End def.

  Arguments llist_app : clear implicits.

End Append.

Section Rotate.

  (* Rotate with lazy lists (with a non-informative "finiteness" predicate 
     It seems the algorithm manipulates f a as lazy lists and r as a list ... no sure
     or three lazy lists ? *)

  Variable (X : Type).
  
  Implicit Type (l r : llist X) (a : llist X).
  
  Section def.

    Let prec  l Hl r Hr: Prop := lfin_length r Hr = 1 + lfin_length l Hl.
    Let rspec l Hl r Hr a Ha m: Prop := m = list_llist (llist_list l Hl++rev (llist_list r Hr)++llist_list a Ha).
  
    Let llist_rotate_rec : forall l r a Hl Hr Ha, @prec l Hl r Hr -> sig (@rspec l Hl r Hr a Ha).
    Proof.
      refine (fix loop l r a Hl Hr Ha { struct Hl } := _). 
      revert Hr.
      refine (match r as r' return forall (Hr : lfin r'), @prec l Hl _ Hr  -> sig (@rspec l Hl r' Hr a Ha) with
        | lnil       => _
        | lcons y r' => _ 
      end); intros Hr' H.
      { exfalso; red in H; rewrite lfin_length_fix_0 in H; discriminate. }
      revert Hl H.
      refine (match l as l' return forall (Hl' : lfin l'), @prec l' Hl' _ Hr' -> sig (rspec Hl' Hr' Ha) with
        | lnil       => _
        | lcons x l' => _
      end); intros Hl' H.
      + exists (lcons y a).
        red in H |- *; revert H.
        rewrite llist_list_fix_0, llist_list_fix_1, lfin_length_fix_0, lfin_length_fix_1.
        destruct r'.
        * rewrite llist_list_fix_0; simpl. 
          rewrite <- llist_list_spec; trivial.
        * rewrite lfin_length_fix_1; discriminate.
      + refine (let (ro,Hro) := loop l' r' (lcons y a) (lfin_inv Hl') (lfin_inv Hr') (lfin_lcons _ Ha) _ in exist _ (lcons x ro) _).
        * red in H |- *; revert H.
          repeat rewrite lfin_length_fix_1; intros; omega.
        * red in Hro |- *; revert Hro.
          repeat rewrite llist_list_fix_1; intros; subst.
          simpl; rewrite app_ass; simpl; reflexivity.
    Qed.

    Definition llist_rotate f r a Hf Hr Ha H: llist X := proj1_sig (@llist_rotate_rec f r a Hf Hr Ha H).

    Fact llist_rotate_spec f r a Hf Hr Ha H : @rspec f Hf r Hr a Ha (@llist_rotate f r a Hf Hr Ha H).
    Proof. apply (proj2_sig (@llist_rotate_rec f r a Hf Hr Ha H)). Qed.

  End def.

  Arguments llist_rotate : clear implicits.

  Fact lfin_rotate f r a Hf Hr Ha H : lfin (llist_rotate f r a Hf Hr Ha H).
  Proof.
    generalize (llist_rotate_spec Ha H); intros E.
    rewrite E; apply lfin_list_llist.
  Qed.

  Fact llist_rotate_eq l r a Hl Hr Ha H : llist_list _ (@lfin_rotate l r a Hl Hr Ha H) = llist_list l Hl++rev (llist_list r Hr)++llist_list a Ha.
  Proof.
    apply list_llist_inj.
    rewrite <- (@llist_rotate_spec l r a Hl Hr Ha H).
    generalize (llist_rotate l r a Hl Hr Ha H) (lfin_rotate Hl Hr Ha H).
    symmetry; apply llist_list_spec.
  Qed.

  Fact llist_rotate_length l r a Hl Hr Ha H : lfin_length _ (@lfin_rotate l r a Hl Hr Ha H) = lfin_length _ Hl + lfin_length _ Hr + lfin_length _ Ha.
  Proof.
    unfold lfin_length.
    rewrite llist_rotate_eq.
    do 2 rewrite app_length.
    rewrite rev_length; omega.
  Qed.
 
End Rotate.

Recursive Extraction llist_list list_llist llist_app llist_rotate.

Check llist_rotate.
Check llist_rotate_spec.

