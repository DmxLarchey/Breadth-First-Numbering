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
    + trivial.
    + intros [ | x l ].
      * trivial.
      * simpl; f_equal; auto.
  Qed.

  (* Every finite list can be transformed into a lazy list. *)

  Fixpoint list_llist l : llist :=
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
  
    Definition llist_list l Hl := proj1_sig (@llist_list_rec l Hl).
  
    Fact llist_list_spec l Hl : l = list_llist (@llist_list l Hl).
    Proof. apply (proj2_sig (@llist_list_rec l Hl)). Qed.

  End llist_list.
  
  Arguments llist_list : clear implicits.
  
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

  Definition lfin_length l Hl := length (llist_list l Hl).

  Arguments lfin_length : clear implicits.
  
  Fact lfin_length_fix_0 H : lfin_length lnil H = 0.
  Proof. unfold lfin_length; rewrite llist_list_fix_0; auto. Qed.
  
  Fact lfin_length_fix_1 x l H : lfin_length (lcons x l) H = S (lfin_length l (lfin_inv H)).
  Proof. unfold lfin_length; rewrite llist_list_fix_1; auto. Qed.
  
End llist.

Arguments lnil {X}.
Arguments llist_list {X}.
Arguments lfin_length {X}.

Section Rotate.

  (* Rotate with lazy lists (with a non-informative "finiteness" predicate 
     It seems the algorithm manipulates f a as lazy lists and r as a list ... no sure
     or three lazy lists ? *)

  Variable (X : Type).
  
  Implicit Type (f r : llist X) (a : list X).
  
  Let prec  f Hf r Hr := lfin_length r Hr = 1 + lfin_length f Hf.
  Let rspec f Hf r Hr a m := m = llist_list f Hf++rev (llist_list r Hr)++a.
  
  Fixpoint rotate f r a (Hf : lfin f) (Hr : lfin r) { struct Hf } : @prec f Hf r Hr -> sig (@rspec f Hf r Hr a). 
  Proof.
    revert Hr.
    refine (match r as r' return forall (Hr : lfin r'), @prec f Hf _ Hr  -> sig (@rspec f Hf r' Hr a) with
      | lnil       => _
      | lcons y r' => _ 
    end); intros Hr' H.
    { exfalso.
      red in H.
      rewrite lfin_length_fix_0 in H; discriminate. }
    revert Hf H.
    refine (match f as f' return forall (Hf' : lfin f'), @prec f' Hf' _ Hr' -> sig (rspec Hf' Hr' a) with
      | lnil       => _
      | lcons x f' => _
    end); intros Hf' H.
    + exists (y::a).
      red in H |- *; revert H.
      rewrite llist_list_fix_0, llist_list_fix_1, lfin_length_fix_0, lfin_length_fix_1.
      destruct r'.
      * rewrite llist_list_fix_0; trivial.
      * rewrite lfin_length_fix_1; discriminate.
    + refine (let (ro,Hro) := rotate f' r' (y::a) (lfin_inv Hf') (lfin_inv Hr') _ in exist _ (x::ro) _).
      * red in H |- *; revert H.
        repeat rewrite lfin_length_fix_1; intros; omega.
      * red in Hro |- *; revert Hro.
        repeat rewrite llist_list_fix_1; intros; subst.
        simpl; rewrite app_ass; auto.
  Defined.

End Rotate.

Recursive Extraction llist_list list_llist rotate.

