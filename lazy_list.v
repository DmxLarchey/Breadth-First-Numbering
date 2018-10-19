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

Require Import List Arith Omega Extraction.

Require Import wf_utils.

Set Implicit Arguments.

Section llist.

  Variable X : Type.

  CoInductive stream : Type :=
    | snil : stream
    | scons : X -> stream -> stream.

  Implicit Types (a: X) (s: stream) (l: list X).

  Unset Elimination Schemes.
    
  Inductive sfin : stream -> Prop :=
    | sfin_snil :  sfin snil
    | sfin_scons : forall a ll, sfin ll -> sfin (scons a ll).

  Arguments sfin_scons : clear implicits.

  Set Elimination Schemes.

  Fact sfin_inv a ll : sfin (scons a ll) -> sfin ll.
  Proof. inversion 1; assumption. Defined.

  Scheme sfin_ind := Induction for sfin Sort Prop.

  Section sfin_uniq.

    (** We show proof irrelevance for sfin by dependent pattern matching 

        Notice { H | ... = ... } is also of sort Prop !!!
        Yes it is strange but it is part of CIC 
      *)

    Let sfin_inv_type ll (H : sfin ll) := 
      match ll as l return sfin l -> Prop with
        | snil       => fun H => sfin_snil = H
        | scons a ll => fun H => { H' | @sfin_scons a ll H' = H }
      end H.

    Fact sfin_invert ll H : @sfin_inv_type ll H.
    Proof. 
      destruct H as [ | ? ? H ]; simpl; trivial. 
      exists H; trivial.
    Defined.

    (* The dependent inductive scheme lfin_ind is used here *)

    Lemma sfin_pirr ll (H1 H2 : sfin ll) : H1 = H2.
    Proof.
      revert H2.
      induction H1; intros H2.
      + apply (sfin_invert H2).
      + destruct (sfin_invert H2) as (H & E).
        subst; f_equal; trivial.
    Qed.

  End sfin_uniq.
    
  Section sfin_rect.

    (** We show dependent recursion principle for sfin implementing
        what a command like

        Scheme sfin_rect := Induction for sfin Sort Type.

        if it worked ...
      *)

    Variable P : forall ll, sfin ll -> Type.

    Hypothesis HP1 : @P _ sfin_snil.
    Hypothesis HP2 : forall a ll H, @P ll H -> P (@sfin_scons a ll H).

    Ltac solve := match goal with |- @P _ ?a -> @P _ ?b => rewrite (@sfin_pirr _ a b); trivial end.

    Fixpoint sfin_rect ll H { struct H } : @P ll H.
    Proof.
      revert H.
      refine (match ll with
        | snil       => fun H => _
        | scons a ll => fun H => _
      end).
      + generalize HP1; solve.
      + generalize (@HP2 a ll (sfin_inv H) (@sfin_rect _ _)); solve.
    Qed.

  End sfin_rect.

  (* Now we define lazy lists *)

  Definition llist := { s | sfin s }.

  Implicit Type ll : llist.

  (* Constructors *)

  Definition lnil : llist := exist _ _ sfin_snil.
  Definition lcons a : llist -> llist.
  Proof.
    intros (ll & H).
    exists (scons a ll).
    apply sfin_scons, H.
  Defined.

  Fact lcons_inj a b ll1 ll2 : lcons a ll1 = lcons b ll2 -> a = b /\ ll1 = ll2.
  Proof.
    revert ll1 ll2; intros (s1 & H1) (s2 & H2); simpl.
    inversion 1; subst; split; auto; f_equal; apply sfin_pirr.
  Qed.

  Fact lnil_lcons_discr a ll : lnil <> lcons a ll.
  Proof. destruct ll; discriminate. Qed.

  Section llist_rect.

    (** And a dependent recursion principle identical to list_rect *)

    Variable P : llist -> Type.
    
    Hypothesis (HP0 : P lnil).
    Hypothesis (HP1 : forall a m, P m -> P (lcons a m)).

    Let Q s (H : sfin s) := P (exist _ s H).

    Let Q_total s H : @Q s H.
    Proof.
      induction H as [ | a s H IH ].
      + apply HP0.
      + apply HP1 with (1 := IH).
    Qed.

    Theorem llist_rect : forall ll, P ll.
    Proof. intros []; apply Q_total. Qed.
  
  End llist_rect.

  Section list_llist.

    (* We define an isomorphism between list and llist *)

    Fixpoint list_llist l :=
      match l with
        | nil  => lnil
        | x::l => lcons x (list_llist l)
      end.

    Fact list_llist_inj l m : list_llist l = list_llist m -> l = m.
    Proof.
      revert m; induction l as [ | a l IH ]; intros [ | b m ]; simpl; auto.
      + intros H; exfalso; revert H; apply lnil_lcons_discr.
      + intros H; exfalso; symmetry in H; revert H; apply lnil_lcons_discr.
      + intros H; apply lcons_inj in H; destruct H; f_equal; auto.
    Qed.

    Let llist_list_rec ll : { l | ll = list_llist l }.
    Proof.
      induction ll as [ | a ll (l & Hl) ] using llist_rect.
      + exists nil; auto.
      + exists (a::l); simpl; f_equal; auto.
    Qed.

    Definition llist_list ll := proj1_sig (llist_list_rec ll).

    Fact id_list_llist ll : ll = list_llist (llist_list ll).
    Proof. apply (proj2_sig (llist_list_rec ll)). Qed.

    Fact id_llist_llist l : l = llist_list (list_llist l).
    Proof. apply list_llist_inj; rewrite <- id_list_llist; trivial. Qed.

    Fact llist_list_nil : llist_list lnil = nil.
    Proof. apply list_llist_inj; rewrite <- id_list_llist; auto. Qed.

    Fact llist_list_cons a ll : llist_list (lcons a ll) = a :: llist_list ll.
    Proof.
      apply list_llist_inj.
      simpl; repeat rewrite <- id_list_llist; trivial.
    Qed.

  End list_llist.

  Definition llength ll := length (llist_list ll).
  
  Fact llength_nil : llength lnil = 0.
  Proof.
    unfold llength; rewrite llist_list_nil; auto.
  Qed.

  Fact llength_cons a ll : llength (lcons a ll) = S (llength ll).
  Proof.
    unfold llength; rewrite llist_list_cons; auto.
  Qed.

End llist.

Arguments lnil {X}.

Extraction Inline sfin_rect llist_rect.

Section Append.

  Variable (X : Type).
  
  Implicit Type (l m k : llist X).

  Definition llist_app l m : { r | llist_list r = llist_list l ++ llist_list m }.
  Proof.
    induction l as [ | x l (r & Hr) ] using llist_rect.
    + exists m; rewrite llist_list_nil; auto.
    + exists (lcons x r); repeat rewrite llist_list_cons; simpl; f_equal; auto.
  Defined.

End Append.

Arguments llist_app {X}.

Section Rotate.

  (* Rotate with lazy lists (with a non-informative "finiteness" predicate 
     It seems the algorithm manipulates f a as lazy lists and r as a list ... no sure
     or three lazy lists ? *)

  Variable (X : Type).
  
  Implicit Type (l r m a : llist X).
  
  Section def.

    Let prec l r := llength r = 1 + llength l.
    Let spec l r a m := llist_list m = llist_list l ++ rev (llist_list r) ++ llist_list a.

    Let llist_rotate_rec l r : forall a, prec l r -> sig (spec l r a).
    Proof.
      induction on l r as loop with measure (llength l); intros a.
      induction r as [ | y r' _ ] using llist_rect; intros H.
      + exfalso; red in H; revert H; rewrite llength_nil; intros; omega.
      + revert H.
        induction l as [ | x l' _ ] using llist_rect; intros H.
        * exists (lcons y a); red in H |- *.
          assert (r' = lnil); [ | subst ].
          { revert H.
            induction r' as [ | ? r' ] using llist_rect; auto.
            do 2 rewrite llength_cons.
            rewrite llength_nil; simpl; intros; omega. }
          do 2 rewrite llist_list_cons, llist_list_nil; auto.
        * refine (let (m,Hm) := loop l' r' _ (lcons y a) _ in exist _ (lcons x m) _).
          - rewrite llength_cons; omega.
          - red in H |- *; do 2 rewrite llength_cons in H; omega.
          - red in H, Hm |- *.
            repeat rewrite llist_list_cons.
            rewrite Hm, llist_list_cons; simpl.
            rewrite app_ass; auto.
    Qed.

    Definition llist_rotate l r a (H : prec l r) := proj1_sig (@llist_rotate_rec l r a H).

    Fact llist_rotate_eq l r a H : @spec l r a (@llist_rotate l r a H).
    Proof. apply (proj2_sig (@llist_rotate_rec l r a H)). Qed.

  End def.

  Arguments llist_rotate : clear implicits.

  Fact llist_rotate_length l r a H : llength (llist_rotate l r a H) = llength l + llength r + llength a.
  Proof.
    unfold llength.
    rewrite llist_rotate_eq, app_length, app_length, rev_length; omega.
  Qed.

End Rotate.

Recursive Extraction llist_list llist_app llist_rotate.


 