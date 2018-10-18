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

Require Import List Extraction.

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

    Let HP0 : forall ll H1 H2, @P ll H1 -> @P ll H2.
    Proof.
      intros ll H1 H2; rewrite (sfin_pirr H1 H2); trivial.
    Defined.

    Hypothesis HP1 : @P _ sfin_snil.
    Hypothesis HP2 : forall a ll H, @P ll H -> P (@sfin_scons a ll H).

    Fixpoint sfin_rect ll H { struct H } : @P ll H.
    Proof.
      revert H.
      refine (match ll with
        | snil       => fun H => _
        | scons a ll => fun H => _
      end).
      + apply HP0 with (1 := HP1).
      + apply HP0 with (1 := @HP2 a ll (sfin_inv H) (@sfin_rect _ _)).
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

  End list_llist.

End llist.
 