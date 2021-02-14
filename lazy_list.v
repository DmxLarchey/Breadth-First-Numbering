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

  Section small_inversions.

    Let shape_inv s := match s with snil => False | _         => True   end.
    Let pred_inv s  := match s with snil => snil  | scons x s => s      end.
    
    Definition sfin_inv x s (H : sfin (scons x s)) : sfin s :=
      match H in sfin s return shape_inv s -> sfin (pred_inv s) with
        | sfin_snil         => fun E => match E with end
        | sfin_scons _ _ H1 => fun _ => H1
      end I.

    Fact sfin_inv' x s : sfin (scons x s) -> sfin s.
    Proof. inversion 1; assumption. Defined.

    Let output_invert s : sfin s -> Prop := 
      match s as s' return sfin s' -> Prop with
        | snil      => fun H => sfin_snil = H
        | scons x s => fun H => { H' | @sfin_scons x s H' = H }
      end.

   (**  Notice { H | ... = ... } is also of sort Prop !!!
         Yes it is strange but it is part of CIC
        see ex_sig generalization in the parenthesis below *)

    Definition sfin_invert s H : @output_invert s H :=
      match H in sfin s return @output_invert s H with
        | sfin_snil         => eq_refl
        | sfin_scons _ _ H' => exist _ H' eq_refl 
      end.

  End small_inversions.

  Section ex_sig_general.

    (* Very small parenthesis *)

    Variable (Q : Prop) (P : Q -> Prop).

    Fact reif : (exists H, P H) -> { H | P H }.
    Proof. intros (H & ?); exists H; assumption. Qed.

  End ex_sig_general.

  (** We show proof irrelevance for sfin by induction/inversion
      where inversion is obtained by dependent pattern matching *)

  Fixpoint sfin_pirr s (H1 : sfin s) : forall H2, H1 = H2.
  Proof.
    destruct H1 as [ | x s H1 ]; intros H2.
    + apply (sfin_invert H2).
    + destruct (sfin_invert H2) as (H & E).
      subst; f_equal; apply sfin_pirr.
  Defined.

  Fixpoint sfin_normalize s (H : sfin s) : sfin s.
  Proof. 
    revert H; refine(match s with 
      | snil      => fun _ => sfin_snil
      | scons x s => fun H => sfin_scons x s (sfin_normalize _ (sfin_inv H))
    end).
  Defined.

  (* For P : forall s, sfin s -> Type, can I show P s H <-> P s H' w/o
     singleton elim ? *)

  Section sfin_rect.

    (** We show dependent recursion principle for sfin implementing
        what a command like

        Scheme sfin_rect := Induction for sfin Sort Type.

        But it is not smart enough to invent PIRR ...

        Remark that we use singleton elimination here ...

        To circumvent, may be it it possible to change sfin_pirr 
        in 
            sfin_pirr s (H1 : sfin s) : forall H2 P, P H1 -> P H2 instead of H1 = H2

        but this does not seem obvious ... would something like
        this work w/o singleton elim ?
      *)

    Variable P : forall s, sfin s -> Type.

    Hypothesis HP1 : @P _ sfin_snil.
    Hypothesis HP2 : forall x s H, @P s H -> P (@sfin_scons x s H).

    Ltac pirr := match goal with |- @P _ ?a -> @P _ ?b => rewrite (@sfin_pirr _ a b); trivial end.

    Fixpoint sfin_rect s H { struct H } : @P s H.
    Proof.
      revert H.
      refine (match s with
        | snil      => fun H => _
        | scons x s => fun H => _
      end).
      + generalize HP1; pirr.
      + generalize (@HP2 x s (sfin_inv' H) (@sfin_rect s (sfin_inv' H))); pirr.
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

  (* Injectivity of constructors *)

  Fact lcons_inj a b ll1 ll2 : lcons a ll1 = lcons b ll2 -> a = b /\ ll1 = ll2.
  Proof.
    revert ll1 ll2; intros (s1 & H1) (s2 & H2); simpl.
    intros E; apply f_equal with (f := @proj1_sig _ _) in E; simpl in E.
    inversion E; subst; split; auto; f_equal.
    apply sfin_pirr.
  Qed.

  Fact lnil_lcons_discr a ll : lnil <> lcons a ll.
  Proof. destruct ll; discriminate. Qed.

  (** And a dependent recursion principle identical to list_rect *)

  Section llist_rect.

    Variable P : llist -> Type.
    
    Hypothesis (HP0 : P lnil).
    Hypothesis (HP1 : forall a m, P m -> P (lcons a m)).

    Theorem llist_rect : forall ll, P ll.
    Proof. 
      intros (? & H). 
      induction H as [ | x s H IH ].
      + apply HP0.
      + apply HP1 with (1 := IH).
    Defined.

  End llist_rect.

  (* We have everything to define an isomorphism between list and llist *)

  Section list_llist.

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

    Section llist_list.

      Let llist_list_rec ll : { l | ll = list_llist l }.
      Proof.
        induction ll as [ | a ll (l & Hl) ] using llist_rect.
        + exists nil; auto.
        + exists (a::l); simpl; f_equal; auto.
      Qed.

      Definition llist_list ll := proj1_sig (llist_list_rec ll).

      Fact id_list_llist ll : ll = list_llist (llist_list ll).
      Proof. apply (proj2_sig (llist_list_rec ll)). Qed.

    End llist_list.

    Fact id_llist_llist l : l = llist_list (list_llist l).
    Proof. apply list_llist_inj; rewrite <- id_list_llist; trivial. Qed.

    (* Fixpoint equations *)

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
  Proof. unfold llength; rewrite llist_list_nil; auto. Qed.

  Fact llength_cons a ll : llength (lcons a ll) = S (llength ll).
  Proof. unfold llength; rewrite llist_list_cons; auto. Qed.

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

Check llist_rotate_eq.

Recursive Extraction llist_list llist_app llist_rotate.


 