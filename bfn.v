(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** Extraction of breadth-first numbering algorithm from Coq to Ocaml 

       see http://okasaki.blogspot.com/2008/07/breadth-first-numbering-algorithm-in.html
       and https://www.westpoint.edu/eecs/SiteAssets/SitePages/Faculty%20Publication%20Documents/Okasaki/jfp95queue.pdf
       and https://www.cs.cmu.edu/~rwh/theses/okasaki.pdf
       and https://www.westpoint.edu/eecs/SiteAssets/SitePages/Faculty%20Publication%20Documents/Okasaki/icfp00bfn.pdf

*)

Require Import List Arith Omega Wellfounded.
Require Import list_utils wf_utils bt bft.

Set Implicit Arguments.

Implicit Types (a n x: nat).

Section seq_an.

  (* seq_an a n = [a;a+1;...;a+(n-1)] *)

  Fixpoint seq_an a n: list nat :=
    match n with
      | 0    => nil
      | S n  => a::seq_an (S a) n
    end.

  Fact seq_an_length a n : length (seq_an a n) = n.
  Proof. revert a; induction n; simpl; intros; f_equal; auto. Qed.

  Fact seq_an_spec a n x : In x (seq_an a n) <-> a <= x < a+n.
  Proof. 
    revert x a; induction n as [ | n IHn ]; intros x a; simpl;
      [ | rewrite IHn ]; omega.
  Qed.

  Fixpoint is_seq_from n (l: list nat) { struct l }: Prop :=
    match l with  
      | nil  => True
      | x::l => n=x /\ is_seq_from (S n) l
    end.

  Theorem is_seq_from_spec a (l: list nat): is_seq_from a l <-> exists n, l = seq_an a n.
  Proof.
    revert a; induction l as [ | x l IH ]; intros a; simpl.
    + split; auto; exists 0; auto.
    + rewrite IH; split.
      * intros (? & n & Hn); subst x; exists (S n); subst; auto.
      * intros ([ | n ] & ?); subst; try discriminate.
        simpl in H; inversion H; subst; split; auto.
        exists n; auto.
  Qed.

End seq_an.

(** Of course, this needs to be replaced by a queue to obtain something efficient *)

Definition list_snoc_match (X: Type) (l: list X) : 2 <= length l -> { x : X & { y : _ & { m | l = m++y::x::nil } } }.
Proof.
  rewrite <- (rev_involutive l), rev_length.
  destruct (rev l) as [ | x [ | y l' ] ]; simpl; try omega; intros _.
  exists x, y, (rev l'); rewrite app_ass; simpl; auto.
Defined.

Section bfn.

  Variable (X : Type).

  Implicit Types (t : bt X) (l: list(bt X)).

  (* the forest (list of bt nat) is a breadth first numbering from n if
     its breadth first traversal yields [n;n+1;....;m[ for some m
   *)

  Definition is_bfn_from n (l: list (bt nat)): Prop := is_seq_from n (bft_f l).

  (* Breadth First Numbering: maps a forest X to a forest nat such that
          1) the two forests are of the same shape
          2) the result is a breadth first numbering from n  
   *)

  Definition bfn_f n l : { m | l ~lt m /\ is_bfn_from n m }.
  Proof.
    induction on n l as bfn_f with measure (lsum l).
    refine (match l as l' return l = l' -> _ with
      | nil              => fun H => exist _ nil _
      | leaf x :: ll     => fun H => let (mm,Hm) := bfn_f (S n) ll _ in exist _ (leaf n::mm) _
      | node a x b :: ll => fun H => let (mm,Hmm) := bfn_f (S n) (ll++a::b::nil) _ in 
                                     match list_snoc_match mm _ with
                                       | existT _ v (existT _ u (exist _ m Hm)) => exist _ (node u n v::m) _
                                     end
    end eq_refl).
    1,2,4,5: cycle 1.

    + subst; simpl; auto.
    + subst; simpl; rewrite lsum_app; simpl; omega.

    + apply proj1, Forall2_length in Hmm.
      rewrite <- Hmm, app_length; simpl; omega.
    + subst; split.
      * constructor.
      * red; rewrite bft_f_fix_0; simpl; auto.
    + destruct Hm as (H1 & H2).
      subst; split; auto.
      red in H2 |- *; rewrite bft_f_fix_3.
      simpl; rewrite <- app_nil_end; auto.
    + subst; destruct Hmm as (H1 & H2).
      Forall2 inv H1 as H3.
      * Forall2 inv H1 as H4.
        Forall2 inv H1 as H5.
        split; auto.
        red in H2 |- *. 
        rewrite bft_f_fix_3; simpl; auto.
      * apply Forall2_length in H1. 
        do 2 rewrite app_length in H1; simpl in H1; omega.
  Defined.

  Section bfn.

    Let bfn_full t : { t' | t ~t t' /\ is_seq_from 0 (bft_std t') }.
    Proof.
      refine (match @bfn_f 0 (t::nil) with
        | exist _ l Hl      => 
        match l as l' return l = l' -> _ with
          | nil   => fun E => _
          | t'::l => fun E => exist _ t' _
        end eq_refl
      end); simpl in *.
      + exfalso; subst; apply proj1 in Hl; inversion Hl.
      + subst; destruct Hl as (H1 & H2).
        Forall2 inv H1 as H3.
        Forall2 inv H1 as H1.
        subst; split; auto.
        red in H2.
        rewrite <- bft_std_eq_bft; auto.
    Qed.

    Definition bfn t := proj1_sig (bfn_full t).

    Fact bfn_spec_1 t : t ~t bfn t.
    Proof. apply (proj2_sig (bfn_full t)). Qed.

    Fact bfn_spec_2 t : exists n, bft_std (bfn t) = seq_an 0 n.
    Proof. apply is_seq_from_spec, (proj2_sig (bfn_full t)). Qed.

  End bfn.

End bfn.

Recursive Extraction bfn.

Check bfn.
Check bfn_spec_1.
Check bfn_spec_2.
             

