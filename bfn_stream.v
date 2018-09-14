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
Require Import list_utils wf_utils bt bft fifo.

Set Implicit Arguments.

Section seq_an.

  (* seq_an a n = [a;a+1;...;a+(n-1)] *)

  Fixpoint seq_an a n : list nat :=
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

End seq_an.

Section streams.

  Variable X : Type.

  CoInductive stream := in_stream : X -> stream -> stream.

  Fixpoint take n s := 
    match n with 
      | 0   => nil
      | S n => match s with in_stream x s => x::take n s end
    end.

  Fixpoint leave n s := 
    match n with 
      | 0   => s
      | S n => match s with in_stream _ s => leave n s end
    end.

  Definition shead s := match s with in_stream x _ => x end.
  Definition stail s := match s with in_stream _ s => s end.

  Fixpoint prefix l s :=
    match l with 
      | nil  => True
      | x::l => match s with in_stream y s => x = y /\ prefix l s end
    end.

End streams.

Section bfn_stream.

  Variable X : Type.

  Implicit Type (t : bt X) (s : stream nat).

  CoFixpoint cst (x : X) := in_stream x (cst x).

  Fixpoint bfn t s { struct t } : bt nat * stream nat :=
    match s with
      | in_stream k s => 
      match t with 
        | leaf x     => (leaf k, in_stream (S k) s)
        | node a x b => let (a',s')  := bfn a s  in
                        let (b',s'') := bfn b s' 
                        in  (node a' k b',in_stream (S k) s'')
      end
    end.

  Definition sfst s := match s with in_stream x _ => x end.
  Definition ssnd s := match s with in_stream _ s => s end.

  (* I should be able to write this but Coq does not type-check the
     nested co-recursive call *)

  Fixpoint bfn_2 t s : stream nat := in_stream (S (sfst s)) (match t with 
        | leaf _     => s
        | node a _ b => bfn_2 b (bfn_2 a s)
      end).

  CoFixpoint s t := bfn_2 t (in_stream 1 (s t)).

  

  Section test.
    
    Variable t : bt X.

    

   
  
  Definition label t :=
    cofix s := snd (bfn t (in_stream 1 s)).
    let (t',s) := bfn t (in_stream 1 s) in t'.
        prefix (first_available (shead s) t) s
    ->  { c : 

  Variable P : bt X -> stream nat -> stream nat -> Prop.

  Fixpoint cumul k l := 
    match l with 
      | nil  => nil
      | x::l => k::cumul (x+k) l
    end.

  Definition first_available k t := cumul k (map (@length _) (niveaux_tree t)). 

  Fixpoint bfn_stream t s { struct t } : 
        prefix (first_available (shead s) t) s
    ->  { c : bt nat * stream nat | 
          let (t',s') := c in t ~t t' /\ s' = stail s }.
  Proof.
    intros H.
    destruct s as [ k s ]; simpl in *.
    destruct t as [ x | a x b ]; simpl in *.
    + exists (leaf k, in_stream (S k) s); simpl.
      split; auto.
      split.
      * unfold bft.
        rewrite bft_f_fix_3; simpl.
        rewrite bft_f_fix_0; auto.
      * admit.
    + destruct (bfn_stream a s) as ( (a',s') & H1 & H2 & H3).
      destruct (bfn_stream b s') as ( (b',s'') & H4 & H5 & H6).
      exists (node a' k b', in_stream (S k) s'').
      split; auto.
      split.
      * unfold bft.
        rewrite bft_f_fix_3; simpl.
        f_equal.
        rewrite bft_f_fix_3; simpl.
simpl.
     
 
