Set Implicit Arguments.

Section stream.

  Variable X Y : Type.

  Inductive bt : Type := leaf : X -> bt | node : bt -> X -> bt -> bt.

  CoInductive stream : Type := scons : X -> stream -> stream.

  Definition shead s : X := match s with scons x _ => x end.
  Definition stail s : X := match s with scons x _ => x end.

  Inductive sprefixed : list X -> stream -> Prop :=
    | in_sprefixed_0 : forall s, sprefixed nil s
    | in_sprefixed_1 : forall x l s, sprefixed l s -> sprefixed (x::l) (scons x s).

End stream.

Section queues.

 (** bfn (k :: ks) (leaf _) = 
      bfn (k :: ks) (node a _ b) = (1+k :: ks'', node a' k b')
        where (ks',a') = bfn (ks, a)
              (ks'',b') = bfn (ks',b) 

     let rec bfn (k :: ks) (node a _ b) = 
         let (ks',a')  = bfn (ks, a) in
         let (ks'',b') = bfn (ks',b) 
         in  (1+k :: ks'', node a' k b')
          
   *)

  Fixpoint bfn (s0 : stream nat) (t : bt unit) :=
    match s0, t with
      | scons n s, leaf _     => (s,leaf n)
      | scons n s, node a _ b => let (s1,a') := bfn s  a in
                                 let (s2,b') := bfn s1 b 
                                 in  (scons (S n) s2, node a' n b')
    end.



  CoInductive bisim : stream nat -> stream nat -> Prop :=
    | in_bisim : forall n s1 s2, bisim s1 s2 -> bisim (scons n s1) (scons n s2).

  CoFixpoint bfn_prop t s1 s2 : bisim s1 s2 -> bisim (fst (bfn s1 t)) (fst (bfn s2 t))
                                       /\ snd (bfn s1 t) = snd (bfn s2 t). 
  Proof.
    intros H.
    destruct s1; destruct s2; destruct t as [ x | a x b ]; simpl in *.
    + inversion H; assumption.
    + .
  Qed.
    induction 1.
    revert s1 s2.
    induction t as [ x | a Ha x b Hb ]; intros [ n1 s1 ] [ n2 s2 ] H; simpl in *.
    + f_equal; auto.
    + 
  Admitted.  

  Check bfn.

  Inductive bfnum_g : bt unit -> bt nat -> Prop :=
    | in_bfnum_g : forall s t t', bfn (scons 1 s) t = (s,t') -> bfnum_g t t'.


  Fact bfnum_g_fun t r1 r2 : bfnum_g t r1 -> bfnum_g t r2 -> r1 = r2.
  Proof.
    intros H; revert H r2.
    induction 1; inversion 1.

  Definition bfnum t := let (s,t') := bfn (scons 1 s) t in t'. 

End queues.

Require Import Extraction.

Extract Inductive prod => "(*)"  [ "(,)" ].
Recursive Extraction bfn.

Eval compute in bfn ( 
                    