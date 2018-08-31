Require Import Fin Arith Omega.

Check Fin.t.

Section finite.

  Definition finite (P : nat -> Prop) := exists m, forall n, P n -> n <= m.

  Fact finite_union n (f : Fin.t n -> nat -> Prop) : (forall p, finite (f p)) -> finite (fun n => exists i, f i n).
  Proof. 
    revert f; induction n as [ | n IHn ]; intros f Hf.
    + exists 0; intros ? (p & _); revert p; apply Fin.case0.
    + destruct (IHn (fun p n => f (Fin.FS p) n)) as (m1 & H1); auto.
      destruct (Hf Fin.F1) as (m0 & H0).
      exists (m0+m1).
      intros i (p & Hp).
      apply caseS in p.
       
   

   