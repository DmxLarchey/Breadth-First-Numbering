Require Import Fin Arith Omega.

Definition finite (P : nat -> Prop) := exists m, forall n, P n -> n <= m.
Definition infinite (P : nat -> Prop) := forall n, exists m, n <= m /\ P m.

Fact infinite_mono (P Q : _ -> Prop) : (forall n, P n -> Q n) -> infinite P -> infinite Q.
Proof.
  intros H H1 n; destruct (H1 n) as (m & ?); firstorder.
Qed.

Fact infinite_not_finite P : infinite P -> ~ finite P.
Proof.
  intros H (m & Hm).
  destruct (H (S m)) as (n & H1 & H2).
  apply Hm in H2; omega.
Qed.

Fact finite_union n (f : Fin.t n -> nat -> Prop) : (forall p, finite (f p)) -> finite (fun n => exists i, f i n).
Proof. 
  revert f; induction n as [ | n IHn ]; intros f Hf.
  + exists 0; intros ? (p & _); revert p; apply Fin.case0.
  + destruct (IHn (fun p n => f (Fin.FS p) n)) as (m1 & H1); auto.
    destruct (Hf Fin.F1) as (m0 & H0).
    exists (m0+m1).
    intros i (p & Hp).
    revert Hp; apply (caseS' p).
    * intros H; generalize (H0 _ H); omega.
    * intros q H; generalize (H1 _ (ex_intro _ _ H)); omega.
Qed.

(* It is impossible to prove bPHP constructively *)

Definition iPHP := forall n (f : nat -> Fin.t n), exists p, infinite (fun n => f n = p).
Definition bPHP := forall f : nat -> bool, infinite (fun n => f n = true) \/ infinite (fun n => f n = false).

Section iPHP_bPHP.

  Theorem iPHP_bPHP : iPHP -> bPHP.
  Proof.
    intros H f.
    set (g (b : bool) := if b then @F1 1 else FS F1).
    destruct (H _ (fun n => g (f n))) as (p & Hp).
    revert Hp.
    apply (caseS' p).
    + intros H1; left. 
      revert H1; apply infinite_mono.
      intros n; destruct (f n); auto; simpl; discriminate.
    + clear p; intros p H1; right.
      revert H1; apply infinite_mono.
      intros n; destruct (f n); auto; simpl; discriminate.
  Qed.

  Let g n : Fin.t (S n) -> bool.
  Proof.
    intros p.
    pattern p.
    apply (caseS' p).
    + exact true.
    + intros _; exact false.
  Defined.

  Definition Fexist n (f : Fin.t n -> bool) : bool.
  Proof.
    induction n as [ | n IHn ].
    + exact false.
    + apply orb.
      * exact (f F1).
      * exact (IHn (fun p => f (FS p))).
  Defined.

  Let h n : Fin.t (S (S n)) -> Fin.t (S n).
  Proof.
    intro p.
    pattern p; apply (caseS' p).
    + exact F1.
    + exact (fun x => x).
  Defined.

  Theorem bPHP_iPHP : bPHP -> iPHP.
  Proof.
    intros H n.
    induction n as [ | [ | n ] IHn ]; intros f.
    + generalize (f 0); apply case0.
    + exists F1.
      intros n; exists n; split; auto.
      generalize (f n).
      intros p; apply (caseS' p); auto.
      apply case0.
    + destruct (IHn (fun n => h _ (f n))) as (p & Hp).
      revert Hp; apply (caseS' p); clear p.
      * intros H1.
        admit.
      * intros p Hp.
        exists (FS (FS p)); revert Hp.
        apply infinite_mono.
        intros q; generalize (f q); clear q.
        do 2 (intros q; apply (caseS' q); clear q; try discriminate).
        intros q; simpl; intro; f_equal; auto.
  Admitted.

End iPHP_bPHP.

Require Import Classical.

Section with_classic.

  Fact not_finite_infinite P : ~ finite P -> infinite P.
  Proof.
    intros H n.
    unfold finite in H.
    generalize (not_ex_all_not _ _ H n); intros H1.
    generalize (not_all_ex_not _ _ H1).
    intros (m & Hm); exists m.
    apply imply_to_and in Hm.
    destruct Hm; split; auto; omega.
  Qed. 

  Definition infinite_PHP : iPHP.
  Proof.
    intros n f; apply not_all_not_ex.
    intros H.
    destruct finite_union with (f := fun p n => f n = p) as (m & Hm).
    { intros p; specialize (H p).
      apply NNPP; contradict H; revert H; apply not_finite_infinite. }
    specialize (Hm (S m) (ex_intro _ _ eq_refl)); omega.
  Qed.

End with_classic.

  
       
   

   