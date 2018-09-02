Require Import Fin Arith Omega Extraction.

Section nat_rev_ind.

  Variables (P : nat -> Prop)
            (HP : forall n, P (S n) -> P n).

  Theorem nat_rev_ind x y : x <= y -> P y -> P x.
  Proof. induction 1; auto. Qed.

End nat_rev_ind.

Definition decidable (P : nat -> Prop) := forall n, { P n } + { ~ P n }.
Definition sinc (f : nat -> nat) := forall n, f n < f (S n).
Definition smono (f : nat -> nat) := forall i j, i < j -> f i < f j.

Fact decidable_bounded P : decidable P -> decidable (fun n => exists k, k < n /\ P k).
Proof.
  intros H n.
  induction n as [ | n IHn ].
  + right; intros (? & ? & _); omega.
  + destruct (H n) as [ H1 | H1 ].
    * left; exists n; split; auto.
    * destruct IHn as [ IHn | IHn ].
      - left; destruct IHn as (k & H2 & H3).
        exists k; split; auto.
      - right; intros (k & H2 & H3).
        destruct (eq_nat_dec k n).
        ++ subst; tauto.
        ++ apply IHn; exists k; split; auto; omega.
Qed.   

Fact smono_inc f : smono f -> forall n, n <= f n.
Proof.
  intros H.
  induction n as [ | n IHn ]; try omega.
  generalize (H n (S n)); intros; omega.
Qed.

Fact sinc_mono f : sinc f -> forall n m, n <= m -> f n <= f m.
Proof.
  intros H n m; induction 1 as [ | m H1 IH1 ]; auto.
  generalize (H m); intros; omega.
Qed.

Fact sinc_smono f : sinc f -> smono f.
Proof.
  intros H n m H1.
  apply lt_le_trans with (1 := H n).
  apply sinc_mono; auto.
Qed.

Section umin_dec.

  Variable (P : nat -> Prop) (Pdec : decidable P).

  Inductive umin_bar n : Prop :=
    | in_umb_0 : P n -> umin_bar n
    | in_umb_1 : umin_bar (S n) -> umin_bar n.

  Let umin_rec : forall n, umin_bar n -> { m | n <= m /\ P m /\ forall k, P k -> k < n \/ m <= k }.
  Proof.
    refine (fix loop n Hn { struct Hn } := 
      match Pdec n with
        | left H => exist _ n _
        | right H => let (r,Hr) := loop (S n) _ in exist _ r _
      end).
    1,2 : cycle 1.
    + inversion Hn; trivial; destruct H; trivial.
    
    + repeat split; auto; intros; omega.
    + destruct Hr as (H1 & H2 & H3).
      repeat split; auto; try omega.
      intros k Hk; specialize (H3 _ Hk).
      destruct (eq_nat_dec n k).
      * subst; tauto.
      * omega.
  Qed.

  Variables (n : nat) (Hn : exists m, n <= m /\ P m).

  Definition umin_dec : { m | n <= m /\ P m /\ forall k, n <= k -> P k -> m <= k }.
  Proof.
    refine (let (r,Hr) := umin_rec n _ in exist _ r _).
    + destruct Hn as (m & H1 & H2); clear Hn.
      generalize (in_umb_0 _ H2).
      apply nat_rev_ind; auto; apply in_umb_1.
    + destruct Hr as (H1 & H2 & H3).
      repeat split; auto.
      intros k H4 H5; specialize (H3 _ H5); omega.
  Defined.

End umin_dec.

Definition finite (P : nat -> Prop) := exists m, forall n, P n -> n <= m.
Definition infinite (P : nat -> Prop) := forall n, exists m, n <= m /\ P m.

Section infinite_enum.

  Variables (P : nat -> Prop) 
            (Pdec : decidable P)
            (Pinf : infinite P).

  Inductive g_enum : nat -> nat -> Prop :=
    | in_g_enum_0 : forall e0, P e0 -> (forall i, P i -> e0 <= i) -> g_enum 0 e0
    | in_g_enum_1 : forall n en eSn, g_enum n en -> en < eSn -> P eSn -> (forall i, en < i -> P i -> eSn <= i) -> g_enum (S n) eSn.

  Section def.

    Let ienum_rec : forall n, sig (g_enum n).
    Proof.
      refine (fix ienum n := match n with
          | 0   => let (r,Hr) := umin_dec _ Pdec 0 _ in exist _ r _
          | S n => let (en,Hen) := ienum n in 
                   let (r,Hr) := umin_dec _ Pdec (S en) _
                   in  exist _ r _
        end).
      1,3 : apply Pinf.
      + destruct Hr as (H1 & H2 & H3).
        constructor; auto.
        intro; apply H3; omega.
      + destruct Hr as (H1 & H2 & H3).
        constructor 2 with en; auto.
    Qed.

    Definition ienum n := proj1_sig (ienum_rec n).

    Fact ienum_spec n : g_enum n (ienum n).
    Proof. apply (proj2_sig _). Qed.

  End def.

  Fact g_enum_fun n e1 e2 : g_enum n e1 -> g_enum n e2 -> e1 = e2.
  Proof.
    intros H1; revert H1 e2.
    induction 1 as [ n H1 H2 | n en r H1 IH1 H2 H3 H4 ]; inversion 1; subst.
    + apply le_antisym; auto.
    + apply IH1 in H5; subst en0.
      apply le_antisym; auto.
  Qed.

  Theorem ienum_P n : P (ienum n).
  Proof.
    generalize (ienum n) (ienum_spec n).
    induction 1; auto.
  Qed.

  Theorem ienum_zero : forall k, P k -> ienum 0 <= k.
  Proof.
    generalize (ienum 0) (ienum_spec 0).
    inversion 1; auto.
  Qed.

  Theorem ienum_next n : ienum n < ienum (S n)
                      /\ forall k, ienum n < k -> P k -> ienum (S n) <= k.
  Proof.
    generalize (ienum (S n)) (ienum_spec (S n)).
    inversion 1; subst.
    rewrite (g_enum_fun _ _ _ (ienum_spec n) H1); auto.
  Qed.

  Theorem ienum_smono : smono ienum.
  Proof.
    apply sinc_smono; red.
    apply ienum_next.
  Qed.

  Fixpoint ienum_inv n := 
    match n with 
      | 0   => 0
      | S n => if Pdec n then S (ienum_inv n) else ienum_inv n
    end.

 
   (*

  ---* ienum 0 = 3
       ienum_inv 2 = 0
       ienum_inv 3 = 0
       ienum_inv 4 = 1 

   *)

  Theorem ienum_prop n : P n <-> n = ienum (ienum_inv n).
  Proof.
    induction n as [ n IHn ] using (well_founded_induction lt_wf); simpl.
    split.
    2: intros H; rewrite H; apply ienum_P.
    destruct n as [ | n ].
    + intros H.
      apply g_enum_fun with 0.
      * constructor; auto; intros; omega.
      * apply ienum_spec.
    + simpl; intros H.
      destruct (Pdec n) as [ H1 | H1 ].
      * rewrite IHn in H1; auto.
        generalize (ienum_next (ienum_inv n)).
        intros (H2 & H3).
        apply le_antisym.
        - rewrite H1 at 1; apply H2.
        - apply H3; auto.
          rewrite <- H1; auto.
      * admit.
  Admitted.

  Hint Resolve ienum_smono ienum_prop.

  Theorem infinite_dec_enum : { f | smono f /\ forall n, P n <-> exists k, n = f k }.
  Proof.
    exists ienum; split; auto.
    intros n; split.
    * exists (ienum_inv n); apply ienum_prop; auto.
    * intros (k & ?); subst; apply ienum_P.
  Qed.
    
End infinite_enum.

Fact infinite_mono (P Q : _ -> Prop) : (forall n, P n -> Q n) -> infinite P -> infinite Q.
Proof.
  intros H H1 n; destruct (H1 n) as (m & ?); firstorder.
Qed.

Section enum_infinite_dec.

  Variable (P : nat -> Prop) (f : nat -> nat) (Hf1 : smono f)
           (Hf2 : forall n, P n <-> exists k, n = f k).

  Theorem enum_infinite_dec : infinite P * decidable P.
  Proof.
    split.
    * apply infinite_mono with (P := fun n => exists k, n = f k).
      + intro; apply Hf2.
      + intros n; exists (f n); split.
        - apply smono_inc; auto.
        - exists n; auto.
    * intros n.
      destruct (decidable_bounded (fun k => n = f k)) with (n0 := S n)
        as [ H | H ].
      + intro; apply eq_nat_dec.
      + left; apply Hf2.
        destruct H as (k & _ & ?); exists k; auto.
      + right; contradict H.
        apply Hf2 in H.
        destruct H as (k & ?); subst.
        exists k; split; auto.
        apply le_n_S, smono_inc; auto.
  Qed.

End enum_infinite_dec.

Check infinite_dec_enum.
Check enum_infinite_dec.

Fact infinite_smono (P : _ -> Prop) f : infinite P 
                                    -> smono f 
                                    -> (forall n, P (f n))
                                    -> infinite (fun n => P n /\ exists k, n = f k).
Proof.
  intros H1 H2 H3 n.
  destruct (H1 n) as (m & H4 & H5).
  exists (f m); repeat split; auto.
  + generalize (smono_inc _ H2 m); omega.
  + exists m; auto.
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
Definition dPHP := forall P Q, decidable P -> decidable Q -> infinite (fun n => P n \/ Q n) -> infinite P \/ infinite Q.

Section bPHP_dPHP.
  
  Theorem bPHP_dPHP : bPHP -> dPHP.
  Proof.
    intros H0 P Q HP1 HQ1 H1.
    assert (decidable (fun n => P n \/ Q n)) as H2.
    { intros n; destruct (HP1 n); destruct (HQ1 n); tauto. }
    generalize (ienum _ H2 H1) (ienum_smono _ H2 H1) (ienum_prop _ H2 H1); intros f Hf1 Hf2.
    set (g n := if HP1 (f n) then true else false).
    destruct (H0 g) as [ H3 | H3 ].
    + left.
      Check (infinite_smono _ _ H3 Hf1).
      revert H3; apply infinite_mono.
      intros n; unfold g.
      destruct (HP1 (f n)).

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

  
       
   

   