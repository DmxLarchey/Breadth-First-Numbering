(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** This is an exercise about the infinite PHP, three versions
    which are constructively equivalent: bPHP, dPHP and iPHP

    for a predicate P : nat -> Prop, infinite means unbounded here

    bPHP states than given an (infinite) sequence of Boolean, it is
    possible to find which of true or false occurs infinitely often

    dPHP states that if the binary union out two decidable predicates
    is infinite then so is of them

    iPHP states that if f maps infinitely (nat) many pigeons into
    finitely many (Fin.t n) holes then one of the holes holds
    infinitely many pigeons

    It is impossible to prove bPHP purely constructively, and thus 
    iPHP or dPHP cannot be proved constructivelly either.

    See also http://math.andrej.com/2011/05/10/running-a-classical-proof-with-choice-in-agda/

*)

Require Import Fin Arith Omega Extraction.

Set Implicit Arguments.

Definition finite (P : nat -> Prop) := exists m, forall n, P n -> n <= m.
Definition infinite (P : nat -> Prop) := forall n, exists m, n <= m /\ P m.
Definition decidable (P : nat -> Prop) := forall n, { P n } + { ~ P n }.

Definition iPHP := forall n (f : nat -> Fin.t n), exists p, infinite (fun n => f n = p).
Definition bPHP := forall f : nat -> bool, infinite (fun n => f n = true) \/ infinite (fun n => f n = false).
Definition dPHP := forall P Q, decidable P -> decidable Q -> infinite (fun n => P n \/ Q n) -> infinite P \/ infinite Q.

Section nat_rev_ind.

  Variables (P : nat -> Prop)
            (HP : forall n, P (S n) -> P n).

  Theorem nat_rev_ind x y : x <= y -> P y -> P x.
  Proof. induction 1; auto. Qed.

End nat_rev_ind.

Fact infinite_mono (P Q : _ -> Prop) : (forall n, P n -> Q n) -> infinite P -> infinite Q.
Proof. intros H H1 n; destruct (H1 n) as (m & ?); firstorder. Qed.

Section decidable.

  Variable (P : nat -> Prop) (Pdec : decidable P).

  Fact decidable_bounded : decidable (fun n => exists k, k < n /\ P k).
  Proof.
    intro n; induction n as [ | n IHn ].
    + right; intros (? & ? & _); omega.
    + destruct (Pdec n) as [ H1 | H1 ].
      * left; exists n; split; auto.
      * destruct IHn as [ IHn | IHn ].
        - left; destruct IHn as (k & H2 & H3).
          exists k; split; auto.
        - right; intros (k & H2 & H3).
          destruct (eq_nat_dec k n).
          ++ subst; tauto.
          ++ apply IHn; exists k; split; auto; omega.
  Qed.   

  Fact find_max n : { m | m < n /\ P m /\ forall i, m < i < n -> ~ P i } + { forall i, i < n -> ~ P i }.
  Proof.
    induction n as [ | n IHn ].
    + right; intros; omega.
    + destruct (Pdec n) as [ H | H ].
      - left; exists n; repeat split; auto; intros; omega.
      - destruct IHn as [ (m & H1 & H2 & H3) | H1 ].
        * left; exists m; repeat split; auto.
          intros i H4.
          destruct (eq_nat_dec i n); subst; auto;
            apply H3; omega.
        * right; intros i Hi.
          destruct (eq_nat_dec i n); subst; auto;
            apply H1; omega.
  Qed.

  Let R n m := ~ P m /\ n = S m.

  Let umin_rec : forall n, Acc R n -> { m | n <= m /\ P m /\ forall k, P k -> k < n \/ m <= k }.
  Proof.
    refine (fix loop n Hn { struct Hn } := 
      match Pdec n with
        | left H => exist _ n _
        | right H => let (r,Hr) := loop (S n) _ in exist _ r _
      end).
    1,2 : cycle 1.
    + apply Acc_inv with (1 := Hn); split; auto.
    + repeat split; auto; intros; omega.
    + destruct Hr as (H1 & H2 & H3).
      repeat split; auto; try omega.
      intros k Hk; specialize (H3 _ Hk).
      destruct (eq_nat_dec n k).
      * subst; tauto.
      * omega.
  Qed.

  (* This is unbounded minimization of a decidable predicate *)

  Variables (n : nat) (Hn : exists m, n <= m /\ P m).

  Definition umin_dec : { m | n <= m /\ P m /\ forall k, n <= k -> P k -> m <= k }.
  Proof.
    refine (let (r,Hr) := @umin_rec n _ in exist _ r _).
    + destruct Hn as (m & H1 & H2); clear Hn.
      assert (Acc R m) as H3.
      { constructor; intros ? (? & _); tauto. }
      revert H3.
      apply nat_rev_ind; auto.
      intros k Hk; constructor.
      intros ? (_ & ?); subst; auto.
    + destruct Hr as (H1 & H2 & H3).
      repeat split; auto.
      intros k H4 H5; specialize (H3 _ H5); omega.
  Defined.

End decidable.

Definition sinc (f : nat -> nat) := forall n, f n < f (S n).
Definition smono (f : nat -> nat) := forall i j, i < j -> f i < f j.

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

Section infinite_enum.

  Variables (P : nat -> Prop) 
            (Pdec : decidable P)
            (Pinf : infinite P).

  (* We build a strictly monotonic enumeration of P (ienum) and its inversion (ienum_inv) *)

  Inductive g_enum : nat -> nat -> Prop :=
    | in_g_enum_0 : forall e0, P e0 -> (forall i, P i -> e0 <= i) -> g_enum 0 e0
    | in_g_enum_1 : forall n en eSn, g_enum n en -> en < eSn -> P eSn -> (forall i, en < i -> P i -> eSn <= i) -> g_enum (S n) eSn.

  Fact g_enum_fun n e1 e2 : g_enum n e1 -> g_enum n e2 -> e1 = e2.
  Proof.
    intros H1; revert H1 e2.
    induction 1 as [ n H1 H2 | n en r H1 IH1 H2 H3 H4 ]; inversion 1; subst.
    + apply le_antisym; auto.
    + apply IH1 in H5; subst en0.
      apply le_antisym; auto.
  Qed.

  Fixpoint ienum (n : nat) : nat.
  Proof.
    refine(match n with
          | 0   => proj1_sig (@umin_dec _ Pdec 0 _)
          | S n => proj1_sig (@umin_dec _ Pdec (S (ienum n)) _)
    end); apply Pinf.
  Defined.

  Fact ienum_spec n : g_enum n (ienum n).
  Proof.
    induction n as [ | n IHn ]; simpl.
    + generalize (proj2_sig (umin_dec Pdec (Pinf 0))); intros (H1 & H2 & H3).
      constructor; auto; intros i; apply H3; omega.
    + generalize (proj2_sig (umin_dec Pdec (Pinf (S (ienum n))))); intros (H1 & H2 & H3). 
      constructor 2 with (ienum n); auto.
  Qed.

  Theorem ienum_P n : P (ienum n).
  Proof. destruct n; simpl; apply (proj2_sig (umin_dec Pdec _)). Qed.

  Theorem ienum_zero : forall k, P k -> ienum 0 <= k.
  Proof. intro; apply (proj2_sig (umin_dec Pdec _)); omega. Qed.

  Hint Resolve ienum_spec.

  Theorem ienum_0_prop n : n = ienum 0 <-> P n /\ forall i, i < n -> ~ P i.
  Proof.
    split.
    + intros; subst; split.
      * apply ienum_P.
      * intros i H1 H2.
        apply ienum_zero in H2; omega.
    + intros (H1 & H2). 
      apply g_enum_fun with 0; auto.
      constructor; auto.
      intros i Hi. 
      destruct (le_lt_dec n i) as [ | C ]; auto.
      destruct (H2 _ C); auto.
  Qed.

  Theorem ienum_next n : ienum n < ienum (S n)
                      /\ forall k, ienum n < k -> P k -> ienum (S n) <= k.
  Proof.
    generalize (ienum (S n)) (ienum_spec (S n)).
    inversion 1; subst.
    rewrite (g_enum_fun (ienum_spec n) H1); auto.
  Qed.

  Fact ienum_S_le n k : k <= ienum (S n) <-> k <= ienum n \/ ienum n < k /\ forall i, ienum n < i < k -> ~ P i.
  Proof.
    split.
    * intros H.
      destruct (le_lt_dec k (ienum n)) as [ | H1 ]; auto.
      right; split; auto.
      generalize (ienum_next n); intros (H2 & H3) i Hi H4.
      apply H3 in H4; omega.
    * intros [ H1 | [ H1 H2 ] ].
      + apply le_trans with (1 := H1), lt_le_weak, ienum_next.
      + specialize (ienum_P (S n)); intros H3.
        generalize (ienum_next n); intros (H0 & _).
        destruct (le_lt_dec k (ienum (S n))) as [ H4 | H4 ]; auto.
        apply H2 in H3; omega.
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

  Fact ienum_inv_prop n m : n <= m -> (forall i, n <= i < m -> ~ P i) -> ienum_inv n = ienum_inv m.
  Proof.
    induction 1 as [ | m H IH ]; auto; intros H1.
    simpl.
    destruct (Pdec m) as [ H2 | H2 ].
    + apply H1 in H2; try tauto; omega.
    + apply IH; intros; apply H1; omega.
  Qed.

  Theorem ienum_inv_ienum n : ienum_inv (ienum n) = n.
  Proof.
    symmetry; induction n as [ | n IHn ].
    + apply (@ienum_inv_prop 0); try omega.
      intros i (_ & Hi); revert Hi.
      apply ienum_0_prop; auto.
    + simpl.
      generalize (proj1_sig (umin_dec Pdec (Pinf (S (ienum n)))))
                 (proj2_sig (umin_dec Pdec (Pinf (S (ienum n))))); intros m (H1 & H2 & H3).
      replace (S n) with (ienum_inv (S (ienum n))).
      2: simpl; rewrite <- IHn; generalize (ienum_P n); destruct (Pdec (ienum n)); auto; tauto.
      apply ienum_inv_prop; auto.
      intros i H4 H5.
      apply H3 in H5; omega.
  Qed.

  Theorem ienum_ienum_inv n : P n <-> n = ienum (ienum_inv n).
  Proof.
    induction n as [ n IHn ] using (well_founded_induction lt_wf); simpl.
    split.
    2: intros H; rewrite H; apply ienum_P.
    destruct n as [ | n ].
    + intros H.
      apply g_enum_fun with 0.
      * constructor; auto; intros; omega.
      * apply ienum_spec.
    + intros H.
      destruct (find_max Pdec (S n)) as [ (m & H1 & H2 & H3) | H1 ].
      * rewrite <- (ienum_inv_prop H1 H3); auto.
        simpl.  
        destruct (Pdec m) as [ _ | H4 ].
        2: tauto.
        rewrite IHn in H2; auto.
        generalize (ienum_next (ienum_inv m)).
        intros (H5 & H6).
        apply le_antisym.
        2: apply H6; auto; rewrite <- H2; auto.
        apply ienum_S_le; right.
        rewrite <- H2; auto.
      * rewrite <- (@ienum_inv_prop 0 (S n)); try omega.
        2: intros; apply H1; omega.
        simpl; apply ienum_0_prop; auto.
  Qed.

  Hint Resolve ienum_smono ienum_ienum_inv.

  Theorem infinite_dec_enum : { f | smono f /\ forall n, P n <-> exists k, n = f k }.
  Proof.
    exists ienum; split; auto.
    intros n; split.
    * exists (ienum_inv n); apply ienum_ienum_inv; auto.
    * intros (k & ?); subst; apply ienum_P.
  Qed.
    
End infinite_enum.

Section enum_infinite_dec.

  Variable (P : nat -> Prop)
           (f : nat -> nat) 
           (Hf1 : smono f)
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
      destruct (@decidable_bounded (fun k => n = f k)) with (n0 := S n)
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

(* Infinite (unbounded) and decidable predicates are exactly
   the direct images of strictly monotonic maps nat -> nat *)

Fact infinite_smono (P Q : _ -> Prop) f : 
      smono f -> (forall n, Q n -> P (f n)) -> infinite Q -> infinite P.
Proof.
  intros H1 H2 H3 n.
  destruct (H3 n) as (m & H4 & H5).
  apply H2 in H5.
  exists (f m); split; auto.
  apply le_trans with (1 := H4), smono_inc, H1.
Qed.

Fact infinite_not_finite P : infinite P -> ~ finite P.
Proof.
  intros H (m & Hm).
  destruct (H (S m)) as (n & H1 & H2).
  apply Hm in H2; omega.
Qed.

Fact finite_cup P Q : finite P -> finite Q -> finite (fun n => P n \/ Q n).
Proof.
  intros (p & Hp) (q & Hq); exists (p+q).
  intros n [ H | H ]; [ apply Hp in H | apply Hq in H ]; omega.
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

(** Equivalence between PHPs *)

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

Theorem bPHP_dPHP : bPHP -> dPHP.
Proof.
  intros H P Q Pdec Qdec IPQ.
  assert (decidable (fun n => P n \/ Q n)) as PQdec.
  { intros n; destruct (Pdec n); destruct (Qdec n); tauto. }
  generalize (ienum PQdec IPQ) (ienum_inv PQdec)  (ienum_smono PQdec IPQ)
             (ienum_inv_ienum PQdec IPQ) (ienum_ienum_inv PQdec IPQ). 
  intros f g Hf1 Hf2 Hf3.
  set (h n := if Pdec (f n) then true else false).
  destruct (H h) as [ H3 | H3 ].
  + left; revert H3; apply infinite_smono with (f := f); auto.
    intros n; unfold h; destruct (Pdec (f n)); try discriminate; tauto.
  + right; revert H3; apply infinite_smono with (f := f); auto.
    intros n; unfold h; destruct (Pdec (f n)); try discriminate.
    destruct (proj2 (Hf3  (f n))) as [ ? | ? ]; try tauto.
    rewrite Hf2; auto.
Qed.

Section dPHP_iPHP.

  Let g n : Fin.t (S n) -> bool.
  Proof.
    intros p.
    pattern p.
    apply (caseS' p).
    + exact true.
    + intros _; exact false.
  Defined.

  Let Fexist n (f : Fin.t n -> bool) : bool.
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

  Let Dec n (f : nat -> Fin.t n) p : decidable (fun n => f n = p).
  Proof. intro; apply Fin.eq_dec. Qed.

  Theorem bPHP_iPHP : dPHP -> iPHP.
  Proof.
    intros H n.
    induction n as [ | [ | n ] IHn ]; intros f.
    + generalize (f 0); apply case0.
    + exists F1.
      intros n; exists n; split; auto.
      generalize (f n).
      intros p; apply (caseS' p); auto.
      apply case0.
    + destruct (IHn (fun n => h (f n))) as (p & Hp).
      revert Hp; apply (caseS' p); clear p.
      * intros H1.
        assert (infinite (fun n => f n = F1) \/ infinite (fun n => f n = FS F1)) as H2.
        { apply H; auto; revert H1; apply infinite_mono.
          intros i; generalize (f i); clear i.
          repeat (intros p; apply (caseS' p); clear p; auto).
          intro; discriminate. }
        destruct H2; firstorder.
      * intros p Hp.
        exists (FS (FS p)); revert Hp.
        apply infinite_mono.
        intros q; generalize (f q); clear q.
        do 2 (intros q; apply (caseS' q); clear q; try discriminate).
        intros q; simpl; intro; f_equal; auto.
  Qed.

End dPHP_iPHP.

Local Hint Resolve iPHP_bPHP bPHP_dPHP bPHP_iPHP.

Theorem all_PHP : iPHP -> bPHP /\ bPHP -> dPHP /\ bPHP -> iPHP.
Proof. auto. Qed.

(** We can show PHPs with excluded middle (choice principle is not needed) *)

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

  Hint Resolve not_finite_infinite.

  Definition infinite_PHP : bPHP.
  Proof.
    intros f; apply NNPP.
    intros H; apply not_or_and in H.
    destruct H as (H1 & H2).
    assert (finite (fun n : nat => f n = true)) as H3.
    { apply NNPP; intro; contradict H1; auto. }
    assert (finite (fun n : nat => f n = false)) as H4.
    { apply NNPP; intro; contradict H2; auto. }
    generalize (finite_cup H3 H4).
    apply infinite_not_finite.
    intros n; exists n; destruct (f n); auto.
  Qed.

End with_classic.
