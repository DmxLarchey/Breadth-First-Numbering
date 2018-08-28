(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** small additions made by Ralph Matthes, CNRS, IRIT *)

Require Import List Arith Omega Wellfounded Permutation.

Require Import php.

Set Implicit Arguments.

Section measure_rect.

  Context  {X : Type} (m : X -> nat) (P : X -> Type)
            (HP : forall x, (forall y, m y < m x -> P y) -> P x).

  Let R x y := m x < m y.

  Fact Acc_measure : well_founded R.
  Proof. unfold R; apply wf_inverse_image, lt_wf. Qed.

  Theorem measure_rect : forall x, P x.
  Proof.
    intros x; generalize (Acc_measure x); revert x.
    refine (fix loop x (H : Acc R x) { struct H } : P x := @HP x (fun y Hy => loop y _)).
    destruct H as [ H ]; apply H; trivial.
  Qed.

End measure_rect.

Section map.

  Variables (X Y : Type) (f g : X -> Y).

  Fact map_ext_dep l : (forall x, In x l -> f x = g x) -> map f l = map g l.
  Proof. rewrite <- Forall_forall; induction 1; simpl; f_equal; auto. Qed.

  Fact map_ext : (forall x, f x = g x) -> (forall l, map f l = map g l).
  Proof. intros; apply map_ext_dep; auto. Qed.

End map.

Section length_split.

  Variable (X : Type).
  Implicit Type (ll : list X).

  Fact list_length_split n ll : { l : _ & { r | ll = l++r /\ length l = n } } + { length ll < n }.
  Proof.
    revert ll; induction n as [ | n IHn ].
    + left; exists nil, ll; auto.
    + intros [ | x ll ].
      * right; simpl; omega.
      * destruct (IHn ll) as [ (l & r & H1 & H2) | H1 ].
        - left; exists (x::l), r; split; subst; auto.
        - right; simpl; omega.
  Qed.

End length_split.

Section zip.

  Variable (X : Type) (f : X -> X -> X).

  Fixpoint zip l m : list X :=
    match l, m with
      | nil,  _    => m
      | _,    nil  => l
      | x::l, y::m => f x y :: zip l m
    end.

  Fact zip_fix_1 l : zip l nil = l.
  Proof. destruct l; auto. Qed.

  Fact zip_app l1 l2 m1 m2 : length l1 = length m1 -> zip (l1++l2) (m1++m2) = zip l1 m1 ++ zip l2 m2.
  Proof.
    revert m1; induction l1 as [| ? ? IH]; intros [|]; simpl; auto; try discriminate; intros; f_equal; apply IH; omega.
  Qed.


  Fact zip_app_left_le l1 l2 m x : length m <= length l1 -> In x l2 -> In x (zip (l1++l2) m).
  Proof.
    revert m; induction l1 as [ | y l1 IH ]; intros [ | z m ]; simpl; try omega.
    + rewrite zip_fix_1; intros; assumption.
    + right; apply in_or_app; simpl; auto.
    + intros H1 H2; right; apply IH; auto; omega.
  Qed.

  (** the obvious weakening to strict inequality *)
  Corollary zip_app_left l1 l2 m x : length m < length l1 -> In x l2 -> In x (zip (l1++l2) m).
  Proof.
    intros H1 H2.
    apply (zip_app_left_le l1 l2 m x).
    + omega.
    + assumption.
  Qed.

  Fact zip_app_right_le l m1 m2 x : length l <= length m1 -> In x m2 -> In x (zip l (m1++m2)).
  Proof.
    revert m1; induction l as [ | y l IH ]; intros [ | z m1 ]; simpl; try omega.
    + intros; assumption.
    + right; apply in_or_app; simpl; auto.
    + intros H1 H2; right; apply IH; auto; omega.
  Qed.

  (** the obvious weakening to strict inequality *)
  Corollary zip_app_right l m1 m2 x : length l < length m1 -> In x m2 -> In x (zip l (m1++m2)).
  Proof.
    intros H1 H2.
    apply (zip_app_right_le l m1 m2 x).
    + omega.
    + assumption.
  Qed.

  Fact zip_spec l m c : In c (zip l m) <-> (exists m1 m2, length l <= length m1 /\ m = m1++c::m2)
                                        \/ (exists l1 l2, length m <= length l1 /\ l = l1++c::l2)
                                        \/ (exists l1 x l2 m1 y m2, c = f x y /\ l = l1++x::l2 /\
                                                              m = m1++y::m2 /\ length l1 = length m1).
  Proof.
    split.
    + revert m; induction l as [ | x l IHl ]; simpl; intros m H.
      * apply in_split in H; destruct H as (m1 & m2 & ?); subst.
        left; exists m1, m2; split; auto; omega.
      * destruct m as [ | y m ]; destruct H as [ H | H ].
        - right; left; subst; exists nil, l; auto.
        - apply in_split in H; destruct H as (l1 & l2 & ?); subst.
          right; left; exists (x::l1), l2; split; auto; simpl; omega.
        - subst; right; right; exists nil, x, l, nil, y, m; simpl; auto.
        - destruct (IHl _ H) as [ (m1 & m2 & H1 & H2) 
                              | [ (l1 & l2 & H1 & H2) 
                                | (l1 & a & l2 & m1 & b & m2 & H1 & H2 & H3 & H4) ] ]; clear H IHl.
          ++ left; subst; exists (y::m1), m2; simpl; split; auto; omega.
          ++ right; left; subst; exists (x::l1), l2; simpl; split; auto; omega.
          ++ right; right; subst; exists (x::l1), a, l2, (y::m1), b, m2; simpl; auto.
    + intros [ (m1 & m2 & H1 & H2) 
           | [ (l1 & l2 & H1 & H2) 
             | (l1 & a & l2 & m1 & b & m2 & H1 & H2 & H3 & H4) ] ]; subst.
      * revert m1 H1; induction l as [ | x l IHl ]; simpl; intros m H1.
        - apply in_or_app; simpl; auto.
        - change (In c (zip (x :: l) (m ++ c :: m2))). destruct m; simpl in H1 |- *; try omega.
          right; apply IHl; omega.
      * revert l1 H1; induction m as [ | y m IHm ]; simpl; intros l H1.
        - rewrite zip_fix_1; apply in_or_app; simpl; auto.
        - destruct l; simpl in H1 |- *; try omega.
          right; apply IHm; omega.
      * revert m1 H4; induction l1; simpl; intros [] H1; simpl; try discriminate; auto.
  Qed.

  Variable (P : X -> Prop).

  Fact zip_monotone l m : Forall P l -> Forall P m -> (forall x y, In x l -> In y m -> P (f x y)) -> Forall P (zip l m).
  Proof. intros H; revert H m; do 2 (induction 1; simpl; auto). Qed.

End zip.

Section map_concat_zip.

  Variable (X Y : Type) (f : X -> Y) (g : X -> X -> X) (h : Y -> Y -> Y).

  (** the following expresses naturality of the monad multiplication [concat]: *)
  Fact map_concat (ll: list (list X)) : map f (concat ll) = concat (map (map f) ll).
  Proof. 
    induction ll; simpl; f_equal; auto.
    rewrite map_app; f_equal; auto.
  Qed.

  (** [f] is a "morphism" from [g] to [h]: *)
  Hypothesis Hgh : forall x y, f (g x y) = h (f x) (f y). 

  Fact map_zip l m : map f (zip g l m) = zip h (map f l) (map f m).
  Proof. revert m; induction l; intros [|]; simpl; f_equal; auto. Qed.

End map_concat_zip.

Fact map_zip_app X Y (f : X -> Y) (l m: list(list X)) :
    map (map f) (zip (@app _) l m) = zip (@app _) (map (map f) l) (map (map f) m).
Proof. apply map_zip; intros; apply map_app. Qed.

Fact In_concat_zip_app_left X (x : X) ll mm : In x (concat ll) -> In x (concat (zip (@app _) ll mm)).
Proof.
  intros H; revert H mm.
  induction ll as [ | l ll IH ]; simpl.
  + intros [].
  + intros H. change (forall mm, In x (concat (zip (app (A:=X)) (l::ll) mm))).
    apply in_app_or in H.
    destruct H as [ H | H ].
    * clear IH; intros []; simpl; try rewrite app_ass; apply in_or_app; tauto.
    * intros []; simpl; try rewrite app_ass; repeat (apply in_or_app; right; auto).
Qed.

Fact In_concat_zip_app_right X (x : X) ll mm : In x (concat mm) -> In x (concat (zip (@app _) ll mm)).
Proof.
  revert mm.
  induction ll as [ | l ll IH ]; simpl; auto.
  intros [ | m mm ]; simpl; intros H1; try tauto.
  rewrite app_ass; apply in_or_app; right.
  apply in_or_app.
  apply in_app_or in H1; firstorder.
Qed.

Section app.

  Variable X : Type.

  Fact split_In ll l (x : X) r : ll = l++x::r -> In x ll.
  Proof. intros; subst; apply in_or_app; simpl; auto. Qed.

  Fact in_concat_iff ll (x : X) : In x (concat ll) <-> exists l, In x l /\ In l ll.
  Proof.
    split.
    * induction ll as [ | l ll IH ]; simpl.
      - intros [].
      - intros H; apply in_app_or in H.
        destruct H as [ H | H ].
        + exists l; split; auto.
        + destruct IH as (l1 & ? & ?); auto; exists l1; auto.
   * intros (l & H1 & H2).
     apply in_split in H2.
     destruct H2 as (ll1 & ll2 & ?); subst.
     rewrite concat_app; apply in_or_app; simpl; right.
     apply in_or_app; simpl; auto.
  Qed.

End app.

Section Forall.

  Variable (X : Type) (R : X -> Prop).

  Fact Forall_app l m : Forall R l -> Forall R m -> Forall R (l++m).
  Proof. induction 1; simpl; auto. Qed.

  Fact Forall_map Y f l : Forall (fun y : Y => R (f y)) l -> Forall R (map f l).
  Proof. induction 1; constructor; auto. Qed.

End Forall.

Section Forall2.

  Variables (X Y : Type) (R : X -> Y -> Prop).

  Fact Forall2_length l m : Forall2 R l m -> length l = length m.
  Proof. induction 1; simpl; f_equal; auto. Qed.

  Fact Forall2_nil_inv_right l : Forall2 R nil l -> l = nil.
  Proof. inversion 1; auto. Qed.

  Fact Forall2_cons_inv x l y m : Forall2 R (x::l) (y::m) -> R x y /\ Forall2 R l m.
  Proof. inversion 1; auto. Qed.

  Fact Forall2_rev l m : Forall2 R l m -> Forall2 R (rev l) (rev m).
  Proof. induction 1; simpl; auto; apply Forall2_app; simpl; auto. Qed.
 
  Fact Forall2_app_inv l1 l2 m1 m2 : length l1 = length m1
                                  -> Forall2 R (l1++l2) (m1++m2)
                                  -> Forall2 R l1 m1 /\ Forall2 R l2 m2.
  Proof.
    revert m1; induction l1 as [ | x l1 IH ]; intros [ | y m1 ]; 
      try discriminate; simpl; intros H1 H2; auto.
    apply Forall2_cons_inv in H2.
    destruct H2; destruct (IH m1); auto.
  Qed.

  Fact Forall2_snoc_inv l x m y : Forall2 R (l++x::nil) (m++y::nil) -> R x y /\ Forall2 R l m.
  Proof.
    intros H.
    apply Forall2_rev in H.
    rewrite rev_app_distr, rev_app_distr in H; simpl in H.
    apply Forall2_cons_inv in H; destruct H as [ H1 H ]; split; auto.
    rewrite <- (rev_involutive l), <- (rev_involutive m); apply Forall2_rev; auto.
  Qed.

  Fact Forall2_2snoc_inv l a b m u v : Forall2 R (l++a::b::nil) (m++u::v::nil) 
                                    -> R a u /\ R b v /\ Forall2 R l m.
  Proof.
    replace (l++a::b::nil) with ((l++a::nil)++b::nil) by (rewrite app_ass; auto).
    replace (m++u::v::nil) with ((m++u::nil)++v::nil) by (rewrite app_ass; auto).
    intros H.
    apply Forall2_snoc_inv in H; destruct H as (H1 & H).
    apply Forall2_snoc_inv in H; tauto.
  Qed.

  Hint Resolve Forall2_app.

  Fact Forall2_concat (l: list(list X)) (m: list(list Y)) : Forall2 (Forall2 R) l m -> Forall2 R (concat l) (concat m).
  Proof. induction 1; simpl; auto. Qed.

  Fact Forall2_zip_app l1 l2 m1 m2 :
       Forall2 (Forall2 R) l1 m1
    -> Forall2 (Forall2 R) l2 m2
    -> Forall2 (Forall2 R) (zip (@app _) l1 l2) (zip (@app _) m1 m2).
  Proof. intros H; revert H l2 m2; do 2 (induction 1; simpl; auto). Qed.

  Fact Forall2_sym l m : Forall2 R l m -> Forall2 (fun y x => R x y) m l.
  Proof. induction 1; constructor; auto. Qed.
  
  Fact Forall2_In_inv_left l m x : Forall2 R l m -> In x l -> exists y, In y m /\ R x y.
  Proof. induction 1; intros []; subst; firstorder. Qed.    

End Forall2.

Tactic Notation "Forall2" "inv" hyp(H) "as" ident(E) :=
  match type of H with
    | Forall2 _ nil _ => apply Forall2_nil_inv_right in H; rename H into E
    | Forall2 _ (_::_) (_::_) => apply Forall2_cons_inv in H; destruct H as [ E H ]
    | Forall2 _ (_++_::nil) (_++_::nil) => apply Forall2_snoc_inv in H; destruct H as [ E H ]
    | Forall2 _ (_++_) (_++_) => apply Forall2_app_inv in H; [ destruct H as [ E H ] | ]
  end.

Fact Forall2_map_left X Y Z (f : X -> Y) (R : Y -> Z -> Prop) l m : 
     Forall2 (fun x z => R (f x) z) l m -> Forall2 R (map f l) m.
Proof. induction 1; simpl; auto. Qed.

Fact Forall2_mono X Y (R S : X -> Y -> Prop) l m : 
        (forall x y, R x y -> S x y)
     -> Forall2 R l m -> Forall2 S l m.
Proof. induction 2; auto. Qed.

Section sorted.

  Variable (X : Type) (R : X -> X -> Prop).

  Inductive sorted : list X -> Prop :=
    | in_sorted_0 : sorted nil
    | in_sorted_1 : forall x l, Forall (R x) l -> sorted l -> sorted (x::l).

  Fact sorted_app l m : (forall x y, In x l -> In y m -> R x y) -> sorted l -> sorted m -> sorted (l++m).
  Proof.
    intros H H1 Hm; revert H1 H.
    induction 1 as [ | x l H1 H2 IH2 ]; intros H3; simpl; auto.
    constructor.
    + apply Forall_app; auto.
      apply Forall_forall; intros; apply H3; simpl; auto.
    + apply IH2; intros; apply H3; simpl; auto.
  Qed.

  Variable (f : X -> X) (Hf : forall x y, R x y -> R (f x) (f y)).

  Fact sorted_map l : sorted l -> sorted (map f l).
  Proof.
    induction 1 as [ | x l H1 H2 IH2 ]; simpl; constructor; auto.
    apply Forall_forall.
    rewrite Forall_forall in H1.
    intros y; rewrite in_map_iff.
    intros (? & ? & ?); subst; auto.
  Qed.

End sorted.

Fact sorted_mono X (R S : X -> X -> Prop) l : (forall x y, In x l -> In y l -> R x y -> S x y) -> sorted R l -> sorted S l.
Proof.
  intros H1 H2; revert H2 H1.
  induction 1 as [ | x l H1 H2 IH2 ]; intros H3.
  + constructor.
  + constructor.
    * revert H1; do 2 rewrite Forall_forall.
      intros H1 y Hy; apply H3; simpl; auto.
    * apply IH2; intros ? ? ? ?; apply H3; simpl; auto.
Qed.

Section sorted_no_dup.
 
  Variables (X : Type) (R : X -> X -> Prop) (HR : forall x, ~ R x x).

  Lemma sorted_no_dup l : sorted R l -> ~ list_has_dup l.
  Proof.
    induction 1 as [ | x l H1 H2 IH2 ]; intros H.
    + inversion H.
    + apply list_hd_cons_inv in H.
      destruct H as [ H | H ]; try tauto.
      rewrite Forall_forall in H1; firstorder.
  Qed.

End sorted_no_dup.


Section no_dup_sorted_with_ineq.

  Variables (X : Type).
  Local Definition R := fun (x y: X) => x <> y.

  (** for this specific relation, not having duplicates is equivalent to being sorted: *)
  Lemma no_dup_sorted_with_ineq l: ~ list_has_dup l -> sorted R l.
  Proof.
    induction l as [ | x l IHl].
    - intros _. constructor.
    - intro H. constructor.
      + rewrite Forall_forall.
        intros y H1 Heq.
        subst.
        apply H.
        constructor 1; assumption.
      + apply IHl.
        intro H1; apply H.
        constructor 2; assumption.
  Qed.

End no_dup_sorted_with_ineq.

Section sorted_perm_aux.

  Variables (X : Type) (R S : X -> X -> Prop)
            (l m : list X) (Hl : ~ list_has_dup l) (Hm : ~ list_has_dup m)
            (Hlm : forall x, In x l <-> In x m).

  Lemma sorted_perm_aux : l ~p m.
  Proof.
    destruct (le_lt_dec (length l) (length m)) as [ H | H ].
    + destruct (@length_le_and_incl_implies_dup_or_perm _ l m) as [ C | C ]; auto.
      * intro; apply Hlm.
      * contradiction.
      * apply Permutation_sym; assumption.
    + destruct (@length_le_and_incl_implies_dup_or_perm _ m l) as [ C | C ]; auto.
      * omega.
      * intro; apply Hlm.
      * contradiction.
  Qed.

End sorted_perm_aux.

Section sorted_perm.

   Variables (X : Type) (R S : X -> X -> Prop)
             (HR : forall x, ~ R x x) (HS : forall x, ~ S x x)
             (l m : list X) (Hl : sorted R l) (Hm : sorted S m)
             (Hlm : forall x, In x l <-> In x m).
  Theorem sorted_perm : l ~p m.
  Proof.
    apply sorted_no_dup in Hl; try assumption.
    apply sorted_no_dup in Hm; try assumption.
    apply sorted_perm_aux; assumption.
  Qed.

End sorted_perm.

Section increase.
 
  Variable (X : Type) (P : nat -> X -> Prop).

  Inductive increase : nat -> list X -> Prop :=
    | in_increase_0 : forall n, increase n nil
    | in_increase_1 : forall n x l, P n x -> increase (S n) l -> increase n (x::l).

  Fact increase_inv n l x : increase n l -> In x l -> exists k, n <= k /\ P k x.
  Proof.
    intros H Hx; revert H; induction 1 as [ n | n y l H1 H2 IH2 ]; simpl.
    + destruct Hx.
    + destruct Hx as [ | Hx ]; subst.
      * exists n; split; auto.
      * destruct IH2 as (k & ? & ?); auto.
        exists k; split; auto; omega.
  Qed.

  Section zip.

     Variable (f : X -> X -> X) (Hf : forall n x y, P n x -> P n y -> P n (f x y)).

     Fact zip_increase l m n : increase n l -> increase n m -> increase n (zip f l m).
     Proof.
       intros H; revert H m.
       induction 1 as [ n | n x l H1 H2 IH2 ]; simpl; intros m Hm; auto.
       change (increase n (zip f (x::l) m)).
       destruct m as [ | y m ]; simpl.
       * constructor; auto.
       * constructor; inversion Hm; auto.
     Qed.

  End zip.

  Section map.

    Variable (f : X -> X) (Hf : forall n x, P n x -> P (S n) (f x)).

    Fact map_increase n l : increase n l -> increase (S n) (map f l).
    Proof. induction 1; simpl; constructor; auto. Qed.

  End map.

End increase.

Section sorted_concat.

  Variable (X : Type) (P : nat -> list X -> Prop) (R : X -> X -> Prop) 
           (HPR : forall i j x l y m, i < j -> P i l -> P j m -> In x l -> In y m -> R x y).

  Fact concat_sorted n ll : increase P n ll -> Forall (sorted R) ll -> sorted R (concat ll).
  Proof.
    induction 1 as [ n | n l ll H1 H2 IH2 ]; simpl.
    + constructor.
    + inversion 1; subst.
      apply sorted_app; auto.
      intros x y; rewrite in_concat_iff.
      intros G1 (m & G2 & G3).
      apply increase_inv with (2 := G3) in H2.
      destruct H2 as (k & H0 & H2).
      revert G1 G2; apply (@HPR n k); auto.
  Qed.

End sorted_concat.

