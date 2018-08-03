(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)


Require Import List Arith Omega Wellfounded.
Require Import utils bt bft.

Set Implicit Arguments.

Section map.

  Variables (X Y : Type) (f g : X -> Y).

  Fact map_ext l : (forall x, In x l -> f x = g x) -> map f l = map g l.
  Proof. rewrite <- Forall_forall; induction 1; simpl; f_equal; auto. Qed.

End map.

Section map_concat_zip.

  Variable (X Y : Type) (f : X -> Y) (g : X -> X -> X) (h : Y -> Y -> Y).

  Fact map_concat ll : map f (concat ll) = concat (map (map f) ll).
  Proof. 
    induction ll; simpl; f_equal; auto.
    rewrite map_app; f_equal; auto.
  Qed.

  Hypothesis Hgh : forall x y, f (g x y) = h (f x) (f y). 

  Fact map_zip l m : map f (zip g l m) = zip h (map f l) (map f m).
  Proof. revert m; induction l; intros [|]; simpl; f_equal; auto. Qed.

End map_concat_zip.

Section zip_app.

  Variable (X : Type).

(*
  Fact zip_app_left l m x u : In x u -> In u l -> In x (zip (@app X) l m).
  Proof.
    revert m; induction l as [ | y l IHl ]; intros [|]; simpl; try tauto.
    intros [|]; subst.
*)
End zip_app.

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

Section bt_branches.

  Variable X : Type.

  Unset Elimination Schemes.

  Inductive btb : list bool -> bt X -> Prop :=
    | in_btb_0 : forall t, btb nil t
    | in_btb_1 : forall l u x v, btb l u -> btb (false::l) (node u x v)
    | in_btb_2 : forall l u x v, btb l v -> btb (true::l)  (node u x v).

  Set Elimination Schemes.

  Scheme btb_ind := Induction for btb Sort Prop.

  Hint Constructors btb.

  Fact btb_inv_1 l u x v : btb (false::l) (node u x v) -> btb l u.
  Proof. inversion 1; trivial. Defined.

  Fact btb_inv_2 l u x v : btb (true::l) (node u x v) -> btb l v.
  Proof. inversion 1; trivial. Defined.

  (* The tree branches by Depth First Traversal *)

  Fixpoint dft_br (t : bt X) : list (list bool) :=
    nil::match t with 
           | leaf _     => nil
           | node u _ v => map (cons false) (dft_br u) ++ map (cons true) (dft_br v)
         end.

  (* branches t included in btb _ t *)

  Fact dft_br_spec_1 t : Forall (fun l => btb l t) (dft_br t).
  Proof.
    induction t as [ x | u Hu x v Hv ].
    + do 2 constructor.
    + simpl; constructor.
      * constructor.
      * apply Forall_app; apply Forall_map; [ revert Hu | revert Hv ]; 
          apply Forall_impl; auto.
  Qed.

  (* number of branches equals size of tree *)

  Fact dft_br_spec_2 t : length (dft_br t) = m_bt t.
  Proof. induction t; simpl; auto; rewrite app_length; repeat rewrite map_length; omega. Qed.

  Inductive lb_lex : list bool -> list bool -> Prop :=
    | in_lb_0 : forall l, lb_lex nil l
    | in_lb_1 : forall l m, lb_lex (false::l) (true::m)
    | in_lb_2 : forall b l m, lb_lex l m -> lb_lex (b::l) (b::m).

  Fact lb_lex_refl l : lb_lex l l.
  Proof. induction l; constructor; auto. Qed.

  Fact lb_lex_trans l m k : lb_lex l m -> lb_lex m k -> lb_lex l k.
  Proof.
    intros H; revert H k.
    induction 1 as [ l | l m | b l m H IH ]; intros k H1.
    + constructor.
    + inversion H1; constructor.
    + inversion H1; constructor; auto.
  Qed.

  Fact lb_lex_antisym l m : lb_lex l m -> lb_lex m l -> l = m.
  Proof. induction 1; inversion 1; f_equal; auto. Qed.

  Definition lb_lex_dec l m : { lb_lex l m } + { lb_lex m l }.
  Proof.
    revert m; induction l as [ | [] l IHl ]; intros m.
    + left; constructor.
    + destruct m as [ | [] m ].
      * right; constructor.
      * destruct (IHl m); [ left | right ]; constructor; auto.
      * right; constructor.
    + destruct m as [ | [] m ].
      * right; constructor.
      * left; constructor.
      * destruct (IHl m); [ left | right ]; constructor; auto.
  Qed.

  (* The Breadth First Search order between bt branches *)

  Definition bft_order l m := length l < length m \/ length l = length m /\ lb_lex l m.

  Fact bft_order_refl l : bft_order l l.
  Proof. right; split; auto; apply lb_lex_refl. Qed.

  Fact bft_order_antisym l m :  bft_order l m ->  bft_order m l -> l = m.
  Proof.
    intros [ | [] ] [ | [] ]; try omega.
    apply lb_lex_antisym; auto.
  Qed.

  Fact bft_order_trans l m k : bft_order l m -> bft_order m k -> bft_order l k.
  Proof.
    intros [ | [] ] [ | [] ]; try (left; omega).
    right; split; try omega.
    apply lb_lex_trans with m; auto.
  Qed.
 
  Definition bft_order_dec l m : { bft_order l m } + { bft_order m l }.
  Proof.
    destruct (le_lt_dec (length l) (length m)).
    2: right; left; auto.
    destruct (le_lt_dec (length m) (length l)).
    2: left; left; auto.
    destruct (lb_lex_dec l m).
    * left; right; split; auto; omega.
    * right; right; split; auto; omega.
  Qed.

  Fixpoint niveaux_br (t : bt X) : list (list (list bool)) :=
    match t with 
      | leaf _     => (nil::nil) :: nil
      | node a _ b => (nil::nil) :: zip (@app _) (map (map (cons false)) (niveaux_br a))
                                                 (map (map (cons true))  (niveaux_br b))
    end.

  Fact niveaux_br_spec_1 t : forall l ll, In l ll -> In ll (niveaux_br t) -> btb l t.
  Proof.
    induction t as [ x | u Hu x v Hv ]; simpl; intros l ll H1 H2.
    * destruct H2 as [ | [] ]; subst.
      destruct H1 as [ | [] ]; subst; constructor.
    * destruct H2 as [ | H2 ]; subst.
      + destruct H1 as [ | [] ]; subst; constructor.
      + rewrite zip_spec in H2.
        destruct H2 as [ (m1 & m2 & _ & H3)
                     | [ (m1 & m2 & _ & H3) 
                       | (l1 & a & l2 & m1 & b & m2 & H2 & H3 & H4 & H5) ] ].
        - apply split_In, in_map_iff in H3.
          destruct H3 as (ll1 & H3 & H4); subst.
          apply in_map_iff in H1.
          destruct H1 as (l1 & ? & H1); subst.
          constructor; apply Hv with (2 := H4); auto.
        - apply split_In, in_map_iff in H3.
          destruct H3 as (ll1 & H3 & H4); subst.
          apply in_map_iff in H1.
          destruct H1 as (l1 & ? & H1); subst.
          constructor; apply Hu with (2 := H4); auto.
        - apply split_In, in_map_iff in H3.
          apply split_In, in_map_iff in H4.
          destruct H3 as (ll1 & ? & H3); subst.
          destruct H4 as (ll2 & ? & H4); subst.
          apply in_app_or in H1.
          destruct H1 as [ H1 | H1 ]; apply in_map_iff in H1;
            destruct H1 as (l3 & ? & H1); subst.
          ** constructor; apply Hu with (2 := H3); auto.
          ** constructor; apply Hv with (2 := H4); auto.
  Qed.

  Fact niveaux_br_spec_0 l t : btb l t -> exists ll, In l ll /\ In ll (niveaux_br t).
  Proof.
    induction 1 as [ t | l u x v H (ll & H1 & H2) | m u x v H (mm & H1 & H2) ].
    + exists (nil::nil); destruct t; simpl; auto.
    + apply in_split in H2.
      destruct H2 as (u1 & u2 & H2).
      destruct (list_length_split (length u1) (niveaux_br v))
        as [ (v1 & [ | mm v2 ] & H3 & H4) | H3 ].
      - exists (map (cons false) ll); simpl; split.
        * apply in_map_iff; exists l; auto.
        * right; apply zip_spec.
          right; left; exists (map (map (cons false)) u1), (map (map (cons false)) u2).
          repeat rewrite map_length.
          rewrite H2, map_app, H3, <- app_nil_end, H4; simpl; auto.
      - exists (map (cons false) ll++map (cons true) mm); simpl; split.
        * apply in_or_app; left; apply in_map_iff; exists l; auto.
        * right; apply zip_spec; right; right.
          exists (map (map (cons false)) u1), (map (cons false) ll), (map (map (cons false)) u2),
                 (map (map (cons true)) v1), (map (cons true) mm), (map (map (cons true)) v2); repeat split; auto.
          ++ rewrite H2, map_app; auto.
          ++ rewrite H3, map_app; auto.
          ++ rewrite map_length, map_length; auto.
      - exists  (map (cons false) ll); simpl; split.
        * apply in_map_iff; exists l; auto.
        * right; rewrite H2, map_app; apply zip_app_left.
          ++ do 2 rewrite map_length; auto.
          ++ apply in_map; simpl; auto.
    + apply in_split in H2.
      destruct H2 as (v1 & v2 & H2).
      destruct (list_length_split (length v1) (niveaux_br u))
        as [ (u1 & [ | ll u2 ] & H3 & H4) | H3 ].
      - exists (map (cons true) mm); simpl; split.
        * apply in_map_iff; exists m; auto.
        * right; apply zip_spec.
          left; exists (map (map (cons true)) v1), (map (map (cons true)) v2).
          repeat rewrite map_length.
          rewrite H2, map_app, H3, <- app_nil_end, H4; simpl; auto.
      - exists (map (cons false) ll++map (cons true) mm); simpl; split.
        * apply in_or_app; right; apply in_map_iff; exists m; auto.
        * right; apply zip_spec; right; right.
          exists (map (map (cons false)) u1), (map (cons false) ll), (map (map (cons false)) u2),
                 (map (map (cons true)) v1), (map (cons true) mm), (map (map (cons true)) v2); repeat split; auto.
          ++ rewrite H3, map_app; auto.
          ++ rewrite H2, map_app; auto.
          ++ rewrite map_length, map_length; auto.
      - exists  (map (cons true) mm); simpl; split.
        * apply in_map_iff; exists m; auto.
        * right; rewrite H2, map_app; apply zip_app_right.
          ++ do 2 rewrite map_length; auto.
          ++ apply in_map; simpl; auto.
  Qed.

  Fact niveaux_br_spec l t : btb l t <-> exists ll, In l ll /\ In ll (niveaux_br t).
  Proof.
    split.
    + apply niveaux_br_spec_0.
    + intros (ll & H1 & H2); revert H1 H2; apply niveaux_br_spec_1.
  Qed.
  
  Fact niveaux_br_spec_2 t : increase (fun n ll => Forall (fun l => length l = n) ll) 0 (niveaux_br t).
  Proof.
    induction t as [ x | u Hu x v Hv ]; simpl.
    + do 2 constructor; auto.
    + constructor.
      * constructor; auto.
      * apply zip_increase.
        - intros; apply Forall_app; auto.
        - apply map_increase; auto. 
          intros l ll H; apply Forall_map; simpl.
          revert H; apply Forall_impl; intros; omega.
        - apply map_increase; auto. 
          intros l ll H; apply Forall_map; simpl.
          revert H; apply Forall_impl; intros; omega.
  Qed.

  Fact niveaux_br_spec_3 t : Forall (sorted lb_lex) (niveaux_br t).
  Proof.
    induction t as [ x | u Hu x v Hv ]; simpl.
    + repeat constructor.
    + constructor.
      * repeat constructor.
      * apply zip_monotone.
        - apply Forall_map; revert Hu; apply Forall_impl.
          intros; apply sorted_map; auto.
          intros; constructor; auto.
        - apply Forall_map; revert Hv; apply Forall_impl.
          intros; apply sorted_map; auto.
          intros; constructor; auto.
        - rewrite Forall_forall in Hu, Hv.
          intros ? ?; do 2 rewrite in_map_iff.
          intros (l & ? & H1) (m & ? & H2); subst.
          apply sorted_app.
          ++ intros c d; do 2 rewrite in_map_iff.
             intros (r & ? & ?) (s & ? & ?); subst; constructor.
          ++ apply sorted_map; auto.
             intros; constructor; auto.
          ++ apply sorted_map; auto.
             intros; constructor; auto.
  Qed. 

  Definition bft_br t : list (list bool) := concat (niveaux_br t).

  (* bft_br contains the branches of t *)

  Fact bft_br_spec_1 l t : In l (bft_br t) <-> btb l t.
  Proof. unfold bft_br; rewrite niveaux_br_spec, in_concat_iff; tauto. Qed.
 
  Hint Resolve niveaux_br_spec_2.

  (* The list of branches generated by bft_br is sorted according to bft_order *)

  Theorem bft_br_spec_2 t : sorted bft_order (bft_br t).
  Proof.
    apply concat_sorted with (P := fun n ll => Forall (fun l => length l = n) ll) (n := 0); auto.
    + intros i j x l y m; do 2 rewrite Forall_forall; intros H1 H2 H3 H4 H5.
      apply H2 in H4; apply H3 in H5.
      left; omega.
    + generalize (niveaux_br_spec_3 t).
      do 2 rewrite Forall_forall.
      intros H l Hl; generalize (H _ Hl).
      apply sorted_mono.
      intros x y H1 H2 H3; right; split; auto.
      generalize (niveaux_br_spec_2 t); intros H4.
      apply increase_inv with (2 := Hl) in H4.
      destruct H4 as (k & _ & H4).
      rewrite Forall_forall in H4.
      repeat rewrite H4; auto.
  Qed.

  Fixpoint in_bt (x : X) t :=
    match t with
      | leaf y => x = y
      | node u y v => x = y \/ in_bt x u \/ in_bt x v
    end.

  Hint Resolve btb_inv_1  btb_inv_2.

  Fixpoint btb_node (l : list bool) t : option X :=
    match l with
      | nil  => Some (root t)
      | b::l => match t with 
        | leaf _     => None
        | node u _ v => btb_node l (if b then v else u)
      end
    end.

  Fact btbn_fix_0 t : btb_node nil t = Some (root t).
  Proof. auto. Qed.

  Fact btbn_fix_1 b l x : btb_node (b::l) (leaf x) = None.
  Proof. auto. Qed.

  Fact btbn_fix_2 l u x v : btb_node (false::l) (node u x v) = btb_node l u.
  Proof. auto. Qed.

  Fact btbn_fix_3 l u x v : btb_node (true::l) (node u x v) = btb_node l v.
  Proof. auto. Qed.

  (* each node corresponding to a branch is in the tree *)

  Fact btbn_spec l t x : btb_node l t = Some x -> in_bt x t.
  Proof.
    revert t x.
    induction l as [ | [] ]; intros [|] ?; simpl; try discriminate.
    + inversion 1; auto.
    + inversion 1; auto.
    + intros G; apply IHl in G; tauto.
    + intros G; apply IHl in G; tauto.
  Qed.

  (* each value in a tree corresponds to some node of a branch *)

  Fact in_bt_inv x t : in_bt x t -> exists l, btb_node l t = Some x.
  Proof.
    induction t as [ y | u Hu y v Hv ]; simpl.
    + intros []; exists nil; auto.
    + intros [ [] | [ H | H ] ].
      - exists nil; auto.
      - destruct (Hu H) as (l & H1); subst; exists (false::l); auto.
      - destruct (Hv H) as (l & H1); subst; exists (true::l); auto.
  Qed.

  Fact niveaux_br_spec_4 t : map (map (@Some _)) (niveaux_tree t) = map (map (fun l => btb_node l t)) (niveaux_br t).
  Proof.
    induction t as [ x | u Hu x v Hv ]; simpl; f_equal; auto.
    rewrite map_zip with (h := @app _).
    2: intros; apply map_app.
    rewrite map_zip with (h := @app _).
    2: intros; apply map_app.
    rewrite Hu, Hv; repeat rewrite map_map; f_equal;
    apply map_ext; intros l _; rewrite map_map; apply map_ext; intros; simpl; auto.
  Qed.

  (* The list of nodes computed by bft_std is the direct map of the sorted list of branches,
     according to the bft_order *)

  Theorem bft_br_spec_3 t : map (@Some _) (bft_std t) = map (fun l => btb_node l t) (bft_br t).
  Proof. unfold bft_std, bft_br; rewrite map_concat, map_concat, niveaux_br_spec_4; auto. Qed.

End bt_branches.

Check bft_br_spec_1.
Check bft_br_spec_2.
Check bft_br_spec_3.