(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             Ralph Matthes [+]                              *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                             [*] Affiliation IRIT -- CNRS   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega Wellfounded Extraction.

Set Implicit Arguments.

(* This is largely obsolete and replaced by llist.v and fifo.v *)

Section llist.

  (* G54DTP Dependently Typed Programming.
    Introduction to coinductive types.
    Venanzio Capretta, March 2011.
  *)

  Variable X : Type.

  CoInductive llist : Type :=
    | lnil: llist
    | lcons: X -> llist -> llist.

  (* We must define an explicit unfold operation. *)

  Definition lunfold (l : llist) : llist :=
    match l with
      | lnil => lnil
      | lcons a l' => lcons a l'
    end.
 
  (* The next function unfolds a lazy list several times:
     the natural number n says how many.
  *)

  Fixpoint lunfold_many (l:llist) n : llist :=
    match n with
      | O    => l
      | S n => match l with
          | lnil      => lnil
          | lcons a l => lcons a (lunfold_many l n)
          end
    end.

  (* We can prove that the unfolding is equal to the original list. *)

  Lemma lunfold_many_eq: forall n (l:llist), l = lunfold_many l n.
  Proof.
    induction n as [ | n IHn ].
    + trivial.
    + intros [ | x l ].
      * trivial.
      * simpl; f_equal; auto.
  Qed.

  (* Every finite list can be transformed into a lazy list. *)

  Fixpoint list_llist l : llist :=
    match l with
      | nil  => lnil
      | a::l => lcons a (list_llist l)
    end.
    
  Fact list_llist_inj l m : list_llist l = list_llist m -> l = m.
  Proof.
    revert m; induction l as [ | x l IHl ]; intros [ | y m ]; auto; try discriminate.
    simpl; intros H; inversion H; f_equal; auto.
  Qed.
    
  Inductive lfin : llist -> Prop :=
    | lfin_lnil :  lfin lnil
    | lfin_lcons : forall a l, lfin l -> lfin (lcons a l).
    
  Fact lfin_inv a l : lfin (lcons a l) -> lfin l.
  Proof. inversion 1; assumption. Defined.

  Section llist_list.

    Let llist_list_rec : forall l, lfin l -> { m | l = list_llist m }.
    Proof.
      refine (fix loop l Hl { struct Hl } := 
        match l as l' return lfin l' -> { m | l' = list_llist m } with
          | lnil      => fun H => exist _ nil _
          | lcons x l => fun H => let (r,Hr) := loop l _ in exist _ (x::r) _
        end Hl); subst; trivial.
      inversion H; trivial.
    Qed.
  
    Definition llist_list l Hl := proj1_sig (@llist_list_rec l Hl).
  
    Fact llist_list_spec l Hl : l = list_llist (@llist_list l Hl).
    Proof. apply (proj2_sig (@llist_list_rec l Hl)). Qed.

  End llist_list.
  
  Arguments llist_list : clear implicits.
  
  Fact llist_list_fix_0 H : llist_list lnil H = nil.
  Proof.
    generalize (llist_list_spec H); simpl.
    generalize (llist_list _ H).
    intros [|]; try discriminate; auto.
  Qed.
  
  Fact llist_list_fix_1 x l H : llist_list (lcons x l) H = x::llist_list l (lfin_inv H).
  Proof.
    generalize (llist_list_spec H); simpl.
    generalize (llist_list _ H).
    intros [|]; try discriminate.
    simpl.
    intros G; inversion G; f_equal; auto.
    apply list_llist_inj; rewrite <- H2.
    apply llist_list_spec.
  Qed.

  Definition lfin_length l Hl := length (llist_list l Hl).

  Arguments lfin_length : clear implicits.
  
  Fact lfin_length_fix_0 H : lfin_length lnil H = 0.
  Proof. unfold lfin_length; rewrite llist_list_fix_0; auto. Qed.
  
  Fact lfin_length_fix_1 x l H : lfin_length (lcons x l) H = S (lfin_length l (lfin_inv H)).
  Proof. unfold lfin_length; rewrite llist_list_fix_1; auto. Qed.
  
End llist.

Arguments lnil {X}.
Arguments llist_list {X}.
Arguments lfin_length {X}.

Recursive Extraction llist_list list_llist.

Section Rotate.

  (* Rotate with lazy lists (with a non-informative "finiteness" predicate 
     It seems the algorithm manipulates f a as lazy lists and r as a list ... no sure
     or three lazy lists ? *)

  Variable (X : Type).
  
  Implicit Type (f r : llist X) (a : list X).
  
  Let prec  f Hf r Hr := lfin_length r Hr = 1 + lfin_length f Hf.
  Let rspec f Hf r Hr a m := m = llist_list f Hf++rev (llist_list r Hr)++a.
  
  Fixpoint rotate f r a (Hf : lfin f) (Hr : lfin r) { struct Hf } : @prec f Hf r Hr -> sig (@rspec f Hf r Hr a). 
  Proof.
    revert Hr.
    refine (match r as r' return forall (Hr : lfin r'), @prec f Hf _ Hr  -> sig (@rspec f Hf r' Hr a) with
      | lnil       => _
      | lcons y r' => _ 
    end); intros Hr' H.
    { exfalso.
      red in H.
      rewrite lfin_length_fix_0 in H; discriminate. }
    revert Hf H.
    refine (match f as f' return forall (Hf' : lfin f'), @prec f' Hf' _ Hr' -> sig (rspec Hf' Hr' a) with
      | lnil       => _
      | lcons x f' => _
    end); intros Hf' H.
    + exists (y::a).
      red in H |- *; revert H.
      rewrite llist_list_fix_0, llist_list_fix_1, lfin_length_fix_0, lfin_length_fix_1.
      destruct r'.
      * rewrite llist_list_fix_0; trivial.
      * rewrite lfin_length_fix_1; discriminate.
    + refine (let (ro,Hro) := rotate f' r' (y::a) (lfin_inv Hf') (lfin_inv Hr') _ in exist _ (x::ro) _).
      * red in H |- *; revert H.
        repeat rewrite lfin_length_fix_1; intros; omega.
      * red in Hro |- *; revert Hro.
        repeat rewrite llist_list_fix_1; intros; subst.
        simpl; rewrite app_ass; auto.
  Defined.

End Rotate.

Recursive Extraction rotate.

Record queue (X : Type) : Type := 
  { Q : Type;
    queue_list  : Q -> list X;
    queue_empty : Q -> bool;
    queue_enq   : Q -> X -> Q;
    queue_deq   : forall q, queue_empty q = false -> X * Q;
    
    queue_empty_spec : forall q, queue_empty q = true <-> queue_list q = nil;
    queue_enq_spec : forall q x, queue_list (queue_enq q x) = queue_list q ++ x :: nil;
    queue_deq_spec : forall q D, let (x,q') := @queue_deq q D in queue_list q = x :: queue_list q' 
   }.

Section Queues.

  (* Where deq(ueue) is implemented as a partial function *)

  Variable (X : Type).
  
  Definition queue_pair := (list X * list X)%type.
  
  Implicit Type q : queue_pair.
  
  Definition queue_length q := let (l,m) := q in length l + length m.
  Definition enq q x := let (l,m) := q in (x::l,m).
  
  Inductive g_deq : queue_pair -> X * queue_pair -> Prop :=
    | in_g_deq_0 : forall l r, l <> nil -> g_deq (nil,rev l) r -> g_deq (l,nil) r
    | in_g_deq_1 : forall l x m, g_deq (l,x::m) (x,(l,m)).
    
  Let R q1 q2 :=
    match q1, q2 with
      | (l1,m1), (l2,m2) => m2 = nil /\ l1 = nil /\ length m1 = length l2
    end.
    
  Let Acc_R q : Acc R q <-> q <> (nil,nil).
  Proof.
    split.
    * induction 1 as [ ([ | x l ],[ | y m ]) H IH ]; try discriminate.
      apply IH; red; simpl; auto.
    * revert q.
      assert (forall l m, m <> nil -> Acc R (l,m)) as H.
      { intros l2 m2 H.
        constructor.
        intros (l1,m1) (? & _); destruct H; auto. }
      intros (l,[ | y m ]) H1.
      + destruct l as [ | x l ].
        - destruct H1; auto.
        - constructor.
          intros (l1,m1); simpl.
          intros (_ & _ & E); apply H.
          destruct m1; discriminate.
      + apply H; discriminate.
  Qed.

  Let deq_rec : forall q, Acc R q -> sig (g_deq q).
  Proof.
    refine (fix loop q Hq { struct Hq } := _).
    revert Hq.
    refine (match q with (l,m) => _ end); clear q.
    refine(match m with
        | nil  => _
        | x::m' => fun _ => exist _ (x,(l,m')) _
      end); clear m.
    2: constructor.
    intros H.
    refine (match l as l' return l = l' -> sig (g_deq (l',nil)) with
        | nil   => fun E => _
        | x::l' => fun E => _
    end eq_refl).
    * exfalso; subst.
      apply Acc_R in H; destruct H; auto.
    * refine (let (r,Hr) := loop (nil,rev l) _ in exist _ r _).
      + destruct H as [ H ].
        apply H; simpl; rewrite rev_length; auto.
      + rewrite <- E; constructor 1; auto.
        subst; discriminate.
  Qed.
  
  Definition deq q Hq := proj1_sig (@deq_rec q (proj2 (@Acc_R q) Hq)).
  
  Arguments deq q Hq : clear implicits.
  
  Fact deq_spec q Hq : g_deq q (deq q Hq).
  Proof. apply (proj2_sig _). Qed.
  
  Definition queue_eq (q1 q2 : queue_pair) :=
    match q1, q2 with (l1,m1), (l2,m2) => m1++rev l1 = m2++rev l2 end.
    
  Infix "~q" := queue_eq (at level 70, no associativity).
  
  Fact queue_eq_refl q : q ~q q.
  Proof.
    revert q; intros []; red; auto.
  Qed.
  
  Fact queue_eq_sym q1 q2 : q1 ~q q2 -> q2 ~q q1.
  Proof.
    revert q1 q2; intros (l1,m1) (l2,m2); simpl.
    symmetry; auto.
  Qed.
  
  Fact queue_eq_trans q1 q2 q3 : q1 ~q q2 -> q2 ~q q3 -> q1 ~q q3.
  Proof.
    revert q1 q2 q3; intros (l1,m1) (l2,m2) (l3,m3); simpl.
    intros H; rewrite H; auto.
  Qed.
  
  Fact queue_eq_nil q1 q2 : q1 ~q q2 -> q1 = (nil,nil) -> q2 = (nil,nil).
  Proof.
    revert q1 q2; intros (l1,m1) (l2,m2); simpl.
    destruct m1; try discriminate.
    intros H1; injection 1; intros; subst l1.
    destruct m2; try discriminate.
    simpl in H1.
    rewrite <- (rev_involutive l2), <- H1; auto.
  Qed.
  
  Fact queue_neq_nil q1 q2 : q1 ~q q2 -> q1 <> (nil,nil) -> q2 <> (nil,nil).
  Proof.
    intros H1 H2; contradict H2; revert H2; apply queue_eq_nil.
    apply queue_eq_sym; auto.
  Qed.
  
  Fact queue_eq_length q1 q2 : q1 ~q q2 -> queue_length q1 = queue_length q2.
  Proof.
    revert q1 q2; intros (l1,m1) (l2,m2); simpl; intros H.
    apply f_equal with (f := @length _) in H.
    rewrite app_length, rev_length, plus_comm in H.
    rewrite H, app_length, rev_length, plus_comm; auto.
  Qed.
  
  Fact enq_eq q1 q2 x : q1 ~q q2 -> enq q1 x ~q enq q2 x.
  Proof.
    revert q1 q2; intros (l1,m1) (l2,m2); simpl; intros H.
    rewrite <- app_ass, H, app_ass; auto.
  Qed.
  
  Definition queue_pair_list q := let (l,m) := q in m++rev l.
  
  Fact queue_norm q : q ~q (nil,queue_pair_list q).
  Proof. destruct q; red; simpl; rewrite <- app_nil_end; auto. Qed.
  
  Fact queue_norm_uniq m1 m2 : (nil,m1) ~q (nil,m2) -> m1 = m2.
  Proof.
    simpl; repeat rewrite <- app_nil_end; auto.
  Qed.
  
  Fact queue_eq_list q1 q2 : q1 ~q q2 -> queue_pair_list q1 = queue_pair_list q2.
  Proof.
    revert q1 q2; intros (l1,m1) (l2,m2); simpl; auto.
  Qed.
  
  Fact g_deq_eq q1 q2 r1 r2 : q1 ~q q2 
                           -> g_deq q1 r1 
                           -> g_deq q2 r2 
                           -> fst r1 = fst r2 
                           /\ snd r1 ~q snd r2.
  Proof.
    intros H1 H2 H3; revert H2 H3 H1.
    induction 1 as [ l1 r1 H1 H2 IH2 | l1 x1 m1 ].
    * intros G1 G2; apply IH2; auto.
      apply queue_eq_trans with (2 := G2).
      red; simpl; rewrite <- app_nil_end; auto.
    * simpl fst; simpl snd.  
      induction 1 as [ l2 r2 G1 G2 IG2 | l2 x2 m2 ]; simpl; intros H.
      + intros; apply IG2; simpl.
        rewrite <- app_nil_end; auto.
      + inversion H; split; auto.
  Qed.
  
  Fact deq_eq q1 q2 D1 D2 : q1 ~q q2 -> fst (deq q1 D1) =  fst (deq q2 D2) 
                                     /\ snd (deq q1 D1) ~q snd (deq q2 D2).
  Proof.
    intros; apply g_deq_eq with q1 q2; auto; apply deq_spec.
  Qed.
  
  Fact deq_fix_fst x m D : fst (deq (nil,x::m) D) = x.
  Proof.
    apply (g_deq_eq (queue_eq_refl _) (deq_spec D) (in_g_deq_1 nil x m)).
  Qed.
  
  Fact deq_fix_snd x m D : snd (deq (nil,x::m) D) ~q (nil,m).
  Proof.
    apply (g_deq_eq (queue_eq_refl _) (deq_spec D) (in_g_deq_1 nil x m)).
  Qed.
  
  Definition queue_nil_dec q : { q = (nil,nil) } + { q <> (nil,nil) }.
  Proof.
    destruct q as ([ | x l],m).
    destruct m as [ | y m ].
    { left; auto. }
    all: right; discriminate.
  Qed.
  
  Fact queue_list_enq q x : queue_pair_list (enq q x) = queue_pair_list q ++ x :: nil.
  Proof.
    destruct q as (l,m); simpl.
    rewrite app_ass; auto.
  Qed.
  
  Fact queue_list_deq q D : 
    let (x,q') := deq q D in queue_pair_list q = x::queue_pair_list q'.
  Proof.
    generalize (queue_neq_nil (queue_norm q) D); intros H.
    generalize (deq_eq D H (queue_norm q)).
    destruct (deq q D) as (x,q'); simpl.
    revert H; generalize (queue_pair_list q).
    intros [ | y l ] H.
    + destruct H; auto.
    + simpl; rewrite deq_fix_fst.
      intros [ H1 H2 ]; subst y.
      apply queue_eq_list in H2.
      rewrite H2.
      f_equal; symmetry.
      generalize (deq_fix_snd H); intros H3.
      apply queue_eq_list in H3; simpl in H3.
      rewrite H3, <- app_nil_end; auto.
  Qed.
  
End Queues.

Arguments deq {X}.

Infix "~q" := (@queue_eq _) (at level 70, no associativity).

Recursive Extraction deq.

Section measure_rect.

  Variables (X : Type) (m : X -> nat) (P : X -> Type)
            (HP : forall x, (forall y, m y < m x -> P y) -> P x).

  Let R x y := m x < m y.

  Let Acc_R : well_founded R.
  Proof. unfold R; apply wf_inverse_image, lt_wf. Qed.

  Theorem measure_rect : forall x, P x.
  Proof.
    intros x; generalize (Acc_R x); revert x.
    refine (fix loop x (H : Acc R x) { struct H } : P x := @HP x (fun y Hy => loop y _)).
    destruct H as [ H ]; apply H; trivial.
  Qed.

End measure_rect.

Section bt.

  Variable X : Type.

  Inductive bt := leaf : X -> bt | node : bt -> X -> bt -> bt.

  Implicit Type t : bt.

  Fixpoint bt_size t := 
    match t with
      | leaf _ => 1
      | node a _ b => 1 + bt_size a + bt_size b
    end.
    
  Fact bt_size_gt_0 t : 0 < bt_size t.
  Proof. destruct t; simpl; omega. Qed.
  
  Fixpoint sub_bt_list t :=
    t :: match t with 
           | leaf x     => nil
           | node a x b => sub_bt_list a ++ sub_bt_list b
         end.
    
  Fixpoint bt_list t := 
    match t with 
      | leaf x => x :: nil
      | node a x b => x :: bt_list a ++ bt_list b
    end.
    
  Definition bt_root t :=  match t with leaf x => x | node _ x _ => x end.
  
  Fact sub_bt_list_list t : map bt_root (sub_bt_list t) = bt_list t.
  Proof. 
    induction t; simpl; f_equal; auto.
    rewrite map_app; f_equal; auto.
  Qed.
  
End bt.

Arguments leaf {X}.
Arguments bt_size {X}.

(* Voilà une bonne spécif. de bt_numbering 

  bt_numbering i t <-> breadth_first t = [i,...,i+bt_size t[ *)

Definition bt_numbering_local t :=
  match t with
    | leaf _     => True
    | node a x b => Forall (lt x) (bt_list a ++ bt_list b) /\ bt_root a < bt_root b
  end.

Definition bt_numbering i t := 
     Forall bt_numbering_local (sub_bt_list t) 
  /\ bt_root t = i 
  /\ forall j, In j (bt_list t) -> i <= j < i+bt_size t.
  
Fact bt_numbering_fix_leaf i x : bt_numbering i (leaf x) <-> i = x.
Proof.
  split.
  + intros (_ & H & _); subst; auto.
  + intros; subst; split; [ | split ]; simpl.
    * constructor; auto; red; auto.
    * auto.
    * intros j [ ? | [] ]; subst; omega.
Qed.

(* NOT READY YET

Fact bt_numbering_fix_node i a x b : bt_numbering i (node a x b) <-> i = x /\ bt_numbering

(* Show that bt_numering i t -> bt_list t ~ [i,...,i+bt_size t[ *)
  
Inductive bt_iso X Y (R : X -> Y -> Prop) : bt X -> bt Y -> Prop :=
  | in_bt_iso_0 : forall x y, R x y -> bt_iso R (leaf x) (leaf y)
  | in_bt_iso_1 : forall s1 x s2 t1 y t2, R x y -> bt_iso R s1 t1 -> bt_iso R s2 t2 -> bt_iso R (node s1 x s2) (node t1 y t2).
  
Fact bt_numbering_uniq R i t1 t2 : bt_iso R t1 t2 -> bt_numbering i t1 -> bt_numbering i t2 -> t1 = t2.
Proof.
  intros H; revert H i.
  induction 1 as [ | s1 x s2 t1 y t2 H1 H2 IH2 H3 IH3 ]; intros i; auto.
  * intros (_ & ? & _) (_ & ? & _); simpl in *; subst; auto.
  * intros (F1 & F2 & F3) (G1 & G2 & G3).
    f_equal.
    1,2 : cycle 1.
    + simpl in F2, G2; subst; auto.
    + 
    
     apply IH2 with (S i).
      split; [ | split ].
      simpl in F1.
    destruct G1 as (G1 & _ & G2).
    repeat split; auto. 
   G2.
  
  Inductive sub_bt : bt -> bt -> Prop :=
    match

*)

Section lsum.

  Variable (X : Type). 
  
  Implicit Type (f : X -> nat).

  Definition lsum f := fold_right (fun x y => f x + y) 0.
  
  Definition lsum_nil f : lsum f nil = 0 := eq_refl.
  
  Fact lsum_app f l m : lsum f (l++m) = lsum f l + lsum f m.
  Proof. induction l; simpl; auto; omega. Qed.
  
  Fact lsum_cst c l : lsum (fun _ => c) l = length l*c.
  Proof. induction l; simpl; auto. Qed.
  
  Fact lsum_plus f g l : lsum (fun x => f x + g x) l = lsum f l + lsum g l.
  Proof. induction l; simpl; omega. Qed.
  
  Fact lsum_rev f l : lsum f (rev l) = lsum f l.
  Proof.
    induction l; simpl; auto.
    rewrite lsum_app; simpl; omega.
  Qed.

(* NOT READY YET

  Definition qsum f (q : list X * list X) := let (l,m) := q in lsum f l + lsum f m.
  
  Fact qsum_queue_list f q : qsum f q = lsum f (queue_list q).
  Proof.
    destruct q as (l,m); simpl.
    rewrite lsum_app, lsum_rev; omega. 
  Qed.
  
  Fact qsum_eq f q1 q2 : q1 ~q q2 -> qsum f q1 = qsum f q2.
  Proof.
    revert q1 q2; intros (l1,m1) (l2,m2); simpl; intros H.
    apply f_equal with (f := lsum f) in H.
    rewrite lsum_app, lsum_rev, plus_comm in H.
    rewrite H, lsum_app, lsum_rev; omega.
  Qed.
  
  (* enc and deq preserve qsum *)

  Fact qsum_enq f q x : qsum f (enq q x) = f x + qsum f q.
  Proof.
    destruct q as (l,m); simpl; omega.
  Qed.
  
  Fact qsum_deq f q D : match deq q D with (x,q') => qsum f q = f x + qsum f q' end.
  Proof.
    generalize (queue_list_deq D).
    destruct (deq q D) as (x,q').
    do 2 rewrite qsum_queue_list.
    intros E; rewrite E; auto.
  Qed.
*)

End lsum.

(* NOT READY YET
Section bfnum.

  Variable X : Type.
  
  Let R q q' := Forall2 (fun (x : bt X) (y : bt nat) => bt_size x = bt_size y) (queue_list q) (rev (queue_list q')).

  Definition bfnum' (i : nat) (q : queue (bt X)) : sig (R q).
  Proof.
    revert i.
    induction q as [ q bfnum' ] using (measure_rect (qsum bt_size)); intros i.
    destruct (queue_nil_dec q) as [ | Dq ].
    + exists (nil,nil); subst; red; simpl; constructor.
    + refine (match deq q Dq as t return deq q Dq = t -> _ with
        | (leaf,q') => _
        | (node a x b,q') => _
      end eq_refl); intros E; generalize (qsum_deq bt_size Dq); intros H; rewrite E in H.
      - refine (let (r,Hr) := bfnum' q' _ i in _).
        { simpl in H; omega. }
        simpl in Hr.
        exists (enq r leaf).
        red; unfold queue_list; simpl.
        rewrite qsum_enq, <- Hr; auto.
      - set (q1 := enq (enq q' a) b).
        refine (let (r,Hr) := bfnum' q1 _ (S i) in _).
        { unfold q1; rewrite qsum_enq, qsum_enq, H; simpl; omega. }
        simpl in Hr.
        assert (r <> (nil,nil)) as Hr'.
        { intro; subst r.
          unfold q1 in Hr.
          do 2 rewrite qsum_enq in Hr.
          simpl in Hr.
          generalize (bt_size_gt_0 b); omega. }
        case_eq (deq r Hr'); intros b' q2 E2.
        generalize (qsum_deq bt_size Hr'); intros H2; rewrite E2 in H2.
        assert (q2 <> (nil,nil)) as Hq2.
        { intro; subst q2.
          rewrite <- Hr in H2.
          unfold q1 in H2.
          do 2 rewrite qsum_enq in H2.
        
        refine (let (b',q2) :=  in _).
   
        refine (let (a',q3) := deq q2 _ in _).
        { intro; subst q2.
          
        
       
      
      exist _ (enq (bfnum' q' _ i) leaf) _).
    
    
*)
