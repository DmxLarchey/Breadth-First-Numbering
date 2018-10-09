(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             Ralph Matthes [+]                              *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                             [+] Affiliation IRIT -- CNRS   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** Extraction of a breadth-first traversal from Coq to Ocaml 

   open List;;

   type 'a bt = Leaf of 'a | Node of 'a bt * 'a * 'a bt;;

   let root t = match t with Leaf x -> x | Node (_,x,_) -> x;;

   let rec subt ll =
     match ll with
       | []                 -> []
       | Leaf _       :: ll -> subt ll
       | Node (a,_,b) :: ll -> a :: b :: subt ll;;

  let rec niveaux ll =
    match ll with
      | [] -> []
      | _  -> map root ll :: niveaux (subt ll);;


  let rec list2bt x ll =
    match ll with
      | []    -> Leaf 0
      | y::ll -> Node (Leaf y,x,list2bt x ll);;

  niveaux [Node (Leaf 1,2,Leaf 3)];;
  niveaux [list2bt 0 [1;2;3;4;5]];;

*)

Require Import List Arith Omega Wellfounded Extraction.
Require Import list_utils wf_utils zip bt.

Set Implicit Arguments.

Section breadth_first_traversal.

  Context (X : Type).
 
  Implicit Type (t : bt X) (l m ll : list (bt X)) (rl rm: list(list X)).

  (* This is the standard/obvious specification of breadth-first traversal *)

  Fixpoint niveaux t : list (list X) :=
    match t with 
      | leaf x     => (x::nil) :: nil
      | node a x b => (x::nil) :: zip (@app _) (niveaux a) (niveaux b)
    end.

  Fact length_niveaux t : list_sum (map (@length _) (niveaux t)) = m_bt t.
  Proof.
    induction t as [ x | a Ha x b Hb ]; simpl; auto.
    rewrite map_zip_length, zip_list_sum; do 2 f_equal; trivial.
  Qed.
    
  Definition bft_std t : list X := concat (niveaux t).

  Fact bft_std_length t : length (bft_std t) = m_bt t.
  Proof.
    unfold bft_std.
    rewrite length_concat.
    apply length_niveaux.
  Qed.

  Fixpoint subt ll : list (bt X) :=
    match ll with
      | nil             => nil
      | leaf _     :: l => subt l
      | node a _ b :: l => a :: b :: subt l
    end.
    
  Fact subt_app l m : subt (l++m) = subt l ++ subt m.
  Proof. induction l as [ | [ | ] ]; simpl; repeat f_equal; auto. Qed.

  Fact subt_dec ll : ll = nil \/ lsum (subt ll) < lsum ll.
  Proof.
    induction ll as [ | [|] ]; simpl; auto;
      right; destruct IHll; subst; simpl; auto; omega.
  Qed.

  Fact subt_le ll : lsum (subt ll) <= lsum ll.
  Proof. destruct (subt_dec ll); subst; simpl; omega. Qed.
  
  Fixpoint forest_decomp ll: list X * list (bt X) :=
    match ll with 
      | nil   => (nil,nil)
      | t::ll => let (ro,sf) := forest_decomp ll in
      match t with
        | leaf x     => (x::ro,sf)
        | node a x b => (x::ro,a::b::sf)
      end
    end.

  Fact forest_decomp_eq ll : forest_decomp ll = (map root ll, subt ll).
  Proof. induction ll as [ | [] ? IH ]; simpl; auto; rewrite IH; auto. Qed.

  (* The specification of niveaux_f
  
      let rec niveaux_f ll =
        match ll with
          | [] -> []
          | _  -> map root ll :: niveaux_f (subt ll);;

     as a graph *)

  Inductive g_niv : list (bt X) -> list (list X) -> Prop :=
    | in_gn_0 : g_niv nil nil
    | in_gn_1 : forall l rl, l <> nil -> g_niv (subt l) rl -> g_niv l (map root l :: rl).
    
  Ltac mysolve := try match goal with H: ?x <> ?x |- _ => destruct H; reflexivity end.

  Fact g_niv_fun l rl1 rl2 : g_niv l rl1 -> g_niv l rl2 -> rl1 = rl2.
  Proof.
    intros H; revert H rl2.
    induction 1 as [ | l m1 H1 H2 IH2 ]; intros m2 H3; inversion H3; auto; subst; mysolve.
    f_equal; apply IH2; trivial.
  Qed.
    
  Fact g_niv_app l rl m rm : g_niv l rl -> g_niv m rm -> g_niv (l++m) (zip (@app _) rl rm).
  Proof.
    intros H1; revert H1 m rm.
    induction 1 as [ | l rl H1 H2 IH2 ]; simpl; auto.
    induction 1 as [ | m rm H3 H4 IH4 ]; simpl; auto.
    * rewrite <- app_nil_end; constructor; auto.
    * rewrite <- map_app; constructor.
      + destruct l; try discriminate.
        destruct H1; auto.
      + rewrite subt_app; apply IH2; auto.
  Qed. 

  (* We show that niveaux satisfies g_niv *)

  Fact g_niv_tree t : g_niv (t::nil) (niveaux t).
  Proof.
    induction t as [ x | a Ha x b Hb ].
    * constructor 2; try discriminate.
      constructor.
    * simpl; constructor 2; try discriminate.
      apply (g_niv_app Ha Hb).
  Qed.
  
  Section niveaux_f.

    (* We reify the graph g_niv using induction on a measure
  
       This one extracts to the exact same Ocaml algo
       as advertised in the opening comments *)

    Let niveaux_f_rec ll : sig (g_niv ll).
    Proof.
      induction on ll as niveaux_f_rec with measure (lsum ll).
      refine (match ll as l return ll = l -> sig (g_niv l) with
          | nil  => fun _ => exist _ nil _
          | t::l => fun E => let (r,Hr) := niveaux_f_rec (subt ll) _
                             in exist _ (map root ll :: r) _
        end eq_refl).
      1,2 : cycle 1. 
      * destruct (subt_dec ll); auto; subst; discriminate.
      * constructor.
      * rewrite <- E; constructor; auto; subst; discriminate.
    Qed.

    Definition niveaux_f ll : list (list X) := proj1_sig (@niveaux_f_rec ll).
 
    Fact niveaux_f_spec ll : g_niv ll (niveaux_f ll).
    Proof. apply (proj2_sig _). Qed.

    Hint Resolve niveaux_f_spec.

    Fact niveaux_f_fix_0 : niveaux_f nil = nil.
    Proof. apply g_niv_fun with nil; auto; constructor. Qed.

    Fact niveaux_f_fix_1 ll : ll <> nil -> niveaux_f ll = map root ll :: niveaux_f (subt ll).
    Proof. intro; apply g_niv_fun with ll; auto; constructor; auto. Qed.
  
  End niveaux_f.

  (* Hence niveaux_f is indeed a generalization of niveaux *)
  
  Fact niveaux_eq_niveaux_f t : niveaux t = niveaux_f (t::nil). 
  Proof.
    apply g_niv_fun with (t::nil).
    + apply g_niv_tree.
    + apply niveaux_f_spec.
  Qed.

  (* Breadth first traversal of a forest *)

  Definition bft_f l := concat (niveaux_f l).

  (* Breadth first traversal of a tree as a particular instance *)

  Definition bft t := bft_f (t::nil).

  (* bft is extensionally equal to bft_std *)
  
  Theorem bft_eq_bft_std t : bft t = bft_std t.
  Proof. unfold bft_std, bft, bft_f; f_equal; symmetry; apply niveaux_eq_niveaux_f. Qed.

  (* Now important fixpoint equations of bft_f *)

  Fact bft_f_fix_0 : bft_f nil = nil.
  Proof. unfold bft_f; rewrite niveaux_f_fix_0; auto. Qed. 

  (** The identity   bft_f (l++m) = map root l ++ bft_f (m++subt l) is critical
      to show the correctness of Breadth First Numbering *)

  (* The induction is a bit complex here because l and m alternate in the proof
     so we proceed by induction on lsum (l++m) *)

  Lemma bft_f_fix_1 l m : bft_f (l++m) = map root l ++ bft_f (m++subt l).
  Proof.
    unfold bft_f.
    induction on l m as IH with measure (lsum (l++m)).
    destruct l as [ | [ x | a x b ] l ].
    + rewrite <- app_nil_end; auto.
    + rewrite niveaux_f_fix_1; try discriminate; simpl; f_equal.
      rewrite map_app, <- app_assoc; f_equal.
      rewrite IH, <- subt_app; auto.
      simpl; repeat rewrite lsum_app.
      generalize (subt_le l); omega.
    + simpl; rewrite niveaux_f_fix_1; try discriminate.
      simpl; f_equal; rewrite map_app, <- app_assoc; f_equal.
      rewrite IH, subt_app; auto.
      simpl; repeat rewrite lsum_app; simpl.
      generalize (subt_le l); omega.
  Qed.

  Corollary bft_f_fix_2 l : bft_f l = map root l ++ bft_f (subt l).
  Proof. rewrite (app_nil_end l) at 1; apply bft_f_fix_1. Qed.

  Corollary bft_f_fix_3 x l : bft_f (x::l) = root x :: bft_f (l++subt (x::nil)).
  Proof. apply bft_f_fix_1 with (l := _::nil). Qed.

  Section bft_f'.

    Inductive g_bft_f : list (bt X) -> list X -> Prop :=
      | in_g_bft_f_0 : g_bft_f nil nil
      | in_g_bft_f_1 : forall lt r, lt <> nil -> g_bft_f (subt lt) r -> g_bft_f lt (map root lt ++ r).

    Fact g_bft_f_inj lt r1 r2 : g_bft_f lt r1 -> g_bft_f lt r2 -> r1 = r2.
    Proof.
      intros H1; revert H1 r2.
      induction 1; inversion 1; subst; auto.
      mysolve.
      f_equal; auto.
    Qed.

    Fact g_bft_f_bft_f lt : g_bft_f lt (bft_f lt).
    Proof.
      induction on lt as IH with measure (lsum lt).
      destruct lt.
      + rewrite bft_f_fix_0; constructor.
      + rewrite bft_f_fix_2; constructor.
        * discriminate.
        * apply IH.
          destruct (subt_dec (b::lt)); auto; subst; discriminate.
    Qed.

    Let bft_f'_rec lt : sig (g_bft_f lt).
    Proof.
      induction on lt as loop with measure (lsum lt).
      refine (match lt as l return lt = l -> sig (g_bft_f l) with
        | nil  => fun _ => exist _ nil _
        | t::l => fun E => let (mm,Hmm) := loop (subt lt) _
                           in exist _ (map root lt ++ mm) _
      end eq_refl).
      + constructor.
      + destruct (subt_dec lt); auto; subst; discriminate.
      + rewrite <- E; constructor; auto; subst; discriminate.
    Qed.

    Definition bft_f' lt := proj1_sig (bft_f'_rec lt).

    Fact bft_f'_spec lt : g_bft_f lt (bft_f' lt).
    Proof. apply (proj2_sig _). Qed.

    Fact bft_f'_eq_bft_f lt : bft_f' lt = bft_f lt.
    Proof.
      apply (@g_bft_f_inj lt).
      + apply bft_f'_spec.
      + apply g_bft_f_bft_f.
    Qed.

    Fact bft_f'_fix_0 : bft_f' nil = nil.
    Proof.
      apply (@g_bft_f_inj nil).
      + apply bft_f'_spec.
      + constructor.
    Qed.

    Fact bft_f'_fix_1 lt : lt <> nil -> bft_f' lt = map root lt ++ bft_f' (subt lt).
    Proof.
      intros H; apply (@g_bft_f_inj lt).
      + apply bft_f'_spec.
      + constructor; auto.
        apply bft_f'_spec.
    Qed.

    Fact bft_f'_fix_2 lt : bft_f' lt = map root lt ++ bft_f' (subt lt).
    Proof. 
      destruct lt; auto.
      apply bft_f'_fix_1; discriminate.
    Qed.

    Fact bft_f'_fix_3 l m : bft_f' (l++m) = map root l ++ bft_f' (m++subt l).
    Proof.
      induction on l m as IH with measure (lsum (l++m)).
      destruct l as [ | [ x | a x b ] l ].
      + rewrite <- app_nil_end; auto.
      + rewrite bft_f'_fix_2.
        simpl.
        rewrite map_app, app_ass; do 2 f_equal.
        rewrite IH.
        * do 2 f_equal; rewrite subt_app; auto.
        * simpl; do 2 rewrite lsum_app.
          generalize (subt_le l); omega.
      + rewrite bft_f'_fix_2.
        simpl.
        rewrite map_app, app_ass; do 2 f_equal.
        rewrite IH.
        * do 2 f_equal; rewrite subt_app; auto.
        * simpl; do 2 rewrite lsum_app.
          simpl; generalize (subt_le l); omega.
   Qed.
   
   Corollary bft_f'_fix_4 x l : bft_f' (x::l) = root x :: bft_f' (l++subt (x::nil)).
   Proof. apply bft_f'_fix_3 with (l := _::nil). Qed.

  End bft_f'.

End breadth_first_traversal.

Section bft_inj.

  Variable X : Type.

  Implicit Types (l m : list (bt X)) (t : bt X).

  (** injectivity of [bft_f] given that the arguments are structurally equal *)

  Theorem bft_f_inj l m : l ~lt m -> bft_f l = bft_f m -> l = m.
  Proof.
    induction on l m as IH with measure (lsum (l++m)).
    revert l m IH; intros [ | t1 l ] [ | t2 m ] IH H; try (inversion H; fail); auto.
    Forall2 inv H as H12.
    do 2 rewrite bft_f_fix_3.
    destruct t1 as [ x | a1 x b1 ]; destruct t2 as [ y | a2 y b2 ]; try (inversion H12; fail); simpl.
    + intros E; inversion E; f_equal.
      do 2 rewrite <- app_nil_end in *.
      apply IH; auto.
      repeat rewrite lsum_app; simpl; omega.
    + apply bt_eq_node_inv in H12; destruct H12 as [ Ha Hb ].
      intros E; injection E; clear E; intros E ?; subst.
      apply IH in E.
      * apply f_equal with (f := @rev _) in E.
        repeat rewrite rev_app_distr in E; simpl in E.
        inversion E; subst; f_equal.
        rewrite <- (rev_involutive l), <- (rev_involutive m).
        f_equal; assumption.
      * repeat rewrite lsum_app; simpl; omega.
      * apply Forall2_app; auto.
  Qed.

  Corollary bft_inj t1 t2 : t1 ~t t2 -> bft t1 = bft t2 -> t1 = t2.
  Proof.
    unfold bft.
    intros H1 H2. 
    apply bft_f_inj in H2; auto.
    inversion H2; auto.
  Qed.

  Corollary bft_std_inj t1 t2 : t1 ~t t2 -> bft_std t1 = bft_std t2 -> t1 = t2.
  Proof. do 2 rewrite <- bft_eq_bft_std; apply bft_inj. Qed.

End bft_inj.

