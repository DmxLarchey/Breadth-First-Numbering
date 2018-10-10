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

   let root t = match t with Leaf x -> x  | Node (_,x,_) -> x;;
   let subt t = match t with Leaf x -> [] | Node (a,x,b) -> [a;b];;

   (* forest_decomp ll = (map root ll, flat_map subt ll) *)

   let rec forest_decomp = function
     | []   -> ([], [])
     | t::l -> let ro,sf = forest_decomp l 
               in match t with
                    | Leaf x         -> (x::ro,sf)
                    | Node (a, x, b) -> (x::ro,a::b::sf)

   let rec bft_f = function 
     | [] -> []
     | _  -> let ro,st = forest_decomp u in ro @ bft_f st

   let bft_forest t = bft_f (t::nil)

*)

Require Import List Arith Omega Wellfounded Extraction.
Require Import list_utils wf_utils zip bt bft_std bft_forest.

Set Implicit Arguments.

Section breadth_first_traversal.

  Notation subtrees := (flat_map (@subt _)).

  Fixpoint forest_children {X} ll : nat * list (bt X) :=
    match ll with 
      | nil   => (0,nil)
      | t::l => let (n,ch) := forest_children l in
      match t with
        | leaf x     => (n,ch)
        | node a x b => (S n,a::b::ch)
      end
    end.

  Fact forest_children_eq X ll : let (n,ch) := @forest_children X ll in ch = subtrees ll /\ 2*n = length ch. 
  Proof. 
    induction ll as [ | [ x | a x b ] ll IH ]; simpl; auto; 
    destruct (forest_children ll) as (n,ch); auto.
    destruct IH as (? & IH); subst; split; auto; simpl; omega.
  Qed.

  Context (X : Type).
 
  Implicit Type (t : bt X) (l m ll : list (bt X)).

  Fixpoint forest_rebuild i (ts : list (bt X)) cs :=
    match ts with 
      | nil => nil
      | leaf _ :: ts => leaf i :: forest_rebuild (S i) ts cs
      | node _ _ _ :: ts =>
      match cs with
        | a :: b :: cs => node a i b :: forest_rebuild (S i) ts cs
        | _ => nil
      end
    end.

  Check forest_rebuild.

  Definition is_bfn_from n k := is_seq_from n (bft_f k).

  Fact forest_rebuild_spec i ts cs : 
        (exists n ls, ts ~lt ls /\ (n,cs) = forest_children ls /\ is_bfn_from (i+n) cs)  
     -> let r := forest_rebuild i ts cs in ts ~lt r /\ is_bfn_from i r.
  Proof.
    revert i cs.
    induction ts as [ | [ x | a x b ] ts IH ]; intros i cs (n & ls & H1 & H2 & H3); simpl.
    + split; auto; red; rewrite bft_f_fix_0; simpl; auto.
    + split.
      * constructor.
        - constructor.
        - destruct (IH (S i) cs).
       
    

  Section bft_f_spec.

    Variables (bft_f : list (bt X) -> list X)
              (bft_f_0 : bft_f nil = nil)
              (bft_f_1 : forall l, bft_f l = roots l ++ bft_f (subtrees l)).

    (** The identity   bft_f (l++m) = map root l ++ bft_f (m++subt l) is critical
        to show the correctness of Breadth First Numbering *)

    (* The induction is a bit complex here because l and m alternate in the proof
       so we proceed by induction on lsum (l++m) *)

    Theorem bft_f_app l m : bft_f (l++m) = roots l ++ bft_f (m++subtrees l).
    Proof.
      induction on l m as IH with measure (lsum (l++m)).
      destruct l as [ | [ x | a x b ] l ]; 
        try (rewrite <- app_nil_end; auto; fail);
      rewrite bft_f_1; simpl;
      (rewrite map_app, app_ass; do 2 f_equal; rewrite IH;
       [ do 2 f_equal; rewrite subtrees_app; auto
       | simpl; do 2 rewrite lsum_app; simpl; generalize (subtrees_le l); omega ]).
    Qed.

    Corollary bft_f_okazaki t l : bft_f (t::l) = root t :: bft_f (l++subt t).
    Proof.
      change (t::l) with ((t::nil)++l).
      rewrite bft_f_app; simpl.
      rewrite <- app_nil_end; trivial.
    Qed.

    Corollary bft_f_okazaki_1 x l : bft_f (leaf x::l) = x::bft_f l.
    Proof. rewrite bft_f_okazaki; simpl; rewrite <- app_nil_end; trivial. Qed.
 
    Corollary bft_f_okazaki_2 a x b l : bft_f (node a x b::l) = x::bft_f (l++a::b::nil).
    Proof. apply bft_f_okazaki. Qed.

  End bft_f_spec.

  Ltac mysolve := try match goal with H: ?x <> ?x |- _ => destruct H; reflexivity end.

  Section bft_f_def.

    (* we use the specification bft_f_0 and bft_f_1 as a definition for
       btf_f where the equation bft_f_1 is used only when wf, ie l <> nil 

       let us first write the graph of the algorithm
     *)

    Inductive g_bft_f : list (bt X) -> list X -> Prop :=
      | in_g_bft_f_0 : g_bft_f nil nil
      | in_g_bft_f_1 : forall ll r, ll <> nil -> g_bft_f (subtrees ll) r -> g_bft_f ll (roots ll ++ r).

    Fact g_bft_f_fun ll r1 r2 : g_bft_f ll r1 -> g_bft_f ll r2 -> r1 = r2.
    Proof.
      intros H1; revert H1 r2.
      induction 1; inversion 1; subst; auto.
      mysolve.
      f_equal; auto.
    Qed.

    Let bft_f_rec ll : sig (g_bft_f ll).
    Proof.
      induction on ll as loop with measure (lsum ll).
      refine (match ll as l return ll = l -> sig (g_bft_f ll) with
        | nil  => fun _  => exist _ nil _
        | t::l => fun E1 => 
        match forest_decomp ll as c return forest_decomp ll = c -> sig (g_bft_f ll) with
          | (ro,st) => fun E2 => let (mm,Hmm) := loop st _
                                 in exist _ (ro ++ mm) _ 
        end eq_refl
      end eq_refl).
      + subst; constructor.
      + rewrite forest_decomp_eq in E2; inversion E2.
        destruct (subtrees_dec ll); auto; subst; discriminate.
      + rewrite forest_decomp_eq in E2; inversion E2.
        constructor; subst; auto; discriminate.
    Qed.

    Definition bft_f ll := proj1_sig (bft_f_rec ll).

    Fact bft_f_spec ll : g_bft_f ll (bft_f ll).
    Proof. apply (proj2_sig _). Qed.

    Hint Resolve bft_f_spec.

    Fact bft_f_fix_0 : bft_f nil = nil.
    Proof. apply g_bft_f_fun with nil; auto; constructor. Qed.

    Fact bft_f_fix_1 ll : ll <> nil -> bft_f ll = roots ll ++ bft_f (subtrees ll).
    Proof. intro; apply g_bft_f_fun with ll; auto; constructor; auto. Qed.
 
  End bft_f_def.

  Fact bft_f_fix_2 lt : bft_f lt = roots lt ++ bft_f (subtrees lt).
  Proof. 
    destruct lt; auto.
    apply bft_f_fix_1; discriminate.
  Qed.

  Fact bft_f_fix_oka_0 : bft_f nil = nil.
  Proof. exact bft_f_fix_0. Qed.

  Hint Resolve bft_f_fix_2.

  Fact bft_f_fix_oka_1 x l : bft_f (leaf x::l) = x::bft_f l.
  Proof. apply bft_f_okazaki_1; auto. Qed.

  Fact bft_f_fix_oka_2 a x b l : bft_f (node a x b::l) = x::bft_f (l++a::b::nil).
  Proof. apply bft_f_okazaki_2; auto. Qed.

  Definition bft_forest t := bft_f (t::nil).

  Section bft_eq_bft_std.

    (** [bft] is extensionally equal to [bft_std] *)

    (** We characterize [niveaux] inductively *)

    Inductive g_niv : list (bt X) -> list (list X) -> Prop :=
      | in_gn_0 : g_niv nil nil
      | in_gn_1 : forall l rl, l <> nil -> g_niv (subtrees l) rl -> g_niv l (roots l :: rl).
    
    Lemma g_niv_app l rl m rm : g_niv l rl -> g_niv m rm -> g_niv (l++m) (zip (@app _) rl rm).
    Proof.
      intros H1; revert H1 m rm.
      induction 1 as [ | l rl H1 H2 IH2 ]; simpl; auto.
      induction 1 as [ | m rm H3 H4 IH4 ]; simpl; auto.
      * rewrite <- app_nil_end; constructor; auto.
      * rewrite <- map_app; constructor.
        + destruct l; try discriminate.
          destruct H1; auto.
        + rewrite subtrees_app; apply IH2; auto.
    Qed. 

    Lemma g_niv_niveaux t : g_niv (t::nil) (niveaux t).
    Proof.
      induction t as [ x | a Ha x b Hb ].
      * constructor 2; try discriminate.
        constructor.
      * simpl; constructor 2; try discriminate.
        apply (g_niv_app Ha Hb).
    Qed.

    Lemma g_niv_bft_f l rl : g_niv l rl -> g_bft_f l (concat rl).
    Proof. induction 1; simpl; constructor; auto. Qed.

    Lemma g_bft_f_bft_std t : g_bft_f (t::nil) (bft_std t).
    Proof. apply g_niv_bft_f, g_niv_niveaux. Qed.
 
    Theorem bft_forest_eq_bft_std t : bft_forest t = bft_std t.
    Proof. 
      apply g_bft_f_fun with (t::nil).
      + apply bft_f_spec.
      + apply g_niv_bft_f, g_niv_niveaux.
    Qed.
 
  End bft_eq_bft_std.

End breadth_first_traversal.

Check forest_decomp_eq.
Check bft_forest_eq_bft_std.
