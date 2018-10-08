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

Require Import bt List.
Require fifo_axm.
Require fifo_triv.
Require fifo_2lists.
Require fifo_3llists.

Set Implicit Arguments.

Module Type FIFO.

Parameters (fifo      : Type -> Type)
           (fifo_list : forall X, fifo X -> list X)
           (fifo_nil  : forall X, { q : fifo X | fifo_list q = nil })
           (fifo_enq  : forall X q x, { q' : fifo X | fifo_list q' = fifo_list q ++ x :: nil })
           (fifo_deq  : forall X q, @fifo_list X q <> nil -> { c : X * fifo X | let (x,q') := c in fifo_list q = x::fifo_list q' })
           (fifo_void : forall X q, { b : bool | b = true <-> @fifo_list X q = nil }).

Arguments fifo_nil {X}.
Arguments fifo_deq {X}.

Notation fifo_lsum := ((fun X (q : fifo (bt X)) => lsum (fifo_list q)) _).

End FIFO.

(** implementation based on a list *)
Module FIFO_triv <: FIFO.

  Definition fifo := fifo_triv.fifo.
  Definition fifo_list := fifo_triv.fifo_list.
  Definition fifo_nil (X: Type) := fifo_triv.fifo_nil (X:=X).
  Definition fifo_enq := fifo_triv.fifo_enq.
  Definition fifo_deq (X: Type) := fifo_triv.fifo_deq (X:=X).
  Definition fifo_void := fifo_triv.fifo_void.

End FIFO_triv.

(** implementation based on two lists *)
Module FIFO_2lists <: FIFO.

  Definition fifo := fifo_2lists.fifo.
  Definition fifo_list := fifo_2lists.fifo_list.
  Definition fifo_nil (X: Type) := fifo_2lists.fifo_nil (X:=X).
  Definition fifo_enq := fifo_2lists.fifo_enq.
  Definition fifo_deq (X: Type) := fifo_2lists.fifo_deq (X:=X).
  Definition fifo_void := fifo_2lists.fifo_void.

End FIFO_2lists.

(** implementation based on three lazy lists *)
Module FIFO_3llists <: FIFO.

  Definition fifo := fifo_3llists.fifo.
  Definition fifo_list := fifo_3llists.fifo_list.
  Definition fifo_nil (X: Type) := fifo_3llists.fifo_nil (X:=X).
  Definition fifo_enq := fifo_3llists.fifo_enq.
  Definition fifo_deq (X: Type) := fifo_3llists.fifo_deq (X:=X).
  Definition fifo_void := fifo_3llists.fifo_void.

End FIFO_3llists.

(** now the redundant module that cannot serve for program extraction *)
Module FIFO_axm <: FIFO.

  Definition fifo := fifo_axm.fifo.
  Definition fifo_list := fifo_axm.fifo_list.
  Definition fifo_nil (X: Type) := fifo_axm.fifo_nil (X:=X).
  Definition fifo_enq := fifo_axm.fifo_enq.
  Definition fifo_deq (X: Type) := fifo_axm.fifo_deq (X:=X).
  Definition fifo_void := fifo_axm.fifo_void.

End FIFO_axm.
