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

(** Extraction of breadth-first numbering algorithm from Coq to Ocaml 

       see http://okasaki.blogspot.com/2008/07/breadth-first-numbering-algorithm-in.html
       and https://www.westpoint.edu/eecs/SiteAssets/SitePages/Faculty%20Publication%20Documents/Okasaki/jfp95queue.pdf
       and https://www.cs.cmu.edu/~rwh/theses/okasaki.pdf
       and https://www.westpoint.edu/eecs/SiteAssets/SitePages/Faculty%20Publication%20Documents/Okasaki/icfp00bfn.pdf

*)

Require Import List Extraction.
Require Import bt fifo bfn_fifo.

Extraction Language OCaml.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Module BFN_triv := BFN_FIFO FIFO_triv.
Module BFN_2lists := BFN_FIFO FIFO_2lists.
Module BFN_3llists := BFN_FIFO FIFO_3llists.
(** the following does not yield executable extracted programs *)
Module BFN_axm := BFN_FIFO FIFO_axm.


(* The extraction here provides either
   1) an empty implementation of FIFOs (with fifo_axm)
   2) a trivial implementation with lists (with fifo_triv)
   3) an implementation with 2 lists and efficient reverse (with fifo_2lists), (relaxed) O(1) enqueue/dequeue
   4) an implementation with 3 lazy lists (with fifo_3llists), O(1) enqueue/dequeue
 *)

Extraction "bfn_axm" BFN_axm.bfn_fifo.
Extraction "bfn_triv" BFN_triv.bfn_fifo.
Extraction "bfn_2lists" BFN_2lists.bfn_fifo.
Extraction "bfn_3llists" BFN_3llists.bfn_fifo.
