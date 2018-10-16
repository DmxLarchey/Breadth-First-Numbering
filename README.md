# Breadth-First-Numbering
Coq implementation of Breadth-First Numbering à la Okasaki

There are 26 Coq vernacular files, here presented in useful order (based on the [dependency graph](dependency_graph.txt)).
* *list_utils.v* --- One of the biggest files, all concerning list operations, list permutations, the lifting of relations to lists and segments of the natural numbers -- auxiliary material with use at many places.
* *wf_utils.v* --- The subtle tactics for measure recursion in one or two arguments with a nat-valued measure function -- this is crucial for smooth extraction throughout.
* *llist.v* --- Some general material on coinductive lists, in particular proven finite ones (including append for those), but also the rotate operation of Okasaki.
* *wf_example.v* --- the example of `itl2` from which the desired code is extracted
* *zip.v* --- zipping with a rich specification and relations with concatenation -- just auxiliary material
* *sorted.v* --- consequences of a list being sorted, in particular absence of duplicates in case of strict orders -- auxiliary material.
* *increase.v* --- small auxiliary file for full spec.~of breadth-first traversal
* *bt.v* --- The largest file in this library, describing binary trees, their branches and orders on those in relation with depth-first and breadth-first traversal and structural relations on trees and forests.
* *fifo.v* --- Just the module type for abstract FIFOs.
* *fifo_triv.v* --- The trivial implementation of FIFO's through lists.
* *fifo_2lists.v* --- An efficient implementation with amortized $O(1)$ operations.
* *fifo_3llists.v* --- The much more complicated FIFO implementation that is slower but has worst-case $O(1)$ operations, invented by Okasaki.
* *dft_std.v* --- Depth-first traversal.
* *bft_std.v* --- Breadth-first traversal naively with levels (specified with the traversal of branches in suitable order).
* *dft_bft_compare.v* --- Only the result that the respective versions that compute branches compute the same branches, and their lists form a permutation. 
* *bft_forest.v* --- Breadth-first traversal for forests of trees, paying much attention to the recursive equations that can guide the definition and/or verification.
* *bft_inj.v* --- Structurally equal forests with the same outcome of breadth-first traversal are equal.
* *bft_fifo.v* --- Breadth-first traversal given an abstract FIFO.
* *bfn_spec.v* --- An abstract view of what is need for breadth-first numbering.
* *bfn_fifo.v* --- The certified analogue of Okasaki's algorithm for breadth-first numbering.
* *bfn_trivial.v* --- Just the instance of the previous with the trivial implemenation of FIFOs.
* *bfn_level.v* --- A certified reconstruction of `bfnum` on page 134 (section 4 and Figure 5) of Okasaki's article. For its full specification, we allow ourselves to use breadth-first numbering obtained in *bfn_trivial.v*.
* *bfr_fifo.v* --- Breadth-first reconstruction, a slightly more general task (see next file) than breadth-first numbering.
* *bfr_bfn_fifo.v* --- Shows the claim that breadth-first numbering is an instance of breadth-first reconstruction (although they have been obtained with different induction principles).
* *extraction.v* --- This operates extraction on-the-fly.
* *benchmarks.v* --- This operates the extraction towards *.ml* files.
