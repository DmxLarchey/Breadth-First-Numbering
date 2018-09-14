open List;;
open Gc;;

#use "bfn.ml";;
(* open Bfn;; *)


let mytime () = Sys.time ();;
let mygcstats () =
  let st = Gc.quick_stat ()      
  in (st.minor_collections,st.major_collections);;

let measure f =
  let (mi1,ma1) = mygcstats ()    in
  let t1  = mytime ()             in
  let r =  f ()                   in
  let t2 = mytime ()              in
  let (mi2,ma2) = mygcstats ()
  in  (t2 -.t1,r,mi2-mi1,ma2-ma1);;
 
(** Compute a random int value within [a,b] with log scale distribution *) 

let random_log a b =
  let a = log (float_of_int a) in
  let b = log (float_of_int b) in
  let r = Random.float (b-.a)
  in  int_of_float (exp (a+.r));;

(** Test for the random log. Display with eg gnuplot

    gnuplot> plot "trl.txt" using 1:(log($2))

*)

let try_random_log s a b n =
  let _ = Random.init s      in
  let rec loop i =
    if n <= i then ()
    else let r = random_log a b   in
         let _ = Printf.printf "%3d %6d\n" i r
         in  loop (i+1)
  in loop 0;;

(* try_random_log 10 10 1000000 300000;; *)

(** Computes a random binary tree of size 2n+1
    It proceeds by first choosing (p,q) st p+q+1 = n
    and then recursively on p then q

    The pair (p,q=n-1-p) is choosen randomly
    using a random function r. Depending on the
    probability distribution of r, one can build 
    nature like looking trees. 

    See  doi:10.1007/BFb0021801

*)

let random_split n = 
  let k = (n-1)/2          in
  let r = Random.int (k+1) 
  in  (r,n-1-r);;

let random_bt r =
  let rec loop n = if n = 0 
                   then (1,Leaf ())
                   else let (p,q) = r n      in
                        let (h1,t1) = loop p in
                        let (h2,t2) = loop q 
                        in  (1+max h1 h2,Node (t1,(),t2))
  in loop;;

let output_all num size height mes min_col maj_col =
  let avg = mes *. 1000000. /. (float_of_int size) 
  in Printf.printf "%06d size=%-6d height=%-5d avg=%fµs time=%fs gc_minor=%d gc_major=%d\n" num size height avg mes min_col maj_col;;

let output_stat num size height mes min_col maj_col =
  let avg = mes *. 1000000. /. (float_of_int size) 
  in Printf.printf "%06d %-6d %f %d\n" num size avg min_col;;

(** loop measuring the node-average time of bfn 
    for random binary tree of size between a and b
    (log scale choice of size) 

    A full GC is performed inbetween every measure
*)

let random_log_bench ?(gc=true) ?(frm=output_stat) 
    ?(bfn=bfn_2l) ?(seed=10) a b n =
  let _ = Random.init seed           in
  let rsze = random_log              in
  let rbt  = random_bt random_split  in
  let rec loop i = 
    if n <= i then ()
    else begin 
          (let sze   = rsze a b                 in
           let (h,t) = rbt sze                  in
           let (m,_,mi_col,ma_col) = measure (fun _ -> bfn t) 
           in  frm i (2*sze+1) h m mi_col ma_col); 
           flush_all ();
           if gc then Gc.compact () else ();
           loop (i+1)
         end
  in loop 0;;

(** random test of bfn_[2l,3q] on trees of size between 101 and 600001 nodes, 
    with full GC sweep between each measurement *)

(*
random_log_bench true output_stat bfn_2l 10 50 300000 2000;; 
random_log_bench true output_stat bfn_3q 10 50 300000 2000;;
*)

random_log_bench ~frm:output_stat ~bfn:bfn_3q 16 600000 1000;; 


