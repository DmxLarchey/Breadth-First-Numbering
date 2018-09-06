open List;;

#use "bfn.ml";;

let mytime () = Sys.time ();;
let measure f =
  let t1 = mytime ()             in
  let r =  f ()                  in
  let t2 = mytime ()             
  in  (t2 -.t1,r);;
  

(*****************)

(* computes the pair (p,q) such that p+q+1=n *)

let split_pq n = 
  let rec loop l p q =
    if p >= 0 then loop ((p,q)::l) (p-1) (q+1) else l
  in loop [] (n-1) 0;;

let rec flat_map f (l : 'x list) = 
  match l with
    | []   -> []
    | x::l -> f x @ flat_map f l;;

let prod f l m = flat_map (fun x -> map (fun y -> f x y) m) l;;

let rec bt_2n1 n =
  if n=0 then [Leaf ()]
  else flat_map (fun (p,q) -> prod (fun x y -> Node (x,(),y)) (bt_2n1 p) (bt_2n1 q)) (split_pq n);;

let test n = 
  let ll = bt_2n1 n  in
  let p = length ll  in
  let (d,_) = measure (fun () -> map bfn_3q ll) in
  let a = d /. (float_of_int (n*p)) 
  in  (n,p,d,a);;

test 5;; (* test 10;; test 11;; *)

(*****************)

let rec liter (l : 'x llist) =
  match Lazy.force l with
    | Lnil        -> 0
    | Lcons (x,l) -> 1+liter l;;

let rec ltake n l = 
  if n = 0 then ([],l) 
  else match Lazy.force l with
         | Lnil        -> ([],l)
         | Lcons (x,l) -> let (c1,c2) = ltake (n-1) l in (x::c1,c2);;

let lsplit_pq n = 
  let rec loop p q = lazy 
    (if p+1 <= n then (Lcons ((p,q),loop (p+1) (q-1))) else Lnil)
  in loop 0 (n-1);; 

let rec __lapp l (m : 'x llist) =
  match l with
    | Lnil        -> Lazy.force m
    | Lcons (x,t) -> Lcons (x,lazy (__lapp (Lazy.force t) m));;

let lapp (l : 'x llist) m : 'x llist = lazy (__lapp (Lazy.force l) m);;

let rec lmap f (l : 'x llist) =
  lazy (match Lazy.force l with
    | Lnil        -> Lnil
    | Lcons (x,l) -> Lcons (f x,lmap f l));;

let rec lflat_map f (l : 'x llist) = 
  lazy (match Lazy.force l with
    | Lnil        -> Lnil
    | Lcons (x,l) -> __lapp (Lazy.force (f x)) (lflat_map f l));;

let lprod f l m = lflat_map (fun x -> lmap (fun y -> f x y) m) l;;

let rec lbt_2n1 n =
  if n=0 then lazy (Lcons (Leaf (), lazy Lnil))
  else let f (p,q) = lprod (fun x y -> Node (x,(),y)) (lbt_2n1 p) (lbt_2n1 q)
       in  lflat_map f (lsplit_pq n);;

let lazy_test n = 
  let l1 = lbt_2n1 n      in
  let l2 = lmap bfn_3q l1 in
  let (d,p) = measure (fun () -> liter l2) in
  let a = d /. (float_of_int (n*p)) 
  in  (n,p,d,a);;

lazy_test 10;; (* lazy_test 11;; lazy_test 12;; lazy_test 20;; *)

(*****************)

let random_bt s =
  let _ = Random.init s      in
  let r p = Random.int (p+1) in
  let rec loop k = if k = 0 
                   then Leaf ()
                   else let p = r ((k-1)/2) 
                        in  Node (loop p,(),loop (k-1-p))
  in loop;;

let rec height t =
  match t with 
    | Leaf _       -> 0
    | Node (l,_,r) -> 1+max (height l) (height r);;

random_bt 10 20;;

let r s n = random_bt s n;;
let h s n = height (r s n);;
let b2 s n = bfn_2l (r s n);;
let b3 s n = bfn_3q (r s n);;

(* This gives an upper bound for the test ... for some unknown reason,
   the stack overflows when numbering random trees of size arround 60k *)

(* b3 10 61661;; b3 10 61662;;

b2 10 61661;;  b2 10 61662;; *)

(* The test function measure the time to BFN a random tree of size n with 
   seed s, b has to be instanciated with either  *) 

let t b s n = 
  let (d,_) = measure (fun () -> b (r s n))  in
  let a = d /. (float_of_int n) 
  in  (n,d,a);;

let t2 = t bfn_2l;;
let t3 = t bfn_3q;;

(* Sample test sizes ... seems the runtime is linear in the number
   of nodes for bfn_3q ... not sure about bfn_2l 

   We should run the benchs over and over again to average noise
*)

let sizes = [10;100;1000;5000;10000;15000;25000;40000;50000;60000];;
map (t2 10) sizes;; 
map (t3 10) sizes;; 





