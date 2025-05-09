module BinomialHeap

open FStar.List.Tot
open FStar.Math.Lib
open FStar.Calc
open InsertionSort

type node0 = | N of nat & int & list node0 // rank, data, children

let rec all_le0 (x: int) (tree: node0) : Tot bool (decreases %[tree; 0])=
  match tree with
  | N (r, k, c) -> x <= k && all_le k c
and all_le (x: int) (bh: list node0) : Tot bool (decreases %[bh; 1])=
  match bh with
    | [] -> true
    | h::hs -> all_le0 x h && all_le x hs

let rec is_heap0 (tree: node0) : bool =
  match tree with
  | N (r, k, c) -> all_le0 k tree && is_heap c
and is_heap (bh: list node0) : bool =
  match bh with
    | [] -> true
    | h::hs -> is_heap0 h && is_heap hs

let rank0 (tree : node0) : nat =
  let N (r,_,_) = tree in
  r

let root0 (tree : node0) : int =
  let N (_,r,_) = tree in
  r

let children0 (tree : node0) : list node0 =
  let N (_,_,c) = tree in
  c

type node = n:node0{is_heap0 n}

let singleton (x: int): node = N (0, x, [])

let link0 (tree1 : node0) (tree2 : node0{rank0 tree1 = rank0 tree2}) : node0 =
  match tree1, tree2 with
  | N (r, k1, c1), N (_, k2, c2) -> if k1 <= k2
                                    then N (r + 1, k1, tree2 :: c1)
                                    else N (r + 1, k2, tree1 :: c2)

let link0_all_le (x: int) (tree1 : node0) (tree2 : node0{rank0 tree1 = rank0 tree2}) :
  Lemma (requires all_le0 x tree1 /\ all_le0 x tree2)
        (ensures all_le0 x (link0 tree1 tree2))
= ()

let append_is_heap (tree1 : node0) (tree2 : node0{rank0 tree1 = rank0 tree2}) : 
  Lemma (requires is_heap0 tree1 /\ is_heap0 tree2)
        (ensures is_heap (tree2::(children0 tree1)))
= ()
  
let is_heap0_all_le0 (tree1 tree2: node0) : 
  Lemma (requires is_heap0 tree1 /\ is_heap0 tree2 /\ root0 tree1 <= root0 tree2)
        (ensures all_le0 (root0 tree1) tree2)
= ()
let link0_is_heap0 (tree1 : node0) (tree2 : node0{rank0 tree1 = rank0 tree2}) : 
  Lemma (requires is_heap0 tree1 /\ is_heap0 tree2)
        (ensures is_heap0 (link0 tree1 tree2))
= match tree1, tree2 with
  | N (r, k1, c1), N (_, k2, c2) -> if k1 <= k2
                                    then (
                                      assert(is_heap (tree2::c1));
                                      assert(all_le0 k1 tree2)
                                    )
                                    else (
                                      assert(is_heap (tree1::c2));
                                      assert(all_le0 k2 tree1)
                                    )

let link (tree1 : node) (tree2 : node{rank0 tree1 = rank0 tree2}) : node 
=
  link0_is_heap0 tree1 tree2;
  link0 tree1 tree2

let rec incr_rank (hs : list node0) : prop =
  match hs with
  | [] -> True
  | [_] -> True
  | h1::h2::hs' -> rank0 h1 < rank0 h2 /\ incr_rank (h2::hs')

let rec number_nodes0 (tree: node0) : nat =
  match tree with
  | N (_, _, c) -> 1 + number_nodes c
and number_nodes (bh: list node0) : nat = 
  match bh with
    | [] -> 0
    | h::hs -> number_nodes0 h + number_nodes hs

type bheap = list node

let emptyHeap : bheap = []

let isEmptyHeap (h: bheap) : bool =
  match h with
  | [] -> true
  | _ -> false

let rec insertTree (t: node) (bh: bheap) : Tot bheap (decreases (length bh))=
  match bh with
  | [] -> [t]
  | h::hs -> if rank0 t < rank0 h
             then t::bh
             else if rank0 t = rank0 h
                  then insertTree (link t h) hs
                  else h :: insertTree t hs

let insert (x: int) (h: bheap) : bheap =
  insertTree (singleton x) h

let rec merge (bh1: bheap) (bh2: bheap) : bheap =
  match bh1, bh2 with
  | [], _ -> bh2
  | _, [] -> bh1
  | h1::hs1, h2::hs2 -> if rank0 h1 < rank0 h2
                        then h1 :: merge hs1 bh2
                        else if rank0 h1 > rank0 h2
                             then h2 :: merge bh1 hs2
                             else insertTree (link h1 h2) (merge hs1 hs2)

let rec removeMinTree (bh: bheap{Cons? bh}) : (node & bheap)  =
  match bh with
  | [h] -> (h, [])
  | h::hs -> let m, hs' = removeMinTree hs in
             if root0 h < root0 m
             then (h, hs)
             else (m, h::hs')


let findMin (bh: bheap{Cons? bh}) : int =
  let m, _ = removeMinTree bh in root0 m

let rec rev_go #a (acc xs : list a) : Tot (list a) (decreases xs)=
  match xs with
  | [] -> acc
  | x::xs -> rev_go (x::acc) xs

let rev (#a:Type) (xs : list a) : list a =
  rev_go [] xs

let rec children (n: node) : Tot (list node) (decreases (number_nodes0 n))
= 
  match n with
    | N (_,_,[]) -> []
    | N (r,k, c::cs) -> c :: children (N (r, k, cs))

let extractMin (bh: bheap{Cons? bh}) : int & bheap =
  let m, hs = removeMinTree bh in 
  root0 m, merge (rev (children m)) hs
  
(*
let rec lemma_removeMinTree_size (bh : bheap{Cons? bh})
  : Lemma (number_nodes bh == number_nodes (snd (removeMinTree bh)) + number_nodes0 (fst (removeMinTree bh)))
  = 
    match bh with
    | [h] -> ()
    | h::hs -> lemma_removeMinTree_size hs

let rec lemma_rev_go_number_nodes (acc ts : list node0)
  : Lemma (ensures number_nodes acc + number_nodes ts == number_nodes (rev_go acc ts))
          (decreases ts)
  =  
    match ts with
     | [] -> ()
     | t::ts -> lemma_rev_go_number_nodes (t::acc) ts

let lemma_rev_number_nodes (ts : list node0)
  : Lemma (number_nodes ts == number_nodes (rev ts))
  = lemma_rev_go_number_nodes [] ts

let rec lemma_insertTree_size (tree: node0) (bh: bheap)
  : Lemma (ensures number_nodes (insertTree tree bh) == number_nodes0 tree + number_nodes bh)
          (decreases bh)
  = 
    match bh with
    | [] -> ()
    | h::hs -> if rank0 tree < rank0 h
               then ()
               else if rank0 tree = rank0 h
                    then lemma_insertTree_size (link tree h) hs
                    else lemma_insertTree_size tree hs

let rec lemma_merge_size (bh1 bh2: bheap)
  : Lemma (number_nodes (merge bh1 bh2) == number_nodes bh1 + number_nodes bh2)
  = 
    match bh1, bh2 with
    | [], _ -> ()
    | _, [] -> ()
    | h1::hs1, h2::hs2 -> if rank0 h1 < rank0 h2
                          then lemma_merge_size hs1 bh2
                          else if rank0 h1 > rank0 h2
                               then lemma_merge_size bh1 hs2
                               else (
                                     lemma_insertTree_size (link h1 h2) (merge hs1 hs2); 
                                     lemma_merge_size hs1 hs2
                                    )

let lemma_deleteMin_size (bh: bheap{Cons? bh})
  : Lemma (number_nodes (snd (extractMin bh)) == number_nodes bh - 1)
= 
  let m, hs = removeMinTree bh in
  calc (==) {
    number_nodes (snd (extractMin bh));
    == {}
    number_nodes (merge (rev (children m)) hs);
    == { lemma_merge_size (rev (children m)) hs } 
    number_nodes (rev (children m)) + number_nodes hs;
    == {lemma_rev_number_nodes (children m) } 
    number_nodes (children m) + number_nodes hs;
    == { lemma_removeMinTree_size bh }
    number_nodes bh - 1;
  }

let rec toList (bh: bheap) : Tot (list int) (decreases (number_nodes bh))=
  match bh with
    | [] -> []
    | _ -> let m, bh' = extractMin bh in
           lemma_deleteMin_size bh;
           m :: toList bh'
*)
let rec elems_node0 (n: node0) : list int =
  let N (x, _, c) = n in
  x :: elems_nodes c
and elems_nodes (cs: list node0) : list int =
  match cs with
    | [] -> []
    | c::cs' -> elems_node0 c @ elems_nodes cs'

let rec toList2 (bh: bheap) : Tot (list int)=
  match bh with
    | [] -> []
    | h::hs -> elems_node0 h @ toList2 hs 

let rec fromList (l: list int) : bheap =
  match l with
    | [] -> []
    | x::xs -> insert x (fromList xs)

(*
let models (bh : bheap) (xs : list int) : prop =
  toList bh == xs
*)

let models (bh : bheap) (xs : list int) : prop =
  perm (toList2 bh) xs

assume val min_list (xs: list int) : int
assume val remove_list (x: int) (xs: list int) : list int

val findMin_ok (bh : bheap) (xs : list int{Cons? xs})
  : Lemma (requires models bh xs)
          (ensures findMin bh == min_list xs)

val deleteMin_ok (bh : bheap) (xs : list int{Cons? xs})
  : Lemma (requires models bh xs)
          (ensures models (snd (extractMin bh)) (remove_list (min_list xs) xs))

val insert_ok  (bh : bheap) (x : int) (xs : list int)
  : Lemma (requires models bh xs)
          (ensures models (insert x bh) (x::xs))

assume val merge_sort (xs ys: list int) : list int

assume val merge_ok (bh1 bh2: bheap) (xs ys: list int) 
  : Lemma (requires models bh1 xs /\ models bh2 ys)
          (ensures models (merge bh1 bh2) (merge_sort xs ys))

(*
let insert_ok  (bh : bheap) (x : int) (xs : list int)
  : Lemma (requires models bh xs)
          (ensures models (insert x bh) (insertion_sort  (x :: xs)))
= assert([singleton x] `models` [x]); 
  merge_ok [singleton x] bh [x] xs; 
  assert (merge [singleton x] bh `models` (merge_sort [x] xs));
  assert (insert x bh `models` (merge_sort [x] xs));
  assert (insert x bh `models` (InsertionSort.insert x xs));
  admit()

*)