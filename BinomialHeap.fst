module BinomialHeap

open FStar.List.Tot
open FStar.Math.Lib
open FStar.Calc
open InsertionSort

type node0 = | N of nat & int & list node0 // rank, data, children

let rank (tree : node0) : nat =
  let N (r,_,_) = tree in
  r

let root (tree : node0) : int =
  let N (_,r,_) = tree in
  r

let children (tree : node0) : list node0 =
  let N (_,_,c) = tree in
  c

let singleton (x: int): node0 = N (0, x, [])

let link (tree1 tree2 : node0) : node0 =
  match tree1, tree2 with
  | N (r, k1, c1), N (_, k2, c2) -> if k1 <= k2
                                    then N (r + 1, k1, tree2 :: c1)
                                    else N (r + 1, k2, tree1 :: c2)

let rec all_nodes (#a:Type) (#b: Type) (bound : a) (f: (x:node0{x << bound}) -> b) (op: b -> b -> b) (e: b) (l: list node0{l << bound}) : b = 
  match l with
    | [] -> e
    | x::xs -> op (f x) (all_nodes bound f op e xs)

let rec all_le0 (x: int) (tree: node0) : bool =
  match tree with
  | N (r, k, c) -> k <= x && all_le x c
and all_le (x: int) (bh: list node0) : bool =
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

let rec incr_rank (hs : list node0) : prop =
  match hs with
  | [] -> True
  | [_] -> True
  | h1::h2::hs' -> rank h1 < rank h2 /\ incr_rank (h2::hs')

let rec number_nodes0 (tree: node0) : nat =
  match tree with
  | N (_, _, c) -> 1 + number_nodes c
and number_nodes (bh: list node0) : nat = 
  match bh with
    | [] -> 0
    | h::hs -> number_nodes0 h + number_nodes hs

type bheap = list node0

let emptyHeap : bheap = []

let isEmptyHeap (h: bheap) : bool =
  match h with
  | [] -> true
  | _ -> false

let rec insertTree (t: node0) (bh: bheap) : Tot bheap (decreases (length bh))=
  match bh with
  | [] -> [t]
  | h::hs -> if rank t < rank h
             then t::bh
             else if rank t = rank h
                  then insertTree (link t h) hs
                  else h :: insertTree t hs

let insert (x: int) (h: bheap) : bheap =
  insertTree (singleton x) h

let rec merge (bh1: bheap) (bh2: bheap) : bheap =
  match bh1, bh2 with
  | [], _ -> bh2
  | _, [] -> bh1
  | h1::hs1, h2::hs2 -> if rank h1 < rank h2
                        then h1 :: merge hs1 bh2
                        else if rank h1 > rank h2
                             then h2 :: merge bh1 hs2
                             else insertTree (link h1 h2) (merge hs1 hs2)

let rec removeMinTree (bh: bheap{Cons? bh}) : (node0 & bheap)  =
  match bh with
  | [h] -> (h, [])
  | h::hs -> let m, hs' = removeMinTree hs in
             if root h < root m
             then (h, hs)
             else (m, h::hs')


let findMin (bh: bheap{Cons? bh}) : int =
  let m, _ = removeMinTree bh in root m

let rec rev_go #a (acc xs : list a) : Tot (list a) (decreases xs)=
  match xs with
  | [] -> acc
  | x::xs -> rev_go (x::acc) xs

let rev (#a:Type) (xs : list a) : list a =
  rev_go [] xs

let extractMin (bh: bheap{Cons? bh}) : int & bheap =
  let m, hs = removeMinTree bh in
  root m, merge (rev (children m)) hs

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
    | h::hs -> if rank tree < rank h
               then ()
               else if rank tree = rank h
                    then lemma_insertTree_size (link tree h) hs
                    else lemma_insertTree_size tree hs

let rec lemma_merge_size (bh1 bh2: bheap)
  : Lemma (number_nodes (merge bh1 bh2) == number_nodes bh1 + number_nodes bh2)
  = 
    match bh1, bh2 with
    | [], _ -> ()
    | _, [] -> ()
    | h1::hs1, h2::hs2 -> if rank h1 < rank h2
                          then lemma_merge_size hs1 bh2
                          else if rank h1 > rank h2
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

let rec fromList (l: list int) : bheap =
  match l with
    | [] -> []
    | x::xs -> insert x (fromList xs)

let models (bh : bheap) (xs : list int) : prop =
  toList bh == xs

val insert_ok  (bh : bheap) (x : int) (xs : list int)
  : Lemma (requires models bh xs)
          (ensures models (insert x bh) (insertion_sort (<) (x :: xs)))

val findMin_ok (bh : bheap) (x : int) (xs : list int)
  : Lemma (requires models bh (x::xs))
          (ensures findMin bh == x)

val deleteMin_ok (bh : bheap) (x : int) (xs : list int)
  : Lemma (requires models bh (x::xs))
          (ensures models (snd (extractMin bh)) xs)

let findMin_ok (bh : bheap) (x : int) (xs : list int)
  : Lemma (requires models bh (x::xs))
          (ensures findMin bh == x) = ()

let deleteMin_ok (bh : bheap) (x : int) (xs : list int)
  : Lemma (requires models bh (x::xs))
          (ensures models (snd (extractMin bh)) xs) = ()
