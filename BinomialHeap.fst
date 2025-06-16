module BinomialHeap

open FStar.List.Tot
open FStar.Math.Lib
open FStar.Calc

(*
  Definición de la estructura de arboles generales y los predicados de heap.
*)
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


(*
  Definición de operaciones de nodos
*)
let singleton (x: int): node = N (0, x, [])

let link0 (tree1 : node0) (tree2 : node0{rank0 tree1 = rank0 tree2}) : node0 =
  match tree1, tree2 with
  | N (r, k1, c1), N (_, k2, c2) -> if k1 <= k2
                                    then N (r + 1, k1, tree2 :: c1)
                                    else N (r + 1, k2, tree1 :: c2)

let link (tree1 : node) (tree2 : node{rank0 tree1 = rank0 tree2}) : node 
= link0 tree1 tree2

let rec incr_rank (hs : list node0) : prop =
  match hs with
  | [] -> True
  | [_] -> True
  | h1::h2::hs' -> rank0 h1 < rank0 h2 /\ incr_rank (h2::hs')

let rec number_nodes0 (tree: node0) : nat =
  match tree with
  | N (_, _, c) -> 1 + number_nodes0_list c
and number_nodes0_list (bh: list node0) : nat = 
  match bh with
    | [] -> 0
    | h::hs -> number_nodes0 h + number_nodes0_list hs

let number_nodes (tree: node) : nat = number_nodes0 tree

let rec list_node_to_node0 (l: list node) : list node0 =
  match l with
    | [] -> []
    | n::ns -> n :: list_node_to_node0 ns

let number_nodes_list (l: list node) : nat =
  number_nodes0_list (list_node_to_node0 l)


(*
  Definición de Binomial Heap y sus operaciones
*)
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

let rec children (n: node) : Tot (list node) (decreases (length (children0 n)))
= 
  match n with
    | N (_,_,[]) -> []
    | N (r,k, c::cs) -> c :: children (N (r, k, cs))

let extractMin (bh: bheap{Cons? bh}) : int & bheap =
  let m, hs = removeMinTree bh in 
  root0 m, merge (rev (children m)) hs
  

(*
  Lemas de las operaciones de Binomial Heap
*)

let rec lemma_removeMinTree_size (bh : bheap{Cons? bh})
  : Lemma (number_nodes_list bh == number_nodes_list (snd (removeMinTree bh)) + number_nodes (fst (removeMinTree bh)))
  = 
    match bh with
    | [h] -> ()
    | h::hs -> lemma_removeMinTree_size hs

let rec lemma_rev_go_number_nodes (acc ts : list node)
  : Lemma (ensures number_nodes_list acc + number_nodes_list ts == number_nodes_list (rev_go acc ts))
          (decreases ts)
  =  
    match ts with
     | [] -> ()
     | t::ts -> lemma_rev_go_number_nodes (t::acc) ts

let lemma_rev_number_nodes (ts : list node)
  : Lemma (number_nodes_list ts == number_nodes_list (rev ts))
  = lemma_rev_go_number_nodes [] ts

let rec lemma_insertTree_size (tree: node) (bh: bheap)
  : Lemma (ensures number_nodes_list (insertTree tree bh) == number_nodes tree + number_nodes_list bh)
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
  : Lemma (number_nodes_list (merge bh1 bh2) == number_nodes_list bh1 + number_nodes_list bh2)
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

let rec lemma_size_children0_children (n: node)
 : Lemma (ensures number_nodes_list (children n) == number_nodes0_list (children0 n)) (decreases (length (children0 n)))
 =
  match n with
    | N (_,_, []) -> ()
    | N (r,k, c::cs) ->  lemma_size_children0_children(N (r,k,cs))

let lemma_size_children (n: node)
  : Lemma (number_nodes n == number_nodes_list (children n) + 1) = lemma_size_children0_children n


let lemma_deleteMin_size (bh: bheap{Cons? bh})
  : Lemma (number_nodes_list (snd (extractMin bh)) == number_nodes_list bh - 1)
= 
  let m, hs = removeMinTree bh in
  calc (==) {
    number_nodes_list (snd (extractMin bh));
    == {}
    number_nodes_list (merge (rev (children m)) hs);
    == { lemma_merge_size (rev (children m)) hs } 
    number_nodes_list (rev (children m)) + number_nodes_list hs;
    == {lemma_rev_number_nodes (children m) } 
    number_nodes_list (children m) + number_nodes_list hs;
    == { lemma_size_children m }
    (number_nodes m - 1) + number_nodes_list hs;
    == { lemma_removeMinTree_size bh }
    number_nodes_list bh - 1;
  }

(*
  Transformaciones de Binomial Heaps a listas
*)
let rec toOrderList (bh: bheap) : Tot (list int) (decreases (number_nodes_list bh))=
  match bh with
    | [] -> []
    | _ -> let m, bh' = extractMin bh in
           lemma_deleteMin_size bh;
           m :: toOrderList bh'

let rec elems_node0 (n: node0) : list int =
  let N (x, _, c) = n in
  x :: elems_nodes c
and elems_nodes (cs: list node0) : list int =
  match cs with
    | [] -> []
    | c::cs' -> elems_node0 c @ elems_nodes cs'

let rec toList (bh: bheap) : Tot (list int)=
  match bh with
    | [] -> []
    | h::hs -> elems_node0 h @ toList hs

let clist t = l : list t {Cons? l}

let rec toListList (bh: bheap) : Tot (list (clist int))=
  match bh with
    | [] -> []
    | h::hs -> elems_node0 h :: toListList hs 

let rec fromList (l: list int) : bheap =
  match l with
    | [] -> []
    | x::xs -> insert x (fromList xs)


(*
  Relación de permutación entre listas y 'models' entre Binomial Heap y listas
*)

let rec count (x:int) (l:list int) : nat =
  match l with
    | [] -> 0
    | y::l' -> (if x = y then 1 else 0) + count x l'

let perm (l1 l2: list int) : GTot Type =
  forall (x:int). count x l1 == count x l2

let models (bh : bheap) (xs : list int) : prop =
  perm (toList bh) xs

let (=~) = perm

val min_list (xs: list int{Cons? xs}) : int
let rec min_list xs =
  match xs with
  | [x] -> x
  | x::xs -> min x (min_list xs)

val lemma_min_in_list (xs: list int { length xs > 0 }) :
  Lemma (ensures mem (min_list xs) xs)

let rec lemma_min_in_list xs =
  match xs with
  | [x] -> ()
  | x::xs' ->
    lemma_min_in_list xs'

let rec lemma_count_mem (l:list int) : Lemma
  (ensures forall x. mem x l <==> count x l > 0)
=
  match l with
  | [] -> ()
  | y::ys ->
    lemma_count_mem ys

val lemma_perm_mem : xs:list int -> ys:list int ->
  Lemma (requires perm xs ys)
        (ensures forall x. mem x xs <==> mem x ys)

let lemma_perm_mem xs ys =
  lemma_count_mem xs;
  lemma_count_mem ys

let rec lemma_min_is_le_all (xs: list int { length xs > 0 }) : Lemma
  (ensures forall y. mem y xs ==> min_list xs <= y)
=
  match xs with
  | [x] -> () 
  | x::xs' -> lemma_min_is_le_all xs'

val lemma_min_list_perm (xs : list int{Cons? xs}) (ys : list int)
  : Lemma (requires xs =~ ys)
          (ensures min_list xs == min_list ys)
let lemma_min_list_perm xs ys =
  lemma_perm_mem xs ys;
  lemma_min_in_list xs;
  lemma_min_in_list ys;
  lemma_min_is_le_all xs;
  lemma_min_is_le_all ys
  

let rec lemma_min_list_concat (xs ys : clist int)
  : Lemma (ensures min_list (xs @ ys) == min_list xs `min` min_list ys) (decreases (length (xs@ys)))
  = 
  match xs with
    | [x] -> ()
    | x::xs' -> lemma_min_list_concat xs' ys

let rec lemma_toList_perm (bh: bheap{Cons? bh})
  : Lemma (let minh, rest = removeMinTree bh in toList bh =~ elems_node0 minh @ toList rest) 
= match bh with
    | [h] -> ()
    | h::hs -> admit()

let lemma_minheap_gt_rest (bh: bheap{Cons? bh})
  : Lemma (let minh, rest = removeMinTree bh in assume (Cons? rest); min_list (elems_node0 minh) <= min_list (toList rest)) 
= admit()

let lemma_min_list_root (bh: bheap{Cons? bh})
  : Lemma (let minh, _ = removeMinTree bh in min_list (elems_node0 minh) = root0 minh) 
= admit()


(*
  Lemas de correctitud de las operaciones Binomial Heap
*)
val findMin_ok (bh : bheap) (xs : list int{Cons? xs})
  : Lemma (requires models bh xs)
          (ensures findMin bh == min_list xs)
let findMin_ok bh xs =
  let minh, rest = removeMinTree bh in
  assume (Cons? rest); // hmm....
  calc (==) {
    min_list xs;
    == { lemma_min_list_perm (toList bh) xs }
    min_list (toList bh);
    == { lemma_toList_perm bh;
         lemma_min_list_perm (toList bh) (elems_node0 minh @ toList rest);
         lemma_min_list_concat (elems_node0 minh) (toList rest)
       }
    min_list (elems_node0 minh) `min` min_list (toList rest);
    == { lemma_minheap_gt_rest bh }
    min_list (elems_node0 minh);
    == { lemma_min_list_root bh } // deberia salir facil por propiedad de heap
    root0 minh;
    == {}
    findMin bh;
  }

assume val remove_list (x: int) (xs: list int) : list int

val deleteMin_ok (bh : bheap) (xs : list int{Cons? xs})
  : Lemma (requires models bh xs)
          (ensures models (snd (extractMin bh)) (remove_list (min_list xs) xs))

val insert_ok  (bh : bheap) (x : int) (xs : list int)
  : Lemma (requires models bh xs)
          (ensures models (insert x bh) (x::xs))

assume val merge_sort (xs ys: list int) : list int

assume val merge_ok (bh1 bh2: bheap) (xs ys: list int) 
  : Lemma (requires models bh1 xs /\ models bh2 ys)
          (ensures models (merge bh1 bh2) (xs @ ys))

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