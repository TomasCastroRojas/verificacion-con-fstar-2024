module BinomialHeap

open FStar.List.Tot
open FStar.Math.Lib
open FStar.Calc
open FStar.Classical

(*
*****************************************************************************
  Definición de la estructura de arboles generales y los predicados de heap.
*****************************************************************************
*)
type node0 = | N of nat & int & list node0 // rank, data, children

(*
  Predicado que verifica si todos los elementos de un árbol son mayores que un valor dado.
  Es decir, que el valor dado es una cota mínima de los elementos del árbol.
*)
let rec all_gt0 (x: int) (tree: node0) : Tot bool =
  match tree with
  | N (r, k, c) -> x <= k && all_gt x c
and all_gt (x: int) (bh: list node0) : Tot bool =
  match bh with
    | [] -> true
    | h::hs -> all_gt0 x h && all_gt x hs

let rec all_gt_trans0 (x y:int) (n: node0)
  : Lemma (requires all_gt0 x n /\ y <= x)
          (ensures  all_gt0 y n)
= match n with
  | N (_, k, cs) -> all_gt_trans x y cs
and all_gt_trans (x y : int) (c : list node0)
  : Lemma (requires all_gt x c /\ y <= x)
          (ensures  all_gt y c)
= match c with
    | [] -> ()
    | c'::cs -> all_gt_trans0 x y c';
                all_gt_trans x y cs

(*
  Propiedad de MinHeap. La raíz de todo arbol es menor a todos sus hijos
*)
let rec is_heap0 (tree: node0) : bool =
  match tree with
  | N (r, k, c) -> all_gt0 k tree && is_heap c
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

(*
  Nodo de un binomial heap
*)
type node = n:node0{is_heap0 n}

let root (tree : node) : int =
  let N (_,r,_) = tree in
  r

(*
**************************************
  Definición de operaciones de nodos
**************************************
*)
let singleton (x: int): node = N (0, x, [])

(*
  Construye un nuevo arbol a partir de otros dos. Esta operación solo tiene sentido si tienen el mismo rango.
  De este modo, se aseguran ciertas propiedades de complejidad por definición (por ejemplo, findMin \in O (lg n)). 
  No se prueban dichas propiedades en este trabajo.
*)
let link0 (tree1 : node0) (tree2 : node0{rank0 tree1 = rank0 tree2}) : node0 =
  match tree1, tree2 with
  | N (r, k1, c1), N (_, k2, c2) -> if k1 <= k2
                                    then N (r + 1, k1, tree2 :: c1)
                                    else N (r + 1, k2, tree1 :: c2)

let link (tree1 : node) (tree2 : node{rank0 tree1 = rank0 tree2}) : node 
= match tree1, tree2 with
  | N (r, k1, c1), N (_, k2, c2) -> if k1 <= k2
                                    then (all_gt_trans0 k2 k1 tree2; N (r + 1, k1, tree2 :: c1))
                                    else (all_gt_trans0 k1 k2 tree1; N (r + 1, k2, tree1 :: c2))

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
*************************************************
  Definición de Binomial Heap y sus operaciones
*************************************************
*)

(*
  Predicado que verifica los rangos de una lista de arboles esta en orden ascendente.
  Las operaciones estan definidas de modo tal de preservar este predicado si bien 
  no se verifican propiedades respecto a esto. Por eso no se incluye en el refinamiento del tipo `bheap`
*)
let rec incr_rank (hs : list node) : prop =
  match hs with
  | [] -> True
  | [_] -> True
  | h1::h2::hs' -> rank0 h1 < rank0 h2 /\ incr_rank (h2::hs')

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

let rec children (n: node) : Tot (list node) (decreases (length (children0 n)))
= 
  match n with
    | N (_,_,[]) -> []
    | N (r,k, c::cs) -> c :: children (N (r, k, cs))

let extractMin (bh: bheap{Cons? bh}) : int & bheap =
  let m, hs = removeMinTree bh in 
  root0 m, merge (rev (children m)) hs
  

(*
*****************************************************************
  Lemas de las operaciones de Binomial Heap respecto a su tamaño
*****************************************************************
*)

let rec lemma_removeMinTree_size (bh : bheap{Cons? bh})
  : Lemma (number_nodes_list bh == number_nodes_list (snd (removeMinTree bh)) + number_nodes (fst (removeMinTree bh)))
  = 
    match bh with
    | [h] -> ()
    | h::hs -> lemma_removeMinTree_size hs

let rec lemma_rev_go_number_nodes (ts acc: list node)
  : Lemma (ensures number_nodes_list ts + number_nodes_list acc == number_nodes_list (rev_acc ts acc))
          (decreases ts)
  =  
    match ts with
     | [] -> ()
     | t::ts' -> lemma_rev_go_number_nodes ts' (t::acc)

let lemma_rev_number_nodes (ts : list node)
  : Lemma (number_nodes_list ts == number_nodes_list (rev ts))
  = lemma_rev_go_number_nodes ts []

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
         [SMTPat (number_nodes_list (children n))]
 =
  match n with
    | N (_,_, []) -> ()
    | N (r,k, c::cs) ->  lemma_size_children0_children(N (r,k,cs))

let lemma_size_children (n: node)
  : Lemma (number_nodes n == number_nodes_list (children n) + 1) 
          [SMTPat (number_nodes n)]
= lemma_size_children0_children n


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
***********************************************
  Transformaciones de Binomial Heaps a listas
***********************************************
*)

(*
  Construye una lista ordenada de números sacando sucesivamente el mínimo del heap.
  Podría utilizarse para la relación `models` y verificar propiedades de listas ordenadas respecto a las queues.
*)
let rec toOrderList (bh: bheap) : Tot (list int) (decreases (number_nodes_list bh))=
  match bh with
    | [] -> []
    | _ -> let m, bh' = extractMin bh in
           lemma_deleteMin_size bh;
           m :: toOrderList bh'

let rec elems_node0 (n: node0) : list int =
  let N (_, x, c) = n in
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

let rec fromList (l: list int) : bheap =
  match l with
    | [] -> []
    | x::xs -> insert x (fromList xs)


(*
*******************************************************************************
  Relación de permutación entre listas y 'models' entre Binomial Heap y listas
*******************************************************************************
*)

let rec count (x:int) (l:list int) : nat =
  match l with
    | [] -> 0
    | y::l' -> (if x = y then 1 else 0) + count x l'

(*
  Dos listas son permutaciones si tienen el mismo "contenido" sin importar el orden.
*)
let perm (l1 l2: list int) : GTot Type =
  forall (x:int). count x l1 == count x l2

(*
  Un binomial heap 'modela' una lista si transformandolo a lista contiene la misma información.
*)
let models (bh : bheap) (xs : list int) : prop =
  perm (toList bh) xs

let (=~) = perm

val min_list (xs: clist int) : int
let rec min_list xs =
  match xs with
  | [x] -> x
  | x::xs -> min x (min_list xs)

val lemma_min_in_list (xs: clist int) :
  Lemma (ensures mem (min_list xs) xs)

let rec lemma_min_in_list xs =
  match xs with
  | [x] -> ()
  | x::xs' ->
    lemma_min_in_list xs'

let rec lemma_count_mem (l:list int) 
 : Lemma (ensures forall x. mem x l <==> count x l > 0)
=
  match l with
  | [] -> ()
  | y::ys ->
    lemma_count_mem ys

val lemma_perm_mem : xs:list int -> ys:list int ->
  Lemma (requires xs =~ ys)
        (ensures forall x. mem x xs <==> mem x ys)

let lemma_perm_mem xs ys =
  lemma_count_mem xs;
  lemma_count_mem ys

let rec lemma_min_is_le_all (xs: clist int) (y : int) : Lemma
  (ensures mem y xs ==> min_list xs <= y)
=
  match xs with
  | [x] -> () 
  | x::xs' -> lemma_min_is_le_all xs' y

val lemma_min_list_perm (xs : clist int) (ys : list int)
  : Lemma (requires xs =~ ys)
          (ensures min_list xs == min_list ys)
let lemma_min_list_perm xs ys =
  let mx = min_list xs in
  let my = min_list ys in
  lemma_min_in_list xs;
  lemma_min_in_list ys;
  lemma_perm_mem xs ys;
  assert (mem mx ys);
  assert (mem my xs);
  lemma_min_is_le_all xs my;
  lemma_min_is_le_all ys mx
  

let rec lemma_min_list_concat (xs ys : clist int)
  : Lemma (ensures min_list (xs @ ys) == min_list xs `min` min_list ys) (decreases (length (xs@ys)))
  = 
  match xs with
    | [x] -> ()
    | x::xs' -> lemma_min_list_concat xs' ys

let rec __count_append (l1 l2: list int) (x:int)
  : Lemma (count x (l1 @ l2) == count x l1 + count x l2)
=
  match l1 with
  | [] -> ()
  | y::ys -> __count_append ys l2 x

let count_append (l1 l2: list int)
  : Lemma (forall x. count x (l1 @ l2) == count x l1 + count x l2)
= FStar.Classical.forall_intro (__count_append l1 l2)

let perm_comm (l1 l2:list int)
  : Lemma (perm (l1 @ l2) (l2 @ l1)) 
=
  count_append l1 l2;
  count_append l2 l1

let perm_sym (l1 l2: list int) 
  : Lemma (requires perm l1 l2)
          (ensures perm l2 l1) = ()

let perm_trans (l1 l2 l3: list int)
  : Lemma (requires perm l1 l2 /\ perm l2 l3)
          (ensures perm l1 l3) = ()

let rec perm_preappend (l1 l2 l3: list int)
  : Lemma (requires perm l2 l3)
          (ensures perm (l1 @ l2) (l1 @ l3))
=
 match l1 with
  | [] -> ()
  | x::xs -> perm_preappend xs l2 l3

let perm_append (l1 l2 l3 l4: list int)
  : Lemma (requires perm l1 l3 /\ perm l2 l4)
          (ensures perm (l1 @ l2) (l3 @ l4)) 
=
  count_append l1 l2;
  count_append l3 l4

let perm_postappend (l1 l2 l3: list int)
  : Lemma (requires perm l1 l2)
          (ensures perm (l1 @ l3) (l2 @ l3))
=
  perm_append l1 l3 l2 l3

let rec append_assoc (l1 l2 l3: list int)
  : Lemma (l1 @ (l2 @ l3) == (l1 @ l2) @ l3) 
=
  match l1 with
    | [] -> ()
    | x::xs -> append_assoc xs l2 l3

let perm_comm_assoc_left (l1 l2 l3: list int)
  : Lemma (perm ((l1 @ l2) @ l3) ((l2 @ l1) @ l3))
= 
  perm_comm l1 l2; perm_postappend (l1 @ l2) (l2 @ l1) l3

let perm_comm_assoc_right (l1 l2 l3: list int)
  : Lemma (perm (l1 @ (l2 @ l3)) (l1 @ (l3 @ l2)))
= 
  perm_comm l2 l3; perm_preappend l1 (l2 @ l3) (l3 @ l2)

let rec lemma_removeMinTree_perm (bh: bheap{Cons? bh})
  : Lemma (let minh, rest = removeMinTree bh in toList bh =~ elems_node0 minh @ toList rest) 
= match bh with
    | [h] -> ()
    | h::hs -> let m, hs' = removeMinTree hs in
               if root0 h < root0 m
               then ()
               else calc (=~)
               {
                toList bh;
                =~ {}
                elems_node0 h @ toList hs;
                =~ {lemma_removeMinTree_perm hs; perm_preappend (elems_node0 h) (toList hs) (elems_node0 m @ toList hs')}
                elems_node0 h @ (elems_node0 m @ toList hs');
                == {append_assoc (elems_node0 h) (elems_node0 m) (toList hs')}
                (elems_node0 h @ elems_node0 m) @ toList hs';
                =~ {perm_comm_assoc_left (elems_node0 h) (elems_node0 m) (toList hs')}
                (elems_node0 m @ elems_node0 h) @ toList hs';
                == {append_assoc (elems_node0 m) (elems_node0 h) (toList hs')}
                elems_node0 m @ (elems_node0 h @ toList hs');
               }

let lemma_node_is_heap0 (n: node) : Lemma
  (ensures (
    let N (_, k, cs) = n in
    is_heap0 n /\ is_heap cs
  ))
= ()

let rec all_gt_list_elem_mem (k : int) (cs : list node0) (x : int)
  : Lemma (requires all_gt k cs /\
                    mem x (elems_nodes cs))
          (ensures  k <= x)
= match cs with
  | [] -> ()
  | c :: cs'  ->
    append_mem (elems_node0 c) (elems_nodes cs') x;
    if mem x (elems_node0 c) 
    then (
      all_gt_list_elem_mem0 k c x
    ) 
    else (
      all_gt_list_elem_mem k cs' x
    )

and all_gt_list_elem_mem0 (k : int) (c : node0) (x : int)
  : Lemma (requires all_gt0 k c /\ mem x (elems_node0 c))
          (ensures  k <= x)
  = let N (_, x', cs) = c in
    if x <> x' 
    then (
      all_gt_list_elem_mem k cs x
    )

let __lemma_root_gt_children (n : node) (x:int)
  : Lemma (ensures (mem x (elems_nodes (children0 n)) ==> root0 n <= x))
= Classical.move_requires (all_gt_list_elem_mem (root0 n) (children0 n)) x

let lemma_root_gt_children (n : node)
  : Lemma (ensures (forall x. mem x (elems_nodes (children0 n)) ==> root0 n <= x))
= Classical.forall_intro (__lemma_root_gt_children n)

let lemma_root_gt_min_children (n: node)
  : Lemma (ensures (match children0 n with | [] -> True | cs -> root0 n <= min_list (elems_nodes cs)))
= match children0 n with
  | [] -> ()
  | cs ->
    lemma_min_in_list (elems_nodes cs);
    lemma_root_gt_children n

let lemma_min_node_root (n: node)
  : Lemma (ensures min_list (elems_node0 n) == root0 n) 
= 
  let N (_, k, cs) = n in
  match cs with
  | [] -> ()
  | _ -> 
    calc (==) {
      min_list (elems_node0 n);
      == {}
      min_list (k :: elems_nodes cs);
      == {}
      min_list ([k] @ elems_nodes cs);
      == { lemma_min_list_concat [k] (elems_nodes cs) }
      min_list ([k]) `min` min_list (elems_nodes cs);
      == { }
      k `min` min_list (elems_nodes cs);
      == { lemma_root_gt_min_children n }
      k;
    }

let lemma_min_append (min heap:node) (bh: bheap{Cons? bh})
  : Lemma (requires (min_list (elems_node0 min) <= min_list (elems_node0 heap) /\ min_list (elems_node0 min) <= min_list (toList bh)))
          (ensures min_list (elems_node0 min) <= min_list (elems_node0 heap @ toList bh)) 
= lemma_min_list_concat (elems_node0 heap) (toList bh)

let lemma_min_trans (min heap:node) (bh: bheap{Cons? bh})
  : Lemma (requires min_list (elems_node0 min) <= min_list (elems_node0 heap) /\ min_list (elems_node0 heap) <= min_list (toList bh))
          (ensures min_list (elems_node0 min) <= min_list (toList bh)) = ()

let lemma_min_root_elems (h1 h2: node)
  : Lemma (requires root0 h1 <= root0 h2)
          (ensures min_list (elems_node0 h1) <= min_list (elems_node0 h2))
= lemma_min_node_root h1;
  lemma_min_node_root h2


let min_of_removeMinTree (bh:bheap{Cons? bh})
  : Lemma (
    let minh, rest = removeMinTree bh in
    match rest with
      | [] -> min_list (toList bh) == min_list (elems_node0 minh)
      | _ -> min_list (toList bh) == min (min_list (elems_node0 minh)) (min_list (toList rest))
  )
= let minh, rest = removeMinTree bh in
  match rest with
    | [] -> ()
    | _ ->
      calc (==) {
        min_list (toList bh);
        == { lemma_removeMinTree_perm bh; lemma_min_list_perm (toList bh) (elems_node0 minh @ toList rest) }
        min_list (elems_node0 minh @ toList rest);
        == { lemma_min_list_concat (elems_node0 minh) (toList rest) }
        min_list (elems_node0 minh) `min` min_list (toList rest);
      }
let rec lemma_minheap_gt_rest (bh: bheap{Cons? bh})
  : Lemma (
    let minh, rest = removeMinTree bh in 
    match rest with 
      | [] -> True 
      | _ -> min_list (elems_node0 minh) <= min_list (toList rest)
    ) 
= 
  match bh with
  | [h] -> ()
  | h::hs ->
      let minh, hs' = removeMinTree hs in
      match hs' with
      | [] -> if root0 h < root0 minh 
              then lemma_min_root_elems h minh
              else lemma_min_root_elems minh h
      | _ ->
        lemma_minheap_gt_rest hs;
        min_of_removeMinTree hs;
        if root0 h < root0 minh 
        then (
          lemma_min_root_elems h minh;
          lemma_min_append h minh hs'
        )
        else (
          lemma_min_root_elems minh h;
          lemma_min_append minh h hs'
        )

let rec lemma_min_removeMintree (bh: bheap{Cons? bh})
  : Lemma (let minh, _ = removeMinTree bh in min_list (toList bh) = root0 minh) 
= 
  match bh with
    | [h] -> lemma_min_node_root h
    | h::hs -> let minh, _ = removeMinTree hs in
               lemma_min_removeMintree hs;
               min_of_removeMinTree bh;
               lemma_minheap_gt_rest bh;
               if root0 h < root0 minh
               then lemma_min_node_root h
               else lemma_min_node_root minh

let lemma_link_perm (tree1 tree2: node)
  : Lemma (requires rank0 tree1 = rank0 tree2)
          (ensures perm (elems_node0 (link tree1 tree2)) (elems_node0 tree1 @ elems_node0 tree2))
=
  let N (r1, k1, c1) = tree1 in
  let N (_, k2, c2) = tree2 in
  if k1 <= k2
  then calc (=~) {
    elems_node0 (link tree1 tree2);
    == {}
    elems_node0 (N (r1 + 1, k1, tree2 :: c1));
    == {}
    k1 :: elems_nodes (tree2 :: c1);
    == {  }
    k1 :: elems_node0 tree2 @ elems_nodes c1;
    =~ { perm_comm_assoc_right [k1] (elems_node0 tree2) (elems_nodes c1) }
    k1 :: elems_nodes c1 @ elems_node0 tree2;
    == { }
    elems_node0 tree1 @ elems_node0 tree2;
  }
  else calc (=~) {
    elems_node0 (link tree1 tree2);
    == {}
    elems_node0 (N (r1 + 1, k2, tree1 :: c2));
    == {}
    k2 :: elems_nodes (tree1 :: c2);
    == {  }
    k2 :: elems_node0 tree1 @ elems_nodes c2;
    =~ { perm_comm_assoc_right [k2] (elems_node0 tree1) (elems_nodes c2) }
    k2 :: elems_nodes c2 @ elems_node0 tree1;
    == { }
    elems_node0 tree2 @ elems_node0 tree1;
    =~ { perm_comm (elems_node0 tree1) (elems_node0 tree2) }
    elems_node0 tree1 @ elems_node0 tree2;
  }

let rec lemma_insertTree_perm (tree: node) (bh: bheap)
  : Lemma (ensures perm (toList (insertTree tree bh)) (elems_node0 tree @ toList bh))
          (decreases (length bh))
=
  match bh with
  | [] -> ()
  | h::hs -> if rank0 tree < rank0 h
             then ()
             else if rank0 tree = rank0 h
                  then calc (=~) {
                    toList (insertTree (link tree h) hs);
                    =~ { lemma_insertTree_perm (link tree h) hs }
                    elems_node0 (link tree h) @ toList hs;
                    =~ { lemma_link_perm tree h; perm_postappend (elems_node0 (link tree h)) ((elems_node0 tree) @ (elems_node0 h)) (toList hs) }
                    (elems_node0 tree @ elems_node0 h) @ toList hs;
                    == { append_assoc (elems_node0 tree) (elems_node0 h) (toList hs) }
                    elems_node0 tree @ (elems_node0 h @ toList hs);
                  }
                  else calc (=~) {
                    toList (h :: insertTree tree hs);
                    == {  }
                    elems_node0 h @ toList (insertTree tree hs);
                    =~ { lemma_insertTree_perm tree hs; perm_preappend (elems_node0 h) (toList (insertTree tree hs)) ((elems_node0 tree) @ (toList hs)) }
                    elems_node0 h @ (elems_node0 tree @ toList hs);
                    == { append_assoc (elems_node0 h) (elems_node0 tree) (toList hs) }
                    (elems_node0 h @ elems_node0 tree) @ toList hs; 
                    =~ {perm_comm_assoc_left (elems_node0 h) (elems_node0 tree) (toList hs)}
                    (elems_node0 tree @ elems_node0 h) @ toList hs;
                    == { append_assoc (elems_node0 tree) (elems_node0 h) (toList hs)}
                    elems_node0 tree @ (elems_node0 h @ toList hs);
                  }     

val remove_list (x: int) (xs: list int) : list int

let rec remove_list x xs =
  match xs with
  | [] -> []
  | y::ys -> if x = y then ys else y :: remove_list x ys

let rec lemma_merge_perm (bh1 bh2: bheap)
  : Lemma (ensures perm (toList (merge bh1 bh2)) ((toList bh1) @ toList bh2))
          (decreases (length bh1 + length bh2))
= match bh1, bh2 with
  | [], _ -> ()
  | _, [] -> ()
  | h1::hs1, h2::hs2 -> if rank0 h1 < rank0 h2
                        then calc (=~) {
                          toList (merge bh1 bh2);
                          == {  }
                          toList (h1 :: merge hs1 bh2);
                          == { }
                          elems_node0 h1 @ toList (merge hs1 bh2);
                          =~ { lemma_merge_perm hs1 bh2; perm_preappend (elems_node0 h1) (toList (merge hs1 bh2)) (toList hs1 @ toList bh2) }
                          elems_node0 h1 @ (toList hs1 @ toList bh2);
                          == { append_assoc (elems_node0 h1) (toList hs1) (toList bh2) }
                          (elems_node0 h1 @ toList hs1) @ toList bh2;
                        }
                        else if rank0 h1 > rank0 h2
                             then calc (=~) {
                               toList (merge bh1 bh2);
                               == { }
                               toList (h2 :: merge bh1 hs2);
                               == { }
                               elems_node0 h2 @ toList (merge bh1 hs2);
                               =~ { lemma_merge_perm bh1 hs2; perm_preappend (elems_node0 h2) (toList (merge bh1 hs2)) (toList bh1 @ toList hs2) }
                               elems_node0 h2 @ (toList bh1 @ toList hs2);
                               == { append_assoc (elems_node0 h2) (toList bh1) (toList hs2) }
                               (elems_node0 h2 @ toList bh1) @ toList hs2;
                               =~ { perm_comm_assoc_left (elems_node0 h2) (toList bh1) (toList hs2) }
                               (toList bh1 @ elems_node0 h2) @ toList hs2;
                               == { append_assoc (toList bh1) (elems_node0 h2) (toList hs2) }
                               toList bh1 @ (elems_node0 h2 @ toList hs2);
                             }
                             else calc (=~) {
                               toList (merge bh1 bh2);
                               == {  }
                               toList (insertTree (link h1 h2) (merge hs1 hs2));
                               =~ { lemma_insertTree_perm (link h1 h2) (merge hs1 hs2) }
                               elems_node0 (link h1 h2) @ toList (merge hs1 hs2);
                               =~ { lemma_link_perm h1 h2;
                                    perm_postappend (elems_node0 (link h1 h2)) ((elems_node0 h1) @ (elems_node0 h2)) (toList (merge hs1 hs2)) }
                               (elems_node0 h1 @ elems_node0 h2) @ toList (merge hs1 hs2);
                               =~ { lemma_merge_perm hs1 hs2;
                                    perm_preappend (elems_node0 h1 @ elems_node0 h2) (toList (merge hs1 hs2)) (toList hs1 @ toList hs2) }
                               (elems_node0 h1 @ elems_node0 h2) @ (toList hs1 @ toList hs2);
                               == { append_assoc (elems_node0 h1) (elems_node0 h2) (toList hs1 @ toList hs2) }
                               elems_node0 h1 @ (elems_node0 h2 @ (toList hs1 @ toList hs2));
                               == { append_assoc (elems_node0 h2) (toList hs1) (toList hs2) }
                               elems_node0 h1 @ ((elems_node0 h2 @ toList hs1) @ toList hs2);
                               =~ { perm_comm_assoc_left (elems_node0 h2) (toList hs1) (toList hs2);
                                    perm_preappend (elems_node0 h1) ((elems_node0 h2 @ toList hs1) @ toList hs2) ((toList hs1 @ elems_node0 h2) @ toList hs2) }
                               elems_node0 h1 @ ((toList hs1 @ elems_node0 h2) @ toList hs2);
                               == { append_assoc (toList hs1) (elems_node0 h2) (toList hs2) }
                               elems_node0 h1 @ (toList hs1 @ (elems_node0 h2 @ toList hs2));
                               == { append_assoc (elems_node0 h1) (toList hs1) (elems_node0 h2 @ toList hs2) }
                               (elems_node0 h1 @ toList hs1) @ (elems_node0 h2 @ toList hs2);
                             }

let rec lemma_cons_perm_int (x: int) (xs: list int)
  : Lemma (ensures perm (x::xs) (xs @ [x]))
=
  match xs with
  | [] -> ()
  | y::ys -> lemma_cons_perm_int x ys

let rec lemma_cons_append_perm_int (x: int) (xs ys: list int)
  : Lemma (ensures perm (x::xs @ ys) (xs @ (x::ys)))
= 
  match xs with
  | [] -> lemma_cons_perm_int x ys
  | _::xs' -> lemma_cons_append_perm_int x xs' ys

let rec lemma_rev_go_perm_int (acc xs: list int)
  : Lemma (ensures perm (rev_acc xs acc) (xs @ acc))
          (decreases xs)
= match xs with
  | [] -> ()
  | x::xs' -> lemma_cons_append_perm_int x xs' acc; lemma_rev_go_perm_int (x::acc) xs'

let lemma_rev_perm_int (xs: list int)
  : Lemma (ensures perm (rev xs) xs)
= lemma_rev_go_perm_int [] xs

let rec lemma_toList_append (l1 l2: bheap)
  : Lemma (ensures toList (l1 @ l2) == (toList l1 @ toList l2))
= match l1 with
    | [] -> ()
    | h::hs -> 
      calc (==) {
        toList (l1 @ l2);
        == {}
        toList ((h::hs) @ l2);
        == {}
        elems_node0 h @ toList (hs @ l2);
        == { lemma_toList_append hs l2 }
        elems_node0 h @ (toList hs @ toList l2);
        == { append_assoc (elems_node0 h) (toList hs) (toList l2)}
        (elems_node0 h @ toList hs) @ toList l2;
      }

let rec lemma_rev_perm_bheap (bh: bheap)
  : Lemma (toList (rev bh) =~ toList bh)
= match bh with
  | [] -> ()
  | h :: t ->
    calc (=~) {
      toList bh;
      == {}
      toList (h :: t);
      == {}
      elems_node0 h @ toList t;
      =~ { perm_comm (elems_node0 h) (toList t) }
      toList t @ elems_node0 h;
      =~ { lemma_rev_perm_bheap t;
          perm_postappend (toList t) (toList (rev t)) (elems_node0 h)
        }
      toList (rev t) @ elems_node0 h;
      == {}
      toList (rev t) @ toList [h];
      =~ { lemma_toList_append (rev t) [h] }
      toList (rev t @ [h]);
      == { rev_append [h] t }
      toList (rev (h :: t));
      == {}
      toList (rev bh);
    }

let lemma_extractMin_perm (bh: bheap{Cons? bh})
  : Lemma (let minh, rest = removeMinTree bh in
           toList (snd (extractMin bh)) =~ (toList (children minh)) @ (toList rest))
= let minh, rest = removeMinTree bh in
  calc (=~) {
  toList (snd (extractMin bh));
  == { }
  toList (merge (rev (children minh)) rest);
  =~ { lemma_merge_perm (rev (children minh)) rest }
  toList (rev (children minh)) @ toList rest;
  =~ { lemma_rev_perm_bheap (children minh);
       perm_postappend (toList (rev (children minh))) (toList (children minh)) (toList rest) }
  toList (children minh) @ toList rest;
}

let rec lemma_removeList_count_elem_mem (x: int) (xs: list int)
  : Lemma (ensures mem x xs ==> count x (remove_list x xs) == count x xs - 1)
= match xs with
  | [] -> ()
  | y::ys -> if x = y
             then ()
             else lemma_removeList_count_elem_mem x ys

let lemma_removeList_minList (xs: list int{Cons? xs})
  : Lemma (ensures count (min_list xs) (remove_list (min_list xs) xs) == count (min_list xs) xs - 1)
= lemma_min_in_list xs; lemma_removeList_count_elem_mem (min_list xs) xs

let rec lemma_toList_children_equal (n: node)
  : Lemma (ensures toList (children n) == elems_nodes (children0 n))
          (decreases (length (children0 n)))
= let N (r, k, c) = n in
  match c with
  | [] -> ()
  | _::cs -> lemma_toList_children_equal (N (r, k, cs))

let lemma_removeList_neutro (x:int) (xs:list int)
  : Lemma (remove_list x (x::xs) == xs)
= ()

let lemma_removeList_node (n: node)
  : Lemma (ensures count (root0 n) (elems_node0 n) == count (root0 n) (toList (children n)) + 1)
= let N (_, k, c) = n in
  match c with
  | [] -> ()
  | _ -> calc (==) {
    count (root0 n) (elems_node0 n);
    == { }
    count k (k :: elems_nodes c);
    == { count_append [k] (elems_nodes c) }
    count k [k] + count k (elems_nodes c);
    == { }
    1 + count k (elems_nodes c);
    == { lemma_toList_children_equal n }
    1 + count k (toList (children n));
  }

let lemma_node_perm_children (n: node)
  : Lemma (ensures perm (elems_node0 n) (root0 n :: (toList (children n))))
= lemma_toList_children_equal n
let lemma_removeList_perm_node (n: node)
  : Lemma (ensures perm (remove_list (root0 n) (elems_node0 n)) (toList (children n)))
= lemma_node_perm_children n; lemma_removeList_node n

let lemma_removeMinTree_min_perm (bh: bheap{Cons? bh})
  : Lemma (let minh, rest = removeMinTree bh in
           toList (children minh) =~ (remove_list (root0 minh) (elems_node0 minh)))
= lemma_removeList_perm_node (fst (removeMinTree bh))

let rec __lemma_removeList_count_elems (xs: list int) (x y: int)
  : Lemma (requires x <> y)
          (ensures count y xs == count y (remove_list x xs))
= match xs with
    | [] -> ()
    | x'::xs' -> __lemma_removeList_count_elems xs' x y

let lemma_removeList_count_elems (xs : list int) (x: int)
  : Lemma (forall y. x <> y ==> count y xs == count y (remove_list x xs))
= FStar.Classical.forall_intro (FStar.Classical.move_requires (__lemma_removeList_count_elems xs x))

let lemma_append_mem (x: int) (xs ys: list int)
  : Lemma (requires mem x xs)
          (ensures mem x (xs@ys))
= append_mem xs ys x

let lemma_removeList_append (x: int) (xs ys: list int)
  : Lemma (requires mem x xs)
          (ensures perm ((remove_list x xs) @ ys) (remove_list x (xs @ ys)))
= lemma_removeList_count_elem_mem x xs;
  lemma_removeList_count_elems xs x;
  lemma_removeList_count_elems (xs @ ys) x;
  count_append (remove_list x xs) ys;
  count_append xs ys;
  lemma_append_mem x xs ys;
  lemma_removeList_count_elem_mem x (xs @ ys)

let rec lemma_not_mem_count (xs: list int) (x: int)
  : Lemma (requires ~ (mem x xs))
          (ensures count x xs == 0)
= match xs with
    | [] -> ()
    | x'::xs' -> lemma_not_mem_count xs' x

let rec lemma_removeList_elem_notmem (xs: list int) (x: int)
  : Lemma (requires ~ (mem x xs))
          (ensures remove_list x xs == xs)
= match xs with
  | [] -> ()
  | x'::xs' -> lemma_removeList_elem_notmem xs' x

let lemma_removeList_perm (x: int) (xs ys: list int)
  : Lemma (requires xs =~ ys)
          (ensures remove_list x xs =~ remove_list x ys)
= lemma_perm_mem xs ys;
  if mem x xs then (
    lemma_removeList_count_elem_mem x xs;
    lemma_removeList_count_elem_mem x ys;
    lemma_removeList_count_elems xs x;
    lemma_removeList_count_elems ys x
  ) else (
    lemma_removeList_elem_notmem xs x;
    lemma_removeList_elem_notmem ys x
  )
(*
**********************************************************
  Lemas de correctitud de las operaciones Binomial Heap
**********************************************************
*)

(*
  La operación findMin es lo mismo que buscar el mínimo de la lista.
*)
val findMin_ok (bh : bheap) (xs : list int{Cons? xs})
  : Lemma (requires models bh xs)
          (ensures findMin bh == min_list xs)
let findMin_ok bh xs =
  let minh, _ = removeMinTree bh in
  calc (==) {
    min_list xs;
    == { lemma_min_list_perm (toList bh) xs }
    min_list (toList bh);
    == { lemma_min_removeMintree bh }
    root0 minh;
    == {}
    findMin bh;
  }

(*
  La operación deleteMin es lo mismo que eliminar el mínimo de la lista.
*)
val deleteMin_ok (bh : bheap) (xs : list int{Cons? xs})
  : Lemma (requires models bh xs)
          (ensures models (snd (extractMin bh)) (remove_list (min_list xs) xs))

let deleteMin_ok bh xs =
  let minh, rest = removeMinTree bh in
  calc (=~) {
    toList (snd (extractMin bh));
    == { }
    toList (merge (rev (children minh)) rest);
    =~ { lemma_merge_perm (rev (children minh)) rest }
    toList (rev (children minh)) @ toList rest;
    =~ { lemma_rev_perm_bheap (children minh); 
         perm_postappend (toList (rev (children minh))) (toList (children minh)) (toList rest) }
    toList (children minh) @ toList rest;
    =~ { lemma_removeMinTree_min_perm bh;
         perm_postappend (toList (children minh)) (remove_list (root0 minh) (elems_node0 minh)) (toList rest) }
    (remove_list (root0 minh) (elems_node0 minh)) @ toList rest;
    =~ { lemma_removeList_append (root0 minh) (elems_node0 minh) (toList rest) }
    remove_list (root0 minh) (elems_node0 minh @ toList rest);
    =~ { lemma_removeMinTree_perm bh;
         lemma_removeList_perm (root0 minh) (toList bh) (elems_node0 minh @ toList rest) }
    remove_list (root0 minh) (toList bh);
    == { lemma_min_removeMintree bh }
    remove_list (min_list (toList bh)) (toList bh);
    == { lemma_min_list_perm (toList bh) xs }
    remove_list (min_list xs) (toList bh);
    =~ { lemma_removeList_perm (min_list xs) (toList bh) xs }
    remove_list (min_list xs) xs;
  }

(*
  La operación insert es lo mismo que agregar un nuevo elemento a la lista.
*)
val insert_ok  (bh : bheap) (x : int) (xs : list int)
  : Lemma (requires models bh xs)
          (ensures models (insert x bh) (x::xs))

let insert_ok bh x xs = lemma_insertTree_perm (singleton x) bh