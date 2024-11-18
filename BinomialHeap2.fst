module BinomialHeap2

open FStar.List.Tot

type node0 = | N of int & int & list node0

let rank (tree : node0) : int =
  let N (r,_,_) = tree in
  r

let root (tree : node0) : int =
  let N (_,r,_) = tree in
  r

let children (tree : node0) : list node0 =
  let N (_,_,c) = tree in
  c

let singleton (x: int): node0 = N (0, x, [])

let link (tree1 : node0) (tree2 : node0{rank tree2 = rank tree1}) : node0 =
  match tree1, tree2 with
  | N (r1, k1, c1), N (r2, k2, c2) -> if k1 <= k2
                                      then N (r1 + 1, k1, tree2 :: c1)
                                      else N (r2 + 1, k2, tree1 :: c2)

let rec all_nodes (f: node0 -> bool) (l: list node0) : bool =
  match l with
  | [] -> true
  | x::xs' -> f x && all_nodes f xs'

[@@expect_failure]
// Como expresar recursivamente la propiedad en la lista de hijos?
let rec min_heap (x: int) (tree: node0) : bool =
  match tree with
  | N (r, k, c) -> k <= x && all_nodes (min_heap x) c

[@@expect_failure]
// Como expresar recursivamente la propiedad en la lista de hijos?
let rec is_heap (x: int) (tree: node0) : bool =
  match tree with
  | N (r, k, c) -> min_heap k tree && all_nodes (is_heap x) c

type heap = list node0

let emptyHeap : heap = []

let isEmptyHeap (h: heap) : bool =
  match h with
  | [] -> true
  | _ -> false

let rec insertTree (t: node0) (bh: heap) : Tot heap (decreases (length bh))=
  match bh with
  | [] -> [t]
  | h::hs -> if rank t < rank h
             then t::bh
             else if rank t = rank h
                  then insertTree (link t h) hs
                  else h :: insertTree t hs

let insert (x: int) (h: heap) : heap =
  insertTree (singleton x) h

let rec merge (bh1: heap) (bh2: heap) : heap =
  match bh1, bh2 with
  | [], _ -> bh2
  | _, [] -> bh1
  | h1::hs1, h2::hs2 -> if rank h1 < rank h2
                        then h1 :: merge hs1 bh2
                        else if rank h1 = rank h2
                              then insertTree (link h1 h2) (merge hs1 hs2)
                              else h2 :: merge bh1 hs2

let rec removeMinTree (bh: heap{Cons? bh}) : node0 & heap =
  match bh with
  | [h] -> (h, [])
  | h::hs -> let m, hs' = removeMinTree hs in
             if root h <= root m
             then (h, hs)
             else (m, h::hs')

let findMin (bh: heap{Cons? bh}) : int =
  let m, _ = removeMinTree bh in root m

let rev (#a:Type) (xs : list a) : list a =
  let rec go (acc xs : list a) : Tot (list a) (decreases xs)=
    match xs with
    | [] -> acc
    | x::xs -> go (x::acc) xs
  in
  go [] xs

let deleteMin (bh: heap{Cons? bh}) : heap =
  let m, hs = removeMinTree bh in
  merge (rev (children m)) hs