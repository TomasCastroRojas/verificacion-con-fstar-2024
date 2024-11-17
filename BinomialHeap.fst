module BinomialHeap

open FStar.List.Tot

type node = 
  | E 
  | N of int & int & node & node & node // data, degre, child, sibling, parent

let mergeNode (b1: node)  (b2: node) : node =
  match b1, b2 with
  | E, E -> E
  | N (_,_,_,_,_), E -> b1
  | E, N (_,_,_,_,_) -> b2
  | N (d1, deg1, c1, s1, p1), N (d2, deg2, c2, s2, p2) ->
  if d1 < d2 
  then let b3 = N (d2, deg2, c2, c1, b1) in
       N (d1, deg1 + 1, b3, s1, p1)
  else let b4 = N (d1, deg1, c1, c2, b2) in
       N (d2, deg2 + 1, b4, s2, p2)


let rec unionBH' (l1: list node) (l2: list node) : list node =
  match l1, l2 with
  | [], [] -> []
  | l, [] -> l
  | [], l -> l
  | E :: l1', _ -> unionBH' l1' l2
  | _, E :: l2' -> unionBH' l1 l2'
  | n1::l1', n2::l2' -> let (N (_,d1,_,_,_)) = n1 in
                        let (N (_,d2,_,_,_)) = n2 in
                        if d1 <= d2
                        then n1 :: unionBH' l1' l2
                        else n2 :: unionBH' l1 l2'

let rec adjust (l : list node) : Tot (list node) (decreases (length l)) =
  match l with
  | [] -> []
  | [x] -> l
  | E :: l' -> adjust l'
  | x :: (E :: l') -> adjust (x::l')
  | n1 :: (n2 :: l') -> let (N (_,d1,_,_,_)) = n1 in
                        let (N (_,d2,_,_,_)) = n2 in
                        if d1 = d2
                        then adjust ((mergeNode n1 n2) :: l')
                        else n1 :: adjust (n2 :: l')

let union (l1: list node) (l2: list node) : list node =
  adjust (unionBH' l1 l2)

let rec findMin (l: list node{Cons?  l}) : int =
  match l with
  | [E] -> 0
  | [N (d,_,_,_,_)] -> d
  | E :: l' -> findMin l'
  | N (d,_,_,_,_) :: l' -> min d (findMin l')

let insert (x: int) (l: list node) : list node =
  let n = N (x, 0, E, E, E) in
  union [n] l

let rec fromChilds (x: node) : list node =
  match x with
  | E -> []
  | N (_,_,_,s,_) -> x :: fromChilds s

let rec extracMin' (l: list node) (m: int): list node =
  match l with
  | [] -> []
  | [E] -> []
  | [N (_,_,c,_,_)] -> fromChilds c
  | E :: l' -> extracMin' l' m
  | x :: l' -> let N (d,_,c,_,_) = x in
               if d = m
               then fromChilds c @ l'
               else x :: extracMin' l' m

let extractMin (l: list node{Cons?  l}) : list node =
  let m = findMin l in
  adjust (extracMin' l m)

let rec findKey (n: node) (k: int) : bool =
  match n with
  | E -> false
  | N (x, _, c, s, _) -> x = k || findKey c k || findKey s k

// Busqueda en el hermano?
//    3
// 5  6
// 10
// y llamo decreaseKeyNode (N 3) 6 2 ?
let rec decreaseKeyNode (n: node) (k: int) (x: int): node =
  match n with
  | E -> E
  | N (d, deg, c, s, p) -> if d = k
                           then N (x, deg, c, s, p)
                           else let c' = decreaseKeyNode c k x in
                                match c' with
                                | E -> n
                                | N (d', deg', c'', s', p') -> if d' <= d
                                                               then N (d', deg, N (d, deg', c'',s', p'), s, p)
                                                               else N (d, deg, c', s, p)
                                
let rec decreaseKey (l: list node) (k: int) (x: int) : list node =
  match l with
  | [] -> []
  | n::l' -> if findKey n k
             then decreaseKeyNode n k x :: l'
             else n :: decreaseKey l' k x