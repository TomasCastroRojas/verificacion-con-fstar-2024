module InsertionSort

let rec count (x:int) (l:list int) : nat =
  match l with
    | [] -> 0
    | y::l' -> (if x = y then 1 else 0) + count x l'

let perm (l1 l2: list int) : GTot Type =
  forall (x:int). count x l1 == count x l2

let rec sorted  (xs: list int) : bool =
  match xs with
    | []
    | [_] -> true
    | x::y::l' ->  x <= y && sorted (y::l')

let rec insert (x: int) (l:list int) : list int =
  match l with
    | [] -> [x]
    | y::l' ->
      if x <= y
      then x::l
      else y :: (insert x l')

let rec lem_insert_perm x l
  : Lemma (perm (x::l) (insert x l))
= match l with
    | [] -> ()
    | y::l' -> lem_insert_perm x l'

let rec lem_insert_sorted x l
  : Lemma (requires sorted l) (ensures sorted (insert x l))
= match l with
    | [] -> ()
    | y::l' -> lem_insert_sorted x l'

let rec insertion_sort (xs: list int) :
  xs':(list int){perm xs xs' /\ sorted xs'}
= match xs with
    | [] -> []
    | x::xs ->
      lem_insert_perm x (insertion_sort xs);
      lem_insert_sorted x (insertion_sort xs);
      insert x (insertion_sort xs)