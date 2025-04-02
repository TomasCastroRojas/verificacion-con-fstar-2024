module InsertionSort

type ord a = f:(a -> a -> bool){forall x y. not (f x y) ==> f x y}

let rec count (#a: eqtype) (x:a) (l:list a) : nat =
  match l with
    | [] -> 0
    | y::l' -> (if x = y then 1 else 0) + count x l'

let perm (#a: eqtype) (l1 l2: list a) : GTot Type =
  forall (x:a). count x l1 == count x l2

let rec sorted (#a:eqtype) (leq: ord a) (xs: list a) : bool =
  match xs with
    | []
    | [_] -> true
    | x::y::l' -> leq x y && sorted leq (y::l')

let rec insert (#a:eqtype) (leq: ord a) (x:a) (l:list a) : list a =
  match l with
    | [] -> [x]
    | y::l' ->
      if leq x y
      then x::l
      else y :: (insert leq x l')

let rec lem_insert_perm (#a:eqtype) (leq: ord a) x l
  : Lemma (perm (x::l) (insert leq x l))
= match l with
    | [] -> ()
    | y::l' -> lem_insert_perm leq x l'

let rec lem_insert_sorted (#a:eqtype) (leq: ord a) x l
  : Lemma (requires sorted leq l) (ensures sorted leq (insert leq x l))
= match l with
    | [] -> ()
    | y::l' -> lem_insert_sorted leq x l'

let rec insertion_sort (#a:eqtype) (leq: ord a) (xs: list a) :
  xs':(list a){perm xs xs' /\ sorted leq xs'}
= match xs with
    | [] -> []
    | x::xs ->
      lem_insert_perm leq x (insertion_sort leq xs);
      lem_insert_sorted leq x (insertion_sort leq xs);
      insert leq x (insertion_sort leq xs)