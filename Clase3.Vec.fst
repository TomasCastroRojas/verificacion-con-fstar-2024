module Clase3.Vec

type vec (a:Type) : nat -> Type =
  | VNil : vec a 0
  | VCons : #n:nat -> hd:a -> tl:vec a n -> vec a (n+1)
  
let vhd (#a:Type) (#n:pos) (xs : vec a n) : a =
  match xs with
  | VCons hd tl -> hd

let vtl (#a:Type) (#n:pos) (xs : vec a n) : vec a (n-1) =
  match xs with
  | VCons hd tl -> tl

let rec vidx (#a:Type) (#n:pos) (xs : vec a n) (i : nat{i < n}) : a =
  match xs with
  | VCons hd tl ->
    if i = 0
    then hd
    else vidx tl (i-1)

let rec vappend (#a:Type) (#n1 #n2 : nat) (xs : vec a n1) (ys : vec a n2) : vec a (n1 + n2) =
  match xs with
  | VNil -> ys
  | VCons hd tl -> VCons hd (vappend tl ys)

let rec vupd (#a:Type) (#n:pos) (xs : vec a n) (i : nat{i < n}) (x : a) : vec a n =
  match i with
  | 0 -> VCons x (vtl xs)
  | _ -> VCons (vhd xs) (vupd (vtl xs) (i-1) x)

(* Definir funciones similares para matrices. Se pueden
usar las definiciones anteriores. *)

type mat (a:Type) : nat-> nat -> Type =
  | MRow : #n:nat -> vec a n -> mat a 1 n
  | MCons : #m:nat -> #n:nat -> vec a n -> mat a m n -> mat a (m+1) n
  
let rec matidx (#a:Type) (#m #n : nat) (ma : mat a m n) (i : nat{i < m}) (j : nat{j < n}) : a =
  match ma with
  | MRow vs -> vidx vs j
  | MCons vs ma' -> if i = 0
                    then vidx vs j
                    else matidx ma' (i-1) j
  
let rec matupd (#a:Type) (#m #n : nat) (ma : mat a m n) (i : nat{i < m}) (j : nat{j < n}) (x : a) : mat a m n =
  match ma with
  | MRow vs -> MRow (vupd vs j x)
  | MCons vs ma' -> if i = 0
                    then MCons (vupd vs j x) ma'
                    else MCons vs (matupd ma' (i-1) j x)
