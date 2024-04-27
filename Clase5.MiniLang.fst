module Clase5.MiniLang

type l_ty =
  | Int
  | Bool

type var = nat

(* Pequeño lenguaje de expresiones, indexado por el tipo de su resultado *)
type expr : l_ty -> Type =
  | EInt : int -> expr Int
  | EBool : bool -> expr Bool
  | EAdd : expr Int -> expr Int -> expr Int
  | EEq : expr Int -> expr Int -> expr Bool
  | EIf :
    #ty:_ ->
    expr Bool -> expr ty -> expr ty -> expr ty

(* Traducción de tipos de MiniLang a tipos de F* *)
let lift (ty : l_ty) : Type =
  match ty with
  | Int -> int
  | Bool -> bool
(* El evaluador intrínsecamente-tipado de MiniLang *)
val eval (#ty:l_ty) (e : expr ty) : Tot (lift ty)
let rec eval (#ty:l_ty) (e : expr ty) : Tot (lift ty) (decreases e) =
  match e with
  | EInt i -> i
  | EBool b -> b
  | EAdd m n -> eval m + eval n
  | EEq m n -> eval m = eval n
  | EIf c t e ->
    if eval c then eval t else eval e

(* Optimización sobre expresionse MiniLang: constant folding *)
let rec constant_fold (#ty:l_ty) (e : expr ty) : Tot (expr ty) (decreases e) =
  match e with
  | EAdd e1 e2 ->
    let e1' = constant_fold e1 in
    let e2' = constant_fold e2 in
    (match e1', e2' with
      | EInt m, EInt n -> EInt (m+n)
      | _ -> EAdd e1' e2')
  | EEq e1 e2 ->
    let e1' = constant_fold e1 in
    let e2' = constant_fold e2 in
    (match e1', e2' with
      | EInt m, EInt n -> EBool (m=n)
      | _ -> EEq e1' e2')
  | EIf c t e ->
    let c' = constant_fold c in
    let t' = constant_fold t in
    let e' = constant_fold e in
    (match c' with
      | EBool true -> t'
      | EBool false -> e'
      | _ -> EIf c' t' e')
  | _ -> e 

(* Correctitud de la optimización de constant folding *)
let rec constant_fold_ok (#ty:l_ty) (e : expr ty)
  : Lemma (ensures eval e == eval (constant_fold e)) (decreases e)
= match e with
  | EAdd m n -> (
    constant_fold_ok m;
    constant_fold_ok n
  )
  | EEq m n -> (
    constant_fold_ok m;
    constant_fold_ok n
  )
  | EIf c t e -> (
    constant_fold_ok c;
    constant_fold_ok t;
    constant_fold_ok e
  )
  | _ -> ()
