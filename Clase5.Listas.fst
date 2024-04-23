module Clase5.Listas

open FStar.List.Tot

val sum_int : list int -> int
let rec sum_int xs =
  match xs with
 | [] -> 0
 | x::xs' -> x + sum_int xs'

(* Demuestre que sum_int "distribuye" sobre la concatenación de listas. *)
let rec sum_append (l1 l2 : list int)
  : Lemma (sum_int (l1 @ l2) == sum_int l1 + sum_int l2)
  = match l1 with
  | [] -> ()
  | x::xs -> sum_append xs l2

(*
Base:
  sum_int ([] @ l2) == sum_int [] + sum_int l2
  sum_int l2        == 0 + sum_int l2
  sum_int l2        == sum_int l2

Inductivo:
  sum_int ((x::xs) @ l2)  == sum_int (x::xs) + sum_int l2
  sum_int (x::(xs @ l2))  == (x + sum_int xs) + sum_int l2
  sum_int (xs @ l2)       == sum_int xs + sum_int l2
*)

(* Idem para length, definida en la librería de F*. *)
let rec len_append (l1 l2 : list int)
  : Lemma (length (l1 @ l2) == length l1 + length l2)
  = match l1 with
  | [] -> ()
  | x::xs -> len_append xs l2

let rec snoc (xs : list int) (x : int) : list int =
  match xs with
  | [] -> [x]
  | y::ys -> y :: snoc ys x

(* unit-tests *)
let _ = assert (snoc [1;2;3] 4 == [1;2;3;4])
let _ = assert (snoc [1;2;3] 5 == [1;2;3;5])

let rec rev_int (xs : list int) : list int =
  match xs with
  | [] -> []
  | x::xs' -> snoc (rev_int xs') x

let rec snoc_append (xs ys : list int) (z : int)
  : Lemma (snoc (xs @ ys) z == xs @ snoc ys z)
  = match xs with
    | [] -> ()
    | _::xs' -> snoc_append xs' ys z

let rec rev_append_int (xs ys : list int)
  : Lemma (rev_int (xs @ ys) == rev_int ys @ rev_int xs)
= match xs with
  | [] -> ()
  | z::zs -> (
    // assert(rev_int (xs @ ys) == rev_int ((z::zs) @ ys));
    // assert(rev_int ((z::zs) @ ys) == rev_int (z::zs@ys));
    // assert(rev_int (z::zs@ys) == snoc(rev_int (zs@ys) z));
    rev_append_int zs ys;
    // assume (snoc (rev_int ys @ rev_int zs) z == rev_int ys @ snoc (rev_int zs z))
    snoc_append (rev_int ys) (rev_int zs) z
  )

let rec snoc_rev (xs : list int) (x : int)
  : Lemma (rev_int (snoc xs x) == x::rev_int xs)
  = match xs with
    | [] -> ()
    | z::zs -> snoc_rev zs x

let rec rev_rev (xs : list int)
  : Lemma (rev_int (rev_int xs) == xs)
= match xs with
  | [] -> ()
  | z::zs -> (
    snoc_rev (rev_int zs) z;
    rev_rev zs
  )

let rec rev_injective (xs ys : list int)
  : Lemma (requires rev_int xs == rev_int ys) (ensures xs == ys)
= admit() // Ni idea
