(******************************)
(*** For debugging purposes ***)
(******************************)

(* print out an integer list *)
let rec print_int_list lst =
  match lst with
  | [] -> ()
  | [x] -> print_int x; print_newline ()
  | x :: xs -> print_int x; print_string "; "; print_int_list xs

(* print out a string list *)
let rec print_string_list lst =
  match lst with
  | [] -> ()
  | [x] -> print_string x; print_newline ()
  | x :: xs -> print_string x; print_string "; "; print_string_list xs


(********************)
(* Problem 1: pow *)
(********************)

let rec pow x p =
  if p = 0 then 1
  else if p = 1 then x
  else x * (pow x (p - 1))

(********************)
(* Problem 2: range *)
(********************)

let rec range num1 num2 =
  if num1 = num2 then [num1]
  else num1::(range (num1 + 1) num2)

(**********************)
(* Problem 3: flatten *)
(**********************)

let rec flatten l = match l with
  | [] -> []
  | (x::xs) -> x @ (flatten xs)

(*****************************)
(* Problem 4: remove_stutter *)
(*****************************)

let rec remove_stutter l = match l with
  | [] -> []
  | (_::[]) -> l
  | (x1::x2::xs) when (x1 = x2) -> remove_stutter (x2::xs)
  | (x1::x2::xs) -> x1::(remove_stutter (x2::xs))

(*********************)
(* Problem 5: rotate *)
(*********************)

let rec first_k l k = match l with
  | [] -> []
  | x::xs when (k > 0) -> x::(first_k xs (k - 1))
  | x::xs -> []

let rec last_n l k = match l with
  | [] -> []
  | x::xs when (k > 0) -> (last_n xs (k - 1))
  | x::xs -> x::(last_n xs (k - 1))

let rotate l n =
  let k = (List.length l) - n in
  let head = (last_n l k) in
  let tail = (first_k l k) in
  head @ tail;;

(*******************)
(* Problem 6: jump *)
(*******************)

(* l1: 2n-1, l2: 2n: when k=2n-1, l1 = 1, *)
let rec jump_helper lst1 lst2 i =
  if (i mod 2 = 1) then match lst1 with
    | [] -> []
    | _::[] -> []
    | _::x1::[] -> [x1]
    | _::x1::xs -> x1::(jump_helper xs lst2 (i+1))
  else match lst2 with
    | [] -> []
    | x0::[] -> [x0]
    | x0::_::xs -> x0::(jump_helper lst1 xs (i+1));;

let jump lst1 lst2 = match lst1, lst2 with
  | _, [] -> []
  | [], _ -> []
  | (h1::t1), (h2::t2) -> jump_helper lst1 lst2 0;;


(******************)
(* Problem 7: nth *)
(******************)

let rec nth_helper l n i = match l with
  | [] -> []
  | x::xs when (i mod n = 0) -> x::(nth_helper xs n (i+1))
  | x::xs -> (nth_helper xs n (i+1));;

let nth l n = (nth_helper l n 1)

(*****************************************************)
(* Problem 8: Digital Roots and Additive Persistence *)
(*****************************************************)

(* digits : int -> int list
 * we assume n >= 0
 * (digits n) is the list of digits of n in the order in which they appear in n
 * e.g. (digits 31243) is [3,1,2,4,3]
 *)

let rec digitsOfInt n =
  if n < 0 then []
  else if n < 10 then [n]
  else
    let digit = (n mod 10) in
    (digitsOfInt (n / 10)) @ (digit::[]);;

(* From http://mathworld.wolfram.com/AdditivePersistence.html
 * Consider the process of taking a number, adding its digits,
 * then adding the digits of the number derived from it, etc.,
 * until the remaining number has only one digit.
 * The number of additions required to obtain a single digit from a number n
 * is called the additive persistence of n, and the digit obtained is called
 * the digital root of n.
 * For example, the sequence obtained from the starting number 9876 is (9876, 30, 3), so
 * 9876 has an additive persistence of 2 and a digital root of 3.
 *)
let rec sum_list l = match l with
  | [] -> 0
  | (x::xs) -> (x + sum_list xs);;

let rec add_helper digits = match digits with
  | [] -> 0
  | x1::[] -> 0
  | x1::xs -> 1 + (add_helper (digitsOfInt (sum_list digits)));;

let rec dig_root_helper digits = match digits with
  | [] -> 0
  | x1::[] -> x1
  | x1::xs -> 
      dig_root_helper (digitsOfInt (sum_list digits));;

let additivePersistence n = add_helper (digitsOfInt n);;

let digitalRoot n = dig_root_helper (digitsOfInt n);;

(********)
(* Done *)
(********)   
let _ = print_string ("Testing your code ...\n")

let main () =
  let error_count = ref 0 in

  (* Testcases for pow *)
  let _ =
    try
      assert (pow 3 1 = 3);
      assert (pow 3 2 = 9);
      assert (pow (-3) 3 = -27)
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for range *)
  let _ =
    try
      assert (range 2 5 = [2;3;4;5]);
      assert (range 0 0 = [0])
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for flatten *)
  let _ =
    try
      assert (flatten [[1;2];[3;4]] = [1;2;3;4]);
      assert (flatten [[1;2];[];[3;4];[]] = [1;2;3;4])
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for remove_stutter *)
  let _ =
    try
      assert (remove_stutter [1;2;2;3;1;1;1;4;4;2;2] = [1; 2; 3; 1; 4; 2]);
      assert (remove_stutter [] = []);
      assert (remove_stutter [1;1;1;1;1] = [1]);
      assert (remove_stutter [1;1;1;1;1;2] = [1;2])
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for rotate *)
  let _ =
    try
      assert (rotate ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"] 2 = ["g"; "h"; "a"; "b"; "c"; "d"; "e"; "f"]);
      assert (rotate ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"] 0 = ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"]);
      assert (rotate ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"] 7 = ["b"; "c"; "d"; "e"; "f"; "g"; "h"; "a"])
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for jump *)
  let _ =
    try
      assert (jump ["first"; "second"; "third"; "fourth"] ["fifth"; "sixth"; "seventh"; "eighth"] = ["fifth"; "second"; "seventh"; "fourth"]);
      assert (jump [1; 3; 5; 7] [0; 2; 4; 6; 8] = [0; 3; 4; 7]);
      assert (jump ["a"; "b"] ["c"] = ["c"])
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for nth *)
  let _ =
    try
      (*print_int_list (nth [1; 2; 3; 4; 5; 6; 7] 1);*)
      assert (nth [1; 2; 3; 4; 5; 6; 7] 1 = [1; 2; 3; 4; 5; 6; 7]);
      assert (nth [1; 2; 3; 4; 5; 6; 7] 2 = [2; 4; 6]);
      assert (nth [1; 2; 3; 4; 5; 6; 7] 3 = [3; 6])
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for digitsOfInt *)
  let _ =
    try
      assert (digitsOfInt 3124 = [3;1;2;4]);
      assert (digitsOfInt 352663 = [3;5;2;6;6;3]);
      assert (digitsOfInt 31243 = [3;1;2;4;3]);
      assert (digitsOfInt 23422 = [2;3;4;2;2])
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for additivePersistence *)
  let _ =
    try
      assert (additivePersistence 9876 = 2)
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for digitalRoot *)
  let _ =
    try
      assert (digitalRoot 9876 = 3)
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  Printf.printf ("%d out of 10 programming questions are correct.\n") (10 - !error_count)

let _ = main()