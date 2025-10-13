open List

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

(* print out a list of integer lists *)
let print_int_list_list lst =
  List.iter print_int_list lst

(* print out a list of string lists *)
let print_string_list_list lst =
  List.iter print_string_list lst


(***********************)
(* Problem 1: cond_dup *)
(***********************)

let rec cond_dup l f = match l with
  | [] -> []
  | (h::t) ->
    if (f h) then h::h::(cond_dup t f)
    else h::(cond_dup t f);;
    
(**********************)
(* Problem 2: n_times *)
(**********************)

let rec n_times (f, n, v) =
  if n <= 0 then v
  else n_times (f, n-1, (f v));;

(**********************)
(* Problem 3: zipwith *)
(**********************)

let rec zipwith f l1 l2 = match l1, l2 with
  | [], _ -> []
  | _, [] -> []
  | (h1::t1), (h2::t2) -> (f h1 h2)::(zipwith f t1 t2);;

(**********************)
(* Problem 4: buckets *)
(**********************)

(* given a value and equiv func, place into correct equiv bucket *)
let rec update_buckets p x buckets = match buckets with
  | [] -> [x]::[]
  | (l1::lsts) ->
      if (p x (List.hd l1)) then ((l1 @ [x])::lsts)
      else l1::(update_buckets p x lsts);;

(*buckets is a list of lists*)
let rec buckets_helper p l buckets = match l with
  | [] -> buckets
  | (h::t) -> let updated = (update_buckets p h buckets) in 
    (buckets_helper p t updated);;

let buckets p l = (buckets_helper p l []);;

(**************************)
(* Problem 5: fib_tailrec *)
(**************************)

let rec fib_helper i n curr prev =
  if (i = n) then curr
  else (fib_helper (i+1) n (curr+prev) curr);;

let fib_tailrec n = fib_helper 1 n 1 0;;

(***********************)
(* Problem 6: sum_rows *)
(***********************)

let sum_rows (rows:int list list) : int list = 
  let sum_row = (fun row -> List.fold_left (+) 0 row) in
  (List.map sum_row rows)

(*****************)
(* Problem 7: ap *)
(*****************)

(* apply takes a function f: 'a list -> 'b list and returns result :: 'b list list'*)
let nested_ap f (args, a) =
  let ap = (List.map f args) in
  match a with
  | [] -> (args, [ap])
  | (_::_) -> (args, ap::a);;

(* apply a list of functions to given args, return list of list results*)
let ap fs args =
  let (ret, nested_res) = (List.fold_right nested_ap fs (args, [])) in
  (List.flatten nested_res);;

(***********************)
(* Problem 8: prefixes *)
(***********************)

let p_helper (a, prev_prefix) x = match a with
  | [] -> ([x]::[], [x])
  | (l1::lsts) -> let curr_prefix = prev_prefix @ [x] in
    (a @ [curr_prefix], curr_prefix);;

(* for every element x in l, prepend x to previous prefix and add to accum*)
(* accum is a list of lists *)
let prefixes l = 
  let (res, _) = (List.fold_left p_helper ([], []) l) in res;;

(***********************)
(* Problem 9: powerset *)
(***********************)

(* new list = 2 * len of old list = old list + insert x into every list *)
(* 1,2,3 -> [] -> [3], [] -> [2, 3], [2], [3], [] -> [1, 2, 3], [1, 2], [1, 3], [1], [2, 3], [2], [3], []*)

let insert_x_pset a x = match a with
  | [] -> [x]::[]
  | (l1::lsts) -> let prependx = (fun l -> x::l) in 
    ([x]::(List.map prependx a)) @ a;;

let powerset l = match l with
  | [] -> []
  | (_::_) -> List.fold_left insert_x_pset [] l;;

(**************************)
(* Problem 10: assoc_list *)
(**************************)

(* for every x in list, count all occurences of x *)
(* when you count an occurence, delete that occurence from lst *)
(* given curr count, in progress result, target, and curr element *)
(* add element to res if not equal to target *)
let update_count (count, res, target) x =
  if (x = target) then (count + 1, res, target)
  else (count, x::res, target)

(* add count of target to counts and update l *)
(* counts is a list of 2-tuples *)
let count (counts, l) target = 
  let (c, res, _) = (List.fold_left update_count (0, [], target) l) in
  if not (c = 0) then ((target, c)::counts, res)
  else (counts, res);;

(* for every element in lst, run through lst and update counts *)
let assoc_list lst = match lst with
  | [] -> []
  | (_::_) -> let (counts, _) = (List.fold_left count ([], lst) lst) in
    counts;;

(********)
(* Done *)
(********)

let _ = print_string ("Testing your code ...\n")

let main () =
  let error_count = ref 0 in

  let cmp x y = if x < y then (-1) else if x = y then 0 else 1 in

  (* Testcases for cond_dup *)
  let _ =
    try
      assert (cond_dup [3;4;5] (fun x -> x mod 2 = 1) = [3;3;4;5;5]);
      assert (cond_dup [] (fun x -> x mod 2 = 1) = []);
      assert (cond_dup [1;2;3;4;5] (fun x -> x mod 2 = 0) = [1;2;2;3;4;4;5])
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for n_times *)
  let _ =
    try
      assert (n_times((fun x-> x+1), 50, 0) = 50);
      assert (n_times ((fun x->x+1), 0, 1) = 1);
      assert (n_times((fun x-> x+2), 50, 0) = 100)
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for zipwith *)
  let _ =
    try
      assert ([5;7] = (zipwith (+) [1;2;3] [4;5]));
      assert ([(1,5); (2,6); (3,7)] = (zipwith (fun x y -> (x,y)) [1;2;3;4] [5;6;7]))
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for buckets *)
  let _ =
    try
      assert (buckets (=) [1;2;3;4] = [[1];[2];[3];[4]]);
      assert (buckets (=) [1;2;3;4;2;3;4;3;4] = [[1];[2;2];[3;3;3];[4;4;4]]);
      assert (buckets (fun x y -> (=) (x mod 3) (y mod 3)) [1;2;3;4;5;6] = [[1;4];[2;5];[3;6]])
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for fib_tailrec *)
  let _ =
    try
      assert (fib_tailrec 50 = 12586269025);
      assert (fib_tailrec 90 = 2880067194370816120)
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for sum_rows *)
  let _ =
    try
      assert (sum_rows [[1;2]; [3;4]] = [3; 7]);
      assert (sum_rows [[5;6;7;8;9]; [10]] = [35; 10])
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for ap *)
  let _ =
    let x = [5;6;7;3] in
    let b = [3] in
    let c = [] in
    let fs1 = [((+) 2) ; (( * ) 7)] in
    try
      assert  ([7;8;9;5;35;42;49;21] = ap fs1 x);
      assert  ([5;21] = ap fs1 b);
      assert  ([] = ap fs1 c);
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for prefixes *)
  let _ =
    try
      assert (prefixes [1;2;3;4] = [[1]; [1;2]; [1;2;3]; [1;2;3;4]]);
      assert (prefixes [] = []);
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (*sort a list of lists *)
  let sort ls =
    List.sort cmp (List.map (List.sort cmp) ls) in

  (* Testcases for powerset *)
  let _ =
    try
      (* Either including or excluding [] in the powerset is marked correct by the tester *)
      assert (sort (powerset [1;2;3]) = sort [[1]; [1; 2]; [1; 2; 3]; [1; 3]; [2]; [2; 3]; [3]] || sort (powerset [1;2;3]) = sort [[];[1]; [1; 2]; [1; 2; 3]; [1; 3]; [2]; [2; 3]; [3]]);
      assert ([] = powerset [] || [[]] = powerset [])
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for assoc_list *)
  let _ =
    let y = ["a";"a";"b";"a"] in
    let z = [1;7;7;1;5;2;7;7] in
    let a = [true;false;false;true;false;false;false] in
    let b = [] in
    try
      assert ([("a",3);("b",1)] = List.sort cmp (assoc_list y));
      assert ([(1,2);(2,1);(5,1);(7,4)] = List.sort cmp (assoc_list z));
      assert ([(false,5);(true,2)] = List.sort cmp (assoc_list a));
      assert ([] = assoc_list b)
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in


  Printf.printf ("%d out of 10 programming questions passed.\n") (10 - !error_count)

let _ = main()
