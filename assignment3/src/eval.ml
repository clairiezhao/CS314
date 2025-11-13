open Ast

exception TypeError
exception UndefinedVar
exception DivByZeroError

(* Remove shadowed bindings *)
let prune_env (env : environment) : environment =
  let binds = List.sort_uniq compare (List.map (fun (id, _) -> id) env) in
  List.map (fun e -> (e, List.assoc e env)) binds

(* Print env to stdout *)
let print_env_std (env : environment): unit =
  List.fold_left (fun _ (var, value) ->
      match value with
        | Int_Val i -> Printf.printf "- %s => %s\n" var (string_of_int i)
        | Bool_Val b -> Printf.printf "- %s => %s\n" var (string_of_bool b)
        | Closure _ -> ()) () (prune_env env)

(* Print env to string *)
let print_env_str (env : environment): string =
  List.fold_left (fun acc (var, value) ->
      match value with
        | Int_Val i -> acc ^ (Printf.sprintf "- %s => %s\n" var (string_of_int i))
        | Bool_Val b -> acc ^ (Printf.sprintf "- %s => %s\n" var (string_of_bool b))
        | Closure _ -> acc
      ) "" (prune_env env)


(***********************)
(****** Your Code ******)
(***********************)

(* evaluate an arithmetic expression in an environment *)
let rec eval_expr (e : exp) (env : environment) : value = match e with
| Var x ->
    (try (List.assoc x env) with
    | Not_found -> raise UndefinedVar)
| Number n -> Int_Val n
| True -> Bool_Val true
| False -> Bool_Val false
  (* expressions that operate excl on ints *)
| Plus (e1, e2) | Minus (e1, e2) | Times (e1, e2) | Div (e1, e2) | Mod (e1, e2) | Leq (e1, e2) | Lt (e1, e2) -> 
    let v1 = eval_expr e1 env in
    let v2 = eval_expr e2 env in
    (match (v1, v2) with
    | (Int_Val n1, Int_Val n2) -> (match e with
      | Plus _ -> Int_Val (n1 + n2)
      | Minus _ -> Int_Val (n1 - n2)
      | Times _ -> Int_Val (n1 * n2)
      | Div _ -> 
          (match v2 with
          | Int_Val 0 -> raise DivByZeroError
          | _ -> Int_Val (n1 / n2))
      | Mod _ -> Int_Val (n1 mod n2)
      | Leq _ -> Bool_Val (n1 <= n2)
      | Lt _ -> Bool_Val (n1 < n2))
    | _ -> raise TypeError)
  (* expressions that operate excl on bools *)
| And (e1, e2) | Or (e1, e2) ->
    let v1 = eval_expr e1 env in
    let v2 = eval_expr e2 env in
    (match (v1, v2) with
    | (Bool_Val b1, Bool_Val b2) -> (match e with
      | And _ -> Bool_Val (b1 && b2)
      | Or _ -> Bool_Val (b1 || b2))
    | _ -> raise TypeError)
| Not e1 -> 
    let v1 = eval_expr e1 env in
    (match v1 with
    | Bool_Val b1 -> Bool_Val (not b1)
    | _ -> raise TypeError)
| Eq (e1, e2) ->
    let v1 = eval_expr e1 env in
    let v2 = eval_expr e2 env in
    (match (v1, v2) with
    | (Bool_Val b1, Bool_Val b2) -> Bool_Val (b1 = b2)
    | (Int_Val n1, Int_Val n2) -> Bool_Val (n1 = n2)
    | _ -> raise TypeError)
| Fun (x, e1) -> Closure (env, x, e1)
| App (e1, e2) ->
    let f = eval_expr e1 env in
    let v2 = eval_expr e2 env in
    (match f with
    | Closure (env1, x, fe) -> eval_expr fe ((x, v2)::env1)
    | _ -> raise TypeError)

(* evaluate a command in an environment *)
let rec eval_command (c : com) (env : environment) : environment = match c with
| Skip -> env
| Comp (c1, c2) ->
    let env1 = eval_command c1 env in
    eval_command c2 env1
| Declare (t, x) -> (match t with
  | Int_Type _ -> (x, Int_Val 0)::env
  | Bool_Type _ -> (x, Bool_Val false)::env
  | Lambda_Type _ -> (x, Closure (env, x, Var x))::env
  | _ -> raise TypeError)
| Assg (x, e) ->
    (try 
      let v0 = List.assoc x env in
      let v1 = eval_expr e env in
      (match (v0, v1) with
      | (Int_Val _, Int_Val _) | (Bool_Val _, Bool_Val _) | (Closure _, Closure _) -> (x, v1)::env
      | _ -> raise TypeError)
    with
    | Not_found -> raise UndefinedVar)
| Cond (e, c1, c2) ->
    let v = eval_expr e env in 
    (match v with
    | Bool_Val true -> eval_command c1 env
    | Bool_Val false -> eval_command c2 env
    | _ -> raise TypeError)
| While (e, c1) ->
    let v = eval_expr e env in
    (match v with
    | Bool_Val true ->
        let env1 = eval_command c1 env in
        eval_command (While (e, c1)) env1
    | Bool_Val false -> env
    | _ -> raise TypeError)
| For (e, c1) ->
    let n = eval_expr e env in
    (match n with
    | Int_Val n ->
      if n > 0 then
        let env1 = eval_command c1 env in
        eval_command (For (Number (n - 1), c1)) env1
      else env
    | _ -> raise TypeError)