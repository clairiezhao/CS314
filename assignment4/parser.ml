open MicroCamlTypes
open Utils
open TokenTypes

(* Provided functions *)

(* Matches the next token in the list, throwing an error if it doesn't match the given token *)
let match_token (toks: token list) (tok: token) =
  match toks with
  | [] -> raise (InvalidInputException(string_of_token tok))
  | h::t when h = tok -> t
  | h::_ -> raise (InvalidInputException(
      Printf.sprintf "Expected %s from input %s, got %s"
        (string_of_token tok)
        (string_of_list string_of_token toks)
        (string_of_token h)))

(* Matches a sequence of tokens given as the second list in the order in which they appear, throwing an error if they don't match *)
let match_many (toks: token list) (to_match: token list) =
  List.fold_left match_token toks to_match

(* Return the next token in the token list as an option *)
let lookahead (toks: token list) =
  match toks with
  | [] -> None
  | h::t -> Some h

(* Return the token at the nth index in the token list as an option*)
let rec lookahead_many (toks: token list) (n: int) =
  match toks, n with
  | h::_, 0 -> Some h
  | _::t, n when n > 0 -> lookahead_many t (n-1)
  | _ -> None

(* Part 2: Parsing expressions *)

(* parse operators *)
let parse_rec toks =
  match lookahead toks with
  | Some Tok_Rec ->
    let toks = match_token toks Tok_Rec in 
    (toks, true)
  | _ -> (toks, false)

let parse_eq_op toks = match lookahead toks with
  | Some Tok_Equal ->
    let toks = match_token toks Tok_Equal in 
    (toks, Equal)
  | Some Tok_NotEqual ->
    let toks = match_token toks Tok_NotEqual in 
    (toks, NotEqual)
  | _ -> raise (InvalidInputException "")

let parse_rel_op toks = match lookahead toks with
  | Some Tok_Less ->
    let toks = match_token toks Tok_Less in 
    (toks, Less)
  | Some Tok_LessEqual ->
    let toks = match_token toks Tok_LessEqual in 
    (toks, LessEqual)
  | Some Tok_Greater ->
    let toks = match_token toks Tok_Greater in 
    (toks, Greater)
  | Some Tok_GreaterEqual ->
    let toks = match_token toks Tok_GreaterEqual in 
    (toks, GreaterEqual)
  | _ -> raise (InvalidInputException "")

let parse_add_op toks = match lookahead toks with
  | Some Tok_Add ->
    let toks = match_token toks Tok_Add in 
    (toks, Add)
  | Some Tok_Sub -> 
    let toks = match_token toks Tok_Sub in 
    (toks, Sub)
  | _ -> raise (InvalidInputException "")

let parse_mult_op toks = match lookahead toks with
  | Some Tok_Mult ->
    let toks = match_token toks Tok_Mult in 
    (toks, Mult)
  | Some Tok_Div ->
    let toks = match_token toks Tok_Div in 
    (toks, Div)
  | _ -> raise (InvalidInputException "")


(* parse expression *)
let rec parse_expr toks = 
  match lookahead toks with
  | Some Tok_Let ->
    let (toks, let_expr) = parse_let toks in
    (toks, let_expr)
  | Some Tok_Fun ->
    let (toks, fun_expr) = parse_fun toks in
    (toks, fun_expr)
  | Some Tok_If ->
    let (toks, if_expr) = parse_if toks in
    (toks, if_expr)
  | Some (Tok_Int _) | Some (Tok_Bool _) | Some (Tok_String _) | Some (Tok_ID _) | Some Tok_LParen | Some Tok_Not ->
    let (toks, or_expr) = parse_or toks in
    (toks, or_expr)
  | _ -> raise (InvalidInputException "")

(* let *)
and parse_let toks = 
  match lookahead toks with
  | Some Tok_Let ->
    let toks = match_token toks Tok_Let in
    let (toks, bool_rec) = parse_rec toks in
    let id = (match lookahead toks with
    | Some (Tok_ID id) -> id
    | _ -> raise (InvalidInputException "")) in
    let toks = match_many toks [Tok_ID id; Tok_Equal] in
    let (toks, e1) = parse_expr toks in
    let toks = match_token toks Tok_In in
    let (toks, e2) = parse_expr toks in
    (toks, Let (id, bool_rec, e1, e2))
  | _ -> raise (InvalidInputException "")

(* function *)
and parse_fun toks =
  match lookahead toks with
  | Some Tok_Fun ->
    let toks = match_token toks Tok_Fun in
    let id = (match lookahead toks with
    | Some (Tok_ID id) -> id
    | _ -> raise (InvalidInputException "")) in
    let toks = match_many toks [Tok_ID id; Tok_Arrow] in
    let (toks, e1) = parse_expr toks in
    (toks, Fun (id, e1))
  | _ -> raise (InvalidInputException "")

(* if *)
and parse_if toks =
  match lookahead toks with
  | Some Tok_If ->
    let toks = match_token toks Tok_If in
    let (toks, e1) = parse_expr toks in
    let toks = match_token toks Tok_Then in
    let (toks, e2) = parse_expr toks in
    let toks = match_token toks Tok_Else in
    let (toks, e3) = parse_expr toks in
    (toks, If (e1, e2, e3))
  | _ -> raise (InvalidInputException "")

(* or *)
and parse_or toks =
  match lookahead toks with
  | Some (Tok_Int _) | Some (Tok_Bool _) | Some (Tok_String _) | Some (Tok_ID _) | Some Tok_LParen | Some Tok_Not ->
    let (toks, and_expr) = parse_and toks in
    let (toks, comp_or_expr) = parse_comp_or toks and_expr in
    (toks, comp_or_expr)
  | _ -> raise (InvalidInputException "")

and parse_comp_or toks and_expr =
  match lookahead toks with
  | Some Tok_Or ->
    let toks = match_token toks Tok_Or in
    let (toks, or_expr) = parse_or toks in
    (toks, Binop (Or, and_expr, or_expr))
  | _ -> (toks, and_expr)

(* and *)
and parse_and toks =
  match lookahead toks with
  | Some (Tok_Int _) | Some (Tok_Bool _) | Some (Tok_String _) | Some (Tok_ID _) | Some Tok_LParen | Some Tok_Not ->
    let (toks, eq_expr) = parse_eq toks in
    let (toks, comp_and_expr) = parse_comp_and toks eq_expr in
    (toks, comp_and_expr)
  | _ -> raise (InvalidInputException "")

and parse_comp_and toks eq_expr =
  match lookahead toks with
  | Some Tok_And ->
    let toks = match_token toks Tok_And in
    let (toks, and_expr) = parse_and toks in
    (toks, Binop (And, eq_expr, and_expr))
  | _ -> (toks, eq_expr)

(* equality expression *)
and parse_eq toks =
  match lookahead toks with
  | Some (Tok_Int _) | Some (Tok_Bool _) | Some (Tok_String _) | Some (Tok_ID _) | Some Tok_LParen | Some Tok_Not ->
    let (toks, rel_expr) = parse_rel toks in
    let (toks, comp_eq_expr) = parse_comp_eq toks rel_expr in
    (toks, comp_eq_expr)
  | _ -> raise (InvalidInputException "")

and parse_comp_eq toks rel_expr =
  match lookahead toks with
  | Some Tok_Equal | Some Tok_NotEqual -> 
    let (toks, eq_op) = parse_eq_op toks in
    let (toks, eq_expr) = parse_eq toks in
    (toks, Binop (eq_op, rel_expr, eq_expr))
  | _ -> (toks, rel_expr)

(* relational expression *)
and parse_rel toks =
  match lookahead toks with
  | Some (Tok_Int _) | Some (Tok_Bool _) | Some (Tok_String _) | Some (Tok_ID _) | Some Tok_LParen | Some Tok_Not ->
    let (toks, add_expr) = parse_add toks in
    let (toks, comp_rel_expr) = parse_comp_rel toks add_expr in
    (toks, comp_rel_expr)
  | _ -> raise (InvalidInputException "")

and parse_comp_rel toks add_expr =
  match lookahead toks with
  | Some Tok_Greater | Some Tok_GreaterEqual | Some Tok_Less | Some Tok_LessEqual -> 
    let (toks, rel_op) = parse_rel_op toks in
    let (toks, rel_expr) = parse_rel toks in
    (toks, Binop (rel_op, add_expr, rel_expr))
  | _ -> (toks, add_expr)

(* additive expression *)
and parse_add toks =
  match lookahead toks with
  | Some (Tok_Int _) | Some (Tok_Bool _) | Some (Tok_String _) | Some (Tok_ID _) | Some Tok_LParen | Some Tok_Not ->
    let (toks, mult_expr) = parse_mult toks in
    let (toks, comp_add_expr) = parse_comp_add toks mult_expr in
    (toks, comp_add_expr)
  | _ -> raise (InvalidInputException "")

and parse_comp_add toks mult_expr =
  match lookahead toks with
  | Some Tok_Add | Some Tok_Sub -> 
    let (toks, add_op) = parse_add_op toks in
    let (toks, add_expr) = parse_add toks in
    (toks, Binop (add_op, mult_expr, add_expr))
  | _ -> (toks, mult_expr)

(* multiplicative expression *)
and parse_mult toks =
  match lookahead toks with
  | Some (Tok_Int _) | Some (Tok_Bool _) | Some (Tok_String _) | Some (Tok_ID _) | Some Tok_LParen | Some Tok_Not ->
    let (toks, concat_expr) = parse_concat toks in
    let (toks, comp_mult_expr) = parse_comp_mult toks concat_expr in
    (toks, comp_mult_expr)
  | _ -> raise (InvalidInputException "")

and parse_comp_mult toks concat_expr =
  match lookahead toks with
  | Some Tok_Mult | Some Tok_Div -> 
    let (toks, mult_op) = parse_mult_op toks in
    let (toks, mult_expr) = parse_mult toks in
    (toks, Binop (mult_op, concat_expr, mult_expr))
  | _ -> (toks, concat_expr)

(* concat expression *)
and parse_concat toks =
  match lookahead toks with
  | Some (Tok_Int _) | Some (Tok_Bool _) | Some (Tok_String _) | Some (Tok_ID _) | Some Tok_LParen | Some Tok_Not ->
    let (toks, unary_expr) = parse_unary toks in
    let (toks, comp_concat_expr) = parse_comp_concat toks unary_expr in
    (toks, comp_concat_expr)
  | _ -> raise (InvalidInputException "")

and parse_comp_concat toks unary_expr =
  match lookahead toks with
  | Some Tok_Concat -> 
    let toks = match_token toks Tok_Concat in
    let (toks, concat_expr) = parse_concat toks in
    (toks, Binop (Concat, unary_expr, concat_expr))
  | _ -> (toks, unary_expr)

(* unary expression *)
and parse_unary toks =
  match lookahead toks with
  | Some Tok_Not ->
    let toks = match_token toks Tok_Not in
    let (toks, unary_expr) = parse_unary toks in
    (toks, Not unary_expr)
  | Some (Tok_Int _) | Some (Tok_Bool _) | Some (Tok_String _) | Some (Tok_ID _) | Some Tok_LParen ->
    let (toks, fun_call_expr) = parse_fun_call toks in
    (toks, fun_call_expr)
  | _ -> raise (InvalidInputException "")

(* function call expression *)
and parse_fun_call toks =
  match lookahead toks with
  | Some (Tok_Int _) | Some (Tok_Bool _) | Some (Tok_String _) | Some (Tok_ID _) | Some Tok_LParen ->
    let (toks, primary_expr) = parse_primary toks in
    let (toks, comp_fun_call_expr) = parse_comp_fun_call toks primary_expr in
    (toks, comp_fun_call_expr)
  | _ -> raise (InvalidInputException "")

and parse_comp_fun_call toks primary_expr =
  match lookahead toks with
  | Some (Tok_Int _) | Some (Tok_Bool _) | Some (Tok_String _) | Some (Tok_ID _) | Some Tok_LParen -> 
    let (toks, primary_expr1) = parse_primary toks in
    (toks, FunctionCall (primary_expr, primary_expr1))
  | _ -> (toks, primary_expr)

(* primary expression *)
and parse_primary toks =
  match lookahead toks with
  | Some (Tok_Int n) ->
    let toks = match_token toks (Tok_Int n) in
    (toks, Int n)
  | Some (Tok_Bool b) ->
    let toks = match_token toks (Tok_Bool b) in
    (toks, Bool b)
  | Some (Tok_String s) ->
    let toks = match_token toks (Tok_String s) in
    (toks, String s)
  | Some (Tok_ID id) ->
    let toks = match_token toks (Tok_ID id) in
    (toks, ID id)
  | Some Tok_LParen ->
    let toks = match_token toks Tok_LParen in
    let (toks, expr) = parse_expr toks in
    let toks = match_token toks Tok_RParen in
    (toks, expr)
  | _ -> raise (InvalidInputException "")