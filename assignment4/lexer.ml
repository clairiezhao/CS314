open TokenTypes
open String

(*type token =
  | Tok_RParen
  | Tok_LParen
  | Tok_Equal
  | Tok_NotEqual
  | Tok_Greater
  | Tok_Less
  | Tok_GreaterEqual
  | Tok_LessEqual
  | Tok_Or
  | Tok_And
  | Tok_Not
  | Tok_If
  | Tok_Then
  | Tok_Else
  | Tok_Add
  | Tok_Sub
  | Tok_Mult
  | Tok_Div
  | Tok_Concat
  | Tok_Let
  | Tok_Rec
  | Tok_In
  | Tok_Def
  | Tok_Fun
  | Tok_Arrow
  | Tok_Int of int
  | Tok_Bool of bool
  | Tok_String of string
  | Tok_ID of string
  | Tok_DoubleSemi*)


(* We provide the regular expressions that may be useful to your code *)

let re_rparen = Str.regexp ")";;
let re_lparen = Str.regexp "(";;
let re_equal = Str.regexp "=";;
let re_not_equal = Str.regexp "<>";;
let re_greater = Str.regexp ">";;
let re_less = Str.regexp "<";;
let re_greater_equal = Str.regexp ">=";;
let re_less_equal = Str.regexp "<=";;
let re_or = Str.regexp "||";;
let re_and = Str.regexp "&&";;
let re_not = Str.regexp "not";;
let re_if = Str.regexp "if";;
let re_then = Str.regexp "then";;
let re_else = Str.regexp "else";;
let re_add = Str.regexp "+";;
let re_sub = Str.regexp "-";;
let re_mult = Str.regexp "*";;
let re_div = Str.regexp "/"
let re_concat = Str.regexp "\\^";;
let re_let = Str.regexp "let";;
let re_rec = Str.regexp "rec";;
let re_in = Str.regexp "in";;
let re_def = Str.regexp "def";;
let re_fun = Str.regexp "fun";;
let re_arrow = Str.regexp "->";;
let re_pos_int = Str.regexp "[0-9]+";;
let re_neg_int = Str.regexp "(-[0-9]+)";;
let re_true = Str.regexp "true";;
let re_false = Str.regexp "false";;
let re_string = Str.regexp "\"[^\"]*\"";;
let re_id = Str.regexp "[a-zA-Z][a-zA-Z0-9]*";;
let re_double_semi = Str.regexp ";;";;
let re_whitespace = Str.regexp "[ \t\n]+";;

(* Part 1: Lexer - IMPLEMENT YOUR CODE BELOW *)

let tokenize input = 
  let rec tok pos s =
    if pos >= String.length s then []
    else
      (* string *)
      (if (Str.string_match re_string s pos) then
        let token = Str.matched_string s in
        let sanitized_token = String.sub token 1 ((String.length token) - 2) in
          (Tok_String sanitized_token)::(tok (pos + (String.length token)) s)
      (* id *)
      else if (Str.string_match re_id s pos) then
        if (Str.string_match re_true s pos) then (Tok_Bool true)::(tok (pos + 4) s)
        else if (Str.string_match re_false s pos) then (Tok_Bool false)::(tok (pos + 5) s)
        else if (Str.string_match re_not s pos) then Tok_Not::(tok (pos + 3) s)
        else if (Str.string_match re_if s pos) then Tok_If::(tok (pos + 2) s)
        else if (Str.string_match re_then s pos) then Tok_Then::(tok (pos + 4) s)
        else if (Str.string_match re_else s pos) then Tok_Else::(tok (pos + 4) s)
        else if (Str.string_match re_let s pos) then Tok_Let::(tok (pos + 3) s)
        else if (Str.string_match re_rec s pos) then Tok_Rec::(tok (pos + 3) s)
        else if (Str.string_match re_in s pos) then Tok_In::(tok (pos + 2) s)
        else if (Str.string_match re_def s pos) then Tok_Def::(tok (pos + 3) s)
        else if (Str.string_match re_fun s pos) then Tok_Fun::(tok (pos + 3) s)
        else
          let _ = Str.string_match re_id s pos in
          let token = Str.matched_string s in
          (Tok_ID token)::(tok (pos + (String.length token)) s)
      (* int *)
      else if (Str.string_match re_pos_int s pos) then
        let token = Str.matched_string s in
        let int_token = int_of_string token in
          (Tok_Int int_token)::(tok (pos + (String.length token)) s)
      else if (Str.string_match re_neg_int s pos) then
        let token = Str.matched_string s in
        let int_len = (String.length token) - 2 in
        let int_token = int_of_string (String.sub token 1 int_len) in
          (Tok_Int int_token)::(tok (pos + (String.length token)) s)
      (* bool *)
      else if (Str.string_match re_true s pos) then
        (Tok_Bool true)::(tok (pos + 4) s)
      else if (Str.string_match re_false s pos) then
        (Tok_Bool false)::(tok (pos + 5) s)
      (* left paren *)
      else if (Str.string_match re_lparen s pos) then
        Tok_LParen::(tok (pos + 1) s)
      (* right paren *)
      else if (Str.string_match re_rparen s pos) then
        Tok_RParen::(tok (pos + 1) s)
      (* equal *)
      else if (Str.string_match re_equal s pos) then
        Tok_Equal::(tok (pos + 1) s)
      (* not equal *)
      else if (Str.string_match re_not_equal s pos) then
        Tok_NotEqual::(tok (pos + 2) s)
      (* greater equal *)
      else if (Str.string_match re_greater_equal s pos) then
        Tok_GreaterEqual::(tok (pos + 2) s)
      (* less equal *)
      else if (Str.string_match re_less_equal s pos) then
        Tok_LessEqual::(tok (pos + 2) s)
      (* greater *)
      else if (Str.string_match re_greater s pos) then
        Tok_Greater::(tok (pos + 1) s)
      (* less *)
      else if (Str.string_match re_less s pos) then
        Tok_Less::(tok (pos + 1) s)
      (* or *)
      else if (Str.string_match re_or s pos) then
        Tok_Or::(tok (pos + 2) s)
      (* and *)
      else if (Str.string_match re_and s pos) then
        Tok_And::(tok (pos + 2) s)
      (* not *)
      else if (Str.string_match re_not s pos) then
        Tok_Not::(tok (pos + 3) s)
      (* if *)
      else if (Str.string_match re_if s pos) then
        Tok_If::(tok (pos + 2) s)
      (* then *)
      else if (Str.string_match re_then s pos) then
        Tok_Then::(tok (pos + 4) s)
      (* else *)
      else if (Str.string_match re_else s pos) then
        Tok_Else::(tok (pos + 4) s)
      (* arrow *)
      else if (Str.string_match re_arrow s pos) then
        Tok_Arrow::(tok (pos + 2) s)
      (* add *)
      else if (Str.string_match re_add s pos) then
        Tok_Add::(tok (pos + 1) s)
      (* subtract *)
      else if (Str.string_match re_sub s pos) then
        Tok_Sub::(tok (pos + 1) s)
      (* multiply *)
      else if (Str.string_match re_mult s pos) then
        Tok_Mult::(tok (pos + 1) s)
      (* divide *)
      else if (Str.string_match re_div s pos) then
        Tok_Div::(tok (pos + 1) s)
      (* concat *)
      else if (Str.string_match re_concat s pos) then
        Tok_Concat::(tok (pos + 1) s)
      (* let *)
      else if (Str.string_match re_let s pos) then
        Tok_Let::(tok (pos + 3) s)
      (* rec *)
      else if (Str.string_match re_rec s pos) then
        Tok_Rec::(tok (pos + 3) s)
      (* in *)
      else if (Str.string_match re_in s pos) then
        Tok_In::(tok (pos + 2) s)
      (* def *)
      else if (Str.string_match re_def s pos) then
        Tok_Def::(tok (pos + 3) s)
      (* fun *)
      else if (Str.string_match re_fun s pos) then
        Tok_Fun::(tok (pos + 3) s)
      (* ;; *)
      else if (Str.string_match re_double_semi s pos) then
        Tok_DoubleSemi::(tok (pos + 2) s)
      (* whitespace *)
      else if (Str.string_match re_whitespace s pos) then
        let token = Str.matched_string s in
          (tok (pos + (String.length token)) s)
      else
        raise (InvalidInputException ""))
  in tok 0 input