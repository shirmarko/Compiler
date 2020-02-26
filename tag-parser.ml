#use "reader.ml";;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)

let check_var x = 
(List.fold_left (fun a b -> (a || (b = x))) false reserved_word_list);;

let rec tag_parsing sexpr = 
match sexpr with
| Bool(x) -> Const(Sexpr(Bool(x)))
| Char(x) -> Const(Sexpr(Char(x)))
| Number(x) -> Const(Sexpr(Number(x)))
| String(x) -> Const(Sexpr(String(x)))

| Pair(Symbol "quote",Pair(sxpr, Nil)) -> Const(Sexpr(sxpr))

| TaggedSexpr (str, Pair (Symbol "quote", Pair (expr, Nil))) -> Const(Sexpr (TaggedSexpr (str, expr)))
| TaggedSexpr(str, sxpr) -> Const(Sexpr(TaggedSexpr(str, sxpr)))

| TagRef(str) -> Const(Sexpr(TagRef(str)))

| Symbol(x) -> (fun (x) -> match (check_var x) with 
              | false -> Var(x)
              | true -> raise X_syntax_error) x

| Pair(Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil)))) -> If(tag_parsing test, tag_parsing dit, tag_parsing dif)
| Pair(Symbol("if"), Pair(test, Pair(dit, Nil))) -> If(tag_parsing test, tag_parsing dit, Const(Void))
| Pair(Symbol "begin", Nil) -> Const(Void)
| Pair(Symbol "begin", Pair(exp, Nil)) -> tag_parsing exp
| Pair(Symbol "begin", lst) -> Seq(pair_to_expr_list lst)
| Pair(Symbol "lambda", Pair(param, body)) -> (fun (x) -> match x with
                                              | Nil -> raise X_syntax_error
                                              | _ -> lambda_tag param body) body

                                             
| Pair(Symbol("or"),Nil) -> Const(Sexpr(Bool(false)))
| Pair(Symbol("or"),Pair(x, Nil)) -> (tag_parsing x) 
| Pair(Symbol("or"),p) -> Or(pair_to_expr_list p)

| Pair(Symbol "define", Pair(Symbol(def_var), Pair(def_val, Nil))) -> (fun (x) -> match (check_var def_var) with 
                                                              | false -> Def(Var(def_var), tag_parsing def_val)
                                                              | true -> raise X_syntax_error) def_var

| Pair(Symbol "define", Pair(Pair(Symbol (def_var),arglist), expr_plus)) -> 
      tag_parsing (Pair(Symbol "define", Pair(Symbol(def_var), Pair(Pair(Symbol "lambda", Pair(arglist, expr_plus)),Nil)))) (**MIT define**)

| Pair(Symbol "set!", Pair(Symbol(set_var), Pair(set_val, Nil))) -> (fun (x) -> match (check_var set_var) with 
                                                              | false -> Set(Var(set_var), tag_parsing set_val)
                                                              | true -> raise X_syntax_error) set_var

| Pair(Symbol "let", Pair(Nil, body)) -> tag_parsing (Pair(Pair(Symbol "lambda", Pair(Nil, body)), Nil))

| Pair(Symbol "let", Pair(p, body)) -> tag_parsing (let_handle p body) (*p = Pair(rib, ribs)*)

| Pair(Symbol "let*", Pair(Nil, body)) -> tag_parsing (Pair(Symbol "let", Pair(Nil, body)))
| Pair(Symbol "let*", Pair(Pair(binding, Nil), body)) -> tag_parsing (Pair(Symbol "let", Pair(Pair(binding, Nil), body)))

| Pair(Symbol "let*", Pair(Pair(first, rest), body)) -> tag_parsing (Pair(Symbol "let", Pair(Pair(first, Nil), Pair(Pair(Symbol "let*", Pair(rest, body)), Nil))))
(* first = Pair(Symbol "var", Pair(Symbol "val", Nil)) *)
(* rest = Pair(Pair(Symbol "var2", Pair(Symbol "val2", Nil)), Nil) *)

| Pair(Symbol "letrec", Pair(bind_list, body)) ->  tag_parsing (let_rec_handle bind_list body)

| Pair(Symbol "cond", list) -> tag_parsing (handle_cond list)

| Pair(Symbol "quasiquote", Pair(sxpr, Nil)) -> tag_parsing (handle_qq sxpr)


| Pair(Symbol("and"),Nil) -> Const(Sexpr(Bool(true)))
| Pair(Symbol("and"),Pair(x, Nil)) -> (tag_parsing x) 

| Pair(Symbol("and"), Pair(expr1, rest)) -> If(tag_parsing expr1, tag_parsing (Pair(Symbol "and", rest)), Const(Sexpr(Bool(false))))

| Pair(x, lst) -> Applic(tag_parsing x, pair_to_expr_list lst) (*Application*) 
| _ -> raise X_syntax_error



(*********************************************************lambda functions*******************************************************************)
and lambda_tag param body = match param with
    | Symbol(x) -> LambdaOpt([], x, check_if_seq_valid body) (*Variadic*)
    | Pair(Symbol(a), rest) -> 
                    let p= (check_proper rest [a]) in 
                    let hasDup = dup_exist ((fun (a,b) -> b) p) in
                    let found_reserved = List.fold_left (fun a b -> (a || (check_var b))) false ((fun (a,b) -> b) p) in
                    if ((not hasDup) && (not found_reserved))
                    then
                      match p with
                      | (false, args) -> (fun (args) -> (fun ((a,b)) -> LambdaOpt(a, b, check_if_seq_valid body)) (seperate_last [] args)) args
                      | (true, args) -> LambdaSimple(args, check_if_seq_valid body)
                    else raise X_syntax_error 
    | Nil -> LambdaSimple([], check_if_seq_valid body) (*lambda with no arguments *)
    | _ -> raise X_syntax_error              



and check_proper lst acc = match lst with
  | Nil -> (true, acc) (**LambdaSimple**)
  | Pair(Symbol(x), y) -> (check_proper y (List.append acc [x]))
  | Symbol(x) -> (false, (List.append acc [x])) (*LambdaOpt*)
  |_-> raise X_syntax_error

and check_if_seq_valid body = 
  let body_list = pair_to_expr_list body in
  match body_list with
  | [] -> raise X_syntax_error
  | [x] -> x
  | _ -> Seq (body_list)

and pair_to_expr_list pair = match pair with
| Nil -> []
| Pair(a, b) -> List.append [tag_parsing a] (pair_to_expr_list b)
| _ -> raise X_syntax_error

and seperate_last lst1 lst2 = match lst2 with
| [] -> failwith "list is empty"
| [x] -> (lst1, x)
| first::rest -> seperate_last (List.append lst1 [first]) rest


and dup_exist lst = match lst with
| [] -> false
| hd::tl -> (List.exists (fun (a) -> a = hd) tl) || dup_exist tl

(*********************************************************let functions*******************************************************************)

and split_rib (lst1,lst2) sym val1 = ((List.append lst1 [sym]), (List.append lst2 [val1]))

and split_params pair res = 
  match pair with
  | Pair(Pair(sym, Pair(val1, Nil)),Nil) -> (split_rib res sym val1)
  | Pair(Pair(sym, Pair(val1, Nil)),ribs) -> (split_params ribs (split_rib res sym val1))
  | _ -> raise X_syntax_error

and list_to_pair list = 
match list with 
| [] -> Nil
| [x] -> Pair(x, Nil)
| hd::rest -> Pair(hd, list_to_pair rest)

and let_handle pair body = 
  let res = split_params pair ([],[]) in
  let params = (fun (a,b) -> a) res in
  let found_reserved = List.fold_left (fun a b -> (a || (check_var b))) false (List.map (fun (y) -> match y with
                                                                                                      | Symbol(x) -> x
                                                                                                      | _ -> raise X_syntax_error) params) in
  let args = (fun (a,b) -> b) res in
  match found_reserved with
    | true -> raise X_syntax_error
    | false -> Pair(Pair(Symbol("lambda"), Pair(list_to_pair params, body)),list_to_pair args)

(*********************************************************letrec functions****************************************************************)

and create_temp_bindings params = 
  match params with 
  | [] -> Nil
  | [x] -> Pair(Pair(x, Pair(Pair(Symbol "quote", Pair(Symbol "whatever", Nil)),Nil)), Nil)
  | head::rest -> Pair(Pair(head, Pair(Pair(Symbol "quote", Pair(Symbol "whatever", Nil)), Nil)), create_temp_bindings rest)

and create_setsbody params args body =
  match params, args with
  | [],[] -> Nil
  | [param], [arg] -> Pair(Pair(Symbol "set!", Pair(param, Pair(arg, Nil))), body)
  | hd_par::tl_par , hd_arg::tl_arg -> Pair(Pair(Symbol "set!", Pair(hd_par, Pair(hd_arg, Nil))), create_setsbody tl_par tl_arg body)
  | _,_ -> Nil


and let_rec_handle bind_list body = 
  let res = split_params bind_list ([],[]) in
  let params = (fun (a,b) -> a) res in
  let found_reserved = List.fold_left (fun a b -> (a || (check_var b))) false (List.map (fun (y) -> match y with
                                                                                                      | Symbol(x) -> x
                                                                                                      | _ -> raise X_syntax_error ) params) in
  let args = (fun (a,b) -> b) res in
  let temp_bindings = create_temp_bindings params in
  let new_sets_body = create_setsbody params args body in
  if found_reserved 
    then raise X_syntax_error
    else
     Pair(Symbol "let", Pair(temp_bindings, new_sets_body))
    

(*********************************************************cond functions******************************************************************)
and handle_nil rest = 
match rest with
| Nil -> Nil
| _ -> Pair(handle_cond rest, Nil)


and handle_cond list = 
match list with
| Nil -> Nil
| Pair(Pair(Symbol "else", begin_seq),_) -> (fun (x) -> match x with
                                                        | Nil -> raise X_syntax_error
                                                        | _ -> Pair(Symbol "begin", begin_seq)) begin_seq

| Pair(Pair(test, Pair(Symbol "=>", Pair(func, Nil))), rest) -> handle_fat_arrow test func rest

| Pair(Pair(test, seq),rest) -> (fun (x) -> match x with
                                                        | Nil -> raise X_syntax_error
                                                        | _ -> Pair(Symbol "if", Pair(test,Pair(Pair(Symbol "begin",seq),handle_nil rest )))) seq
| _ -> raise X_syntax_error


and handle_fat_arrow test func rest = 
match rest with 
| Nil -> Pair(Symbol "let", Pair(Pair(Pair(Symbol "value", Pair(test, Nil)),
          Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, Pair(func, Nil))), Nil)), Nil)),
            Pair(Pair(Symbol "if", Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), Nil))), Nil)))

| _ ->  Pair(Symbol "let", Pair(Pair(Pair(Symbol "value", Pair(test, Nil)),
        Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil,Pair(func, Nil))), Nil)), 
          Pair(Pair(Symbol "rest", Pair(Pair(Symbol "lambda", Pair(Nil, handle_nil rest)), Nil)), Nil))),                                                                   
            Pair(Pair(Symbol "if", Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), Pair(Pair(Symbol "rest", Nil), Nil)))), Nil)))       

(*********************************************************quasi-quote functions******************************************************************)

and handle_qq sexpr = 
match sexpr with
| Pair(Symbol "unquote", Pair(sxpr, Nil)) -> sxpr
| Pair(Symbol "unquote-splicing", Pair(sxpr, Nil)) -> raise X_syntax_error
| Nil -> Pair(Symbol "quote", Pair(Nil, Nil))
| Symbol(x) -> Pair(Symbol "quote", Pair(Symbol(x),Nil))
| Pair(Pair(Symbol "unquote-splicing", Pair(sxpr,Nil)), cdr) -> Pair(Symbol "append", Pair(sxpr, Pair(handle_qq cdr, Nil)))
| Pair(car, Pair(Symbol "unquote-splicing", Pair(sxpr,Nil))) -> Pair(Symbol "cons", Pair(handle_qq car, Pair(sxpr,Nil)))
| Pair(car, cdr) -> Pair(Symbol "cons", Pair(handle_qq car, Pair(handle_qq cdr, Nil)))
| _ -> sexpr

and is_proper_list sexpr = 
match sexpr with
| Pair(a,Nil) -> true
| Pair(a,b) -> is_proper_list b
| _-> raise X_syntax_error


let tag_parse_expression sexpr = tag_parsing sexpr;;

let tag_parse_expressions sexpr = List.map tag_parse_expression sexpr;;


end;; (* struct Tag_Parser *)
