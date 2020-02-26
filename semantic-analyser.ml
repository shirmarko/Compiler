#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct



let rec add_lexical expr = 

match expr with

| LambdaSimple(params, body) ->  LambdaSimple'(params, (handle_lambda params body []))

| LambdaOpt(params, optional, body) -> let new_body = (handle_lambda (List.append params [optional]) body []) in 

                                          LambdaOpt'(params,optional, new_body) 

| Const(exp) -> Const'(exp)

| Var(exp) -> Var'(VarFree(exp))

| If(test, dit, dif) -> If'(add_lexical test, add_lexical dit, add_lexical dif)

| Seq(exps) -> Seq'(List.map add_lexical exps) 

| Set(set_var, set_val) -> Set'(add_lexical set_var, add_lexical set_val)

| Def(def_var, def_val) -> Def'(add_lexical def_var, add_lexical def_val)

| Or(exps) -> Or'(List.map add_lexical exps)

| Applic(op, args) -> Applic'(add_lexical op, (List.map add_lexical args))



and handle_lambda params body acc = 

let acc = [params]::acc in

handle_body acc body





and handle_body acc body = 

  match body with

  | Var(str) -> (handle_var str acc (-1))

  

  | Const(exp) -> Const'(exp)

  | If(test, dit, dif) -> If'((handle_body acc) test, (handle_body acc) dit, (handle_body acc) dif)

  | Seq(exps) -> Seq'(List.map (handle_body acc) exps)

  | Set(set_var, set_val) -> Set'(handle_body acc set_var, handle_body acc set_val)

  | Or(exps) -> Or'(List.map (handle_body acc) exps)

  | Applic(op, args) -> Applic'(handle_body acc op, (List.map (handle_body acc) args))

  (* | Applic(op, args) -> Applic'( handle_body acc op, (List.map (handle_body acc) op::args)) *)

  

  | LambdaSimple(params2, body2) -> LambdaSimple'(params2, handle_lambda params2 body2 acc)

  | LambdaOpt(params2, optional, body2) -> LambdaOpt'(params2, optional, handle_lambda (List.append params2 [optional]) body2 acc)

  

  | _ -> raise X_syntax_error

  (* | Def(def_var, def_val) -> raise X_syntax_error *)



and handle_var v acc b_level = 

  match acc with

  | [] -> Var'(VarFree(v))             

  | [lst]::rest -> let index = (list_contains v lst 0) in

                    if (index = -1)

                      then handle_var v rest (b_level + 1)

                      else

                        if (b_level = -1)

                          then Var'(VarParam(v, index))

                          else

                            Var'(VarBound(v, b_level, index))

  | _ -> raise X_syntax_error                        



and list_contains v lst index = 

  match lst with

  | [] -> (-1)

  | a::rest -> if (v = a)

                    then index

                    else

                      list_contains v rest (index + 1)



(****************************************** annotate_tail_calls *******************************************)





and annotate_tp tp_in expr  = 

  match expr with 

  | LambdaSimple'(params, body) -> LambdaSimple'(params, annotate_tp true body)               

  | LambdaOpt'(params, optional, body) -> LambdaOpt'(params, optional, annotate_tp true body)

  | If'(test, dit, dif) -> If'(annotate_tp false test, annotate_tp tp_in dit, annotate_tp tp_in dif)

  | Seq'(exps) -> Seq'(handle_list exps tp_in)

  | Set'(set_var, set_val) -> Set'(annotate_tp false set_var, annotate_tp false set_val) (****check!@ set_var*)

  | Def'(def_var, def_val) -> Def'(annotate_tp false def_var, annotate_tp false def_val) (****check!@ def_var*)

  | Or'(exps) -> Or'(handle_list exps tp_in)

  | Applic'(op, args) -> handle_app op args tp_in

  |_ -> expr (*Var' and Const'*)







and handle_list exps tp_in = 

  match exps with

  | [] -> raise X_syntax_error

  | [last] -> [annotate_tp tp_in last ]

  | first::rest -> (List.append [annotate_tp false first ] (handle_list rest tp_in))



and handle_app op args tp_in = 

  match tp_in with

  | true -> ApplicTP'(annotate_tp false op , (List.map (annotate_tp false) args))

  | false -> Applic'(annotate_tp false op , (List.map (annotate_tp false) args))



(************************************************** boxing ********************************************)



and boxing expr = 

  match expr with

  | LambdaSimple'(params, body) -> (handle_boxing_lambdas params body)

  | LambdaOpt'(params, optional, body) -> (handle_boxing_lambdaopt params optional body)

  

  | If'(test, dit, dif) -> If'(boxing test, boxing dit, boxing dif)

  | Seq'(exps) -> Seq'(List.map boxing exps)

  (*********)

  | Set'(set_var, set_val) -> Set'(boxing set_var, boxing set_val)

  | Def'(def_var, def_val) -> Def'(def_var, boxing def_val)

  (*********)

  | Or'(exps) -> Or'(List.map boxing exps)

  | Applic'(op, args) -> Applic'(boxing op, (List.map boxing args))

  | ApplicTP'(op, args) -> ApplicTP'(boxing op, (List.map boxing args))

  |_ -> expr

  

and handle_boxing_lambdas params body = 

  let new_body = (try_box params body 0) in

  let new_body2 = boxing new_body in

  LambdaSimple'(params, new_body2)



and handle_boxing_lambdaopt params optional body = 

  let new_body = (try_box (List.append params [optional]) body 0) in

  let new_body2 = boxing new_body in

  LambdaOpt'(params, optional, new_body2)



and try_box params body index=

  match params with

  | [] -> boxing body

  | first::rest ->  try_box rest (search_and_box first body index) (index+1)





and search_and_box param body index =

  let result = search_P0 param body in (*returns just param list*)

  let paramed_vars = [result] in

  let bounded_vars = search_B0 param body in

  let result = (List.append paramed_vars bounded_vars) in

  

  let set_index_list = make_index_list result "set" 0 in

  let get_index_list = make_index_list result "get" 0 in



  let is_eq_list = check_eq_list set_index_list get_index_list in

  match set_index_list, get_index_list with

  | [], [] -> body

  | [], _ -> body

  | _, [] -> body

  | _, _ -> if (is_eq_list)

              then body

              else build_boxed_body param body index





and build_boxed_body param body index = 

  match body with

  | Seq'(list) -> (fun (list) -> match list with

                  | Set'(x,Box'(VarParam (_, _)))::rest -> Seq'((add_seq param list index)) 

                  | _ -> Seq'([Set'(Var'(VarParam(param, index)), Box'(VarParam(param, index)))]@[add_set_get param body])) list

  | _ -> Seq'((List.append [Set'(Var'(VarParam(param, index)), Box'(VarParam(param, index)))] [add_set_get param body]))



and add_seq param exps index = 

  match exps with

  | [] -> []

  | hd::tl -> match hd with

              | Set'(x,Box'(VarParam (_, _))) -> [hd]@(add_seq param tl index)

              | _ -> [Set'(Var'(VarParam(param, index)), Box'(VarParam(param, index)))] @ (List.map (add_set_get param) exps)  







and add_set_get param body = 

  match body with

  | Const'(exp) -> body

  | Var'(exp) -> (fun (exp) -> match exp with

                  | VarParam(str, mi) when (str = param) -> BoxGet'(exp)

                  | VarBound(str, mi, ma) when (str = param) -> BoxGet'(exp)

                  | _ -> body) exp

  

  | If'(test, dit, dif) -> If'(add_set_get param test, add_set_get param dit, add_set_get param dif)

  | Seq'(exps) -> Seq'(List.map (add_set_get param) exps)

  | Set'(set_var, set_val) -> (fun (set_var) -> match set_var with

                              | Var'(VarParam(str, mi)) when (str = param) -> BoxSet'(VarParam(str, mi), add_set_get param set_val)

                              | Var'(VarBound(str, mi, ma)) when (str = param) -> BoxSet'(VarBound(str, mi, ma), add_set_get param set_val)

                              | _ -> Set'(set_var, add_set_get param set_val)) set_var

  | BoxSet'(set_var, set_val) -> BoxSet'(set_var, (add_set_get param set_val))

  | Def'(def_var, def_val) -> Def'(def_var, add_set_get param def_val)

  | Or'(exps) -> Or'(List.map (add_set_get param) exps)

  | LambdaSimple'(params2, body2) -> if ((list_contains param params2 (0)) = (-1))

                                      then LambdaSimple'(params2, add_set_get param body2)

                                      else body

  | LambdaOpt'(params2, optional2, body2) -> if ((list_contains param (List.append params2 [optional2]) (0)) = (-1))

                                              then LambdaOpt'(params2, optional2, add_set_get param body2)

                                              else body

  | Applic'(op, args) -> Applic'(add_set_get param op, (List.map (add_set_get param) args))

  | ApplicTP'(op, args) -> ApplicTP'(add_set_get param op, (List.map (add_set_get param) args))

  | _ -> body





and search_P0 param body = 

  match body with

  | If'(test, dit, dif) -> (search_P0 param test)@(search_P0 param dit)@(search_P0 param dif)

  | Seq'(exps) -> (List.fold_left (fun a b -> a@(search_P0 param b)) [] exps)

  | Or'(exps) -> (List.fold_left (fun a b -> a@(search_P0 param b)) [] exps)

  | Applic'(op, args) -> (search_P0 param op)@(List.fold_left (fun a b -> a@(search_P0 param b)) [] args)

  | ApplicTP'(op, args) -> (search_P0 param op)@(List.fold_left (fun a b -> a@(search_P0 param b)) [] args)

  | BoxSet'(set_var, set_val) -> (search_P0 param set_val)

  | Set'(set_var, set_val) -> (fun (y) -> match y with

                              | Var'(VarParam(x, mi)) when (x = param) -> ["set"]

                              | _ -> []) set_var



  | Var'(var) -> (fun (y) -> match y with

              | VarParam(x, mi) when (x = param) -> ["get"]

              | _ -> []) var

  | _ -> []



and search_B0 param body = 

  match body with

  | If'(test, dit, dif) -> (search_B0 param test)@(search_B0 param dit)@(search_B0 param dif)

  | Seq'(exps) -> (List.fold_left (fun a b -> a@(search_B0 param b)) [] exps)

  | Or'(exps) -> (List.fold_left (fun a b -> a@(search_B0 param b)) [] exps)

  | Applic'(op, args) -> (search_B0 param op)@(List.fold_left (fun a b -> a@(search_B0 param b)) [] args)

  | ApplicTP'(op, args) -> (search_B0 param op)@(List.fold_left (fun a b -> a@(search_B0 param b)) [] args)

  

  | BoxSet'(set_var, set_val) -> (search_B0 param set_val)

  | Set'(set_var, set_val) -> (search_B0 param set_var)@(search_B0 param set_val)

  (*NO NEED FOR VAR, SEARCHING ONLY BOUND VARS*)



  | LambdaSimple'(params2, body2) -> if ((list_contains param params2 (0)) = (-1))

                                        then [(make_rib param body2)]

                                        else []

  | LambdaOpt'(params2, optional2, body2) ->if ((list_contains param (List.append params2 [optional2]) (0)) = (-1))

                                            then [(make_rib param body2)]

                                            else []

  | _ -> []



  and make_rib param body = 

    match body with

    | Set'(set_var, set_val) -> (fun (set_var) -> match set_var with

                              | Var'(VarBound(x, mi, ma)) when (x = param) ->  ["set"]@(make_rib param set_val)                                                            

                              | _ -> (make_rib param set_val)) set_var



    | If'(test, dit, dif) -> (make_rib param test)@(make_rib param dit)@(make_rib param dif)

    | Seq'(exps) -> (List.fold_left (fun a b -> a@(make_rib param b)) [] exps)

    | Or'(exps) -> (List.fold_left (fun a b -> a@(make_rib param b)) [] exps)

    | Applic'(op, args) -> (make_rib param op)@(List.fold_left (fun a b -> a@(make_rib param b)) [] args)

    | ApplicTP'(op, args) -> (make_rib param op)@(List.fold_left (fun a b -> a@(make_rib param b)) [] args)

    | BoxSet'(set_var, set_val) -> (make_rib param set_val)

    | LambdaSimple'(params2, body2) -> if ((list_contains param params2 (0)) = (-1))

                                          then (make_rib param body2)

                                          else []

    | LambdaOpt'(params2, optional2, body2) -> if ((list_contains param (List.append params2 [optional2]) (0)) = (-1))

                                              then (make_rib param body2)

                                              else []

    | Var'(var) -> (fun (var) -> match var with

                  | VarBound(x, mi, ma) when (x = param) ->  ["get"]                  

                  | _ -> []) var

    | _ -> []



 and make_index_list list act index = 

  match list with

  | [] -> []

  | first::rest -> if ((list_contains act first 0) = (-1)) (*-1 -> didnt find*)

                      then (make_index_list rest act (index+1))

                      else [index]@(make_index_list rest act (index+1))



  and check_eq_list lst1 lst2 = 

    match lst1, lst2 with

    | [],[] -> true

    | hd1::tl1, hd2::tl2 -> if (hd1 = hd2)

                              then (check_eq_list tl1 tl2)

                              else false

    | _,_ -> false;;    





let annotate_lexical_addresses e = add_lexical e;;



let annotate_tail_calls e = annotate_tp false e;;



let box_set e = boxing e;;



let run_semantics expr =

  box_set

    (annotate_tail_calls

       (annotate_lexical_addresses expr));;   
  

(* let run_semantics expr =

  box_set

       (annotate_lexical_addresses expr);;    *)
  
end;; (* struct Semantics *)
