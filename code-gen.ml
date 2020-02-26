#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "SOB_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* This signature represents the idea of outputing assembly code as a string
     for a single AST', given the full constants and fvars tables. 
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string

  val gen_and_rename : expr' -> expr'
end;;

exception X_error;;
exception X_error1;;
exception X_error2;;
exception X_error3;;
exception X_error4;;
exception X_not_yet_implemented;;

module Code_Gen : CODE_GEN = struct
  (* let make_consts_tbl asts = raise X_not_yet_implemented;;
  let make_fvars_tbl asts = raise X_not_yet_implemented;;
  let generate consts fvars e = raise X_not_yet_implemented;; *)




(****************************************************const table************************************************************)

let rename_index = ref 0;;

let incr_rename() = 
    rename_index := !rename_index + 1;;

let tagged_list = ref [];;

let update_tagged_list list =
  tagged_list := list;;

let rec handle_consts asts = 
  (* let renamed_asts = (List.map gen_and_rename asts) in *)
  let renamed_asts = asts in
  let first_level = (List.fold_left (fun a b -> a@ (const_list_level_1 b)) [] renamed_asts) in
  let after_remove = remove_dup first_level in
  let tag_collection = add_tags_sexpr after_remove in
  ignore(update_tagged_list tag_collection);
  let expanded_pairs = expand_pair after_remove in
  let remove_tagSexp_from_const = (List.map (fun constant-> match constant with 
                                                            | Void -> constant
                                                            | Sexpr(x) -> (Sexpr(remove_tagSexp x))) expanded_pairs) in
  let after_remove_2 = remove_dup remove_tagSexp_from_const in
  let pre_const = [(Void, (0, "MAKE_VOID")); (Sexpr(Nil), (1, "MAKE_NIL"));
                    (Sexpr(Bool false), (2, "MAKE_BOOL(0)")); (Sexpr(Bool true), (4, "MAKE_BOOL(1)"))] in
  let create_offsets = handle_offsets after_remove_2 pre_const 6 in
    (List.map (set_tagRef_pointers create_offsets tag_collection) create_offsets)

    
and gen_and_rename2 ast =
  let index = !rename_index in
  ignore(incr_rename()); 
  rename index ast


and rename index ast = 
  match ast with
  | Const'(x) -> (fun x -> match x with
                            | Void -> ast
                            | Sexpr(y) -> Const'(Sexpr(rename_sexpr index y))) x
  | BoxSet'(var, exp) -> BoxSet'(var, rename index exp)
  | If'(test, dit, dif) -> If'(rename index test, rename index dit, rename index dif)
  | Seq'(exps) -> Seq'(List.map (rename index) exps)
  | Set'(a, b) -> Set'(rename index a, rename index b)
  | Def'(a, b) -> Def'(rename index a, rename index b)
  | Or'(exps) -> Or'(List.map (rename index) exps)
  | LambdaSimple'(params, body) -> LambdaSimple'(params, rename index body)
  | LambdaOpt'(params, opt, body) -> LambdaOpt'(params, opt, rename index body )
  | Applic'(op, args) -> Applic'(rename index op, (List.map (rename index) args))
  | ApplicTP'(op, args) -> ApplicTP'(rename index op, (List.map (rename index) args))
  | _ -> ast (*Var', Box', BoxGet'*)

and rename_sexpr index sexpr = 
  match sexpr with
  | Pair(car, cdr) -> Pair(rename_sexpr index car, rename_sexpr index cdr)
  | TaggedSexpr(name, sexpr2) -> TaggedSexpr(name^string_of_int(index), rename_sexpr index sexpr2)
  | TagRef(name) -> TagRef(name^string_of_int(index))
  | _ -> sexpr (*Bool, Nil, Number, Char, String, Symbol*)



and create_const_tuple sexp offset prev_list = 
  match sexp with
  | Sexpr(Number(Int (x))) -> ((Sexpr(Number(Int (x))), (offset, "MAKE_LITERAL_INT(" ^(string_of_int x)^")")), 9)
  | Sexpr(Number(Float (x))) -> ((Sexpr(Number(Float (x))), (offset, "MAKE_LITERAL_FLOAT(" ^(string_of_float x)^")")), 9)
  (* | Sexpr(Char(c)) -> ((Sexpr(Char(c)), (offset, "MAKE_LITERAL_CHAR(\'" ^(Char.escaped c)^"\')")), 2) *)
  | Sexpr(Char(c)) -> ((Sexpr(Char(c)), (offset, "MAKE_LITERAL_CHAR(" ^(string_of_int(Char.code c))^")")), 2)
  (* | Sexpr(String(str)) -> ((Sexpr(String str), (offset, "MAKE_LITERAL_STRING \"" ^str^"\"")), 9 + (String.length str)) *)
  | Sexpr(String(str)) -> ((Sexpr(String str), (offset, "MAKE_LITERAL_STRING " ^(string_of_int(String.length str))^ ", \"" ^str^"\"")), 9 + (String.length str))
  | Sexpr(Symbol(sym)) -> ((Sexpr(Symbol sym), (offset, "MAKE_LITERAL_SYMBOL(const_tbl+" ^(string_of_int (find_offset (String sym) prev_list))^")")), 9)
  
  | Sexpr(Pair(TagRef(name1), TagRef(name2))) -> ((Sexpr(Pair(TagRef(name1), TagRef(name2))),(offset,"MAKE_LITERAL_PAIR(const_tbl+-1, const_tbl+-1)")), 17)
  | Sexpr(Pair(car, TagRef(name))) -> ((Sexpr(Pair(car, TagRef(name))),(offset,(string_of_int (find_offset car prev_list)))), 17)
  | Sexpr(Pair(TagRef(name), cdr)) -> ((Sexpr(Pair(TagRef(name), cdr)),(offset,(string_of_int (find_offset cdr prev_list)))), 17)

  | Sexpr(Pair(car,cdr)) -> ((Sexpr(Pair(car,cdr)), (offset, "MAKE_LITERAL_PAIR(const_tbl+"^
                  (string_of_int (find_offset car prev_list))^", const_tbl+"^(string_of_int (find_offset cdr prev_list))^")")), 17)
  (* | Sexpr(TaggedSexpr(name,sxpr)) -> ((Sexpr(TaggedSexpr(name,sxpr)), (offset, "")), 0) *)
  | Sexpr(TagRef(name)) -> ((Sexpr(TagRef(name)), (offset, "")), -1)
  | _ -> raise X_error

  

and find_offset obj prev_list = 
  match prev_list with
  | [] -> raise X_error
  | (Sexpr(hd), (offset, x))::tl when (sexpr_eq hd obj) -> offset
  | hd::tl -> find_offset obj tl

and handle_offsets const_list tuple_list offset = 
  match const_list with
  | [] -> tuple_list
  | hd::tl -> let new_const =  (create_const_tuple hd offset tuple_list) in
              let tuple = ((fun (t,o) -> t) new_const) in
              let obj_size = ((fun (t,o) -> o) new_const) in
              if (obj_size = -1)
                then (handle_offsets tl tuple_list offset)
                else
                  let new_offset = (offset+obj_size) in
                  let new_tuple_list = tuple_list@[tuple] in
                  (handle_offsets tl new_tuple_list new_offset)
  
  
and const_list_level_1 ast = 
  match ast with
  | Const'(x) -> [x]
  | BoxSet'(v, exp) -> (const_list_level_1 exp)
  | If'(test, dit, dif) -> (const_list_level_1 test) @ (const_list_level_1 dit) @ (const_list_level_1 dif)
  | Seq'(exps) -> (List.fold_left (fun a b -> a@(const_list_level_1 b)) [] exps)
  | Set'(s_var, s_val) -> (const_list_level_1 s_var) @ (const_list_level_1 s_val)
  | Def'(d_var, d_val) -> (const_list_level_1 d_var) @ (const_list_level_1 d_val)
  | Or'(exps) -> (List.fold_left (fun a b -> a@(const_list_level_1 b)) [] exps)
  | LambdaSimple'(params, body) -> (const_list_level_1 body)
  | LambdaOpt'(params, opt,  body) -> (const_list_level_1 body)
  | Applic'(op, args) -> (const_list_level_1 op) @ (List.fold_left (fun a b -> a@(const_list_level_1 b)) [] args)
  | ApplicTP'(op, args) -> (const_list_level_1 op) @ (List.fold_left (fun a b -> a@(const_list_level_1 b)) [] args)
  | _ -> []


and remove_dup list = 
  match list with
  | [] -> []
  | hd::tl -> [hd]@(remove_dup (check_dup hd tl))

and check_dup hd tl =
  match tl with
  | [] -> []
  | t1::t2 when (expr_eq (Const(hd)) (Const(t1))) -> (check_dup hd t2)
  | t1::t2 -> [t1]@(check_dup hd t2)

and expand_pair const_list = 
  match const_list with
  | [] -> []
  | hd::tl -> (check_const hd)@(expand_pair tl)

and check_const const =
  match const with
  | Void -> []
  | Sexpr(x) ->  check_paired x

and check_paired sexpr = 
  match sexpr with
  | Bool(x) -> []
  | Nil -> []
  | Symbol(str) -> [Sexpr(String(str)); Sexpr(Symbol(str))]
  | Pair(car, cdr) -> (check_paired car)@(check_paired cdr)@[Sexpr(sexpr)]
  | TaggedSexpr(name, sexpr2) -> check_paired sexpr2
  | TagRef(name) -> [Sexpr(sexpr)]
  | _ -> [Sexpr(sexpr)] (*number, char, string*)
  
and remove_tagSexp sexpr = 
  match sexpr with
  | TaggedSexpr(name,sexpr2) -> remove_tagSexp sexpr2
  | Pair(car, cdr) -> Pair(remove_tagSexp car, remove_tagSexp cdr)
  | _ -> sexpr

and add_tags_sexpr const_list = 
  match const_list with
  | [] -> []
  | hd::tl -> (check_const_tag hd)@(add_tags_sexpr tl)

and check_const_tag const =
  match const with
  | Void -> []
  | Sexpr(x) ->  add_tag x

and add_tag sexpr = 
  match sexpr with
  | Pair(car, cdr) -> (add_tag car)@(add_tag cdr)
  | TaggedSexpr(name, sexpr2) -> [(name, sexpr2)]
  | _ -> []

and set_tagRef_pointers const_tbl tag_collection const=
  match const with
  | (Sexpr(Pair(TagRef(name1), TagRef(name2))),(offset,"MAKE_LITERAL_PAIR(const_tbl+-1, const_tbl+-1)")) ->
    (Sexpr(Pair(TagRef(name1), TagRef(name2))),(offset,"MAKE_LITERAL_PAIR(const_tbl+"^(find_offset_tagreg name1 tag_collection const_tbl)^", const_tbl+"
    ^(find_offset_tagreg name2 tag_collection const_tbl)^")"))
  | (Sexpr(Pair(car, TagRef(name))),(offset,car_offset)) ->
    (Sexpr(Pair(car, TagRef(name))),(offset,"MAKE_LITERAL_PAIR(const_tbl+"^car_offset^", const_tbl+"^(find_offset_tagreg name tag_collection const_tbl)^")"))
  |(Sexpr(Pair(TagRef(name), cdr)),(offset,cdr_offset)) ->
    (Sexpr(Pair(TagRef(name), cdr)), (offset,"MAKE_LITERAL_PAIR(const_tbl+"^(find_offset_tagreg name tag_collection const_tbl)^", const_tbl+"^cdr_offset^")"))
  | _ -> const

and find_offset_tagreg name tag_collection const_tbl =
  string_of_int(tagref_address const_tbl (find_sexp_tag name tag_collection))

and find_sexp_tag name tag_collection = 
  match tag_collection with
  | [] -> raise X_error
  | (name2, sexpr)::tl when (name2 = name) -> sexpr
  | (name2, sexpr)::tl -> find_sexp_tag name tl

and tagref_address const_tbl sexpr = 
  match const_tbl with
  | [] -> raise X_error
  | (Sexpr(sexpr2), (offset, str))::tl when (sexpr_eq sexpr sexpr2) -> offset
  | (sexpr2, (offset, str))::tl -> tagref_address tl sexpr

(********************************************free_vars**********************************************)

let rec create_fvar_table asts=
  let fvar_list = (List.fold_left (fun a b -> a @ (fvar_table_ast b)) [] asts) in
  let primitive_names_to_labels = 
  ["boolean?"; "float?"; "integer?"; "pair?";
   "null?"; "char?"; "string?";
   "procedure?"; "symbol?"; "string-length";
   "string-ref"; "string-set!"; "make-string";
   "symbol->string"; 
   "char->integer"; "integer->char"; "eq?";
   "+"; "*"; "-"; "/"; "<"; "="; "car"; "cdr"; "cons"; "set-car!"; "set-cdr!"; "apply"] in
  let prim_with_fvars = primitive_names_to_labels@fvar_list in
  let list_without_dup = remove_dup_fvar prim_with_fvars in
  (fvars_to_tuples list_without_dup [] 0)

and fvars_to_tuples fvars tuples_list offset = 
  match fvars with
  | [] -> tuples_list
  | hd::tl -> (fvars_to_tuples tl (tuples_list@[(hd, offset)]) (offset+8))


and fvar_table_ast ast =
  match ast with
  | Var'(VarFree(str)) -> [str]
  | Box'(VarFree(str)) -> [str]
  | BoxGet'(VarFree(str)) -> [str]
  | BoxSet'(VarFree(str), expr) -> [str] @ (fvar_table_ast expr)
  | BoxSet'(var, expr) -> (fvar_table_ast expr)
  | If'(test, dit, dif) -> (fvar_table_ast test) @ (fvar_table_ast dit) @ (fvar_table_ast dif)
  | Seq'(exps) -> (List.fold_left (fun a b -> a@ (fvar_table_ast b)) [] exps)
  | Set'(exp1, exp2) -> (fvar_table_ast exp1) @ (fvar_table_ast exp2)
  | Def'(exp1, exp2) -> (fvar_table_ast exp1) @ (fvar_table_ast exp2)
  | Or'(exps) -> (List.fold_left (fun a b -> a@ (fvar_table_ast b)) [] exps)
  | LambdaSimple'(params, body) -> (fvar_table_ast body)
  | LambdaOpt'(params, opt, body) -> (fvar_table_ast body)
  | Applic'(op, args) -> (fvar_table_ast op) @ (List.fold_left (fun a b -> a@ (fvar_table_ast b)) [] args)
  | ApplicTP'(op, args) -> (fvar_table_ast op) @ (List.fold_left (fun a b -> a@ (fvar_table_ast b)) [] args)
  | _ -> []

and remove_dup_fvar list = 
  match list with
  | [] -> []
  | hd::tl -> [hd]@(remove_dup_fvar (check_dup_fvar hd tl))

and check_dup_fvar hd tl =
  match tl with
  | [] -> []
  | t1::t2 when (hd = t1) -> (check_dup_fvar hd t2)
  | t1::t2 -> [t1]@(check_dup_fvar hd t2)


(********************************************generator**********************************************)
  let label_counter = ref 0;;
    
  let count () =
    ( label_counter := 1 + !label_counter ;
      !label_counter );;
    
(* val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string *)
let rec start_gen depth consts fvars ast = 
  match ast with
  | Const'(x) -> "\tmov rax, const_tbl+" ^ (addressInConstTable consts x)^ "\n"
  | Seq'(exps) -> (List.fold_left (fun a b -> (a ^ (start_gen depth consts fvars b) ^ "\n")) "" exps)
  | If'(test, dit, dif) -> let count = string_of_int (count()) in
                            (start_gen depth consts fvars test) ^"\n"
                            ^"\tcmp rax, SOB_FALSE_ADDRESS\n"
                            ^"\tje Lelse_"^count^"\n"
                            ^(start_gen depth consts fvars dit) ^"\n"
                            ^"\tjmp Lexit_"^count^"\n"
                            ^"\tLelse_"^count^":\n"
                            ^(start_gen depth consts fvars dif) ^"\n"
                            ^"\tLexit_"^count^":\n"
  | Or'(exps) -> let count = string_of_int (count()) in
                (String.concat ("\n\tcmp rax, SOB_FALSE_ADDRESS\n"^"\tjne Lexit_"^count^"\n") 
                (List.map (start_gen depth consts fvars) exps))^"\n\tLexit_"^count^":\n"
  | Var'(VarParam(_, minor)) -> "\tmov rax, qword [rbp + 8 *(4 + "^(string_of_int minor)^")]    ;GetvarParam \n"
  | Set'(Var'(VarParam(_, minor)),exp) -> (start_gen depth consts fvars exp)^
                                          "\tmov qword [rbp + 8 *(4+"^(string_of_int minor)^")], rax  ;SetvarParam \n"^
                                          "\tmov rax, SOB_VOID_ADDRESS\n"
  | Var'(VarBound(_, major, minor)) ->  "\tmov rax, qword [rbp + 8 * 2]   ;GetvarBound \n"
                                        ^"\tmov rax, qword [rax + 8 * "^(string_of_int major)^"]\n"
                                        ^"\tmov rax, qword [rax + 8 * "^(string_of_int minor)^"]\n"
  | Set'(Var'(VarBound(_,major,minor)),exp) -> (start_gen depth consts fvars exp)^
                                              "\tmov rbx, qword [rbp + 8 * 2]   ;SetvarBound  \n"^
                                              "\tmov rbx, qword [rbx + 8 * "^(string_of_int major)^"]\n"^
                                              "\tmov qword [rbx + 8 *"^(string_of_int minor)^"], rax\n"^
                                              "\tmov rax, SOB_VOID_ADDRESS\n"
  | Var'(VarFree(v)) -> "\tmov rax, qword ["^(label_in_fvar_table fvars v)^"]   ;GetvarFree \n"                          
  | Set'(Var'(VarFree(v)),exp) -> (start_gen depth consts fvars exp)^
                                   "\tmov qword ["^(label_in_fvar_table fvars v)^"], rax    ;SetvarFree \n"^
                                   "\tmov rax, SOB_VOID_ADDRESS\n"
  | Def'(Var'(VarFree(v)),exp) -> (start_gen depth consts fvars exp)^
                                   "\tmov qword ["^(label_in_fvar_table fvars v)^"], rax    ;DetvarFree \n"^
                                   "\tmov rax, SOB_VOID_ADDRESS\n"
  | BoxGet'(v) -> (start_gen depth consts fvars (Var'(v)))^ "\tmov rax, qword [rax]   ;BoxGet'  \n"
  | BoxSet'(v,exp) -> (start_gen depth consts fvars exp)^
                            "\tpush rax     ;BoxSet'  \n"^
                            (start_gen depth consts fvars (Var'(v)))^
                            "\tpop qword [rax]\n"^
                            "\tmov rax, SOB_VOID_ADDRESS\n"
  | LambdaSimple'(params, body) -> (generate_lambda depth consts fvars params body)
  | Applic'(proc, args) -> (generate_app depth consts fvars proc args)
  | ApplicTP'(proc, args) -> (generate_app depth consts fvars proc args)
  | LambdaOpt'(params, opt, body) -> (generate_opt depth consts fvars params opt body)
  | Box'(VarParam (name,minor)) -> "\tMALLOC rax, 8\n"^
                                    "\tmov rbx, qword [rbp + 8 *(4+"^(string_of_int minor)^")]\n"^
                                    "\tmov [rax], rbx\n"
  | _ -> "not yet implemented"

(*******************************************LambdaSimple***********************************************)

and generate_lambda depth consts fvars params body = 
  let gen_body = (start_gen (depth+1) consts fvars body) in
  let label = string_of_int(count()) in
  let make_closure = 
"\tMAKE_CLOSURE(rax, rdi, Lcode_" ^label^")

  jmp Lcont_"^label^"

  Lcode_"^label^":
    push rbp
    mov rbp, rsp\n"
    (* "mov qword [rbp+3*WORD_SIZE], "^string_of_int(params_length_int+1)^" \n" *)
    ^gen_body^
"   leave
    ret

  Lcont_"^label^":\n" in
  
  if (depth = 0)
  then
    "\tmov rdi, SOB_NIL_ADDRESS\n"^make_closure

  else
  let malloc_new_env = "\tMALLOC rbx, "^(string_of_int((depth)*8)) ^"     ;malloc newEnv size :"^(string_of_int((depth)*8)) ^"\n" in
  let malloc_env_0_params =
  "\tmov rsi,qword [rbp + 8 * 3]     ;creates a ptr to the params on stack                         
  cmp rsi, 0                         ;checks if the prevEnv was empty lambda
  jne Lreg_label_"^label^"
  mov rdx, SOB_NIL_ADDRESS          ;case for empty prevEnv
  jmp after_MALLOC_PARAM_"^label^"
  Lreg_label_"^label^":
  shl rsi, 3                         ;mult by 8, to fit size of ptr's
  MALLOC rdx, rsi
  after_MALLOC_PARAM_"^label^":\n" in
  let insert_params_ptr_to_new_env = "\tmov [rbx], rdx\n" in

  malloc_new_env^malloc_env_0_params^insert_params_ptr_to_new_env^
"\tmov rdi, rbx               ;saves the ptr to the new_env
  mov rcx, 0
  .loop1:                     ;copying params from stack 
    cmp rcx, qword [rbp + 8 * 3]        ;end of copying loop \ prevEnv is empty
    jz .loop_end1
    mov rsi, qword [rbp + 8 * (4 + rcx)]
    mov qword [rdx], rsi      ;rsi holds the env length
    add rdx, 8
    inc rcx
    jmp .loop1
  .loop_end1:

  add rbx, 8                  ;rbx before adding, held the param MALLOC or SOB_NIL_ADDRESS in case of prevEnv was empty
  mov rcx, 0
  mov rax, qword [rbp + 8 * 2]      ;the prevEnv from the stack
  cmp rax, SOB_NIL_ADDRESS      ;handling the case of depth=1, and creating first time env
  jz .loop_end2
    .loop2:         ;copying prev environment to ExtEnv
      cmp rcx, "^string_of_int(depth-1)^"   
      jz .loop_end2
      mov rdx, [rax]    ;rdx points to prev env
      mov qword [rbx], rdx
      add rax, 8
      add rbx, 8    
      inc rcx
      jmp .loop2
    .loop_end2:\n"
    ^make_closure

(***********************************search in const and fvar table*********************************)

and addressInConstTable consts exp = 
  match exp with
  | Void -> addressInConstTable2 consts exp
  | Sexpr(TagRef(name)) -> search_in_tagged_list name consts
  | Sexpr(x) -> addressInConstTable2 consts (Sexpr(remove_tagSexp x))

and addressInConstTable2 consts exp = 
  match consts with
  | [] -> raise X_error1
  | (const, (address, str))::tl when (expr'_eq (Const'(exp)) (Const'(const))) -> (string_of_int(address))
  | hd::tl -> addressInConstTable2 tl exp
  
and search_in_tagged_list name consts =
  let tag_list = !tagged_list in
  search2_tag_list name consts tag_list
  
and search2_tag_list name consts tag_list =
  match tag_list with
  | [] -> raise X_error2
  | (name2, sexpr2)::tl when (name = name2) -> (addressInConstTable2 consts (Sexpr(sexpr2)))
  | hd::tl -> search2_tag_list name consts tl

and label_in_fvar_table fvars v = 
  match fvars with
  | [] -> raise X_error
  | (var, address)::tl when (v = var) -> "fvar_tbl+"^(string_of_int(address))
  | hd::tl -> label_in_fvar_table tl v

(*******************************************Applic***********************************************)

and generate_app depth consts fvars proc args =
  let n = string_of_int(List.length(args) + 1) in
  let magic = "\tmov rdx, MAGIC
  \tpush rdx\n" in
  let gen_args = (List.fold_right (fun a b -> b^(start_gen depth consts fvars a)^"\tpush rax\n") args "") in
  let push_n = "\tmov rdx, "^n^"
  push rdx\n" in
  let gen_proc = (start_gen depth consts fvars proc) in
  magic^
  gen_args^
  push_n^
  gen_proc^
  "\tCLOSURE_ENV rbx, rax
   \tpush rbx
   \tCLOSURE_CODE rbx, rax
   \tcall rbx
   \tadd rsp, 8     ;pop env
   \tpop rbx        ;arg count
   \tshl rbx, 3     ;rbx = rbx * 8
   add rsp, rbx     ;pop args
   ;add rsp, 8       ;pop MAGIC \n"

(*******************************************lamdaOpt***********************************************)
and generate_opt depth consts fvars params opt body = 
  let gen_body = (start_gen (depth+1) consts fvars body) in
  let label = string_of_int(count()) in
  let params_length_int = List.length(params) in
  let params_length_string = string_of_int(List.length(params)) in
  let fix_stack_lambdaOpt= 
    "\tcmp PARAM_COUNT, "^string_of_int(List.length(params) + 1)^"
    ja Label_greater_"^label^"           ;args.len > params.len
    
    ;args.len = params.len
    ;mov qword [rbp+3*WORD_SIZE], "^string_of_int(params_length_int+1)^"
    jmp Lend_lambdaOpt_"^label^"
    
    
    Label_greater_"^label^":                    ;args.len > params.len
    mov rbx, PARAM_COUNT
    sub rbx, "^params_length_string^"     ; rbx = num of args - num of params
    sub rbx, 1                            ; added because of the changing to magic
    mov r15, PARAM_COUNT
    shl r15, 3
    mov rsi, rbp
    add rsi, 16                           ;was 24, before changing to magic                       
    add rsi, r15                          ; rsi = the stack address of the first argument
    mov rdi, [rsi]                        ; rdi = the first argument to copy
    MAKE_PAIR(rax, rdi, SOB_NIL_ADDRESS)  ; rax = holds the malloc address of the pair
    mov rcx, 1
    Loop_copy_to_malloc_"^label^":
        cmp rcx, rbx                      
        je Label_end_copy_"^label^"
        sub rsi, 8
        mov rdi, [rsi]
        mov rdx, rax
        MAKE_PAIR(rax, rdi, rdx)
        add rcx, 1
        jmp Loop_copy_to_malloc_"^label^"
    Label_end_copy_"^label^":
    mov rcx, 0
    mov cl, byte [rax]                                                ;debug T_PAIR
    mov r11, rbp                   
    add r11, 32
    add r11, "^string_of_int(params_length_int*8)^"               ; saves the place in stack to put the list
    mov [r11], rax                                                ; put the list the stack
    add r11, 8            
    
    ;mov qword [rbp+3*WORD_SIZE], "^string_of_int(params_length_int+1)^"  ;increase number of args in stack
    
    
    ;mov qword [r11], MAGIC                                        ;insert MAGIC above list
    ;mov qword [rbp+3*WORD_SIZE], "^string_of_int(params_length_int+1)^"        ;change the args number in stack

    ;r11 holds the address of first arg to be copied
    ;r10 holds the prev rbp - where we need to put the new frame


    ;SHIFT_OPT "^string_of_int(params_length_int+6)^", r11, r10                    ;number of recieved args +1(list) +5 (consts-env, ret, magic..)
    
    Lend_lambdaOpt_"^label^":\n" in 

  let make_closure = 
"\tMAKE_CLOSURE(rax, rdi, Lcode_" ^label^")

  jmp Lcont_"^label^"

  Lcode_"^label^": 
    mov r10, rbp                    ;saves the old frame rbp
    push rbp
    mov rbp, rsp\n"
    ^fix_stack_lambdaOpt^
    gen_body^
"   leave
    ret

  Lcont_"^label^":\n" in
  
  if (depth = 0)
  then
    "\tmov rdi, SOB_NIL_ADDRESS\n"^make_closure

  else
  let malloc_new_env = "\tMALLOC rbx, "^(string_of_int((depth)*8)) ^"     ;malloc newEnv size :"^(string_of_int((depth)*8)) ^"\n" in
  let malloc_env_0_params =
  "\tmov rsi,qword [rbp + 8 * 3]     ;creates a ptr to the params on stack                         
  cmp rsi, 0                         ;checks if the prevEnv was empty lambda
  jne Lreg_label_"^label^"
  mov rdx, SOB_NIL_ADDRESS          ;case for empty prevEnv
  jmp after_MALLOC_PARAM_"^label^"
  Lreg_label_"^label^":
  shl rsi, 3                         ;mult by 8, to fit size of ptr's
  MALLOC rdx, rsi
  after_MALLOC_PARAM_"^label^":\n" in
  let insert_params_ptr_to_new_env = "\tmov [rbx], rdx\n" in

  malloc_new_env^malloc_env_0_params^insert_params_ptr_to_new_env^
"\tmov rdi, rbx               ;saves the ptr to the new_env
  mov rcx, 0
  .loop1:                     ;copying params from stack 
    cmp rcx, qword [rbp + 8 * 3]        ;end of copying loop \ prevEnv is empty
    jz .loop_end1
    mov rsi, qword [rbp + 8 * (4 + rcx)]
    mov qword [rdx], rsi      ;rsi holds the env length
    add rdx, 8
    inc rcx
    jmp .loop1
  .loop_end1:

  add rbx, 8                  ;rbx before adding, held the param MALLOC or SOB_NIL_ADDRESS in case of prevEnv was empty
  mov rcx, 0
  mov rax, qword [rbp + 8 * 2]      ;the prevEnv from the stack
  cmp rax, SOB_NIL_ADDRESS      ;handling the case of depth=1, and creating first time env
  jz .loop_end2
    .loop2:         ;copying prev environment to ExtEnv
      cmp rcx, "^string_of_int(depth-1)^"   
      jz .loop_end2
      mov rdx, [rax]    ;rdx points to prev env
      mov qword [rbx], rdx
      add rax, 8
      add rbx, 8    
      inc rcx
      jmp .loop2
    .loop_end2:\n"
    ^make_closure


(********************************************applicTP**********************************************)

and generate_app_tp depth consts fvars proc args =
  let n = string_of_int(List.length(args) + 1) in
  let magic = "\tmov rdx, MAGIC
  \tpush rdx\n" in
  let gen_args = (List.fold_right (fun a b -> b^(start_gen depth consts fvars a)^"\tpush rax\n") args "") in
  let push_n = "\tmov rdx, "^n^"
  \tpush rdx\n" in
  let gen_proc = (start_gen depth consts fvars proc) in
  magic^
  gen_args^
  push_n^
  gen_proc^
  "\tCLOSURE_ENV rbx, rax
   \tpush rbx
   \tpush qword [rbp +8]            ;old ret address
   \tSHIFT_FRAME "^string_of_int(5+(List.length(args)))^"    ;shift TP
   \tCLOSURE_CODE rbx, rax
   \tjmp rbx\n";;




(********************************************END**********************************************)

  let make_consts_tbl asts = handle_consts asts;;
  let make_fvars_tbl asts = create_fvar_table asts;;
  let generate consts fvars e = start_gen 0 consts fvars e;;
  let gen_and_rename ast = gen_and_rename2 ast;;
end;;