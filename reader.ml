#use "pc.ml";;

open PC;;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Int of int
  | Float of float;;

type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | TaggedSexpr of string * sexpr
  | TagRef of string;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | TaggedSexpr(name1, expr1), TaggedSexpr(name2, expr2) -> (name1 = name2) && (sexpr_eq expr1 expr2) 
  | TagRef(name1), TagRef(name2) -> name1 = name2
  | _ -> false;;
  
module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

 

(*********************************************our code************************************************)

(********************************************* help ***********************************************)

let make_paired nt_left nt_right nt =
  let nt = caten nt_left nt in
  let nt = pack nt (function (_, e) -> e) in
  let nt = caten nt nt_right in
  let nt = pack nt (function (e, _) -> e) in
  nt;;

let nt_whitespaces = star nt_whitespace;;

let make_spaced nt = make_paired nt_whitespaces nt_whitespaces nt;;

let make_paren nt = make_paired ( char '(' ) ( char ')' ) nt ;;

(********************************************* bool ***********************************************)
let _true_ = 
  let nt= (word_ci "#t") in 
  let nt= pack nt (fun (x) -> Bool(true)) in
  nt;;
let _false_ = 
  let nt= (word_ci "#f") in 
  let nt= pack nt (fun (x) -> Bool(false)) in
  nt;;

let _bool_ = disj _true_ _false_;;


  (********************************************* symbol **********************************************)


  let _digitsym_ = range '0' '9';;
  let _lowersym_ = range 'a' 'z';;
  let _uppersym_ = 
    let _uppersym_= range 'A' 'Z' in
    let _uppersym_ = pack _uppersym_ (fun (x) -> lowercase_ascii x ) in
    _uppersym_;;
  let _othersym_ = disj_list [(char '!'); (char '$'); (char '^'); (char '*');
                  (char '-'); (char '_'); (char '='); (char '+'); (char '<'); (char '>'); (char '?'); (char '/'); (char ':'); ];;

  let _symbol_ = 
    let nt = disj_list [_digitsym_; _lowersym_; _uppersym_; _othersym_] in
    let nt = plus nt in
    let nt = pack nt (fun (x) -> Symbol(list_to_string x)) in
    nt;;

(********************************************* number ***********************************************)

let _digit_ = range '0' '9';;
let _natural_ = plus _digit_;;

let _positiveInt_ =
  let nt = pack _natural_ (fun (ds) ->  (list_to_string ds)) in
  let nt = caten (char '+') nt in
  let nt = pack nt (fun (x,s) -> s) in
  nt;;

let _negativeInt_ =
  let nt = pack _natural_ (fun (ds) -> ('-'::ds)) in
  let nt = pack nt (fun (ds) ->  (list_to_string ds)) in
  let nt = caten (char '-') nt in
  let nt = pack nt (fun (x,s) -> s ) in
  nt;;

let _unsignedInt_ =
  let nt = pack _natural_ (fun (ds) ->  (list_to_string ds)) in
  nt;;

let _integer_ = disj _positiveInt_ (disj _negativeInt_ _unsignedInt_);;

(* let _floatWithNoPre_ =
  let nt = pack _natural_ (fun (ds) -> ('.'::ds)) in
  let nt = pack nt (fun (ds) ->  (list_to_string ds)) in
  let ntdot = caten (char '.') nt in
  let ntdot = pack ntdot (fun (x,s) -> s) in
  ntdot;; *)

let _floatWithPre_ = 
  let nt = pack _natural_ (fun (ds) -> ('.'::ds)) in
  let nt = pack nt (fun (ds) -> (list_to_string ds)) in 
  let ntdot = caten (char '.') nt in
  let ntdot = pack ntdot (fun (x,s) -> s) in
  let nt4 = caten _integer_ ntdot in
  let nt5 = pack nt4 (fun (i,f) ->  (i^f)) in
  nt5;;

(* let _float_ = disj _floatWithNoPre_ _floatWithPre_;; *)
let _float_ = _floatWithPre_;;

(* let _LiteralCharwithoutDigits_ = const (fun ch -> (Char.code ch) != 34 && (Char.code ch) != 92
 && (Char.code ch) != 40 && (Char.code ch) != 41 && (Char.code ch) != 59 &&
 ((Char.code ch) <= 48 || (Char.code ch) >= 57 ) && (Char.code ch > 32)) ;; *)

let _reg_number_  =
  let _numInt_ = pack _integer_ (fun (x) -> Int (int_of_string x)) in
  let _numFloat_ = pack _float_ (fun (x) -> Float (float_of_string x)) in
  let nt = disj _numFloat_ _numInt_ in
  let nt = pack nt (fun (x) -> Number (x)) in
  nt;;

  (*********************Scientific notation***************************)

let _sci_number_ = 
  
  let nt = caten _reg_number_ (char_ci 'e') in
  let nt = pack nt (fun (e,s) -> e) in
  let _numInt_ = pack _integer_ (fun (x) -> Int (int_of_string x)) in
  let nt = caten nt _numInt_ in
  let nt1 = pack nt (fun (x, y) -> match x, y with  
                                                            | Number(Int(p)), Int (i)-> Number( Float((float_of_int p)*.(10.**(float_of_int i))))
                                                            | Number(Float(p)), Int (i)-> Number( Float(p*.(10.**(float_of_int i))))
                                                            | _, _ -> Nil )in
  nt1;;

(************************************radix******************************)

  let make_NT_digit ch_from ch_to displacement =
    let nt = const (fun ch -> ch_from <= ch && ch <= ch_to) in
    let nt = pack nt (let delta = (Char.code ch_from) - displacement in
		      fun ch -> (Char.code ch) - delta) in
          nt;;

  let digit_convert = 
    let nt = disj_list [(make_NT_digit '0' '9' 0) ;	(make_NT_digit 'a' 'z' 10); (make_NT_digit 'A' 'Z' 10)] in
    let nt = plus nt in
    nt;;

  let digit_convert_float = 
    let nt = disj_list [(make_NT_digit '0' '9' 0) ;	(make_NT_digit 'a' 'z' 10); (make_NT_digit 'A' 'Z' 10)] in
    let nt = pack nt (fun x -> float_of_int x) in
    let nt = plus nt in
    nt;;

  let _rad_ lst base = 
    (List.fold_left (fun a b -> base * a + b) 0 lst);;

  let _rad_after_dot_ lst base = 
    let nt = (List.fold_right (fun a b -> ((a /. base) +. (b/. base) )) lst 0.) in
    nt;;

  let nt_sign  = 
     let nt = maybe (disj (char '-') (char '+')) in
     let nt = pack nt (fun (x) -> match x with
                        | Some ('-')-> int_of_string("-1")
                        | Some ('+') -> int_of_string("1")
                        | None -> int_of_string("1")
                        | _ -> int_of_string("1")) in
                        nt ;;     

  let begin_sul_base_r = 
    let nt_sul = (char '#') in
    let nt_base = pack _natural_ (fun (ds) ->  (list_to_string ds)) in
    let nt_base = pack nt_base (fun x -> (int_of_string x)) in
    let nt_r = (char_ci 'r') in                                    
    let nt_caten = caten nt_sul nt_base in
    let nt_caten = pack nt_caten (fun (sul, base) ->  base) in
    let nt_caten = caten nt_caten nt_r in
    let nt_only_base = pack nt_caten (fun (base,r) -> base) in 
    nt_only_base;;


  let _rad_int_ = 
    let nt_only_base = begin_sul_base_r in
    let nt_base_sign = caten nt_only_base nt_sign in (*base, sign*)
    let nt_base_sign_num = caten nt_base_sign digit_convert in (*((base,sign), lst)*)
    let nt = pack nt_base_sign_num (fun ((base,sign), lst) -> (_rad_ lst base)*sign ) in
    let nt = pack nt (fun x -> Number (Int (x))) in
    nt;;

let _rad_float_ = 
    let nt_only_base = begin_sul_base_r in
    let nt_base_sign = caten nt_only_base nt_sign in (*base, sign*)
    let nt_base_sign_num = caten nt_base_sign digit_convert in (*((base,sign), lst)*)
    let nt = pack nt_base_sign_num (fun ((base,sign), lst) -> (base,(_rad_ lst base)*sign)) in (*(base, ans)*)
    let dot = (char '.') in
    let dot = caten dot digit_convert_float in 
    let dot = pack dot (fun (dot,lst) -> lst) in
    let nt_caten = caten nt dot in (*((base, ans), lst_dot)*)
    let nt_caten = pack nt_caten (fun ((base,ans), lst) -> (float_of_int ans) +. (_rad_after_dot_ lst (float_of_int base))) in
    let nt_caten = pack nt_caten (fun (x) -> Number (Float(x))) in
    nt_caten;;

  let _radix_= disj _rad_float_ _rad_int_ ;;


(**************************number***************************)

let _number_ = 
  let nt = disj_list [_sci_number_ ; _radix_; _reg_number_ ] in
  let nt = not_followed_by nt _symbol_ in
  nt;;

(********************************************* char ***********************************************)

            
let _ntnul_ = pack (word_ci "#\\nul") (fun (x) -> (Char (Char.chr(0))));;

let _ntnewline_ = pack (word_ci "#\\newline") (fun (x) -> (Char (Char.chr(10))));;

let _ntreturn_ = pack (word_ci "#\\return") (fun (x) -> (Char (Char.chr(13))));;

let _nttab_ = pack (word_ci "#\\tab") (fun (x) -> (Char (Char.chr(9))));;

let _ntpage_ = pack (word_ci "#\\page") (fun (x) -> (Char (Char.chr(12))));;

let _ntspace_ = pack (word_ci "#\\space") (fun (x) -> (Char (Char.chr(32))));;

let _named_ = disj_list [_ntnul_; _ntnewline_; _ntreturn_; _nttab_; _ntpage_; _ntspace_];;


let _visible_ =
  let nt = const (fun ch -> (Char.code ch) > 32) in
  let nt = caten (word "#\\") nt in
  let nt = pack nt (fun (sul,ch) -> Char(ch)) in
  nt;;

let _char_ = disj _named_ _visible_ ;;

(********************************************* string ***********************************************)

let _str_= make_paired (char '"') (char '"');;

let _metaChar_ = 
  let ntr = pack (word_ci "\\r") (fun (x) ->  (Char.chr(13))) in
  let ntt = pack (word_ci "\\t") (fun (x) ->  (Char.chr(9))) in
  let ntn = pack (word_ci "\\n") (fun (x) ->  (Char.chr(10))) in
  let ntf = pack (word_ci "\\f") (fun (x) ->  (Char.chr(12))) in
  let nt1 = pack (word_ci "\\\\") (fun (x) ->  (Char.chr(92))) in
  let nt2 = pack (word_ci "\\\"") (fun (x) -> (Char.chr(34))) in
  let nt = disj_list [ntr; ntt; ntn; ntf; nt1; nt2] in
  nt;;

let _LiteralChar_ = const (fun ch -> (Char.code ch) != 34 && (Char.code ch) != 92 ) ;;
let _strChar_ = disj _LiteralChar_ _metaChar_;;

let _string_ = 
  let nt = _str_ (star _strChar_) in
  let nt = pack nt (fun (lst) -> String (list_to_string lst)) in
  nt;;


  (********************************************* symbol **********************************************)


  (* let _digitsym_ = range '0' '9';;
  let _lowersym_ = range 'a' 'z';;
  let _uppersym_ = 
    let _uppersym_= range 'A' 'Z' in
    let _uppersym_ = pack _uppersym_ (fun (x) -> lowercase_ascii x ) in
    _uppersym_;;
  let _othersym_ = disj_list [(char '!'); (char '$'); (char '^'); (char '*');
                  (char '-'); (char '_'); (char '='); (char '+'); (char '<'); (char '>'); (char '?'); (char '/'); (char ':'); ];;

  let _symbol_ = 
    let nt = disj_list [_digitsym_; _lowersym_; _uppersym_; _othersym_] in
    let nt = plus nt in
    let nt = pack nt (fun (x) -> Symbol(list_to_string x)) in
    nt;; *)

 
 (********************************************* sexp ***********************************************)

 let rec to_pair p = match p with
 | [] -> Nil
 | (x::rest) -> Pair(x, to_pair rest) ;;

 let rec to_pair_dotted p = match p with
 | x::[] -> x
 | (x::rest) -> Pair(x, to_pair_dotted rest)
 | [] -> Nil ;;

 let rec  _sexp_ s =
    let nt = disj_list [_bool_; _char_; _number_; _string_; _symbol_;_empty_list_ ;  _list_ ; _dotted_; _allQuoted_; _tag_ ] in
    let nt = make_skip nt in
    nt s 

 (********************************************* list ***********************************************)

 and _list_ s = 
    let nt = make_spaced _sexp_ in
    let _sexps_ = star nt in
    let _makeList_ = make_paren _sexps_  in
    let _listToPair_ = pack _makeList_ (fun (lst) -> to_pair lst) in
    let _checkList_ = pack _listToPair_(fun (lst) -> match (dup_exist (filter_tag lst)) with
                                                      | false -> lst
                                                      | true -> raise X_this_should_not_happen ) in
    _checkList_ s
    (* _listToPair_  s *)


  and _dotted_ s = 
    (* let nt = make_spaced _sexp_ in *)
    let _plussexp_ = plus _sexp_ in
    let nt1 = caten _plussexp_ (char '.') in
    let nt1 = pack nt1 (fun (plus, dot) -> plus) in
    let nt1 = caten nt1 _sexp_ in
    let nt1 = pack nt1 (fun ((e,s)) -> List.append e [s]) in
    let nt1 = make_paren nt1 in
    let _dottedtoPair_ = pack nt1 (fun (lst) -> to_pair_dotted lst) in
    let _checkList_ = pack _dottedtoPair_ (fun (lst) -> match (dup_exist (filter_tag lst)) with
                                                      | false -> lst
                                                      | true -> raise X_this_should_not_happen ) in
    _checkList_ s
    (* _dottedtoPair_ s *)

  and dup_exist lst = match lst with
  | [] -> false
  | hd::tl -> List.exists ((=) hd) tl || dup_exist tl


  and filter_tag pair = match pair with 
  | TaggedSexpr(str,expr) -> str::(filter_tag expr)
  | Pair(x,y) -> List.append (filter_tag x)  (filter_tag y )
  | _ -> []




(********************************************* Nil ***********************************************)
and _empty_list_ s = 
  let _skip_ = star (disj_list [sexp_comment ; line_comment; nt_whitespace; nt_none]) in
  let nt = make_paren _skip_ in
  let nt = pack nt (fun (x) -> Nil) in
    nt s


(********************************************* quoted ***********************************************)
and _allQuoted_ s = 
  let nt = make_spaced _sexp_ in
  let _quoted_ = pack (caten (char '\'') nt) (fun (q,exp) -> exp) in 
  let _quoted_ = pack _quoted_ (fun (exp) -> (Symbol("quote"))::(exp::[])) in
  
  let _quasiquoted_ = pack (caten (char '`') nt) (fun (q,exp) -> exp) in 
  let _quasiquoted_ = pack _quasiquoted_ (fun (exp) -> (Symbol("quasiquote"))::(exp::[])) in
  
  let _unquoted_ = pack (caten (char ',') nt) (fun (q,exp) -> exp) in 
  let _unquoted_ = pack _unquoted_ (fun (exp) -> (Symbol("unquote"))::(exp::[])) in 

  let _unquoted_splicing_ = pack (caten (word ",@") nt) (fun (q,exp) -> exp) in 
  let _unquoted_splicing_ = pack _unquoted_splicing_ (fun (exp) -> (Symbol("unquote-splicing"))::(exp::[])) in
  
  let _quotedisj_ = (disj_list [_quoted_; _quasiquoted_; _unquoted_; _unquoted_splicing_]) in
  let ntt = pack _quotedisj_ (fun (lst) -> to_pair lst) in
    ntt s


  (**************************************************** tags *************************************************)
    and _continue_tag_ s = 
      let nt_eq = (char '=') in 
      let nt = caten nt_eq _sexp_ in
      let nt = pack nt (fun (eq,sexp) -> sexp) in
      nt s 
    
    
    and _tag_ s = 
      let sul = (char '#') in
      let make_sym = make_paired (char '{') (char '}') (make_spaced _symbol_) in
      let prefix = caten sul make_sym in (*(sul, symbol)*)
      let tag_ref = pack prefix (fun (sul, symbol) -> symbol) in
      let cont_check = caten tag_ref (maybe _continue_tag_) in
      let cont_check = pack cont_check (fun (sym, option)-> match option with
                                                        | Some(e) when (check sym e) -> raise X_this_should_not_happen
                                                        | Some(e) when not(check sym e) -> to_tagExp sym e
                                                        | None -> to_tagExp sym Nil
                                                        | Some(_) -> Nil) in
      cont_check s

    and check symbol expr = match expr with 
                            | TaggedSexpr(a,b) -> (sexpr_eq (Symbol(a)) symbol) || (check symbol b)
                            | Pair(a,b) -> (check symbol a) || (check symbol b)
                            | _ -> false
    
    and to_tagExp sym expr = match expr, sym with
                            | Nil, Symbol(x) -> TagRef(x)
                            | _ , Symbol(x) -> TaggedSexpr(x, expr)
                            | _,_ -> Nil
  (***************************************** comments and skip ******************************************)

  and sexp_comment s = 
    let sexp_comment = caten (word "#;") _sexp_  in 
    let sexp_comment = pack sexp_comment (fun (e,s) -> ' ') in 
    sexp_comment s

  and line_comment s = 
    let line_comment = char ';' in
    (*let legal_before = diff nt_any line_comment in*)
    let nt_end = disj (pack (word "\n") (fun (x) -> [])) (pack nt_end_of_input (fun (x) -> [])) in
    let nt = star (diff nt_any nt_end) in
    let nt = caten nt nt_end in
    let nt = pack nt (fun (e,s) -> []) in
    let line_comment = caten line_comment nt in
    let line_comment = pack line_comment (fun (e,s) -> ' ') in
    line_comment s
    (*end of input - not followed by \n*)

  and make_skip nt = 
    let _skip_ = disj_list [sexp_comment ; line_comment; nt_whitespace] in
    
    let _skip_ = star _skip_ in
    make_paired _skip_ _skip_ nt;;

    
(* let read_sexpr string = (fun (parsed,un)-> parsed)(_sexp_ (string_to_list string));; *)
let read_sexpr string = (fun (parsed,un)-> match un with 
                                          | [] -> parsed
                                          | _ -> raise X_no_match)(_sexp_ (string_to_list string));;

let read_sexprs string = (fun (parsed,un)-> parsed)((star (disj _sexp_ nt_none)) (string_to_list string));;

end;; (* struct Reader *)
