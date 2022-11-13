(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

#use "pc.ml";;

let rec gcd a b =
  match (a, b) with
  | (0, b) -> b
  | (a, 0) -> a
  | (a, b) -> gcd b (a mod b);;

type scm_number =
  | ScmRational of (int * int)
  | ScmReal of float;;

type sexpr =
  | ScmVoid
  | ScmNil
  | ScmBoolean of bool
  | ScmChar of char
  | ScmString of string
  | ScmSymbol of string
  | ScmNumber of scm_number
  | ScmVector of (sexpr list)
  | ScmPair of (sexpr * sexpr);;
type parts = 
  | Static of string
  | Dynamic of sexpr;;

module type READER = sig
    val nt_sexpr : sexpr PC.parser
end;; (* end of READER signature *)
(*return the reader here*)
module Reader : READER = struct
open PC;;

let unitify nt = pack nt (fun _ -> ());;


let rec nt_whitespace str =
  const (fun ch -> ch <= ' ') str

  (*change and to here*)
and nt_end_of_line_or_file str = 
  let nt1 = unitify (char '\n') in
  let nt2 = unitify nt_end_of_input in
  let nt1 = disj nt1 nt2 in
  nt1 str

  (*change and to here*)
and nt_line_comment str = 
  let nt1 = char ';' in
  let nt2 = diff nt_any nt_end_of_line_or_file in
  let nt2 = star nt2 in
  let nt1 = caten nt1 (caten nt2 nt_end_of_line_or_file) in 
  let nt1 = unitify nt1 in 
  nt1 str

let rec nt_rec str =
  let nt = disj_list [unitify nt_sexpr; unitify nt_number;unitify nt_boolean;unitify nt_char;unitify nt_symbol;
   unitify nt_string;unitify nt_vector;unitify nt_list;unitify nt_quoted_forms;nt_comment;] in
  let nt = unitify (caten (caten (star nt_whitespace) nt ) (star nt_whitespace)) in
  nt str

             
and nt_sexpr_comment str = 
  let nt1 = unitify (caten (word "#;") nt_rec) in 
  nt1 str
  
and nt_paired_comment str = 
  let nt2 = disj_list [unitify nt_char; unitify nt_string; nt_comment] in 
  let nt3 = disj nt2 (unitify (one_of "{}")) in 
  let nt3 = diff nt_any nt3 in
  let nt3 = disj (unitify nt3) nt2 in
  let nt2 = star nt3 in
  let nt1 = unitify (caten (char '{') (caten nt2 (char '}'))) in
  nt1 str
and nt_comment str =
  disj_list
  [nt_line_comment;
    nt_paired_comment;
    nt_sexpr_comment] str


and nt_skip_star str =
  let nt1 = disj (unitify nt_whitespace) nt_comment in
  let nt1 = unitify (star nt1) in
  nt1 str
and make_skipped_star (nt : 'a parser) =
  let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
  let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
  nt1


and nt_natural = 
  pack (plus (range_ci '0' '9')) (fun (e) -> int_of_string(list_to_string e)) 
and nt_int str = 
  let digit = nt_natural in
  let sign = maybe (disj (char '-') (char '+')) in
  let nt1 = caten sign digit in
  let nt1 = pack nt1 (fun (sign,digit)->
    match sign with
    | Some('-') -> ((-1)* digit)
    | _ -> digit) in 
  nt1 str

 
and nt_frac str = 
  let nt1 = caten nt_int (char '/') in
  let nt1 = pack (caten nt1 nt_natural) (fun ((e0,_),e2) -> (e0/abs (gcd e0 e2),e2/abs (gcd e0 e2))) in
  let nt1 = pack (only_if nt1 (fun ((x,y))-> y!=0)) (fun ((x,y))-> ScmRational (x,y)) in
  nt1 str

and nt_integer_part str = 
 let nt1 = pack nt_natural (fun (e) -> string_of_int e) in
 nt1 str

and nt_mantissa str = 
  let nt1 = pack (plus (range_ci '0' '9')) (fun (ans) -> list_to_string ans) in
  nt1 str
  

and nt_exponent str = 
  let worde = word_ci "e" in
  let word1 =  word "*10^" in
  let word2 = word "*10**" in
  let nt1 = pack (caten (disj_list [worde;word1;word2]) nt_int) (fun (a,b) -> ("e")^(string_of_int b))  in
  nt1 str


  


and nt_float str = 
  let char_dot = word "." in
  let nt_int_string = pack nt_int (fun (e) -> string_of_int e) in

  let exp = pack (maybe nt_exponent) (fun (e) -> 
    match e with
    | None -> "e0"
    | Some(e) -> e) in
  
  let mantissa = pack (maybe nt_mantissa) (fun (e)->
    match e with
    | Some(e) -> "."^e
    | None -> ""
    )  in
  let mantissa = pack (caten char_dot mantissa) (fun(_,e) -> e) in

  let nt_floatA = pack (caten nt_int_string mantissa) (fun (n,m) -> n^m) in

  let nt_floatA = pack (caten nt_floatA exp) (fun (a,exp) ->  a^exp) in

  let nt_floatB = pack (caten char_dot nt_mantissa) (fun (_,e) -> e ) in
  let nt_floatB =  pack (caten nt_floatB exp) (fun (m,e) -> "."^ m^e) in

  let nt_floatC = pack (caten nt_int_string nt_exponent) (fun (n,e) -> n^e) in

  let sign = maybe (disj (char '-') (char '+')) in

  let nt_ans = pack (disj_list [nt_floatA; nt_floatB; nt_floatC]) (fun (s)->  s)  in

  let nt_ans = pack (caten sign nt_ans) (fun (signn,f) -> 
    match signn with
    | Some('-') -> ScmReal ((float_of_int (-1)) *. (float_of_string f))
    | _-> ScmReal (float_of_string f)
    ) in

  nt_ans str
  

and nt_number str =
  let nt1 = nt_float in
  let nt2 = nt_frac in
  let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
  let nt1 = disj nt1 (disj nt2 nt3) in
  let nt1 = pack nt1 (fun r -> ScmNumber r) in
  let nt1 = not_followed_by nt1 nt_symbol_char in
  nt1 str 
  (*change here to and*)
and nt_boolean str = 
  let nt1 = word_ci "#f" in
  let nt1 = pack nt1 (fun _-> false) in
  let nt2 = word_ci "#t" in
  let nt2 = pack nt2 (fun _ -> true) in
  let nt1 = disj nt1 nt2 in
  let nt1 = pack nt1 (fun b -> ScmBoolean b) in
  nt1 str

and nt_char_simple str = 
    let nt1 = diff nt_any (const(fun (c) -> c <= ' '))  in
    nt1 str
and make_named_char char_name ch = 
    let nt1 = word_ci char_name in
    pack nt1 (fun (e) -> ch)

and nt_char_named str =
  let nt1 =
    disj_list [(make_named_char "newline" '\n');
               (make_named_char "page" '\012');
               (make_named_char "return" '\r');
               (make_named_char "space" ' ');
               (make_named_char "tab" '\t');
               (make_named_char "nul" '\000')] in
  nt1 str


and nt_char_hex str = 
  let nt1 = range_ci '0' '9' in
  let nt2 = range_ci 'a' 'f' in
  let nt1 = plus (disj nt1 nt2 )in
  let nt_ans = pack (caten (word "x")  nt1) (fun (x,n) -> char_of_int (int_of_string ("0x"^(list_to_string n)))) in
  nt_ans str
  and nt_char str = 
  let nt = pack (caten (word "#\\") (disj_list [nt_char_named;nt_char_hex;nt_char_simple]))
    (fun (_,c) -> ScmChar c) in
  nt str



and nt_symbol_char str = 
    let nt_digit = range '0' '9' in 
    let nt_az = range 'a' 'z' in
    let nt_AZ = range 'A' 'Z' in
    let nt_sim = disj_list[(char '!');(char '$');(char '^');(char '*');(char '-');
    (char '_'); (char '=');(char '+');(char '<');(char '>');(char '?');(char '/'); (char ':')] in
    let nt_ans = disj_list[nt_digit; nt_az;nt_AZ;nt_sim] in
    nt_ans str

and nt_symbol str =
  let nt1 = plus nt_symbol_char in
  let nt1 = pack nt1 list_to_string in
  let nt1 = pack nt1 (fun name -> ScmSymbol name) in
  let nt1 = diff nt1 nt_number in
  nt1 str

  (* need to add the f *)
and string_meta_char str =
let nt1 =
  disj_list [(make_named_char "\\n" '\n');
             (make_named_char "\\f" '\012');
             (make_named_char "\\r" '\r');
             (make_named_char "\\\"" '\"');
             (make_named_char "\\t" '\t');
             (make_named_char "~~" '~')] in
nt1 str


    

and nt_string_literal_char str =
  let nt = diff nt_any (disj_list [(char '\\');(char '"');(char '~')]) in
  nt str
  
and nt_string_hex_char str =
  let nt = pack (caten ((caten (word "\\") nt_char_hex)) (char ';')) (fun ((_,x),_)-> x) in
  nt str
and nt_string_interpolator str = 
  let nt1 = unitify(caten nt_skip_star (char '~')) in
  let nt2 = unitify(caten (caten nt1 (char '{')) nt_skip_star)  in
  let nt3 = pack (caten (caten nt2 nt_sexpr) (char '}')) (fun ((_,sexpr),_)->Dynamic(ScmPair(ScmSymbol "format",ScmPair(ScmString "~a",ScmPair(sexpr,ScmNil))))) in
  
  nt3 str


  and counter () = 
  let x = ref 0 in
  let get () = !x in
  let inc () = !x + 1 in
  (get,inc)
and nt_string str = 
    let string_char = pack (plus (disj_list[nt_string_literal_char;string_meta_char;nt_string_hex_char])) (fun (s) -> Static(list_to_string s)) in
    let string_char = star (disj nt_string_interpolator string_char) in
    let string_char = pack (caten (char '"') (caten string_char (char '"'))) (fun (_,(e,_))->
      match e with
      | [] -> ScmString ""
      | (Static(e))::[] -> ScmString e
      | (Dynamic(e))::[] -> e
      | Static(e)::rest -> ScmPair(ScmSymbol "string-append" ,ScmPair(ScmString e ,(nt_hard rest)))
      | Dynamic(e)::rest -> ScmPair(ScmSymbol "string-append" ,ScmPair(e ,(nt_hard rest)))) in
      
    string_char str

and nt_hard rest = 
    List.fold_right
    (fun a l -> 
      match a with
      | Dynamic(a) -> ScmPair(a,l)
      | Static(a) -> ScmPair(ScmString(a),l)) 
    rest
    ScmNil


    



and nt_vector str =
  let nt1 = word "#(" in
  let nt2 = caten nt_skip_star (char ')') in
  let nt2 = pack nt2 (fun _ -> ScmVector []) in
  let nt3 = plus nt_sexpr in
  let nt4 = char ')' in
  let nt3 = caten nt3 nt4 in
  let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
  let nt2 = disj nt2 nt3 in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
  nt1 str



  

and nt_proper_list str = 
  let nt4 = caten (caten (char '(') (plus nt_sexpr )) (char (')'))  in
  let nt2 = pack  nt4 (fun ((_,sexpr),_)->
    List.fold_right
              (fun curr sexpr_list -> ScmPair (curr, sexpr_list))
              sexpr
              ScmNil ) in
  nt2 str

and nt_improper_list str = 
  let nt1 = char '(' in   (* open par with spaces *)
  let nt2 = char '.' in
  let nt3 = char ')' in (*close par*)
  let nt4 = nt_sexpr in
  let nt5 = pack (caten (caten (plus nt4) nt2) nt4) (fun((left_sexpr,_),right_sexpr) -> (left_sexpr,right_sexpr)) in
  let nt5 = pack (caten nt1 nt5) (fun (_,(eft_sexpr,right_sexpr)) -> (eft_sexpr,right_sexpr)) in
  let nt2 = pack (caten nt5 nt3) (fun ((left_sexpres,right_sexprs),_)->
    List.fold_right
              (fun curr sexpr_list -> ScmPair (curr, sexpr_list))
              left_sexpres
              right_sexprs ) in
  nt2 str
and nt_empty_list str = 
  let nt1 = pack(caten (caten (char '(') nt_skip_star ) (char ')')) (fun ((_,_),_) -> ScmNil) in
  nt1 str
and nt_list str = 
    let nt1 = disj_list [nt_empty_list;nt_proper_list; nt_improper_list; ] in
    nt1 str
    
  
and nt_quoted_forms str =
  let nt = disj_list [nt_quote;nt_quasiquote;nt_unquote;nt_unquote_splicing] in
  nt str
  
and nt_quote str = (* ' *)
  let nt1 = word "'" in
  let nt1 = pack (caten nt1 nt_sexpr) (fun (tag,sexp) -> (ScmPair( ScmSymbol "quote" , (ScmPair (sexp, ScmNil))))) in
  nt1 str
 
and nt_quasiquote str =(* ` *)
  let nt1 = word "`" in
  let nt1 = pack (caten nt1 nt_sexpr) (fun (tag,sexp) -> (ScmPair( ScmSymbol "quasiquote" ,(ScmPair (sexp, ScmNil))))) in
  nt1 str
and nt_unquote str = (* , *)
  let nt1 = word "," in
  let nt1 = pack (caten nt1 nt_sexpr) (fun (tag,sexp) -> (ScmPair( ScmSymbol "unquote" ,(ScmPair (sexp, ScmNil))))) in
  nt1 str
and nt_unquote_splicing str = (* ,@ *)
  let nt1 = word ",@" in
  let nt1 = pack (caten nt1 nt_sexpr) (fun (tag,sexp) -> (ScmPair( ScmSymbol "unquote-splicing" ,(ScmPair (sexp, ScmNil))))) in
  nt1 str

(*change to and*)
and nt_sexpr str =
  let nt1 =
    disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
               nt_string; nt_vector; nt_list; nt_quoted_forms] in
  let nt1 = make_skipped_star nt1 in
  nt1 str

end;; (* end of struct Reader *)

let rec string_of_sexpr = function
  | ScmVoid -> "#<void>"
  | ScmNil -> "()"
  | ScmBoolean(false) -> "#f"
  | ScmBoolean(true) -> "#t"
  | ScmChar('\n') -> "#\\newline"
  | ScmChar('\r') -> "#\\return"
  | ScmChar('\012') -> "#\\page"
  | ScmChar('\t') -> "#\\tab"
  | ScmChar(' ') -> "#\\space"
  | ScmChar(ch) ->
     if (ch < ' ')
     then let n = int_of_char ch in
          Printf.sprintf "#\\x%x" n
     else Printf.sprintf "#\\%c" ch
  | ScmString(str) ->
     Printf.sprintf "\"%s\""
       (String.concat ""
          (List.map
             (function
              | '\n' -> "\\n"
              | '\012' -> "\\f"
              | '\r' -> "\\r"
              | '\t' -> "\\t"
              | ch ->
                 if (ch < ' ')
                 then Printf.sprintf "\\x%x;" (int_of_char ch)
                 else Printf.sprintf "%c" ch)
             (string_to_list str)))
  | ScmSymbol(sym) -> sym
  | ScmNumber(ScmRational(0, _)) -> "0"
  | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
  | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
  | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
  | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
  | ScmVector(sexprs) ->
     let strings = List.map string_of_sexpr sexprs in
     let inner_string = String.concat " " strings in
     Printf.sprintf "#(%s)" inner_string
  | ScmPair(ScmSymbol "quote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "'%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "quasiquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "`%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote-splicing",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",@%s" (string_of_sexpr sexpr)
  | ScmPair(car, cdr) ->
     string_of_sexpr' (string_of_sexpr car) cdr
and string_of_sexpr' car_string = function
  | ScmNil -> Printf.sprintf "(%s)" car_string
  | ScmPair(cadr, cddr) ->
     let new_car_string =
       Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
     string_of_sexpr' new_car_string cddr
  | cdr ->
     let cdr_string = (string_of_sexpr cdr) in
     Printf.sprintf "(%s . %s)" car_string cdr_string;;
