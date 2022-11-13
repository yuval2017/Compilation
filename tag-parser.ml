#use "reader.ml";;

type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;

let rec list_to_proper_list = function
| [] -> ScmNil
| hd::[] -> ScmPair (hd, ScmNil)
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec list_to_improper_list = function
| [] -> raise X_proper_list_error
| hd::[] -> hd
| hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
match scm_list with
| ScmNil -> sexpr
| ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
| _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))

let rec scm_map f sexpr =
match sexpr with
| ScmNil -> ScmNil
| ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
| _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
match sexpr1, sexpr2 with
| ScmNil, ScmNil -> ScmNil
| ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
| _, _ ->
    let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
    raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
| ScmNil -> []
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;




let rec scm_is_list = function
| ScmPair (hd, tl) -> scm_is_list tl
| ScmNil -> true
| _ -> false

let rec scm_list_length = function
| ScmPair (hd, tl) -> 1 + (scm_list_length tl)
| ScmNil -> 0
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec untag expr =
let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

let untag_lambda_opt vars var body =
let vars = match vars with
| [] -> ScmSymbol var
| _ -> list_to_improper_list (untag_vars (vars@[var])) in
list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

match expr with
| (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
| ScmConst s -> s
| ScmVar (name) -> ScmSymbol(name)
| ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
| ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
| ScmSeq(exprs) -> untag_tagged_list "begin" exprs
| ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
| ScmDef (var, value) -> untag_tagged_list "define" [var; value]
| ScmOr (exprs) -> untag_tagged_list "or" exprs
| ScmLambdaSimple (vars, ScmSeq(body)) ->
    let vars = list_to_proper_list (untag_vars vars) in
    let body = List.map untag body in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
| ScmLambdaSimple (vars, body) ->
    let vars = list_to_proper_list (untag_vars vars) in
    list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
| ScmLambdaOpt (vars, var, ScmSeq(body)) ->
    let body = List.map untag body in
    untag_lambda_opt vars var body
| ScmLambdaOpt (vars, var, body) ->
    let body = [untag body] in
    untag_lambda_opt vars var body
| ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;


let rec string_of_expr expr =
string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
match n1, n2 with
| ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
        numerator1 = numerator2 && denominator1 = denominator2
| ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
| _, _ -> false

let rec sexpr_eq s1 s2 =
match s1, s2 with
| (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
| ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
| ScmChar(char1), ScmChar(char2) -> char1 = char2
| ScmString(string1), ScmString(string2) -> String.equal string1 string2
| ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
| ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
| ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
| ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
| _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                            (expr_eq dit1 dit2) &&
                                              (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
        List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
        (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
end;; 

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;



let rec tag_parse_expression sexpr =
let sexpr = macro_expand sexpr in
match sexpr with 
| ScmNil -> ScmConst(ScmNil)
| ScmBoolean(e) -> ScmConst(ScmBoolean(e))
| ScmChar(e) -> ScmConst(ScmChar(e))
| ScmNumber(e) -> ScmConst(ScmNumber(e))
| ScmString(e) -> ScmConst(ScmString(e))
| ScmVoid -> ScmConst ScmVoid
| ScmVector(e) -> ScmConst(sexpr)
| ScmPair (ScmSymbol "quote", (ScmPair (e, ScmNil))) -> ScmConst(e)
| ScmSymbol(e) -> if List.mem e reserved_word_list then raise (X_reserved_word e) else ScmVar e 
| ScmPair(ScmSymbol "if",ScmPair(test, ScmPair (dit, maybe_dif)))-> ScmIf ((tag_parse_expression test), (tag_parse_expression dit), (if_exp maybe_dif))
| ScmPair (ScmSymbol "or", sexprs) -> (match sexprs with
  | ScmPair (e, ScmNil) -> tag_parse_expression e
  | ScmNil ->  ScmConst(ScmBoolean false)
  | _ -> ScmOr (par_to_array sexprs tag_parse_expression))
  (*calculate the body of the labda*)
| ScmPair(ScmSymbol "begin",sexprs) -> begin_fun sexprs
| (ScmPair(ScmSymbol "lambda",ScmPair(args,body))) -> lambda_exp args body
| (ScmPair(ScmSymbol "define", ScmNil)) -> raise (X_syntax_error(sexpr, "bad define syntax"))
| (ScmPair(ScmSymbol "define", ScmPair(vars,vals))) -> define_exp vars vals sexpr
| ScmPair(ScmSymbol "set!",ScmPair (var, to_set)) -> set_exp var to_set
| ScmPair(app, sexprs) -> ScmApplic((tag_parse_expression app), to_list_scm2 sexprs)



and throw_exeption sexpr message =
 raise (X_syntax_error (sexpr, message))

and to_list_scm sexpr =
  match sexpr with
  | ScmNil -> []
  | ScmPair(e,rest) -> (tag_parse_expression e)::(to_list_scm rest)
  | e -> throw_exeption sexpr "Sexpr structure not recognized"


and to_list_scm2 sexpr =
  match sexpr with
  | ScmNil -> []
  | ScmPair(e,rest) -> (tag_parse_expression e)::(to_list_scm rest)
  | e -> [(tag_parse_expression e)]
  


and set_exp var sexpr = 
  match var, sexpr with
  | ScmSymbol(x), ScmPair(to_set,ScmNil) -> ScmSet(ScmVar(x), tag_parse_expression(to_set))
  | ScmSymbol(x), to_set -> ScmSet(ScmVar(x), tag_parse_expression(to_set))
  | _-> raise (X_syntax_error (sexpr, "Expected variable on LHS of set!"))

and lambda_exp args body= 
  (*calculate the body first *)
  let b = lambda_body body in
  match args with
    | ScmNil -> ScmLambdaSimple([],b)
    (*if its lambda a *something* *)
    | ScmSymbol(e)  -> ScmLambdaOpt([],e,b)
    (*else check for the lamba type *)
    | ScmPair(sexpr,sexprs) -> (*check what type of lambda *need to chnge the func name* *)(let lambda = is_simple sexprs in
      (*check for the last element the fund gives and we know the type if lambda *)
      match lambda with
      | ScmNil -> ScmLambdaSimple((lambda_args args) , b)
      | ScmSymbol(e) -> ScmLambdaOpt((lambda_args args),e,b)
      |_ -> raise (X_syntax_error (lambda, "Sexpr structure not recognized")))
    | _ -> raise (X_syntax_error (args, "Sexpr structure not recognized"))
      
    (*two type of lambda's body hence we check *)
and lambda_body body = 
  match body with
  | ScmPair(sexpr,ScmNil) -> tag_parse_expression sexpr
  | _-> ScmSeq(par_to_array body tag_parse_expression)
  


 and begin_fun sexpr =
    match sexpr with
    | ScmPair(sexpr,ScmNil) -> tag_parse_expression sexpr
    | _-> ScmSeq(to_list_scm2 sexpr)
   


(*if the last element is ScmNil return it else its need to be Symbole so retun it *)
and is_simple pairs = 
  match pairs with
  | ScmPair(e1,e2) -> is_simple(e2)
  | ScmNil -> ScmNil
  | ScmSymbol(e) -> ScmSymbol(e)
  | _ -> raise (X_syntax_error (pairs, "Sexpr structure not recognized"))


(*args func *)
and lambda_args args =
 match args with
 | ScmPair(ScmSymbol(e),sexprs) -> e::(lambda_args sexprs)
 | ScmNil->[]
 | ScmSymbol(e) -> []
 | _ -> raise (X_syntax_error (args, "Sexpr structure not recognized"))


 and define_exp vars vals sexpr=
  match vars,vals with
    | ScmSymbol(e), (ScmPair(vals,ScmNil))-> if List.mem e ["define"] then raise (X_syntax_error (sexpr, "Expected variable on LHS of define")) else ScmDef(ScmVar e , tag_parse_expression vals)
    | ScmSymbol(e), vals -> if List.mem e ["define"] then raise (X_syntax_error (sexpr, "Expected variable on LHS of define")) else ScmDef(ScmVar e , tag_parse_expression vals)
    | ScmPair(ScmSymbol v,a),_ -> ScmDef (ScmVar v, tag_parse_expression (ScmPair(ScmSymbol "lambda",ScmPair(a,vals))))
    | _,_ -> raise (X_syntax_error (sexpr, "Expected variable on LHS of define"))


  and wrap_seq sexpr = 
    if (scm_list_length sexpr) > 1 then ScmSeq((to_list_scm sexpr)) else (tag_parse_expression sexpr)

 

and par_fold_right pairs func init  =
  match pairs with
  | ScmPair(sexpr,sexprs) -> func (par_fold_right sexprs func init) sexpr
  | _ -> init 
  



and par_to_array pairs func = 
  (par_fold_right pairs (fun arr a -> (func a) :: arr) [])
  
and if_exp e = 
  match e with
  | ScmPair(e,ScmNil) -> tag_parse_expression e
  | ScmNil -> ScmConst ScmVoid
  | e -> raise X_proper_list_error
  and macro_expand sexpr =
  match sexpr with
  | ScmPair(ScmSymbol "cond",expr) -> ribs_exp expr
  | ScmPair(ScmSymbol "and", exprs) -> and_exp exprs
  | ScmPair(ScmSymbol "let", ScmPair(ScmPair(ScmNil,ScmNil), body)) -> ScmPair(ScmSymbol "lambda",ScmPair(ScmNil,body))
  | ScmPair(ScmSymbol "let", ScmPair(ribs,body)) -> expand_let ribs body
  | ScmPair(ScmSymbol "let*", ScmPair(ribs,body)) -> expand_let_star ribs body
  | ScmPair(ScmSymbol "letrec", ScmPair(ribs,body)) -> expand_let_rec ribs body
  | ScmPair(ScmSymbol "quasiquote",sexpr) -> (
    match sexpr with
    | ScmPair(expr,ScmNil) -> expand_quasiquote expr
    | expr -> expand_quasiquote expr
  )
  (* Handle macro expansion patterns here *)
    | _ -> sexpr


  and and_exp exprs =
  match exprs with
  | ScmNil -> ScmBoolean true 
  | ScmPair(e, ScmNil) -> e
  | ScmPair(e1, e2) -> ScmPair(ScmSymbol "if", ScmPair(e1, ScmPair ((and_exp e2) , ScmPair (ScmBoolean false, ScmNil ))))
  | _-> raise X_proper_list_error


    and ribs_exp ribs =
    match ribs with
    | ScmPair(ScmNil, ScmNil)-> ScmVoid
    | ScmNil -> ScmVoid
    | ScmPair(ScmPair(ScmSymbol "else", ScmNil), ribs) -> raise (X_syntax_error (ribs, "syntax error"))
    (* first case (the common form)*)
    | ScmPair(ScmPair(ScmSymbol "else", ScmPair(expr,ScmNil)), ribs) ->  macro_expand expr
    | ScmPair(ScmPair(ScmSymbol "else", exprs), ribs) ->  (ScmPair(ScmSymbol "begin", macro_expand exprs))
    (* arrow form *)
    | ScmPair(ScmPair(expr, ScmPair(ScmSymbol "=>", expr_f)) , ScmNil) -> create_let expr expr_f ScmNil
    | ScmPair(ScmPair(expr, ScmPair(ScmSymbol "=>", expr_f)) , rest_ribs) -> cond_arrow expr expr_f rest_ribs
    | ScmPair(ScmPair(expr, ScmPair(e1,ScmNil)) , ScmNil) -> ScmPair(ScmSymbol "if", ScmPair((macro_expand expr), ScmPair ((macro_expand e1), ScmNil)))
    | ScmPair(ScmPair(expr, exprs) , ScmNil) -> ScmPair(ScmSymbol "if", ScmPair((macro_expand expr), ScmPair ((ScmPair (ScmSymbol "begin", (macro_expand exprs))), ScmNil)))
    | ScmPair(ScmPair(expr, ScmPair(e1,ScmNil)) , rest)->  ScmPair(ScmSymbol "if", ScmPair(macro_expand expr, ScmPair(macro_expand e1, ScmPair(ribs_exp rest, ScmNil))))
    | ScmPair(ScmPair(expr, exprs) , rest)->  ScmPair(ScmSymbol "if", ScmPair(macro_expand expr, ScmPair((ScmPair (ScmSymbol "begin", macro_expand exprs)), ScmPair(ribs_exp rest, ScmNil))))
    | _-> raise X_proper_list_error


     and cond_arrow value f rest =
    let f = match f with
    | ScmPair(_,_) -> f
    | _-> raise (X_syntax_error( f , "f must be a function")) in
    let re = ribs_exp rest in
    let vali = (ScmPair(ScmSymbol "value",ScmPair(value,ScmNil))) in
    let foo = ScmPair(ScmSymbol "f",ScmPair(ScmPair(ScmSymbol "lambda",ScmPair(ScmNil,f)),ScmNil)) in
    let re = ScmPair(ScmSymbol "rest",ScmPair(ScmPair(ScmSymbol "lambda",ScmPair(ScmNil,ScmPair(re,ScmNil))),ScmNil)) in
    let ribs = ScmPair(vali,ScmPair(foo,ScmPair(re,ScmNil))) in
    let body = ScmPair(ScmPair(ScmSymbol "if",ScmPair(ScmSymbol "value",ScmPair(ScmPair
               (ScmPair (ScmSymbol "f", ScmNil),
             ScmPair (ScmSymbol "value", ScmNil)),
           ScmPair (ScmPair (ScmSymbol "rest", ScmNil), ScmNil)))),
     ScmNil) in
    macro_expand (ScmPair(ScmSymbol "let",ScmPair (ribs,body)))


    and expand_quasiquote sexpr=
    match sexpr with
    | ScmNil -> ScmPair(ScmSymbol "quote", ScmPair(ScmNil,ScmNil))
    | ScmPair(ScmSymbol "unquote", ScmPair(exp,ScmNil)) -> exp 
    | ScmPair(ScmSymbol "unquote-splicing", ScmPair(exp,ScmNil)) when (scm_is_list exp)-> ScmPair (ScmSymbol "quote", (ScmPair (sexpr, ScmNil))) 
    | ScmPair(ScmPair(ScmSymbol "unquote-splicing", ScmPair(exp, ScmNil)), rest) -> ScmPair(ScmSymbol "append", ScmPair(exp, ScmPair( (expand_quasiquote rest), ScmNil)))
    | ScmPair(exp, ScmPair(ScmSymbol "unquote-splicing", ScmPair(sexp, ScmNil))) -> ScmPair(ScmSymbol "cons", ScmPair((expand_quasiquote exp), ScmPair(sexp, ScmNil)))
    | ScmPair(first,rest) -> ScmPair(ScmSymbol "cons", ScmPair((expand_quasiquote first), ScmPair((expand_quasiquote rest), ScmNil)))
    | ScmVector x -> (ScmPair(ScmSymbol "list->vector" , ScmPair (expand_quasiquote (list_to_proper_list x), ScmNil)))
    | x -> ScmPair(ScmSymbol "quote", ScmPair(x, ScmNil))


      
  (* (let ((value <expr>)
      (f (lambda () <exprf>))
      (rest (lambda () <cont-ribs>)))
    (if value
        ((f) value)
        (rest))) *)    
  and create_let value f rest =
    ScmPair(ScmSymbol "let", ScmPair(ScmPair(ScmPair(ScmSymbol "value",value), ScmPair(ScmPair(ScmSymbol "f", create_lambda f), ScmPair(ScmSymbol "rest", ScmPair(create_lambda rest, ScmNil)))), (ScmPair(ScmSymbol "if", ScmPair (value, ScmPair(ScmPair(f, ScmNil), ScmPair(value, ScmPair(rest, ScmNil))))))) )
      
  and create_lambda body =
    ScmPair(ScmSymbol "lambda", ScmPair(ScmNil, ScmPair(body, ScmNil)))
and more_match sexpr = 
match sexpr with
| ScmPair(e1,ScmNil)-> e1
| e -> ScmPair(ScmSymbol "begin",e)

  
  
and need_wrap sexpr =
match sexpr with
  | ScmNil -> false 
  | ScmPair(_,ScmNil) -> false
  |ScmPair(_,ScmPair(_,_)) -> true
  |ScmPair (_,_) -> true
  |_->false
  

and let_args args = 
let args = match args with
  | ScmNil -> ScmNil
  | ScmPair(ScmPair(var,exp),rest) -> ScmPair(var,let_args rest)
  | e -> raise X_proper_list_error in
  args


and let_exprs exprs = 
match exprs with
| ScmNil -> ScmNil
| ScmPair(ScmPair(var,exp), ScmNil) -> exp
| ScmPair(ScmPair(var,exp),rest) ->  scm_append exp (let_exprs rest)
| e -> raise X_proper_list_error 

and check_diff args =
  match args with
  | [] -> true
  | hd::[] -> true
  | hd::rest -> if List.mem hd rest then false
    else check_diff rest 

  
and expand_let ribs body =
    let args = let_args ribs in
    let exprs = let_exprs ribs in
    if (check_diff (scm_list_to_list args)) = false then raise (X_syntax_error(ScmPair(ribs,body), "vals must be diffrent")) else
    if(scm_list_length args) = (scm_list_length exprs) then ScmPair(ScmPair(ScmSymbol "lambda",ScmPair(let_args ribs,body)),let_exprs ribs) 
    else 
    raise (X_syntax_error(ScmPair(ribs,body), "args and exprs must be in the same length"))



  
and expand_let_star ribs body =  
  match ribs with
  | ScmNil -> macro_expand (ScmPair(ScmSymbol "let",ScmPair(ScmNil, body)))
  | ScmPair(expr,ScmNil) -> macro_expand (ScmPair(ScmSymbol "let",ScmPair(ribs, body)))
  | ScmPair(expr,rest) -> macro_expand (ScmPair(ScmSymbol "let",ScmPair(ScmPair(expr,ScmNil),(ScmPair(expand_let_star rest body,ScmNil)))))
  | e -> raise X_proper_list_error 

and let_rec_what_ever ribs =  
match ribs with
| ScmNil -> ScmNil
| ScmPair(ScmPair(var,exp),rest) -> ScmPair(ScmPair(var,(ScmPair(ScmPair(ScmSymbol "quote", ScmPair(ScmSymbol "whatever", ScmNil)),ScmNil))),let_rec_what_ever rest) 
| e -> raise X_proper_list_error 

and let_rec_set_exprs exprs body = 
match exprs with
| ScmNil -> body
| ScmPair(ScmPair(var,exp),rest) ->  ScmPair(ScmPair(ScmSymbol "set!",ScmPair(var,exp)),let_rec_set_exprs rest body)
| e -> raise X_proper_list_error 


 and expand_let_rec ribs body =
  let whatever = let_rec_what_ever ribs in
  let exprs = let_rec_set_exprs ribs body in
  macro_expand (ScmPair(ScmSymbol "let",ScmPair(whatever,exprs)))
   (*end*)

end;; 

