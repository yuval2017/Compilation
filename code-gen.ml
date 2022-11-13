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
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string
end;;


exception X_Not_Found_error of sexpr * string;;
module Code_Gen : CODE_GEN = struct


let rec fvar_offset sexpr list =    
  match list with    
  | [] -> raise X_this_should_not_happen
  | (s,i)::rest -> if sexpr = s then i else fvar_offset sexpr rest  

let rec const_offset sexpr list =    
  match list with    
  | [] -> raise (X_Not_Found_error (sexpr, "this sexpr not found"))
  | (c,(i,s))::rest -> if sexpr_eq c sexpr then i else const_offset sexpr rest  


  let rec is_member list sexpr = 
    match list with
    | [] -> false
    | e::rest -> if  expr'_eq (ScmConst'(e)) (ScmConst'(sexpr)) then true else is_member rest sexpr


  let rec remove_duplicates list correct_sexpr_list = 
    match list with
    | [] -> correct_sexpr_list
    | y::rest -> if (is_member correct_sexpr_list y ) then remove_duplicates rest correct_sexpr_list 
    else remove_duplicates rest (correct_sexpr_list@[y])




let scan_ast asts = 
      let rec extract_constants_with_set expr' list=      
       match expr' with
        | ScmConst'(e) -> if is_member list e then list else e::list
        | ScmVar'(_) -> list
        | ScmBox'(_) -> list
        | ScmBoxGet'(_) -> list
        | ScmBoxSet' (var,expr') -> extract_constants_with_set expr' list
        | ScmIf'(test,dit,dif) -> extract_constants_with_set test (extract_constants_with_set dit (extract_constants_with_set dif list))
        | ScmSeq' (e) -> List.fold_left (fun acc x -> extract_constants_with_set x acc) list e
        | ScmSet'(var,expr') -> extract_constants_with_set expr' list
        | ScmDef'(var,expr') -> extract_constants_with_set expr' list
        | ScmOr'(e) -> List.fold_left (fun acc x -> extract_constants_with_set x acc) list e
        | ScmLambdaSimple'(args,expr') -> extract_constants_with_set expr' list
        | ScmLambdaOpt'(args,arg,expr') -> extract_constants_with_set expr' list
        | ScmApplic'(app,rands) -> List.fold_left (fun acc x -> extract_constants_with_set x acc) (extract_constants_with_set app list) rands
        | ScmApplicTP'(app,rands) -> List.fold_left (fun acc x -> extract_constants_with_set x acc) (extract_constants_with_set app list) rands
      in
      List.rev (List.fold_left (fun acc expr' -> extract_constants_with_set expr' acc)  [] asts)

    
       


    let expand_list_to_sub_constants list_exprs = 
      let rec expand_list sexpr new_list= 
        match sexpr with
        | ScmSymbol(e) -> new_list@[ScmString(e)] 
        | ScmPair(e1,e2) ->  (expand_list e2 ((expand_list e1 new_list)@[e1]))@[e2]
        | ScmVector(e) ->(List.fold_left (fun acc x -> expand_list x acc) new_list e)@[sexpr]
        | _-> new_list@[sexpr]
      in
      [ScmVoid;ScmNil;(ScmBoolean false);(ScmBoolean true)]@(remove_duplicates  (List.fold_left (fun acc sexpr -> match sexpr with
      | ScmVoid -> acc 
      | ScmNil -> acc
      | ScmBoolean(_) -> acc
      | _ -> (expand_list sexpr acc)@[sexpr]) [] list_exprs) [])

         
let generate_offsets list_sexpr  =
  let rec run list_sexpr counter table = 
  match list_sexpr with     
    | [] -> table
    | sexpr::rest -> (match sexpr with
      | ScmVoid -> run rest (counter + 1) (table@[(sexpr,(counter , "\tMAKE_VOID"))])
      | ScmNil -> run rest (counter + 1) (table@[(sexpr,(counter, "\tMAKE_NIL"))])
      | ScmBoolean(e) -> (match e with
        | true -> run rest (counter + 2) (table@[(sexpr,(counter,"\tMAKE_LITERAL_BOOL(1)"))])
        | false -> run rest (counter + 2) (table@[(sexpr,(counter,"\tMAKE_LITERAL_BOOL(0)"))]))
      | ScmChar(e) -> run rest (counter + 2) (table@[(sexpr,(counter, "\tMAKE_LITERAL_CHAR("^(string_of_int(int_of_char e))^")"))])
      | ScmString(e) -> run rest (counter + String.length(e) + 8 + 1) (table@[(sexpr,(counter ,("\tMAKE_LITERAL_STRING \""^e^"\"")))])
      | ScmSymbol(e) -> run rest (counter + 9) (table@[(sexpr,(counter,"\tMAKE_LITERAL_SYMBOL(const_tbl + "^string_of_int (const_offset (ScmString(e)) table)^")"))])
      | ScmNumber(e) -> ( match e with
        | ScmRational(num,den) -> run rest (counter + 17) (table@[(sexpr,(counter,"\tMAKE_LITERAL_RATIONAL("^string_of_int(num)^"," ^string_of_int(den)^")"))])
        | ScmReal(f) -> run rest (counter + 9) (table@[(sexpr,(counter,"\tMAKE_LITERAL_FLOAT("^string_of_float(f)^")"))]))
      | ScmVector(e) ->     
        let rec make_str e = 
          (match e with
          | [] -> ""
          | hd::[] ->  "const_tbl + " ^ (string_of_int (const_offset hd table))
          | hd::rest -> "const_tbl + " ^ ((string_of_int (const_offset hd table))^","^ (make_str rest)))
      in
        run rest (counter + 1 + 8 + 8*List.length(e)) (table@[(sexpr,(counter,"\tMAKE_LITERAL_VECTOR "^(make_str e)))])
      | ScmPair(e1,e2) -> (run rest (counter + 1 + 8 + 8)) (table@[(sexpr,(counter, "\tMAKE_LITERAL_PAIR(const_tbl + "^string_of_int (const_offset e1 table)^",const_tbl + "^string_of_int (const_offset e2 table)^")"))]))
in
run list_sexpr 0 []

  let make_consts_tbl asts = generate_offsets (expand_list_to_sub_constants (scan_ast asts))




    let make_fvars_tbl asts =
    let rec run expr' list =
      match expr' with     
    | ScmConst'(_) ->  list 
    | ScmVar'(e) -> (match e with
      | VarFree(str) ->if List.mem str (List.map (fun (e,index) -> e) list) then list else let index = List.length list in list@[(str, index)]
      |_-> list)
    | ScmBox'(_) -> list
    | ScmBoxGet'(_) -> list
    | ScmBoxSet' (var,expr') -> run (ScmVar' var) (run expr' list)
    | ScmIf'(test,dit,dif) -> run test (run dit (run  dif list))
    | ScmSeq' (e) -> List.fold_left (fun acc x -> run x acc) list e
    | ScmSet'(var,expr') -> run (ScmVar' var) (run expr' list)
    | ScmDef'(var,expr') -> run (ScmVar' var) (run expr' list)
    | ScmOr'(e) -> List.fold_left (fun acc x -> run x acc) list e
    | ScmLambdaSimple'(args,expr') -> run expr' list
    | ScmLambdaOpt'(args,arg,expr') -> run expr' list
    | ScmApplic'(app,rands) -> run app (List.fold_left (fun acc x -> run x acc) list rands)
    | ScmApplicTP'(app,rands) -> run app (List.fold_left (fun acc x -> run x acc) list rands)
    in
    let ans = List.fold_left (fun acc x -> run x acc) [("boolean?",0); ("flonum?",1); ("rational?",2);
                                              ("pair?",3); ("null?",4); ("char?",5); ("string?",6);
                                              ("procedure?",7); ("symbol?",8);
                                              ("string-length",9); ("string-ref",10); ("string-set!",11);
                                              ("make-string",12); ("symbol->string",13);
                                              ("char->integer",14); ("integer->char",15); ("exact->inexact",16);
                                              ("eq?",17);
                                              ("+",18); ("*",19); ("/",20); ("=",21); ("<",22);
                                              ("numerator",23); ("denominator",24); ("gcd",25);
                                              ("car",26);("cdr",27);("set-car!",28);("set-cdr!",29);("cons",30);("apply",31)] asts

  in
  List.map (fun x -> match x with
  | (x1,x2) -> (x1,x2*8)) ans


  let mov_qword left right dir = 
    match dir with
    | true -> "\tmov qword["^right^"] , " ^ left ^"\n"
    | false -> "\tmov " ^ left ^ ", qword["^right^"] \n"

  let or_exit = ref 0
  let generete_exit = 
    fun _ ->(or_exit := !or_exit + 1);  string_of_int (!or_exit)
  let l_code = ref 0
  let generate_Lcode = 
    fun _ ->(l_code := !l_code + 1);  string_of_int (!l_code)
  
    
let generate consts fvars e = 
  let rec run e dep = 
      match e with
      | ScmConst'(c) -> "\tmov rax,const_tbl + " ^ string_of_int (const_offset c consts) ^ "\n"
      | ScmVar'(v) -> (match v with
        | VarParam(_,minor) -> (mov_qword "rax" ("rbp + 8 * (4 + "^(string_of_int minor)^ ")") false)
        | VarBound(_,major,minor) -> ((mov_qword "rax" ("rbp+8*2") false) ^ (mov_qword "rax" ("rax+8*" ^ (string_of_int major)) false)  ^ (mov_qword "rax" ("rax+8*" ^ (string_of_int minor)) false)) 
        | VarFree (b) -> (mov_qword "rax" ("fvar_tbl + " ^ (string_of_int ((fvar_offset b fvars)))) false) 
        )
      | ScmDef'(v,expr') -> let str = run expr' dep in  (match v with      
        | VarFree (b) -> str ^ (mov_qword "rax" ("fvar_tbl + " ^ (string_of_int ((fvar_offset b fvars)))) true) ^ "\tmov rax, " ^ sob_void ^ "\n"
        |_->raise X_this_should_not_happen
        )
      | ScmSet'(v,expr') -> let str = run expr' dep in  (match v with
        | VarParam(_,minor) ->  str^(mov_qword "rax" ("rbp + 8 * (4 + "^(string_of_int minor)^ ")") true) ^ "\tmov rax, " ^ sob_void ^ "\n"
        | VarBound(_,major,minor) -> str ^ ((mov_qword "rbx" ("rbp+8*2") false) ^ (mov_qword "rbx" ("rbx+8*" ^ (string_of_int major)) false)  ^ (mov_qword "rax" ("rbx+8*" ^ (string_of_int minor)) true)) ^ "\tmov rax, " ^ sob_void ^ "\n"
        | VarFree (b) -> str ^ (mov_qword "rax" ("fvar_tbl + " ^ (string_of_int (fvar_offset b fvars))) true) ^ "\tmov rax, " ^ sob_void ^ "\n"
        )
      | ScmSeq'(e) -> List.fold_left (fun acc x -> acc^(run x dep)) "" e
      | ScmOr'(e) -> (let ex = generete_exit() in 
        let rec fold_except_last e  =  (match e with
          | [] -> ""
          | expr::[] -> (run expr dep)^"Lexit"^ex^":\n"
          | expr::rest -> ((run expr dep)^"\tcmp rax, SOB_FALSE_ADDRESS\n\tjne Lexit"^ex^"\n") ^ (fold_except_last rest))
      in
      fold_except_last e)
      | ScmIf'(test,dit,dif) -> let ex = generete_exit() in
        ((run test dep)^"\tcmp rax, SOB_FALSE_ADDRESS\n\tje Lelse"^ex^"\n") ^ ((run dit dep)^"\tjmp Lexit"^ex^"\n\tLelse" ^ex^":\n") ^ ((run dif dep)^"\tLexit" ^ex^ ":\n")
      | ScmBoxGet'(v) -> (run (ScmVar'(v)) dep)^(mov_qword "rax" "rax" false)
      | ScmBoxSet'(v,expr) ->((run expr dep)^"\tpush rax\n")^ (run (ScmVar'(v)) dep)^"\tpop qword[rax]\n\tmov rax, SOB_VOID_ADDRESS\n"
      | ScmLambdaSimple'(args,body) -> genarete_lambda args "" false body dep
      | ScmLambdaOpt'(args,arg,body) -> genarete_lambda args arg true body dep
      | ScmApplic'(app,params) -> genarete_applic app params dep
      | ScmApplicTP'(app,params)-> genarete_applicTP app params dep
      | ScmBox'(e) -> (match e with
      | VarParam(_,minor) -> "  \tMALLOC rax,WORD_SIZE\n\tmov rdx,qword[rbp+WORD_SIZE*(4+"^(string_of_int minor)^")]\n\tmov qword[rax], rdx\n"
                                | _ -> raise X_this_should_not_happen)
      
    and sob_void = "SOB_VOID_ADDRESS"
    and genarete_lambda args opt is_opt body dep = 
      let l_code = generate_Lcode() in
      match dep with
      | 0 -> "\tMAKE_CLOSURE(rax, SOB_NIL_ADDRESS, Lcode"^l_code^")\n\tjmp Lcont"^l_code^"\n\tLcode"^l_code^":\n\tpush rbp\n\tmov rbp,rsp\n\t"^ (add_adjustment args l_code is_opt body dep)
      | d -> "\tmov rbx, qword[rbp +WORD_SIZE*2] ;pointer to Env
              \tmov rax, "^(string_of_int ((d+1)*8))^"
              \tMALLOC rax,rax ;rax hold's pointer to major vector
              \tmov rbx,qword[rbp+WORD_SIZE*2]        ;env pointer
              \tmov r8, rax ;r8 = NewEnv
              \tadd rax, WORD_SIZE ; NewEnv[1]
              \tcmp rbx,SOB_NIL_ADDRESS
              \tje AddDummy"^l_code^"


              \tmov rcx,"^(string_of_int d)^"
              \tExtend"^l_code^":
              \tmov rdx, qword[rbx]       ;rdx = Env[i]
              \tmov qword[rax],rdx        ; ExtEnv[i+1] = Env[i]
              \tadd rbx, WORD_SIZE
              \tadd rax, WORD_SIZE
              \tloop Extend"^l_code^"
              \tAddDummy"^l_code^":
              \tmov qword[rax], SOB_NIL_ADDRESS

              \tmov rax, qword[rbp+WORD_SIZE*3]     ; rax = argc
              \tshl rax, 3
              \tmov rbx, rax
              \tMALLOC rbx, rbx ; create minor vector
              \tmov rax, r8
              \tmov qword[rax], rbx     ;ExtEnv[0] = minor vector


              \tmov rdx, rbp
              \tadd rdx, 32     ; *rdx = params
              \tmov rcx, qword[rbp+WORD_SIZE*3]     ;rcx = argc 
              \tmov r8, rax
              \tcmp rcx, 0
              \tje Continue"^l_code^"  
              \tAddParams"^l_code^":
              \tmov rax, qword[rdx]       ; rax = param[i]
              \tmov qword[rbx],rax      ;ExtEnv[0][i] = param[i]
              \tadd rbx, WORD_SIZE
              \tadd rdx, WORD_SIZE
              \tloop AddParams"^l_code^"  
              \tContinue"^l_code^": 
              \tmov rbx, r8     ; rbx = *ExtEnv 
              \tMAKE_CLOSURE(rax, rbx, Lcode"^l_code^")
              \tjmp Lcont"^l_code^"
              Lcode"^l_code^":
              \tpush rbp
              \tmov rbp, rsp\n
              "

              ^add_adjustment args l_code is_opt body dep

              and add_adjustment args l_code is_opt body dep = 
              (match is_opt with
              | false -> 
              "" 
              | true ->
              let n = (List.length(args)) + 1 in
              "
              \tcmp qword[rbp+8*3], "^(string_of_int n)^"
              \tjae Contract"^l_code^"

              Expand"^l_code^":
              \tmov rcx, 0
              \tmov rdx, [rbp +WORD_SIZE*3]
              \tadd rdx, 4
              ShiftStackDown"^l_code^":
              \tmov rbx,qword[rbp+WORD_SIZE*rcx]
              \tmov qword[rbp+WORD_SIZE*(rcx-1)],rbx
              \tdec rdx
              \tinc rcx
              \tcmp rdx, 0
              \tjne ShiftStackDown"^l_code^"
              \tsub rbp, WORD_SIZE
              \tmov qword[rbp+WORD_SIZE*3], "^(string_of_int n)^"
              \tmov qword[rbp+WORD_SIZE*("^string_of_int (n+3)^")],SOB_NIL_ADDRESS
              \tmov rsp, rbp

              \tjmp Exit"^l_code^"

              Contract"^l_code^":
              \tmov rbx,qword[rbp+WORD_SIZE*3]    
              \tmov r14,SOB_NIL_ADDRESS
              \tmov rcx, rbx
              \tsub rcx, "^(string_of_int (n-1))^"
               

              \tMakePotsList"^l_code^":
              \tdec rbx
              \tmov rdx,r14
              \tmov rax,PVAR(rbx)
              \tMAKE_PAIR (r14, rax,rdx)
              \tloop MakePotsList"^l_code^"

              \tmov rcx, "^(string_of_int (n+3))^"
              \tmov rdx, qword[rbp+WORD_SIZE*3] 
              \tsub rdx, "^(string_of_int n)^"
              
              ShiftStack"^l_code^":
              \tmov rbx,qword[rbp+WORD_SIZE*(rcx-1)]
              \tadd rcx,rdx
              \tmov qword[rbp+WORD_SIZE*(rcx-1)],rbx
              \tsub rcx,rdx
              \tloop ShiftStack"^l_code^"


              \tshl rdx,3
              \tadd rbp,rdx
              \tmov qword[rbp+WORD_SIZE*3],"^(string_of_int n)^"
              \tmov qword[rbp+WORD_SIZE*(4+"^(string_of_int (n-1))^")],r14
              \tmov rsp,rbp

              Exit"^l_code^":\n
              " 

              )^(run body (dep + 1))^"
              
              \tleave
              \tret
              Lcont"^l_code^":\n"


              and genarete_applic app params dep = 
                let n = List.length(params) in
                (List.fold_right(fun x acc -> acc^(run x dep)^"\tpush rax \n")  params "")^"
                \tpush "^(string_of_int n)^"\n"^
                (run app dep)^"
                \tpush qword[rax+TYPE_SIZE]
                \tcall qword[rax+TYPE_SIZE+WORD_SIZE]
                \tadd rsp,8
                \tpop rbx
                \tshl rbx, 3
                \tadd rsp,rbx\n"

            and genarete_applicTP app params dep = 
                let l_code = generate_Lcode() in
                let n = List.length(params) in 
                "\n\t"^(List.fold_right(fun x acc -> acc^(run x dep)^"\tpush rax \n")  params "")^"
                \tpush "^(string_of_int n)^"\n"^
                (run app dep)^"
    
                \tpush qword[rax + TYPE_SIZE]
                \tpush qword[rbp + 1*WORD_SIZE]
                \tmov r8, qword[rbp +  3*WORD_SIZE]   
                \tadd r8, 4 
                \tshl r8, 3 
                \tadd r8, rbp 

                \tmov rdx, rbp 
                \tmov rbp, qword[rbp]
                

                DuplicateFrame"^l_code^":
                \tsub rdx, WORD_SIZE
                \tsub r8, WORD_SIZE               
                \tmov rcx, qword[rdx]
                \tmov qword[r8], rcx
                \tcmp rdx, rsp
                \tjne DuplicateFrame"^l_code^"

                \tmov rsp, r8
                \tjmp qword[rax+TYPE_SIZE+WORD_SIZE]\n"


    in
  
run e 0

      

end;;

