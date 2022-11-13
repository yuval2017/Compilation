(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

#use "tag-parser.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type var' = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | ScmConst' of sexpr
  | ScmVar' of var'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmSet' of var' * expr'
  | ScmDef' of var' * expr'
  | ScmOr' of expr' list
  | ScmLambdaSimple' of string list * expr'
  | ScmLambdaOpt' of string list * string * expr'
  | ScmApplic' of expr' * (expr' list)
  | ScmApplicTP' of expr' * (expr' list);;

let rec get_var_name var = 
  match var with
  | VarFree (name) -> name
  | VarBound (name, major1, minor1) -> name
  | VarParam (name,_) -> name
let var_eq v1 v2 =
match v1, v2 with
  | VarFree (name1), VarFree (name2) -> String.equal name1 name2
  | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
    major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
  | VarParam (name1, index1), VarParam (name2, index2) ->
       index1 = index2 && (String.equal name1 name2)
  | _ -> false
  
  
let rec expr'_eq e1 e2 =
  match e1, e2 with
  | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
  | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                            (expr'_eq dit1 dit2) &&
                                              (expr'_eq dif1 dif2)
  | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
        List.for_all2 expr'_eq exprs1 exprs2
  | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
        (var_eq var1 var2) && (expr'_eq val1 val2)
  | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
     (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
      (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
  | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
  | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
  | _ -> false;;


module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val run_semantics : expr -> expr'
end;; (* end of module type SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct



  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

  let tag_lexical_address_for_var name params env = 
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> VarFree name
        | Some(major, minor) -> VarBound(name, major, minor))
    | Some minor -> VarParam(name, minor);;

  (* run this first! *)
  let annotate_lexical_addresses pe = 
   let rec run pe params env =
      match pe with  
      | ScmConst(e) -> ScmConst'(e)
      | ScmVar(e)-> ScmVar'(tag_lexical_address_for_var e params env)
      | ScmIf(test,dit,dif) -> ScmIf'(run test params env,run dit params env, run dif params env)
      | ScmOr(e) -> ScmOr'(List.map (fun x -> run x params env) e) 
      | ScmSeq(e) -> ScmSeq'(List.map (fun x -> run x params env) e) 
      | ScmLambdaSimple(pars,body) -> ScmLambdaSimple'(pars,(run body pars (params::env)))
      | ScmLambdaOpt(pars,par,body) -> ScmLambdaOpt'(pars,par,run body (pars@[par]) (params::env))
      | ScmDef(v,e) -> (match v with
        | ScmVar(var) -> ScmDef'(tag_lexical_address_for_var var params env , run e params env)
        | _-> raise X_this_should_not_happen
      )
      | ScmSet(v,e) -> (match v with
      | ScmVar(var) -> ScmSet'(tag_lexical_address_for_var var params env , run e params env)
      | _-> raise X_this_should_not_happen
      )
      | ScmApplic(app,exprs) -> ScmApplic'(run app params env, List.map (fun x -> run x params env) exprs)
      

   in 
   run pe [] [];;
   

  let rec rdc_rac s =
    match s with
    | [e] -> ([], e)
    | e :: s ->
       let (rdc, rac) = rdc_rac s
       in (e :: rdc, rac)
    | _ -> raise X_this_should_not_happen;;
  

  let annotate_tail_calls pe =
    let rec run pe in_tail =
      match pe with
        | ScmConst'(e) -> pe
        | ScmVar'(e) -> pe
        | ScmIf'(test,dit,dif) -> ScmIf'(run test false, run dit in_tail, (run dif in_tail))
        | ScmOr'(e) -> ScmOr'(wrap_last e in_tail)
        | ScmSeq'(e) -> ScmSeq'(wrap_last e in_tail)
        | ScmLambdaSimple'(params,body) -> ScmLambdaSimple'(params, (run body true))
        | ScmLambdaOpt' (pars,par,body) -> ScmLambdaOpt' (pars,par,(run body true))
        | ScmDef'(v,expr') -> ScmDef'(v,run expr' false)
        | ScmSet'(v,expr') -> ScmSet'(v,run expr' false)
        | ScmApplic'(app,exprs') -> if in_tail then ScmApplicTP'(run app false, List.map (fun x -> run x false) exprs') 
          else ScmApplic'(run app false, List.map (fun x -> run x false) exprs')
        | _-> raise X_not_yet_implemented 
        
    and wrap_last e in_tail =
      match e with
        |  expr::[] -> [run expr in_tail]
        |  expr::exps -> (run expr false)::(wrap_last exps in_tail) 
        |  [] -> []



   in 
   run pe false;;

   


  let append list1 list2 =
    match list1,list2 with
    | [list1x,list1y],[list2x,list2y] -> [list1x@list2x,list1y@list2y] 
    | _-> raise X_this_should_not_happen 
  let check_eq_vars var name = 
    get_var_name var = name
let find_reads name enclosing_lambda expr = 
  let empty = [[],[]]
in
  let rec run name enclosing_lambda expr read_write need_deeper = 
    match expr with
    | ScmConst'(e) -> read_write
    | ScmVar'(var) -> if check_eq_vars var name then append read_write [[enclosing_lambda],[]]  else read_write
    | ScmIf'(test,dit,dif) -> append read_write (append (append (run name enclosing_lambda test empty need_deeper) (run name enclosing_lambda dit empty need_deeper)) (run name enclosing_lambda dif empty need_deeper))
    | ScmOr'(e) -> append read_write (List.fold_left (fun acc x -> append  (run name enclosing_lambda x empty need_deeper) acc) empty e) 
    | ScmSeq'(e) -> append read_write (List.fold_left (fun acc x -> append (run name enclosing_lambda x empty need_deeper) acc ) empty e) 
    | ScmLambdaSimple'(args,body) -> if List.mem name args then read_write else if need_deeper then append read_write (run name expr body empty false) else append read_write (run name enclosing_lambda body empty false)
    | ScmLambdaOpt'(args,arg,body) -> if name = arg || List.mem name args then read_write else if need_deeper then append read_write (run name expr body empty false) else append read_write (run name enclosing_lambda body empty false)
    | ScmDef'(v,expr') -> read_write
    | ScmSet'(v,expr') -> if check_eq_vars v name then append read_write (append [[],[enclosing_lambda]] (run name enclosing_lambda expr' empty need_deeper))  else append read_write (run name enclosing_lambda expr' empty need_deeper)
    | ScmApplic'(app,exprs') ->append read_write  (append (run name enclosing_lambda app empty need_deeper) (List.fold_left (fun acc x -> append (run name enclosing_lambda x empty need_deeper) acc) empty exprs' ))
    | ScmApplicTP'(app,exprs') ->append read_write (append (run name enclosing_lambda app empty need_deeper) (List.fold_left (fun acc x -> append (run name enclosing_lambda x empty need_deeper) acc) empty exprs' ))
    | ScmBoxSet'(v,expr') -> append read_write (run name enclosing_lambda expr' empty need_deeper)
    | ScmBox'(_) -> read_write
    | ScmBoxGet'(_) -> read_write
  in
  run name enclosing_lambda expr empty true


let rec box_set expr = 
  match expr with
      | ScmConst'(e) -> expr
      | ScmVar'(var) -> expr
      | ScmIf'(test,dit,dif) -> ScmIf'(box_set test,box_set dit,box_set dif)
      | ScmOr'(e) -> ScmOr'(List.map box_set e)
      | ScmSeq'(e) -> ScmSeq'(List.map box_set e)
      | ScmLambdaSimple'(args,body) -> ScmLambdaSimple'(args, box_set (help_func expr body args))
      | ScmLambdaOpt'(args,arg,body) -> ScmLambdaOpt'(args,arg, box_set (help_func expr body (args@[arg])))
      | ScmDef'(v,expr') -> ScmDef'(v, box_set expr')
      | ScmSet'(v,expr') ->  ScmSet'(v,box_set expr')
      | ScmApplic'(app,exprs') -> ScmApplic'(box_set app, List.map box_set exprs')
      | ScmApplicTP'(app,exprs') -> ScmApplicTP'(box_set app, List.map box_set exprs')
      | ScmBoxSet' (v,expr') -> ScmBoxSet'(v,box_set expr')
      | _-> expr


  and help_func enclosing_lambda body args =
    let args = List.rev args in
    let minor = (List.length args) -1 in
    let rec box_body gets_and_sets body args minor = 
      
      match gets_and_sets, args with 
      | _,[] -> body
      | [_,[]]::rest_args_get_and_sets,_::rest_args -> box_body rest_args_get_and_sets body rest_args (minor - 1)
      | [[],_]::rest_args_get_and_sets,_::rest_args -> box_body rest_args_get_and_sets body rest_args (minor - 1)
      | [args_gets,args_sets]::rest_args_get_and_sets, arg::restargs -> box_body rest_args_get_and_sets (body_change body args_gets args_sets arg minor) restargs (minor-1)
      | _-> raise X_this_should_not_happen
    in 
    box_body (List.map (fun arg -> find_reads arg enclosing_lambda body) args) body args minor

    and body_change body gets sets name minor  = 
       if (List.mem true (List.map (fun x -> check_exist_lambda x sets) gets)) then rewrite_body body name minor else body

    and check_exist_lambda get_lambda lambdas_sets_list =
      match lambdas_sets_list,get_lambda with
      | [],_ -> false
      | set_lambda::_,get_lambda when not (get_lambda == set_lambda) -> true
      | set_lambda::rest,get_lambda -> check_exist_lambda get_lambda rest
    and rewrite_body body name minor= 
      let rec keep_change body name = 
          match body with
              | ScmConst'(e) -> body
              | ScmVar'(var) -> if check_eq_vars var name then ScmBoxGet' (var) else body
              | ScmIf'(test,dit,dif) -> ScmIf'(keep_change test name, keep_change dit name, keep_change dif name)
              | ScmOr'(e) ->ScmOr'( List.map (fun  x -> keep_change x name ) e)
              | ScmSeq'(e) -> ScmSeq'(List.map(fun x -> keep_change x name ) e)
              | ScmLambdaSimple'(args,b) -> if List.mem name args then body else ScmLambdaSimple'(args,keep_change b name)
              | ScmLambdaOpt'(args,arg,b) -> if name = arg || List.mem name args then b else ScmLambdaOpt'(args,arg,keep_change b name)  
              | ScmSet'(v,expr') ->  if check_eq_vars v name then ScmBoxSet'(v, keep_change expr' name) else ScmSet'(v, keep_change expr' name) 
              | ScmApplic'(app,exprs') -> ScmApplic'(keep_change app name, List.map (fun x -> keep_change x name) exprs')
              | ScmApplicTP'(app,exprs') -> ScmApplicTP'(keep_change app name, List.map (fun x -> keep_change x name) exprs')
              | ScmDef'(v,expr') -> body
              | ScmBoxSet'(v,expr') ->  ScmBoxSet'(v, keep_change expr' name) 
              | _-> body
            in
          let add_seq body name = 
            match body with
                (*| ScmSet'(VarParam(_,_ ), ScmBox'(VarParam(_,_))) ->  ScmSeq'(ScmSet'(VarParam(name, minor), ScmBox'(VarParam(name,minor)))::(List.map (fun x -> keep_change x name) e))*)  
            | ScmSeq'(e) -> ScmSeq'(ScmSet'(VarParam(name, minor), ScmBox'(VarParam(name,minor)))::(List.map (fun x -> keep_change x name) e))
            | expr' -> ScmSeq'(ScmSet'(VarParam(name, minor), ScmBox'(VarParam(name,minor)))::[keep_change body name])    
          in
          add_seq body name
          


  let run_semantics expr =
    box_set
      (annotate_tail_calls
         (annotate_lexical_addresses expr))

end;; (* end of module Semantic_Analysis *)
