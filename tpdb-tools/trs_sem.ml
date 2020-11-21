open Format
open Trs_ast

type type_info =
  | Var
  | Function of int ref

exception Sem_error of Lexing.position * string

let error loc msg = raise (Sem_error (loc,msg))

let warning loc msg = 
  eprintf "%a: warning, %s.@." Trs_ast.print_loc loc msg

let ident env (loc,id) =
  try
    match List.assoc id env with
      | Function _ -> env
      | Var -> error loc (id ^ " is a variable")
  with
      Not_found -> (id,Function (ref (-1)))::env

let check_binary env (loc,id) =
  try
    match List.assoc id env with
      | Function x -> 
	  if !x=2 then env
	  else if !x = -1 then begin x:=2; env end
	  else error loc ("bad arity for " ^ id)
      | Var -> error loc (id ^ " is a variable")
  with
      Not_found -> (id,Function (ref 2))::env

let rec term env t = 
  match t with
    | Term((loc,id),l) ->
	let env = List.fold_left term env l in
	try
	  match List.assoc id env with
	    | Function x ->
		if !x = -1 then (x := List.length l; env)
		else if !x = List.length l then env
		else error loc ("bad arity for " ^ id)
	    | Var ->
		if l=[] then env
		else error loc (id ^ " is a variable")
	with
	    Not_found ->
	      (id,Function (ref (List.length l)))::env

let equation env (t1,t2) = term (term env t1) t2

let theory env t = 
  match t with
    | Builtin((_loc,"AC"),funlist) ->
	List.fold_left check_binary env funlist
    | Builtin((_loc,"C"),funlist) ->
	List.fold_left check_binary env funlist
    | Builtin((_loc,"A"),funlist) ->
	List.fold_left check_binary env funlist
    | Builtin((loc,id),funlist) ->
	printf "%a: warning, unknown theory %s@." print_loc loc id;
	List.fold_left ident env funlist
    | Equations l -> List.fold_left equation env l

let vars env l =
  List.fold_left
    (fun env (loc,id) ->
       try
	 let _ = List.assoc id env in
	 error loc ("duplicate declaration for " ^ id)
       with Not_found -> (id,Var)::env)
    env l

(* verifying extra vars condition is done afterwards *)

let cond env c =
  match c with
    | Arrow (t1,t2) -> term (term env t1) t2
    | Darrow (t1,t2) -> term (term env t1) t2
 
let rule env = function
  | Rew(c,l,r) | RelRew(c,l,r) ->
      let env = term env l in
      let env = List.fold_left cond env c in
      term env r

let decl env d = 
  match d with
    | VarDecl l -> vars env l
    | TheoryDecl l -> List.fold_left theory env l
    | RulesDecl l -> List.fold_left rule env l
    | StrategyDecl _s -> env
    | OtherDecl _ -> env

(* post checking *)

let csstrat env ((loc,id),l) =
  try
    match List.assoc id env with
      | Var -> error loc (id ^ " is a variable")
      | Function x ->
	  if !x = -1
	  then warning loc (id ^ " never used")
	  else 
	    if List.for_all 
	      (fun (loc,i) -> 
		 if 1 <= i && i <= !x then true
		 else error loc ("wrong replacement positions for " ^id)) l
	    then ()
	    else error loc ("checking replacement positions for " ^id^ " failed")

  with Not_found ->
    warning loc (id ^ " never used")

let strategy env s =
  match s with
    | Innermost -> ()
    | Outermost -> ()
    | ContextSensitive l -> List.iter (csstrat env) l

module StringSet = Set.Make(String)

let rec new_vars_of_term env vars t =
  match t with
    | Term((_loc,id),l) ->
	let vars = 
	  List.fold_left (new_vars_of_term env) vars l
	in
	try
	  match List.assoc id env with
	    | Function _x -> vars
	    | Var -> StringSet.add id vars
	with
	    Not_found ->
	      assert false

let rec check_vars_of_term env vars t =
  match t with
    | Term((loc,id),l) ->
	List.iter (check_vars_of_term env vars) l;
	try
	  match List.assoc id env with
	    | Function _x -> ()
	    | Var -> 
		if StringSet.mem id vars
		then () else
		  warning loc ("variable " ^ id ^ " is unbound")
	with
	    Not_found ->
	      assert false

let extra_var_conditions env = function
  | Rew(c,l,r) | RelRew(c,l,r) ->
      let lvars = new_vars_of_term env StringSet.empty l  in
      let cvars = 
	List.fold_left 
	  (fun vars cond ->
	     match cond with
	       | Arrow (t1,t2) -> 
		   check_vars_of_term env vars t1;
		   new_vars_of_term env vars t2
	       | Darrow (t1,t2) -> 
		   check_vars_of_term env vars t1;
		   check_vars_of_term env vars t2;
		   vars)       
	  lvars c
      in
      check_vars_of_term env cvars r

let post_check env d = 
  match d with
    | VarDecl _l -> ()
    | TheoryDecl _l -> ()
    | RulesDecl l -> List.iter (extra_var_conditions env) l
    | StrategyDecl s -> strategy env s
    | OtherDecl((loc,s),_) -> 
	match s with
	  | "from" 
	  | "Comment"
	  | "COMMENTS"
	  | "TPDB"
	  | "MODEL"
	  | "COMMENT" -> ()
	  | _ ->
	      error loc ("non-standard section " ^ s ^ " in file")
	      

let spec l =
  let env = List.fold_left (fun env d -> decl env d) [] l in
  List.iter (post_check env) l;
  env
