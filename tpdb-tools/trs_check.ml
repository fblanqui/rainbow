open Format
open Lexing
open Trs_ast

let verbose = ref false

let cime_output = ref false

let extension f =
  try
    let i = String.rindex f '.' in
    String.sub f (i+1) (String.length f - i - 1)
  with Not_found -> ""

let rm_extension f =
  try
    let i = String.rindex f '.' in
    String.sub f 0 i 
  with Not_found -> f

(* db output *)

let db_output = ref false

let db_ch = ref stdout

let db_fmt = ref std_formatter

let db_trs_pbs = ref []

let db_srs_pbs = ref []

let db_lp_pbs = ref []

let make_id dir file =
  let s = dir ^ "." ^ file in
  for i=0 to String.length s - 1 do
    match String.get s i with
      | '0'..'9' | 'A' .. 'Z' | 'a' .. 'z' | '_' | '.' | '-' -> ()
      | '/' -> String.set s i '.'
      | _ -> String.set s i '_'
  done;
  s



let db_pb pbs f =
  let dir = Filename.dirname f in
  let file = Filename.basename f in
  let name = rm_extension file in
  let id = make_id dir file in
  fprintf !db_fmt "%s = {@." id;
  pbs := (dir,id) :: !pbs;
  fprintf !db_fmt "name  = \"%s - %s\";@." dir name;
  fprintf !db_fmt "file  = \"%s\";@." f;
  dir,id

let get_categories ast =
  List.fold_left
    (fun (cond,t,i,o,cs,rel) decl ->
       match decl with
	 | RulesDecl l -> 
	     let cond =
	       List.fold_left
		 (fun cond r -> 
		    match r with
		      | Rew([],_,_) -> cond
		      | Rew(_,_,_) -> true
		      | RelRew(_,_,_) -> cond)
		 cond l
	     in 
	     let rel =
	       List.fold_left
		 (fun rel r -> 
		    match r with
		      | Rew(_,_,_) -> rel
		      | RelRew(_,_,_) -> true)
		 rel l
	     in 
	     (cond,t,i,o,cs,rel)
	 | TheoryDecl _ -> (cond,true,i,o,cs,rel)
	 | StrategyDecl Innermost -> (cond,t,true,o,cs,rel)
	 | StrategyDecl Outermost -> (cond,t,i,true,cs,rel)
	 | StrategyDecl (ContextSensitive _) -> (cond,t,i,o,true,rel)
	 | VarDecl _ | OtherDecl _ -> (cond,t,i,o,cs,rel))
    (false,false,false,false,false,false)
    ast

let get_srs_categories ast =
  List.fold_left
    (fun (rel) decl ->
       match decl with
	 | Srs_ast.RulesDecl l -> 
	     let rel =
	       List.fold_left
		 (fun rel r -> 
		    match r with
		      | Srs_ast.Rew(_,_) -> rel
		      | Srs_ast.RelRew(_,_) -> true)
		 rel l
	     in 
	     (rel)
	 | Srs_ast.StrategyDecl Srs_ast.Leftmost -> (rel)
	 | Srs_ast.StrategyDecl Srs_ast.Rightmost -> (rel)
	 | Srs_ast.OtherDecl _ -> (rel))
    (false)
    ast

let check_has f b1 b2 msg =
  if b1 && b2 then
    printf "Warning: problem %s has both %s.@." f msg 

let db_trs f ast = 
  let dir,id = db_pb db_trs_pbs f in
  let (has_cond,has_theory,has_innermost,has_outermost,has_context_sensitive,has_rel) =
    get_categories ast
  in
  let has_strategy = has_innermost || has_outermost || has_context_sensitive in
  check_has f has_cond has_theory "conditions and theory";
  check_has f has_cond has_strategy "conditions and strategy";
  check_has f has_theory has_strategy "theory and strategy";
  check_has f has_innermost has_outermost "innermost and outermost";
  check_has f has_innermost has_context_sensitive "innermost and CS strategy";
  check_has f has_outermost has_context_sensitive "outermost and CS strategy";
  fprintf !db_fmt "conditional = %b;@." has_cond;
  fprintf !db_fmt "theory  = %b;@." has_theory;
  fprintf !db_fmt "innermost  = %b;@." has_innermost;
  fprintf !db_fmt "outermost  = %b;@." has_outermost;
  fprintf !db_fmt "contextsensitive = %b;@." has_context_sensitive;
  fprintf !db_fmt "relative = %b;@." has_rel;
  fprintf !db_fmt "}@.@.";
  dir,id

let db_srs f ast = 
  let dir,id = db_pb db_srs_pbs f in
  let (has_rel) =
    get_srs_categories ast
  in
  fprintf !db_fmt "relative = %b;@." has_rel;
  fprintf !db_fmt "}@.@.";
  dir,id

let get_query f ast = 
  match
    List.fold_left
      (fun query decl ->
	 match decl with
	   | Lp_ast.Clause _ -> query
	   | Lp_ast.Query q -> 
	       match query with
		 | None -> Some q
		 | Some _ -> 
		     printf "Warning: too many queries in %s@." f; 
		     query)
      None ast
  with
    | None -> 
	printf "Warning: no query in %s@." f;
	"no_query_given()"
    | Some q -> 
	match q with
	  | Lp_ast.Pred((_,id),l) ->
	      try
		let args,_ =
		  List.fold_right
		    (fun a (args,sep) ->
		       match a with
			 | Lp_ast.Term((_,"i"),[]) 
			 | Lp_ast.Term((_,"b"),[]) -> ("i"^sep^args,",")
			 | Lp_ast.Term((_,"o"),[]) 
			 | Lp_ast.Term((_,"f"),[]) -> ("o"^sep^args,",")
			 | _ -> raise Exit)
		    l ("",")")
		in
		id ^ "(" ^ args
	      with
		  Exit -> 
		    printf "Warning: ill-formed query in %s@." f; 
		    "ill_formed_query()"



let db_lp f ast = 
  let dir,id = db_pb db_lp_pbs f in
  let query = get_query f ast in
  fprintf !db_fmt "query = \"%s\";@." query;
  fprintf !db_fmt "}@.@.";
  dir,id

let db_list name l =
  match l with
    | [] -> fprintf !db_fmt "%s = [ ];@." name;
    | (_dir,p)::r ->
	  fprintf !db_fmt "@[%s = [ %s" name p;
	  List.iter (fun (_,f) -> fprintf !db_fmt ";@ %s" f) r;
	  fprintf !db_fmt "];@]@."

(* filtering big dirs *)

let limit = ref 128

module StringSet = Set.Make(String)

let big_dirs = Hashtbl.create 7

let record_big_dirs dir id =
  try
    let (n,l) = Hashtbl.find big_dirs dir in
    Hashtbl.replace big_dirs dir (n+1,id::l)
  with Not_found -> 
    Hashtbl.replace big_dirs dir (1,[id])

let bdirs = Hashtbl.create 7 

let filter_big_dirs () =
  Hashtbl.iter 
    (fun dir (n,l) ->       
       let a = Array.make n "" in
       let _ = 
	 List.fold_left
	   (fun i id -> a.(i) <- id; i+1)
	   0 l
       in
       if n > !limit then
	 begin
	   printf "filtering %d problems from dir %s:@." !limit dir;
	   let k = ref 0 and l = ref StringSet.empty in
	   while !k < !limit do
	     let i = Random.int n in
	     let id = a.(i) in
	     if id <> "" then
	       begin
		 l := StringSet.add id !l;
		 incr k;
		 a.(i) <- ""
	   end
	   done;
	   Hashtbl.add bdirs dir !l
	 end)
    big_dirs

let filter_pbs pb =
  pb :=
    List.filter
      (fun (dir,id) ->
	 try
	   StringSet.mem id (Hashtbl.find bdirs dir)
	 with Not_found -> true)
      !pb
	   
  


let db_main () =
  filter_big_dirs ();
  filter_pbs db_trs_pbs;
  filter_pbs db_srs_pbs;
  fprintf !db_fmt "_main = {@.";
  fprintf !db_fmt "trs_tools = [ aprove ; cime ; jambox ; muterm ; nti ; tpa ; tpac ; ttt2 ; ttt2c ] ;@.";
  db_list "trs_pbs" !db_trs_pbs;
  fprintf !db_fmt "srs_tools = [ aprove ; cime ; jambox ; matchbox ; multumnonmulta ; nti ; torpa ; tpa ; ttt2 ] ;@.";
  db_list "srs_pbs" !db_srs_pbs;
  fprintf !db_fmt "lp_tools = [ aprove ; nti ; polytool ; talp ] ;@.";
  db_list "lp_pbs" !db_lp_pbs;
  fprintf !db_fmt "}@.";
  close_out !db_ch;
  printf "Database written@.";
  printf "Number of TRS pbs: %d@." (List.length !db_trs_pbs);
  printf "Number of SRS pbs: %d@." (List.length !db_srs_pbs);
  printf "Number of LP pbs : %d@." (List.length !db_lp_pbs)



(* main *)

let srs_files = ref []

let trs_files = ref []

let lp_files = ref []

let fp_files = ref []

let relative = ref false

let conditional = ref false 

let theory = ref false

let innermost = ref false

let outermost = ref false

let contextsensitive= ref false

let rec parse_args args =
  match args with
    | [] -> ()
    | "-v"::rem -> verbose := true; parse_args rem
    | "-cime"::rem -> cime_output := true; parse_args rem
    | "-db"::f::rem -> 
	db_output := true; 
	db_ch := open_out f; 	
	db_fmt := formatter_of_out_channel !db_ch;
	parse_args rem
    | "-trs"::f::rem -> 
	trs_files := f :: !trs_files; parse_args rem
    | "-srs"::f::rem -> 
	srs_files := f :: !srs_files; parse_args rem
    | "-relative"::rem ->
	relative := true; parse_args rem
    | "-conditional"::rem ->
        conditional := true;  parse_args rem
    | "-theory"::rem ->
	theory := true; parse_args rem
    | "-innermost"::rem ->
	innermost := true; parse_args rem
    | "-outermost"::rem ->
	outermost := true; parse_args rem
    | "-contextsensitive"::rem ->
	contextsensitive:= true; parse_args rem
    | f::rem ->
	begin
	  match extension f with
	    | "trs" ->
		trs_files := f :: !trs_files; parse_args rem
	    | "srs" ->
		srs_files := f :: !srs_files; parse_args rem
	    | "pl" ->
		lp_files := f :: !lp_files; parse_args rem
	    | "fp" ->
		fp_files := f :: !fp_files; parse_args rem
	    | _ ->
		eprintf "don't known what to do with argument %s@." f;
		exit 2;
	end
	

let check_trs f =
  let c = open_in f in
  let lb = from_channel c in
  try
    lb.lex_curr_p <-
    { pos_fname = f ; pos_lnum = 1; pos_cnum = 0; pos_bol = 0};
    let ast = Trs_parser.spec Trs_lexer.token lb in
    if !verbose then printf "parse ok@.";
    close_in c;
    let env = Trs_sem.spec ast in
    if !verbose then 
      begin
	printf "semantics ok, function symbols are:@.";
	List.iter
	  (fun (id,arity) ->
	     match arity with
	       | Trs_sem.Var -> ()
	       | Trs_sem.Function x -> printf "%s: %d@." id !x)
	  env
      end;
    let (has_cond,has_theory,has_innermost,has_outermost,has_context_sensitive,has_rel) =
	get_categories ast
    in
    if !cime_output then Cime.output f env has_innermost ast;
    let do_output =
      !db_output &&
	(if !relative then has_rel else 
	 if !conditional then has_cond else 
	 if !theory then has_theory else 
	 if !innermost then has_innermost else 
	 if !outermost then has_outermost else 
	 if !contextsensitive then has_context_sensitive else 
	   not (has_cond || has_theory || has_innermost || 
		  has_outermost || has_context_sensitive || has_rel))
    in
    if do_output then 
      let dir,id = db_trs f ast in 
      record_big_dirs dir id
  with 
    | Parsing.Parse_error ->
	let loc = Lexing.lexeme_start_p lb in
	eprintf "%a: syntax error.@." Trs_ast.print_loc loc;
	close_in c;
	exit 1
    | Trs_lexer.Lexing_error msg ->
	let loc = Lexing.lexeme_start_p lb in
	eprintf "%a: lexer error, %s.@." Trs_ast.print_loc loc msg;
	close_in c;
	exit 1
    | Trs_sem.Sem_error(loc,msg) ->
	eprintf "%a: %s.@." Trs_ast.print_loc loc msg;
	exit 1

let check_srs f =
  let c = open_in f in
  let lb = from_channel c in
  try
    lb.lex_curr_p <-
    { pos_fname = f ; pos_lnum = 1; pos_cnum = 0; pos_bol = 0};
    let ast = Srs_parser.spec Srs_lexer.token lb in
    if !verbose then printf "parse ok@.";
    close_in c;
    let has_rel = get_srs_categories ast in
    if !cime_output then Cime.output_srs f false ast;
    let do_output =
      !db_output &&
	(if !relative then has_rel else not has_rel)
    in
    if do_output then 
      let dir,id = db_srs f ast in
      record_big_dirs dir id
  with 
    | Parsing.Parse_error ->
	let loc = Lexing.lexeme_start_p lb in
	eprintf "%a: syntax error.@." Trs_ast.print_loc loc;
	close_in c;
	exit 1

let check_lp f =
  let c = open_in f in
  let lb = from_channel c in
  try
    lb.lex_curr_p <-
    { pos_fname = f ; pos_lnum = 1; pos_cnum = 0; pos_bol = 0};
    let ast = Lp_parser.spec Lp_lexer.token lb in
    if !verbose then printf "parse ok@.";
    close_in c;
    if !db_output then let _dir = db_lp f ast in ()
  with 
    | Parsing.Parse_error ->
	let loc = Lexing.lexeme_start_p lb in
	eprintf "%a: syntax error.@." Trs_ast.print_loc loc;
	close_in c;
	if !db_output then
	  printf "Giving up on file %s@." f
	else exit 1
    | Failure msg ->
	let loc = Lexing.lexeme_start_p lb in
	eprintf "%a: Failure: %s.@." Trs_ast.print_loc loc msg;
	if !db_output then
	  printf "Giving up on file %s@." f
	else exit 1
  
let main () =
  try
    parse_args (List.tl (Array.to_list Sys.argv));
    List.iter check_trs !trs_files;
    List.iter check_srs !srs_files;
    List.iter check_lp !lp_files;
    if !db_output then db_main ();
    exit 0
      
  with
    | Sys_error msg ->
	eprintf "System error: %s.@." msg;
	exit 1
    | Failure msg ->
	eprintf "Failure: %s.@." msg;
	exit 1

let _ = Printexc.catch main ()
