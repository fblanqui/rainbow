open Trs_ast
open Format

let print_cime_id fmt id =
  let has_symbols = ref false 
  and has_letters = ref false
  in
  for i = 0 to String.length id - 1 do
    match id.[i] with
      | 'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' | '_' | '\'' ->
	  has_letters := true
      | _ -> 
	  has_symbols := true
  done;
  let s =
    if !has_symbols && !has_letters then
      let s = ref "" in
      for i = 0 to String.length id - 1 do
	match id.[i] with
	  | 'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' | '_' | '\'' ->
	      ()
	  | c -> 
	      s := !s ^ String.make 1 c
      done;
      !s      
    else id
  in
  let s =
    match s with
      | ">" -> "_gt_"
      | "<" -> "_lt_"
      | _ -> s
  in
  fprintf fmt "%s" s

let rec print_cime_term fmt t =
  match t with
    | Term((_,id),[]) -> fprintf fmt " %a " print_cime_id id
    | Term((_,id),t::l) -> 
	fprintf fmt " %a (%a%a)" print_cime_id id 
	  print_cime_term t print_cime_term_list l

and print_cime_term_list fmt l =
  match l with
    | [] -> ()
    | t::l -> fprintf fmt ",%a%a" print_cime_term t print_cime_term_list l


let print_cime_rules fmt ast =
  List.iter
    (fun decl ->
       match decl with
	 | VarDecl _ -> ()
	 | TheoryDecl _l ->
	     () (* failwith "Theories not yet supported" *)
	 | RulesDecl l ->
	     List.iter
	       (fun r ->
		  match r with
		    | Rew([],lhs,rhs) ->
			fprintf fmt "%a -> %a ;@."
			  print_cime_term lhs print_cime_term rhs
		    | RelRew([],lhs,rhs) ->
			fprintf fmt "%a -> %a ;@."
			  print_cime_term lhs print_cime_term rhs
			(* failwith "relative termination not supported" *)
		    | Rew(_::_,_,_) | RelRew(_::_,_,_) ->
			failwith "conditional rules not supported")
	       l
	 | StrategyDecl _ ->
	     () (* failwith "Strategies not yet supported" *)
	 | OtherDecl _ -> ())
    ast
	

let output f env has_innermost ast =
  let c = open_out (f ^ ".cim2") in
  let fmt = formatter_of_out_channel c in
  let (ac,comm) =
    List.fold_left
      (fun acc decl -> 
	 match decl with
	   | TheoryDecl l ->
	       List.fold_left
		 (fun (ac,comm) th ->
		    match th with
		      | Builtin((_,id),idl) ->
			  begin
			    match id with
			      | "AC" -> ((List.map snd idl)@ac,comm)
			      | "C" -> (ac,(List.map snd idl)@comm)
			      | _ ->
				  eprintf "Cime do not support builtin theory %s@." id;
				  exit 1
			  end
		      | Equations _ ->
			  eprintf "Cime do not support arbitrary equational theories@.";
			  exit 1)
		 acc l
	   | VarDecl _ | RulesDecl _ | StrategyDecl _ | OtherDecl (_,_) -> acc)
      ([],[]) ast
  in
  let (sigma,vars) = 
    List.fold_left
      (fun (sigma,vars) (id,arity) ->
	 match arity with
	   | Trs_sem.Var -> (sigma,id::vars)
	   | Trs_sem.Function x -> 
	       if List.mem id ac
	       then ((id,-2)::sigma,vars)
	       else
		 if List.mem id comm
		 then ((id,-1)::sigma,vars)
		 else
		   ((id,!x)::sigma,vars))
      ([],[])      
      env
  in
  fprintf fmt "let X = vars \"";
  List.iter (fun id -> fprintf fmt "%a " print_cime_id id) vars;
  fprintf fmt "\";@.";
  fprintf fmt "let F = signature \"";
  List.iter (fun (id,n) -> 
	       let ar =
		 match n with
		   | -2 -> "prefix AC"
		   | -1 -> "prefix commutative"
		   | _ -> string_of_int n
	       in
	       fprintf fmt "%a : %s ; " print_cime_id id ar) sigma;
  fprintf fmt "\";@.";
  fprintf fmt "let R = %s F X \"" (if has_innermost then "TRS" else "HTRS {}");
  print_cime_rules fmt ast;
  fprintf fmt "\";@.";
  if has_innermost then
    begin
      fprintf fmt "termcrit \"innermost\";@.";
      fprintf fmt "termcrit \"nomarks\";@.";
      fprintf fmt "termination R;@.";
    end
  else
    begin
      fprintf fmt "termcrit \"minimal\";@.";
      fprintf fmt "h_termination R;@.";
    end;
  fprintf fmt "output_last_proof \"\";@.";
  fprintf fmt "#quit;@.";
  close_out c

module StringSet = Set.Make(String)


let rec print_cime_word fmt w =
  match w with
    | [] -> fprintf fmt "x"
    | (_,i)::r ->
	fprintf fmt " %s ( %a ) " i print_cime_word r

let print_cime_srs_rules fmt ast =
  List.iter
    (fun decl ->
       match decl with
	 | Srs_ast.RulesDecl l ->
	     List.iter
	       (fun r -> match r with
		  | Srs_ast.Rew(lhs,rhs) ->
		      fprintf fmt "%a -> %a ;@."
			print_cime_word lhs print_cime_word rhs
		  | Srs_ast.RelRew(lhs,rhs) ->
		      fprintf fmt "%a -> %a ;@."
			print_cime_word lhs print_cime_word rhs
 			(* failwith "relative termination not supported") *))
	       l
	 | Srs_ast.StrategyDecl _ | Srs_ast.OtherDecl _ -> ())
    ast
	
let output_srs f has_innermost ast =
  let c = open_out (f ^ ".cim2") in
  let fmt = formatter_of_out_channel c in
  fprintf fmt "let X = vars \"x\";@.";
  let sigma = 
    List.fold_left 
      (fun s decl ->
	 match decl with
	   | Srs_ast.RulesDecl dl ->
	       List.fold_left
		 (fun s r ->
		    match r with
		      | Srs_ast.Rew(l,r) | Srs_ast.RelRew(l,r) ->
			  let s = 
			    List.fold_left
			      (fun s (_,i) -> StringSet.add i s) s l
			  in
			  List.fold_left
			    (fun s (_,i) -> StringSet.add i s) s r)
		 s dl 
	   | Srs_ast.StrategyDecl _ | Srs_ast.OtherDecl _ -> s)      
      StringSet.empty 
      ast
  in      
  fprintf fmt "let F = signature \"";
  StringSet.iter (fun id -> fprintf fmt "%s : 1 ; " id) sigma;
  fprintf fmt "\";@.";
  fprintf fmt "let R = %s F X \"" (if has_innermost then "TRS" else "HTRS {}");
  print_cime_srs_rules fmt ast;
  fprintf fmt "\";@.";
  if has_innermost then
    begin
      fprintf fmt "termcrit \"innermost\";@.";
      fprintf fmt "termcrit \"nomarks\";@.";
      fprintf fmt "termination R;@.";
    end
  else
    begin
      fprintf fmt "termcrit \"minimal\";@.";
      fprintf fmt "h_termination R;@.";
    end;
  fprintf fmt "output_last_proof \"proof.scr\";@.";
  fprintf fmt "#quit;@.";
  close_out c
