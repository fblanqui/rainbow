

type ident = Lexing.position * string

type term = 
  | Var of ident
  | Term of ident * term list

type lit = Pred of ident * term list

type decl =
  | Clause of lit * lit list
  | Query of lit

	





