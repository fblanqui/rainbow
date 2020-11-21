
type type_info =
  | Var
  | Function of int ref

exception Sem_error of Lexing.position * string

val spec : Trs_ast.decl list -> (string * type_info) list
