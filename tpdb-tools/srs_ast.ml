
type ident = Lexing.position * string

type word = ident list

type rule = 
  | Rew of word * word 
  | RelRew of word * word

type strategy = 
  | Leftmost
  | Rightmost

type decl =
  | RulesDecl of rule list
  | StrategyDecl of strategy
  | OtherDecl of string list


  
