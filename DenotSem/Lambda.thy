(*<*)
theory Lambda
  imports Main
begin
(*>*)

section "Syntax of Lambda Calculus"
  
datatype exp = EVar nat | ENat nat | ELam exp ("\<lambda>" 1000) | EApp exp exp
  | EPrim "nat \<Rightarrow> nat \<Rightarrow> nat" exp exp | EIf exp exp exp

(*<*)
end
(*>*)

