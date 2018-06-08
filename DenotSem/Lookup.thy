theory Lookup
  imports Main
begin

fun lookup :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "lookup [] a = None" |
  "lookup ((b,c)#L) a = (if a = b then Some c else lookup L a)"

end