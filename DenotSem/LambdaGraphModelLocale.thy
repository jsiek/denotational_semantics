theory LambdaGraphModelLocale
  imports Lambda
begin

locale lambda_graph_model = 
  fixes D :: "exp \<Rightarrow> 'a list \<Rightarrow> 'a set" and up :: "'a \<Rightarrow> 'a set" and
    inj_nat :: "nat \<Rightarrow> 'a" 
  assumes d_var: "D (EVar x) \<rho> = up (\<rho>!x)" and
    d_nat: "D (ENat n) \<rho> = up (inj_nat n)" and
    d_lam: "D (ELam e) \<rho> = ..."
    
end