theory ReductionSem
  imports Lambda Subst
begin

text{*
  The following is the definition of full beta reduction.
*}  
  
inductive reduce :: "exp \<Rightarrow> exp \<Rightarrow> bool" (infix "\<longrightarrow>" 55) where
  beta[intro!]: "EApp (ELam e) e' \<longrightarrow> \<up> (-1) 0 ([0 \<mapsto> e'] e)" |
  lam_cong[intro!]: "e \<longrightarrow> e' \<Longrightarrow> ELam e \<longrightarrow> ELam e'" |
  app_left[intro!]: "\<lbrakk> e1 \<longrightarrow> e1' \<rbrakk> \<Longrightarrow> EApp e1 e2 \<longrightarrow> EApp e1' e2" |
  app_right[intro!]: "\<lbrakk> e2 \<longrightarrow> e2' \<rbrakk> \<Longrightarrow> EApp e1 e2 \<longrightarrow> EApp e1 e2'" |
  delta[intro!]: "EPrim f (ENat n1) (ENat n2) \<longrightarrow> ENat (f n1 n2)" |
  prim_left[intro!]: "\<lbrakk> e1 \<longrightarrow> e1' \<rbrakk> \<Longrightarrow> EPrim f e1 e2 \<longrightarrow> EPrim f e1' e2" |
  prim_right[intro!]: "\<lbrakk> e2 \<longrightarrow> e2' \<rbrakk> \<Longrightarrow> EPrim f e1 e2 \<longrightarrow> EPrim f e1 e2'" |
  if_zero[intro!]: "EIf (ENat 0) thn els \<longrightarrow> els" |
  if_nz[intro!]: "n \<noteq> 0 \<Longrightarrow> EIf (ENat n) thn els \<longrightarrow> thn" |
  if_cond[intro!]: "\<lbrakk> cond \<longrightarrow> cond' \<rbrakk> \<Longrightarrow> 
    EIf cond thn els \<longrightarrow> EIf cond' thn els" 

inductive_cases
  red_var_inv[elim!]: "EVar x \<longrightarrow> e" and
  red_int_inv[elim!]: "ENat n \<longrightarrow> e" and
  red_lam_inv[elim!]: "ELam e \<longrightarrow> e'" and
  red_app_inv[elim!]: "EApp e1 e2 \<longrightarrow> e'"
  
inductive multi_step :: "exp \<Rightarrow> exp \<Rightarrow> bool" (infix "\<longrightarrow>*" 55) where
  ms_nil[intro!]: "e \<longrightarrow>* e" |
  ms_cons[intro!]: "\<lbrakk> e1 \<longrightarrow> e2; e2 \<longrightarrow>* e3 \<rbrakk> \<Longrightarrow> e1 \<longrightarrow>* e3"

definition diverge :: "exp \<Rightarrow> bool" where
  "diverge e \<equiv> (\<forall> e'. e \<longrightarrow>* e' \<longrightarrow> (\<exists> e''. e' \<longrightarrow> e''))"
  
definition stuck :: "exp \<Rightarrow> bool" where
  "stuck e \<equiv> \<not> (\<exists> e'. e \<longrightarrow> e')" 
declare stuck_def[simp]

inductive isval :: "exp \<Rightarrow> bool" where
  valnat[intro!]: "isval (ENat n)" |
  vallam[intro!]: "isval (ELam e)"

definition goes_wrong :: "exp \<Rightarrow> bool" where
  "goes_wrong e \<equiv> \<exists> e'. e \<longrightarrow>* e' \<and> stuck e' \<and> \<not> isval e'"
declare goes_wrong_def[simp]

datatype obs = ONat nat | OFun | OBad

fun observe :: "exp \<Rightarrow> obs \<Rightarrow> bool" where
  "observe (ENat n) (ONat n') = (n = n')" |
  "observe (ELam e) OFun = True" |
  "observe e ob = False" 

definition run :: "exp \<Rightarrow> obs \<Rightarrow> bool" (infix "\<Down>" 52) where
  "run e ob \<equiv> ((\<exists> v. e \<longrightarrow>* v \<and> observe v ob)
              \<or> ((diverge e \<or> goes_wrong e) \<and> ob = OBad))"
  
end