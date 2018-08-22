theory LambdaGraphModelLocale
  imports Lambda DenotAlt Deterministic DenotFSet Subst
begin
  
locale model_base =
  fixes D :: "exp \<Rightarrow> 'a list \<Rightarrow> 'a set" and le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<lesssim>" 55) and
    inj_nat :: "nat \<Rightarrow> 'a" and app :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" and wf:: "'a \<Rightarrow> bool" and
    is_fun :: "'a \<Rightarrow> bool" and entries :: "'a \<Rightarrow> ('a \<times> 'a) fset"
begin
  
definition wf_env :: "'a list \<Rightarrow> bool" where
  "wf_env \<rho> \<equiv> \<forall>k. k < length \<rho> \<longrightarrow> wf (\<rho>!k)"

end  

locale lambda_graph_model = model_base +
  assumes d_var: "D (EVar x) \<rho> = (if x < length \<rho> then {\<rho>!x} else {})" and
    d_nat: "D (ENat n) \<rho> = {inj_nat n}" and
    d_lam: "D (ELam e) \<rho> = { f. wf f \<and> is_fun f 
              \<and> (\<forall> v v'. (v,v') |\<in>| entries f \<longrightarrow> (\<exists>v''. v'' \<in> D e (v#\<rho>) \<and> v' \<lesssim> v''))}" and
    d_app: "D (EApp e1 e2) \<rho> = {v'. \<exists> f v. f \<in> D e1 \<rho> \<and> v \<in> D e2 \<rho> \<and> v' \<in> app f v }" and
    d_prim: "D (EPrim f e1 e2) \<rho> = {v. wf v \<and> (\<exists> v1 v2 n1 n2. v1 \<in> D e1 \<rho> \<and> v2 \<in> D e2 \<rho> 
            \<and> inj_nat n1 \<lesssim> v1 \<and> inj_nat n2 \<lesssim> v2 \<and> v \<lesssim> inj_nat (f n1 n2))}" and
    d_if: "D (EIf e1 e2 e3) \<rho> = {v. \<exists> v1 n1. v1 \<in> D e1 \<rho> \<and> inj_nat n1 \<lesssim> v1 \<and>
          (n1 = 0 \<longrightarrow> v \<in> D e3 \<rho>) \<and> (n1 \<noteq> 0 \<longrightarrow> v \<in> D e2 \<rho>) }"
    
interpretation intersection_model:
  lambda_graph_model DenotAlt.D "(\<lambda>a b. (b::ty) <: a)" TNat fun_app wf_ty fun_pred entries
  apply unfold_locales apply force+ done
    
  
abbreviation up_val :: "val \<Rightarrow> val set" where
  "up_val v \<equiv> {v'. v' \<sqsubseteq> v}" 
  
abbreviation simple_apply :: "val \<Rightarrow> val \<Rightarrow> val set" where
  "simple_apply v1 v2 \<equiv> { v3. \<exists>f v2' v3'. v1=VFun f \<and> (v2',v3') |\<in>| f \<and> v2' \<sqsubseteq> v2 \<and> v3 \<sqsubseteq> v3' }"

fun is_fun_val :: "val \<Rightarrow> bool" where
  "is_fun_val (VNat n) = False" |
  "is_fun_val (VFun f) = True"
  
fun fun_entries :: "val \<Rightarrow> (val \<times> val) fset" where
  "fun_entries (VNat n) = {||}" |
  "fun_entries (VFun f) = f"
  
interpretation simple_model: lambda_graph_model DenotFSet.E val_le VNat simple_apply 
  "\<lambda>v. True" is_fun_val fun_entries
  apply unfold_locales
       apply force
      apply force
     defer
     apply simp apply (smt Collect_cong notin_fset)   
    apply simp apply (rule Collect_cong) apply (rule iffI) 
     apply blast using val_le.simps apply auto[1]
  using val_le.simps apply auto[1] 
  apply simp apply (rule Collect_cong) apply (rule iffI) 
  apply (metis fun_entries.simps(2) is_fun_val.simps(2) notin_fset)
  by (metis fun_entries.simps(2) is_fun_val.elims(2) notin_fset)

lemma nth_append_less: "n < length xs \<Longrightarrow> (xs @ ys)!n = xs!n"  
  using nth_append[of xs ys n] by simp
    
lemma nth_append_greater: "length xs \<le> n \<Longrightarrow> (xs @ ys)!n = ys!(n - length xs)"
  using nth_append[of xs ys n] by auto
  
context lambda_graph_model
begin

definition lam :: "('a \<Rightarrow> 'a set) \<Rightarrow> 'a set" where
  "lam G = { f. wf f \<and> is_fun f 
              \<and> (\<forall> v v'. (v,v') |\<in>| entries f \<longrightarrow> (\<exists>v''. v'' \<in> G v \<and> v' \<lesssim> v''))}"

lemma lambda_def[simp]: "D (ELam e) \<rho> = lam (\<lambda>v. D e (v # \<rho>))"
  unfolding lam_def using d_lam by blast
  
lemma sem_shift: "D e (\<rho>\<^sub>1@\<rho>\<^sub>3) = D (shift (length \<rho>\<^sub>2) (length \<rho>\<^sub>1) e) (\<rho>\<^sub>1 @ \<rho>\<^sub>2 @ \<rho>\<^sub>3)" 
proof (induction e arbitrary: \<rho>\<^sub>1 \<rho>\<^sub>2 \<rho>\<^sub>3)
  case (EVar x)
  show ?case
  proof (cases "x < length \<rho>\<^sub>1")
    case True
    from True have r13_x: "(\<rho>\<^sub>1 @ \<rho>\<^sub>3)!x = \<rho>\<^sub>1!x" using nth_append_less by auto
    from True have r123_x: "(\<rho>\<^sub>1 @ \<rho>\<^sub>2 @ \<rho>\<^sub>3)!x = \<rho>\<^sub>1!x" using nth_append_less by auto
    have "D (EVar x) (\<rho>\<^sub>1@\<rho>\<^sub>3) = {\<rho>\<^sub>1!x}" using True d_var r13_x by auto
    also have "... = D (shift (length \<rho>\<^sub>2) (length \<rho>\<^sub>1) (EVar x)) (\<rho>\<^sub>1 @ \<rho>\<^sub>2 @ \<rho>\<^sub>3)"
      using r123_x True d_var by auto
    finally show ?thesis by simp
  next
    case False from False have 1: "length \<rho>\<^sub>1 \<le> x" by simp    
    show ?thesis
    proof (cases "x < length (\<rho>\<^sub>1@\<rho>\<^sub>3)")
      case True
      from 1 have r13_x: "(\<rho>\<^sub>1@\<rho>\<^sub>3)!x = \<rho>\<^sub>3!(x - length \<rho>\<^sub>1)" using nth_append_greater[of \<rho>\<^sub>1 x] by simp
      have 2: "D (EVar x) (\<rho>\<^sub>1@\<rho>\<^sub>3) = {\<rho>\<^sub>3!(x - length \<rho>\<^sub>1)}" 
        using r13_x 1 True d_var by simp
      also have "... = D (shift (length \<rho>\<^sub>2) (length \<rho>\<^sub>1) (EVar x)) (\<rho>\<^sub>1 @ \<rho>\<^sub>2 @ \<rho>\<^sub>3)"
      proof -
        have 3: "length (\<rho>\<^sub>1@\<rho>\<^sub>2) \<le> x + length \<rho>\<^sub>2" using 1 by simp
        then have 4: "((\<rho>\<^sub>1 @ \<rho>\<^sub>2) @ \<rho>\<^sub>3) ! (x + length \<rho>\<^sub>2) = \<rho>\<^sub>3!((x + length \<rho>\<^sub>2) - length (\<rho>\<^sub>1@\<rho>\<^sub>2))"
          by (rule nth_append_greater)
        show ?thesis using 1 4 d_var True by simp 
      qed
      finally show ?thesis by simp
    next
      case False
      then show ?thesis using d_var by simp
    qed        
  qed
next
  case (ELam e)
  let ?n = "length \<rho>\<^sub>1" and ?m = "length \<rho>\<^sub>2"  
  have "D (\<lambda> e) (\<rho>\<^sub>1 @ \<rho>\<^sub>3) = lam (\<lambda>d. D e (d # \<rho>\<^sub>1 @ \<rho>\<^sub>3))" by simp
  also have "... = lam (\<lambda>d. D (\<up> ?m (Suc ?n) e) (d # \<rho>\<^sub>1 @ \<rho>\<^sub>2 @ \<rho>\<^sub>3))"
  proof -
    { fix d have "D e (d#\<rho>\<^sub>1@\<rho>\<^sub>3) = D (\<up> ?m (Suc ?n) e) (d#\<rho>\<^sub>1@\<rho>\<^sub>2@\<rho>\<^sub>3)"
        using ELam[of "d#\<rho>\<^sub>1" \<rho>\<^sub>3 \<rho>\<^sub>2] by simp }
    thus ?thesis by simp    
  qed
  also have "... = D (\<up> ?m ?n (\<lambda> e)) (\<rho>\<^sub>1 @ \<rho>\<^sub>2 @ \<rho>\<^sub>3)" by simp
  finally show ?case by blast       
qed (auto simp: d_nat d_app d_prim d_if)

thm Set.set_eqI

lemma sem_subst_lam:
  fixes f::'a
  assumes IH: "(\<Union>v\<in>D e' \<rho>\<^sub>2. D e (\<rho>\<^sub>1 @ v # \<rho>\<^sub>2)) = D ([length \<rho>\<^sub>1\<mapsto>\<up> (length \<rho>\<^sub>1) 0 e']e) (\<rho>\<^sub>1 @ \<rho>\<^sub>2)" 
  shows "(f \<in> (\<Union>v\<in>D e' \<rho>\<^sub>2. D (\<lambda> e) (\<rho>\<^sub>1 @ v # \<rho>\<^sub>2)))
        = (f \<in> D ([length \<rho>\<^sub>1\<mapsto>\<up> (length \<rho>\<^sub>1) 0 e']\<lambda> e) (\<rho>\<^sub>1 @ \<rho>\<^sub>2))" using IH
    apply (induction f)
    
sorry
  
lemma sem_subst:
  assumes ne_ep: "D e' \<rho>\<^sub>2 \<noteq> {}"
  shows "(\<Union>v\<in> D e' \<rho>\<^sub>2. D e (\<rho>\<^sub>1@v#\<rho>\<^sub>2)) = D (([length \<rho>\<^sub>1 \<mapsto> (\<up> (length \<rho>\<^sub>1) 0 e')] e)) (\<rho>\<^sub>1@\<rho>\<^sub>2)" using ne_ep
proof (induction e arbitrary: \<rho>\<^sub>1 \<rho>\<^sub>2)
  case (EVar x)
  show ?case
  proof (cases "x < length \<rho>\<^sub>1")
    case True
    have "(\<Union>v\<in>D e' \<rho>\<^sub>2. D (EVar x) (\<rho>\<^sub>1@v#\<rho>\<^sub>2)) = (\<Union>v\<in>D e' \<rho>\<^sub>2. D (EVar x) \<rho>\<^sub>1)"
        using EVar True nth_append_less[of x \<rho>\<^sub>1] d_var by auto  
    also have "... = D (EVar x) \<rho>\<^sub>1" using EVar by auto
    also have "... = D (EVar x) (\<rho>\<^sub>1@\<rho>\<^sub>2)" using True nth_append_less[of x \<rho>\<^sub>1] d_var by auto
    also have "D (EVar x) (\<rho>\<^sub>1@\<rho>\<^sub>2) = D (([length \<rho>\<^sub>1\<mapsto>\<up> (length \<rho>\<^sub>1) 0 e']EVar x)) (\<rho>\<^sub>1@\<rho>\<^sub>2)"
      using True by simp
    finally show ?thesis by simp
  next
    case False from False have 1: "length \<rho>\<^sub>1 \<le> x" by simp
    show ?thesis
    proof (cases "x = length \<rho>\<^sub>1")
      case True
      have "(\<Union>v\<in>D e' \<rho>\<^sub>2. D (EVar x) (\<rho>\<^sub>1 @ v # \<rho>\<^sub>2)) = (\<Union>v\<in>D e' \<rho>\<^sub>2. {v})"
        using EVar True d_var by simp
      also have "... = D e' \<rho>\<^sub>2" by simp
      also have "... = D (shift (length \<rho>\<^sub>1) 0 e') (\<rho>\<^sub>1 @ \<rho>\<^sub>2)" using sem_shift[of e' "[]"] by simp
      also from True have "... = D (([length \<rho>\<^sub>1\<mapsto>\<up> (length \<rho>\<^sub>1) 0 e']EVar x)) (\<rho>\<^sub>1@\<rho>\<^sub>2)" by simp
      finally show ?thesis by blast
    next
      case False
         let ?x = "x - Suc (length \<rho>\<^sub>1)"
      have 2: "\<rho>\<^sub>2!?x = (\<rho>\<^sub>1 @ \<rho>\<^sub>2)!(x-1)" using False 1 nth_append_greater[of \<rho>\<^sub>1] by auto          
      have "\<And>v. ((\<rho>\<^sub>1@[v])@\<rho>\<^sub>2)!x = \<rho>\<^sub>2!(x - (length (\<rho>\<^sub>1@[v])))"
        apply (rule nth_append_greater) using False 1 by auto
      then have "(\<Union>v\<in>D e' \<rho>\<^sub>2. D (EVar x) (\<rho>\<^sub>1@v#\<rho>\<^sub>2)) = (\<Union>v\<in>D e' \<rho>\<^sub>2. D (EVar ?x) \<rho>\<^sub>2)" 
        using False 1 d_var by auto
      also have "... = D (EVar ?x) \<rho>\<^sub>2" using EVar by auto
      also  have "... = D (EVar (x-1)) (\<rho>\<^sub>1 @ \<rho>\<^sub>2)" using False 1 2 d_var by auto
      also from False 1 have "... = D (([length \<rho>\<^sub>1\<mapsto>\<up> (length \<rho>\<^sub>1) 0 e']EVar x)) (\<rho>\<^sub>1@\<rho>\<^sub>2)" by simp
      finally show ?thesis by simp
    qed
  qed
next
  case (ENat x)
  then show ?case using d_nat by auto
next
  case (ELam e)
  show ?case
  proof (rule set_eqI)
    fix f
    show "(f \<in> (\<Union>v\<in>D e' \<rho>\<^sub>2. D (\<lambda> e) (\<rho>\<^sub>1 @ v # \<rho>\<^sub>2)))
        = (f \<in> D ([length \<rho>\<^sub>1\<mapsto>\<up> (length \<rho>\<^sub>1) 0 e']\<lambda> e) (\<rho>\<^sub>1 @ \<rho>\<^sub>2))"
      sorry
  qed    
(*    
  let ?n = "length \<rho>\<^sub>1" and ?m = "length \<rho>\<^sub>2"  

  have "(\<Union>v\<in>D e' \<rho>\<^sub>2. D (\<lambda> e) (\<rho>\<^sub>1 @ v # \<rho>\<^sub>2)) 
                 = (\<Union>v\<in>D e' \<rho>\<^sub>2. lam (\<lambda>d. D e (d # \<rho>\<^sub>1 @ v # \<rho>\<^sub>2)))" by simp
  also have "... = lam (\<lambda>d. D ([Suc ?n\<mapsto>\<up> (Suc ?n) 0 e']e) (d # \<rho>\<^sub>1 @ \<rho>\<^sub>2))" 
  proof (rule set_eqI)
    fix f
    
    
  proof -
    { fix G H
      have "(\<Union>v\<in>D e' \<rho>\<^sub>2. lam (\<lambda>d. G d v)) = lam (\<lambda>d. H d)" sorry 
    }
    { fix d::'a
      have "(\<Union>v\<in>D e' \<rho>\<^sub>2. D e (d # \<rho>\<^sub>1 @ v # \<rho>\<^sub>2)) = D ([Suc ?n\<mapsto>\<up> (Suc ?n) 0 e']e) (d # \<rho>\<^sub>1 @ \<rho>\<^sub>2)"        
        using ELam.IH[of \<rho>\<^sub>2 "d#\<rho>\<^sub>1"] ELam.prems by simp }
    then have 1: "(\<Union>v\<in>D e' \<rho>\<^sub>2. lam (\<lambda>d. D e (d # \<rho>\<^sub>1 @ v # \<rho>\<^sub>2)))
      \<subseteq> lam (\<lambda>d. D ([Suc (length \<rho>\<^sub>1)\<mapsto>\<up> (Suc (length \<rho>\<^sub>1)) 0 e']e) (d # \<rho>\<^sub>1 @ \<rho>\<^sub>2))"
      unfolding lam_def by fastforce
    have 2: "lam (\<lambda>d. D ([Suc (length \<rho>\<^sub>1)\<mapsto>\<up> (Suc (length \<rho>\<^sub>1)) 0 e']e) (d # \<rho>\<^sub>1 @ \<rho>\<^sub>2))
      \<subseteq> (\<Union>v\<in>D e' \<rho>\<^sub>2. lam (\<lambda>d. D e (d # \<rho>\<^sub>1 @ v # \<rho>\<^sub>2)))"
      unfolding lam_def apply auto
        
      sorry
    show ?thesis using 1 2 by blast
  qed
  also have "... = D ([?n\<mapsto>\<up> ?n 0 e']\<lambda> e) (\<rho>\<^sub>1 @ \<rho>\<^sub>2)" by simp     
  finally show ?case by simp
*)
next
  case (EApp e1 e2)
  then show ?case using d_app sorry
next
  case (EPrim x1a e1 e2)
  then show ?case using d_prim sorry
next
  case (EIf e1 e2 e3)
  then show ?case using d_if sorry
qed 
    
end
    
  
end