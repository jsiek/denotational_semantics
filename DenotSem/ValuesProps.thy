theory ValuesProps
  imports Values
begin

lemma fun_le_subset: "set t1 \<subseteq> set t2 \<Longrightarrow> t1 \<sqsubseteq> t2"
 by (induction t1) auto  
  
lemma fun_le_append1: "t1 \<sqsubseteq> t1 @ t2"
proof -
  have "set t1 \<subseteq> set (t1 @ t2)" by auto
  then show ?thesis using fun_le_subset by blast
qed
  
lemma fun_le_append2: "t1 \<sqsubseteq> t2 @ t1"
proof -
  have "set t1 \<subseteq> set (t2 @ t1)" by auto
  then show ?thesis using fun_le_subset by blast
qed

lemma fun_append_le: fixes t1::"entry list" and t1'::"entry list"
  assumes t1_t2: "t1 \<sqsubseteq> t2" and t1p_t2: "t1' \<sqsubseteq> t2" shows "t1 @ t1' \<sqsubseteq> t2"    
  using t1_t2 t1p_t2 by (induction t1 arbitrary: t1' t2) auto
    
lemma join_lub_aux: fixes v1::val and v2::val 
  assumes n: "n = size v1 + size v2" and ub1: "v1 \<sqsubseteq> v" and ub2: "v2 \<sqsubseteq> v"
  shows "val_lub (v1 \<squnion> v2) v1 v2"
  using n ub1 ub2 apply (induction n arbitrary: v1 v2 v rule: nat_less_induct)
  apply (case_tac v1)
   apply (case_tac v2) apply force apply force
  apply (case_tac v2) apply force
  apply clarify  
  apply (rule conjI) apply (simp only: vfun_join)
   apply clarify apply (rule fun_le_append1)
  apply (rule conjI) apply (simp only: vfun_join)
   apply clarify apply (rule fun_le_append2)
  apply clarify apply (simp only: vfun_join)
  apply clarify
  apply (rule fun_append_le) apply blast apply blast
  done

abbreviation bounded :: "val \<Rightarrow> val \<Rightarrow> bool" where
  "bounded v1 v2 \<equiv> (\<exists> v. is_val v \<and> v1 \<sqsubseteq> v \<and> v2 \<sqsubseteq> v)" 

proposition join_lub: fixes v1::val and v2::val 
  assumes v12: "bounded v1 v2" shows "val_lub (v1 \<squnion> v2) v1 v2"
  using join_lub_aux v12 by blast

end
