theory LETrans
  imports Values2
begin

    
lemma le_trans_aux: assumes n: "n = vsize v1 + vsize v2 + vsize v3" and
    v1_v2: "v1 \<sqsubseteq> v2" and v2_v3: "v2 \<sqsubseteq> v3"
  shows "v1 \<sqsubseteq> v3"
  using n v2_v3 v1_v2
proof (induction n arbitrary: v1 v2 v3 rule: nat_less_induct)
  let ?S = "\<lambda>x y z. vsize x + vsize y + vsize z"
  let ?P = "\<lambda>x y z. y \<sqsubseteq> z \<longrightarrow> x \<sqsubseteq> y \<longrightarrow> x \<sqsubseteq> z"
  case (1 n)
  show ?case
  proof (cases v1)
    case (VNat n1) then have v1: "v1 = VNat n1" .
    then have v3: "v3 = VNat n1" using 1 by (case_tac v2) auto
    then show "v1 \<sqsubseteq> v3" using v1 v3 by blast
  next
    case (VFun f1)
    then have v1: "v1 = VFun f1" .
    obtain f2 f3 where v2: "v2 = VFun f2" and v3: "v3 = VFun f3"
      using 1 v1 apply (case_tac v2) apply auto apply (case_tac v3) by auto

    show ?thesis
    proof (cases "f1 = []")
      case True
      then show ?thesis using v1 v3 by blast
    next
      case False then have f1_ne: "f1 \<noteq> []" .
          
      have "VFun f2 \<sqsubseteq> VFun f3" using 1(3) v2 v3 by simp
      then show ?thesis
      proof (rule le_fun_fun_inv)
        (* case le_bot *)
        assume "f2 = []" then show ?thesis using "1.prems"(3) v2 v3 by blast
            
      next (* case le_app_R1 *)
        fix f3a f3b assume f3: "f3 = f3a@f3b" and f2_f3a: "VFun f2 \<sqsubseteq> VFun f3a" and
          f3b_ne: "f3b \<noteq> []"
        then have f1_f3a: "VFun f1 \<sqsubseteq> VFun f3a" using 1(1) 1(2) 1(4) v1 v2 v3
          using nat_less_IH3[of n ?S ?P "VFun f1" "VFun f2" "VFun f3a"] by auto
        then show "v1 \<sqsubseteq> v3" using v1 v3 f3 f3b_ne f1_ne apply simp by (rule le_app_R1) auto

      next (* case le_app_R2 *)
        fix f3a f3b assume f3: "f3 = f3a@f3b" and f2_f3a: "VFun f2 \<sqsubseteq> VFun f3b" and
           f3b_ne: "f3a \<noteq> []"
        then have f1_f3a: "VFun f1 \<sqsubseteq> VFun f3b" using 1(1) 1(2) 1(4) v1 v2 v3
          using nat_less_IH3[of n ?S ?P "VFun f1" "VFun f2" "VFun f3b"] by auto
        then show "v1 \<sqsubseteq> v3" using v1 v3 f3 f3b_ne f1_ne apply simp apply (rule le_app_R2) by auto
            
      next (* case le_app_L *)
        fix f2a f2b assume f2: "f2 = f2a@f2b" and f2a_f3: "VFun f2a \<sqsubseteq> VFun f3"
          and f2b_f3: "VFun f2b \<sqsubseteq> VFun f3" and f2a_ne: "f2a \<noteq> []" and f2b_ne: "f2b \<noteq> []" 
        have f2_f3: "VFun f2 \<sqsubseteq> VFun f3" using f2a_f3 f2b_f3 f2 apply simp
         apply (rule le_app_L) using f2a_ne f2b_ne apply auto done
          
        show "v1 \<sqsubseteq> v3" using 1(4) v1 v2 v3 apply simp
        proof (erule le_fun_fun_inv)
          (* subcase le_bot *)
          assume "f1 = []" then show "VFun f1 \<sqsubseteq> VFun f3" by auto

        next (* subcase le_app_R1 *) 
          fix f2c f2d assume f2_cd: "f2 = f2c @ f2d" and f1_f2c: "VFun f1 \<sqsubseteq> VFun f2c"
            and f1_ne: "f1 \<noteq> []" and f2d_ne: "f2d \<noteq> []"
          have f2c_f3: "VFun f2c \<sqsubseteq> VFun f3"
            using le_app_app[of f2 f2a f2b f2c f2d f3] f2 f2_cd f2a_ne f2b_ne f2a_f3 f2b_f3 by auto 
          have s: "vsize (VFun f1) + vsize (VFun f2c) + vsize (VFun f3) < n"
            using 1(2) v1 v2 v3 f2_cd f2d_ne by auto
          show "VFun f1 \<sqsubseteq> VFun f3" using 1(1) s f1_f2c f2c_f3 by blast      
              
        next (* subcase le_app_R2 *)
          fix f2c f2d
          assume f2_cd:"f2 = f2c @ f2d" and f1_f2d: "VFun f1 \<sqsubseteq> VFun f2d" and f2c_ne:"f2c \<noteq> []"          
          have f2d_f3: "VFun f2d \<sqsubseteq> VFun f3"
            using le_app_app[of f2 f2a f2b f2c f2d f3] f2 f2_cd f2a_ne f2b_ne f2a_f3 f2b_f3 by auto
          show "VFun f1 \<sqsubseteq> VFun f3"
          proof (cases "f2d = []") 
            case True then have "f1 = []" using f1_f2d by blast then show ?thesis by blast
          next
            case False
            then have s: "vsize (VFun f1) + vsize (VFun f2d) + vsize (VFun f3) < n"
              using 1(2) v1 v2 v3 f2 f2_cd f2c_ne apply auto by (metis fsize_append fsize_append_left)
            show "VFun f1 \<sqsubseteq> VFun f3" using 1(1) s f1_f2d f2d_f3 by blast
          qed
            
        next (* subcase le_app_L *)
          fix f1a f1b assume f1: "f1 = f1a @ f1b" and f1a_f2: "VFun f1a \<sqsubseteq> VFun f2" and
            f1b_f2: "VFun f1b \<sqsubseteq> VFun f2" and f1a_ne: "f1a \<noteq> []" and f1b_ne: "f1b \<noteq> []"
          have "vsize (VFun f1a) + vsize (VFun f2) + vsize (VFun f3) < n"
            using 1(2) v1 v2 v3 f1 f1b_ne by auto
          then have f1a_f3: "VFun f1a \<sqsubseteq> VFun f3" using f1a_f2 f2_f3 1(1) by blast
          have "vsize (VFun f1b) + vsize (VFun f2) + vsize (VFun f3) < n"
            using 1(2) v1 v2 v3 f1 f1a_ne by auto
          then have f1b_f3: "VFun f1b \<sqsubseteq> VFun f3" using f1b_f2 f2_f3 1(1) by blast        
          show "VFun f1 \<sqsubseteq> VFun f3" using f1a_f3 f1b_f3 f1 apply simp apply (rule le_app_L)
            using f1a_ne f1b_ne by auto

        next (* subcase le_arrow *)
          fix vc va vb vd assume f2_: "f2 = [(vc, vd)]"
          have "False" using f2 f2_ f2a_ne f2b_ne by (case_tac f2a) auto
          then show "VFun f1 \<sqsubseteq> VFun f3" ..
              
        next (* subcase le_distr *)
         (* fix va vb vab v22 v11 v11'
          assume f1: "f1 = [(v11, v11')]" and f2_: "f2 = [(v22, va), (v22, vb)]" 
            and vab: "va \<squnion> vb = Some vab" and v22_v1: "v22 \<sqsubseteq> v11" and v1'_vab: "v11' \<sqsubseteq> vab"
            and "vab \<noteq> va" and "vab \<noteq> vb"

          have f2ab: "f2a = [(v22, va)] \<and> f2b = [(v22, vb)]" using f2 f2_ f2a_ne f2b_ne f2a_f3
            apply simp apply (case_tac f2a) apply force apply (case_tac f2b) apply force 
              apply (case_tac f2b) apply force apply (case_tac list) apply auto done            
          have v2va_f3: "v22\<mapsto>va \<sqsubseteq> VFun f3" using f2a_f3 f2ab by simp
          have v2vb_f3: "v22\<mapsto>vb \<sqsubseteq> VFun f3" using f2b_f3 f2ab by simp
          
          have 2: "v11\<mapsto>v11' \<sqsubseteq> v22 \<mapsto> vab" using v22_v1 v1'_vab by (rule le_arrow)
          have 3: "v22 \<mapsto> vab \<sqsubseteq> VFun f3" using f2a_f3 f2b_f3 f2ab sorry
              
              (* 
              Need le_dist_L!
              *)
            
          have "vsize (v11\<mapsto>v11') + vsize (v22 \<mapsto> vab) + vsize (VFun f3) < n"
            using 1(2) v1 v2 v3 f1 f2 f2_ f2ab vab vsize_join[of va vb vab] 
            apply auto apply (case_tac "vsize v22") using vsize_pos[of v22] apply force by arith 
          then show "VFun f1 \<sqsubseteq> VFun f3" using 2 3 1(1) f1 by blast*)
          show "VFun f1 \<sqsubseteq> VFun f3" sorry
        qed
      next
        show ?thesis sorry
      next
        show ?thesis sorry
      qed
    qed
  qed
qed

end
