text\<open> 18 November 2021: Exercise for Homework 11 in CS 511 \<close> 
text\<open> Proof of theorem RichGF_5 at the end of this script is a possible solution \<close>

theory HW11_solution
  imports Main
begin

text\<open> 
If every poor man has a rich father, then there is a rich man who has a rich grandfather  \<close>

theorem RichGF_1 : 
  "\<forall> x. \<not> rich x \<longrightarrow> rich (father x) \<Longrightarrow> \<exists> x. rich x \<and> rich (father (father x))"
  by blast (* you can also try 'auto' *)

text \<open> The second proof contains 5 'apply' instructions,
       followed by a single invocation of the pre-defined method 'auto' \<close>
theorem RichGF_2 : 
  "\<forall> x. \<not> rich x \<longrightarrow> rich (father x) \<Longrightarrow> \<exists> x. rich x \<and> rich (father (father x))"
  apply (rule exCI)
  apply (rule conjI)
   apply (rule classical)
   apply (rotate_tac -2)
   apply (erule notE)
  by auto

text \<open> We simplify the notation a little, by replacing unary predicate 'rich' by 'R' 
       and unary function 'father' by 'f' \<close>

text\<open> The third proof contains 18 'apply' instructions,
      followed by a single invocation of the pre-defined method 'blast' \<close>
theorem RichGF_3 : 
  "\<forall> x. \<not> R x \<longrightarrow> R (f x) \<Longrightarrow> \<exists> x. R (f (f x)) \<and> R x"
  apply (rule classical)
  apply (rule exI)
  apply (rule conjI)

   apply (rule classical)
   apply (rule allE, assumption)
   apply (erule impE, assumption)
   apply (erule notE)
   apply (rule exI)
   apply (rule conjI, assumption)
   apply (rule classical) 
   apply (erule allE, erule notE, erule impE)
    apply assumption+ 
  by blast

text \<open> The fourth proof contains 45 'apply' instructions,
       and no invocation of any pre-defined method \<close>
theorem RichGF_4 : 
  "\<forall> x. \<not> R x \<longrightarrow> R (f x) \<Longrightarrow> \<exists> x. R x \<and> R (f (f x))"
  apply (rule classical)
  apply (rule exI)
  apply (rule conjI)

   apply (rule classical)
   apply (rule allE, assumption)
   apply (erule impE, assumption)
   apply (erule notE)
   apply (rule exCI)
   apply (rule conjI, assumption)
   apply (rule classical) 
   apply (erule notE, erule allE, erule mp, rule notI)

   apply (erule allE, rotate_tac -1, erule notE, rule conjI, rotate_tac -1)
  apply assumption+

  apply (rule classical) 
  apply (rule allE, assumption)
  apply (erule impE, assumption)
  apply (erule notE)
  apply (rule exCI)
  apply (rule conjI, assumption)
  apply (rule classical)
  apply (erule notE, erule allE, erule mp, rule notI)

  apply (erule notE, erule allE, erule notE, rule conjI, rotate_tac -1) 
   apply assumption+
  done

text \<open> The fifth proof contains 33 'apply' instructions,
       and no invocation of any pre-defined method \<close>
theorem RichGF_5 : 
  "\<forall> x. \<not> R x \<longrightarrow> R (f x) \<Longrightarrow> \<exists> x. R (f (f x)) \<and> R x"
  apply (rule classical)
  apply (rule exI)
  apply (rule conjI)

   apply (rule classical)
   apply (rule allE, assumption)
   apply (erule impE, assumption)
   apply (erule notE)
   apply (rule exI)
   apply (rule conjI, assumption)
   apply (rule classical) 
   apply (erule allE, erule notE, erule impE)
    apply assumption apply assumption 

  apply (rule classical)
  apply (rule allE) apply assumption
  apply (erule impE) apply assumption
  apply (erule notE)
  apply (rule exI)
  apply (rule conjI) apply assumption
  apply (rule classical)
  apply (erule allE)
  apply (erule notE)
  apply (erule impE) apply assumption
  apply assumption
  done

end