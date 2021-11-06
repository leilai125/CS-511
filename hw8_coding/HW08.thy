text\<open> 29 October 2021: Exercise for Homework Assignment 08 in CS 511 \<close> 
text\<open> Your task to remove the invocations of the pre-defined method 
      'blast' by an equivalent sequence of 'apply' steps \<close>

theory HW08
  imports Main
begin

text\<open> 'blast' is invoked three times, once in the proof of each of
      lemmas K1, L1, and M1 below \<close>

(* lemma K1 is the same in Exercise 2.3.9 (k), page 161, in [LCS] *)
lemma K1 : "\<forall> x. (P x \<and> Q x) \<Longrightarrow> (\<forall> x. P x) \<and> (\<forall> x. Q x)" 
  apply (rule conjI)
   apply (rule allI)
   apply (erule_tac x = "x" in allE)
   apply (erule conjE)
   apply assumption
  apply (rule allI)
  apply (erule_tac x = "x" in allE)
  apply (erule conjE)
  apply assumption

(* lemma L1 is the same in Exercise 2.3.9 (l), page 161, in [LCS] *)
lemma L1 : "(\<forall> x. P x) \<or> (\<forall> x. Q x) \<Longrightarrow> \<forall> x. (P x \<or> Q x)" 
  by blast

(* lemma M1 is the same in Exercise 2.3.9 (m), page 161, in [LCS] *)
lemma M1 : "\<exists> x. (P x \<and> Q x) \<Longrightarrow> (\<exists> x. P x) \<and> (\<exists> x. Q x)" 
  by blast

end