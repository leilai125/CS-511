theory deMorgan1
  imports Main

begin 

text\<open> Apply style \<close>
lemma deMorgan : "\<not> (P \<or> Q) \<longrightarrow> (\<not> P \<and> \<not> Q)"
  apply (rule impI)
  apply (rule conjI)
  apply (rule notI)
  apply (erule notE)
  apply (rule disjI1)
  apply assumption
  apply (rule notI)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done