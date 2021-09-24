theory deMorgan3
  imports Main

begin 

text\<open> Apply style \<close>
lemma deMorgan : " (\<not>P \<or> \<not>Q) \<longrightarrow> \<not>( P \<and> Q)"
  apply (rule impI)
  apply (erule disjE)
  apply (rule notI)
  apply (erule notE)
  apply (erule conjE)
  apply assumption
  apply (rule notI)
  apply (erule notE)
  apply (erule conjE)
  apply assumption