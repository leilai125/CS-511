theory HealthyOrIll
  imports Main
begin

text\<open> Apply style \<close>
lemma HealthyOrIll : "(Healthy \<or> Ill) \<and> (Healthy \<longrightarrow> Travel) \<and> \<not>Ill \<longrightarrow> Travel"
  apply (rule impI)
  apply (erule conjE)
  apply (erule conjE)
  apply (erule disjE)
   apply (erule impE)
    apply assumption
   apply assumption
  apply (erule notE)
  apply assumption
  done