Always assume Theorem~\ref{thm:thm1} (stated in `AndrewsDhar_arXivPaper.tex`).  That is, the formalization should have the following shape:
```lean
/-- the statement of theorem 1 -/
def Thm1 (...) : Prop := ...

lemma intermediate_lemma (thm1 : Thm1 ...) : statement_of_intermediate_lemma := by sorry

theorem prop_gamma (thm1 : Thm1 ...) : statement_of_prop_gamma := by sorry
```
