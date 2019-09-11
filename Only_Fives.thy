theory
  Only_Fives
imports
  Main
begin

inductive only_fives :: ‹nat list ⇒ bool› where
  ‹only_fives []› |
  ‹⟦only_fives xs⟧ ⟹ only_fives (xs @ [5])›

theorem only_fives_concat:
  assumes ‹only_fives xs› and ‹only_fives ys›
  shows ‹only_fives (xs @ ys)›
using assms proof (induction ys rule: List.rev_induct)
  case Nil
  then show ‹only_fives (xs @ [])›
    by auto
next
  case (snoc y ys)
  hence ‹only_fives ys›
    using only_fives.simps by blast
  hence ‹only_fives (xs @ ys)›
    by (simp add: snoc.IH snoc.prems(1))
  moreover have ‹y = 5›
    using only_fives.cases snoc.prems(2) by auto
  ultimately show ‹only_fives (xs @ ys @ [y])›
    using only_fives.intros(2) by force
qed

end
