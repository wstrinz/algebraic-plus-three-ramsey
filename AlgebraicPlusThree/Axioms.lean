module

public import AlgebraicPlusThree.AlgPlusThree
public import AlgebraicPlusThree.MathlibStatement

/-!
# Axioms report

`lake build` prints, for each advertised theorem, the satisfiability witness, the bridge and the
six-point case, the axioms it depends on. Expected on every line: `[propext, Classical.choice, Quot.sound]`.
-/

#print axioms OAI.EuclideanRamsey.ramsey_alg_plus_three
#print axioms AlgebraicPlusThree.ramsey_alg_plus_three_mathlib
#print axioms AlgebraicPlusThree.ramsey_alg_plus_three_nonvacuous
#print axioms AlgebraicPlusThree.oai_congruent_iff
#print axioms AlgebraicPlusThree.oai_ramsey_iff
#print axioms OAI.EuclideanRamsey.circle_ramsey_of_le_six
