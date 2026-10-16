module

public import AlgebraicPlusThree.AlgPlusThree
public import AlgebraicPlusThree.MathlibStatement

public section

/-!
# Proved solution

`OAI.EuclideanRamsey.ramsey_alg_plus_three` (Theorem B(b)) is proved in
`AlgebraicPlusThree/AlgPlusThree.lean`, from the six-point case `circle_ramsey_of_le_six`
(`AlgebraicPlusThree/SixPoint.lean`) and an explicit field-criterion certificate
(`AlgebraicPlusThree/AlgPlusThreeCore.lean`). `AlgebraicPlusThree.ramsey_alg_plus_three_mathlib` is
proved in `AlgebraicPlusThree/MathlibStatement.lean`, through the OpenAI/Mathlib bridge
`AlgebraicPlusThree/MathlibBridge.lean`. All of it sits on the module-system port of OpenAI's
EuclideanRamsey development (`OAI/`). `Space`, `Congruent` and `Ramsey` come from
`OAI/Combinatorics/EuclideanRamsey/Model.lean`; Comparator checks that they are identical to the
restatements in `Challenge.lean`.
-/
