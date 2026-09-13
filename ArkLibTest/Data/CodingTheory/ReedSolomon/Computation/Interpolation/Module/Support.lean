import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Module.Support

namespace ReedSolomon.HiddenDerivative.InterpolationModuleTests

open InterpolationModule

example : (JetMonomial.mk 2 [1]).xInterval 3 10 = [0, 1] := by decide
example : (JetMonomial.mk 2 [1]).xInterval 3 8 = [] := by decide
example : (JetMonomial.mk 2 [1]).xInterval 3 7 = [] := by decide
example : (JetMonomial.mk 0 []).xInterval 0 0 = [] := by decide

example (b : JetMonomial) (D d m J A x : ℕ) :
    b.vector x ∈ InterpolationSupportMachine.supportSpec
        (InterpolationSupportMachine.parametersWithBudget D d m J A) ↔
      b.higher.length = d ∧ b.zeroth + b.higher.sum < J ∧
        x ∈ b.xInterval D (m * A) := b.mem_support_iff D d m J A x

end ReedSolomon.HiddenDerivative.InterpolationModuleTests
