module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalTailSobolev.Realization
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalTailSobolev.Vector

/-!
# Physical-tail kernel jets give the actual Sobolev operator bound

This is the conditional kernel-to-operator deduction for both physical
tails in `actualAngularPDO_sub_identity_comp_rightLocalizer_eq_tails`,
and hence `app:ch_regular:eq:resolved-angular-tail` and
`app:ch_regular:eq:chain-tail`. It retains Euclidean volume, the Euclidean
fiber norm, the exact right-quantized symbol and the physical `2π` convention.

The sole remaining quantitative input is `B ≥ 0` and, for every `j ≤ m`,
`(1 + ‖x-y‖)^(n+1) * ‖iteratedFDeriv ℝ j K_y x‖ ≤ B`, where
`K_y x = ((1 - χ x : ℝ) : ℂ) * rightLocalizerScalarKernel ρ mi x y`.
Its actual producer is `PhysicalTailJets` (fleet task
`jc-identity-physical-tail-kernel-jets`) at spatial order `n+1`, with
`B = Cjet * ρ^(n+m) * (L/ρ)^N`. The fixed physical plateau is used by that
producer. The parent must instantiate this exact bound on the same masks;
this module does not claim the unconditional rapid-decay estimate.

The proofs construct classical output jets on compact tests, derive their
L² bounds by Schur, construct their weak jets, apply the existing Fourier
comparison, and extend by density. The final endpoint uses the same
`M.adjoint` as `TerminalTails`, with no new realization hypothesis beyond
the original left-localizer action.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect

open FourierIntegral FiniteChain.Graph LowBounds Pseudodifferential PhysicalTailSobolev

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- Finite output jets of the actual physical-tail kernel imply an
all-data L²-to-Fourier-Sobolev bound for the original right localizer.
The literal action on dense graph tests suffices. The constant depends
only on dimension, fiber dimension and order, before the symbol, mask,
scale and kernel budget (`app:ch_regular:eq:chain-tail`). -/
theorem exists_rightLocalizer_physicalTail_sobolev_constant (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ), ρ ≠ 0 →
      ∀ (mi : LocalizerSymbol n), ContDiff ℝ ∞ mi → HasCompactSupport mi →
      ∀ (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχb : ∀ x, ‖χ x‖ ≤ 1),
      ∀ B : ℝ, 0 ≤ B →
      (∀ j ≤ m, ∀ x y : E,
        (1 + ‖x - y‖) ^ (n + 1) *
          ‖iteratedFDeriv ℝ j
            (fun z ↦ ((1 - χ z : ℝ) : ℂ) * rightLocalizerScalarKernel ρ mi z y) x‖ ≤ B) →
      ∀ R : H →L[ℂ] H,
      (∀ u : graphTestSpace n r, R (graphTestToLp u) =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (rightLocalizer ρ mi (fun y ↦ (u.val y).ofLp) x)) →
      ∀ u : H,
        MemVectorFourierSobolev (m : ℝ)
          (((sourceCutMultiplier χ hχ.continuous hχb - 1).comp R) u) ∧
        vectorFourierSobolevNorm (m : ℝ)
          (((sourceCutMultiplier χ hχ.continuous hχb - 1).comp R) u) ≤ C * B * ‖u‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_physicalTail_vector_fourierSobolev_constant (n := n) (r := r) m
  refine ⟨C, hC, ?_⟩
  intro ρ hρ mi hi his χ hχ hχb B hB hb R hR u
  apply hbound (signedRightLocalizerPhysicalTailKernel ρ mi χ)
    (contDiff_signedRightLocalizerPhysicalTailKernel_joint hρ mi hi his χ hχ) B hB
    _ ((sourceCutMultiplier χ hχ.continuous hχb - 1).comp R)
    (signedRightLocalizerPhysicalTail_graphTest_action hρ mi hi.continuous his
      χ hχ.continuous hχb R hR) u
  intro j hj x y
  rw [norm_iteratedFDeriv_signedRightLocalizerPhysicalTailKernel]
  exact hb j hj x y

/-- The endpoint for the SAME left-localizer adjoint occurring in both
physical tails of `actualAngularPDO_sub_identity_comp_rightLocalizer_eq_tails`.
The original left action determines its adjoint uniquely via the existing
bounded-localizer constructor. No right action, weak-derivative identity,
Sobolev-membership premise or operator-decay premise is added.

The parent supplies the displayed `hjets` from `PhysicalTailJets` at spatial
weight `n+1` and `B = Cjet * ρ^(n+m) * (L/ρ)^N`, using the actual output or
source mask. This theorem is the conditional Sobolev deduction, not the
unconditional rapid-decay construction
(`app:ch_regular:eq:resolved-angular-tail`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_leftLocalizer_adjoint_physicalTail_sobolev_constant (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ), ρ ≠ 0 →
      ∀ (mi : LocalizerSymbol n), ContDiff ℝ ∞ mi → HasCompactSupport mi →
      ∀ (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχb : ∀ x, ‖χ x‖ ≤ 1),
      ∀ B : ℝ, 0 ≤ B →
      (∀ j ≤ m, ∀ x y : E,
        (1 + ‖x - y‖) ^ (n + 1) *
          ‖iteratedFDeriv ℝ j
            (fun z ↦ ((1 - χ z : ℝ) : ℂ) * rightLocalizerScalarKernel ρ mi z y) x‖ ≤ B) →
      ∀ M : H →L[ℂ] H,
      (∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → M u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      ∀ u : H,
        MemVectorFourierSobolev (m : ℝ)
          (((sourceCutMultiplier χ hχ.continuous hχb - 1).comp M.adjoint) u) ∧
        vectorFourierSobolevNorm (m : ℝ)
          (((sourceCutMultiplier χ hχ.continuous hχb - 1).comp M.adjoint) u) ≤ C * B * ‖u‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_rightLocalizer_physicalTail_sobolev_constant (n := n) (r := r) m
  refine ⟨C, hC, ?_⟩
  intro ρ hρ mi hi his χ hχ hχb B hB hjets M hM u
  exact hbound ρ hρ mi hi his χ hχ hχb B hB hjets M.adjoint
    (rightLocalizer_graphTest_action_of_ae ρ mi M.adjoint
      (rightLocalizer_adjoint_ae_of_leftLocalizer hρ mi hi.continuous his M hM)) u

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
