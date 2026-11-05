module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalTailJets
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalTailSobolev

/-! # Concrete physical-tail Sobolev decay

The jet producer is instantiated at spatial weight `n+1`, closing the analytic
premise of the physical-tail realization for `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
open FourierIntegral FiniteChain.Graph LowBounds Pseudodifferential
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The actual fixed mask plateau produces the full physical-tail estimate,
with no remaining kernel or Sobolev premise. This is applied twice to the SAME
localizer in `app:ch_regular:eq:resolved-angular-tail`. -/
theorem exists_leftLocalizer_adjoint_physicalTail_sobolev_decay
    (mi : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχrange : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (hplateau : ∀ y ∈ Prod.fst '' tsupport mi, y ∈ interior {x | χ x = 1})
    (m N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ →
      ∀ M : H →L[ℂ] H,
      (∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → M u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      ∀ u : H,
        let T := sourceCutMultiplier (r := r) χ hχ.continuous
          (fun x ↦ (Real.norm_of_nonneg (hχrange x).1).trans_le (hχrange x).2)
        MemVectorFourierSobolev (m : ℝ) (((T - 1).comp M.adjoint) u) ∧
        vectorFourierSobolevNorm (m : ℝ) (((T - 1).comp M.adjoint) u) ≤
          C * ρ ^ (n + m) * (L / ρ) ^ N * ‖u‖ := by
  obtain ⟨A, hA, ha⟩ := exists_leftLocalizer_adjoint_physicalTail_sobolev_constant
    (n := n) (r := r) m
  obtain ⟨B, hB, hb⟩ := exists_rightLocalizerScalarKernel_physicalTail_jet_decay
    mi hi his χ hχ hχs hχrange hplateau m (n + 1) N
  refine ⟨A * B, mul_nonneg hA hB, ?_⟩
  intro ρ L hL hLρ M hM u
  have hρ : 0 < ρ := zero_lt_one.trans_le (hL.trans hLρ)
  obtain ⟨hm, hn⟩ := ha ρ hρ.ne' mi hi his χ hχ
    (fun x ↦ (Real.norm_of_nonneg (hχrange x).1).trans_le (hχrange x).2)
    (B * ρ ^ (n + m) * (L / ρ) ^ N) (by positivity)
    (hb ρ L hL hLρ) M hM u
  exact ⟨hm, by simpa only [mul_assoc] using hn⟩

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
