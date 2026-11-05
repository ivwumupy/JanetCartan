module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Estimates.Basic

/-!
# Localized scalar multiplication on Euclidean L²

The product and its distributional Leibniz rule used in
`app:ch_response:eq:response-graded-displacement`,
`app:ch_response:eq:response-graded-derivative`, and
`app:ch_response:eq:response-graded-strain`.
All measures here are literal Euclidean Lebesgue measure.
-/

@[expose] public noncomputable section

open MeasureTheory LineDeriv
open scoped ENNReal ContDiff SchwartzMap
open JanetCartan.AmplitudeBound JanetCartan.Pseudodifferential

namespace JanetCartan.IsometricEmbedding.Reconstruction

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-- The actual L² product in `app:ch_response:eq:response-reconstruction-grading`.
Compact support is only required of the coefficient. -/
def localizedScalarProduct (c : E → ℂ) (hc : ContDiff ℝ ∞ c)
    (hcs : HasCompactSupport c) (u : L2) : L2 :=
  ((hc.continuous.memLp_of_hasCompactSupport hcs : MemLp c ∞).mul
    (Lp.memLp u)).toLp (fun x ↦ c x * u x)

/-- The product representative is pointwise multiplication almost everywhere,
for `app:ch_response:eq:response-graded-displacement`. -/
theorem localizedScalarProduct_ae (c : E → ℂ) (hc : ContDiff ℝ ∞ c)
    (hcs : HasCompactSupport c) (u : L2) :
    localizedScalarProduct c hc hcs u =ᵐ[volume] fun x ↦ c x * u x :=
  MemLp.coeFn_toLp _

/-- The order-zero multiplier estimate for
`app:ch_response:eq:response-graded-displacement`. -/
theorem norm_localizedScalarProduct_le (c : E → ℂ) (hc : ContDiff ℝ ∞ c)
    (hcs : HasCompactSupport c) (u : L2) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖c x‖ ≤ C) :
    ‖localizedScalarProduct c hc hcs u‖ ≤ C * ‖u‖ := by
  have he := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (Lp.memLp (localizedScalarProduct c hc hcs u)).aestronglyMeasurable
    (show ∀ᵐ x ∂volume, ‖localizedScalarProduct c hc hcs u x‖ ≤ C * ‖u x‖ from by
      filter_upwards [localizedScalarProduct_ae c hc hcs u] with x hx
      rw [hx, norm_mul]
      exact mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)) 2
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.memLp u).eLpNorm_ne_top) he
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, ← Lp.norm_def] using hr

/-- Distributional realization of multiplication, for the Leibniz step in
`app:ch_response:eq:response-graded-derivative`. -/
theorem localizedScalarProduct_distribution (c : E → ℂ) (hc : ContDiff ℝ ∞ c)
    (hcs : HasCompactSupport c) (u : L2) :
    (localizedScalarProduct c hc hcs u : 𝓢'(E, ℂ)) =
      TemperedDistribution.smulLeftCLM ℂ c (u : 𝓢'(E, ℂ)) := by
  exact toTemperedDistribution_toLp_pointwise_smul c (hcs.hasTemperateGrowth hc) u
    ((hc.continuous.memLp_of_hasCompactSupport hcs : MemLp c ∞).mul (Lp.memLp u))

/-- The distributional Leibniz rule derived by testing against Schwartz functions,
for `app:ch_response:eq:response-graded-derivative`. -/
theorem localizedScalarProduct_distribution_leibniz (c : E → ℂ) (hc : ContDiff ℝ ∞ c) (hcs : HasCompactSupport c)
    (i : Fin d) (T : 𝓢'(E, ℂ)) :
    ∂_{(EuclideanSpace.single i 1 : E)} (TemperedDistribution.smulLeftCLM ℂ c T) =
      TemperedDistribution.smulLeftCLM ℂ (euclideanCoordinateDerivList [i] c) T +
      TemperedDistribution.smulLeftCLM ℂ c (∂_{(EuclideanSpace.single i 1 : E)} T) := by
  let dc := euclideanCoordinateDerivList [i] c
  have hcg := hcs.hasTemperateGrowth hc
  have hdcg := (hasCompactSupport_euclideanCoordinateDerivList hcs [i]).hasTemperateGrowth
    (contDiff_euclideanCoordinateDerivList hc [i])
  have htest (φ : 𝓢(E, ℂ)) :
      ∂_{(EuclideanSpace.single i 1 : E)} (SchwartzMap.smulLeftCLM ℂ c φ) =
        SchwartzMap.smulLeftCLM ℂ dc φ +
        SchwartzMap.smulLeftCLM ℂ c (∂_{(EuclideanSpace.single i 1 : E)} φ) := by
    ext x
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have he : ⇑(SchwartzMap.smulLeftCLM ℂ c φ) = c * ⇑φ := by
      ext x
      simp [SchwartzMap.smulLeftCLM_apply_apply hcg, smul_eq_mul]
    rw [he, fderiv_mul (hc.differentiable (by simp) x) (φ.differentiable x)]
    simp [SchwartzMap.smulLeftCLM_apply_apply hcg,
      SchwartzMap.smulLeftCLM_apply_apply (show dc.HasTemperateGrowth from hdcg), SchwartzMap.lineDerivOp_apply_eq_fderiv,
      smul_eq_mul, mul_comm, add_comm]
    exact Or.inl rfl
  ext φ
  simp only [TemperedDistribution.lineDerivOp_apply_apply,
    TemperedDistribution.smulLeftCLM_apply_apply, add_apply,
    htest, map_neg, map_add]
  abel

/-- Actual L² representatives satisfy the coefficient product rule, supplying
the induction for `app:ch_response:eq:response-graded-displacement`. -/
theorem localizedScalarProduct_coordinateDerivative
    (c : E → ℂ) (hc : ContDiff ℝ ∞ c) (hcs : HasCompactSupport c)
    {u v : L2} {i : Fin d} (hv : HasEuclideanL2CoordinateDerivative i u v) :
    HasEuclideanL2CoordinateDerivative i (localizedScalarProduct c hc hcs u)
      (localizedScalarProduct (euclideanCoordinateDerivList [i] c)
        (contDiff_euclideanCoordinateDerivList hc [i])
        (hasCompactSupport_euclideanCoordinateDerivList hcs [i]) u +
       localizedScalarProduct c hc hcs v) := by
  change ∂_{(EuclideanSpace.basisFun (Fin d) ℝ i)}
    (localizedScalarProduct c hc hcs u : 𝓢'(E, ℂ)) =
      (Lp.toTemperedDistributionCLM ℂ volume 2) _
  rw [map_add]
  change _ =
    (localizedScalarProduct (euclideanCoordinateDerivList [i] c)
      (contDiff_euclideanCoordinateDerivList hc [i])
      (hasCompactSupport_euclideanCoordinateDerivList hcs [i]) u : 𝓢'(E, ℂ)) +
    (localizedScalarProduct c hc hcs v : 𝓢'(E, ℂ))
  simp only [localizedScalarProduct_distribution, EuclideanSpace.basisFun_apply]
  rw [localizedScalarProduct_distribution_leibniz c hc hcs]
  change ∂_{(EuclideanSpace.basisFun (Fin d) ℝ i)} (u : 𝓢'(E, ℂ)) =
    (v : 𝓢'(E, ℂ)) at hv
  rw [EuclideanSpace.basisFun_apply] at hv
  rw [hv]

end JanetCartan.IsometricEmbedding.Reconstruction
