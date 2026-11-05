module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.FrequencyCutoff.Multipliers.L2

/-! # Schwartz realization and literal graph factorization

Exact agreement of the physical-frequency regularization on Schwartz inputs,
Lebesgue L², and source-first graphs (`app:ch_regular_base:thm:actual-calculus`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory FourierTransform
namespace JanetCartan.FourierIntegral.LowBounds.FrequencyCutoff
variable {n r : ℕ}
local notation "ℰ" => Euclidean n
local notation "𝒱" => EuclideanSpace ℂ (Fin r)

/-- The actual Schwartz Fourier cutoff in Step 1 of
`app:ch_regular_base:thm:actual-calculus`; works for both coordinate and Hilbert fibers. -/
def schwartzMultiplier (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    (j : ℕ) : SchwartzMap ℰ F →L[ℂ] SchwartzMap ℰ F :=
  SchwartzMap.fourierMultiplierCLM F (cycleCutoff j)

/-- Fourier-side action of the Schwartz cutoff (same Step 1). -/
theorem fourier_schwartzMultiplier {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] (j : ℕ) (u : SchwartzMap ℰ F) :
    𝓕 (schwartzMultiplier F j u) = SchwartzMap.smulLeftCLM F (cycleCutoff j) (𝓕 u) := by
  simp [schwartzMultiplier, SchwartzMap.fourierMultiplierCLM_apply]

/-- Exact agreement with the L² operator, proving Schwartz preservation for
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem multiplier_toLp (j : ℕ) (u : SchwartzMap ℰ 𝒱) :
    multiplier j (u.toLp 2) = (schwartzMultiplier 𝒱 j u).toLp 2 := by
  rw [multiplier_apply, SchwartzMap.toLp_fourier_eq]
  have hm : frequencyMultiplication j ((𝓕 u).toLp 2) =
      (SchwartzMap.smulLeftCLM 𝒱 (cycleCutoff j) (𝓕 u)).toLp 2 := by
    apply Lp.ext
    filter_upwards [frequencyMultiplication_coeFn j ((𝓕 u).toLp 2),
      (𝓕 u).coeFn_toLp 2,
      (SchwartzMap.smulLeftCLM 𝒱 (cycleCutoff j) (𝓕 u)).coeFn_toLp 2] with ξ hm hu hs
    rw [hm, hu, hs, SchwartzMap.smulLeftCLM_apply (cycleCutoff_hasTemperateGrowth j)]
  rw [hm, SchwartzMap.toLp_fourierInv_eq]
  rfl

/-- The standard finite-fiber continuous linear equivalence applied to Schwartz
inputs; the consumer is `multiplier_toEuclideanSchwartz_toLp` (same Step 1). -/
def toEuclideanSchwartz :
    SchwartzMap ℰ (Fin r → ℂ) →L[ℂ] SchwartzMap ℰ 𝒱 :=
  SchwartzMap.postcompCLM
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)).symm.toContinuousLinearMap

/-- Pointwise bridge to the exact Euclidean fibers of `VectorGraph` (same Step 1). -/
theorem toEuclideanSchwartz_apply (u : SchwartzMap ℰ (Fin r → ℂ)) (x : ℰ) :
    toEuclideanSchwartz u x = WithLp.toLp 2 (u x) := rfl

/-- Fourier transformation commutes exactly with the finite-fiber bridge,
used by the literal graph factorization in the same Step 1. -/
theorem toEuclideanSchwartz_fourier (u : SchwartzMap ℰ (Fin r → ℂ)) :
    toEuclideanSchwartz (𝓕 u) = 𝓕 (toEuclideanSchwartz u) := by
  let e := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)).symm
  apply SchwartzMap.ext
  intro ξ
  change e (𝓕 (u : ℰ → Fin r → ℂ) ξ) =
    𝓕 (fun x ↦ e (u x)) ξ
  simp only [Real.fourier_eq']
  rw [← e.integral_comp_comm]
  congr 1

/-- The same cutoff acts on coordinate and Euclidean Schwartz fibers,
without a norm-equivalence constant (same Step 1). -/
theorem toEuclideanSchwartz_schwartzMultiplier (j : ℕ)
    (u : SchwartzMap ℰ (Fin r → ℂ)) :
    toEuclideanSchwartz (schwartzMultiplier (Fin r → ℂ) j u) =
      schwartzMultiplier 𝒱 j (toEuclideanSchwartz u) := by
  apply (fourierEquiv ℂ (SchwartzMap ℰ 𝒱)).injective
  change 𝓕 (toEuclideanSchwartz (schwartzMultiplier (Fin r → ℂ) j u)) =
    𝓕 (schwartzMultiplier 𝒱 j (toEuclideanSchwartz u))
  rw [← toEuclideanSchwartz_fourier, fourier_schwartzMultiplier,
    fourier_schwartzMultiplier, ← toEuclideanSchwartz_fourier]
  apply SchwartzMap.ext
  intro ξ
  simp only [toEuclideanSchwartz_apply,
    SchwartzMap.smulLeftCLM_apply (cycleCutoff_hasTemperateGrowth j)]
  rfl

/-- Exact L² agreement for the coordinate Schwartz inputs of the literal graph
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem multiplier_toEuclideanSchwartz_toLp (j : ℕ)
    (u : SchwartzMap ℰ (Fin r → ℂ)) :
    multiplier j ((toEuclideanSchwartz u).toLp 2) =
      (toEuclideanSchwartz (schwartzMultiplier (Fin r → ℂ) j u)).toLp 2 := by
  rw [multiplier_toLp, toEuclideanSchwartz_schwartzMultiplier]

/-- In physical covectors the Schwartz multiplier is exactly `χ_j(η)`,
consumed by `graphOperator_eq_graphOperator_schwartzMultiplier` (same Step 1). -/
theorem sourceInputFourierTransform_schwartzMultiplier (j : ℕ)
    (u : SchwartzMap ℰ (Fin r → ℂ)) (η : ℰ) :
    sourceInputFourierTransform (schwartzMultiplier (Fin r → ℂ) j u) η =
      complexPhysicalCutoff j η • sourceInputFourierTransform u η := by
  change 𝓕 (schwartzMultiplier (Fin r → ℂ) j u) ((2 * Real.pi)⁻¹ • η) =
    complexPhysicalCutoff j η • 𝓕 u ((2 * Real.pi)⁻¹ • η)
  rw [fourier_schwartzMultiplier,
    SchwartzMap.smulLeftCLM_apply (cycleCutoff_hasTemperateGrowth j)]
  simp only [cycleCutoff, smul_smul,
    mul_inv_cancel₀ (show 2 * Real.pi ≠ 0 by positivity), one_smul]

/-- Literal source-first graph identity for arbitrary phase and amplitude.
No bounded uncut graph or integrability hypothesis is used: source integration
is evaluated on Schwartz data first. Source:
`app:ch_regular_base:thm:actual-calculus`, exact right Fourier multiplication. -/
theorem graphOperator_eq_graphOperator_schwartzMultiplier
    (S : ℰ → ℰ → ℝ) (A : ℰ → ℰ → Matrix (Fin r) (Fin r) ℂ)
    (j : ℕ) (u : SchwartzMap ℰ (Fin r → ℂ)) :
    graphOperator S (fun x _ η ↦ complexPhysicalCutoff j η • A x η) u =
      graphOperator S (fun x _ η ↦ A x η) (schwartzMultiplier (Fin r → ℂ) j u) := by
  funext x
  rw [graphOperator_eq_sourceFourierIntegral, graphOperator_eq_sourceFourierIntegral]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  rw [sourceInputFourierTransform_schwartzMultiplier, Matrix.smul_mulVec,
    Matrix.mulVec_smul]

end JanetCartan.FourierIntegral.LowBounds.FrequencyCutoff
