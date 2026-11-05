module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.FullOperator

/-!
# Exact right Fourier multiplication

The source-independent case in item (3) of
`app:ch_regular_base:thm:actual-calculus`: right composition by a smooth
Fourier multiplier of temperate growth is exact multiplication of the
amplitude. The multiplier is realized as an actual inverse Fourier integral
on Schwartz data, and no physical or frequency integrability is postulated.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap
namespace JanetCartan.Pseudodifferential
variable {V : Type} {F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `app:ch_regular_base:thm:actual-calculus`: The inverse Fourier transform of the symbol times
the input Fourier transform. Its pointwise formula is proved below for symbols of temperate
growth. -/
def schwartzFrequencyMultiplier (q : V → ℂ) (u : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  𝓕⁻ (SchwartzMap.smulLeftCLM ℂ q (𝓕 u))

/-- `app:ch_regular_base:thm:actual-calculus`: The constructed Schwartz multiplier has exactly the
prescribed Fourier transform. -/
theorem fourier_schwartzFrequencyMultiplier (q : V → ℂ) (hq : q.HasTemperateGrowth)
    (u : 𝓢(V, ℂ)) (ξ : V) :
    (𝓕 (schwartzFrequencyMultiplier q u) : 𝓢(V, ℂ)) ξ = q ξ * (𝓕 u : 𝓢(V, ℂ)) ξ := by
  simp [schwartzFrequencyMultiplier, FourierTransform.fourier_fourierInv_eq,
    SchwartzMap.smulLeftCLM_apply_apply hq]

/-- `app:ch_regular_base:thm:actual-calculus`: The Schwartz multiplier agrees pointwise with the
actual source-independent integral operator. -/
theorem schwartzFrequencyMultiplier_eq_sourceIndependentOperator
    (q : V → ℂ) (hq : q.HasTemperateGrowth) (u : 𝓢(V, ℂ)) (x : V) :
    schwartzFrequencyMultiplier q u x = sourceIndependentOperator (fun _ ξ ↦ q ξ) u x := by
  rw [schwartzFrequencyMultiplier, SchwartzMap.fourierInv_coe,
    SchwartzMap.smulLeftCLM_apply hq]
  unfold sourceIndependentOperator
  apply congrArg (fun f : V → ℂ ↦ 𝓕⁻ f x)
  funext ξ
  exact mul_comm _ _

/-- `app:ch_regular_base:thm:actual-calculus`: Right Fourier multiplication is exactly amplitude
multiplication, retaining its frequency argument. -/
theorem sourceIndependentOperator_schwartzFrequencyMultiplier
    (a : V → V → F) (q : V → ℂ) (hq : q.HasTemperateGrowth)
    (u : 𝓢(V, ℂ)) (x : V) :
    sourceIndependentOperator a (schwartzFrequencyMultiplier q u) x =
      sourceIndependentOperator (fun x ξ ↦ q ξ • a x ξ) u x := by
  unfold sourceIndependentOperator
  simp_rw [fourier_schwartzFrequencyMultiplier q hq u]
  apply congrArg (fun f : V → F ↦ 𝓕⁻ f x)
  funext ξ
  rw [mul_smul, smul_comm]

/-- `app:ch_regular_base:thm:actual-calculus`: Composition of the actual source-independent
integral operators equals multiplication of the symbols. Fourier inversion discharges the
intermediate transform identity. -/
theorem fullAmplitudeOperator_sourceIndependent_comp_frequencyMultiplier [CompleteSpace F]
    (a : V → V → F) (q : V → ℂ) (hq : q.HasTemperateGrowth)
    (u : 𝓢(V, ℂ)) (x : V) :
    fullAmplitudeOperator (fun x _y ξ ↦ a x ξ)
      (sourceIndependentOperator (fun _ ξ ↦ q ξ) u) x =
      sourceIndependentOperator (fun x ξ ↦ q ξ • a x ξ) u x := by
  have heq : sourceIndependentOperator (fun _ ξ ↦ q ξ) u =
      (schwartzFrequencyMultiplier q u : V → ℂ) :=
    funext fun y ↦ (schwartzFrequencyMultiplier_eq_sourceIndependentOperator q hq u y).symm
  rw [heq, fullAmplitudeOperator_sourceIndependent]
  exact sourceIndependentOperator_schwartzFrequencyMultiplier a q hq u x
end JanetCartan.Pseudodifferential
