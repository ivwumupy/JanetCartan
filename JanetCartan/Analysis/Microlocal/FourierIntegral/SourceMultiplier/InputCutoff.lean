module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceMultiplier.OperatorLimit

/-!
# The fixed input Fourier cutoff

This is the vector-valued, physical-frequency version of
`Pseudodifferential.schwartzFrequencyMultiplier`. The factor `2π` in the
multiplier argument is essential: the phase and `Π_in` use physical covectors,
whereas Mathlib's Fourier transform uses cycles. The final identity retains
`Π_in` on both sides of `app:ch_regular_base:eq:fixed-source-multiplication`.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open scoped Matrix.Norms.Frobenius RealInnerProductSpace
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}

/-- The actual fixed input multiplier in physical covectors. Temperate growth
of the fixed smooth cutoff ensures that its product with Schwartz frequency
data is Schwartz. Source: `app:ch_regular_base:eq:fixed-source-multiplication`. -/
def sourceInputFrequencyCutoff (q : Euclidean n → ℂ) (hq : q.HasTemperateGrowth)
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ)) :
    SchwartzMap (Euclidean n) (Fin r → ℂ) :=
  𝓕⁻ (SchwartzMap.bilinLeftCLM
    (ContinuousLinearMap.lsmul ℂ ℂ (E := Fin r → ℂ)).flip
    (show (fun ξ : Euclidean n ↦ q ((2 * Real.pi) • ξ)).HasTemperateGrowth by
      fun_prop) (𝓕 u))

/-- The cutoff acts at precisely the original physical input covector, with no
suppressed normalization. Source:
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem sourceInputFourierTransform_frequencyCutoff
    (q : Euclidean n → ℂ) (hq : q.HasTemperateGrowth)
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ)) (η : Euclidean n) :
    sourceInputFourierTransform (sourceInputFrequencyCutoff q hq u) η =
      q η • sourceInputFourierTransform u η := by
  unfold sourceInputFourierTransform sourceInputFrequencyCutoff
  rw [fourier_fourierInv_eq]
  change q ((2 * Real.pi) • ((2 * Real.pi)⁻¹ • η)) •
    (𝓕 u : SchwartzMap (Euclidean n) (Fin r → ℂ)) ((2 * Real.pi)⁻¹ • η) = _
  rw [smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
  rfl

/-- Right composition by the fixed input cutoff multiplies the source-independent
graph amplitude at that same physical covector. This identifies `Π_in` as an
actual Fourier operator in `app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem graphOperator_sourceInputFrequencyCutoff
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (q : Euclidean n → ℂ) (hq : q.HasTemperateGrowth)
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ)) (x : Euclidean n) :
    graphOperator S (fun z _ η ↦ A z η) (sourceInputFrequencyCutoff q hq u) x =
      graphOperator S (fun z _ η ↦ q η • A z η) u x := by
  simp_rw [graphOperator_eq_sourceFourierIntegral,
    sourceInputFourierTransform_frequencyCutoff, Matrix.mulVec_smul, Matrix.smul_mulVec]

/-- `(T_A m) Π_in = T_b Π_in` for the actual source-first integrals on Schwartz
data. The supplied `S,A` retain their angular and low-frequency extensions, and
`q` is the fixed physical input Fourier cutoff, including all its transitions.
No plateau property is needed for this equality; the parent construction chooses
`q = 1` on the specified graph support. Source:
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem graphOperator_sourceSymbol_inputCutoff
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (m : SchwartzMap (Euclidean n) ℂ)
    (q : Euclidean n → ℂ) (hq : q.HasTemperateGrowth)
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ)) (x : Euclidean n)
    (hS : Continuous (S x)) (hA : Continuous (A x))
    (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    (hbound : ∀ η, ‖A x η‖ ≤ C * (1 + ‖η‖ ^ k)) :
    graphOperator S (fun z _ η ↦ A z η)
      (fun y ↦ m y • sourceInputFrequencyCutoff q hq u y) x =
      graphOperator S (fun z _ η ↦ sourceSymbol S A m z η)
        (sourceInputFrequencyCutoff q hq u) x :=
  graphOperator_sourceSymbol S A m (sourceInputFrequencyCutoff q hq u) x
    hS hA C hC k hbound

end JanetCartan.FourierIntegral
