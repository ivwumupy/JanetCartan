module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.Expectation.Weighted
public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.Expectation.ScalarMass

/-!
# Expectation of the literal separated-sampling blocks

Specialization of the conditional weighted-family deductions to the unchanged
colors and weights of `app:ch_waves:eq:sampling-prefix-normal`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators
namespace JanetCartan.SamplingKernelBounds.Expectation
open SeparatedSampling Sampling
variable {E F ι κ : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {p : ℕ} {ψ : Point → ℝ} {w : ℝ → ℝ} {B P W h : ℝ}

/-- Insert the literal window and color into the weighted expectation interface
(`app:ch_waves:eq:sampling-prefix-normal`). No operator conclusions are inputs. -/
def blockFamily (b : HilbertBasis ι ℂ E)
    (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hψc : Continuous ψ) (hwc : Continuous w)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] F)
    (hTc : ∀ c, Continuous (T c)) (hTS : ∀ c z, IsHilbertSchmidt b (T c z))
    (hSq : ∀ c, Continuous (fun z ↦ hilbertSchmidtSq b (T c z))) :
    WeightedFamily (F := F) b (ShiftIndex p B h) where
  operator q := T (color p q)
  weight q z := ψ z * blockWeight w h q z
  continuous_operator q := hTc (color p q)
  hilbertSchmidt q := hTS (color p q)
  continuous_hilbertSchmidtSq q := hSq (color p q)
  continuous_weight q := hψc.mul (continuous_blockWeight hwc h q)
  compactSupport_weight q := compactSupport_patchWeight hψ q
  nonneg_weight q z := mul_nonneg (hψ.nonneg z) (Finset.prod_nonneg (fun i _ ↦ hw.nonneg (z i / h - (q.val i : ℝ))))

variable (b : HilbertBasis ι ℂ E)
    (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hψc : Continuous ψ) (hwc : Continuous w)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] F)
    (hTc : ∀ c, Continuous (T c)) (hTS : ∀ c z, IsHilbertSchmidt b (T c z))
    (hSq : ∀ c, Continuous (fun z ↦ hilbertSchmidtSq b (T c z)))

/-- The block family has exactly the finite continuum expectation in
`app:ch_waves:eq:sampling-prefix-normal`. -/
theorem blockFamily_expectation_eq :
    (blockFamily (h := h) b hw hψ hψc hwc T hTc hTS hSq).expectation =
      ∑ q ∈ integerCube (blockCutoff p B h),
        ∫ z, (ψ z * blockWeight w h q z) • atomNormal (T (color p q) z) := by
  exact Finset.sum_coe_sort (integerCube (blockCutoff p B h))
    (fun q ↦ ∫ z, (ψ z * blockWeight w h q z) • atomNormal (T (color p q) z))

omit [CompleteSpace E] [CompleteSpace F] in
/-- Mesh-independent mass for the literal block family
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem blockFamily_mass_le (hh : 0 < h) (hh₁ : h ≤ 1) :
    (blockFamily (h := h) b hw hψ hψc hwc T hTc hTS hSq).mass ≤
      countConstant p B * (P * W ^ 3) := by
  change (∑ q : ShiftIndex p B h, ∫ z, ψ z * blockWeight w h q z) ≤ _
  rw [Finset.sum_coe_sort (integerCube (blockCutoff p B h))
    (fun q ↦ ∫ z, ψ z * blockWeight w h q z)]
  exact continuum_mass_le hw hψ hψc hwc hh hh₁

/-- The expectation retains exactly the original samples, colors and nodes
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem blockFamily_eq_sample_expectation (hh : 0 < h) :
    (blockFamily (h := h) b hw hψ hψc hwc T hTc hTS hSq).expectation =
      ∫ ω, ∑ a ∈ samples p B ψ w h (extendedShift ω),
        weight ψ w h (extendedShift ω) a •
          atomNormal (T (color p a.1) (node h (extendedShift ω) a)) ∂shiftLaw p B h := by
  rw [blockFamily_expectation_eq]
  exact (integral_sampleNormal_shiftLaw hw hψ hψc hwc hh T hTc).symm

/-- Literal color mass `m_c`, with the fixed finite block enumeration from
`app:ch_waves:eq:sampling-prefix-normal`. -/
def colorMass (p : ℕ) (B h : ℝ) (w : ℝ → ℝ) (c : Fin 3 → Fin (p + 1))
    (z : Point) : ℝ :=
  ∑ q ∈ (integerCube (blockCutoff p B h)).filter (fun q ↦ color p q = c), blockWeight w h q z

/-- Regrouping gives exactly the manuscript's `∑c ∫ ψ m_c T_c T_c*`
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem blockFamily_expectation_eq_colors :
    (blockFamily (h := h) b hw hψ hψc hwc T hTc hTS hSq).expectation =
      ∑ c, ∫ z, (ψ z * colorMass p B h w c z) • atomNormal (T c z) := by
  classical
  rw [blockFamily_expectation_eq]
  rw [← Finset.sum_fiberwise (integerCube (blockCutoff p B h)) (color p)
    (fun q ↦ ∫ z, (ψ z * blockWeight w h q z) • atomNormal (T (color p q) z))]
  apply Finset.sum_congr rfl
  intro c _
  simp only [colorMass, Finset.mul_sum, Finset.sum_smul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q hq
    rw [(Finset.mem_filter.mp hq).2]
  · intro q hq
    rw [← (Finset.mem_filter.mp hq).2]
    exact integrable_blockIntegrand hψ hψc hwc h T hTc q

/-- The mesh-independent `C Λ^n` trace estimate for the literal expectation
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem blockFamily_trace_le_scale [Countable κ] (a : HilbertBasis κ ℂ F)
    (hh : 0 < h) (hh₁ : h ≤ 1) (n : ℕ) (Λ C_HS : ℝ)
    (hHS : ∀ c z, hilbertSchmidtSq b (T c z) ≤ C_HS * Λ ^ n) :
    positiveTrace a (blockFamily (h := h) b hw hψ hψc hwc T hTc hTS hSq).expectation ≤
      (C_HS * (countConstant p B * (P * W ^ 3))) * Λ ^ n := by
  have hH : 0 ≤ C_HS * Λ ^ n :=
    (show 0 ≤ hilbertSchmidtSq b (T (fun _ ↦ 0) 0) from
      tsum_nonneg (fun _ ↦ sq_nonneg _)).trans (hHS _ _)
  exact WeightedFamily.trace_le_scale _ a n Λ C_HS _ hH
    (fun q z ↦ hHS (color p q) z)
    (blockFamily_mass_le b hw hψ hψc hwc T hTc hTS hSq hh hh₁)

end JanetCartan.SamplingKernelBounds.Expectation
