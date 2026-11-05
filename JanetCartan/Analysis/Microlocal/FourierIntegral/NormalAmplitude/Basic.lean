module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.Kernel
public import JanetCartan.Analysis.Microlocal.NormalComparison.ChangeOfVariables

/-!
# The full matrix cross-normal amplitude

Exact substitution in `app:ch_regular_base:eq:actual-normal-amplitude`, with
physical covectors and the Lebesgue measure. This is an identity of the displayed
Bochner kernel integrals; passage from regularizations to oscillatory operators
belongs to the consuming finite FIO calculus.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}

/-- The two independent positions and the physical covector in
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
abbrev NormalVariables (n : ℕ) := Euclidean n × (Euclidean n × Euclidean n)

/-- The matrix numerator of the cross-normal, retaining both amplitudes and
all their cutoffs (`app:ch_regular_base:eq:actual-normal-amplitude`). -/
def crossNormalNumerator
    (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (x y η : Euclidean n) : Matrix (Fin r) (Fin r) ℂ :=
  A x η * (B y η).conjTranspose

/-- The full inverse-Jacobian amplitude, before zero extension
(`app:ch_regular_base:eq:actual-normal-amplitude`). -/
def crossNormalAmplitude
    (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (J : Euclidean n → Euclidean n → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (x y ξ : Euclidean n) : Matrix (Fin r) (Fin r) ℂ :=
  |(J x y (η x y ξ)).det|⁻¹ • crossNormalNumerator A B x y (η x y ξ)

/-- Literal zero extension off the joint inverse chart. No cutoffs are
removed from the numerator (`app:ch_regular_base:eq:actual-normal-amplitude`). -/
def extendedCrossNormalAmplitude (Ω : Set (NormalVariables n))
    (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (J : Euclidean n → Euclidean n → Euclidean n → Euclidean n →L[ℝ] Euclidean n) :
    NormalVariables n → Matrix (Fin r) (Fin r) ℂ :=
  Ω.indicator (fun q ↦ crossNormalAmplitude A B η J q.1 q.2.1 q.2.2)

/-- Exact cross-normal kernel in physical covectors, normalized by `(2π)⁻ⁿ`
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
def crossNormalKernel (D : Set (Euclidean n))
    (S : Euclidean n → Euclidean n → ℝ)
    (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (x y : Euclidean n) : Matrix (Fin r) (Fin r) ℂ :=
  ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ u in D,
    NormalComparison.oscillatoryFactor 1 (S x u - S y u) •
      crossNormalNumerator A B x y u

/-- The exact matrix cross-normal substitution, applying the shared Bochner
Jacobian theorem to the entire matrix numerator. Phase linearization is proved
by the segment FTC, not assumed. Source: `app:ch_regular_base:eq:actual-normal-amplitude`.
The actual Hamilton/compatible geometry producer must supply the inverse and gap. -/
theorem crossNormalKernel_eq_integral_image
    (D : Set (Euclidean n)) (hD : MeasurableSet D)
    (S : Euclidean n → Euclidean n → ℝ)
    (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (J : Euclidean n → Euclidean n → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (x y : Euclidean n)
    (hS : ∀ u ∈ D, ∀ t ∈ uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ (fun z ↦ S z u) (y + t • (x - y)))
    (hint : ∀ u ∈ D, IntervalIntegrable
      (fun t : ℝ ↦ fderiv ℝ (fun z ↦ S z u) (y + t • (x - y))) volume 0 1)
    (hΞ : ∀ u ∈ D, HasFDerivWithinAt (NormalComparison.averagedGradient S x y)
      (J x y u) D u)
    (hinj : InjOn (NormalComparison.averagedGradient S x y) D)
    (hη : ∀ u ∈ D, η x y (NormalComparison.averagedGradient S x y u) = u)
    {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ u ∈ D, δ ≤ |(J x y u).det|) :
    crossNormalKernel D S A B x y =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ •
        ∫ ξ in (NormalComparison.averagedGradient S x y) '' D,
          NormalComparison.oscillatoryFactor 1 (inner ℝ (x - y) ξ) •
            crossNormalAmplitude A B η J x y ξ := by
  unfold crossNormalKernel
  congr 1
  rw [NormalComparison.integral_eq_inverse_jacobian_integral D hD
    (NormalComparison.averagedGradient S x y) (η x y) (J x y) hΞ hinj hη
    (fun u hu ↦ abs_pos.mp (hδ.trans_le (hgap u hu)))]
  apply setIntegral_congr_fun (measurable_image_of_fderivWithin hD hΞ hinj)
  rintro ξ ⟨u, hu, rfl⟩
  simp only [crossNormalAmplitude, hη u hu,
    NormalComparison.phase_sub_eq_inner_averagedGradient S x y u (hS u hu) (hint u hu)]
  exact smul_comm _ _ _

/-- Whole-space version with the literal zero extension on each chart fiber.
The normalization and all pulled-back cutoffs remain exact
(`app:ch_regular_base:eq:actual-normal-amplitude`). -/
theorem crossNormalKernel_eq_integral_zeroExtension
    (D : Set (Euclidean n)) (hD : MeasurableSet D)
    (S : Euclidean n → Euclidean n → ℝ)
    (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (J : Euclidean n → Euclidean n → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (x y : Euclidean n)
    (hS : ∀ u ∈ D, ∀ t ∈ uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ (fun z ↦ S z u) (y + t • (x - y)))
    (hint : ∀ u ∈ D, IntervalIntegrable
      (fun t : ℝ ↦ fderiv ℝ (fun z ↦ S z u) (y + t • (x - y))) volume 0 1)
    (hΞ : ∀ u ∈ D, HasFDerivWithinAt (NormalComparison.averagedGradient S x y)
      (J x y u) D u)
    (hinj : InjOn (NormalComparison.averagedGradient S x y) D)
    (hη : ∀ u ∈ D, η x y (NormalComparison.averagedGradient S x y u) = u)
    {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ u ∈ D, δ ≤ |(J x y u).det|) :
    crossNormalKernel D S A B x y =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ ξ,
        NormalComparison.oscillatoryFactor 1 (inner ℝ (x - y) ξ) •
          extendedCrossNormalAmplitude
            {q | q.2.2 ∈ (NormalComparison.averagedGradient S q.1 q.2.1) '' D}
            A B η J (x, (y, ξ)) := by
  rw [crossNormalKernel_eq_integral_image D hD S A B η J x y
    hS hint hΞ hinj hη hδ hgap,
    ← integral_indicator (measurable_image_of_fderivWithin hD hΞ hinj)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  by_cases hξ : ξ ∈ (NormalComparison.averagedGradient S x y) '' D <;>
    simp only [extendedCrossNormalAmplitude, Set.indicator, Set.mem_ofPred_eq]
    <;> simp [hξ]

end JanetCartan.FourierIntegral
