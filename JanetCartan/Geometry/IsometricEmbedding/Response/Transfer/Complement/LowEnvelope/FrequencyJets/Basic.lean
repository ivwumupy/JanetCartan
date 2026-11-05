module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.OutputJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.FourierReconstruction
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ReverseDerivative.Weighted

/-!
# Literal demodulated graphs and their Fourier reconstruction

The order-zero identities and original target supports used by frequency
differentiation in `app:ch_response:thm:response-literal-transfer`. The full
amplitude is arbitrary, so the complete complement and the weighted inverse
retain every cutoff and both physical positions. The datum has only physical
L² regularity and low Fourier support.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.LowEnvelope

open FourierIntegral NormalComparison JanetCartan.Localization

variable {n r : ℕ}

/-- The literal forward graph with its two original carriers, for
`app:ch_response:thm:response-literal-transfer`. -/
def forwardDemodulatedGraph (S : Euclidean n → Euclidean n → ℝ)
    (φ : Euclidean n → ℝ) (A : FullAmplitude n r) (ζ : Euclidean n) (ρ : ℝ)
    (f : Euclidean n → Fin r → ℂ) (x : Euclidean n) : Fin r → ℂ :=
  carrier (-ρ) φ x •
    graphOperator S A (fun y ↦ carrier ρ (fun z ↦ inner ℝ z ζ) y • f y) x

/-- The literal reverse graph with the reversed carrier pair, for
`app:ch_response:thm:response-literal-transfer`. The amplitude may be
`reverseFullAmplitude` or its complete complementary amplitude. -/
def reverseDemodulatedGraph (S : Euclidean n → Euclidean n → ℝ)
    (φ : Euclidean n → ℝ) (A : FullAmplitude n r) (ζ : Euclidean n) (ρ : ℝ)
    (f : Euclidean n → Fin r → ℂ) (y : Euclidean n) : Fin r → ℂ :=
  carrier (-ρ) (fun z ↦ inner ℝ z ζ) y •
    ReverseDerivative.reverseGraph S A (fun x ↦ carrier ρ φ x • f x) y

private theorem carrier_neg_eq (ρ : ℝ) (φ : Euclidean n → ℝ) (x : Euclidean n) :
    carrier (-ρ) φ x = Complex.exp ((-(ρ * φ x) : ℂ) * Complex.I) := by
  simp only [carrier, neg_mul, Complex.ofReal_neg, Complex.ofReal_mul]
  congr 1
  ring

/-- Exact demodulated forward reconstruction, with the paper's single outer
`(2π)⁻ⁿ`. This is the order-zero case consumed by frequency differentiation in
`app:ch_response:thm:response-literal-transfer`; no physical L¹ premise is used. -/
theorem forwardDemodulatedGraph_lowSupport_reconstruction
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (ζ : Euclidean n) (ρ : ℝ) (x : Euclidean n)
    (ha : ∀ η, Continuous (fun y ↦ A x y η))
    (hc : ∀ η, HasCompactSupport (fun y ↦ A x y η))
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hs : ∀ᵐ θ ∂volume, Λ < ‖θ‖ → paperL2FourierTransform f θ = 0) :
    forwardDemodulatedGraph S φ A ζ ρ (fun y ↦ ⇑(f y)) x =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ η, ∫ θ,
        (sourceKernel (forwardSourcePhase (fun z ξ ↦ S z ξ - ρ * φ z)
          ζ ρ x η θ) A x η).mulVec (paperL2FourierTransform f θ) := by
  unfold forwardDemodulatedGraph
  rw [graphOperator_lowSupport_reconstruction S A ζ ρ x ha hc f hΛ hs,
    smul_comm, ← integral_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with θ
  have he : forwardSourcePhase (fun z ξ ↦ S z ξ - ρ * φ z) ζ ρ x η θ =
      fun y ↦ forwardSourcePhase S ζ ρ x η θ y - ρ * φ x := by
    funext y
    unfold forwardSourcePhase
    ring
  rw [he, sourceKernel_sub_const, Matrix.smul_mulVec, carrier_neg_eq]
  simp only [Complex.ofReal_mul]

/-- Exact demodulated reverse reconstruction, including its nonlinear source
phase and original matrix order (`app:ch_response:thm:response-literal-transfer`). -/
theorem reverseDemodulatedGraph_lowSupport_reconstruction
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (ζ : Euclidean n) (ρ : ℝ) (y : Euclidean n)
    (hφ : Continuous φ) (hS : ∀ η, Continuous (fun x ↦ S x η))
    (ha : ∀ η, Continuous (fun x ↦ A y x η))
    (hc : ∀ η, HasCompactSupport (fun x ↦ A y x η))
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hs : ∀ᵐ θ ∂volume, Λ < ‖θ‖ → paperL2FourierTransform f θ = 0) :
    reverseDemodulatedGraph S φ A ζ ρ (fun x ↦ ⇑(f x)) y =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ η, ∫ θ,
        (sourceKernel (fun x ↦ reverseSourcePhase S φ ρ y η θ x -
          ρ * inner ℝ y ζ) A y η).mulVec (paperL2FourierTransform f θ) := by
  unfold reverseDemodulatedGraph ReverseDerivative.reverseGraph
  rw [reverseGraph_lowSupport_reconstruction S A φ hφ ρ y hS ha hc f hΛ hs,
    smul_comm, ← integral_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with θ
  rw [sourceKernel_sub_const, Matrix.smul_mulVec, carrier_neg_eq]
  simp only [Complex.ofReal_mul]

/-- The original closed target support contains the literal forward output.
No smoothness or integral estimate is needed for this support assertion in
`app:ch_response:thm:response-literal-transfer`. -/
theorem tsupport_forwardDemodulatedGraph_subset
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (ζ : Euclidean n) (ρ : ℝ)
    (f : Euclidean n → Fin r → ℂ) {K : Set (Euclidean n)} (hK : IsClosed K)
    (hs : ∀ x y η, x ∉ K → A x y η = 0) :
    tsupport (forwardDemodulatedGraph S φ A ζ ρ f) ⊆ K := by
  apply closure_minimal ?_ hK
  intro x hx
  by_contra hn
  exact hx (by simp [forwardDemodulatedGraph, graphOperator, hs x _ _ hn])

/-- The reverse graph keeps its own original target cutoff, with the physical
positions in the reverse order (`app:ch_response:thm:response-literal-transfer`). -/
theorem tsupport_reverseDemodulatedGraph_subset
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (ζ : Euclidean n) (ρ : ℝ)
    (f : Euclidean n → Fin r → ℂ) {K : Set (Euclidean n)} (hK : IsClosed K)
    (hs : ∀ y x η, y ∉ K → A y x η = 0) :
    tsupport (reverseDemodulatedGraph S φ A ζ ρ f) ⊆ K := by
  apply closure_minimal ?_ hK
  intro y hy
  by_contra hn
  exact hy (by simp [reverseDemodulatedGraph, ReverseDerivative.reverseGraph, hs y _ _ hn])

/-- Compactness of the original forward target support is preserved in
`app:ch_response:thm:response-literal-transfer`. -/
theorem hasCompactSupport_forwardDemodulatedGraph
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (ζ : Euclidean n) (ρ : ℝ)
    (f : Euclidean n → Fin r → ℂ) {K : Set (Euclidean n)} (hK : IsCompact K)
    (hs : ∀ x y η, x ∉ K → A x y η = 0) :
    HasCompactSupport (forwardDemodulatedGraph S φ A ζ ρ f) :=
  hK.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_forwardDemodulatedGraph_subset S φ A ζ ρ f hK.isClosed hs)

/-- Compactness of the original reverse target support is preserved in
`app:ch_response:thm:response-literal-transfer`. -/
theorem hasCompactSupport_reverseDemodulatedGraph
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (ζ : Euclidean n) (ρ : ℝ)
    (f : Euclidean n → Fin r → ℂ) {K : Set (Euclidean n)} (hK : IsCompact K)
    (hs : ∀ y x η, y ∉ K → A y x η = 0) :
    HasCompactSupport (reverseDemodulatedGraph S φ A ζ ρ f) :=
  hK.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_reverseDemodulatedGraph_subset S φ A ζ ρ f hK.isClosed hs)

end JanetCartan.ResponseTransfer.LowEnvelope
