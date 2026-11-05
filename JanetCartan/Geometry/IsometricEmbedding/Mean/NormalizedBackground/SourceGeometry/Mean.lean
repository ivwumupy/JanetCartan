module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.CarrierMean
public import JanetCartan.Analysis.Calculus.CompactParameterIntegral
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Smoothness of the actual compact carrier mean

The integration step of `app:ch_background:prop:bg-normalized`. The weights,
carrier domains and measures are fixed. Smoothness and integrability are derived
from the original fields. Taking the measure to be Lebesgue measure gives the
literal integral in the manuscript, without any torus identification.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.NormalizedBackground.SourceGeometry

variable {A E Z F : Type} {n : ℕ} [Fintype A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z] [BorelSpace Z]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

omit [Fintype A] [FiniteDimensional ℝ E] [MeasurableSpace Z] [BorelSpace Z] in
/-- Smoothness of each literal weighted rank-one entry, before integration
(`app:ch_background:prop:bg-normalized`). -/
theorem contDiffOn_carrierMean_integrand {U : Set E} {V : Set Z}
    {w : Z → ℝ} {ν : E × Z → F} {ξ : E × Z → Euclidean n}
    (hw : ContDiffOn ℝ ∞ w V) (hν : ContDiffOn ℝ ∞ ν (U ×ˢ V))
    (hξ : ContDiffOn ℝ ∞ ξ (U ×ˢ V)) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun p : E × Z ↦ w p.2 * ‖ν p‖ ^ 2 * (ξ p i * ξ p j))
      (U ×ˢ V) := by
  simp only [← real_inner_self_eq_norm_sq]
  exact ((hw.comp contDiffOn_snd (fun _ h ↦ h.2)).mul (hν.inner ℝ hν)).mul
    (((contDiffOn_piLp 2).mp hξ i).mul ((contDiffOn_piLp 2).mp hξ j))

omit [Fintype A] [FiniteDimensional ℝ E] in
/-- Integrability of every actual carrier-mean entry on the fixed compact
carrier set (`app:ch_background:prop:bg-normalized`). -/
theorem integrable_carrierMean_entries
    (μ : A → Measure Z) (K V : A → Set Z) {U : Set E}
    [∀ a, IsFiniteMeasure ((μ a).restrict (K a))]
    (hK : ∀ a, IsCompact (K a)) (hKV : ∀ a, K a ⊆ V a)
    (w : A → Z → ℝ) (ν : A → E × Z → F) (ξ : A → E × Z → Euclidean n)
    (hw : ∀ a, ContDiffOn ℝ ∞ (w a) (V a))
    (hν : ∀ a, ContDiffOn ℝ ∞ (ν a) (U ×ˢ V a))
    (hξ : ∀ a, ContDiffOn ℝ ∞ (ξ a) (U ×ˢ V a))
    {x : E} (hx : x ∈ U) (a : A) (i j : Fin n) :
    Integrable (fun z ↦ w a z * ‖ν a (x, z)‖ ^ 2 *
      (ξ a (x, z) i * ξ a (x, z) j)) ((μ a).restrict (K a)) :=
  integrableOn_compactParameter (hK a) (hKV a)
    (contDiffOn_carrierMean_integrand (hw a) (hν a) (hξ a) i j).continuousOn hx

/-- Smoothness of the literal mean follows from the fields, on their original
open seed box (`app:ch_background:eq:bg-Hsigma`). There is no assumed smooth
mean among the hypotheses. -/
theorem contDiffOn_carrierMean_compact
    (μ : A → Measure Z) (K V : A → Set Z) {U : Set E}
    [∀ a, IsFiniteMeasure ((μ a).restrict (K a))]
    (hU : IsOpen U) (hV : ∀ a, IsOpen (V a))
    (hK : ∀ a, IsCompact (K a)) (hKV : ∀ a, K a ⊆ V a)
    (w : A → Z → ℝ) (ν : A → E × Z → F) (ξ : A → E × Z → Euclidean n)
    (hw : ∀ a, ContDiffOn ℝ ∞ (w a) (V a))
    (hν : ∀ a, ContDiffOn ℝ ∞ (ν a) (U ×ˢ V a))
    (hξ : ∀ a, ContDiffOn ℝ ∞ (ξ a) (U ×ˢ V a)) :
    ContDiffOn ℝ ∞ (carrierMean (fun a ↦ (μ a).restrict (K a)) w ν ξ) U := by
  let L : (Fin n → Fin n → ℝ) →ₗ[ℝ] MetricTensor n := LinearMap.id
  let C : (Fin n → Fin n → ℝ) →L[ℝ] MetricTensor n :=
    ⟨L, L.continuous_of_finiteDimensional⟩
  unfold carrierMean
  apply ContDiffOn.sum
  intro a _
  apply C.contDiff.comp_contDiffOn
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  exact contDiffOn_compactParameterIntegral hU (hV a)
    (hK a) (hKV a) (contDiffOn_carrierMean_integrand (hw a) (hν a) (hξ a) i j)

omit [FiniteDimensional ℝ E] in

/-- Positivity of the constant mean at zero, with integrability discharged
from the same compact smooth input fields (`app:ch_background:prop:bg-normalized`). -/
theorem normalizedCarrierMean_zero_posSemidef_of_smooth_compact
    (μ : A → Measure Z) (K V : A → Set Z) {U : Set E}
    [∀ a, IsFiniteMeasure ((μ a).restrict (K a))]
    (hK : ∀ a, IsCompact (K a)) (hKV : ∀ a, K a ⊆ V a) (h0 : (0 : E) ∈ U)
    (w : A → Z → ℝ) (ν : A → E × Z → F) (ξ : A → E × Z → Euclidean n)
    (hw : ∀ a, ContDiffOn ℝ ∞ (w a) (V a))
    (hν : ∀ a, ContDiffOn ℝ ∞ (ν a) (U ×ˢ V a))
    (hξ : ∀ a, ContDiffOn ℝ ∞ (ξ a) (U ×ˢ V a))
    (hpos : ∀ a z, 0 ≤ w a z) (x : E) :
    (normalizedCarrierMean (fun a ↦ (μ a).restrict (K a)) w ν ξ 0 x).PosSemidef := by
  exact normalizedCarrierMean_zero_posSemidef _ w ν ξ x hpos
    (fun a i j ↦ integrable_carrierMean_entries μ K V hK hKV w ν ξ hw hν hξ h0 a i j)

omit [FiniteDimensional ℝ E] [NormedSpace ℝ Z] [BorelSpace Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Z]
    [InnerProductSpace ℝ F] in
/-- Compactly supported weights allow restriction of the original measure
without changing the mean (`app:ch_background:eq:bg-Hsigma`). This applies to
Lebesgue measure itself, so there is no change of the input data model. -/
theorem carrierMean_restrict_of_weight_support (μ : A → Measure Z) (K : A → Set Z)
    (w : A → Z → ℝ) (ν : A → E × Z → F) (ξ : A → E × Z → Euclidean n)
    (hw : ∀ a z, z ∉ K a → w a z = 0) :
    carrierMean (fun a ↦ (μ a).restrict (K a)) w ν ξ = carrierMean μ w ν ξ := by
  funext x
  unfold carrierMean
  apply Finset.sum_congr rfl
  intro a _
  ext i j
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  simp [hw a z hz]

/-- Smoothness of the original, unrestricted carrier integral with fixed
compactly supported weights (`app:ch_background:eq:bg-Hsigma`). -/
theorem contDiffOn_carrierMean_of_weight_support
    (μ : A → Measure Z) (K V : A → Set Z) {U : Set E}
    [∀ a, IsFiniteMeasure ((μ a).restrict (K a))]
    (hU : IsOpen U) (hV : ∀ a, IsOpen (V a))
    (hK : ∀ a, IsCompact (K a)) (hKV : ∀ a, K a ⊆ V a)
    (w : A → Z → ℝ) (ν : A → E × Z → F) (ξ : A → E × Z → Euclidean n)
    (hw : ∀ a, ContDiffOn ℝ ∞ (w a) (V a))
    (hν : ∀ a, ContDiffOn ℝ ∞ (ν a) (U ×ˢ V a))
    (hξ : ∀ a, ContDiffOn ℝ ∞ (ξ a) (U ×ˢ V a))
    (hsupp : ∀ a z, z ∉ K a → w a z = 0) :
    ContDiffOn ℝ ∞ (carrierMean μ w ν ξ) U := by
  rw [← carrierMean_restrict_of_weight_support μ K w ν ξ hsupp]
  exact contDiffOn_carrierMean_compact μ K V hU hV hK hKV w ν ξ hw hν hξ

end JanetCartan.NormalizedBackground.SourceGeometry
