module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.UncutNormal.WeightedBounds.Jets
public import JanetCartan.Analysis.Microlocal.FourierIntegral.UncutNormal.WeightedBounds.Growth

/-!
# Weighted whole-image graph amplitude from original primitives

For `app:ch_regular_base:eq:actual-matrix-inverse`, the actual amplitude is the
published `maskedWeightedAmplitude S c U = c |det S_{xη}| U⁻*`, with the entire
real mask retained. The inverse and absolute determinant estimates are proved
on fixed coefficient sets from original norm bounds and positive determinant
gaps. Local phase jets through `primitiveNormalReserve n + 2` and original
matrix/mask jets through `primitiveNormalReserve n` suffice for the normalized
order-zero jets on every whole-image source band.

Buffered mask support proves global smoothness and continuity; the original
physical support is unchanged. Original zeroth mask/matrix bounds and the mixed
phase second-jet bound give global boundedness and hence polynomial growth.
The assembly theorem supplies every amplitude premise of
`WholeImageGeometry.exists_graphL2_of_wholeImage_phase`. The parent's geometric
phase hypotheses, actual graph construction and uncut cross-normal identity are
separate obligations; no bounded graph operator is an input here.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.UncutNormal
open NormalComparison WholeImageGeometry LowBounds
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- All amplitude inputs for the weighted forward graph in
`app:ch_regular_base:eq:actual-matrix-inverse`, ready for
`WholeImageGeometry.exists_graphL2_of_wholeImage_phase`.

The constants depend only on the original zeroth bounds, finite-jet bounds,
dimension, matrix size and two positive gaps. They precede all fields, charts,
source-band endpoints and shell indices. The exact finite costs are
`wholeImagePhaseReserve n = primitiveNormalReserve n + 2` for the phase and
`primitiveNormalReserve n` for the original mask and matrix. Gaps are required
only on the buffered chart containing the complete mask's topological support.
The parent must supply these original primitive hypotheses from its actual data;
there are no inverse, density, weighted-amplitude or operator bounds among them. -/
theorem exists_maskedWeightedAmplitude_wholeImage_inputs (M₀ M B₀ Bφ : ℝ)
    {δJ δU : ℝ} (hδJ : 0 < δJ) (hδU : 0 < δU) :
    ∃ α > 0, ∃ P > 0,
      ∀ (X D Kout : Set E) (S : E → E → ℝ) (c : E → E → ℝ) (U : E → E → Mat)
        (a b : ℝ),
      IsOpen X → IsOpen D → Convex ℝ X → IsCompact Kout →
      ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D) →
      ContDiffOn ℝ ∞ (Function.uncurry c) (X ×ˢ D) →
      ContDiffOn ℝ ∞ (Function.uncurry U) (X ×ˢ D) →
      tsupport (Function.uncurry c) ⊆ X ×ˢ D →
      (∀ x u, x ∉ Kout → c x u = 0) →
      (∀ x ∈ X, ∀ u ∈ D, ‖c x u‖ ≤ M₀) →
      (∀ x ∈ X, ∀ u ∈ D, ‖U x u‖ ≤ M₀) →
      (∀ x ∈ X, ∀ u ∈ D,
        ‖fderiv ℝ (fun v ↦ fderiv ℝ (fun z ↦ S z v) x) u‖ ≤ B₀) →
      (∀ x ∈ X, ∀ u ∈ D, δJ ≤ phaseJacobian S x u) →
      (∀ x ∈ X, ∀ u ∈ D, δU ≤ ‖(U x u).det‖) →
      (∀ j : ℕ, ∀ z ∈ X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b,
        ∀ k ≤ wholeImagePhaseReserve n, ‖iteratedFDeriv ℝ k
          (Function.uncurry (normalizedPhase ((2 : ℝ)^j) S)) z‖ ≤ Bφ) →
      (∀ j : ℕ, ∀ z ∈ X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b,
        ∀ k ≤ primitiveNormalReserve n, ‖iteratedFDeriv ℝ k
          (fun q : E × E ↦ c q.1 (((2 : ℝ)^j) • q.2)) z‖ ≤ M) →
      (∀ j : ℕ, ∀ z ∈ X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b,
        ∀ k ≤ primitiveNormalReserve n, ‖iteratedFDeriv ℝ k
          (Function.uncurry (normalizedNormalMatrix ((2 : ℝ)^j) 0 U)) z‖ ≤ M) →
      ContDiffOn ℝ ∞ (Function.uncurry (maskedWeightedAmplitude S c U)) (X ×ˢ D) ∧
      Continuous (Function.uncurry (maskedWeightedAmplitude S c U)) ∧
      (∃ K : Set E, IsCompact K ∧ ∀ x u, x ∉ K → maskedWeightedAmplitude S c U x u = 0) ∧
      tsupport (Function.uncurry (maskedWeightedAmplitude S c U)) ⊆ X ×ˢ D ∧
      (∀ x u, ‖maskedWeightedAmplitude S c U x u‖ ≤ P * (1 + ‖u‖ ^ (0 : ℕ))) ∧
      ∀ j : ℕ, ∀ z ∈ X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b,
        ∀ k ≤ primitiveNormalReserve n, ‖iteratedFDeriv ℝ k
          (Function.uncurry (normalizedNormalMatrix ((2 : ℝ)^j) 0
            (maskedWeightedAmplitude S c U))) z‖ ≤ α := by
  obtain ⟨α, hα, hjets⟩ := exists_maskedWeightedAmplitude_normalized_jet_bound (n := n) (r := r)
    (primitiveNormalReserve n) M Bφ hδJ hδU
  obtain ⟨P, hP, hgrowth⟩ := exists_maskedAmplitudes_global_bound (n := n) (r := r)
    M₀ B₀ hδJ hδU
  refine ⟨α, hα, P, hP, ?_⟩
  intro X D Kout S c U a b hX hD hcX hKout hS hc hU hbuffer hphysical
    hc₀ hU₀ hmix hJ hdet hφjet hcjet hUjet
  have hsmooth := (maskedAmplitudes_contDiff hX hD hcX hS hc hU
    (fun x hx u hu ↦ ne_of_gt (hδJ.trans_le (hJ x hx u hu)))
    (fun x hx u hu ↦ norm_pos_iff.mp (hδU.trans_le (hdet x hx u hu))) hbuffer).2
  refine ⟨hsmooth.contDiffOn, hsmooth.continuous,
    ⟨Kout, hKout, (maskedAmplitudes_physical_support S c U Kout hphysical).2⟩,
    (maskedAmplitudes_tsupport_subset S c U).2.trans hbuffer, ?_, ?_⟩
  · intro x u
    have h := (hgrowth X D S c U hX hD hcX hS hbuffer hc₀ hU₀ hmix hJ hdet x u).2
    simpa using h.trans (show P ≤ P * (1 + (1 : ℝ)) by linarith)
  · intro j z hz k hk
    exact hjets X D S c U hX hD hcX hS hc hU hJ hdet ((2 : ℝ)^j) a b
      (pow_ne_zero _ (by norm_num)) (hφjet j) (hcjet j) (hUjet j) z hz k hk

end JanetCartan.FourierIntegral.UncutNormal
