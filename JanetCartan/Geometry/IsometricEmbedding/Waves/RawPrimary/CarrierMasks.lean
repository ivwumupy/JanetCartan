module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.MaskProfiles
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.Base

/-!
# Original detector masks uniformly over carrier labels

The joint mask producer controls every carrier derivative. Freezing a carrier
is a norm-one affine pullback, so the SAME constants bound the mask jets used
by `UniformCanonicalSlice` (`app:ch_waves:eq:individual-raw-slice`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff

namespace JanetCartan.RawPrimary
open MaskProfiles SliceBounds SliceGeometry

private theorem norm_iteratedFDeriv_freeze_carrier_le
    {Z E : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : Set Z} (hV : IsOpen V) {f : Z × E → ℂ}
    (hf : ContDiffOn ℝ ∞ f (V ×ˢ univ)) {z : Z} (hz : z ∈ V) (x : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y ↦ f (z, y)) x‖ ≤ ‖iteratedFDeriv ℝ k f (z, x)‖ := by
  let L : E →L[ℝ] Z × E := ContinuousLinearMap.inr ℝ Z E
  let g := fun w : Z × E ↦ f ((z, 0) + w)
  let W := (fun w : Z × E ↦ (z, 0) + w) ⁻¹' (V ×ˢ univ)
  have hW : IsOpen W := (hV.prod isOpen_univ).preimage (by fun_prop)
  have hg : ContDiffOn ℝ ∞ g W := hf.comp (by fun_prop) (fun _ h ↦ h)
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro y
    simp [L]
  have hx : L x ∈ W := by simpa [W, L] using hz
  have he : (fun y ↦ f (z, y)) = g ∘ L := by funext y; simp [g, L]
  rw [he]
  apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le L hW hg hx k).trans
  apply (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL)).trans_eq
  simp only [g, iteratedFDeriv_comp_add_left]
  simp [L]

/-- All original normalized mask premises with one budget before the carrier
label. Primitive angular smoothness on a neighborhood of the compact carrier
set and degree-zero homogeneity supply the actual bounds, preserving both
quadratures and the full high-pass transition. No mask seminorm is assumed
(`app:ch_waves:eq:B-bounds`, `app:ch_waves:eq:individual-raw-slice`). -/
theorem exists_uniform_carrierMask_premises {n : ℕ}
    {ξ : Euclidean n} (sec : ActualCarriers.FrozenPhaseReference.AdaptedSection ξ)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (angular : Euclidean 3 → Euclidean (n - 1) → ℂ) (H : Euclidean (n - 1) → ℝ)
    {S V : Set (Euclidean 3)} (hS : IsCompact S) (hV : IsOpen V) (hSV : S ⊆ V)
    (ha : ∀ z ∈ V, ∀ θ, θ ≠ 0 →
      ContDiffAt ℝ ∞ (fun q : Euclidean 3 × Euclidean (n - 1) ↦ angular q.1 q.2) (z, θ))
    (hah : ∀ z, ∀ t : ℝ, 0 < t → ∀ θ, angular z (t • θ) = angular z θ)
    (hH : ContDiff ℝ ∞ H) (hH₀ : ∀ η, ‖η‖ ≤ 1 → H η = 0)
    (hH₁ : ∀ η, 2 ≤ ‖η‖ → H η = 1) (ρ e : ℝ) :
    ∃ bmask : ℕ → ℝ, (∀ k, 0 ≤ bmask k) ∧ ∀ z ∈ S,
      Measurable (detectorMask (angular z) H) ∧
      (∃ Md : ℝ, ∀ η, ‖detectorMask (angular z) H η‖ ≤ Md) ∧
      (∀ j, ContDiffOn ℝ ∞ (normalizedMask (angular z) H j) (sliceInputExtension n)) ∧
      (∀ j, Function.support (normalizedMask (angular z) H j) ⊆ sliceInputCore n) ∧
      (∀ j, tsupport (normalizedMask (angular z) H j) ⊆ sliceInputExtension n) ∧
      ∀ j, ∀ q ∈ sliceClosedCore n ρ e, ∀ k,
        ‖iteratedFDeriv ℝ k
          (fun w : ℝ × (ℝ × Euclidean (n - 1)) × Euclidean (n - 1) ↦
            (χ (adaptedPhysicalCoordinates sec w.2.1) : ℂ) *
              normalizedMask (angular z) H j w.2.2) q‖ ≤ bmask k := by
  obtain ⟨B, hB, hb⟩ := exists_sliceClosedCore_mask_joint_bounds sec χ hχ angular H hS
    (fun z hz ↦ ha z (hSV hz)) hah hH hH₁ ρ e
  refine ⟨B, hB, ?_⟩
  intro z hz
  have hang (θ) (hθ : θ ≠ 0) : ContDiffAt ℝ ∞ (angular z) θ :=
    (ha z (hSV hz) θ hθ).comp θ (contDiffAt_const.prodMk contDiffAt_id)
  obtain ⟨hm, hmb, hs, hsp, hts, _⟩ :=
    canonicalSlice_mask_premises sec χ hχ (angular z) H hang (hah z) hH hH₀ hH₁ ρ e
  refine ⟨hm, hmb, hs, hsp, hts, ?_⟩
  intro j q hq k
  let f := fun w : Euclidean 3 × (ℝ × (ℝ × Euclidean (n - 1)) × Euclidean (n - 1)) ↦
    (χ (adaptedPhysicalCoordinates sec w.2.2.1) : ℂ) *
      normalizedMask (angular w.1) H j w.2.2.2
  have hf : ContDiffOn ℝ ∞ f (V ×ˢ univ) := by
    intro w hw
    have hc : ContDiff ℝ ∞ (fun w : Euclidean 3 ×
        (ℝ × (ℝ × Euclidean (n - 1)) × Euclidean (n - 1)) ↦
        (χ (adaptedPhysicalCoordinates sec w.2.2.1) : ℂ)) := by
      change ContDiff ℝ ∞ (fun w : Euclidean 3 ×
        (ℝ × (ℝ × Euclidean (n - 1)) × Euclidean (n - 1)) ↦
        (χ ((NullTransport.ActualFlow.adaptedCoordinates sec).symm w.2.2.1) : ℂ))
      exact Complex.ofRealCLM.contDiff.comp (hχ.comp
        ((NullTransport.ActualFlow.adaptedCoordinates sec).symm.contDiff.comp
          (contDiff_fst.comp (contDiff_snd.comp contDiff_snd))))
    exact (hc.contDiffAt.mul ((contDiffAt_normalizedMask_joint angular H
      (ha w.1 hw.1) hH j w.2.2.2).comp w
        (contDiffAt_fst.prodMk (contDiffAt_snd.comp w
          (contDiffAt_snd.comp w contDiffAt_snd))))).contDiffWithinAt
  exact (norm_iteratedFDeriv_freeze_carrier_le hV hf (hSV hz) q k).trans (hb j z hz q hq k)

end JanetCartan.RawPrimary
