module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.MaskProfiles.Detector
public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceGeometry.Domains

/-!
# Uniform normalized mask and joint physical-cutoff bounds

The constants here are proved from the three exact profiles, primitive
punctured angular smoothness and positive homogeneity, and the original
high-pass. They are independent of the band label, ceiling, semiclassical
parameter and Hilbert datum. The physical-cutoff theorem supplies the exact
`bmask` premise of `CanonicalSlice.exists_canonical_rawSliceSobolev` and
`SliceBounds.exists_rawPhysicalSliceSobolev_wkbGrades`.
The carrier version bounds full joint derivatives on a fixed compact carrier
set, rather than merely bounding each carrier separately.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.RawPrimary.MaskProfiles
open RawInputPartition SliceBounds SliceGeometry

private theorem exists_bound_three_profiles
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : ℕ → V → ℂ) {K : Set V} (hK : IsCompact K)
    (hf : ∀ i, ∀ q ∈ K, ContDiffAt ℝ ∞ (f i) q)
    (heq : ∀ j, f j = f (min j 2)) :
    ∃ B : ℕ → ℝ, (∀ k, 0 ≤ B k) ∧ ∀ j, ∀ q ∈ K, ∀ k,
      ‖iteratedFDeriv ℝ k (f j) q‖ ≤ B k := by
  let C (i k : ℕ) := cNorm K k (f i)
  have hC (i k : ℕ) : 0 ≤ C i k := cNorm_nonneg _ _ _
  refine ⟨fun k ↦ ∑ i ∈ Finset.range 3, C i k,
    fun k ↦ Finset.sum_nonneg (fun i _ ↦ hC i k), ?_⟩
  intro j q hq k
  rw [heq j]
  calc
    _ ≤ C (min j 2) k := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun x hx ↦ (hf _ x hx).of_le (by simp)) hq le_rfl
    _ ≤ _ := Finset.single_le_sum (fun i _ ↦ hC i k)
      (Finset.mem_range.mpr (by omega))

variable {n : ℕ}
local notation "E" => Euclidean (n - 1)
local notation "Q" => ℝ × (ℝ × E) × E

/-- All orders of the literal normalized masks are bounded globally by
constants independent of the band label and ceiling
(`app:ch_waves:eq:B-bounds`). -/
theorem exists_uniform_normalizedMask_derivative_bounds (a : E → ℂ) (H : E → ℝ)
    (ha : ∀ θ : E, θ ≠ 0 → ContDiffAt ℝ ∞ a θ)
    (hah : ∀ r : ℝ, 0 < r → ∀ θ, a (r • θ) = a θ)
    (hH : ContDiff ℝ ∞ H) (hH₁ : ∀ η, 2 ≤ ‖η‖ → H η = 1) :
    ∃ B : ℕ → ℝ, (∀ k, 0 ≤ B k) ∧ ∀ j θ k,
      ‖iteratedFDeriv ℝ k (normalizedMask a H j) θ‖ ≤ B k := by
  obtain ⟨B, hB, hb⟩ := exists_bound_three_profiles (normalizedMask a H)
    (isCompact_closedBall (0 : E) 2)
    (fun j _ _ ↦ (contDiff_normalizedMask a H ha hH j).contDiffAt)
    (normalizedMask_eq_min a H hah hH₁)
  refine ⟨B, hB, fun j θ k ↦ ?_⟩
  by_cases hθ : θ ∈ closedBall (0 : E) 2
  · exact hb j θ hθ k
  · have hz : iteratedFDeriv ℝ k (normalizedMask a H j) θ = 0 := by
      by_contra hn
      exact hθ (tsupport_normalizedMask_subset a H j (support_iteratedFDeriv_subset k hn))
    simpa only [hz, norm_zero] using hB k

/-- In particular the normalized complex masks themselves are uniformly
bounded, preserving both quadratures (`app:ch_waves:eq:B-bounds`). -/
theorem exists_uniform_normalizedMask_bound (a : E → ℂ) (H : E → ℝ)
    (ha : ∀ θ : E, θ ≠ 0 → ContDiffAt ℝ ∞ a θ)
    (hah : ∀ r : ℝ, 0 < r → ∀ θ, a (r • θ) = a θ)
    (hH : ContDiff ℝ ∞ H) (hH₁ : ∀ η, 2 ≤ ‖η‖ → H η = 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j θ, ‖normalizedMask a H j θ‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := exists_uniform_normalizedMask_derivative_bounds a H ha hah hH hH₁
  exact ⟨B 0, hB 0, fun j θ ↦ by simpa only [norm_iteratedFDeriv_zero] using hb j θ 0⟩

/-- The exact joint physical-cutoff bound requested by the canonical slice
consumer, for the retained adapted section and the original fixed cutoff.
Compact support of the cutoff is not needed for this compact-core bound;
in particular this applies to the consumer's smooth compact cutoff.
No constant depends on `j`, `K`, `τ` or the input datum
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem exists_sliceClosedCore_mask_bounds
    {ξ : Euclidean n} (sec : ActualCarriers.FrozenPhaseReference.AdaptedSection ξ)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (a : E → ℂ) (H : E → ℝ)
    (ha : ∀ θ : E, θ ≠ 0 → ContDiffAt ℝ ∞ a θ)
    (hah : ∀ r : ℝ, 0 < r → ∀ θ, a (r • θ) = a θ)
    (hH : ContDiff ℝ ∞ H) (hH₁ : ∀ η, 2 ≤ ‖η‖ → H η = 1)
    (ρ e : ℝ) :
    ∃ bmask : ℕ → ℝ, (∀ k, 0 ≤ bmask k) ∧
      ∀ j, ∀ q ∈ sliceClosedCore n ρ e, ∀ k,
        ‖iteratedFDeriv ℝ k (fun w : Q ↦
          (χ (adaptedPhysicalCoordinates sec w.2.1) : ℂ) * normalizedMask a H j w.2.2) q‖ ≤
            bmask k := by
  apply exists_bound_three_profiles _ (isCompact_sliceClosedCore ρ e)
  · intro j q _
    have hc : ContDiff ℝ ∞ (fun w : Q ↦ (χ (adaptedPhysicalCoordinates sec w.2.1) : ℂ)) := by
      change ContDiff ℝ ∞ (fun w : Q ↦
        (χ ((NullTransport.ActualFlow.adaptedCoordinates sec).symm w.2.1) : ℂ))
      exact Complex.ofRealCLM.contDiff.comp (hχ.comp
        ((NullTransport.ActualFlow.adaptedCoordinates sec).symm.contDiff.comp
          (contDiff_fst.comp contDiff_snd)))
    exact (hc.mul ((contDiff_normalizedMask a H ha hH j).comp
      (contDiff_snd.comp contDiff_snd))).contDiffAt
  · intro j
    funext w
    rw [normalizedMask_eq_min a H hah hH₁ j]

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Uniform full carrier/input derivatives on a fixed compact carrier set.
The primitive detector must be smooth on a neighborhood of each retained
carrier and each nonzero frequency, and homogeneous there for every carrier.
All normalized profile estimates are conclusions
(`app:ch_waves:eq:B-bounds`). -/
theorem exists_uniform_normalizedMask_joint_derivative_bounds
    (a : Z → E → ℂ) (H : E → ℝ) {S : Set Z} (hS : IsCompact S)
    (ha : ∀ z ∈ S, ∀ θ : E, θ ≠ 0 →
      ContDiffAt ℝ ∞ (fun q : Z × E ↦ a q.1 q.2) (z, θ))
    (hah : ∀ z, ∀ r : ℝ, 0 < r → ∀ θ, a z (r • θ) = a z θ)
    (hH : ContDiff ℝ ∞ H) (hH₁ : ∀ η, 2 ≤ ‖η‖ → H η = 1) :
    ∃ B : ℕ → ℝ, (∀ k, 0 ≤ B k) ∧ ∀ j, ∀ z ∈ S, ∀ θ k,
      ‖iteratedFDeriv ℝ k
        (fun q : Z × E ↦ normalizedMask (a q.1) H j q.2) (z, θ)‖ ≤ B k := by
  obtain ⟨B, hB, hb⟩ := exists_bound_three_profiles
    (fun j (q : Z × E) ↦ normalizedMask (a q.1) H j q.2)
    (hS.prod (isCompact_closedBall (0 : E) 2))
    (fun j q hq ↦ contDiffAt_normalizedMask_joint a H (ha q.1 hq.1) hH j q.2)
    (fun j ↦ funext (fun q ↦ congrFun (normalizedMask_eq_min (a q.1) H (hah q.1) hH₁ j) q.2))
  refine ⟨B, hB, fun j z hz θ k ↦ ?_⟩
  by_cases hθ : θ ∈ closedBall (0 : E) 2
  · exact hb j (z, θ) ⟨hz, hθ⟩ k
  · have heq : iteratedFDeriv ℝ k
        (fun q : Z × E ↦ normalizedMask (a q.1) H j q.2) (z, θ) = 0 := by
      by_contra hn
      have hm : (z, θ) ∈ tsupport (fun q : Z × E ↦ normalizedMask (a q.1) H j q.2) :=
        support_iteratedFDeriv_subset (𝕜 := ℝ) k hn
      have hmem := tsupport_normalizedMask_joint_subset a H j hm
      exact hθ hmem
    simpa only [heq, norm_zero] using hB k

/-- Full carrier/physical/input derivatives of the SAME cutoff mask are
uniform on the retained compact carrier set and original slice core
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem exists_sliceClosedCore_mask_joint_bounds
    {ξ : Euclidean n} (sec : ActualCarriers.FrozenPhaseReference.AdaptedSection ξ)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (a : Z → E → ℂ) (H : E → ℝ) {S : Set Z} (hS : IsCompact S)
    (ha : ∀ z ∈ S, ∀ θ : E, θ ≠ 0 →
      ContDiffAt ℝ ∞ (fun q : Z × E ↦ a q.1 q.2) (z, θ))
    (hah : ∀ z, ∀ r : ℝ, 0 < r → ∀ θ, a z (r • θ) = a z θ)
    (hH : ContDiff ℝ ∞ H) (hH₁ : ∀ η, 2 ≤ ‖η‖ → H η = 1)
    (ρ e : ℝ) :
    ∃ bmask : ℕ → ℝ, (∀ k, 0 ≤ bmask k) ∧
      ∀ j, ∀ z ∈ S, ∀ q ∈ sliceClosedCore n ρ e, ∀ k,
        ‖iteratedFDeriv ℝ k (fun w : Z × Q ↦
          (χ (adaptedPhysicalCoordinates sec w.2.2.1) : ℂ) *
            normalizedMask (a w.1) H j w.2.2.2) (z, q)‖ ≤ bmask k := by
  have hs (j : ℕ) (w : Z × Q) (hw : w ∈ S ×ˢ sliceClosedCore n ρ e) :
      ContDiffAt ℝ ∞ (fun w : Z × Q ↦
        (χ (adaptedPhysicalCoordinates sec w.2.2.1) : ℂ) *
          normalizedMask (a w.1) H j w.2.2.2) w := by
    have hc : ContDiff ℝ ∞
        (fun w : Z × Q ↦ (χ (adaptedPhysicalCoordinates sec w.2.2.1) : ℂ)) := by
      change ContDiff ℝ ∞ (fun w : Z × Q ↦
        (χ ((NullTransport.ActualFlow.adaptedCoordinates sec).symm w.2.2.1) : ℂ))
      exact Complex.ofRealCLM.contDiff.comp (hχ.comp
        ((NullTransport.ActualFlow.adaptedCoordinates sec).symm.contDiff.comp
          (contDiff_fst.comp (contDiff_snd.comp contDiff_snd))))
    exact hc.contDiffAt.mul ((contDiffAt_normalizedMask_joint a H (ha w.1 hw.1) hH j w.2.2.2).comp w
      (contDiffAt_fst.prodMk (contDiffAt_snd.comp w (contDiffAt_snd.comp w contDiffAt_snd))))
  obtain ⟨B, hB, hb⟩ := exists_bound_three_profiles
    (fun j (w : Z × Q) ↦ (χ (adaptedPhysicalCoordinates sec w.2.2.1) : ℂ) *
      normalizedMask (a w.1) H j w.2.2.2)
    (hS.prod (isCompact_sliceClosedCore ρ e)) hs
    (fun j ↦ funext (fun w ↦ by rw [normalizedMask_eq_min (a w.1) H (hah w.1) hH₁ j]))
  exact ⟨B, hB, fun j z hz q hq k ↦ hb j (z, q) ⟨hz, hq⟩ k⟩

end JanetCartan.RawPrimary.MaskProfiles
