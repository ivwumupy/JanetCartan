module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.NormalCompletionScaling
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.PrincipalNormal

/-!
# Nonvanishing of the normalized principal normal

For `app:ch_background:prop:bg-normalized`, nonvanishing at zero follows from
the actual normal equation and pencil kernel. No nonvanishing of the output
normal is assumed. Compactness then gives one positive bound on a fixed compact
physical/carrier set. Only the normalized pullback is evaluated at scale zero.
-/

@[expose] public noncomputable section

open Set Matrix
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.NormalizedBackground.SourceGeometry

open LeadingWave AmbientResponse ProjectedStressFrame

/-- The geometric normal equation forces nonvanishing for nonzero pencil-null
input data (`app:ch_background:prop:bg-normalized`). -/
theorem principalNormal_ne_zero_of_pencil_null {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x ξ b : Euclidean n}
    (hF : ContDiffAt ℝ 2 F x)
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N)))
    (hframe : ∃ e : Module.Basis (Fin n) ℝ (symmetricNormalMap F x).ker,
      ∀ i, ((e i : SymmetricTensor n) : MetricTensor n) = projectedStress F x i)
    (hnull : ActualCarriers.pencil (projectedStress F x) ξ *ᵥ (fun j ↦ b j) = 0)
    (hξ : ξ ≠ 0) (hb : b ≠ 0) :
    principalNormal (canonicalNormalCompletion F x) ξ b ≠ 0 := by
  intro hzero
  have hpair := principalNormal_pairing_of_pencil_null hF hrank hframe hnull
  rw [hzero] at hpair
  apply symmetricProduct_ne_zero hξ hb
  ext i j
  have hij := congrFun (congrFun hpair i) j
  simpa [normalPairing] using hij.symm

/-- One scale interval and positive lower bound for the normalized normal on
one fixed compact physical/carrier set, from the seed kernel and geometry
(`app:ch_background:prop:bg-normalized`). The choice precedes derivative order. -/
theorem exists_uniform_principalNormal_lower_bound {n N : ℕ}
    {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : Euclidean n → Euclidean N} {s : Set (Euclidean n)}
    {U K : Set (Euclidean n × Z)} {ξ b : Euclidean n × Z → Euclidean n}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s) (h0 : (0 : Euclidean n) ∈ s)
    (himm : IsImmersionOn F s) (hrank : HasFullNormalRankOn F s)
    (hU : MapsTo Prod.fst U s) (hUopen : IsOpen U)
    (hξ : ContDiffOn ℝ ∞ ξ U) (hb : ContDiffOn ℝ ∞ b U)
    (hK : IsCompact K) (hKU : ∀ p ∈ K, (0, p.2) ∈ U)
    (hframe : ∃ e : Module.Basis (Fin n) ℝ (symmetricNormalMap F 0).ker,
      ∀ i, ((e i : SymmetricTensor n) : MetricTensor n) = projectedStress F 0 i)
    (hnull : ∀ p ∈ K, ActualCarriers.pencil (projectedStress F 0) (ξ (0, p.2)) *ᵥ
      (fun j ↦ b (0, p.2) j) = 0)
    (hξ0 : ∀ p ∈ K, ξ (0, p.2) ≠ 0) (hb0 : ∀ p ∈ K, b (0, p.2) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ ∈ Icc (0 : ℝ) ρ₀, ∀ p ∈ K,
        c ≤ ‖normalizedPullback
          (fun q ↦ principalNormal (canonicalNormalCompletion F q.1) (ξ q) (b q))
          (ρ, p)‖ := by
  obtain ⟨c, hc, ε, hε, hbound⟩ := exists_uniform_norm_lower_bound hK
    (fun p hp ↦ (contDiffAt_normalizedPrincipalNormal_zero hs hF himm hrank hU hUopen
      hξ hb p.1 p.2 (hKU p hp)).continuousAt)
    (fun p hp ↦ by
      rw [normalizedPullback_zero]
      exact principalNormal_ne_zero_of_pencil_null
        ((hF.contDiffAt (hs.mem_nhds h0)).of_le (by simp)) (hrank 0 h0)
        hframe (hnull p hp) (hξ0 p hp) (hb0 p hp))
  refine ⟨c, hc, ε / 2, half_pos hε, ?_⟩
  intro ρ hρ p hp
  exact hbound ρ (by rw [abs_of_nonneg hρ.1]; exact hρ.2.trans_lt (half_lt_self hε)) p hp

end JanetCartan.NormalizedBackground.SourceGeometry
