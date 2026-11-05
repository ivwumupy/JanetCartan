module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.Integration

/-!
# Quantitative passage to the spectator integral

These estimates consume the joint shell jets in
`app:ch_background:eq:bg-full-complex-amplitude`. Restriction to a fixed
spectator has norm at most one and integration costs only its fixed volume.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n : ℕ}

/-- Fixing the spectator does not enlarge any joint jet. Source:
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem norm_iteratedFDeriv_spectatorSlice_le
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : Variables n × Euclidean 2 → G} (hf : ContDiff ℝ ∞ f)
    (k : ℕ) (x : Variables n) (v : Euclidean 2) :
    ‖iteratedFDeriv ℝ k (fun y ↦ f (y, v)) x‖ ≤
      ‖iteratedFDeriv ℝ k f (x, v)‖ := by
  let L := ContinuousLinearMap.inl ℝ (Variables n) (Euclidean 2)
  let g := fun p : Variables n × Euclidean 2 ↦ f (p + (0, v))
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (by intro y; simp [L])
  have he : (fun y ↦ f (y, v)) = g ∘ L := by funext y; simp [g, L]
  rw [he, L.iteratedFDeriv_comp_right hg x (by simp)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ k g (L x)‖ * ∏ _ : Fin k, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ k g (L x)‖ * ∏ _ : Fin k, (1 : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg L)
        (fun _ _ ↦ hL)) (norm_nonneg _)
    _ = _ := by simp [g, L, iteratedFDeriv_comp_add_right]

/-- A uniform joint density bound passes through the fixed compact spectator
integral, with the same common high norm. Source:
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem norm_iteratedFDeriv_spectatorIntegral_le
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {f : Variables n × Euclidean 2 → G} (hf : ContDiff ℝ ∞ f)
    {K : Set (Euclidean 2)} (hK : IsCompact K) (k : ℕ) (x : Variables n)
    {B : ℝ} (hB : ∀ v ∈ K, ‖iteratedFDeriv ℝ k f (x, v)‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (fun y ↦ ∫ v in K, f (y, v)) x‖ ≤ B * volume.real K := by
  rw [iteratedFDeriv_spectatorIntegral hK k hf x]
  apply norm_setIntegral_le_of_norm_le_const_ae' hK.measure_lt_top
  filter_upwards [] with v hv
  exact (norm_iteratedFDeriv_spectatorSlice_le hf k x v).trans (hB v hv)

end JanetCartan.ContinuumNormalReduction.TransportSymbol
