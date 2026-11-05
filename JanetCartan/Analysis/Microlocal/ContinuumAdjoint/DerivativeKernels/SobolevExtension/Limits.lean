module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.Weights
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension.Limits

/-!
# Physical Sobolev bounds under carrier L² limits

For `app:ch_background:prop:bg-adjoint`, Fatou's lemma passes convergent
bounds to the actual full physical Fourier norm on `carrierMeasure`.
The extended norm is retained until finiteness has been proved. These lemmas
supply the limit step for
`memPhysicalSobolev_partialUnitaryInverse_of_compactSmooth_bound`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow CarrierSobolev

variable {n : ℕ}

/-- Lower semicontinuity with convergent bounds for the extended physical
Fourier norm in `app:ch_background:prop:bg-adjoint`. An a.e. convergent
subsequence of the shared `initialFourier` transforms and Fatou's lemma
preserve the literal weight and carrier measure. No Sobolev membership of
the limit is assumed. -/
theorem eLpNorm_initialWeight_initialFourier_le_of_tendsto (s : ℕ)
    {u : ℕ → CarrierL2 n} {v : CarrierL2 n} (hu : Tendsto u atTop (𝓝 v))
    {b : ℕ → ℝ≥0∞} {B : ℝ≥0∞} (hb : Tendsto b atTop (𝓝 B))
    (hbound : ∀ k, eLpNorm (fun ξ ↦ initialWeight s ξ • initialFourier n (u k) ξ)
      2 (carrierMeasure n) ≤ b k) :
    eLpNorm (fun ξ ↦ initialWeight s ξ • initialFourier n v ξ)
      2 (carrierMeasure n) ≤ B := by
  have hF : Tendsto (fun k ↦ initialFourier n (u k)) atTop (𝓝 (initialFourier n v)) :=
    (initialFourier n).continuous.continuousAt.tendsto.comp hu
  obtain ⟨φ, hφ, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hF).exists_seq_tendsto_ae
  have hw : ∀ᵐ ξ ∂carrierMeasure n,
      Tendsto (fun k ↦ initialWeight s ξ • initialFourier n (u (φ k)) ξ)
        atTop (𝓝 (initialWeight s ξ • initialFourier n v ξ)) := by
    filter_upwards [hae] with ξ hξ
    exact tendsto_const_nhds.smul hξ
  have hfat := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2)
    (fun k ↦ aestronglyMeasurable_weightedInitialFourier s (u (φ k)))
    (fun ξ ↦ initialWeight s ξ • initialFourier n v ξ)
    (aestronglyMeasurable_weightedInitialFourier s v) hw
  exact hfat.trans ((liminf_le_liminf (Eventually.of_forall (fun k ↦ hbound (φ k)))).trans_eq
    (hb.comp hφ.tendsto_atTop).liminf_eq)

/-- Physical Sobolev membership and the unchanged bound pass through a carrier
L² limit for `app:ch_background:prop:bg-adjoint`. This is the limit step used
to extend the compact measurement-data estimate to every Sobolev datum. -/
theorem memPhysicalSobolev_and_norm_le_of_tendsto (s : ℕ)
    {u : ℕ → CarrierL2 n} {v : CarrierL2 n} (hu : Tendsto u atTop (𝓝 v))
    (hmem : ∀ k, MemPhysicalSobolev s (u k))
    {b : ℕ → ℝ} {B : ℝ} (hb : Tendsto b atTop (𝓝 B))
    (hbound : ∀ k, physicalSobolevNorm s (u k) ≤ b k) :
    MemPhysicalSobolev s v ∧ physicalSobolevNorm s v ≤ B := by
  have hB : 0 ≤ B := ge_of_tendsto hb (Eventually.of_forall fun k ↦
    ENNReal.toReal_nonneg.trans (hbound k))
  have he : eLpNorm (fun ξ ↦ initialWeight s ξ • initialFourier n v ξ)
      2 (carrierMeasure n) ≤ ENNReal.ofReal B := by
    apply eLpNorm_initialWeight_initialFourier_le_of_tendsto s hu
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hb)
    intro k
    rw [← ENNReal.ofReal_toReal (hmem k).eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal (hbound k)
  refine ⟨he.trans_lt ENNReal.ofReal_lt_top, ?_⟩
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq
    (ENNReal.toReal_ofReal hB)

end JanetCartan.ContinuumAdjoint.DerivativeKernels
