module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.UncutDensity.RawSynthesis

/-!
# Measured raw densities as literal L² classes

For `app:ch_background:eq:bg-density-twice` and
`app:ch_mean_pairs:eq:mean-density-recursion`, the literal transported mean
belongs to the original output L² space and converges strongly whenever its
regular raw inputs converge in L². The proof uses the bounded carrier already
realized on tests, and proves its agreement with the literal raw integral.
The conditional raw membership remains in the existing transverse weighted
domain; the full mixed Sobolev producer must supply that membership.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace JanetCartan.UncutDensity
open ContinuumRow RawCutoffBounds ContinuumAdjoint.DensityMultiplier

variable {n N : ℕ}

/-- Changing an initial-data representative leaves synthesis unchanged at
almost every carrier parameter and **every** initial position. This permits
evaluation at the actual footpoint without pulling back an a.e. statement
along a graph (`app:ch_background:eq:bg-density-twice`). -/
theorem initialDensity_congr (d : CarrierData n N) (c : ℝ)
    {f g : CarrierVariable n → ℂ} (hfg : f =ᵐ[carrierMeasure n] g) :
    ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      ∀ y, initialDensity d c f (z, y) = initialDensity d c g (z, y) := by
  filter_upwards [Measure.ae_ae_of_ae_prod hfg] with z hz
  intro y
  unfold initialDensity CarrierSobolev.radianInverseIntegral
  congr 2
  apply integral_congr_ae
  filter_upwards [hz] with η hη
  rw [hη]

/-- The literal transported increment is independent of the raw L²
representative, pointwise in the measured variable. The slice-wise identity
holds for all initial positions before the footpoint is substituted
(`app:ch_background:eq:bg-density-twice`). -/
theorem measuredIncrement_initialDensity_congr (d : CarrierData n N)
    (ψ : CarrierParameter → ℝ) (c : ℝ)
    {f g : CarrierVariable n → ℂ} (hfg : f =ᵐ[carrierMeasure n] g) :
    measuredIncrement d ψ (initialDensity d c f) =
      measuredIncrement d ψ (initialDensity d c g) := by
  funext x
  apply congrArg (fun v : Torus n → Euclidean n ↦ d.outputChart.indicator v x)
  funext x
  apply integral_congr_ae
  filter_upwards [initialDensity_congr d c hfg] with z hz
  rw [hz]

section Geometry

variable (d : CarrierData n N) (s : ℕ) (hs : n - 1 < 2 * s)
    (χ : CarrierParameter → ℝ)
    (hχ : ∀ z θ, d.angularCutoff z θ ≠ 0 → χ z = 1)
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ u : carrierInitialTestSpace n,
      U (carrierInitialTestToLp u) =ᵐ[volume] carrierTestIntegral d u.val)
    (hk : ∀ x, AEStronglyMeasurable (carrierKernel d x) (carrierMeasure n))
    {K : Set CarrierParameter} (hK : IsCompact K)
    (hsupp : ∀ z ∉ K, ∀ θ, d.angularCutoff z θ = 0)
    (hst : ∀ x, ContinuousOn (measuredStress d x) K)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hρ : ∀ z θ, |d.angularCutoff z θ| ≤ A)
    (hhi : ∀ r, |d.highCutoff r| ≤ B)

include hs hχ hU hk hK hsupp hst hA hB hρ hhi

/-- The literal measured increment for coefficient `c` is `c/2` times the
existing real channel. The cases `c = 4` and `c = -2` are respectively
`app:ch_background:eq:bg-density-twice` and
`app:ch_mean_pairs:eq:mean-density-recursion`. -/
theorem measuredIncrement_raw_coeFn (c : ℝ) (f : CarrierL2 n)
    (hf : CarrierWeightedMem (etaBesselWeight (s + 1)) f) :
    measuredIncrement d (fun z ↦ χ z ^ 2) (initialDensity d c f) =ᵐ[volume]
      ((c / 2) • carrierChannel U f : OutputL2 n) := by
  have hkernel x := memLp_inverseWeight_carrierKernel d s hs x
    (hk x) hK hsupp (hst x) hA hB hρ hhi
  filter_upwards [carrierRealization_weighted d (s + 1) U hU
      (Eventually.of_forall hkernel) f hf,
    carrierChannel_coeFn U f, Lp.coeFn_smul (c / 2) (carrierChannel U f)]
    with x hx hy hz
  rw [measuredIncrement_initialDensity d χ hχ c f x
    (integrable_carrierKernel_of_weighted d (s + 1) f hf x (hkernel x)),
    hz, Pi.smul_apply, hy, hx, smul_smul]
  congr 1
  ring

/-- L² membership is a consequence of the proved literal raw identity,
not an extra assumption on transported densities
(`app:ch_background:eq:bg-density-twice`). -/
theorem measuredIncrement_raw_memLp (c : ℝ) (f : CarrierL2 n)
    (hf : CarrierWeightedMem (etaBesselWeight (s + 1)) f) :
    MemLp (measuredIncrement d (fun z ↦ χ z ^ 2) (initialDensity d c f)) 2 volume :=
  (Lp.memLp ((c / 2) • carrierChannel U f)).ae_eq
    (measuredIncrement_raw_coeFn d s hs χ hχ U hU hk hK hsupp hst hA hB hρ hhi c f hf).symm

/-- Exact class identity for the measured raw density, used when adding the
finite carrier channels in `app:ch_background:eq:bg-density-twice`. -/
theorem measuredIncrement_raw_toLp (c : ℝ) (f : CarrierL2 n)
    (hf : CarrierWeightedMem (etaBesselWeight (s + 1)) f) :
    (measuredIncrement_raw_memLp d s hs χ hχ U hU hk hK hsupp hst hA hB hρ hhi
      c f hf).toLp _ = (c / 2) • carrierChannel U f := by
  apply Lp.ext
  exact (measuredIncrement_raw_memLp d s hs χ hχ U hU hk hK hsupp hst hA hB hρ hhi
    c f hf).coeFn_toLp.trans
      (measuredIncrement_raw_coeFn d s hs χ hχ U hU hk hK hsupp hst hA hB hρ hhi c f hf)

/-- Strong convergence of actual measured increments to the measured raw
increment. Only L² input convergence is needed once every input belongs to
the sufficient regularity domain; no uniform higher norm is assumed
(`app:ch_background:eq:bg-density-twice`,
`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem measuredIncrement_raw_tendsto (c : ℝ) (f : ℕ → CarrierL2 n) (g : CarrierL2 n)
    (hf : ∀ k, CarrierWeightedMem (etaBesselWeight (s + 1)) (f k))
    (hg : CarrierWeightedMem (etaBesselWeight (s + 1)) g)
    (hlim : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun k ↦ (measuredIncrement_raw_memLp d s hs χ hχ U hU hk hK hsupp hst
      hA hB hρ hhi c (f k) (hf k)).toLp _) atTop
      (𝓝 ((measuredIncrement_raw_memLp d s hs χ hχ U hU hk hK hsupp hst
        hA hB hρ hhi c g hg).toLp _)) := by
  have he (u : CarrierL2 n) (hu : CarrierWeightedMem (etaBesselWeight (s + 1)) u) :=
    measuredIncrement_raw_toLp d s hs χ hχ U hU hk hK hsupp hst hA hB hρ hhi c u hu
  rw [he g hg]
  exact (tendsto_const_nhds.smul
    ((carrierChannel U).continuous.tendsto g |>.comp hlim)).congr
      (fun k ↦ (he (f k) (hf k)).symm)

end Geometry
end JanetCartan.UncutDensity
