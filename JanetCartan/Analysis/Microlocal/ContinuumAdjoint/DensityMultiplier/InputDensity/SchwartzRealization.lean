module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputDensity.SchwartzTests
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend

/-!
# Schwartz realization in the full raw Sobolev space

For `app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`, the forward partial Fourier estimate
bounds compact frequency tests in the full raw norm by their weighted carrier
jets. Each jet is bounded by a continuous finite Schwartz seminorm and a fixed
integrable decay weight for the literal product measure. The compact realization
is consequently continuous and extends to all Schwartz data, since the explicit
expanding cutoffs converge in Schwartz topology and the raw space is complete.

The resulting map and its raw L² identity supply exactly `R` and `hR` in
`InputDensity.denseRange_rawTestSobolev_of_schwartz`. The separate Schwartz
preimage construction and final density assembly are not assumed here. No reverse
mixed-jet estimate or replacement Sobolev scale is used.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped SchwartzMap Topology ContDiff

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev
variable {n : ℕ}

private theorem carrierMeasure_temperate (n : ℕ) :
    (carrierMeasure n).HasTemperateGrowth := by
  let : (volume : Measure CarrierParameter).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  let : (carrierMeasure n).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  infer_instance

private theorem etaBesselWeight_le (t : ℕ) (x : CarrierVariable n) :
    etaBesselWeight t x ≤ (1 + ‖x‖) ^ t := by
  apply pow_le_pow_left₀ (Real.sqrt_nonneg _) _
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have h := norm_snd_le x
    nlinarith [norm_nonneg x, norm_nonneg x.2]

private theorem schwartz_weightedCarrierJet_bound (q k t : ℕ)
    (f : 𝓢(CarrierVariable n, ℂ)) (x : CarrierVariable n) :
    ‖weightedCarrierJet k t f x‖ ≤
      (2 ^ (q + t) * (Finset.Iic (q + t, k)).sup
        (schwartzSeminormFamily ℂ (CarrierVariable n) ℂ) f) *
          (1 + ‖x‖) ^ (-(q : ℝ)) := by
  have hx : 0 < 1 + ‖x‖ := by positivity
  rw [Real.rpow_neg hx.le, Real.rpow_natCast, ← div_eq_mul_inv,
    le_div_iff₀ (pow_pos hx q)]
  calc
    _ ≤ ((1 + ‖x‖) ^ t * ‖iteratedFDeriv ℝ k f x‖) * (1 + ‖x‖) ^ q := by
      gcongr
      simp only [weightedCarrierJet, norm_smul,
        Real.norm_of_nonneg (etaBesselWeight_nonneg _ _)]
      exact mul_le_mul (etaBesselWeight_le t x)
        (norm_carrierJet_le_fullJet k (f.smooth ⊤) x) (norm_nonneg _) (by positivity)
    _ = (1 + ‖x‖) ^ (q + t) * ‖iteratedFDeriv ℝ k f x‖ := by rw [pow_add]; ring
    _ ≤ _ := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (q + t, k)) le_rfl le_rfl f x

private theorem exists_schwartz_jet_bound (k t : ℕ) :
    ∃ B : 𝓢(DensityEuclidean n, ℂ) → ℝ,
      Continuous B ∧ B 0 = 0 ∧ ∀ f : 𝓢(DensityEuclidean n, ℂ),
        lpNorm (weightedCarrierJet k t (f ∘ densityCoordinates n))
          2 (carrierMeasure n) ≤ B f := by
  obtain ⟨q, hq⟩ := (carrierMeasure_temperate n).exists_eLpNorm_lt_top 2
  let w : CarrierVariable n → ℝ := fun x ↦ (1 + ‖x‖) ^ (-(q : ℝ))
  have hw : MemLp w 2 (carrierMeasure n) := hq
  let P := (Finset.Iic (q + t, k)).sup (schwartzSeminormFamily ℂ (CarrierVariable n) ℂ)
  let T : 𝓢(DensityEuclidean n, ℂ) →L[ℂ] 𝓢(CarrierVariable n, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (densityCoordinates n)
  refine ⟨fun f ↦ (2 ^ (q + t) * P (T f)) * lpNorm w 2 (carrierMeasure n), ?_, ?_, ?_⟩
  · exact (((Seminorm.continuous_finsetSup fun i _ ↦
      (schwartz_withSeminorms ℂ (CarrierVariable n) ℂ).continuous_seminorm i).comp
        T.continuous).const_mul _).mul_const _
  · simp
  · intro f
    calc
      _ ≤ lpNorm ((2 ^ (q + t) * P (T f)) • w) 2 (carrierMeasure n) :=
        lpNorm_mono_real (hw.const_smul _) (schwartz_weightedCarrierJet_bound q k t (T f))
      _ = _ := by
        rw [lpNorm_const_smul, coe_nnnorm, Real.norm_of_nonneg (by positivity)]


private theorem exists_compactSchwartz_raw_bound (s : ℕ) :
    ∃ B : 𝓢(DensityEuclidean n, ℂ) → ℝ,
      Continuous B ∧ B 0 = 0 ∧ ∀ (f : 𝓢(DensityEuclidean n, ℂ))
        (hf : HasCompactSupport (f : DensityEuclidean n → ℂ)),
        ‖rawTestSobolev s (rawSchwartzTest f hf)‖ ≤ B f := by
  obtain ⟨C, hC, hbound⟩ := exists_partialUnitaryInverse_test_sobolev_bound (n := n) s
  choose B hB hB0 hboundB using fun k ↦ exists_schwartz_jet_bound (n := n) k (s - k)
  refine ⟨fun f ↦ C * ∑ k ∈ Finset.range (s + 1), B k f, ?_, ?_, ?_⟩
  · exact (continuous_finsetSum _ fun k _ ↦ hB k).const_mul C
  · simp [hB0]
  · intro f hf
    rw [norm_rawTestSobolev]
    exact (hbound (rawSchwartzTest f hf)).2.trans
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ ↦ hboundB k f) hC)

private abbrev compactSchwartz : Submodule ℂ 𝓢(DensityEuclidean n, ℂ) where
  carrier := {f | HasCompactSupport (f : DensityEuclidean n → ℂ)}
  zero_mem' := by simp [HasCompactSupport]
  add_mem' hf hg := hf.add hg
  smul_mem' c f hf := hf.smul_left

private instance : IsUniformAddGroup (compactSchwartz (n := n)) :=
  IsUniformInducing.isUniformAddGroup (compactSchwartz (n := n)).subtype
    isUniformEmbedding_subtype_val.isUniformInducing

private theorem denseRange_compactSchwartz :
    DenseRange (compactSchwartz (n := n)).subtypeL := by
  intro f
  exact mem_closure_of_tendsto (Pseudodifferential.CompactSchwartz.tendsto_truncate f)
    (Eventually.of_forall fun j ↦ ⟨⟨Pseudodifferential.CompactSchwartz.truncate f j,
      Pseudodifferential.CompactSchwartz.truncate_hasCompactSupport f j⟩, rfl⟩)

private def compactRawLinear (s : ℕ) :
    compactSchwartz (n := n) →ₗ[ℂ] RawSobolevSpace n s where
  toFun f := rawTestSobolev s (rawSchwartzTest f.val f.property)
  map_add' f g := by
    apply RawSobolevSpace.toRawL2_injective s
    simp only [map_add, toRawL2_rawTestSobolev, carrierInitialTestToLp_rawSchwartzTest,
      Submodule.coe_add]
  map_smul' c f := by
    apply RawSobolevSpace.toRawL2_injective s
    simp only [map_smul, toRawL2_rawTestSobolev, carrierInitialTestToLp_rawSchwartzTest,
      Submodule.coe_smul, RingHom.id_apply]

private theorem continuous_compactRawLinear (s : ℕ) :
    Continuous (compactRawLinear (n := n) s) := by
  obtain ⟨B, hB, hB0, hbound⟩ := exists_compactSchwartz_raw_bound (n := n) s
  have hb (f : compactSchwartz (n := n)) : ‖compactRawLinear s f‖ ≤ B f.val :=
    hbound f.val f.property
  have ht : Tendsto (fun f : compactSchwartz (n := n) ↦ B f.val) (𝓝 0) (𝓝 0) := by
    simpa only [Function.comp_def, Submodule.subtypeL_apply, Submodule.coe_zero, hB0] using
      (hB.comp (compactSchwartz (n := n)).subtypeL.continuous).tendsto 0
  exact continuous_of_tendsto_nhds_zero (compactRawLinear s) (squeeze_zero_norm hb ht)

private def compactRawContinuous (s : ℕ) :
    compactSchwartz (n := n) →L[ℂ] RawSobolevSpace n s :=
  ⟨compactRawLinear s, continuous_compactRawLinear s⟩

/-- Continuous realization of Schwartz data in the existing full raw Sobolev
space, for `app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`. The forward partial Fourier bound
controls compact tests by continuous Schwartz seminorms. Extension along the
dense compact Schwartz subspace therefore takes place in the complete full raw
norm, with the original product measure and unitary radian convention. This
supplies `R` in `denseRange_rawTestSobolev_of_schwartz`. -/
@[no_expose] def rawSchwartzSobolev (s : ℕ) :
    𝓢(DensityEuclidean n, ℂ) →L[ℂ] RawSobolevSpace n s :=
  (compactRawContinuous s).extend (compactSchwartz (n := n)).subtypeL

/-- The continuous full-norm realization retains exactly the Schwartz raw L²
class (`app:ch_background:prop:bg-adjoint`). This supplies `hR` in
`denseRange_rawTestSobolev_of_schwartz`, without a reverse mixed-jet comparison. -/
@[simp] theorem toRawL2_rawSchwartzSobolev (s : ℕ) (f : 𝓢(DensityEuclidean n, ℂ)) :
    RawSobolevSpace.toRawL2 s (rawSchwartzSobolev s f) = rawSchwartzToL2 n f := by
  refine denseRange_compactSchwartz.induction_on f
    (isClosed_eq ((RawSobolevSpace.toRawL2 s).continuous.comp
      (rawSchwartzSobolev s).continuous) (rawSchwartzToL2 n).continuous) ?_
  intro g
  rw [rawSchwartzSobolev, ContinuousLinearMap.extend_eq _ denseRange_compactSchwartz
    isUniformEmbedding_subtype_val.isUniformInducing]
  exact (toRawL2_rawTestSobolev s _).trans
    (carrierInitialTestToLp_rawSchwartzTest g.val g.property)

/-- Every Schwartz raw datum belongs to the existing full raw Sobolev level.
This is actual membership for the realization used in
`app:ch_background:eq:bg-density-adjoint`, with no additional analytic premise. -/
theorem rawSchwartzToL2_memRawSobolev (s : ℕ) (f : 𝓢(DensityEuclidean n, ℂ)) :
    MemRawSobolev s (rawSchwartzToL2 n f) := by
  rw [← toRawL2_rawSchwartzSobolev s f]
  exact RawSobolevSpace.toRawL2_mem s _

end JanetCartan.ContinuumAdjoint.DensityMultiplier
