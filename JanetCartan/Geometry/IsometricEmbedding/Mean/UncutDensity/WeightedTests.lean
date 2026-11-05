module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.UncutDensity.Tests
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.MixedJetBound

/-!
# Compact test approximation in the existing transverse weighted domain

For `app:ch_background:eq:bg-density-twice`, approximate the weighted raw input
in L² and divide the tests by the positive Bessel weight. This constructs the
approximation needed for literal kernel evaluation, without a spatial cutoff
or a frequency truncation in the resulting density. The domain is the existing
`CarrierWeightedMem`, a necessary consequence of the full mixed raw regularity.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace JanetCartan.UncutDensity
open ContinuumRow RawCutoffBounds ContinuumAdjoint.DensityMultiplier

variable {n : ℕ}

/-- Positivity of the existing transverse weight used in the domain passage
for `app:ch_background:eq:bg-density-twice`. -/
theorem etaBesselWeight_pos (s : ℕ) (p : CarrierVariable n) :
    0 < etaBesselWeight s p := by unfold etaBesselWeight; positivity

/-- The reciprocal weight is smooth even at zero frequency; this is used to
construct actual compact smooth tests for `app:ch_background:eq:bg-density-twice`. -/
theorem contDiff_inv_etaBesselWeight (s : ℕ) :
    ContDiff ℝ ∞ (fun p : CarrierVariable n ↦ (etaBesselWeight s p)⁻¹) := by
  have h : ContDiff ℝ ∞ (etaBesselWeight (n := n) s) :=
    ((contDiff_const.add ((contDiff_norm_sq ℝ).comp contDiff_snd)).sqrt
      (fun p ↦ by dsimp; positivity)).pow s
  exact h.inv (fun p ↦ ne_of_gt (etaBesselWeight_pos s p))

/-- Division by the Bessel weight preserves the shared test domain
(`app:ch_background:eq:bg-density-twice`). -/
def divideWeightTest (s : ℕ) (u : carrierInitialTestSpace n) :
    carrierInitialTestSpace n :=
  ⟨fun p ↦ (etaBesselWeight s p)⁻¹ • u.val p,
    (contDiff_inv_etaBesselWeight s).smul u.property.1, u.property.2.smul_left (f := fun p ↦ (etaBesselWeight s p)⁻¹)⟩

/-- The reciprocal weight is a bounded multiplier on the original L² space,
used only to prove convergence (`app:ch_background:eq:bg-density-twice`). -/
def inverseWeightMask (s : ℕ) : Lp ℝ (⊤ : ENNReal) (carrierMeasure n) :=
  carrierMask (fun p ↦ (etaBesselWeight s p)⁻¹)
    (contDiff_inv_etaBesselWeight s).continuous.aestronglyMeasurable
    (Eventually.of_forall fun p ↦ ⟨inv_nonneg.mpr (etaBesselWeight_nonneg s p),
      inv_le_one_of_one_le₀ (by
        simpa [etaBesselWeight] using etaBesselWeight_mono (n := n) (Nat.zero_le s) p)⟩)

/-- Literal representative of reciprocal multiplication, for the domain
passage in `app:ch_background:eq:bg-density-twice`. -/
theorem inverseWeightMask_coeFn (s : ℕ) :
    inverseWeightMask (n := n) s =ᵐ[carrierMeasure n]
      fun p ↦ (etaBesselWeight s p)⁻¹ := by
  unfold inverseWeightMask
  exact carrierMask_coeFn _ _ _

/-- Dividing a smooth test agrees with the existing bounded multiplier,
so the same raw L² topology is retained (`app:ch_background:eq:bg-density-twice`). -/
theorem divideWeightTest_toLp (s : ℕ) (u : carrierInitialTestSpace n) :
    carrierInitialTestToLp (divideWeightTest s u) =
      carrierMultiplier (inverseWeightMask s) (carrierInitialTestToLp u) := by
  apply Lp.ext
  filter_upwards [(carrierInitialTest_memLp (divideWeightTest s u)).coeFn_toLp,
    carrierMultiplier_coeFn (inverseWeightMask s) (carrierInitialTestToLp u),
    inverseWeightMask_coeFn (n := n) s, (carrierInitialTest_memLp u).coeFn_toLp]
    with p hp hq hr ht
  change carrierInitialTestToLp u p = u.val p at ht
  exact hp.trans (by rw [hq, hr, ht]; rfl)

/-- The inverse multiplier recovers the original raw datum from its weighted
class (`app:ch_background:eq:bg-density-twice`). -/
theorem inverseWeight_weightedInput (s : ℕ) (f : CarrierL2 n)
    (hf : CarrierWeightedMem (etaBesselWeight s) f) :
    carrierMultiplier (inverseWeightMask s) (hf.toLp _) = f := by
  apply Lp.ext
  filter_upwards [carrierMultiplier_coeFn (inverseWeightMask s) (hf.toLp _),
    inverseWeightMask_coeFn (n := n) s, hf.coeFn_toLp] with p hp hq hr
  rw [hp, hq, hr, smul_smul, inv_mul_cancel₀ (ne_of_gt (etaBesselWeight_pos s p)),
    one_smul]

/-- Construct compact smooth approximations of every weighted raw input. Both
weighted and unweighted convergence are proved; neither is a hypothesis on an
output or a transported density (`app:ch_background:eq:bg-density-twice`). -/
theorem exists_weighted_test_approximation (s : ℕ) (f : CarrierL2 n)
    (hf : CarrierWeightedMem (etaBesselWeight s) f) :
    ∃ u : ℕ → carrierInitialTestSpace n,
      Tendsto (fun k ↦ carrierInitialTestToLp (u k)) atTop (𝓝 (hf.toLp _)) ∧
      Tendsto (fun k ↦ carrierInitialTestToLp (divideWeightTest s (u k)))
        atTop (𝓝 f) := by
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp
    (denseRange_carrierInitialTestToLp (hf.toLp _))
  choose u hu using hv
  refine ⟨u, hlim.congr (fun k ↦ (hu k).symm), ?_⟩
  have ht := (carrierMultiplier (inverseWeightMask s)).continuous.tendsto
    (hf.toLp _) |>.comp hlim
  rw [inverseWeight_weightedInput s f hf] at ht
  exact ht.congr (fun k ↦ by rw [divideWeightTest_toLp, hu]; rfl)

end JanetCartan.UncutDensity
