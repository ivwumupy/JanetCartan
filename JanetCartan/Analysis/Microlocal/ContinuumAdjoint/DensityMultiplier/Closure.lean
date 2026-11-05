module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.WeightedL2
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Closure of the literal density multiplier on carrier L²

For `app:ch_background:eq:bg-density-adjoint`, strong L² limits preserve the
pointwise unbounded multiplier relation. Convergence of the existing weighted
input classes implies convergence of the exact half-order outputs. These are
closure ingredients for extending the smooth mixed-jet estimates; no new
Sobolev scale or density assertion is introduced here.

The partial Fourier identification, mixed weak derivatives, and density in the
full shared `X^s` graph norm remain the responsibility of `Mean/CarrierSobolev`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology
namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow RawCutoffBounds
variable {n : ℕ}

/-- The literal multiplication relation is closed under simultaneous strong
carrier L² convergence, even for an unbounded coefficient. This identifies the
frequency output after density extension (`app:ch_background:eq:bg-density-adjoint`). -/
theorem carrierMultiplier_relation_of_tendsto (b : CarrierVariable n → ℂ)
    {f g : ℕ → CarrierL2 n} {u v : CarrierL2 n}
    (hf : Tendsto f atTop (𝓝 u)) (hg : Tendsto g atTop (𝓝 v))
    (hfg : ∀ j, g j =ᵐ[carrierMeasure n] fun x ↦ b x * f j x) :
    v =ᵐ[carrierMeasure n] fun x ↦ b x * u x := by
  obtain ⟨σ, hσ, hσlim⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
  obtain ⟨τ, hτ, hτlim⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hg.comp hσ.tendsto_atTop)).exists_seq_tendsto_ae
  filter_upwards [hσlim, hτlim, ae_all_iff.mpr hfg] with x hx hy hxy
  have hlim := (tendsto_const_nhds (x := b x)).mul (hx.comp hτ.tendsto_atTop)
  have he : (fun j ↦ g (σ (τ j)) x) = (fun j ↦ b x * f (σ (τ j)) x) :=
    funext fun j ↦ hxy _
  exact tendsto_nhds_unique hy (he.symm ▸ hlim)

/-- A Cauchy sequence of weighted classes identifies the weighted class of
its unweighted L² limit. Membership is proved, not assumed. This is used to
close the multiplier estimates on raw data (`app:ch_background:eq:bg-density-adjoint`). -/
theorem carrierWeightedMem_and_tendsto_of_cauchySeq (w : CarrierVariable n → ℝ)
    {f : ℕ → CarrierL2 n} {u : CarrierL2 n}
    (hf : ∀ j, CarrierWeightedMem w (f j))
    (hlim : Tendsto f atTop (𝓝 u))
    (hc : CauchySeq (fun j ↦ (hf j).toLp (fun x ↦ w x • f j x))) :
    ∃ hu : CarrierWeightedMem w u,
      Tendsto (fun j ↦ (hf j).toLp (fun x ↦ w x • f j x)) atTop
        (𝓝 (hu.toLp (fun x ↦ w x • u x))) := by
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hc
  have he : v =ᵐ[carrierMeasure n] fun x ↦ w x • u x := by
    simpa only [Complex.real_smul] using carrierMultiplier_relation_of_tendsto
      (fun x ↦ (w x : ℂ)) hlim hv (fun j ↦ by
        simpa only [Complex.real_smul] using (hf j).coeFn_toLp)
  have hu : CarrierWeightedMem w u := (Lp.memLp v).ae_eq he
  refine ⟨hu, ?_⟩
  have hid : hu.toLp (fun x ↦ w x • u x) = v := Lp.ext (hu.coeFn_toLp.trans he.symm)
  rwa [hid]

/-- Difference estimate for the exact half-order output on the existing
weighted classes. The coefficient has no upper frequency cutoff
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem norm_weightedHalfOrderOutput_sub_le (s : ℕ)
    {a : CarrierVariable n → ℂ} (ha : AEStronglyMeasurable a (carrierMeasure n))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ᵐ x ∂carrierMeasure n, ‖a x‖ ≤ M)
    (f g : CarrierL2 n)
    (hf : CarrierWeightedMem (etaBesselWeight (s + 1)) f)
    (hg : CarrierWeightedMem (etaBesselWeight (s + 1)) g) :
    ‖weightedHalfOrderOutput s ha hM hbound f hf -
        weightedHalfOrderOutput s ha hM hbound g hg‖ ≤
      M * ‖hf.toLp (fun x ↦ etaBesselWeight (s + 1) x • f x) -
        hg.toLp (fun x ↦ etaBesselWeight (s + 1) x • g x)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (weightedHalfOrderOutput s ha hM hbound f hf)
    (weightedHalfOrderOutput s ha hM hbound g hg),
    Lp.coeFn_sub (hf.toLp _) (hg.toLp _),
    weightedHalfOrderOutput_coeFn s ha hM hbound f hf,
    weightedHalfOrderOutput_coeFn s ha hM hbound g hg,
    hf.coeFn_toLp, hg.coeFn_toLp, hbound] with x hout hin hfx hgx hfw hgw hx
  simp only [hout, hin, Pi.sub_apply, hfx, hgx, hfw, hgw, ← smul_sub, ← mul_sub]
  exact norm_weighted_halfOrderCoefficient_mul_le s hM x hx (f x - g x)

/-- Weighted input convergence implies strong convergence of the literal
half-order outputs. This supplies the continuity step for dense test
approximations (`app:ch_background:eq:bg-density-adjoint`). -/
theorem tendsto_weightedHalfOrderOutput (s : ℕ)
    {a : CarrierVariable n → ℂ} (ha : AEStronglyMeasurable a (carrierMeasure n))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ᵐ x ∂carrierMeasure n, ‖a x‖ ≤ M)
    {f : ℕ → CarrierL2 n} {u : CarrierL2 n}
    (hf : ∀ j, CarrierWeightedMem (etaBesselWeight (s + 1)) (f j))
    (hu : CarrierWeightedMem (etaBesselWeight (s + 1)) u)
    (hlim : Tendsto (fun j ↦ (hf j).toLp (fun x ↦ etaBesselWeight (s + 1) x • f j x))
      atTop (𝓝 (hu.toLp (fun x ↦ etaBesselWeight (s + 1) x • u x)))) :
    Tendsto (fun j ↦ weightedHalfOrderOutput s ha hM hbound (f j) (hf j)) atTop
      (𝓝 (weightedHalfOrderOutput s ha hM hbound u hu)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hlim ⊢
  exact squeeze_zero (fun j ↦ norm_nonneg _)
    (fun j ↦ norm_weightedHalfOrderOutput_sub_le s ha hM hbound (f j) u (hf j) hu)
    (by simpa using hlim.const_mul M)

/-- Closure from an approximating sequence needs only an unweighted L²
limit and Cauchy weighted inputs; it produces weighted membership and the
convergent half-order output. The separate scale construction supplies such
sequences for its graph domain (`app:ch_background:eq:bg-density-adjoint`). -/
theorem halfOrderOutput_closure (s : ℕ)
    {a : CarrierVariable n → ℂ} (ha : AEStronglyMeasurable a (carrierMeasure n))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ᵐ x ∂carrierMeasure n, ‖a x‖ ≤ M)
    {f : ℕ → CarrierL2 n} {u : CarrierL2 n}
    (hf : ∀ j, CarrierWeightedMem (etaBesselWeight (s + 1)) (f j))
    (hlim : Tendsto f atTop (𝓝 u))
    (hc : CauchySeq (fun j ↦
      (hf j).toLp (fun x ↦ etaBesselWeight (s + 1) x • f j x))) :
    ∃ hu : CarrierWeightedMem (etaBesselWeight (s + 1)) u,
      Tendsto (fun j ↦ weightedHalfOrderOutput s ha hM hbound (f j) (hf j)) atTop
        (𝓝 (weightedHalfOrderOutput s ha hM hbound u hu)) ∧
      ‖weightedHalfOrderOutput s ha hM hbound u hu‖ ≤
        M * carrierWeightedNorm (etaBesselWeight (s + 1)) u hu := by
  obtain ⟨hu, hweighted⟩ := carrierWeightedMem_and_tendsto_of_cauchySeq _ hf hlim hc
  exact ⟨hu, tendsto_weightedHalfOrderOutput s ha hM hbound hf hu hweighted,
    norm_weightedHalfOrderOutput_le s ha hM hbound u hu⟩

end JanetCartan.ContinuumAdjoint.DensityMultiplier
