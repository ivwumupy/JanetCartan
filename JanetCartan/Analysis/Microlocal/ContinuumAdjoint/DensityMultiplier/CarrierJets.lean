module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.Symbol
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Carrier derivatives of the half-order density multiplier

The carrier-variable Leibniz estimate in `app:ch_background:eq:bg-density-adjoint`.
These are actual strong derivatives on smooth data, with all transverse weights
integrated against the shared measure `dz dη`. No derivative in `η` is used as
an initial-coordinate derivative. The shared weak Sobolev scale and its density
theorem must still extend these estimates to the full graph domain.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier

open ContinuumRow

variable {n : ℕ}

/-- The actual `k`th carrier derivative with `t` transverse Bessel weights.
This is an individual jet, not a new Sobolev space
(`app:ch_background:prop:bg-adjoint`). -/
def weightedCarrierJet (k t : ℕ) (f : CarrierVariable n → ℂ) (x : CarrierVariable n) :
    CarrierParameter [×k]→L[ℝ] ℂ :=
  etaBesselWeight t x • iteratedFDeriv ℝ k (fun z ↦ f (z, x.2)) x.1

private theorem carrierJet_eq_restriction (k : ℕ) {f : CarrierVariable n → ℂ}
    (hf : ContDiff ℝ ∞ f) (x : CarrierVariable n) :
    iteratedFDeriv ℝ k (fun z ↦ f (z, x.2)) x.1 =
      (iteratedFDeriv ℝ k f x).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inl ℝ CarrierParameter (Euclidean (n - 1))) := by
  let L := ContinuousLinearMap.inl ℝ CarrierParameter (Euclidean (n - 1))
  have hg : ContDiff ℝ ∞ (fun y : CarrierVariable n ↦ f (y + (0, x.2))) :=
    hf.comp (contDiff_id.add contDiff_const)
  have he := L.iteratedFDeriv_comp_right hg x.1 (i := k) (by simp)
  simpa only [Function.comp_def, L, ContinuousLinearMap.inl_apply,
    Prod.mk_add_mk, add_zero, zero_add, iteratedFDeriv_comp_add_right] using he

/-- Restricting a full derivative to carrier directions does not enlarge its
norm. This transfers compact-mask bounds to the carrier Leibniz estimate
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem norm_carrierJet_le_fullJet (k : ℕ) {f : CarrierVariable n → ℂ}
    (hf : ContDiff ℝ ∞ f) (x : CarrierVariable n) :
    ‖iteratedFDeriv ℝ k (fun z ↦ f (z, x.2)) x.1‖ ≤ ‖iteratedFDeriv ℝ k f x‖ := by
  rw [carrierJet_eq_restriction k hf]
  calc
    _ ≤ ‖iteratedFDeriv ℝ k f x‖ * ∏ _ : Fin k,
        ‖ContinuousLinearMap.inl ℝ CarrierParameter (Euclidean (n - 1))‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ k f x‖ * ∏ _ : Fin k, (1 : ℝ) := by
      gcongr
      exact ContinuousLinearMap.norm_inl_le_one ℝ _ _
    _ = _ := by simp

/-- Joint continuity of the actual weighted carrier jet on smooth data
(`app:ch_background:prop:bg-adjoint`). -/
theorem continuous_weightedCarrierJet (k t : ℕ) {f : CarrierVariable n → ℂ}
    (hf : ContDiff ℝ ∞ f) : Continuous (weightedCarrierJet k t f) := by
  have hc := (ContinuousMultilinearMap.compContinuousLinearMapL
    (F := ℂ) (fun _ : Fin k ↦
      ContinuousLinearMap.inl ℝ CarrierParameter (Euclidean (n - 1)))).continuous.comp
        (hf.continuous_iteratedFDeriv (by simp : (k : ℕ∞ω) ≤ ∞))
  convert (continuous_etaBesselWeight t).smul hc using 1
  funext x
  change etaBesselWeight t x • iteratedFDeriv ℝ k (fun z ↦ f (z, x.2)) x.1 =
    etaBesselWeight t x • _
  rw [carrierJet_eq_restriction k hf]
  rfl

/-- The half-order factor is constant in every carrier derivative, including
at zero frequency (`app:ch_background:eq:bg-density-adjoint`). -/
theorem weightedCarrierJet_halfOrder_mul (k t : ℕ) {a f : CarrierVariable n → ℂ}
    (ha : ∀ η, ContDiff ℝ ∞ (fun z ↦ a (z, η)))
    (hf : ∀ η, ContDiff ℝ ∞ (fun z ↦ f (z, η))) (x : CarrierVariable n) :
    weightedCarrierJet k t (fun y ↦ halfOrderCoefficient a y * f y) x =
      Real.sqrt ‖x.2‖ • weightedCarrierJet k t (fun y ↦ a y * f y) x := by
  unfold weightedCarrierJet halfOrderCoefficient
  have he : (fun z : CarrierParameter ↦
      (Real.sqrt ‖x.2‖ : ℂ) * a (z, x.2) * f (z, x.2)) =
      (fun z ↦ Real.sqrt ‖x.2‖ • (a (z, x.2) * f (z, x.2))) := by
    ext z
    simp only [Complex.real_smul, mul_assoc]
  rw [he, iteratedFDeriv_const_smul_apply'
    (((ha x.2).mul (hf x.2)).of_le (by simp)).contDiffAt, smul_comm]

/-- The output jets are measurable despite the square root at zero: the
only derivatives here are in `z` (`app:ch_background:eq:bg-density-adjoint`). -/
theorem continuous_weightedCarrierJet_halfOrder_mul (k t : ℕ)
    {a f : CarrierVariable n → ℂ} (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) :
    Continuous (weightedCarrierJet k t (fun x ↦ halfOrderCoefficient a x * f x)) := by
  have ha' η : ContDiff ℝ ∞ (fun z : CarrierParameter ↦ a (z, η)) :=
    ha.comp (contDiff_id.prodMk contDiff_const)
  have hf' η : ContDiff ℝ ∞ (fun z : CarrierParameter ↦ f (z, η)) :=
    hf.comp (contDiff_id.prodMk contDiff_const)
  convert (Real.continuous_sqrt.comp continuous_snd.norm).smul
    (continuous_weightedCarrierJet k t (ha.mul hf)) using 1
  funext x
  exact weightedCarrierJet_halfOrder_mul k t ha' hf' x

/-- The full carrier Leibniz estimate for the exact half-order multiplier.
Each mask derivative has its own bound `M i`. Spending one transverse integer
derivative suffices, uniformly over all frequencies
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem norm_weightedCarrierJet_halfOrder_mul_le (k t : ℕ)
    {a f : CarrierVariable n → ℂ}
    (ha : ∀ η, ContDiff ℝ ∞ (fun z ↦ a (z, η)))
    (hf : ∀ η, ContDiff ℝ ∞ (fun z ↦ f (z, η)))
    (M : ℕ → ℝ) (hM : ∀ i ≤ k, 0 ≤ M i)
    (hbound : ∀ i ≤ k, ∀ x : CarrierVariable n,
      ‖iteratedFDeriv ℝ i (fun z ↦ a (z, x.2)) x.1‖ ≤ M i)
    (x : CarrierVariable n) :
    ‖weightedCarrierJet k t (fun y ↦ halfOrderCoefficient a y * f y) x‖ ≤
      ∑ i ∈ Finset.range (k + 1),
        ((k.choose i : ℝ) * M i) * ‖weightedCarrierJet (k - i) (t + 1) f x‖ := by
  rw [weightedCarrierJet_halfOrder_mul k t ha hf, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  simp only [weightedCarrierJet, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (etaBesselWeight_nonneg _ _)]
  calc
    _ ≤ Real.sqrt ‖x.2‖ * (etaBesselWeight t x *
        ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun z ↦ a (z, x.2)) x.1‖ *
          ‖iteratedFDeriv ℝ (k - i) (fun z ↦ f (z, x.2)) x.1‖) := by
      gcongr
      · exact etaBesselWeight_nonneg t x
      · exact norm_iteratedFDeriv_mul_le (ha x.2) (hf x.2) x.1 (by simp)
    _ = ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun z ↦ a (z, x.2)) x.1‖ *
          (etaBesselWeight t x * Real.sqrt ‖x.2‖) *
          ‖iteratedFDeriv ℝ (k - i) (fun z ↦ f (z, x.2)) x.1‖ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := by simpa using (Finset.mem_range.mp hi)
      have h := mul_le_mul (hbound i hik x) (etaBesselWeight_mul_sqrt_le t x)
        (mul_nonneg (etaBesselWeight_nonneg t x) (Real.sqrt_nonneg _)) (hM i hik)
      nlinarith [mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (k.choose i)),
        norm_nonneg (iteratedFDeriv ℝ (k - i) (fun z ↦ f (z, x.2)) x.1)]

/-- Integrated carrier Leibniz estimate on smooth members of the actual mixed
graph domain. Finite L² energies of the indicated input jets imply finite
output energy, as well as its bound. Thus integrability is proved, not inferred
from a possibly infinite seminorm (`app:ch_background:eq:bg-density-adjoint`). -/
theorem weightedCarrierJet_halfOrder_mul_memLp_and_bound (k t : ℕ)
    {a f : CarrierVariable n → ℂ} (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f)
    (M : ℕ → ℝ) (hM : ∀ i ≤ k, 0 ≤ M i)
    (hbound : ∀ i ≤ k, ∀ x : CarrierVariable n,
      ‖iteratedFDeriv ℝ i (fun z ↦ a (z, x.2)) x.1‖ ≤ M i)
    (hmem : ∀ j ≤ k, MemLp (weightedCarrierJet j (t + 1) f) 2 (carrierMeasure n)) :
    MemLp (weightedCarrierJet k t (fun x ↦ halfOrderCoefficient a x * f x))
        2 (carrierMeasure n) ∧
      lpNorm (weightedCarrierJet k t (fun x ↦ halfOrderCoefficient a x * f x))
        2 (carrierMeasure n) ≤
      ∑ i ∈ Finset.range (k + 1), ((k.choose i : ℝ) * M i) *
        lpNorm (weightedCarrierJet (k - i) (t + 1) f) 2 (carrierMeasure n) := by
  let v i := weightedCarrierJet (k - i) (t + 1) f
  let c i := (k.choose i : ℝ) * M i
  let g i := fun x ↦ c i * ‖v i x‖
  have hg i : MemLp (g i) 2 (carrierMeasure n) :=
    ((hmem (k - i) (Nat.sub_le _ _)).norm).const_mul (c i)
  have hsum := memLp_finsetSum (Finset.range (k + 1)) (fun i _ ↦ hg i)
  have hpt x := norm_weightedCarrierJet_halfOrder_mul_le k t
    (fun η ↦ ha.comp (contDiff_id.prodMk contDiff_const))
    (fun η ↦ hf.comp (contDiff_id.prodMk contDiff_const)) M hM hbound x
  constructor
  · exact hsum.mono' (continuous_weightedCarrierJet_halfOrder_mul k t ha hf).aestronglyMeasurable
      (Filter.Eventually.of_forall hpt)
  · calc
      _ ≤ lpNorm (fun x ↦ ∑ i ∈ Finset.range (k + 1), g i x) 2 (carrierMeasure n) :=
        lpNorm_mono_real hsum hpt
      _ ≤ ∑ i ∈ Finset.range (k + 1), lpNorm (g i) 2 (carrierMeasure n) := by
        have he : (fun x ↦ ∑ i ∈ Finset.range (k + 1), g i x) =
            ∑ i ∈ Finset.range (k + 1), g i := by ext x; simp
        rw [he]
        exact lpNorm_sum_le (fun i (_ : i ∈ Finset.range (k + 1)) ↦ hg i)
          (by norm_num : (1 : ENNReal) ≤ 2)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        have hc : 0 ≤ c i := mul_nonneg (Nat.cast_nonneg _)
          (hM i (by simpa using Finset.mem_range.mp hi))
        change lpNorm ((c i) • (fun x ↦ ‖v i x‖)) 2 (carrierMeasure n) = _
        rw [lpNorm_const_smul, lpNorm_norm (hmem (k - i) (Nat.sub_le _ _)).aestronglyMeasurable]
        simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hc, c]

/-- Every carrier derivative of the fixed angular/high mask is bounded by
the corresponding derivative of `ρ` on unit directions. No bounds at the
zero direction and no frequency ceiling are needed
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem norm_carrierJet_angularHighMask_le (k : ℕ)
    {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
    (hρ : ∀ θ, ContDiff ℝ ∞ (fun z ↦ ρ (z, θ)))
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ z θ, ‖θ‖ = 1 →
      ‖iteratedFDeriv ℝ k (fun w ↦ ρ (w, θ)) z‖ ≤ M)
    (hχ : ∀ r, |χ r| ≤ 1) (hχ0 : χ 0 = 0) (x : CarrierVariable n) :
    ‖iteratedFDeriv ℝ k (fun z ↦ angularHighMask ρ χ (z, x.2)) x.1‖ ≤ M := by
  unfold angularHighMask
  dsimp only
  rw [iteratedFDeriv_const_smul_apply' ((hρ _).of_le (by simp)).contDiffAt,
    norm_smul, Real.norm_eq_abs]
  by_cases hx : x.2 = 0
  · simpa [hx, hχ0] using hM
  · have hn : ‖‖x.2‖⁻¹ • x.2‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
    exact (mul_le_mul (hχ _) (hbound _ _ hn) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul _)

/-- The high cutoff removes the angular singularity at zero. Thus the literal
mask is jointly smooth in the carrier and frequency variables; this is used
only for measurability of carrier jets, not for taking frequency derivatives
as initial derivatives (`app:ch_background:eq:bg-density-adjoint`). -/
theorem contDiff_angularHighMask {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hχ : ContDiff ℝ ∞ χ)
    (hlow : ∀ r ≤ 1, χ r = 0) : ContDiff ℝ ∞ (angularHighMask ρ χ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x.2 = 0
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    have he : ∀ᶠ y : CarrierVariable n in nhds x, ‖y.2‖ < 1 :=
      continuous_snd.norm.continuousAt.eventually_lt continuousAt_const (by simp [hx])
    filter_upwards [he] with y hy
    simp [angularHighMask, hlow _ hy.le]
  · have hn : ContDiffAt ℝ ∞ (fun y : CarrierVariable n ↦ ‖y.2‖) x :=
      contDiffAt_snd.norm ℝ hx
    exact (hχ.contDiffAt.comp x hn).smul
      (hρ.contDiffAt.comp x (contDiffAt_fst.prodMk
        ((hn.inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_snd)))

/-- The integrated mixed-jet bound specialized to the paper's angular/high
symbol. Its hypotheses concern the smooth masks and the input jet energies;
the output integrability and estimate are proved
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem weightedCarrierJet_densitySymbol_memLp_and_bound (k t : ℕ)
    {ρ f : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hf : ContDiff ℝ ∞ f) (hχsmooth : ContDiff ℝ ∞ χ)
    (hlow : ∀ r ≤ 1, χ r = 0) (hχ : ∀ r, |χ r| ≤ 1)
    (M : ℕ → ℝ) (hM : ∀ i ≤ k, 0 ≤ M i)
    (hbound : ∀ i ≤ k, ∀ z θ, ‖θ‖ = 1 →
      ‖iteratedFDeriv ℝ i (fun w ↦ ρ (w, θ)) z‖ ≤ M i)
    (hmem : ∀ j ≤ k, MemLp (weightedCarrierJet j (t + 1) f) 2 (carrierMeasure n)) :
    MemLp (weightedCarrierJet k t (fun x ↦ densityFrequencySymbol ρ χ x * f x))
        2 (carrierMeasure n) ∧
      lpNorm (weightedCarrierJet k t (fun x ↦ densityFrequencySymbol ρ χ x * f x))
        2 (carrierMeasure n) ≤
      ∑ i ∈ Finset.range (k + 1), ((k.choose i : ℝ) * M i) *
        lpNorm (weightedCarrierJet (k - i) (t + 1) f) 2 (carrierMeasure n) :=
  weightedCarrierJet_halfOrder_mul_memLp_and_bound k t
    (contDiff_angularHighMask hρ hχsmooth hlow) hf M hM
    (fun i hi x ↦ norm_carrierJet_angularHighMask_le i
      (fun _θ ↦ hρ.comp (contDiff_id.prodMk contDiff_const)) (hM i hi)
      (hbound i hi) hχ (hlow 0 zero_le_one) x) hmem

end JanetCartan.ContinuumAdjoint.DensityMultiplier
