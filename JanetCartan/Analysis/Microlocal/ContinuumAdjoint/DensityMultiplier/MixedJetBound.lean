module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.TestDomain
public import Mathlib.Data.Nat.Choose.Sum

/-!
# The total mixed test-function estimate

For `app:ch_background:eq:bg-density-adjoint`, sum the carrier Leibniz estimates
at the actual total order: a term with `k` carrier derivatives has only `s-k`
transverse weights. The exact half-order symbol therefore costs one total
integer derivative, not one derivative in each variable separately.

`mixedCarrierJetNorm` is a numerical aggregate on smooth functions, not a new
Sobolev space. Its comparison with the shared weak graph norm after partial
inverse Fourier transformation remains the responsibility of the assembly.
The output integrability and estimate below follow from the fixed mask and
input integrability; neither is an input hypothesis.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow
variable {n : ℕ}

/-- Transverse weights increase with the integer order, as used when summing
the carrier Leibniz terms in `app:ch_background:eq:bg-density-adjoint`. -/
theorem etaBesselWeight_mono {s t : ℕ} (hst : s ≤ t) (x : CarrierVariable n) :
    etaBesselWeight s x ≤ etaBesselWeight t x := by
  apply pow_le_pow_right₀ _ hst
  exact Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg ‖x.2‖])

/-- Lower transverse weights preserve finite jet energy. This is the
triangular total-order bookkeeping of `app:ch_background:eq:bg-density-adjoint`. -/
theorem memLp_weightedCarrierJet_mono (k : ℕ) {s t : ℕ} (hst : s ≤ t)
    {f : CarrierVariable n → ℂ} (hf : ContDiff ℝ ∞ f)
    (hmem : MemLp (weightedCarrierJet k t f) 2 (carrierMeasure n)) :
    MemLp (weightedCarrierJet k s f) 2 (carrierMeasure n) := by
  apply hmem.mono (continuous_weightedCarrierJet k s hf).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  simp only [weightedCarrierJet, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (etaBesselWeight_nonneg _ _)]
  exact mul_le_mul_of_nonneg_right (etaBesselWeight_mono hst x) (norm_nonneg _)

/-- The same transverse-weight comparison for the actual L² jet norms
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem lpNorm_weightedCarrierJet_mono (k : ℕ) {s t : ℕ} (hst : s ≤ t)
    {f : CarrierVariable n → ℂ}
    (hmem : MemLp (weightedCarrierJet k t f) 2 (carrierMeasure n)) :
    lpNorm (weightedCarrierJet k s f) 2 (carrierMeasure n) ≤
      lpNorm (weightedCarrierJet k t f) 2 (carrierMeasure n) := by
  rw [← lpNorm_norm hmem.aestronglyMeasurable]
  apply lpNorm_mono_real hmem.norm
  intro x
  simp only [weightedCarrierJet, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (etaBesselWeight_nonneg _ _)]
  exact mul_le_mul_of_nonneg_right (etaBesselWeight_mono hst x) (norm_nonneg _)

/-- A finite sum of actual smooth jet norms at total order `s`; no completion
or replacement of the shared raw domain is made here
(`app:ch_background:prop:bg-adjoint`). -/
def mixedCarrierJetNorm (s : ℕ) (f : CarrierVariable n → ℂ) : ℝ :=
  ∑ k ∈ Finset.range (s + 1),
    lpNorm (weightedCarrierJet k (s - k) f) 2 (carrierMeasure n)

/-- Nonnegativity of the smooth total-order aggregate
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem mixedCarrierJetNorm_nonneg (s : ℕ) (f : CarrierVariable n → ℂ) :
    0 ≤ mixedCarrierJetNorm s f :=
  Finset.sum_nonneg (fun _ _ ↦ lpNorm_nonneg)

/-- Each permitted mixed jet is controlled by the total-order aggregate;
lower-order terms from differentiating the mask obey the same bound
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem lpNorm_weightedCarrierJet_le_mixedCarrierJetNorm {s k t : ℕ}
    (hkt : k + t ≤ s) {f : CarrierVariable n → ℂ}
    (hmem : MemLp (weightedCarrierJet k (s - k) f) 2 (carrierMeasure n)) :
    lpNorm (weightedCarrierJet k t f) 2 (carrierMeasure n) ≤ mixedCarrierJetNorm s f := by
  refine (lpNorm_weightedCarrierJet_mono k (by omega : t ≤ s - k) hmem).trans ?_
  exact Finset.single_le_sum
    (s := Finset.range (s + 1))
    (f := fun j ↦ lpNorm (weightedCarrierJet j (s - j) f) 2 (carrierMeasure n))
    (fun _ _ ↦ lpNorm_nonneg) (Finset.mem_range.mpr (by omega : k < s + 1))

/-- Full total-order bound for the literal density symbol on smooth finite
energy data. All `z` derivatives of the mask are included, and the input loses
exactly one total integer derivative. The constant is chosen independently of
the datum (`app:ch_background:eq:bg-density-adjoint`). -/
theorem exists_densitySymbol_mixedJet_bound (s : ℕ)
    {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχsmooth : ContDiff ℝ ∞ χ) (hlow : ∀ r ≤ 1, χ r = 0)
    (hχ : ∀ r, |χ r| ≤ 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ f : CarrierVariable n → ℂ, ContDiff ℝ ∞ f →
      (∀ k ≤ s + 1, MemLp (weightedCarrierJet k (s + 1 - k) f) 2 (carrierMeasure n)) →
      (∀ k ≤ s, MemLp
        (weightedCarrierJet k (s - k) (fun x ↦ densityFrequencySymbol ρ χ x * f x))
          2 (carrierMeasure n)) ∧
      mixedCarrierJetNorm s (fun x ↦ densityFrequencySymbol ρ χ x * f x) ≤
        L * mixedCarrierJetNorm (s + 1) f := by
  obtain ⟨C, hC, hb⟩ :=
    exists_densitySymbol_jet_bound_of_compactSupport s hρ hcρ hχsmooth hlow hχ
  refine ⟨(s + 1 : ℕ) * ((2 : ℝ) ^ s * C), by positivity, ?_⟩
  intro f hf hmem
  have hjet k (hk : k ≤ s) := hb k hk (s - k) f hf (fun j hj ↦
    memLp_weightedCarrierJet_mono j (by omega : s - k + 1 ≤ s + 1 - j) hf
      (hmem j (by omega)))
  refine ⟨fun k hk ↦ (hjet k hk).1, ?_⟩
  have hbound k (hk : k ≤ s) :
      lpNorm (weightedCarrierJet k (s - k)
        (fun x ↦ densityFrequencySymbol ρ χ x * f x)) 2 (carrierMeasure n) ≤
      (2 : ℝ) ^ s * C * mixedCarrierJetNorm (s + 1) f := by
    calc
      _ ≤ ∑ i ∈ Finset.range (k + 1), ((k.choose i : ℝ) * C) *
          lpNorm (weightedCarrierJet (k - i) (s - k + 1) f) 2 (carrierMeasure n) :=
        (hjet k hk).2
      _ ≤ ∑ i ∈ Finset.range (k + 1), ((k.choose i : ℝ) * C) *
          mixedCarrierJetNorm (s + 1) f := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact lpNorm_weightedCarrierJet_le_mixedCarrierJetNorm (by omega)
          (hmem (k - i) (by omega))
      _ = (2 : ℝ) ^ k * C * mixedCarrierJetNorm (s + 1) f := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 2
        exact_mod_cast Nat.sum_range_choose k
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk) hC)
        (mixedCarrierJetNorm_nonneg _ _)
  calc
    _ ≤ ∑ _k ∈ Finset.range (s + 1),
        (2 : ℝ) ^ s * C * mixedCarrierJetNorm (s + 1) f :=
      Finset.sum_le_sum (fun k hk ↦ hbound k (by simpa using Finset.mem_range.mp hk))
    _ = _ := by simp [Nat.cast_add, Nat.cast_one, mul_assoc]

/-- On compact smooth tests, every input energy condition is automatic.
This is the total-order estimate to be transported by the shared partial
Plancherel theorem and extended by graph-norm density
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem exists_densitySymbol_mixedJet_test_bound (s : ℕ)
    {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχsmooth : ContDiff ℝ ∞ χ) (hlow : ∀ r ≤ 1, χ r = 0)
    (hχ : ∀ r, |χ r| ≤ 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ f : CarrierVariable n → ℂ,
      ContDiff ℝ ∞ f → HasCompactSupport f →
      mixedCarrierJetNorm s (fun x ↦ densityFrequencySymbol ρ χ x * f x) ≤
        L * mixedCarrierJetNorm (s + 1) f := by
  obtain ⟨L, hL, hb⟩ := exists_densitySymbol_mixedJet_bound s hρ hcρ hχsmooth hlow hχ
  exact ⟨L, hL, fun f hf hc ↦ (hb f hf (fun k _ ↦
    memLp_weightedCarrierJet_of_compactSupport k (s + 1 - k) hf hc)).2⟩

/-- The zero carrier jet is exactly the transverse weighted pointwise norm.
This connects the total-order estimate to the actual raw cutoff classes
(`app:ch_background:defn:bg-mixed`). -/
theorem norm_weightedCarrierJet_zero (s : ℕ) (f : CarrierVariable n → ℂ)
    (x : CarrierVariable n) :
    ‖weightedCarrierJet 0 s f x‖ = ‖etaBesselWeight s x • f x‖ := by
  simp only [weightedCarrierJet, norm_smul, norm_iteratedFDeriv_zero]

/-- The raw tail's existing weighted domain follows from finite zero-carrier
jet energy of a representative, on the same literal Lebesgue L² class
(`app:ch_background:defn:bg-mixed`). -/
theorem carrierWeightedMem_of_zeroJet (s : ℕ) (u : CarrierL2 n)
    {f : CarrierVariable n → ℂ} (he : u =ᵐ[carrierMeasure n] f)
    (hm : MemLp (weightedCarrierJet 0 s f) 2 (carrierMeasure n)) :
    RawCutoffBounds.CarrierWeightedMem (etaBesselWeight s) u := by
  apply hm.congr_norm
    ((continuous_etaBesselWeight s).aestronglyMeasurable.smul (Lp.aestronglyMeasurable u))
  filter_upwards [he] with x hx
  simp only [norm_weightedCarrierJet_zero, Pi.smul_apply', hx]

/-- The raw transverse weighted norm is bounded by the smooth mixed aggregate,
without extra constants or a change of measure. The shared graph-domain owner
can pass this estimate to limits (`app:ch_background:defn:bg-mixed`). -/
theorem carrierWeightedNorm_le_mixedCarrierJetNorm (s : ℕ) (u : CarrierL2 n)
    {f : CarrierVariable n → ℂ} (he : u =ᵐ[carrierMeasure n] f)
    (hm : MemLp (weightedCarrierJet 0 s f) 2 (carrierMeasure n)) :
    RawCutoffBounds.carrierWeightedNorm (etaBesselWeight s) u
        (carrierWeightedMem_of_zeroJet s u he hm) ≤ mixedCarrierJetNorm s f := by
  have heq : lpNorm (fun x ↦ etaBesselWeight s x • u x) 2 (carrierMeasure n) =
      lpNorm (weightedCarrierJet 0 s f) 2 (carrierMeasure n) := by
    apply congrArg ENNReal.toReal
    apply eLpNorm_congr_norm_ae
      ((continuous_etaBesselWeight s).aestronglyMeasurable.smul (Lp.aestronglyMeasurable u))
      hm.aestronglyMeasurable
    filter_upwards [he] with x hx
    simp only [norm_weightedCarrierJet_zero, Pi.smul_apply', hx]
  unfold RawCutoffBounds.carrierWeightedNorm
  erw [Lp.norm_toLp]
  rw [toReal_eLpNorm, heq]
  exact lpNorm_weightedCarrierJet_le_mixedCarrierJetNorm (by omega : 0 + s ≤ s)
    (by simpa using hm)

/-- The existing squared-cutoff tail estimate now consumes the actual total
mixed test energy on literal carrier classes (`main:eq:linear-two-errors`). -/
theorem carrierSquaredCutoff_tail_of_mixedJets {K : ℝ} (hK : 1 ≤ K) (s : ℕ)
    (m : Lp ℝ (⊤ : ENNReal) (carrierMeasure n)) (u : CarrierL2 n)
    (hm : ∀ᵐ x ∂carrierMeasure n, m x ∈ Set.Icc (0 : ℝ) 1)
    (hone : ∀ᵐ x ∂carrierMeasure n, u x ≠ 0 → ‖x.2‖ ≤ K → m x = 1)
    {f : CarrierVariable n → ℂ} (he : u =ᵐ[carrierMeasure n] f)
    (hf : MemLp (weightedCarrierJet 0 s f) 2 (carrierMeasure n)) :
    ‖u - RawCutoffBounds.carrierSquaredCutoff m u‖ ≤
      (K ^ s)⁻¹ * mixedCarrierJetNorm s f := by
  exact (RawCutoffBounds.carrierSquaredCutoff_tail hK s m u hm hone
    (etaBesselWeight s) (carrierWeightedMem_of_zeroJet s u he hf)
    (Filter.Eventually.of_forall (fun _ ↦ le_rfl))).trans
      (mul_le_mul_of_nonneg_left (carrierWeightedNorm_le_mixedCarrierJetNorm s u he hf)
        (by positivity))

/-- The total-order estimate applies to differences of compact smooth tests.
This gives the uniform continuity needed for the graph closure, rather than
assuming a bound on the completed operator
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem exists_densitySymbol_mixedJet_difference_bound (s : ℕ)
    {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχsmooth : ContDiff ℝ ∞ χ) (hlow : ∀ r ≤ 1, χ r = 0)
    (hχ : ∀ r, |χ r| ≤ 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ f g : CarrierVariable n → ℂ,
      ContDiff ℝ ∞ f → HasCompactSupport f →
      ContDiff ℝ ∞ g → HasCompactSupport g →
      mixedCarrierJetNorm s (fun x ↦ densityFrequencySymbol ρ χ x * f x -
          densityFrequencySymbol ρ χ x * g x) ≤
        L * mixedCarrierJetNorm (s + 1) (f - g) := by
  obtain ⟨L, hL, hb⟩ := exists_densitySymbol_mixedJet_test_bound s hρ hcρ hχsmooth hlow hχ
  refine ⟨L, hL, fun f g hf hcf hg hcg ↦ ?_⟩
  simpa only [Pi.sub_apply, mul_sub] using hb (f - g) (hf.sub hg) (hcf.sub hcg)

end JanetCartan.ContinuumAdjoint.DensityMultiplier
