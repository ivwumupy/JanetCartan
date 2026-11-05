module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.GraphClosure
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.Weights

/-!
# Splitting the full physical Fourier weight

For `app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`, the full weight is bounded by the
sum of its carrier and transverse restrictions. Thus the test estimate can
be assembled from parameter differentiation and transverse weighted
Plancherel separately, without any extra derivatives in η.

The restrictions below are evaluations of the existing `initialWeight`,
not definitions of a replacement Sobolev space. The two restricted estimates
remain analytic obligations of the test-estimate construction.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev
variable {n : ℕ}

/-- The full physical weight is bounded by the sum of its restrictions to
all three carrier coordinates and all `n - 1` transverse coordinates. This
is the pointwise comparison used to assemble the compact-test estimate for
`app:ch_background:eq:bg-density-adjoint`. -/
theorem initialWeight_le_split_sum (s : ℕ) (ξ : CarrierVariable n) :
    initialWeight s ξ ≤ (2 : ℝ) ^ (s - 1) *
      (initialWeight s (ξ.1, (0 : Euclidean (n - 1))) +
        initialWeight s ((0 : CarrierParameter), ξ.2)) := by
  let a := 1 + (2 * Real.pi) ^ 2 * (|ξ.1.1| ^ 2 + ‖ξ.1.2‖ ^ 2)
  let b := 1 + (2 * Real.pi) ^ 2 * ‖ξ.2‖ ^ 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hab : 0 ≤ a + b - 1 := by
    have ha' : 1 ≤ a := by
      dsimp [a]
      exact le_add_of_nonneg_right (by positivity)
    linarith
  have he : initialWeight s ξ = Real.sqrt (a + b - 1) ^ s := by
    rw [initialWeight_eq_coordinates]
    have he : 1 + (2 * Real.pi) ^ 2 *
        (|ξ.1.1| ^ 2 + ‖ξ.1.2‖ ^ 2 + ‖ξ.2‖ ^ 2) = a + b - 1 := by
      dsimp [a, b]; ring
    rw [he, Real.rpow_div_two_eq_sqrt _ hab, Real.rpow_natCast]
  have hea : initialWeight s (ξ.1, (0 : Euclidean (n - 1))) = Real.sqrt a ^ s := by
    rw [initialWeight_eq_coordinates]
    simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
    rw [Real.rpow_div_two_eq_sqrt _ ha, Real.rpow_natCast]
  have heb : initialWeight s ((0 : CarrierParameter), ξ.2) = Real.sqrt b ^ s := by
    rw [initialWeight_eq_coordinates]
    simp only [Prod.fst_zero, Prod.snd_zero, abs_zero, norm_zero,
      zero_pow (by decide : 2 ≠ 0), zero_add]
    rw [Real.rpow_div_two_eq_sqrt _ hb, Real.rpow_natCast]
  rw [he, hea, heb]
  calc
    _ ≤ (Real.sqrt a + Real.sqrt b) ^ s := by
      apply pow_le_pow_left₀ (Real.sqrt_nonneg _)
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
        mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
    _ ≤ _ := add_pow_le (Real.sqrt_nonneg a) (Real.sqrt_nonneg b) s

/-- Finite energy for the two restricted weights implies full physical
Sobolev membership, with their numerical norm sum controlling the result.
The compact-test Plancherel producers must supply both hypotheses before
this implication proves the estimate in `app:ch_background:eq:bg-density-adjoint`. -/
theorem physicalSobolev_of_split_weight_memLp (s : ℕ) (u : CarrierL2 n)
    (hz : MemLp (fun ξ : CarrierVariable n =>
      initialWeight s (ξ.1, (0 : Euclidean (n - 1))) • initialFourier n u ξ)
      2 (carrierMeasure n))
    (hη : MemLp (fun ξ : CarrierVariable n =>
      initialWeight s ((0 : CarrierParameter), ξ.2) • initialFourier n u ξ)
      2 (carrierMeasure n)) :
    MemPhysicalSobolev s u ∧ physicalSobolevNorm s u ≤ (2 : ℝ) ^ (s - 1) *
      (lpNorm (fun ξ : CarrierVariable n =>
        initialWeight s (ξ.1, (0 : Euclidean (n - 1))) • initialFourier n u ξ)
        2 (carrierMeasure n) +
      lpNorm (fun ξ : CarrierVariable n =>
        initialWeight s ((0 : CarrierParameter), ξ.2) • initialFourier n u ξ)
        2 (carrierMeasure n)) := by
  let p := fun ξ : CarrierVariable n =>
    initialWeight s (ξ.1, (0 : Euclidean (n - 1))) • initialFourier n u ξ
  let q := fun ξ : CarrierVariable n =>
    initialWeight s ((0 : CarrierParameter), ξ.2) • initialFourier n u ξ
  let g := (fun ξ => ‖p ξ‖) + (fun ξ => ‖q ξ‖)
  let C := (2 : ℝ) ^ (s - 1)
  have hC : 0 ≤ C := by positivity
  have hg : MemLp g 2 (carrierMeasure n) := hz.norm.add hη.norm
  have hb (ξ : CarrierVariable n) :
      ‖initialWeight s ξ • initialFourier n u ξ‖ ≤ (C • g) ξ := by
    simp only [p, q, g, Pi.add_apply, Pi.smul_apply, smul_eq_mul, norm_smul,
      Real.norm_eq_abs, abs_of_pos (initialWeight_pos _ _)]
    simpa only [C, mul_add, add_mul, mul_assoc] using
      mul_le_mul_of_nonneg_right (initialWeight_le_split_sum s ξ)
        (norm_nonneg (initialFourier n u ξ))
  have hm : MemPhysicalSobolev s u :=
    (hg.const_smul C).mono (aestronglyMeasurable_weightedInitialFourier s u)
      (.of_forall fun ξ => (hb ξ).trans (le_abs_self _))
  refine ⟨hm, ?_⟩
  change lpNorm (fun ξ => initialWeight s ξ • initialFourier n u ξ)
    2 (carrierMeasure n) ≤ _
  calc
    _ ≤ lpNorm (C • g) 2 (carrierMeasure n) := lpNorm_mono_real (hg.const_smul C) hb
    _ = C * lpNorm g 2 (carrierMeasure n) := by
      rw [lpNorm_const_smul]
      simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hC]
    _ ≤ C * (lpNorm p 2 (carrierMeasure n) + lpNorm q 2 (carrierMeasure n)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      have hp : MemLp p 2 (carrierMeasure n) := hz
      have hq : MemLp q 2 (carrierMeasure n) := hη
      simpa only [lpNorm_norm hp.aestronglyMeasurable,
        lpNorm_norm hq.aestronglyMeasurable] using lpNorm_add_le hp.norm (by norm_num :
          (1 : ENNReal) ≤ 2) (g := fun ξ => ‖q ξ‖)

/-- The unweighted carrier jet sum is bounded by the existing triangular
mixed aggregate on compact smooth tests. This is the input comparison for
parameter Plancherel in `app:ch_background:eq:bg-density-adjoint`. -/
theorem sum_unweightedCarrierJet_le_mixedCarrierJetNorm (s : ℕ)
    (f : carrierInitialTestSpace n) :
    (∑ k ∈ Finset.range (s + 1),
      lpNorm (weightedCarrierJet k 0 f.val) 2 (carrierMeasure n)) ≤
      mixedCarrierJetNorm s f.val := by
  apply Finset.sum_le_sum
  intro k _
  exact lpNorm_weightedCarrierJet_mono k (Nat.zero_le _)
    (memLp_weightedCarrierJet_of_compactSupport k (s - k) f.property.1 f.property.2)

end JanetCartan.ContinuumAdjoint.DensityMultiplier
