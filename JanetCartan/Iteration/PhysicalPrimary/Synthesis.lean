module

public import JanetCartan.Iteration.PhysicalPrimary.Norms
public import JanetCartan.Iteration.PhysicalPrimary.Envelope
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.SampleBudgets

/-!
# Sharp physical synthesis on the unchanged finite sample

Paper-v2 `main:eq:primary-fixed-scales`: the exact real quadrature sum costs
only the square root of the original sample count.  The inverse-carrier
factor of the actual displacement envelope is retained in every physical
Sobolev order.  The amplitude uses the literal revised forcing exponent.

These are deductions from the same atoms' physical envelope estimates, not
an original-data existence assertion.  The fixed-K source producer must
instantiate those envelopes for `Z₀ + W(v)` with its prescribed inverse;
the old adaptive canonical run is not used.  No final primary estimate is
assumed. Consumer: `RevisedStage.increment_estimates_of_physicalSobolev_profiles`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric MeasureTheory FourierTransform
open scoped ContDiff

namespace JanetCartan.PhysicalPrimary

open UniformStep Pseudodifferential

variable {n N : ℕ} {ι : Type*} [Fintype ι]

/-- Finite real-quadrature synthesis bounds the actual physical jet by
its original complex jets. Zero weights and empty samples require no change
of family (`main:eq:primary`). -/
theorem norm_iteratedFDeriv_sampledPrimary_le {b : ℝ} (hb : 0 ≤ b) (μ : ι → ℝ)
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)) (q : ℕ) (x : Euclidean n)
    (hZ : ∀ i, ContDiffAt ℝ q (Z i) x) {M : ℝ}
    (hjet : ∀ i, ‖iteratedFDeriv ℝ q (Z i) x‖ ≤ M) :
    ‖iteratedFDeriv ℝ q (sampledPrimary b μ Z) x‖ ≤
      (b * Real.sqrt 2) * ((∑ i, Real.sqrt (μ i)) * M) := by
  have hr (i : ι) : ContDiffAt ℝ q (euclideanRealPart ∘ Z i) x :=
    euclideanRealPart.contDiff.contDiffAt.comp x (hZ i)
  have hreal (i : ι) : ‖iteratedFDeriv ℝ q (euclideanRealPart ∘ Z i) x‖ ≤ M := by
    apply (euclideanRealPart.norm_iteratedFDeriv_comp_left (hZ i) le_rfl).trans
    exact ((mul_le_mul_of_nonneg_right euclideanRealPart_norm_le (norm_nonneg _)).trans_eq
      (one_mul _)).trans (hjet i)
  have hsum : ContDiffAt ℝ q (∑ i, Real.sqrt (μ i) • (euclideanRealPart ∘ Z i)) x := by
    convert ContDiffAt.sum (s := Finset.univ)
      (fun i _ ↦ (hr i).const_smul (Real.sqrt (μ i))) using 1
    ext y a
    simp only [Pi.smul_apply, Finset.sum_apply]
  rw [sampledPrimary, iteratedFDeriv_const_smul_apply hsum,
    iteratedFDeriv_sum_apply (f := fun i ↦ Real.sqrt (μ i) • (euclideanRealPart ∘ Z i))
      (u := Finset.univ) (fun i _ ↦ (hr i).const_smul (Real.sqrt (μ i)))]
  simp_rw [iteratedFDeriv_const_smul_apply (hr _)]
  rw [norm_smul, Real.norm_of_nonneg (mul_nonneg hb (Real.sqrt_nonneg _))]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hb (Real.sqrt_nonneg _))
  exact WeightedFamily.norm_sum_weight_smul_le_of_norm_le Finset.univ
    (fun i ↦ Real.sqrt (μ i)) (fun _ _ ↦ Real.sqrt_nonneg _)
    (fun i ↦ iteratedFDeriv ℝ q (euclideanRealPart ∘ Z i) x) (fun i _ ↦ hreal i)

/-- The local norm needed by the actual compact primary follows from the
same atoms' sharp physical jets. The `λ⁻¹` is retained also at order zero
(`main:eq:primary-fixed-scales`). -/
theorem cNorm_sampledPrimary_le_of_sharp_jets (D : LocalDomain) {b : ℝ} (hb : 0 ≤ b)
    (μ : ι → ℝ) (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) (D.chart n))
    (Cphys : ℕ → ℝ) (hCphys : ∀ q, 0 ≤ Cphys q) {lam : ℝ} (hlam : 1 ≤ lam)
    (hjet : ∀ i q, ∀ x ∈ closedBall (0 : Euclidean n) (physicalCutoff (n := n) D).rOut,
      ‖iteratedFDeriv ℝ q (Z i) x‖ ≤ Cphys q * lam ^ ((q : ℝ) - 1)) (r : ℕ) :
    cNorm (closedBall (0 : Euclidean n) (physicalCutoff (n := n) D).rOut)
        r (sampledPrimary b μ Z) ≤
      (b * Real.sqrt 2) * (∑ i, Real.sqrt (μ i)) *
        (∑ j ∈ Finset.range (r + 1), Cphys j) * lam ^ ((r : ℝ) - 1) := by
  have hcut : (physicalCutoff (n := n) D).rOut < D.chartRadius := by
    dsimp only [physicalCutoff]
    linarith [D.coreRadius_lt_chartRadius]
  have hjets (q : ℕ) (hq : q ≤ r) (x : Euclidean n)
      (hx : x ∈ closedBall (0 : Euclidean n) (physicalCutoff (n := n) D).rOut) :
      ‖iteratedFDeriv ℝ q (sampledPrimary b μ Z) x‖ ≤
        (b * Real.sqrt 2) * ((∑ i, Real.sqrt (μ i)) * (Cphys q * lam ^ ((r : ℝ) - 1))) := by
    apply norm_iteratedFDeriv_sampledPrimary_le hb μ Z q x
      (fun i ↦ ((hZ i).contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hcut hx))).of_le (by simp))
    intro i
    exact (hjet i q x hx).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hlam (sub_le_sub_right (by exact_mod_cast hq) 1)) (hCphys q))
  have hc := cNorm_le_sum_of_bounds
    (C := fun q ↦ (b * Real.sqrt 2) * ((∑ i, Real.sqrt (μ i)) * (Cphys q * lam ^ ((r : ℝ) - 1))))
    (fun q _ ↦ mul_nonneg (mul_nonneg hb (Real.sqrt_nonneg _))
      (mul_nonneg (Finset.sum_nonneg fun i _ ↦ Real.sqrt_nonneg (μ i))
        (mul_nonneg (hCphys q) (Real.rpow_nonneg (zero_le_one.trans hlam) _)))) hjets
  apply hc.trans_eq
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The physical radian Sobolev profiles of the SAME compact primary, with
constants before scale, amplitude and wave selection. The original sample
count and mass give exactly the square-root count loss, and the amplitude
is `δ R^RevisedScales.forcingExponent`, never the incompatible old exponent.
The actual fixed-K wave producer still supplies its own sharp atom jets. -/
theorem exists_cutSampledPrimary_physical_profiles (D : LocalDomain)
    (Cphys : ℕ → ℝ) (hCphys : ∀ q, 0 ≤ Cphys q)
    {Ccount Cmass : ℝ} (hCcount : 0 ≤ Ccount) (hCmass : 0 ≤ Cmass) :
    ∃ C : ℕ → ℝ, (∀ r, 0 ≤ C r) ∧
      ∀ (R δ : ℝ), 1 ≤ R → 0 ≤ δ →
      ∀ (μ : ι → ℝ), (∀ i, 0 ≤ μ i) →
      (Fintype.card ι : ℝ) ≤ Ccount * R ^ (1 + samplingSlack) →
      (∑ i, μ i) ≤ Cmass →
      ∀ (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
        (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) (D.chart n)),
      (∀ i q, ∀ x ∈ closedBall (0 : Euclidean n) (physicalCutoff (n := n) D).rOut,
        ‖iteratedFDeriv ℝ q (Z i) x‖ ≤ Cphys q * (R ^ carrierExponent) ^ ((q : ℝ) - 1)) →
      ∀ r : ℕ, (eLpNorm (fun ξ ↦ euclideanSobolevWeight (r : ℝ) ((2 * Real.pi) • ξ) •
          𝓕 (PhysicalCutoff.complexify
            (cutSampledPrimary D (δ * R ^ RevisedScales.forcingExponent n) μ Z hZ)) ξ) 2 volume).toReal ≤
        C r * δ * R ^ (RevisedScales.forcingExponent n + (1 + samplingSlack) / 2) *
          (R ^ carrierExponent) ^ ((r : ℝ) - 1) := by
  choose Ccut hCcut hcut using fun r ↦ exists_cutSchwartz_physicalWeightedNorm_bound (n := n) (N := N) D r
  let C (r : ℕ) := Ccut r * Real.sqrt 2 * Real.sqrt (Ccount * Cmass) *
    (∑ j ∈ Finset.range (r + 1), Cphys j)
  have hCtotal (r : ℕ) : 0 ≤ ∑ j ∈ Finset.range (r + 1), Cphys j :=
    Finset.sum_nonneg fun j _ ↦ hCphys j
  refine ⟨C, fun r ↦ mul_nonneg
    (mul_nonneg (mul_nonneg (hCcut r) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    (hCtotal r), ?_⟩
  intro R δ hR hδ μ hμ hcount hmass Z hZ hjet r
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hweights := sampled_weight_sum_le μ hμ hRp hCcount hCmass hcount hmass
  have hlam : 1 ≤ R ^ carrierExponent := Real.one_le_rpow hR (by norm_num [carrierExponent])
  have hc := cNorm_sampledPrimary_le_of_sharp_jets D
    (b := δ * R ^ RevisedScales.forcingExponent n) (by positivity) μ Z hZ Cphys hCphys hlam hjet r
  have hCcutr := hCcut r
  have hCtotalr := hCtotal r
  calc
    _ ≤ Ccut r * cNorm (closedBall (0 : Euclidean n) (physicalCutoff (n := n) D).rOut)
        r (sampledPrimary (δ * R ^ RevisedScales.forcingExponent n) μ Z) :=
      hcut r _ (contDiffOn_sampledPrimary _ μ hZ)
    _ ≤ Ccut r * ((δ * R ^ RevisedScales.forcingExponent n * Real.sqrt 2) *
        (∑ i, Real.sqrt (μ i)) * (∑ j ∈ Finset.range (r + 1), Cphys j) *
          (R ^ carrierExponent) ^ ((r : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hc (hCcut r)
    _ ≤ Ccut r * ((δ * R ^ RevisedScales.forcingExponent n * Real.sqrt 2) *
        (Real.sqrt (Ccount * Cmass) * R ^ ((1 + samplingSlack) / 2)) *
          (∑ j ∈ Finset.range (r + 1), Cphys j) *
          (R ^ carrierExponent) ^ ((r : ℝ) - 1)) := by gcongr
    _ = _ := by rw [Real.rpow_add hRp]; dsimp only [C]; ring

end JanetCartan.PhysicalPrimary
