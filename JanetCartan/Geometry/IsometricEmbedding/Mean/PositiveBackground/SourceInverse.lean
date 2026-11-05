module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.FixedSource
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.DensityRegularity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.InitialLabels
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.Density
public import JanetCartan.Analysis.ContDiff.PositiveSquareRoot

/-!
# Source-to-density bounds for the original inverse

For `app:ch_background:eq:bg-positive-profile`, apply the primitive normal
bootstrap and raw-adjoint estimates to the constructed compact source. The
same inverse supplies every raw order, including the image and exterior slots.
The fixed angular and high-frequency masks give constants independent of the
source contraction even though the geometric row varies.
The `with_exterior` statements keep a supplied fixed exterior cutoff, whose
radius may differ from the source and measurement radius. The original
fixed-radius statements are specializations of those same proofs.

The actual uniform gap, elliptic regularity/estimate and raw-adjoint bounds
remain the obligations of the normalized-background and continuum-inverse
producers for their SAME row. Source bounds are supplied by `CommonSource`
and `NormalizedSourceSobolev`; no inverse regularity, small density or positive
background is assumed here. This deduction does not prove those producer
estimates, detector matching, or the corrected-positive row gap.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.PositiveBackground
open ContinuumRow CarrierSobolev ContinuumInverse

variable {n N : ℕ} {ι : Type*} [Fintype ι]

/-- Uncut synthesis depends on the original two masks, not on the varying
geometric coefficients of the row (`app:ch_background:eq:bg-density-four`).
This permits uniform density constants without identifying different rows. -/
theorem initialDensity_eq_of_masks (d e : CarrierData n N)
    (hangular : d.angularCutoff = e.angularCutoff) (hhigh : d.highCutoff = e.highCutoff)
    (c : ℝ) (u : CarrierVariable n → ℂ) :
    UncutDensity.initialDensity d c u = UncutDensity.initialDensity e c u := by
  funext p
  simp only [UncutDensity.initialDensity, UncutDensity.carrierDensitySymbol,
    hangular, hhigh]

private theorem raw_component_le_gradeNorm {s : ℕ} {u : AugmentedInput n ι}
    (hu : u ∈ augmentedInputLevel n ι s) (i : ι) :
    rawSobolevNorm s (u.fst.snd i) ≤ (augmentedInputSobolevScale n ι).gradeNorm s u := by
  obtain ⟨v, rfl⟩ := hu
  apply le_trans _ (augmentedInputSobolevScale_gradeNorm s v).symm.le
  exact (RawSobolevSpace.norm_eq s (v.fst.snd i)).symm.le.trans
    ((PiLp.norm_apply_le v.fst.snd i).trans
      ((WithLp.norm_snd_le _ v.fst).trans (WithLp.norm_fst_le _ v)))

section UniformSourceExterior

variable {r σ₀ gap : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (hσ₀ : 0 < σ₀) (hgap : 0 < gap)
    (image : ℝ → OutputL2 n →L[ℝ] OutputL2 n)
    (U : ℝ → ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (ψ : C(Torus n, ℝ))
    (Q : ℝ → Euclidean n → Fin n → MetricTensor n) (R : ℝ → MetricField n)
    (hQ : ∀ σ ∈ Ioc (0 : ℝ) σ₀, ContDiffOn ℝ ∞ (Q σ) (Metric.ball 0 (4 * r)))
    (hR : ∀ σ ∈ Ioc (0 : ℝ) σ₀, ContDiffOn ℝ ∞ (R σ) (Metric.ball 0 (4 * r)))
    (C K a B : ℕ → ℝ) (b : ℕ)
    (hC : ∀ s, 0 ≤ C s) (hK : ∀ s, 0 ≤ K s)
    (ha : ∀ s, 0 ≤ a s) (ha_mono : Monotone a) (hB : ∀ s, 0 ≤ B s)
    (hsource : ∀ (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) σ₀) (s : ℕ),
      (periodicSobolevScale n (Euclidean n)).gradeNorm s
        (fixedSourceToL2 hr hcell (Q σ) (R σ) (hQ σ hσ) (hR σ hσ)) ≤ B s * σ)
    (hcoercive : ∀ σ ∈ Ioc (0 : ℝ) σ₀, ∀ w,
      gap * ‖w‖ ^ 2 ≤
        ‖(augmentedRow (image σ) (U σ) ψ).adjoint w‖ ^ 2)
    (hreg : ∀ σ ∈ Ioc (0 : ℝ) σ₀, ∀ s w,
      w ∈ periodicSobolevLevel n (Euclidean n) s →
      CoerciveInverse.normalOperator
          (augmentedRow (image σ) (U σ) ψ) w ∈
        periodicSobolevLevel n (Euclidean n) (s + 1) →
      w ∈ periodicSobolevLevel n (Euclidean n) (s + 1))
    (hstep : ∀ σ ∈ Ioc (0 : ℝ) σ₀, ∀ s w,
      w ∈ periodicSobolevLevel n (Euclidean n) (s + 1) →
      CoerciveInverse.normalOperator
          (augmentedRow (image σ) (U σ) ψ) w ∈
        periodicSobolevLevel n (Euclidean n) (s + 1) →
      (periodicSobolevScale n (Euclidean n)).gradeNorm (s + 1) w ≤ C (s + 1) *
        ((periodicSobolevScale n (Euclidean n)).gradeNorm (s + 1)
          (CoerciveInverse.normalOperator
            (augmentedRow (image σ) (U σ) ψ) w) +
          (periodicSobolevScale n (Euclidean n)).gradeNorm s w +
          (1 + a (s + 1 + b)) * ‖w‖))
    (hrawReg : ∀ σ ∈ Ioc (0 : ℝ) σ₀, ∀ s w,
      w ∈ periodicSobolevLevel n (Euclidean n) s →
      (augmentedRow (image σ) (U σ) ψ).adjoint w ∈
        augmentedInputLevel n ι s)
    (hraw : ∀ σ ∈ Ioc (0 : ℝ) σ₀, ∀ s w,
      w ∈ periodicSobolevLevel n (Euclidean n) s →
      (augmentedInputSobolevScale n ι).gradeNorm s
        ((augmentedRow (image σ) (U σ) ψ).adjoint w) ≤
        K s * ((periodicSobolevScale n (Euclidean n)).gradeNorm s w +
          (1 + a (s + b)) * ‖w‖))

include hgap hC hK ha ha_mono hB hsource hcoercive hreg hstep hrawReg hraw in
/-- The actual compact source produces one all-order raw correction of size
`O_s(σ)`, including its original supplied exterior component. The cutoff
`ψ` is retained independently of the fixed source and measurement radius.
Uniform primitive normal and adjoint estimates precede `σ`; the inverse is
never reselected by order
(`app:ch_background:eq:bg-current-raising`, `bg-positive-profile`). -/
theorem fixedSource_uncorrectedRawCorrection_bounds_with_exterior :
    ∃ L : ℕ → ℝ, (∀ s, 0 ≤ L s) ∧
      ∀ (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) σ₀),
      let raw := uncorrectedRawCorrection (image σ) (U σ)
        ψ (FixedCutoffs.periodic hr hcell 0)
        (fixedResidualToL2 hr hcell (Q σ) (R σ) (hQ σ hσ) (hR σ hσ))
      (∀ s, raw ∈ augmentedInputLevel n ι s) ∧
        (∀ s, (augmentedInputSobolevScale n ι).gradeNorm s raw ≤ L s * σ) ∧
        ∀ i s, rawSobolevNorm s (raw.fst.snd i) ≤ L s * σ := by
  let D := fun s ↦ bootstrapConstant gap C s +
    K s * (bootstrapConstant gap C s + gap⁻¹)
  have hD (s) : 0 ≤ D s := by
    dsimp [D]
    have := bootstrapConstant_nonneg hgap hC s
    have := hK s
    positivity
  refine ⟨fun s ↦ D s * (B s + (1 + a (s + b)) * B 0),
    fun s ↦ mul_nonneg (hD s) (add_nonneg (hB s)
      (mul_nonneg (by linarith [ha (s + b)]) (hB 0))), ?_⟩
  intro σ hσ raw
  let e := fixedSourceToL2 hr hcell (Q σ) (R σ) (hQ σ hσ) (hR σ hσ)
  have he (s) : e ∈ periodicSobolevLevel n (Euclidean n) s :=
    fixedSourceToL2_mem hr hcell _ _ _ _ s
  have hrawEq : raw = CoerciveInverse.rightInverse
      (augmentedRow (image σ) (U σ) ψ) e := by
    dsimp only [raw, uncorrectedRawCorrection]
    rw [inverseSource_fixedResidualToL2]
  have hinverse (s) := canonical_inverse_estimate
    (periodicSobolevScale n (Euclidean n)) (augmentedInputSobolevScale n ι)
    (augmentedRow (image σ) (U σ) ψ)
    hgap (hcoercive σ hσ) hC hK ha ha_mono (hreg σ hσ) (hstep σ hσ)
    (hrawReg σ hσ) (hraw σ hσ) s (he s)
  have hmem (s) : raw ∈ augmentedInputLevel n ι s := by
    rw [hrawEq]
    exact (hinverse s).2.1
  have hnorm : ‖e‖ ≤ B 0 * σ := by
    simpa only [GradedScale.gradeNorm_zero] using hsource σ hσ 0
  have hbnd (s) : (augmentedInputSobolevScale n ι).gradeNorm s raw ≤
      D s * (B s + (1 + a (s + b)) * B 0) * σ := by
    have ht := (hinverse s).2.2.2
    rw [← hrawEq] at ht
    have hpos := (periodicSobolevScale n (Euclidean n)).gradeNorm_nonneg s
      ((CoerciveInverse.normalOperator
        (augmentedRow (image σ) (U σ) ψ)).inverse e)
    calc
      _ ≤ D s * ((periodicSobolevScale n (Euclidean n)).gradeNorm s e +
          (1 + a (s + b)) * ‖e‖) := (le_add_of_nonneg_left hpos).trans ht
      _ ≤ D s * (B s * σ + (1 + a (s + b)) * (B 0 * σ)) := by
        apply mul_le_mul_of_nonneg_left _ (hD s)
        exact add_le_add (hsource σ hσ s)
          (mul_le_mul_of_nonneg_left hnorm (by linarith [ha (s + b)]))
      _ = _ := by ring
  exact ⟨hmem, hbnd, fun i s ↦ (raw_component_le_gradeNorm (hmem s) i).trans (hbnd s)⟩

include hσ₀ hgap hC hK ha ha_mono hB hsource hcoercive hreg hstep hrawReg hraw in
/-- Apply the primitive estimates to the actual compact source and construct
the literal smooth factor-four density. One family of representatives works
at every order; one source contraction makes its prescribed finite low norm
small and its positive amplitude smooth on ALL initial variables. The masks
are fixed, while the geometry and the original uncorrected inverse may vary
with `σ`. The supplied exterior cutoff is kept unchanged throughout; it
need not equal the source cutoff (`app:ch_background:prop:bg-positive`,
`bg-positive-profile`).

This discharges density regularity and smallness from the displayed primitive
normal/adjoint estimates, not those estimates themselves. The finite low norm
is also controlled on the actual ODE-label domain. Applying the original wider
density-class normal theorem to this same family remains necessary for the
corrected gap; positivity alone is not a coercivity proof. -/
theorem exists_small_uncorrectedDensity_of_normal_estimates_with_exterior
    (d : ℝ → ι → CarrierData n N)
    (z₀ : ι → Euclidean 3) (η₀ : ι → Euclidean (n - 1))
    (rMask angleWidth : ι → ℝ) (hrMask : ∀ i, 0 < rMask i)
    (hangleWidth : ∀ i, 0 < angleWidth i)
    (hangular : ∀ σ ∈ Ioc (0 : ℝ) σ₀, ∀ i, (d σ i).angularCutoff =
      CanonicalConic.angularMask (z₀ i) (η₀ i) (hrMask i) (hangleWidth i))
    (hhigh : ∀ σ ∈ Ioc (0 : ℝ) σ₀, ∀ i, (d σ i).highCutoff = FixedCutoffs.highFrequency) :
    ∃ D : ℕ → ℝ, (∀ s, 0 < D s) ∧
      ∃ v : Ioc (0 : ℝ) σ₀ → ι → CarrierVariable n → ℝ,
        (∀ σ i, ContDiff ℝ ∞ (v σ i)) ∧
        (∀ σ i, v σ i =ᵐ[carrierMeasure n]
          uncorrectedDensity (d σ) (image σ) (U σ)
            ψ (FixedCutoffs.periodic hr hcell 0)
            (fixedResidualToL2 hr hcell (Q σ) (R σ) (hQ σ σ.property) (hR σ σ.property)) i) ∧
        (∀ σ s, ∑ i, cNorm univ s (v σ i) ≤ D s * σ.val) ∧
        (∀ σ i s j, j ≤ s → ∀ p, ‖iteratedFDeriv ℝ j (v σ i) p‖ ≤ D s * σ.val) ∧
        ∀ (Klabel : Set (Euclidean (n - 1) × Euclidean 3)), IsCompact Klabel →
          ∀ (k : ℕ) (ε : ℝ), 0 < ε → ∃ σ₁ > (0 : ℝ), σ₁ ≤ σ₀ ∧
          ∀ σ : Ioc (0 : ℝ) σ₀, σ.val ≤ σ₁ →
            (∑ i, cNorm univ k (v σ i) ≤ ε) ∧
            (∀ i, cNorm Klabel k (densityOnInitialLabels (v σ i)) ≤ ε) ∧
            (∀ i p, 1 + v σ i p ∈ Icc (1 / 2 : ℝ) (3 / 2)) ∧
            (∀ i, ContDiff ℝ ∞ (fun p ↦ positiveDensityAmplitude σ.val (v σ i p))) ∧
            (∀ i p, 0 < positiveDensityAmplitude σ.val (v σ i p)) ∧
            ∀ i p, positiveDensityAmplitude σ.val (v σ i p) ^ 2 =
              σ.val ^ 2 * (1 + v σ i p) := by
  classical
  let d₀ := d σ₀
  have htop : σ₀ ∈ Ioc (0 : ℝ) σ₀ := ⟨hσ₀, le_rfl⟩
  have hρsmooth (i) : ContDiff ℝ ∞
      (fun p : CarrierVariable n ↦ ((d₀ i).angularCutoff p.1 p.2 : ℂ)) := by
    dsimp only [d₀]
    rw [hangular σ₀ htop i]
    exact ContinuumAdjoint.Canonical.densityAngular_smooth _ _ _ _
  have hcρ (i) : HasCompactSupport
      (fun p : CarrierVariable n ↦ ((d₀ i).angularCutoff p.1 p.2 : ℂ)) := by
    dsimp only [d₀]
    rw [hangular σ₀ htop i]
    exact ContinuumAdjoint.Canonical.densityAngular_compact _ _ _ _
  have hχsmooth (i) : ContDiff ℝ ∞ (d₀ i).highCutoff := by
    dsimp only [d₀]
    rw [hhigh σ₀ htop i]
    exact FixedCutoffs.highFrequency_smooth
  have hlow (i) (t : ℝ) (ht : t ≤ 1) : (d₀ i).highCutoff t = 0 := by
    dsimp only [d₀]
    rw [hhigh σ₀ htop i]
    exact FixedCutoffs.highFrequency_zero ht
  have hhi (i) (t : ℝ) : |(d₀ i).highCutoff t| ≤ 1 := by
    dsimp only [d₀]
    rw [hhigh σ₀ htop i]
    exact ContinuumAdjoint.Canonical.densityHigh_abs_le t
  have hρ (i) (z : CarrierParameter) (η : Euclidean (n - 1)) :
      |(d₀ i).angularCutoff z η| ≤ 1 := by
    dsimp only [d₀]
    rw [hangular σ₀ htop i]
    have h := CanonicalConic.angularMask_mem_Icc (z₀ i) (η₀ i) (hrMask i) (hangleWidth i) z η
    rw [abs_of_nonneg h.1]
    exact h.2
  obtain ⟨L, hL, hcorrection⟩ := fixedSource_uncorrectedRawCorrection_bounds_with_exterior
    hr hcell hgap image U ψ Q R hQ hR C K a B b hC hK ha ha_mono hB
    hsource hcoercive hreg hstep hrawReg hraw
  let raw (σ : Ioc (0 : ℝ) σ₀) := uncorrectedRawCorrection (image σ) (U σ)
    ψ (FixedCutoffs.periodic hr hcell 0)
    (fixedResidualToL2 hr hcell (Q σ) (R σ) (hQ σ σ.property) (hR σ σ.property))
  have hrawMem (σ : Ioc (0 : ℝ) σ₀) (i : ι) (s : ℕ) :
      MemRawSobolev s ((raw σ).fst.snd i) :=
    ((mem_augmentedInputLevel_iff s (raw σ)).mp
      ((hcorrection σ σ.property).1 s)).2.1 i
  choose Cden hCden hconstruct using fun i ↦ exists_smooth_initialDensity_four_cNorm
    (d₀ i) (hρsmooth i) (hcρ i) (hχsmooth i) (hlow i) (hhi i) zero_le_one (hρ i)
  choose Cp hCp hp using fun i s ↦ CurrentMean.exists_initialDensityRepresentative_derivative_bound
    (d₀ i) (hρsmooth i) (hcρ i) (hχsmooth i) (hlow i) (hhi i) zero_le_one (hρ i) 4 s
  choose v hv he hb using fun (σ : Ioc (0 : ℝ) σ₀) i ↦
    hconstruct i ((raw σ).fst.snd i) (hrawMem σ i)
  let q := 3 + (n - 1) + 1
  let D := fun s ↦ 1 + ∑ i, (Cden i s + Cp i s) * L (s + q + 1)
  have hterm (i : ι) (s : ℕ) : 0 ≤ (Cden i s + Cp i s) * L (s + q + 1) :=
    mul_nonneg (add_nonneg (hCden i s) (hCp i s)) (hL _)
  have hD (s) : 0 < D s := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) ↦ hterm i s)
    dsimp only [D]
    linarith
  have hcBound (σ : Ioc (0 : ℝ) σ₀) (i : ι) (s : ℕ) :
      cNorm univ s (v σ i) ≤ (Cden i s + Cp i s) * L (s + q + 1) * σ.val := by
    calc
      _ ≤ Cden i s * rawSobolevNorm (s + q + 1) ((raw σ).fst.snd i) := hb σ i s
      _ ≤ Cden i s * (L (s + q + 1) * σ.val) :=
        mul_le_mul_of_nonneg_left ((hcorrection σ σ.property).2.2 i _) (hCden i s)
      _ ≤ (Cden i s + Cp i s) * L (s + q + 1) * σ.val := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hCp i s))
          (mul_nonneg (hL _) σ.property.1.le)
  have hsum (σ : Ioc (0 : ℝ) σ₀) (s : ℕ) :
      ∑ i, cNorm univ s (v σ i) ≤ D s * σ.val := by
    calc
      _ ≤ ∑ i, (Cden i s + Cp i s) * L (s + q + 1) * σ.val :=
        Finset.sum_le_sum (fun i _ ↦ hcBound σ i s)
      _ = (∑ i, (Cden i s + Cp i s) * L (s + q + 1)) * σ.val :=
        (Finset.sum_mul ..).symm
      _ ≤ D s * σ.val :=
        mul_le_mul_of_nonneg_right (by dsimp [D]; linarith) σ.property.1.le
  have hpoint (σ : Ioc (0 : ℝ) σ₀) (i : ι) (s j : ℕ) (hj : j ≤ s) (p) :
      ‖iteratedFDeriv ℝ j (v σ i) p‖ ≤ D s * σ.val := by
    have hp' : ‖iteratedFDeriv ℝ j (v σ i) p‖ ≤
        Cp i s * rawSobolevNorm (s + q + 1) ((raw σ).fst.snd i) := by
      simpa only [q, Nat.add_assoc] using
        hp i s _ (hrawMem σ i) _ (hv σ i) (he σ i) j hj p
    calc
      _ ≤ Cp i s * rawSobolevNorm (s + q + 1) ((raw σ).fst.snd i) := hp'
      _ ≤ Cp i s * (L (s + q + 1) * σ.val) :=
        mul_le_mul_of_nonneg_left ((hcorrection σ σ.property).2.2 i _) (hCp i s)
      _ ≤ ((Cden i s + Cp i s) * L (s + q + 1)) * σ.val := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hCden i s))
          (mul_nonneg (hL _) σ.property.1.le)
      _ ≤ D s * σ.val := by
        apply mul_le_mul_of_nonneg_right _ σ.property.1.le
        exact (Finset.single_le_sum (fun i _ ↦ hterm i s) (Finset.mem_univ i)).trans
          (by dsimp [D]; linarith)
  refine ⟨D, hD, v, hv, ?_, hsum, hpoint, ?_⟩
  · intro σ i
    have hmask := initialDensity_eq_of_masks (d σ i) (d₀ i)
      ((hangular σ σ.property i).trans (hangular σ₀ htop i).symm)
      ((hhigh σ σ.property i).trans (hhigh σ₀ htop i).symm) 4 ((raw σ).fst.snd i)
    exact (he σ i).trans (Filter.Eventually.of_forall (congrFun hmask.symm))
  intro Klabel hKlabel k ε hε
  obtain ⟨E, hE, hlabel⟩ := exists_cNorm_densityOnInitialLabels_le hKlabel k
  have hE1 : 0 < E + 1 := by linarith
  let σ₁ := min σ₀ (min (ε / (E + 1)) (1 / 2) / D k)
  have hσ₁ : 0 < σ₁ :=
    lt_min hσ₀ (div_pos (lt_min (div_pos hε hE1) (by norm_num)) (hD k))
  refine ⟨σ₁, hσ₁, min_le_left _ _, ?_⟩
  intro σ hσ
  have hsmall : D k * σ.val ≤ min (ε / (E + 1)) (1 / 2) := by
    have hle := hσ.trans (min_le_right σ₀ (min (ε / (E + 1)) (1 / 2) / D k))
    exact (mul_comm _ _).trans_le ((le_div_iff₀ (hD k)).mp hle)
  have hscaled : (E + 1) * (D k * σ.val) ≤ ε := by
    rw [mul_comm]
    exact (le_div_iff₀ hE1).mp (hsmall.trans (min_le_left _ _))
  have hsize : 0 ≤ D k * σ.val := mul_nonneg (hD k).le σ.property.1.le
  have hlabelSmall (i : ι) : cNorm Klabel k (densityOnInitialLabels (v σ i)) ≤ ε :=
    (hlabel _ _ hsize (hv σ i) (hpoint σ i k)).trans
      ((mul_le_mul_of_nonneg_right (by linarith : E ≤ E + 1) hsize).trans hscaled)
  have hrawSmall : D k * σ.val ≤ ε :=
    (le_mul_of_one_le_left hsize (by linarith : 1 ≤ E + 1)).trans hscaled
  have hinterval (i : ι) (p : CarrierVariable n) :
      1 + v σ i p ∈ Icc (1 / 2 : ℝ) (3 / 2) := by
    have hn : |v σ i p| ≤ (1 / 2 : ℝ) := by
      have ht := (hpoint σ i k 0 (Nat.zero_le k) p).trans
        (hsmall.trans (min_le_right _ _))
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using ht
    have hh := abs_le.mp hn
    constructor <;> linarith [hh.1, hh.2]
  have hamp (i : ι) := positiveDensityAmplitude_properties σ.property.1 (hv σ i) (hinterval i)
  exact ⟨(hsum σ k).trans hrawSmall, hlabelSmall, hinterval,
    fun i ↦ (hamp i).1, fun i ↦ (hamp i).2.1, fun i ↦ (hamp i).2.2⟩

end UniformSourceExterior

section UniformSource

variable {r σ₀ gap : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (hσ₀ : 0 < σ₀) (hgap : 0 < gap)
    (image : ℝ → OutputL2 n →L[ℝ] OutputL2 n)
    (U : ℝ → ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (Q : ℝ → Euclidean n → Fin n → MetricTensor n) (R : ℝ → MetricField n)
    (hQ : ∀ σ ∈ Ioc (0 : ℝ) σ₀, ContDiffOn ℝ ∞ (Q σ) (Metric.ball 0 (4 * r)))
    (hR : ∀ σ ∈ Ioc (0 : ℝ) σ₀, ContDiffOn ℝ ∞ (R σ) (Metric.ball 0 (4 * r)))
    (C K a B : ℕ → ℝ) (b : ℕ)
    (hC : ∀ s, 0 ≤ C s) (hK : ∀ s, 0 ≤ K s)
    (ha : ∀ s, 0 ≤ a s) (ha_mono : Monotone a) (hB : ∀ s, 0 ≤ B s)
    (hsource : ∀ (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) σ₀) (s : ℕ),
      (periodicSobolevScale n (Euclidean n)).gradeNorm s
        (fixedSourceToL2 hr hcell (Q σ) (R σ) (hQ σ hσ) (hR σ hσ)) ≤ B s * σ)
    (hcoercive : ∀ σ ∈ Ioc (0 : ℝ) σ₀, ∀ w,
      gap * ‖w‖ ^ 2 ≤
        ‖(augmentedRow (image σ) (U σ) (FixedCutoffs.periodic hr hcell 0)).adjoint w‖ ^ 2)
    (hreg : ∀ σ ∈ Ioc (0 : ℝ) σ₀, ∀ s w,
      w ∈ periodicSobolevLevel n (Euclidean n) s →
      CoerciveInverse.normalOperator
          (augmentedRow (image σ) (U σ) (FixedCutoffs.periodic hr hcell 0)) w ∈
        periodicSobolevLevel n (Euclidean n) (s + 1) →
      w ∈ periodicSobolevLevel n (Euclidean n) (s + 1))
    (hstep : ∀ σ ∈ Ioc (0 : ℝ) σ₀, ∀ s w,
      w ∈ periodicSobolevLevel n (Euclidean n) (s + 1) →
      CoerciveInverse.normalOperator
          (augmentedRow (image σ) (U σ) (FixedCutoffs.periodic hr hcell 0)) w ∈
        periodicSobolevLevel n (Euclidean n) (s + 1) →
      (periodicSobolevScale n (Euclidean n)).gradeNorm (s + 1) w ≤ C (s + 1) *
        ((periodicSobolevScale n (Euclidean n)).gradeNorm (s + 1)
          (CoerciveInverse.normalOperator
            (augmentedRow (image σ) (U σ) (FixedCutoffs.periodic hr hcell 0)) w) +
          (periodicSobolevScale n (Euclidean n)).gradeNorm s w +
          (1 + a (s + 1 + b)) * ‖w‖))
    (hrawReg : ∀ σ ∈ Ioc (0 : ℝ) σ₀, ∀ s w,
      w ∈ periodicSobolevLevel n (Euclidean n) s →
      (augmentedRow (image σ) (U σ) (FixedCutoffs.periodic hr hcell 0)).adjoint w ∈
        augmentedInputLevel n ι s)
    (hraw : ∀ σ ∈ Ioc (0 : ℝ) σ₀, ∀ s w,
      w ∈ periodicSobolevLevel n (Euclidean n) s →
      (augmentedInputSobolevScale n ι).gradeNorm s
        ((augmentedRow (image σ) (U σ) (FixedCutoffs.periodic hr hcell 0)).adjoint w) ≤
        K s * ((periodicSobolevScale n (Euclidean n)).gradeNorm s w +
          (1 + a (s + b)) * ‖w‖))
include hgap hC hK ha ha_mono hB hsource hcoercive hreg hstep hrawReg hraw in
/-- The original fixed-radius source-to-raw API is the specialization of the
same-row exterior-preserving estimate (`app:ch_background:eq:bg-current-raising`,
`app:ch_background:eq:bg-positive-profile`). -/
theorem fixedSource_uncorrectedRawCorrection_bounds :
    ∃ L : ℕ → ℝ, (∀ s, 0 ≤ L s) ∧
      ∀ (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) σ₀),
      let raw := uncorrectedRawCorrection (image σ) (U σ)
        (FixedCutoffs.periodic hr hcell 0) (FixedCutoffs.periodic hr hcell 0)
        (fixedResidualToL2 hr hcell (Q σ) (R σ) (hQ σ hσ) (hR σ hσ))
      (∀ s, raw ∈ augmentedInputLevel n ι s) ∧
        (∀ s, (augmentedInputSobolevScale n ι).gradeNorm s raw ≤ L s * σ) ∧
        ∀ i s, rawSobolevNorm s (raw.fst.snd i) ≤ L s * σ := by
  exact fixedSource_uncorrectedRawCorrection_bounds_with_exterior hr hcell hgap
    image U (FixedCutoffs.periodic hr hcell 0) Q R hQ hR C K a B b
    hC hK ha ha_mono hB hsource hcoercive hreg hstep hrawReg hraw

include hσ₀ hgap hC hK ha ha_mono hB hsource hcoercive hreg hstep hrawReg hraw in
/-- The original fixed-radius factor-four density constructor retains its
statement, as a specialization with the original exterior cutoff
(`app:ch_background:prop:bg-positive`, `app:ch_background:eq:bg-positive-profile`). -/
theorem exists_small_uncorrectedDensity_of_normal_estimates
    (d : ℝ → ι → CarrierData n N)
    (z₀ : ι → Euclidean 3) (η₀ : ι → Euclidean (n - 1))
    (rMask angleWidth : ι → ℝ) (hrMask : ∀ i, 0 < rMask i)
    (hangleWidth : ∀ i, 0 < angleWidth i)
    (hangular : ∀ σ ∈ Ioc (0 : ℝ) σ₀, ∀ i, (d σ i).angularCutoff =
      CanonicalConic.angularMask (z₀ i) (η₀ i) (hrMask i) (hangleWidth i))
    (hhigh : ∀ σ ∈ Ioc (0 : ℝ) σ₀, ∀ i, (d σ i).highCutoff = FixedCutoffs.highFrequency) :
    ∃ D : ℕ → ℝ, (∀ s, 0 < D s) ∧
      ∃ v : Ioc (0 : ℝ) σ₀ → ι → CarrierVariable n → ℝ,
        (∀ σ i, ContDiff ℝ ∞ (v σ i)) ∧
        (∀ σ i, v σ i =ᵐ[carrierMeasure n]
          uncorrectedDensity (d σ) (image σ) (U σ)
            (FixedCutoffs.periodic hr hcell 0) (FixedCutoffs.periodic hr hcell 0)
            (fixedResidualToL2 hr hcell (Q σ) (R σ) (hQ σ σ.property) (hR σ σ.property)) i) ∧
        (∀ σ s, ∑ i, cNorm univ s (v σ i) ≤ D s * σ.val) ∧
        (∀ σ i s j, j ≤ s → ∀ p, ‖iteratedFDeriv ℝ j (v σ i) p‖ ≤ D s * σ.val) ∧
        ∀ (Klabel : Set (Euclidean (n - 1) × Euclidean 3)), IsCompact Klabel →
          ∀ (k : ℕ) (ε : ℝ), 0 < ε → ∃ σ₁ > (0 : ℝ), σ₁ ≤ σ₀ ∧
          ∀ σ : Ioc (0 : ℝ) σ₀, σ.val ≤ σ₁ →
            (∑ i, cNorm univ k (v σ i) ≤ ε) ∧
            (∀ i, cNorm Klabel k (densityOnInitialLabels (v σ i)) ≤ ε) ∧
            (∀ i p, 1 + v σ i p ∈ Icc (1 / 2 : ℝ) (3 / 2)) ∧
            (∀ i, ContDiff ℝ ∞ (fun p ↦ positiveDensityAmplitude σ.val (v σ i p))) ∧
            (∀ i p, 0 < positiveDensityAmplitude σ.val (v σ i p)) ∧
            ∀ i p, positiveDensityAmplitude σ.val (v σ i p) ^ 2 =
              σ.val ^ 2 * (1 + v σ i p) := by
  exact exists_small_uncorrectedDensity_of_normal_estimates_with_exterior hr hcell hσ₀ hgap
    image U (FixedCutoffs.periodic hr hcell 0) Q R hQ hR C K a B b
    hC hK ha ha_mono hB hsource hcoercive hreg hstep hrawReg hraw
    d z₀ η₀ rMask angleWidth hrMask hangleWidth hangular hhigh

end UniformSource
end JanetCartan.PositiveBackground
