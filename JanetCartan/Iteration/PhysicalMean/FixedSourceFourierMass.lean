module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.MaskedEstimates
public import JanetCartan.Iteration.PhysicalSamplingShells.Space
public import JanetCartan.Iteration.PhysicalMean.CurrentIndividual
public import Mathlib.Topology.Metrizable.Uniformity

/-!
# Fixed-source Fourier mass on the original wide input

The sharp displacement estimate in `main:eq:primary-fixed-scales` integrates
atomwise bounds against the SAME fixed-cutoff Fourier density. A finite radial
moment, not the cutoff-dependent bare L² norm, controls this mass. No old
forcing exponent, adaptive cutoff, sample cardinality or new raw input is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

open MeasureTheory
open scoped BigOperators

namespace JanetCartan.PhysicalMean.FixedSourceFourierMass
open RawInputRealization RawInputPartition PhysicalSamplingShells

/-- The weighted norm of the original two-shell input. The weight is a
finite radial moment, not a replacement input or a frequency-count factor. -/
def refinedMomentNorm {n J : ℕ} (v : RefinedInput n J) : ℝ :=
  Real.sqrt (∑ i : RefinedIndex J, (refinedRadius i ^ n * ‖v i‖) ^ 2)

private theorem inverse_radius_sum_le {n : ℕ} (hn : 1 ≤ n) (J : ℕ) :
    (∑ i : RefinedIndex J, 1 / refinedRadius i ^ n) ≤ 4 := by
  have hterm (i : RefinedIndex J) :
      1 / refinedRadius i ^ n ≤ (1 / (2 : ℝ)) ^ i.1.val := by
    have hr : (2 : ℝ) ^ i.1.val ≤ refinedRadius i := by
      exact pow_le_pow_right₀ (by norm_num) (Nat.le_add_right _ _)
    have h1 : 1 ≤ refinedRadius i := one_le_pow₀ (by norm_num)
    have hp : refinedRadius i ≤ refinedRadius i ^ n := by
      simpa only [pow_one] using pow_le_pow_right₀ h1 hn
    simpa only [one_div, inv_pow] using
      one_div_le_one_div_of_le (pow_pos (by norm_num) _) (hr.trans hp)
  have hg : (∑ j : Fin J, (1 / (2 : ℝ)) ^ j.val) ≤ 2 := by
    simpa only [Fin.sum_univ_eq_sum_range] using sum_geometric_two_le J
  calc
    _ ≤ ∑ i : RefinedIndex J, (1 / (2 : ℝ)) ^ i.1.val :=
      Finset.sum_le_sum (fun i _ ↦ hterm i)
    _ = 2 * ∑ j : Fin J, (1 / (2 : ℝ)) ^ j.val := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Finset.mul_sum]
      norm_num
    _ ≤ 4 := by linarith

/-- Fourier L¹ of the SAME refined density, with one finite radial moment
and a dimension-only constant. In particular there is no `J` or cutoff loss
in the sharp physical-jet consumer (`main:eq:primary-fixed-scales`). -/
theorem integral_norm_density_le_moment {n J : ℕ} (hn : 1 ≤ n)
    {β : RefinedIndex J → Euclidean (n - 1) → ℂ}
    (hβ : ∀ i, Measurable (β i)) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i η, ‖β i η‖ ≤ M) (v : RefinedInput n J) :
    (∫ η, ‖density β v η‖) ≤
      (2 * M * Real.sqrt (unitBallVolume n)) * refinedMomentNorm v := by
  classical
  let c : RefinedIndex J → ℝ := fun i ↦ Real.sqrt (refinedRadius i) * M *
    Real.sqrt ((annularMeasure n (refinedRadius i) Set.univ).toReal)
  let a : RefinedIndex J → ℝ := fun i ↦ c i / refinedRadius i ^ n
  let b : RefinedIndex J → ℝ := fun i ↦ refinedRadius i ^ n * ‖v i‖
  have hc (i : RefinedIndex J) :
      a i ^ 2 ≤ (M ^ 2 * unitBallVolume n) / refinedRadius i ^ n := by
    have hp : 0 < refinedRadius i ^ n := pow_pos (refinedRadius_pos i) _
    calc
      _ = c i ^ 2 / (refinedRadius i ^ n) ^ 2 := div_pow _ _ _
      _ ≤ (M ^ 2 * unitBallVolume n * refinedRadius i ^ n) /
          (refinedRadius i ^ n) ^ 2 :=
        div_le_div_of_nonneg_right (channel_constant_sq_le hn (refinedRadius_pos i).le)
          (sq_nonneg _)
      _ = _ := by field_simp
  have hV : 0 ≤ unitBallVolume n := ENNReal.toReal_nonneg
  have hsum : (∑ i, a i ^ 2) ≤ (2 * M * Real.sqrt (unitBallVolume n)) ^ 2 := by
    calc
      _ ≤ ∑ i : RefinedIndex J, (M ^ 2 * unitBallVolume n) / refinedRadius i ^ n :=
        Finset.sum_le_sum (fun i _ ↦ hc i)
      _ = (M ^ 2 * unitBallVolume n) * ∑ i : RefinedIndex J, 1 / refinedRadius i ^ n := by
        simp only [Finset.mul_sum, mul_one_div]
      _ ≤ (M ^ 2 * unitBallVolume n) * 4 :=
        mul_le_mul_of_nonneg_left (inverse_radius_sum_le hn J)
          (mul_nonneg (sq_nonneg M) ENNReal.toReal_nonneg)
      _ = _ := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hV]
        ring
  have hroot : Real.sqrt (∑ i, a i ^ 2) ≤ 2 * M * Real.sqrt (unitBallVolume n) :=
    (Real.sqrt_le_sqrt hsum).trans_eq (Real.sqrt_sq (by positivity))
  calc
    _ ≤ ∫ η, ∑ i, ‖channelDensity (β i) (v i) η‖ := by
      apply integral_mono (integrable_density hβ hbound v).norm
        (integrable_finsetSum _ (fun i _ ↦ (integrable_channelDensity (hβ i) (hbound i) (v i)).norm))
      intro η
      exact norm_sum_le _ _
    _ = ∑ i, ∫ η, ‖channelDensity (β i) (v i) η‖ :=
      integral_finsetSum _ (fun i _ ↦ (integrable_channelDensity (hβ i) (hbound i) (v i)).norm)
    _ ≤ ∑ i, c i * ‖v i‖ :=
      Finset.sum_le_sum (fun i _ ↦ integral_norm_channelDensity_le hM (hbound i) (v i))
    _ = ∑ i, a i * b i := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [a, b]
      field_simp [pow_ne_zero n (ne_of_gt (refinedRadius_pos i))]
    _ ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _)

/-- The literal original wide density has the same bound after its existing
isometric two-shell identification. No Fourier normalization is changed. -/
theorem integral_norm_weightedWideDensity_le_moment {n J : ℕ} (hn : 1 ≤ n)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hbound : ∀ η, ‖d η‖ ≤ M)
    (v : WideInput n J) :
    (∫ η, ‖weightedWideDensity d v η‖) ≤
      (2 * M * Real.sqrt (unitBallVolume n)) * refinedMomentNorm (wideRefinement n J v) := by
  rw [integral_congr_ae ((weightedWideDensity_eq_refined hd hM hbound v).mono
    (fun _ h ↦ congrArg norm h))]
  exact integral_norm_density_le_moment hn
    (fun i ↦ measurable_weightedRadialBand hd i.1.val) hM
    (fun i ↦ norm_weightedRadialBand_le hbound i.1.val) _

private theorem shell_radius_bounds {n J : ℕ} :
    ∀ᵐ u ∂annularShellMeasure (n := n) (refinedRadius (J := J)),
      refinedRadius u.1 ≤ 2 * ‖u.2‖ ∧ (1 / 2 : ℝ) ≤ ‖u.2‖ := by
  apply Measure.ae_sum_iff.mpr
  intro i
  apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
  filter_upwards [ae_restrict_mem (measurableSet_annulus n (refinedRadius i))] with η hη
  have hl : refinedRadius i / 2 ≤ ‖η‖ := by
    simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hη.2
  have hr : 1 ≤ refinedRadius i := one_le_pow₀ (by norm_num)
  exact ⟨by linarith, by linarith⟩

private theorem radial_half_weight_bound (n : ℕ) {R r : ℝ}
    (hR : 0 ≤ R) (hRr : R ≤ 2 * r) (hr : (1 / 2 : ℝ) ≤ r) :
    R ^ n ≤ 2 ^ (n + 1) * r ^ ((n : ℝ) + 1 / 2) := by
  have hr0 : 0 < r := by linarith
  have hs : (1 / 2 : ℝ) ≤ Real.sqrt r :=
    (Real.le_sqrt (by norm_num) hr0.le).mpr (by nlinarith)
  have hp : r ^ n ≤ 2 * (r ^ n * Real.sqrt r) := by
    nlinarith [mul_nonneg (pow_nonneg hr0.le n) (sub_nonneg.mpr hs)]
  calc
    R ^ n ≤ (2 * r) ^ n := pow_le_pow_left₀ hR hRr n
    _ = 2 ^ n * r ^ n := mul_pow _ _ _
    _ ≤ 2 ^ n * (2 * (r ^ n * Real.sqrt r)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by
      rw [Real.rpow_add hr0, Real.rpow_natCast, ← Real.sqrt_eq_rpow, pow_succ]
      ring

/-- The literal shell isometry turns one native `(n+1)-1/2` moment into
the weighted refined norm. The constant is independent of the band count.
The actual moment producer is `nativeRealIndividualAdjoint_moment_L2_bound`
at `q=n+1`, applied to the SAME uncut-current inverse source. -/
theorem refinedMomentNorm_le_halfMoment {n J : ℕ}
    (f : Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))))
    (hf : MemLp (fun u ↦ ((‖u.2‖ ^ ((n : ℝ) + 1 / 2) : ℝ) : ℂ) * f u)
      2 (annularShellMeasure (n := n) (refinedRadius (J := J)))) :
    refinedMomentNorm (annularShellEquiv (refinedRadius (J := J)) f) ≤
      2 ^ (n + 1) * lpNorm (fun u ↦ ((‖u.2‖ ^ ((n : ℝ) + 1 / 2) : ℝ) : ℂ) * f u)
        2 (annularShellMeasure (n := n) (refinedRadius (J := J))) := by
  let μ := annularShellMeasure (n := n) (refinedRadius (J := J))
  let g : RefinedIndex J × Euclidean (n - 1) → ℂ :=
    fun u ↦ (refinedRadius u.1 ^ n : ℝ) • f u
  let F : RefinedIndex J × Euclidean (n - 1) → ℂ :=
    fun u ↦ ((‖u.2‖ ^ ((n : ℝ) + 1 / 2) : ℝ) : ℂ) * f u
  let C : ℝ := 2 ^ (n + 1)
  have hC : 0 ≤ C := by positivity
  have hg : AEStronglyMeasurable g μ := by
    have hm : AEStronglyMeasurable
        (fun u : RefinedIndex J × Euclidean (n - 1) ↦ (refinedRadius u.1 ^ n : ℝ)) μ :=
      ((measurable_of_finite (fun i : RefinedIndex J ↦ refinedRadius i ^ n)).comp
        measurable_fst).aestronglyMeasurable
    exact hm.smul (Lp.aestronglyMeasurable f)
  have hle : ∀ᵐ u ∂μ, ‖g u‖ ≤ ‖(C • F) u‖ := by
    filter_upwards [shell_radius_bounds (n := n) (J := J)] with u hu
    simp only [g, F, Pi.smul_apply, norm_smul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hC, Real.norm_of_nonneg (pow_nonneg (refinedRadius_pos u.1).le n),
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg u.2) _)]
    exact (mul_le_mul_of_nonneg_right
      (radial_half_weight_bound n (refinedRadius_pos u.1).le hu.1 hu.2) (norm_nonneg (f u))).trans_eq (by ring)
  have hmem : MemLp g 2 μ := (hf.const_smul C).mono hg hle
  let w : Lp ℂ 2 μ := hmem.toLp g
  have he (i : RefinedIndex J) :
      annularShellEquiv (refinedRadius (J := J)) w i =
        (refinedRadius i ^ n : ℝ) • annularShellEquiv (refinedRadius (J := J)) f i := by
    apply Lp.ext
    filter_upwards [annularShellEquiv_ae (refinedRadius (J := J)) w i,
      annularShellEquiv_ae (refinedRadius (J := J)) f i,
      ae_annularShell_slice (refinedRadius (J := J)) hmem.coeFn_toLp i,
      Lp.coeFn_smul (refinedRadius i ^ n : ℝ)
        (annularShellEquiv (refinedRadius (J := J)) f i)] with η hw hf hg hs
    change w (i, η) = g (i, η) at hg
    rw [hw, hg, hs]
    change g (i, η) = (refinedRadius i ^ n : ℝ) •
      annularShellEquiv (refinedRadius (J := J)) f i η
    rw [hf]
  have hnorm : refinedMomentNorm (annularShellEquiv (refinedRadius (J := J)) f) =
      lpNorm g 2 μ := by
    calc
      _ = Real.sqrt (∑ i : RefinedIndex J,
          ‖annularShellEquiv (refinedRadius (J := J)) w i‖ ^ 2) := by
        simp only [refinedMomentNorm, he, norm_smul,
          Real.norm_of_nonneg (pow_nonneg (refinedRadius_pos _).le n)]
      _ = ‖annularShellEquiv (refinedRadius (J := J)) w‖ := by
        rw [← norm_input_sq, Real.sqrt_sq (norm_nonneg _)]
      _ = ‖w‖ := (annularShellEquiv (refinedRadius (J := J))).norm_map w
      _ = _ := by rw [Lp.norm_toLp, toReal_eLpNorm]
  rw [hnorm]
  have hb := ENNReal.toReal_mono (hf.const_smul C).eLpNorm_ne_top (eLpNorm_mono_ae hg hle)
  simpa only [toReal_eLpNorm, lpNorm_const_smul, coe_nnnorm,
    Real.norm_of_nonneg hC] using hb

/-- Uniform Fourier mass for the SAME wide datum obtained by the original
shell and wide isometries. Only a finite native moment is consumed, never a
postulated mass bound or an old-manuscript forcing estimate. -/
theorem integral_norm_wide_of_halfMoment {n J : ℕ} (hn : 1 ≤ n)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hbound : ∀ η, ‖d η‖ ≤ M)
    (f : Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))))
    (hf : MemLp (fun u ↦ ((‖u.2‖ ^ ((n : ℝ) + 1 / 2) : ℝ) : ℂ) * f u)
      2 (annularShellMeasure (n := n) (refinedRadius (J := J)))) :
    (∫ η, ‖weightedWideDensity d
      ((wideRefinement n J).symm (annularShellEquiv (refinedRadius (J := J)) f)) η‖) ≤
      ((2 * M * Real.sqrt (unitBallVolume n)) * 2 ^ (n + 1)) *
        lpNorm (fun u ↦ ((‖u.2‖ ^ ((n : ℝ) + 1 / 2) : ℝ) : ℂ) * f u)
          2 (annularShellMeasure (n := n) (refinedRadius (J := J))) := by
  have h := integral_norm_weightedWideDensity_le_moment hn hd hM hbound
    ((wideRefinement n J).symm (annularShellEquiv (refinedRadius (J := J)) f))
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (refinedMomentNorm_le_halfMoment f hf)
    (by positivity)).trans_eq (by ring))

open Set CurrentMean PeriodicLocalL2 Pseudodifferential AmplitudeBound.PaperEstimates
open scoped ContDiff

local instance (J : ℕ) : MetricSpace (RefinedIndex J) :=
  TopologicalSpace.metrizableSpaceMetric (RefinedIndex J)

/-- Apply the original HALFWEIGHTED individual adjoint at the fixed order
`q=n+1`, then both unchanged shell/wide isometries. The source is arbitrary
regular `u`; in the actual mean construction it is the SAME `Q0 e`, and the
existing inverse-source profile pays these orders below `2*m0`. This is a
native-operator application, not a hypothesis asserting a Fourier mass bound
(`app:ch_mean_pairs:eq:raw-adjoint-moments`, `main:eq:primary-fixed-scales`). -/
theorem nativeIndividual_fourierMass_le {n J : ℕ} (hn : 1 ≤ n)
    (φ : (RefinedIndex J × Euclidean (n - 1)) → Euclidean n → ℝ)
    (m : RefinedIndex J × Euclidean (n - 1) → ℝ)
    (a : Fin n → Unit → RefinedIndex J → Euclidean (n - 1) → Euclidean n → ℂ)
    (L : RefinedIndex J → Euclidean (n - 1) → Euclidean (n - 1) → Euclidean n → Euclidean n)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
    (hhigh : ∀ z, ‖z.2‖ ≤ 1 → m z = 0)
    (ha : ∀ i j k, ContDiff ℝ ∞ (Function.uncurry (a i j k)))
    (hL : ∀ i h, ContDiff ℝ ∞ (fun p : Euclidean (n - 1) × Euclidean n ↦ L i p.1 h p.2))
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (has : ∀ i j k η, tsupport (a i j k η) ⊆ K)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ halfOpenCell n) (hχK : ∀ x ∈ K, χ x = 1)
    (Rbox : ℝ) (hbox : ∀ x ∈ K, ∀ i, |x i| ≤ Rbox)
    (Tbare : Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Euclidean n)))
    (hTbare : ∀ f : Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))),
      Tbare f =ᵐ[volume] fun x ↦ ∫ z,
        sampledMomentKernel φ m (fun _ x ↦ (χ x : ℂ)) x z * f z
          ∂annularShellMeasure (n := n) (refinedRadius (J := J)))
    (hφsmooth : ∀ z, ContDiff ℝ ∞ (φ z))
    (hphase : ∀ z, m z ≠ 0 → ∀ h x, x ∈ K →
      inner ℝ h z.2 = fderiv ℝ (φ z) x (L z.1 z.2 h x))
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (r₀ : ℕ) {T : ℝ} (hT : 1 ≤ T)
    (hamp : ∀ i j k η, m (k, η) ≠ 0 → ∀ x ∈ K, ∀ s,
      ‖iteratedFDeriv ℝ s (a i j k η) x‖ ≤ B s * T ^ (s - (r₀ + (n / 2 + 1))))
    (hcoeff : ∀ k η, m (k, η) ≠ 0 → ∀ h, ‖h‖ ≤ 1 → ∀ x ∈ K, ∀ s,
      ‖iteratedFDeriv ℝ s (L k η h) x‖ ≤ B s * T ^ (s - (r₀ + (n / 2 + 1))))
    (u : ContinuumRow.OutputL2 n)
    (hu : ∀ s, u ∈ periodicSobolevLevel n (Euclidean n) s)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hbound : ∀ η, ‖d η‖ ≤ M) :
    let μ := annularShellMeasure (n := n) (refinedRadius (J := J))
    let S := nativeMatrixRowOperator μ volume
      (sampledMomentMatrixEntry μ φ (halfWeightedMomentMask m) a hφ
        (continuous_halfWeightedMomentMask m hm) (hasCompactSupport_halfWeightedMomentMask m hms) ha hK has)
    let raw := finiteL2CoordinateIsometry μ
      ((transferOutputOperator (realQuadratureChannel S)).adjoint u) ()
    (∫ η, ‖weightedWideDensity d
      ((wideRefinement n J).symm (annularShellEquiv (refinedRadius (J := J)) raw)) η‖) ≤
      ((2 * M * Real.sqrt (unitBallVolume n)) * 2 ^ (n + 1)) *
        (nativeRealMomentConstant χ hχ hc hs Rbox B (n + 1) * ‖Tbare‖ *
          ∑ k ∈ Finset.range (n + 1 + 1), T ^ (n + 1 - k - r₀) * periodicSobolevNorm k u) := by
  intro μ S raw
  have hmoment := nativeRealIndividualAdjoint_moment_L2_bound μ φ m a L hφ hm hms hhigh
    ha hL hK has χ hχ hc hs hχK Rbox hbox Tbare hTbare hφsmooth hphase B hB
    (n + 1) r₀ hT hamp hcoeff u hu ()
  have hexp : ((n + 1 : ℕ) : ℝ) - 1 / 2 = (n : ℝ) + 1 / 2 := by
    push_cast
    ring
  dsimp only at hmoment
  rw [hexp] at hmoment
  exact (integral_norm_wide_of_halfMoment hn hd hM hbound raw hmoment.1).trans
    (mul_le_mul_of_nonneg_left hmoment.2 (by positivity))

end JanetCartan.PhysicalMean.FixedSourceFourierMass
