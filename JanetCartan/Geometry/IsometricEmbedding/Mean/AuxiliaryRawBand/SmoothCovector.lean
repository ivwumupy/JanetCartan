module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRawBand.Source
public import JanetCartan.Analysis.Fourier.Periodic.Reconstruction

/-!
# Smoothness of the fixed auxiliary covector

The series fixed in `app:ch_background:eq:bg-Vaux` converges smoothly, represents
its L² Bessel inverse, and has the exact one-order Sobolev norm gain required by
`app:ch_background:prop:bg-mixed-physical`.
-/

@[expose] public noncomputable section

open MeasureTheory UnitAddTorus
open scoped ContDiff RealInnerProductSpace

namespace JanetCartan.AuxiliaryRawBand

open ContinuumRow

variable {n : ℕ}

private theorem bessel_mode_eq (k : Fin n → ℤ) (a b : Euclidean n) :
    (fun x ↦ periodicBesselSymbol k • periodicFourierModeOfParts k a b x) =
      periodicFourierModeOfParts k (periodicBesselSymbol k • a)
        (periodicBesselSymbol k • b) := by
  funext x
  simp only [periodicFourierModeOfParts, periodicFourierMode, smul_sub]
  congr 1 <;> exact smul_comm _ _ _

private theorem bessel_coeff_bound (k : Fin n → ℤ) (a b : Euclidean n) :
    ‖periodicBesselSymbol k • a‖ + ‖periodicBesselSymbol k • b‖ ≤ ‖a‖ + ‖b‖ := by
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (periodicBesselSymbol_pos k)]
  exact add_le_add
    (mul_le_of_le_one_left (norm_nonneg _) (periodicBesselSymbol_le_one k))
    (mul_le_of_le_one_left (norm_nonneg _) (periodicBesselSymbol_le_one k))

private theorem norm_bessel_mode_le (k : Fin n → ℤ) (a b : Euclidean n)
    (x : Torus n) :
    ‖periodicBesselSymbol k • periodicFourierModeOfParts k a b x‖ ≤ ‖a‖ + ‖b‖ := by
  rw [congrFun (bessel_mode_eq k a b) x]
  exact (norm_periodicFourierMode_le k _ _ x).trans (bessel_coeff_bound k a b)

/-- Absolute convergence of the particular covector series in
`app:ch_background:eq:bg-Vaux`, including dimension zero. -/
theorem summable_rawCovector (χsrc : C(Torus n, ℝ))
    (hχ : IsSmoothPeriodic (χsrc : Torus n → ℝ)) (K : ℝ) (h : OutputL2 n)
    (x : Torus n) :
    Summable (fun k : Fin n → ℤ ↦ periodicBesselSymbol k •
      periodicFourierModeOfParts k (periodicFourierCoeff (rawSource χsrc K h) k).1
        (periodicFourierCoeff (rawSource χsrc K h) k).2 x) := by
  have hs := (isSmoothPeriodic_rawSource χsrc hχ K h).summable_frequencyNorm_pow_coeff 0
  simp only [pow_zero, one_mul] at hs
  exact Summable.of_norm_bounded hs (fun k ↦ norm_bessel_mode_le k _ _ x)

/-- Smoothness of the fixed Fourier-series covector used by the physical field
in `app:ch_background:eq:bg-Vaux`; no representative is chosen at any order. -/
theorem isSmoothPeriodic_rawCovector (χsrc : C(Torus n, ℝ))
    (hχ : IsSmoothPeriodic (χsrc : Torus n → ℝ)) (K : ℝ) (h : OutputL2 n) :
    IsSmoothPeriodic (rawCovector χsrc K h) := by
  have hs := (isSmoothPeriodic_rawSource χsrc hχ K h).summable_frequencyNorm_pow_coeff
  constructor
  · unfold rawCovector
    refine continuous_tsum ?_ (by simpa using hs 0) ?_
    · intro k
      exact (continuous_periodicFourierMode k _).const_smul (periodicBesselSymbol k)
    · exact fun k x ↦ norm_bessel_mode_le k _ _ x
  · unfold periodicLift rawCovector
    simp_rw [congrFun (bessel_mode_eq _ _ _) _]
    apply contDiff_tsum (N := ⊤)
      (v := fun j k ↦ frequencyNorm k ^ j *
        (‖(periodicFourierCoeff (rawSource χsrc K h) k).1‖ +
          ‖(periodicFourierCoeff (rawSource χsrc K h) k).2‖))
    · intro k
      exact contDiff_periodicLift_periodicFourierMode k _ _
    · exact fun j _ ↦ hs j
    · intro j k x _
      exact (norm_iteratedFDeriv_periodicFourierMode_le k _ _ j x).trans
        (mul_le_mul_of_nonneg_left (bessel_coeff_bound k _ _)
          (pow_nonneg (frequencyNorm_nonneg k) j))

private theorem scalar_reconstruction (u : PeriodicL2 n ℝ)
    (hs : Summable (fun k ↦ ‖(periodicFourierCoeff u k).1‖ +
      ‖(periodicFourierCoeff u k).2‖)) :
    u =ᵐ[volume] fun x ↦ ∑' k, periodicFourierMode k (periodicFourierCoeff u k) x := by
  let μ := Measure.pi (fun _ : Fin n ↦ (AddCircle.haarAddCircle : Measure UnitAddCircle))
  have hμ : (volume : Measure (Torus n)) = μ := torus_volume_eq_pi_haarAddCircle
  have hu : MemLp (fun x ↦ (u x : ℂ)) 2 μ := by
    rw [← hμ]
    exact (Lp.memLp u).ofReal
  let z := hu.toLp (fun x ↦ (u x : ℂ))
  have hz : z =ᵐ[volume] fun x ↦ (u x : ℂ) := by
    simpa only [hμ] using hu.coeFn_toLp
  have hc (k : Fin n → ℤ) : mFourierCoeff z k =
      ⟨(periodicFourierCoeff u k).1, (periodicFourierCoeff u k).2⟩ := by
    rw [show mFourierCoeff z k = mFourierCoeff (fun x ↦ (u x : ℂ)) k from
      (by
        simp only [mFourierCoeff_eq_volume_integral]
        exact integral_congr_ae (hz.mono fun x hx ↦ by simp only [hx]))]
    exact mFourierCoeff_ofReal_memLp (Lp.memLp u) k
  let modes : (Fin n → ℤ) → C(Torus n, ℂ) := fun k ↦ mFourierCoeff z k • mFourier k
  have hm : Summable modes := by
    apply Summable.of_norm_bounded hs
    intro k
    simp only [modes, norm_smul, mFourier_norm, mul_one, hc]
    exact Complex.norm_le_abs_re_add_abs_im _
  have he : ContinuousMap.toLp 2 μ ℂ (∑' k, modes k) = z := by
    have hmLp : HasSum (fun k ↦ ContinuousMap.toLp 2 μ ℂ (modes k)) z := by
      convert! hasSum_mFourier_series_L2 z using 1
    exact ((ContinuousMap.toLp 2 μ ℂ).hasSum hm.hasSum).unique hmLp
  have hae : z =ᵐ[volume] ((∑' k, modes k : C(Torus n, ℂ)) : Torus n → ℂ) := by
    rw [hμ]
    rw [← he]
    exact ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) μ (∑' k, modes k)
  filter_upwards [hz, hae] with x hx hg
  have hsx := (ContinuousMap.evalCLM ℂ x).hasSum hm.hasSum
  have hre := Complex.reCLM.hasSum hsx
  have heq (k : Fin n → ℤ) : (modes k x).re =
      periodicFourierMode k (periodicFourierCoeff u k) x := by
    simp [modes, hc, periodicFourierMode, Complex.mul_re, mul_comm]
  change HasSum (fun k ↦ (modes k x).re) ((∑' k, modes k : C(Torus n, ℂ)) x).re at hre
  simp_rw [heq] at hre
  rw [hre.tsum_eq, ← hg, hx]
  rfl

private theorem coeff_rawCovectorL2 (χsrc : C(Torus n, ℝ)) (K : ℝ)
    (h : OutputL2 n) (k : Fin n → ℤ) :
    periodicFourierCoeff (rawCovectorL2 χsrc K h) k =
      periodicBesselSymbol k • periodicFourierCoeff (rawSource χsrc K h) k := by
  have hc := rawCovectorL2_coeff χsrc K h k
  simp only [periodicL2FourierCoeff_apply, ← WithLp.toLp_smul] at hc
  have hc' := WithLp.toLp_injective 2 hc
  rw [periodicFourierCoeff_congr_ae (rawSourceL2_coeFn χsrc K h)] at hc'
  exact hc'

private theorem inner_rawCovectorL2_ae (χsrc : C(Torus n, ℝ))
    (hχ : IsSmoothPeriodic (χsrc : Torus n → ℝ)) (K : ℝ) (h : OutputL2 n)
    (v : Euclidean n) :
    (fun x ↦ ⟪v, rawCovectorL2 χsrc K h x⟫) =ᵐ[volume]
      fun x ↦ ⟪v, rawCovector χsrc K h x⟫ := by
  let L := innerSL ℝ v
  let u := L.compLp (rawCovectorL2 χsrc K h)
  have hc (k : Fin n → ℤ) : periodicFourierCoeff u k =
      (L (periodicBesselSymbol k • (periodicFourierCoeff (rawSource χsrc K h) k).1),
       L (periodicBesselSymbol k • (periodicFourierCoeff (rawSource χsrc K h) k).2)) := by
    rw [periodicFourierCoeff_congr_ae (L.coeFn_compLp _)]
    simp only [L, innerSL_apply_apply]
    rw [periodicFourierCoeff_inner (Lp.memLp _), coeff_rawCovectorL2]
    rfl
  have hs : Summable (fun k ↦ ‖(periodicFourierCoeff u k).1‖ +
      ‖(periodicFourierCoeff u k).2‖) := by
    have hsource := (isSmoothPeriodic_rawSource χsrc hχ K h).summable_frequencyNorm_pow_coeff 0
    simp only [pow_zero, one_mul] at hsource
    apply Summable.of_nonneg_of_le (fun _ ↦ by positivity) _ (hsource.mul_left ‖L‖)
    intro k
    rw [hc]
    calc
      _ ≤ ‖L‖ * (‖periodicBesselSymbol k • (periodicFourierCoeff (rawSource χsrc K h) k).1‖ +
          ‖periodicBesselSymbol k • (periodicFourierCoeff (rawSource χsrc K h) k).2‖) := by
        rw [mul_add]
        exact add_le_add (L.le_opNorm _) (L.le_opNorm _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (bessel_coeff_bound k _ _) (norm_nonneg _)
  have heq (x : Torus n) :
      (∑' k, periodicFourierMode k (periodicFourierCoeff u k) x) =
        L (rawCovector χsrc K h x) := by
    rw [rawCovector, L.map_tsum (summable_rawCovector χsrc hχ K h x)]
    apply tsum_congr
    intro k
    rw [hc]
    simp only [periodicFourierMode, map_smul, map_sub, smul_sub]
    congr 1 <;> exact smul_comm _ _ _
  change (fun x ↦ L (rawCovectorL2 χsrc K h x)) =ᵐ[volume]
    fun x ↦ L (rawCovector χsrc K h x)
  filter_upwards [L.coeFn_compLp (rawCovectorL2 χsrc K h), scalar_reconstruction u hs]
    with x hx hy
  exact hx.symm.trans (hy.trans (heq x))

/-- The literal smooth series represents the L² covector in
`app:ch_background:eq:bg-Vaux`. -/
theorem rawCovectorL2_coeFn (χsrc : C(Torus n, ℝ))
    (hχ : IsSmoothPeriodic (χsrc : Torus n → ℝ)) (K : ℝ) (h : OutputL2 n) :
    rawCovectorL2 χsrc K h =ᵐ[volume] rawCovector χsrc K h := by
  let b := stdOrthonormalBasis ℝ (Euclidean n)
  have ha := ae_all_iff.mpr (fun i ↦ inner_rawCovectorL2_ae χsrc hχ K h (b i))
  filter_upwards [ha] with x hx
  apply b.repr.injective
  ext i
  simpa only [OrthonormalBasis.repr_apply_apply] using hx i


/-- Every Sobolev realization of the fixed series has the same underlying L²
covector (`app:ch_background:eq:bg-Vaux`). -/
theorem toL2_ofSmooth_rawCovector (χsrc : C(Torus n, ℝ))
    (hχ : IsSmoothPeriodic (χsrc : Torus n → ℝ)) (K : ℝ) (h : OutputL2 n) (s : ℕ) :
    PeriodicSobolevSpace.toL2 s (PeriodicSobolevSpace.ofSmooth s
      (rawCovector χsrc K h) (isSmoothPeriodic_rawCovector χsrc hχ K h)) =
        rawCovectorL2 χsrc K h := by
  apply Lp.ext
  exact (PeriodicSobolevSpace.toL2_ofSmooth_ae _ _ _).trans
    (rawCovectorL2_coeFn χsrc hχ K h).symm

/-- Smooth realization and the actual one-order Bessel gain agree as Sobolev
space elements, not just as norm estimates (`app:ch_background:eq:bg-Vaux`). -/
theorem ofSmooth_rawCovector_eq_gain (χsrc : C(Torus n, ℝ))
    (hχ : IsSmoothPeriodic (χsrc : Torus n → ℝ)) (K : ℝ) (h : OutputL2 n) (s : ℕ) :
    PeriodicSobolevSpace.ofSmooth (s + 1) (rawCovector χsrc K h)
      (isSmoothPeriodic_rawCovector χsrc hχ K h) =
        periodicBesselGain s (PeriodicSobolevSpace.ofSmooth s (rawSource χsrc K h)
          (isSmoothPeriodic_rawSource χsrc hχ K h)) := by
  apply PeriodicSobolevSpace.toL2_injective (s + 1)
  rw [toL2_ofSmooth_rawCovector χsrc hχ, toL2_gain_rawSource χsrc hχ]

/-- Exact norm gain for the fixed smooth covector, supplying the derivative
paired with the full geometric strain in
`app:ch_background:eq:bg-Vaux-raw-band`. -/
theorem periodicSobolevNorm_rawCovector (χsrc : C(Torus n, ℝ))
    (hχ : IsSmoothPeriodic (χsrc : Torus n → ℝ)) (K : ℝ) (h : OutputL2 n) (s : ℕ) :
    periodicSobolevNorm (s + 1) (rawCovector χsrc K h) =
      periodicSobolevNorm s (rawSource χsrc K h) := by
  have hn : ‖PeriodicSobolevSpace.ofSmooth (s + 1) (rawCovector χsrc K h)
      (isSmoothPeriodic_rawCovector χsrc hχ K h)‖ =
      periodicSobolevNorm (s + 1) (rawCovector χsrc K h) := by
    rw [PeriodicSobolevSpace.norm_eq]
    simp only [periodicSobolevNorm,
      periodicFourierCoeff_congr_ae (PeriodicSobolevSpace.toL2_ofSmooth_ae _ _ _),
      Nat.cast_add, Nat.cast_one]
  rw [← hn, ofSmooth_rawCovector_eq_gain χsrc hχ, norm_gain_rawSource χsrc hχ]

end JanetCartan.AuxiliaryRawBand
