module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.Representatives
public import JanetCartan.Analysis.Fourier.Periodic.Reconstruction

/-!
# The smooth representative needed by the uncut preparation

The uncut auxiliary data in `app:ch_mean_pairs:eq:mean-density-recursion`
belong to every actual periodic Sobolev level. Their Fourier series therefore
defines one smooth representative, independent of the derivative order. This
leaf supplies the missing passage from those proved memberships to actual
functions; it makes no smoothness assertion for arbitrary L² data.
-/

@[expose] public noncomputable section

open MeasureTheory UnitAddTorus
open scoped ContDiff RealInnerProductSpace ENNReal

namespace JanetCartan.CurrentMean

variable {n : ℕ}

/-- Full periodic Sobolev membership gives every absolutely summable Fourier
moment needed by the uncut auxiliary update
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem summable_preparation_fourier_moments (u : ContinuumRow.OutputL2 n)
    (hu : ∀ s, u ∈ periodicSobolevLevel n (Euclidean n) s) (j : ℕ) :
    Summable (fun k ↦ frequencyNorm k ^ j *
      (‖(periodicFourierCoeff u k).1‖ + ‖(periodicFourierCoeff u k).2‖)) := by
  let s := j + (n + 1)
  let C := ‖periodicSobolevAnalysis s ⟨u, hu s⟩‖
  have hb (k : Fin n → ℤ) : periodicSobolevWeight s k *
      (‖(periodicFourierCoeff u k).1‖ + ‖(periodicFourierCoeff u k).2‖) ≤ 2 * C := by
    have hk := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (periodicSobolevAnalysis s ⟨u, hu s⟩) k
    simp only [periodicSobolevAnalysis_apply, weightedPeriodicL2FourierCoeff_apply,
      norm_smul, Real.norm_eq_abs, abs_of_pos (periodicSobolevWeight_pos _ _)] at hk
    have h₁ := WithLp.norm_fst_le (p := 2) _ (periodicL2FourierCoeff k u)
    have h₂ := WithLp.norm_snd_le (p := 2) _ (periodicL2FourierCoeff k u)
    change ‖(periodicFourierCoeff u k).1‖ ≤ _ at h₁
    change ‖(periodicFourierCoeff u k).2‖ ≤ _ at h₂
    nlinarith [periodicSobolevWeight_pos s k]
  have hs := (summable_frequencyNorm_rpow (n := n)
    (p := (n + 1 : ℕ)) (by push_cast; linarith)).mul_left (2 * C)
  apply Summable.of_norm_bounded_eventually hs
  filter_upwards [Filter.eventually_cofinite_ne 0] with k hk
  have hp := frequencyNorm_pos_of_ne_zero k hk
  have hw : frequencyNorm k ^ s ≤ periodicSobolevWeight s k := by
    apply pow_le_pow_left₀ hp.le
    have hsq := Real.sq_sqrt (show 0 ≤ 1 + frequencyNorm k ^ 2 by positivity)
    have hn := Real.sqrt_nonneg (1 + frequencyNorm k ^ 2)
    nlinarith
  have hdecay : ‖(periodicFourierCoeff u k).1‖ + ‖(periodicFourierCoeff u k).2‖ ≤
      2 * C / frequencyNorm k ^ s := by
    apply (le_div_iff₀ (pow_pos hp s)).mpr
    exact (by simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_right hw (by positivity)).trans (hb k))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ frequencyNorm k ^ j * (2 * C / frequencyNorm k ^ s) :=
      mul_le_mul_of_nonneg_left hdecay (pow_nonneg hp.le j)
    _ = 2 * C * frequencyNorm k ^ (-((n + 1 : ℕ) : ℝ)) := by
      rw [Real.rpow_neg hp.le, Real.rpow_natCast]
      dsimp [s]
      rw [pow_add]
      field_simp

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
    rw [hμ, ← he]
    exact ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) μ (∑' k, modes k)
  filter_upwards [hz, hae] with x hx hg
  have hre := Complex.reCLM.hasSum ((ContinuousMap.evalCLM ℂ x).hasSum hm.hasSum)
  have heq (k : Fin n → ℤ) : (modes k x).re =
      periodicFourierMode k (periodicFourierCoeff u k) x := by
    simp [modes, hc, periodicFourierMode, Complex.mul_re, mul_comm]
  change HasSum (fun k ↦ (modes k x).re) ((∑' k, modes k : C(Torus n, ℂ)) x).re at hre
  simp_rw [heq] at hre
  rw [hre.tsum_eq, ← hg, hx]
  rfl

/-- The literal Fourier representative of the uncut periodic preparation
data (`app:ch_mean_pairs:eq:mean-density-recursion`). -/
def preparationFourierRepresentative (u : ContinuumRow.OutputL2 n) : Torus n → Euclidean n :=
  fun x ↦ ∑' k, periodicFourierMode k (periodicFourierCoeff u k) x

/-- Smoothness of this ONE representative follows by differentiating its
absolutely convergent series at every order
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem isSmoothPeriodic_preparationFourierRepresentative (u : ContinuumRow.OutputL2 n)
    (hu : ∀ s, u ∈ periodicSobolevLevel n (Euclidean n) s) :
    IsSmoothPeriodic (preparationFourierRepresentative u) := by
  have hs := summable_preparation_fourier_moments u hu
  constructor
  · unfold preparationFourierRepresentative
    exact continuous_tsum (u := fun k ↦ ‖(periodicFourierCoeff u k).1‖ +
      ‖(periodicFourierCoeff u k).2‖) (fun k ↦ continuous_periodicFourierMode k _)
      (by simpa using hs 0) (fun k x ↦ norm_periodicFourierMode_le k _ _ x)
  · unfold periodicLift preparationFourierRepresentative
    apply contDiff_tsum (N := ⊤)
      (v := fun j k ↦ frequencyNorm k ^ j *
        (‖(periodicFourierCoeff u k).1‖ + ‖(periodicFourierCoeff u k).2‖))
    · exact fun k ↦ contDiff_periodicLift_periodicFourierMode k _ _
    · exact fun j _ ↦ hs j
    · exact fun j k x _ ↦ norm_iteratedFDeriv_periodicFourierMode_le k _ _ j x

/-- The smooth Fourier representative realizes the original L² class,
with both real Fourier components retained
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem preparationFourierRepresentative_ae (u : ContinuumRow.OutputL2 n)
    (hu : ∀ s, u ∈ periodicSobolevLevel n (Euclidean n) s) :
    u =ᵐ[volume] preparationFourierRepresentative u := by
  have hs : Summable (fun k ↦ ‖(periodicFourierCoeff u k).1‖ +
      ‖(periodicFourierCoeff u k).2‖) := by
    simpa using summable_preparation_fourier_moments u hu 0
  have hm (x : Torus n) := Summable.of_norm_bounded hs
    (fun k ↦ norm_periodicFourierMode_le k (periodicFourierCoeff u k).1
      (periodicFourierCoeff u k).2 x)
  let b := stdOrthonormalBasis ℝ (Euclidean n)
  suffices h : ∀ i, (fun x ↦ ⟪b i, u x⟫) =ᵐ[volume]
      fun x ↦ ⟪b i, preparationFourierRepresentative u x⟫ by
    filter_upwards [ae_all_iff.mpr h] with x hx
    apply b.repr.injective
    ext i
    simpa only [OrthonormalBasis.repr_apply_apply] using hx i
  intro i
  let L := innerSL ℝ (b i)
  let v := L.compLp u
  have hc (k : Fin n → ℤ) : periodicFourierCoeff v k =
      (L (periodicFourierCoeff u k).1, L (periodicFourierCoeff u k).2) := by
    rw [periodicFourierCoeff_congr_ae (L.coeFn_compLp u)]
    exact periodicFourierCoeff_inner (Lp.memLp u) (b i) k
  have hsv : Summable (fun k ↦ ‖(periodicFourierCoeff v k).1‖ +
      ‖(periodicFourierCoeff v k).2‖) := by
    apply Summable.of_nonneg_of_le (fun _ ↦ by positivity) _ (hs.mul_left ‖L‖)
    intro k
    rw [hc, mul_add]
    exact add_le_add (L.le_opNorm _) (L.le_opNorm _)
  have he (x : Torus n) : (∑' k, periodicFourierMode k (periodicFourierCoeff v k) x) =
      L (preparationFourierRepresentative u x) := by
    rw [preparationFourierRepresentative, L.map_tsum (hm x)]
    apply tsum_congr
    intro k
    simp only [hc, periodicFourierMode, map_sub, map_smul]
  filter_upwards [L.coeFn_compLp u, scalar_reconstruction v hsv] with x hx hy
  exact hx.symm.trans (hy.trans (he x))

end JanetCartan.CurrentMean
