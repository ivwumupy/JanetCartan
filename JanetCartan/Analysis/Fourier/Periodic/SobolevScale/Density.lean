module

public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.Density.Coefficients
public import Mathlib.Analysis.Normed.Group.Tannery
/-!
# Smooth density in the periodic Sobolev spaces

For `app:not:fourier` and `app:ch_background:prop:bg-inverse`, approximate every
Sobolev element by the finite real Fourier cutoffs at radii `j + 1`. The cutoff
coefficient formula holds for arbitrary L² inputs. Dominated convergence of the
summable weighted energies proves convergence in the actual Sobolev norm.

The resulting density statements also give smooth density in L² and dense range
of every Sobolev inclusion into L², in particular the order-one inclusion needed
for the negative-order dual. No positive-dimension or nonzero-codomain assumption
is required.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace JanetCartan.PeriodicSobolevSpace
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The L² class of a smooth Sobolev element has the prescribed representative
(`app:not:fourier`). -/
theorem toL2_ofSmooth_ae (s : ℕ) (f : Torus n → F) (hf : IsSmoothPeriodic f) :
    (toL2 s (ofSmooth s f hf) : Torus n → F) =ᵐ[volume] f := by
  exact (hf.1.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)).coeFn_toLp

/-- Finite smooth Fourier approximations in the actual Sobolev space
(`app:ch_background:prop:bg-inverse`). The radius is always positive. -/
def smoothApproximation (s : ℕ) (u : PeriodicSobolevSpace n F s) (j : ℕ) :
    PeriodicSobolevSpace n F s :=
  ofSmooth s (periodicCutoff (j + 1) (toL2 s u))
    (isSmoothPeriodic_periodicCutoff _ _)

/-- The finite approximation multiplies the weighted Fourier coefficients by the
shared cutoff symbol (`app:not:fourier`). -/
theorem analysis_smoothApproximation (s : ℕ) (u : PeriodicSobolevSpace n F s)
    (j : ℕ) (k : Fin n → ℤ) :
    analysis s (smoothApproximation s u j) k =
      periodicCutoffSymbol (j + 1) k • analysis s u k := by
  rw [analysis_apply, analysis_apply]
  simp only [periodicL2FourierCoeff_apply, smoothApproximation,
    periodicFourierCoeff_congr_ae (toL2_ofSmooth_ae _ _ _),
    periodicFourierCoeff_periodicCutoff_memLp (Lp.memLp _) (by positivity : (0 : ℝ) < j + 1),
    WithLp.toLp_smul]
  exact smul_comm _ _ _

/-- The weighted Fourier energy sums to the squared Sobolev norm
(`app:not:fourier`; `app:ch_background:prop:bg-inverse`). -/
theorem hasSum_sq_analysis (s : ℕ) (u : PeriodicSobolevSpace n F s) :
    HasSum (fun k ↦ ‖analysis s u k‖ ^ 2) (‖u‖ ^ 2) := by
  have hn : ‖analysis s u‖ = ‖u‖ := (analysisIsometry s).norm_map u
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, hn] using
    lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (analysis s u)

/-- The weighted Fourier energy of the approximation error tends to zero
(`app:ch_background:prop:bg-inverse`). This is dominated convergence of a
genuinely summable energy series, with eventual equality at each frequency. -/
theorem tendsto_weighted_error_energy (s : ℕ) (u : PeriodicSobolevSpace n F s) :
    Tendsto (fun j ↦ ∑' k, ‖analysis s (smoothApproximation s u j - u) k‖ ^ 2)
      atTop (𝓝 0) := by
  have hpoint (k : Fin n → ℤ) :
      Tendsto (fun j ↦ ‖analysis s (smoothApproximation s u j - u) k‖ ^ 2)
        atTop (𝓝 0) := by
    obtain ⟨N, hN⟩ := exists_nat_gt (frequencyNorm k)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with j hj
    have hk : frequencyNorm k ≤ (j : ℝ) + 1 := by
      have hNj : (N : ℝ) ≤ j := by exact_mod_cast hj
      linarith
    simp only [map_sub, lp.coeFn_sub, Pi.sub_apply, analysis_smoothApproximation,
      periodicCutoffSymbol_eq_one (by positivity) hk, one_smul, sub_self, norm_zero,
      zero_pow (by decide : 2 ≠ 0)]
  have hbound (j : ℕ) (k : Fin n → ℤ) :
      ‖‖analysis s (smoothApproximation s u j - u) k‖ ^ 2‖ ≤ ‖analysis s u k‖ ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [map_sub, lp.coeFn_sub, Pi.sub_apply, analysis_smoothApproximation]
    have heq : periodicCutoffSymbol (j + 1) k • analysis s u k - analysis s u k =
        (periodicCutoffSymbol (j + 1) k - 1) • analysis s u k := by
      rw [sub_smul, one_smul]
    rw [heq, norm_smul]
    have hc : periodicCutoffSymbol (j + 1) k ∈ Set.Icc (0 : ℝ) 1 :=
      fourierCutoff_mem_Icc _
    have ha : ‖periodicCutoffSymbol (j + 1) k - 1‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hc.1, hc.2]
    gcongr
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ha (norm_nonneg (analysis s u k))
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence
    (hasSum_sq_analysis s u).summable hpoint (Eventually.of_forall hbound)

/-- Finite smooth Fourier approximations converge in the Sobolev norm
(`app:ch_background:prop:bg-inverse`). -/
theorem tendsto_smoothApproximation (s : ℕ) (u : PeriodicSobolevSpace n F s) :
    Tendsto (smoothApproximation s u) atTop (𝓝 u) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h := tendsto_weighted_error_energy s u
  simp_rw [(hasSum_sq_analysis s _).tsum_eq] at h
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs

/-- Smooth periodic representatives are dense in each actual Sobolev space
with its Sobolev topology (`app:ch_background:prop:bg-inverse`). -/
theorem denseRange_ofSmooth (s : ℕ) :
    DenseRange (fun f : {f : Torus n → F // IsSmoothPeriodic f} ↦ ofSmooth s f.1 f.2) := by
  intro u
  apply mem_closure_of_tendsto (tendsto_smoothApproximation s u)
  exact Eventually.of_forall fun j ↦
    ⟨⟨periodicCutoff (j + 1) (toL2 s u), isSmoothPeriodic_periodicCutoff _ _⟩, rfl⟩

/-- Smooth periodic representatives, realized through any Sobolev level,
are dense in real L² (`app:not:fourier`; `app:ch_background:prop:bg-inverse`). -/
theorem denseRange_toL2_ofSmooth (s : ℕ) :
    DenseRange (fun f : {f : Torus n → F // IsSmoothPeriodic f} ↦
      toL2 s (ofSmooth s f.1 f.2)) := by
  have hz : Function.Surjective (toL2 (n := n) (F := F) 0) := by
    intro u
    exact ⟨ofL2 0 u (by rw [periodicSobolevLevel_zero]; trivial), toL2_ofL2 _ _ _⟩
  have h := hz.denseRange.comp (denseRange_ofSmooth (n := n) (F := F) 0)
    (toL2 0).continuous
  change DenseRange (fun f : {f : Torus n → F // IsSmoothPeriodic f} ↦
    toL2 0 (ofSmooth 0 f.1 f.2)) at h
  have heq (f : {f : Torus n → F // IsSmoothPeriodic f}) :
      toL2 s (ofSmooth s f.1 f.2) = toL2 0 (ofSmooth 0 f.1 f.2) := by
    apply Lp.ext
    exact (toL2_ofSmooth_ae s f.1 f.2).trans (toL2_ofSmooth_ae 0 f.1 f.2).symm
  simpa only [heq] using h

/-- Every nonnegative Sobolev level has dense image in L². In particular,
`s = 1` supplies the dense inclusion for negative-order duality
(`app:ch_background:prop:bg-inverse`). -/
theorem denseRange_toL2 (s : ℕ) : DenseRange (toL2 (n := n) (F := F) s) :=
  (denseRange_toL2_ofSmooth (n := n) (F := F) s).of_comp

end JanetCartan.PeriodicSobolevSpace
