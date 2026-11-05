module

public import JanetCartan.Analysis.Fourier.Periodic.Mode
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Smooth periodic Fourier cutoffs

The fixed real-even symbol and the actual finite Fourier multiplier in
`main:lem:smoothing` and Appendix B of paper.tex, in the unit-torus convention.
-/

@[expose] public noncomputable section

open scoped ContDiff
open MeasureTheory

namespace JanetCartan

/-- The fixed bump underlying the symbol of `main:lem:smoothing`. -/
def fourierCutoffBump (n : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The real smooth symbol in `main:lem:smoothing`, with plateaus at radii 1 and 2. -/
def fourierCutoff {n : ℕ} : EuclideanSpace ℝ (Fin n) → ℝ := fourierCutoffBump n

/-- Smoothness of the fixed symbol (`main:lem:smoothing`). -/
theorem contDiff_fourierCutoff {n : ℕ} : ContDiff ℝ ∞ (@fourierCutoff n) :=
  (fourierCutoffBump n).contDiff

/-- Evenness ensures preservation of reality (`main:lem:smoothing`). -/
@[simp] theorem fourierCutoff_neg {n : ℕ} (ξ : EuclideanSpace ℝ (Fin n)) :
    fourierCutoff (-ξ) = fourierCutoff ξ := (fourierCutoffBump n).neg ξ

/-- The symbol is a contraction (`main:lem:smoothing`). -/
theorem fourierCutoff_mem_Icc {n : ℕ} (ξ : EuclideanSpace ℝ (Fin n)) :
    fourierCutoff ξ ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(fourierCutoffBump n).nonneg, (fourierCutoffBump n).le_one⟩

/-- The inner plateau of the smoothing symbol (`main:lem:smoothing`). -/
theorem fourierCutoff_eq_one {n : ℕ} {ξ : EuclideanSpace ℝ (Fin n)} (h : ‖ξ‖ ≤ 1) :
    fourierCutoff ξ = 1 :=
  (fourierCutoffBump n).one_of_mem_closedBall (by simpa [fourierCutoffBump] using h)

/-- The outer plateau of the smoothing symbol (`main:lem:smoothing`). -/
theorem fourierCutoff_eq_zero {n : ℕ} {ξ : EuclideanSpace ℝ (Fin n)} (h : 2 ≤ ‖ξ‖) :
    fourierCutoff ξ = 0 :=
  (fourierCutoffBump n).zero_of_le_dist (by simpa [fourierCutoffBump] using h)

/-- Compact support of the fixed smoothing symbol (`main:lem:smoothing`). -/
theorem hasCompactSupport_fourierCutoff {n : ℕ} : HasCompactSupport (@fourierCutoff n) :=
  (fourierCutoffBump n).hasCompactSupport

/-- Rescaled multiplier at the physical frequency `2πk` (`main:lem:smoothing`). -/
def periodicCutoffSymbol {n : ℕ} (R : ℝ) (k : Fin n → ℤ) : ℝ :=
  fourierCutoff ((2 * Real.pi / R) •
    (WithLp.toLp 2 (fun i ↦ (k i : ℝ)) : EuclideanSpace ℝ (Fin n)))

private theorem norm_scaled_frequency {n : ℕ} {R : ℝ} (hR : 0 < R) (k : Fin n → ℤ) :
    ‖(2 * Real.pi / R) •
      (WithLp.toLp 2 (fun i ↦ (k i : ℝ)) : EuclideanSpace ℝ (Fin n))‖ =
      frequencyNorm k / R := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  simp only [frequencyNorm]
  ring

/-- Evenness of the rescaled symbol (`main:lem:smoothing`). -/
@[simp] theorem periodicCutoffSymbol_neg {n : ℕ} (R : ℝ) (k : Fin n → ℤ) :
    periodicCutoffSymbol R (-k) = periodicCutoffSymbol R k := by
  unfold periodicCutoffSymbol
  have h : (WithLp.toLp 2 (fun i ↦ ((-k) i : ℝ)) : EuclideanSpace ℝ (Fin n)) =
      -(WithLp.toLp 2 (fun i ↦ (k i : ℝ))) := by ext i; simp
  rw [h, smul_neg, fourierCutoff_neg]

/-- Low physical frequencies are unchanged (`main:lem:smoothing`). -/
theorem periodicCutoffSymbol_eq_one {n : ℕ} {R : ℝ} (hR : 0 < R)
    {k : Fin n → ℤ} (hk : frequencyNorm k ≤ R) : periodicCutoffSymbol R k = 1 := by
  apply fourierCutoff_eq_one
  rw [norm_scaled_frequency hR]
  exact (div_le_one hR).2 hk

/-- Frequencies at least `2R` are killed (`main:lem:smoothing`). -/
theorem periodicCutoffSymbol_eq_zero {n : ℕ} {R : ℝ} (hR : 0 < R)
    {k : Fin n → ℤ} (hk : 2 * R ≤ frequencyNorm k) : periodicCutoffSymbol R k = 0 := by
  apply fourierCutoff_eq_zero
  rw [norm_scaled_frequency hR]
  exact (le_div_iff₀ hR).2 hk

/-- A finite box containing the support of the multiplier (`main:lem:smoothing`). -/
def periodicCutoffBox (n : ℕ) (R : ℝ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun _ ↦ Finset.Icc (-⌈2 * R⌉) ⌈2 * R⌉

/-- Every frequency below `2R` lies in the defining finite box (`main:lem:smoothing`). -/
theorem mem_periodicCutoffBox {n : ℕ} {R : ℝ} {k : Fin n → ℤ}
    (hk : frequencyNorm k ≤ 2 * R) : k ∈ periodicCutoffBox n R := by
  apply Fintype.mem_piFinset.mpr
  intro i
  have hi := PiLp.norm_apply_le (WithLp.toLp 2 (fun j ↦ (k j : ℝ))) i
  have hn := norm_nonneg (WithLp.toLp 2 (fun j ↦ (k j : ℝ)))
  have hp := Real.two_le_pi
  have hbound : |(k i : ℝ)| ≤ (⌈2 * R⌉ : ℝ) := by
    calc
      |(k i : ℝ)| ≤ ‖(WithLp.toLp 2 (fun j ↦ (k j : ℝ)) :
          EuclideanSpace ℝ (Fin n))‖ := hi
      _ ≤ frequencyNorm k := by unfold frequencyNorm; nlinarith
      _ ≤ 2 * R := hk
      _ ≤ (⌈2 * R⌉ : ℝ) := Int.le_ceil _
  rw [Finset.mem_Icc]
  exact ⟨by exact_mod_cast (abs_le.mp hbound).1,
    by exact_mod_cast (abs_le.mp hbound).2⟩

/-- Outside the finite box the symbol vanishes (`main:lem:smoothing`). -/
theorem periodicCutoffSymbol_eq_zero_of_notMem {n : ℕ} {R : ℝ} (hR : 0 < R)
    {k : Fin n → ℤ} (hk : k ∉ periodicCutoffBox n R) : periodicCutoffSymbol R k = 0 := by
  apply periodicCutoffSymbol_eq_zero hR
  exact le_of_lt (lt_of_not_ge (fun h ↦ hk (mem_periodicCutoffBox h)))

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual real periodic smoothing operator of `main:lem:smoothing`.

The finite sum uses the shared normalized Fourier coefficients. Its codomain is the
original real normed space; in particular real vector and matrix fields remain real.
-/
def periodicCutoff (R : ℝ) (f : Torus n → F) (x : Torus n) : F :=
  ∑ k ∈ periodicCutoffBox n R,
    periodicCutoffSymbol R k • periodicFourierMode k (periodicFourierCoeff f k) x

/-- Continuity of a real Fourier mode (Appendix B). -/
theorem continuous_periodicFourierMode (k : Fin n → ℤ) (a : F × F) :
    Continuous (periodicFourierMode k a) := by
  unfold periodicFourierMode
  fun_prop

/-- Smoothness of the Euclidean lift of the unit-torus character (Appendix B). -/
theorem contDiff_periodicLift_mFourier (k : Fin n → ℤ) :
    ContDiff ℝ ∞ (periodicLift (UnitAddTorus.mFourier k)) := by
  change ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) ↦
    ∏ i, fourier (k i) (x i : AddCircle (1 : ℝ)))
  simp only [fourier_coe_apply]
  apply contDiff_prod
  intro i _
  exact ((contDiff_const.mul
    (Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj i).contDiff)).div_const _).cexp

/-- Every real Fourier mode is smooth periodic (Appendix B). -/
theorem isSmoothPeriodic_periodicFourierMode (k : Fin n → ℤ) (a : F × F) :
    IsSmoothPeriodic (periodicFourierMode k a) := by
  refine ⟨continuous_periodicFourierMode k a, ?_⟩
  exact ((Complex.reCLM.contDiff.comp (contDiff_periodicLift_mFourier k)).smul
    contDiff_const).sub
    ((Complex.imCLM.contDiff.comp (contDiff_periodicLift_mFourier k)).smul contDiff_const)

/-- The cutoff produces a smooth periodic real field (`main:lem:smoothing`). -/
theorem isSmoothPeriodic_periodicCutoff (R : ℝ) (f : Torus n → F) :
    IsSmoothPeriodic (periodicCutoff R f) := by
  constructor
  · unfold periodicCutoff
    exact continuous_finsetSum _ fun k _ ↦ continuous_const.smul
      (continuous_periodicFourierMode k _)
  · change ContDiff ℝ ∞ (fun x ↦ ∑ k ∈ periodicCutoffBox n R,
      periodicCutoffSymbol R k • periodicLift (periodicFourierMode k (periodicFourierCoeff f k)) x)
    exact ContDiff.sum fun k _ ↦ contDiff_const.smul
      (isSmoothPeriodic_periodicFourierMode k _).2

end JanetCartan
