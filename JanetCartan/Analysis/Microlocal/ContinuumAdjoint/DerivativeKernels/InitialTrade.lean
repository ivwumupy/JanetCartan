module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.CompactTrade
/-!
# Physical frequency multiplication as a measurement derivative

For `app:ch_background:eq:bg-derivative-trade`, the row of the rectangular left
inverse gives `ηⱼ = dₓΦ(Lⱼ)`. This proves the initial-coordinate derivative trade
as multiplication by `i ηⱼ`. There is no differentiation in η and no initial
physical cutoff. The auxiliary phase translation in the proof is only a way to
reuse the checked compact parameter integration-by-parts theorem.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open NormalComparison
variable {n : ℕ}

/-- A constant phase translation factors out of the literal chart integral,
with the physical exponential convention of `app:ch_background:eq:bg-T`. -/
theorem chartAdjoint_phase_shift (φ : Euclidean n → ℝ) (a v : Euclidean n → ℂ) (t η : ℝ) :
    chartAdjoint (fun x ↦ φ x - t * η) a v =
      Complex.exp (Complex.I * (t * η : ℝ)) * chartAdjoint φ a v := by
  unfold chartAdjoint
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  unfold oscillatoryFactor
  rw [show Complex.I * ((-1 : ℝ) * (φ x - t * η) : ℝ) =
      Complex.I * (t * η : ℝ) + Complex.I * ((-1 : ℝ) * φ x : ℝ) by push_cast; ring,
    Complex.exp_add]
  ring

/-- The coefficient with no output derivative after a physical initial
coordinate derivative, for `app:ch_background:prop:bg-adjoint`. -/
def initialZeroAmplitude (a : Euclidean n → ℂ)
    (L : Euclidean n → Euclidean n) (x : Euclidean n) : ℂ :=
  ∑ j, partialDeriv (fun y ↦ L y j • a y) x j

/-- The coefficient of `∂xⱼ v` after a physical initial coordinate derivative,
for `app:ch_background:prop:bg-adjoint`. -/
def initialFirstAmplitude (a : Euclidean n → ℂ)
    (L : Euclidean n → Euclidean n) (j : Fin n) (x : Euclidean n) : ℂ :=
  L x j • a x

/-- Multiplication by physical `i η` is exactly the transpose of a measurement
phase derivative (`app:ch_background:eq:bg-derivative-trade`). The phase relation
is required only on amplitude support; the compact support of that amplitude
supplies convergence and removes every boundary term. -/
theorem chartAdjoint_initial_trade {φ : Euclidean n → ℝ} {a v : Euclidean n → ℂ}
    {L : Euclidean n → Euclidean n} (hφ : ContDiff ℝ ∞ φ)
    (ha : ContDiff ℝ ∞ a) (hv : ContDiff ℝ ∞ v) (hL : ContDiff ℝ ∞ L)
    (hs : HasCompactSupport a) (η : ℝ)
    (hphase : ∀ x, a x ≠ 0 → η = fderiv ℝ φ x (L x)) :
    (Complex.I * (η : ℂ)) * chartAdjoint φ a v =
      ∫ x, oscillatoryFactor (-1) (φ x) *
        (initialZeroAmplitude a L x * v x +
          ∑ j, initialFirstAmplitude a L j x * partialDeriv v x j) := by
  have hΦ : ContDiff ℝ ∞ (fun p : ℝ × Euclidean n ↦ φ p.2 - p.1 * η) :=
    (hφ.comp contDiff_snd).sub (contDiff_fst.mul contDiff_const)
  have hp (x : Euclidean n) (hx : a x ≠ 0) :
      deriv (fun t ↦ φ x - t * η) 0 =
        fderiv ℝ (fun y ↦ φ y - 0 * η) x (-L x) := by
    simp only [zero_mul, sub_zero, map_neg]
    rw [← hphase x hx]
    simp
  have hd := hasDerivAt_chartAdjoint_carrier isOpen_univ hs hΦ
    (ha.comp contDiff_snd) hL.neg hv (fun _ _ ↦ Set.Subset.rfl)
    (Set.mem_univ (0 : ℝ)) hp
  have he : HasDerivAt
      (fun t : ℝ ↦ chartAdjoint (fun x ↦ φ x - t * η) a v)
      ((Complex.I * (η : ℂ)) * chartAdjoint φ a v) 0 := by
    simp_rw [chartAdjoint_phase_shift]
    convert ((((hasDerivAt_id (0 : ℝ)).mul_const η).ofReal_comp.const_mul
      Complex.I).cexp.mul_const (chartAdjoint φ a v)) using 1 <;> simp
  have h := he.unique hd
  simpa [carrierZeroAmplitude, carrierFirstAmplitude, initialZeroAmplitude,
    initialFirstAmplitude, transportCoefficient,
    partialDeriv, fderiv_neg, Finset.sum_neg_distrib] using h
end JanetCartan.ContinuumAdjoint.DerivativeKernels
