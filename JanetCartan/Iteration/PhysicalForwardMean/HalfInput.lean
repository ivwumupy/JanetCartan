module

public import JanetCartan.Iteration.PhysicalForwardMean.ShellMoments
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exact half-frequency input on the original single-shell measure

For the individual mean-field estimate (`app:ch_mean_pairs:eq:block-fields`),
scalar36 bounds the BARE tester. The original raw forward operator is NOT bare:
its original halfweight is moved exactly to the input, on the SAME native
refined-shell measure. Every weighted moment is exactly k+1/2, never replaced
by a cutoff-power bound. Membership uses the original finite annuli only.
-/

@[expose] public noncomputable section
open Set MeasureTheory
namespace JanetCartan.PhysicalForwardMean
open PhysicalSamplingShells RawInputRealization RawInputPartition

variable {n : ℕ} {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
local notation "X" => ι × Euclidean (n - 1)

/-- The original halfweight times an arbitrary original native L² input still
belongs to L². This is membership, NOT a frequency-ceiling norm estimate. -/
theorem memLp_radialHalfInput_annularShell
    (radius : ι → ℝ) (v : Lp ℂ 2 (annularShellMeasure (n := n) radius)) :
    MemLp (fun u : X ↦ (Real.sqrt ‖u.2‖ : ℂ) * v u) 2 (annularShellMeasure radius) := by
  have hm := (Lp.memLp v).norm.add (memLp_radialMoment_annularShell radius v 1).norm
  apply hm.mono'
    (((Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_norm)).measurable.comp
      measurable_snd).aestronglyMeasurable.mul (Lp.aestronglyMeasurable v))
  apply Filter.Eventually.of_forall
  intro u
  have hs : Real.sqrt ‖u.2‖ ≤ 1 + ‖u.2‖ := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg ‖u.2‖, norm_nonneg u.2]
  change ‖(Real.sqrt ‖u.2‖ : ℂ) * v u‖ ≤ ‖v u‖ + ‖(‖u.2‖ : ℂ)^1 * v u‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    pow_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  calc
    Real.sqrt ‖u.2‖ * ‖v u‖ ≤ (1 + ‖u.2‖) * ‖v u‖ :=
      mul_le_mul_of_nonneg_right hs (norm_nonneg (v u))
    _ = ‖v u‖ + ‖u.2‖ * ‖v u‖ := by ring

/-- The original half-frequency datum, without changing the native source
measure, its annular restrictions or either refined copy of a band. -/
def radialHalfInput (radius : ι → ℝ)
    (v : Lp ℂ 2 (annularShellMeasure (n := n) radius)) :
    Lp ℂ 2 (annularShellMeasure (n := n) radius) :=
  (memLp_radialHalfInput_annularShell radius v).toLp (fun u ↦ (Real.sqrt ‖u.2‖ : ℂ) * v u)

/-- The actual native L² half datum has precisely the halfweighted input
representative; no equality of arbitrary L² representatives is asserted. -/
theorem radialHalfInput_coe_ae (radius : ι → ℝ)
    (v : Lp ℂ 2 (annularShellMeasure (n := n) radius)) :
    radialHalfInput radius v =ᵐ[annularShellMeasure radius]
      fun u : X ↦ (Real.sqrt ‖u.2‖ : ℂ) * v u :=
  MemLp.coeFn_toLp (memLp_radialHalfInput_annularShell radius v)

/-- Exact k+1/2 moment identity, including zero frequency. -/
theorem radial_pow_mul_sqrt {d : ℕ} (η : Euclidean d) (k : ℕ) :
    (‖η‖ : ℂ)^k * (Real.sqrt ‖η‖ : ℂ) = ((‖η‖ ^ ((k : ℝ) + 1 / 2) : ℝ) : ℂ) := by
  rw [Real.rpow_add_of_nonneg (norm_nonneg η) (Nat.cast_nonneg k) (by norm_num),
    Real.rpow_natCast, ← Real.sqrt_eq_rpow, Complex.ofReal_mul, Complex.ofReal_pow]

/-- Every halfweighted physical input moment on the original finite shell
measure is genuinely L², with no regularity premise on the input. -/
theorem memLp_radialHalfMoment_annularShell (radius : ι → ℝ)
    (v : Lp ℂ 2 (annularShellMeasure (n := n) radius)) (k : ℕ) :
    MemLp (fun u : X ↦ ((‖u.2‖ ^ ((k : ℝ) + 1 / 2) : ℝ) : ℂ) * v u) 2
      (annularShellMeasure radius) := by
  have heq : (fun u : X ↦ (‖u.2‖ : ℂ)^k * radialHalfInput radius v u) =ᵐ[annularShellMeasure radius]
      fun u : X ↦ ((‖u.2‖ ^ ((k : ℝ) + 1 / 2) : ℝ) : ℂ) * v u := by
    filter_upwards [radialHalfInput_coe_ae radius v] with u hu
    rw [hu, ← mul_assoc, radial_pow_mul_sqrt]
  exact (memLp_congr_ae heq).mp (memLp_radialMoment_annularShell radius (radialHalfInput radius v) k)

/-- The input moment norm in the bare-tester estimate is EXACTLY the original
k+1/2 moment, not a k moment with a hidden K^(1/2) constant. -/
theorem eLpNorm_radialHalfInput_moment (radius : ι → ℝ)
    (v : Lp ℂ 2 (annularShellMeasure (n := n) radius)) (k : ℕ) :
    eLpNorm (fun u : X ↦ (‖u.2‖ : ℂ)^k * radialHalfInput radius v u) 2
        (annularShellMeasure radius) =
      eLpNorm (fun u : X ↦ ((‖u.2‖ ^ ((k : ℝ) + 1 / 2) : ℝ) : ℂ) * v u) 2
        (annularShellMeasure radius) := by
  apply eLpNorm_congr_ae
  filter_upwards [radialHalfInput_coe_ae radius v] with u hu
  rw [hu, ← mul_assoc, radial_pow_mul_sqrt]

end JanetCartan.PhysicalForwardMean
