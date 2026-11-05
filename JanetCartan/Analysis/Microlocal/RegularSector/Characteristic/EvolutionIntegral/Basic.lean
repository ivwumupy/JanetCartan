module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.Operators
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Elapsed-time phases and full amplitudes

These are the literal objects in `app:ch_regular_base:eq:fixed-time-representation`.
Spacetime uses the existing Euclidean graph coordinates, with time first. Both
physical masks and the conic Fourier multiplier remain in the full amplitude.
The bounded graph at each elapsed time is the existing `fullGraphOperator`;
this file does not assert that its defining realization hypotheses hold.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral

open FourierIntegral

variable {d q : ℕ}

/-- Spatial coordinates of a spacetime vector, in
`app:ch_regular_base:eq:fixed-time-representation`. -/
def spatialPart (x : Euclidean (d + 1)) : Euclidean d :=
  WithLp.toLp 2 (fun i ↦ x i.succ)

/-- The two-time spatial phase from `app:ch_regular_base:lem:retarded-kernel`. -/
abbrev TwoTimePhase (d : ℕ) := ℝ → ℝ → Euclidean d → Euclidean d → ℝ

/-- The original matrix symbol, before the two physical masks and Fourier
multiplier, in `app:ch_regular_base:lem:retarded-kernel`. -/
abbrev TwoTimeAmplitude (d q : ℕ) :=
  ℝ → ℝ → Euclidean d → Euclidean d → Matrix (Fin q) (Fin q) ℂ

/-- The actual elapsed-time spacetime phase `Θ_r`, with physical covectors.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
def elapsedPhase (Ψ : TwoTimePhase d) (r : ℝ)
    (x ξ : Euclidean (d + 1)) : ℝ :=
  (x 0 - r) * ξ 0 + Ψ (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)

/-- The full two-position amplitude in the fixed-time representation. A
lower-end buffer is part of the original two-time amplitude `b`; neither
physical mask is commuted through the oscillatory operator.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
def elapsedAmplitude (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ) (r : ℝ) : FullAmplitude (d + 1) q :=
  fun x z ξ ↦ (χout x * χsource z * β ξ) •
    b (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)

/-- Spacetime Hilbert space used by the existing graph realization in
`app:ch_regular_base:eq:fixed-time-representation`. -/
abbrev SpacetimeL2 (d q : ℕ) :=
  Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure (Euclidean (d + 1)))

/-- The existing full graph realization for the actual elapsed-time phase
and amplitude. Its low bound and test identification still require the
primitive graph constructor. Source: `app:ch_regular_base:lem:retarded-kernel`. -/
def elapsedGraph (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ) (r : ℝ) :
    SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q :=
  FullLowBounds.fullGraphOperator (elapsedPhase Ψ r)
    (elapsedAmplitude b χout χsource β r)

/-- The datum-wise elapsed-time integral. This definition makes no
operator-norm measurability assumption. Its bounded linear realization is
constructed after proving strong measurability and uniform graph bounds.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
def elapsedGraphIntegral (Δ : ℝ) (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ) (u : SpacetimeL2 d q) : SpacetimeL2 d q :=
  ∫ r in Icc 0 Δ, elapsedGraph Ψ b χout χsource β r u

/-- Splitting the physical Euclidean pairing into time and space, as used
in `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem inner_eq_time_add_spatial (x ξ : Euclidean (d + 1)) :
    inner ℝ x ξ = x 0 * ξ 0 + inner ℝ (spatialPart x) (spatialPart ξ) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, spatialPart]
  rw [Fin.sum_univ_succ]
  ring

/-- The zero elapsed-time phase is the diagonal phase, including its time
coordinate. Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem elapsedPhase_zero (Ψ : TwoTimePhase d)
    (hdiag : ∀ t y η, Ψ t t y η = inner ℝ y η) (x ξ : Euclidean (d + 1)) :
    elapsedPhase Ψ 0 x ξ = inner ℝ x ξ := by
  simp only [elapsedPhase, sub_zero, hdiag, inner_eq_time_add_spatial]

/-- Vanishing of the original amplitude below its lower buffer is retained
at each elapsed time. Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem elapsedAmplitude_eq_zero_of_lower_buffer (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ) (a r : ℝ)
    (hb : ∀ t s y η, s ≤ a → b t s y η = 0)
    (x z ξ : Euclidean (d + 1)) (hx : x 0 - r ≤ a) :
    elapsedAmplitude b χout χsource β r x z ξ = 0 := by
  simp only [elapsedAmplitude, hb _ _ _ _ hx, smul_zero]

/-- Both physical masks stay in the elapsed-time amplitude.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem elapsedAmplitude_eq_zero_of_mask (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ) (r : ℝ)
    (x z ξ : Euclidean (d + 1))
    (h : χout x = 0 ∨ χsource z = 0 ∨ β ξ = 0) :
    elapsedAmplitude b χout χsource β r x z ξ = 0 := by
  rcases h with h | h | h <;> simp [elapsedAmplitude, h]

/-- Reversing the integration variable gives precisely the retarded time
triangle, before any oscillatory limiting argument. Consumer: the literal
kernel identification in `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem integral_elapsed_eq_retarded {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (a t : ℝ) (f : ℝ → F) :
    (∫ r in (0 : ℝ)..t - a, f (t - r)) = ∫ s in a..t, f s := by
  simpa only [sub_sub_cancel, sub_zero] using
    intervalIntegral.integral_comp_sub_left f (a := 0) (b := t - a) t

/-- The same fixed slab length works for every output time in the slab,
because the lower-end buffer kills the excess elapsed-time interval. This
retains the full triangle and its endpoints in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem integral_fixed_slab_eq_retarded {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {a t Δ : ℝ} (hat : a ≤ t) (htΔ : t - a ≤ Δ)
    (f : ℝ → F) (hf : IntervalIntegrable (fun r ↦ f (t - r)) volume 0 Δ)
    (hzero : ∀ s ≤ a, f s = 0) :
    (∫ r in Icc 0 Δ, f (t - r)) = ∫ s in a..t, f s := by
  have hta : 0 ≤ t - a := sub_nonneg.mpr hat
  have hΔ : 0 ≤ Δ := hta.trans htΔ
  have hleft : IntervalIntegrable (fun r ↦ f (t - r)) volume 0 (t - a) := by
    apply hf.mono_set
    rw [uIcc_of_le hta, uIcc_of_le hΔ]
    exact Icc_subset_Icc le_rfl htΔ
  have hright : IntervalIntegrable (fun r ↦ f (t - r)) volume (t - a) Δ := by
    apply hf.mono_set
    rw [uIcc_of_le htΔ, uIcc_of_le hΔ]
    exact Icc_subset_Icc hta le_rfl
  have htail : (∫ r in t - a..Δ, f (t - r)) = 0 := by
    calc
      _ = ∫ _r in t - a..Δ, (0 : F) := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [uIcc_of_le htΔ] at hr
        exact hzero (t - r) (by linarith [hr.1])
      _ = 0 := intervalIntegral.integral_zero
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hΔ,
    ← intervalIntegral.integral_add_adjacent_intervals hleft hright, htail, add_zero]
  exact integral_elapsed_eq_retarded a t f

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral
