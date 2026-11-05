module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.Basic

/-!
# Radial continuation of the characteristic amplitudes

The leading matrix has order zero, and the correction and its full physical
residual have order minus one. Continue their values from the SAME fixed
section as `ConicPhase.phase`, retaining both times and the physical position.
These formulas are used by the retarded symbol budgets and the supported
physical cancellation in `app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:eq:energy-complete-residual` of `paper-v2.tex`.
No smoothness at the spatial zero covector is asserted.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.RegularSector.Characteristic.ConicAmplitude

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The continuation of an amplitude of order `-o` from the fixed phase
section. The direct construction uses `o=0` for `W₀` and `o=1` for `W₁,PW₁`
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def extend (ℓ : E →L[ℝ] ℝ) (o : ℕ) (f : TwoTimePoint E → F)
    (q : TwoTimePoint E) : F :=
  (ℓ q.2.2.2)⁻¹ ^ o • f (ConicPhase.normalize ℓ q)

/-- Exact radial order of the continued amplitude, before taking any jets
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem extend_smul (ℓ : E →L[ℝ] ℝ) (o : ℕ) (f : TwoTimePoint E → F)
    (q : TwoTimePoint E) {a : ℝ} (ha : a ≠ 0) :
    extend ℓ o f (q.1, (q.2.1, (q.2.2.1, a • q.2.2.2))) =
      a⁻¹ ^ o • extend ℓ o f q := by
  simp only [extend, ConicPhase.normalize_smul ℓ q ha, map_smul,
    smul_eq_mul, mul_inv, mul_pow, smul_smul]

/-- The extension keeps the literal amplitude on its fixed section
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem extend_of_eq_one (ℓ : E →L[ℝ] ℝ) (o : ℕ) (f : TwoTimePoint E → F)
    {q : TwoTimePoint E} (hq : ℓ q.2.2.2 = 1) : extend ℓ o f q = f q := by
  simp [extend, ConicPhase.normalize_of_eq_one ℓ hq, hq]

/-- Smoothness is proved on the same positive conic chart as the phase,
from local amplitude smoothness alone (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem contDiffOn_extend (ℓ : E →L[ℝ] ℝ) (o : ℕ)
    {U : Set (TwoTimePoint E)} (hU : IsOpen U)
    {f : TwoTimePoint E → F} (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (extend ℓ o f) (ConicPhase.domain ℓ U) := by
  intro q hq
  exact ((((ℓ.contDiff.contDiffAt.comp q contDiffAt_snd.snd.snd).inv hq.1.ne').pow o).smul
    ((hf.contDiffAt (hU.mem_nhds hq.2)).comp q
      (ConicPhase.contDiffAt_normalize ℓ hq.1.ne'))).contDiffWithinAt

/-- The continuation vanishes exactly when its original section amplitude
vanishes. This retains the original transported support; it introduces no
new source mask (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem extend_eq_zero_iff (ℓ : E →L[ℝ] ℝ) (o : ℕ) (f : TwoTimePoint E → F)
    {q : TwoTimePoint E} (hq : ℓ q.2.2.2 ≠ 0) :
    extend ℓ o f q = 0 ↔ f (ConicPhase.normalize ℓ q) = 0 := by
  simp only [extend, smul_eq_zero, inv_eq_zero, pow_eq_zero_iff', hq, false_and, false_or]

/-- The supported portion of the conic amplitude is exactly the radial
continuation of the local support (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem support_extend_inter_domain (ℓ : E →L[ℝ] ℝ) (o : ℕ)
    (f : TwoTimePoint E → F) (U : Set (TwoTimePoint E)) :
    Function.support (extend ℓ o f) ∩ ConicPhase.domain ℓ U =
      (ConicPhase.normalize ℓ ⁻¹' Function.support f) ∩ ConicPhase.domain ℓ U := by
  ext q
  by_cases hq : q ∈ ConicPhase.domain ℓ U
  · simp only [mem_inter_iff, hq, and_true, mem_preimage, Function.mem_support]
    exact not_congr (extend_eq_zero_iff ℓ o f hq.1.ne')
  · simp [hq]

/-- Local vanishing at the normalized point gives local vanishing of the
actual conic amplitude. This transfers the transported source-support
margin to the conic chart (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem extend_eventuallyEq_zero (ℓ : E →L[ℝ] ℝ) (o : ℕ)
    {f : TwoTimePoint E → F} {q : TwoTimePoint E} (hq : ℓ q.2.2.2 ≠ 0)
    (hf : f =ᶠ[𝓝 (ConicPhase.normalize ℓ q)] 0) :
    extend ℓ o f =ᶠ[𝓝 q] 0 := by
  filter_upwards [hf.comp_tendsto (ConicPhase.contDiffAt_normalize ℓ hq).continuousAt]
    with p hp
  simp only [Function.comp_apply, Pi.zero_apply] at hp
  simp only [extend, hp, smul_zero, Pi.zero_apply]

/-- Every joint conic-amplitude derivative vanishes off the original
transported support margin; no derivative support condition is assumed
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem iteratedFDeriv_extend_eq_zero (ℓ : E →L[ℝ] ℝ) (o : ℕ)
    {f : TwoTimePoint E → F} {q : TwoTimePoint E} (hq : ℓ q.2.2.2 ≠ 0)
    (hf : f =ᶠ[𝓝 (ConicPhase.normalize ℓ q)] 0) (m : ℕ) :
    iteratedFDeriv ℝ m (extend ℓ o f) q = 0 := by
  simpa using ((extend_eventuallyEq_zero ℓ o hq hf).iteratedFDeriv ℝ m).eq_of_nhds

end JanetCartan.RegularSector.Characteristic.ConicAmplitude
