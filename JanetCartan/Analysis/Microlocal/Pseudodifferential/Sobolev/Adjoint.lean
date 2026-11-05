module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Adjoint.CompactKernel

/-!
# Literal adjoint amplitudes

Physical reversal and conjugation realize the actual Hilbert adjoint for
`app:ch_regular_base:thm:actual-calculus` (2)–(3), retaining the exact support,
derivative budgets, masks, and `2π` convention. The compact-frequency kernel
identity passes to the full operator through strong limits of both amplitudes.
Primitive source bounds identify the resulting source-first integral on compact
smooth tests.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ContDiff Topology
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential

variable {d : ℕ} (hd : 0 < d) (R : ℝ)
  (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hb : ContDiff ℝ ∞ (Function.uncurry b))
  (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
  (hbound : HasAmplitudeDerivativeBound b (2 * (d + 1)) A)

/-- Frequency exhaustion converges strongly to the full bounded realization
(`app:ch_regular_base:thm:actual-calculus`). -/
theorem tendsto_twoPositionCompactFrequencyL2Operator
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    Tendsto (fun ρ : ℝ ↦ twoPositionCompactFrequencyL2Operator hd R b hb hs A hbound ρ f)
      atTop (𝓝 (twoPositionL2Operator hd R b hb hs A hbound f)) :=
  tendsto_boxCompactFrequencyAmplitudeOperator ..

/-- The literal reversed conjugate amplitude realizes the actual Hilbert
adjoint (`app:ch_regular_base:thm:actual-calculus` (2)–(3)). The same fixed
physical support and derivative budget suffice. The proof takes limits in the
compact-frequency adjoint identity, using strong convergence on both sides. -/
theorem twoPositionL2Operator_adjoint :
    (twoPositionL2Operator hd R b hb hs A hbound).adjoint =
      twoPositionL2Operator hd R (adjointAmplitude b)
        (contDiff_adjointAmplitude hb) (supportedInCenteredBox_adjointAmplitude hs) A
        (hasAmplitudeDerivativeBound_adjointAmplitude
          (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) hbound) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  have hleft := (tendsto_twoPositionCompactFrequencyL2Operator hd R (adjointAmplitude b)
    (contDiff_adjointAmplitude hb) (supportedInCenteredBox_adjointAmplitude hs) A
    (hasAmplitudeDerivativeBound_adjointAmplitude
      (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) hbound) f).inner
        (𝕜 := ℂ) (tendsto_const_nhds (x := g))
  have hright := (tendsto_const_nhds (x := f)).inner (𝕜 := ℂ)
    (tendsto_twoPositionCompactFrequencyL2Operator hd R b hb hs A hbound g)
  apply tendsto_nhds_unique hleft
  convert hright using 1
  funext ρ
  rw [← twoPositionCompactFrequencyL2Operator_adjoint hd R b hb hs A hbound,
    ContinuousLinearMap.adjoint_inner_left]

/-- The compact-frequency adjoints also converge strongly on every L² datum.
This follows from reversal and frequency exhaustion for the reversed amplitude
(`app:ch_regular_base:thm:actual-calculus`). -/
theorem tendsto_twoPositionCompactFrequencyL2Operator_adjoint
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    Tendsto (fun ρ : ℝ ↦
      (twoPositionCompactFrequencyL2Operator hd R b hb hs A hbound ρ).adjoint f)
      atTop (𝓝 ((twoPositionL2Operator hd R b hb hs A hbound).adjoint f)) := by
  simp only [twoPositionCompactFrequencyL2Operator_adjoint, twoPositionL2Operator_adjoint]
  exact tendsto_twoPositionCompactFrequencyL2Operator ..

/-- The actual Hilbert adjoint equals the literal source-first integral when
the reversed source transform is integrable. The amplitude is exactly
`c†(x,y,ξ) = conj(c(y,x,ξ))`, including every mask
(`app:ch_regular_base:thm:actual-calculus` (2)–(3)). -/
theorem twoPositionL2Operator_adjoint_ae_fullAmplitudeOperator
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2)
    (hi : ∀ᵐ x, Integrable (sourceAmplitudeTransform
      (fun x y ξ ↦ star (b ξ (pairedPosition y x))) f x)) :
    (twoPositionL2Operator hd R b hb hs A hbound).adjoint f =ᵐ[volume]
      fullAmplitudeOperator (fun x y ξ ↦ star (b ξ (pairedPosition y x))) f := by
  rw [twoPositionL2Operator_adjoint]
  simpa only [adjointAmplitude_pairedPosition] using
    twoPositionL2Operator_ae_fullAmplitudeOperator hd R (adjointAmplitude b)
      (contDiff_adjointAmplitude hb) (supportedInCenteredBox_adjointAmplitude hs) A
      (hasAmplitudeDerivativeBound_adjointAmplitude
        (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) hbound) f
      (by simpa only [adjointAmplitude_pairedPosition] using hi)

/-- The literal adjoint formula is independent of the L² representative of
the datum (`app:ch_regular_base:thm:actual-calculus`). -/
theorem twoPositionL2Operator_adjoint_toLp_ae_fullAmplitudeOperator
    (u : EuclideanSpace ℝ (Fin d) → ℂ) (hu : MemLp u 2)
    (hi : ∀ᵐ x, Integrable (sourceAmplitudeTransform
      (fun x y ξ ↦ star (b ξ (pairedPosition y x))) u x)) :
    (twoPositionL2Operator hd R b hb hs A hbound).adjoint (hu.toLp u) =ᵐ[volume]
      fullAmplitudeOperator (fun x y ξ ↦ star (b ξ (pairedPosition y x))) u := by
  rw [twoPositionL2Operator_adjoint]
  simpa only [adjointAmplitude_pairedPosition] using
    twoPositionL2Operator_toLp_ae_fullAmplitudeOperator hd R (adjointAmplitude b)
      (contDiff_adjointAmplitude hb) (supportedInCenteredBox_adjointAmplitude hs) A
      (hasAmplitudeDerivativeBound_adjointAmplitude
        (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) hbound) u hu
      (by simpa only [adjointAmplitude_pairedPosition] using hi)

/-- Primitive bounds on derivatives in the original target position imply
the source-first literal adjoint formula on compact smooth tests. The reserve
is `dim + 1`; all source integrability and realization premises are discharged
(`app:ch_regular_base:thm:actual-calculus` (2)–(3)). -/
theorem twoPositionL2Operator_adjoint_toLp_ae_fullAmplitudeOperator_of_sourceBounds
    (u : EuclideanSpace ℝ (Fin d) → ℂ) (hu : MemLp u 2)
    (huc : ContDiff ℝ (d + 1) u) (hus : HasCompactSupport u)
    (M : EuclideanSpace ℝ (Fin d) → ℕ → ℝ)
    (hM : ∀ x j, j ≤ d + 1 → ∀ y ξ,
      ‖iteratedFDeriv ℝ j (fun z ↦ b ξ (pairedPosition z x)) y‖ ≤ M x j) :
    (twoPositionL2Operator hd R b hb hs A hbound).adjoint (hu.toLp u) =ᵐ[volume]
      fullAmplitudeOperator (fun x y ξ ↦ star (b ξ (pairedPosition y x))) u := by
  rw [twoPositionL2Operator_adjoint]
  have hsource : ∀ x j, j ≤ d + 1 → ∀ y ξ,
      ‖iteratedFDeriv ℝ j (fun z ↦ adjointAmplitude b ξ (pairedPosition x z)) y‖ ≤
        M x j := by
    intro x j hj y ξ
    rw [norm_iteratedFDeriv_adjointAmplitude_source]
    exact hM x j hj y ξ
  simpa only [adjointAmplitude_pairedPosition] using
    twoPositionL2Operator_toLp_ae_fullAmplitudeOperator_of_sourceBounds hd R (adjointAmplitude b)
      (contDiff_adjointAmplitude hb) (supportedInCenteredBox_adjointAmplitude hs) A
      (hasAmplitudeDerivativeBound_adjointAmplitude
        (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) hbound) u hu huc hus M hsource

include hd hb hs hbound in
/-- The literal source-first adjoint has the same low L² constant. Primitive
source bounds ensure convergence on compact smooth tests; the Hilbert adjoint
identity supplies the estimate (`app:ch_regular_base:eq:fio-input`, index zero). -/
theorem fullAmplitudeOperator_adjoint_l2_bound_of_sourceBounds
    (u : EuclideanSpace ℝ (Fin d) → ℂ)
    (huc : ContDiff ℝ (d + 1) u) (hus : HasCompactSupport u)
    (M : EuclideanSpace ℝ (Fin d) → ℕ → ℝ)
    (hM : ∀ x j, j ≤ d + 1 → ∀ y ξ,
      ‖iteratedFDeriv ℝ j (fun z ↦ b ξ (pairedPosition z x)) y‖ ≤ M x j) :
    MemLp (fullAmplitudeOperator (fun x y ξ ↦ star (b ξ (pairedPosition y x))) u) 2 ∧
      (eLpNorm (fullAmplitudeOperator (fun x y ξ ↦ star (b ξ (pairedPosition y x))) u)
        2 volume).toReal ≤
      (fixedBoxAmplitudeConstant d R * A) * (eLpNorm u 2 volume).toReal := by
  have hu : MemLp u 2 := huc.continuous.memLp_of_hasCompactSupport hus
  have heq := twoPositionL2Operator_adjoint_toLp_ae_fullAmplitudeOperator_of_sourceBounds
    hd R b hb hs A hbound u hu huc hus M hM
  refine ⟨(Lp.memLp _).ae_eq heq, ?_⟩
  rw [← eLpNorm_congr_ae heq, ← Lp.norm_def]
  simpa only [Lp.norm_toLp] using
    norm_twoPositionL2Operator_adjoint_apply_le hd R b hb hs A hbound (hu.toLp u)

end JanetCartan.Pseudodifferential
