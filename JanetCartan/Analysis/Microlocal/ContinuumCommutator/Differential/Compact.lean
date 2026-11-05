module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Bounds

/-!
# Compact-test commutator representatives

The actual scalar operator and its literal Hilbert adjoint satisfy
`app:ch_background:eq:bg-commutator` on compact smooth data. These are the
interfaces for extension to H^(s-1), not an assumption about such an extension.
-/

@[expose] public noncomputable section
open MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- `app:ch_background:eq:bg-commutator`: the distributional commutator of
the actual operator has an L² representative with the additive bound. The low
primitive budget defines the operator, and the high budget enters only the
coefficient of the input L² norm. No commutator premise is assumed. -/
theorem exists_twoPositionL2Operator_compact_commutator_bound
    (hd : 0 < d) (R : ℝ) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
        (hb : ContDiff ℝ ∞ (Function.uncurry b))
        (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (H : ℝ)
        (hM : HasAmplitudeDerivativeBound b (2 * (d + 1) + 1) M)
        (is : List (Fin d)) (_hlen : is.length = n + 1)
        (_hH : HasAmplitudeDerivativeBound b (2 * (d + 1) + is.length) H)
        (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u),
        let f : L² := (hu.continuous.memLp_of_hasCompactSupport hus).toLp u
        let df : L² :=
          ((contDiff_euclideanCoordinateDerivList hu is).continuous.memLp_of_hasCompactSupport
            (hasCompactSupport_euclideanCoordinateDerivList hus is)).toLp
              (euclideanCoordinateDerivList is u)
        let T := twoPositionL2Operator hd R b hb hs M
          (amplitudeDerivativeBound_of_le hM (Nat.le_succ _))
        ∃ w : L²,
          orderedTransferAction (fun i => lineDerivOp (EuclideanSpace.single i 1 : E)) is
            (T f : 𝓢'(E, ℂ)) - (T df : 𝓢'(E, ℂ)) = (w : 𝓢'(E, ℂ)) ∧
          ‖w‖ ≤ C * (fourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖) := by
  obtain ⟨C, hC, he⟩ := exists_differentialCommutatorCompactL2_tame_constant hd R n M
  refine ⟨C, hC, ?_⟩
  intro b hb hs H hM is hlen hH u hu hus
  refine ⟨differentialCommutatorCompactL2 hd R b hb hs H is hH u hu hus, ?_,
    he b hb hs H hM is hlen hH u hu hus⟩
  exact twoPositionL2Operator_differential_commutator hd R b hb hs H is hH u hu hus

/-- `app:ch_background:eq:bg-commutator` for the literal Hilbert adjoint.
The adjoint is realized by reversing the two positions and conjugating the
complete amplitude, so its primitive bounds follow from the original ones.
The constant and derivative reserve are unchanged. -/
theorem exists_twoPositionL2Operator_adjoint_compact_commutator_bound
    (hd : 0 < d) (R : ℝ) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
        (hb : ContDiff ℝ ∞ (Function.uncurry b))
        (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (H : ℝ)
        (hM : HasAmplitudeDerivativeBound b (2 * (d + 1) + 1) M)
        (is : List (Fin d)) (_hlen : is.length = n + 1)
        (_hH : HasAmplitudeDerivativeBound b (2 * (d + 1) + is.length) H)
        (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u),
        let f : L² := (hu.continuous.memLp_of_hasCompactSupport hus).toLp u
        let df : L² :=
          ((contDiff_euclideanCoordinateDerivList hu is).continuous.memLp_of_hasCompactSupport
            (hasCompactSupport_euclideanCoordinateDerivList hus is)).toLp
              (euclideanCoordinateDerivList is u)
        let T := (twoPositionL2Operator hd R b hb hs M
          (amplitudeDerivativeBound_of_le hM (Nat.le_succ _))).adjoint
        ∃ w : L²,
          orderedTransferAction (fun i => lineDerivOp (EuclideanSpace.single i 1 : E)) is
            (T f : 𝓢'(E, ℂ)) - (T df : 𝓢'(E, ℂ)) = (w : 𝓢'(E, ℂ)) ∧
          ‖w‖ ≤ C * (fourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖) := by
  obtain ⟨C, hC, he⟩ := exists_twoPositionL2Operator_compact_commutator_bound hd R n M
  refine ⟨C, hC, ?_⟩
  intro b hb hs H hM is hlen hH u hu hus
  dsimp only
  rw [twoPositionL2Operator_adjoint]
  exact he (adjointAmplitude b) (contDiff_adjointAmplitude hb)
    (supportedInCenteredBox_adjointAmplitude hs) H
    (hasAmplitudeDerivativeBound_adjointAmplitude
      (fun _ => hb.comp (contDiff_const.prodMk contDiff_id)) hM) is hlen
    (hasAmplitudeDerivativeBound_adjointAmplitude
      (fun _ => hb.comp (contDiff_const.prodMk contDiff_id)) hH) u hu hus

end JanetCartan.Pseudodifferential
