module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.HigherRegularity.RealCommutator.ComplexMatrix
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.HigherRegularity.RealCommutator.FiniteAssembly

/-!
# Higher commutators from the actual real normal representation

Construct the continuous real commutators in
`app:ch_background:eq:bg-commutator` from full two-position matrix amplitudes.
The representation is exactly the one used by `Translation.Assembly`, with
all real weights (including the carrier weight four) and the exterior `χ²`.
The common constant is chosen before the amplitudes and high budget, and the
reserve remains `2 * (n + 1)`.

The resulting family supplies the commutator inputs of
`HigherRegularity.mem_succ_of_commutators` and
`HigherRegularity.exists_top_weakDerivative_norm_le`. The normal producer still
owns its literal representation and primitive amplitude budgets; the inverse
consumer still owns first-order inverse preservation and coercivity.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
open JanetCartan.AmplitudeBound JanetCartan.Pseudodifferential
open JanetCartan.PeriodicLocalL2 JanetCartan.ContinuumRow

namespace JanetCartan.ContinuumCommutator.HigherRegularity.RealCommutator

open PeriodicSobolevSpace

variable {n : ℕ} {κ : Type*} [Fintype κ]
local notation "Vℝ" => EuclideanSpace ℝ (Fin n)

/-- The actual real vector-valued commutators of a represented continuum normal,
constructed from primitive full-amplitude bounds. The smooth weak identity and
continuous additive estimate are the exact inputs to
`HigherRegularity.mem_succ_of_commutators` and
`HigherRegularity.exists_top_weakDerivative_norm_le`.

The constant depends only on the fixed low budgets, weights, cutoff, chart and
order. The sole high budget multiplies the original L² norm, with the unchanged
reserve `2 * (n + 1)` (`app:ch_background:eq:bg-commutator`,
`app:ch_background:prop:bg-inverse`). -/
theorem exists_sobolev_commutators_of_matrix_representation
    (hn : 0 < n) (R : ℝ) (hR : R < 1 / 2) (s : ℕ)
    (M c : κ → ℝ) (χ : C(Torus n, ℝ)) (hχ : IsSmoothPeriodic χ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : κ → Vℝ → EuclideanSpace ℝ (Fin (2 * n)) →
          Matrix (Fin n) (Fin n) ℂ)
        (hb : ∀ a, ContDiff ℝ ∞ (Function.uncurry (b a)))
        (hs : ∀ a ξ i j, SupportedInCenteredBox R (fun z ↦ b a ξ z i j))
        (H : ℝ)
        (hM : ∀ a i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b a ξ z i j)
          (2 * (n + 1) + 1) (M a))
        (_hH : ∀ a i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b a ξ z i j)
          (2 * (n + 1) + (s + 1)) H)
        (E : PeriodicL2 n Vℝ →L[ℝ] PeriodicL2 n Vℝ)
        (_hE : E = (∑ a, c a • realOutputCompression (transferOperator
          (vectorTwoPositionL2Operator hn R (b a) (hb a) (hs a) (M a)
            (fun i j ξ js hjs ↦ hM a i j ξ js (Nat.le_succ_of_le hjs))))) +
              cutoffMultiplier (χ ^ 2)),
        ∃ K : (is : List (Fin n)) → is.length = s + 1 →
            PeriodicSobolevSpace n Vℝ s →L[ℝ] PeriodicL2 n Vℝ,
          (∀ (is : List (Fin n)) (hlen : is.length = s + 1)
            (f : Torus n → Vℝ) (hf : IsSmoothPeriodic f),
            HasPeriodicWeakDerivativeList is (E (toL2 s (ofSmooth s f hf)))
              (E (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f)
                (hf.coordinateDerivList is))) + K is hlen (ofSmooth s f hf))) ∧
          (∀ (is : List (Fin n)) (hlen : is.length = s + 1) u,
            ‖K is hlen u‖ ≤ C * (‖u‖ + max 1 H * ‖toL2 s u‖)) := by
  classical
  choose C hC hcomm using fun a ↦
    exists_vectorTwoPosition_sobolev_commutator_bound hn R hR s (M a)
  refine ⟨(∑ a, |c a| * C a) + cutoffCommutatorConstant χ hχ s, ?_, ?_⟩
  · exact add_nonneg (Finset.sum_nonneg fun a _ ↦ mul_nonneg (abs_nonneg _) (hC a))
      (cutoffCommutatorConstant_pos χ hχ s).le
  intro b hb hs H hM hH E hE
  choose K hidentity hbound using fun a (is : List (Fin n)) (hlen : is.length = s + 1) ↦
    hcomm a (b a) (hb a) (hs a) H (hM a) is hlen (by simpa only [hlen] using hH a)
  refine ⟨fun is hlen ↦ matrixSumCutoffCommutator s is hlen c
    (fun a ↦ K a is hlen) χ hχ, ?_, ?_⟩
  · intro is hlen f hf
    rw [hE]
    exact matrixSumCutoffCommutator_ofSmooth s is hlen _ c (fun a ↦ K a is hlen)
      (fun a ↦ hidentity a is hlen) χ hχ f hf
  · intro is hlen u
    exact norm_matrixSumCutoffCommutator_le s is hlen c C hC (fun a ↦ K a is hlen)
      H (fun a ↦ hbound a is hlen) χ hχ u

end JanetCartan.ContinuumCommutator.HigherRegularity.RealCommutator
