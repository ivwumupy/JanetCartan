module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.HigherRegularity.RealCommutator
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.HigherRegularity.FirstOrderAction
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.HigherRegularity.Estimates

/-!
# Higher elliptic regularity from the actual continuum representation

For `app:ch_background:prop:bg-inverse` and `app:ch_background:eq:bg-r-inverse`,
construct the differential commutators from primitive full-amplitude bounds,
justify the missing weak derivatives in H⁻¹, reconstruct the actual Fourier
Sobolev norms, and instantiate both analytic inputs of the inverse bootstrap.

The bounded H¹ action of the inverse is the permitted first-order input. Its
actual producer is `ContinuumCommutator.periodicCoerciveInverseH1`, with
compatibility `toL2_periodicCoerciveInverseH1`. The forward H¹ action is derived
here from the order-one commutator. Every order uses the same `E.inverse`.

The normal construction still owns the literal representation, primitive
amplitude budgets, self-adjointness, coercive gap, and first-order inverse
input. This connector proves their higher-order consequences; it does not
assert an unconditional construction of the normal. No commutator estimate,
regularity implication, or elliptic step estimate is an input.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
open JanetCartan.AmplitudeBound JanetCartan.Pseudodifferential
open JanetCartan.PeriodicLocalL2 JanetCartan.ContinuumRow
namespace JanetCartan.ContinuumCommutator.HigherRegularity

open PeriodicSobolevSpace

variable {n : ℕ} {κ : Type*} [Fintype κ]
local notation "Vℝ" => EuclideanSpace ℝ (Fin n)
local notation "S" => periodicSobolevScale n Vℝ

/-- The analytic inputs `hreg` and `hstep` of `ContinuumInverse.Bootstrap`, and
the resulting regularity and tame estimate for the original inverse, from
the actual normal representation and primitive matrix-amplitude budgets.

The constants are chosen before the amplitudes, the high profile `A`, and its
additional shift `b₀`. The fixed derivative reserve is `2 * (n + 1)`; the total
shift `2 * (n + 1) + b₀` is independent of the Sobolev order. All weights of the
literal real representation, including the carrier weight four, are retained.
This is the connector consumed by the continuum elliptic and inverse assembly
(`app:ch_background:eq:bg-commutator`, `app:ch_background:prop:bg-inverse`,
`app:ch_background:eq:bg-r-inverse`). -/
theorem exists_elliptic_estimates_of_matrix_representation
    (hn : 0 < n) (R : ℝ) (hR : R < 1 / 2)
    (M c : κ → ℝ) (χ : C(Torus n, ℝ)) (hχ : IsSmoothPeriodic χ)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (b : κ → Vℝ → EuclideanSpace ℝ (Fin (2 * n)) →
          Matrix (Fin n) (Fin n) ℂ)
        (hb : ∀ a, ContDiff ℝ ∞ (Function.uncurry (b a)))
        (hs : ∀ a ξ i j, SupportedInCenteredBox R (fun z ↦ b a ξ z i j))
        (A : ℕ → ℝ) (b₀ : ℕ) (_ha : ∀ s, 0 ≤ A s) (_hmono : Monotone A)
        (hM : ∀ a i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b a ξ z i j)
          (2 * (n + 1) + 1) (M a))
        (_hH : ∀ s a i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b a ξ z i j)
          (2 * (n + 1) + (s + 1)) (A (s + 1 + (2 * (n + 1) + b₀))))
        (E : PeriodicL2 n Vℝ →L[ℝ] PeriodicL2 n Vℝ)
        (_hE : E = (∑ a, c a • realOutputCompression (transferOperator
          (vectorTwoPositionL2Operator hn R (b a) (hb a) (hs a) (M a)
            (fun i j ξ js hjs ↦ hM a i j ξ js (Nat.le_succ_of_le hjs))))) +
              cutoffMultiplier (χ ^ 2))
        (Q₁ : PeriodicSobolevSpace n Vℝ 1 →L[ℝ] PeriodicSobolevSpace n Vℝ 1)
        (_hQ₁ : ∀ u, toL2 1 (Q₁ u) = E.inverse (toL2 1 u))
        (_hself : IsSelfAdjoint E) (_hgap : ∀ v, γ * ‖v‖ ^ 2 ≤ ⟪E v, v⟫),
        (∀ s v, v ∈ (S).level s → E v ∈ (S).level (s + 1) → v ∈ (S).level (s + 1)) ∧
        (∀ s v, v ∈ (S).level (s + 1) → E v ∈ (S).level (s + 1) →
          (S).gradeNorm (s + 1) v ≤ C (s + 1) *
            ((S).gradeNorm (s + 1) (E v) + (S).gradeNorm s v +
              (1 + A (s + 1 + (2 * (n + 1) + b₀))) * ‖v‖)) ∧
        (∀ s e, e ∈ (S).level s → E.inverse e ∈ (S).level s ∧
          (S).gradeNorm s (E.inverse e) ≤ ContinuumInverse.bootstrapConstant γ C s *
            ((S).gradeNorm s e + (1 + A (s + (2 * (n + 1) + b₀))) * ‖e‖)) := by
  classical
  choose D hD hcomm using fun s ↦
    RealCommutator.exists_sobolev_commutators_of_matrix_representation hn R hR s M c χ hχ
  let C := fun t ↦ ellipticStepConstant n (t - 1) γ (D (t - 1))
  refine ⟨C, fun t ↦ ellipticStepConstant_nonneg n (t - 1) hγ (hD (t - 1)), ?_⟩
  intro b hb hs A b₀ ha hmono hM hH E hE Q₁ hQ₁ hself hgap
  choose K hidentity hbound using fun s ↦
    hcomm s b hb hs (A (s + 1 + (2 * (n + 1) + b₀))) hM (hH s) E hE
  obtain ⟨E₁, hE₁⟩ := exists_firstOrderRestriction_of_commutators E (K 0) (hidentity 0)
  have hreg : ∀ s v, v ∈ (S).level s → E v ∈ (S).level (s + 1) →
      v ∈ (S).level (s + 1) :=
    fun s ↦ mem_succ_of_commutators E E₁ Q₁ hself hE₁ hQ₁ hγ hgap s (K s) (hidentity s)
  refine ⟨hreg, ?_, ?_⟩
  · intro s v hv hev
    have hA : 0 ≤ 1 + A (s + 1 + (2 * (n + 1) + b₀)) := by
      linarith [ha (s + 1 + (2 * (n + 1) + b₀))]
    have hmax : max 1 (A (s + 1 + (2 * (n + 1) + b₀))) ≤
        1 + A (s + 1 + (2 * (n + 1) + b₀)) :=
      max_le (by linarith [ha (s + 1 + (2 * (n + 1) + b₀))]) (by linarith)
    simpa only [C, Nat.add_sub_cancel] using
      gradeNorm_succ_le_of_commutators E E₁ Q₁ hself hE₁ hQ₁ hγ hgap s (K s) (hidentity s)
        (hD s) hA (fun is hlen u ↦ (hbound s is hlen u).trans
          (mul_le_mul_of_nonneg_left (add_le_add_right
            (mul_le_mul_of_nonneg_right hmax (norm_nonneg _)) _) (hD s))) v
        (antitone_periodicSobolevLevel (Nat.le_succ s) hv) hev
  · intro s e he
    exact ⟨ContinuumInverse.inverse_mem S E hγ hgap hreg s he,
      inverse_gradeNorm_le_of_commutators E E₁ Q₁ hself hE₁ hQ₁ hγ hgap K hidentity
        hD ha hmono hbound s he⟩

end JanetCartan.ContinuumCommutator.HigherRegularity
