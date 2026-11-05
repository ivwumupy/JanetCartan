module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Translation
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Translation.Assembly
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FiniteNormal

/-!
# Translation bound for the literal image-carrier-exterior normal

The first-order connection in `app:ch_background:eq:bg-commutator` adds the
literal image normal to the full reflected carrier normals and the exterior
multiplier `(1 - ψ)²`. The reflected real carrier representation already includes
both quadratures and factor four, so its coefficient in the finite sum is one.

The consumer `jc-continuum-elliptic-bootstrap` obtains one bound and one positive
translation radius before choosing any coefficients, amplitudes, or history.
The image jets are produced by `ContinuumRow.ImageGeometry` / `HistoryImage`;
the actual carrier representation and its primitive budgets are produced by
`CarrierNormalRealization.SupportedShell` with `CanonicalConic` / `CanonicalBudgets`.
The row parent must instantiate these hypotheses on the same finite family.
No commutator estimate or full image PDO representation is an input.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
open JanetCartan.AmplitudeBound JanetCartan.Pseudodifferential
open JanetCartan.PeriodicLocalL2 JanetCartan.ContinuumRow

namespace JanetCartan.ContinuumCommutator.AugmentedFirstOrder

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- Uniform divided-translation estimate for the SAME augmented row normal
(`app:ch_background:eq:bg-commutator`, `app:ch_background:prop:bg-inverse`).
The constants precede the varying image coefficients, all three cutoffs, carrier
amplitudes and carrier operators. `hT` is the full reflected REAL carrier-normal
identity from `CarrierNormalRealization.SupportedShell`; its factor four must
not be inserted a second time. `hA` requires its first additional derivative.
Actual representation, budget and cutoff instantiation remain with the row
parent; this theorem proves the finite assembly from those primitive inputs. -/
theorem exists_uniform_augmentedNormal_translation_bound
    (hn : 0 < n) (R : ℝ) (hR : R < 1 / 2)
    (A : ι → ℝ) (hA0 : ∀ a, 0 ≤ A a)
    (C K M S Km Ks Me Ke : ℝ) (hC0 : 0 ≤ C) (hK0 : 0 ≤ K)
    (hM0 : 0 ≤ M) (hS0 : 0 ≤ S) (hKm0 : 0 ≤ Km) (hKs0 : 0 ≤ Ks)
    (hMe0 : 0 ≤ Me) (hKe0 : 0 ≤ Ke) :
    ∃ B ≥ 0, ∃ h₀ > 0, R + h₀ < 1 / 2 ∧
      ∀ (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ)),
      (∀ j, IsSmoothPeriodic (c j)) →
      (∀ j x, |c j x| ≤ C) →
      (∀ j x, ‖iteratedFDeriv ℝ 1 (periodicLift (c j)) x‖ ≤ K) →
      ∀ (χmeas χsrc ψ : C(Torus n, ℝ)),
      IsSmoothPeriodic χmeas → IsSmoothPeriodic χsrc → IsSmoothPeriodic (1 - ψ : C(Torus n, ℝ)) →
      (∀ x, ‖χmeas x‖ ≤ M) → (∀ x, ‖χsrc x‖ ≤ S) →
      (∀ x, ‖iteratedFDeriv ℝ 1 (periodicLift χmeas) x‖ ≤ Km) →
      (∀ x, ‖iteratedFDeriv ℝ 1 (periodicLift χsrc) x‖ ≤ Ks) →
      (∀ x, ‖(1 - ψ) x‖ ≤ Me) →
      (∀ x, ‖iteratedFDeriv ℝ 1 (periodicLift (1 - ψ : C(Torus n, ℝ))) x‖ ≤ Ke) →
      ∀ (b : ι → Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
        (hb : ∀ a, ContDiff ℝ ∞ (Function.uncurry (b a)))
        (hs : ∀ a ξ r s, SupportedInCenteredBox R (fun z ↦ b a ξ z r s))
        (hA : ∀ a r s, HasAmplitudeDerivativeBound (fun ξ z ↦ b a ξ z r s)
          (2 * (n + 1) + 1) (A a))
        (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n),
      (∀ a, (carrierChannel (T a)).comp (carrierChannel (T a)).adjoint =
        realOutputCompression (transferOperator
          (vectorTwoPositionL2Operator hn R (b a) (hb a) (hs a) (A a)
            (fun r s ξ is his ↦ hA a r s ξ is (Nat.le_succ_of_le his))))) →
      ∀ (i : Fin n) (h : ℝ), 0 < |h| → |h| ≤ h₀ →
        ‖periodicConjugationDifference
          (augmentedNormal (imageChannel c χmeas χsrc) T ψ) i h‖ ≤ B := by
  classical
  obtain ⟨Bi, hBi, himage⟩ :=
    ImageChannelTranslation.exists_uniform_imageNormal_translation_bound
      n C K M S Km Ks hC0 hK0 hM0 hS0 hKm0 hKs0
  let h₀ : ℝ := (1 / 2 - R) / 2
  have hh₀ : 0 < h₀ := by dsimp [h₀]; linarith
  have hbuffer : R + h₀ < 1 / 2 := by dsimp [h₀]; linarith
  let Bc := (∑ a, (n : ℝ) ^ 2 *
    (fixedBoxAmplitudeConstant n (R + h₀) * (2 * A a))) + 2 * Me * Ke
  have hBc : 0 ≤ Bc := by
    dsimp [Bc]
    have hf := fixedBoxAmplitudeConstant_nonneg n (R + h₀)
    exact add_nonneg (Finset.sum_nonneg fun a _ ↦
      mul_nonneg (sq_nonneg _) (mul_nonneg hf (mul_nonneg (by norm_num) (hA0 a))))
      (by positivity)
  refine ⟨Bi + Bc, add_nonneg hBi hBc, h₀, hh₀, hbuffer, ?_⟩
  intro c hc hC hK χmeas χsrc ψ hm hsrc he hM hS hKm hKs hMe hKe b hb hs hA T hT
    i h hh hsmall
  have he' : ∀ x, ‖fderiv ℝ (periodicLift (1 - ψ : C(Torus n, ℝ))) x
      (EuclideanSpace.single i 1)‖ ≤ Ke := by
    intro x
    have hj := hKe x
    rw [norm_iteratedFDeriv_one] at hj
    simpa [EuclideanSpace.single, PiLp.norm_single] using
      ((fderiv ℝ (periodicLift (1 - ψ : C(Torus n, ℝ))) x).le_opNorm
        (EuclideanSpace.single i 1)).trans
          (mul_le_mul_of_nonneg_right hj (norm_nonneg _))
  have hcarrier := norm_periodicConjugationDifference_matrixSum_exterior_le
    hn R h₀ b hb hs A hA hbuffer (fun _ ↦ 1) (1 - ψ)
    (he.2.differentiable (by simp)) i Me Ke hMe0 hKe0 hMe he' h (abs_pos.mp hh) hsmall
  simp only [one_smul, abs_one, one_mul] at hcarrier
  rw [augmentedNormal_eq_sum, add_assoc]
  simp_rw [hT]
  rw [periodicConjugationDifference_add]
  exact (norm_add_le _ _).trans (add_le_add
    (himage c hc hC hK χmeas χsrc hm hsrc hM hS hKm hKs i h) hcarrier)

end JanetCartan.ContinuumCommutator.AugmentedFirstOrder
