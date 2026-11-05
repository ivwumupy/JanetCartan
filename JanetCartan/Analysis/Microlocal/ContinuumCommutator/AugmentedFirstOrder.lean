module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.AugmentedFirstOrder.Translation
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.FirstOrderRegularity

/-!
# H¹ restriction of the same augmented continuum inverse

For `app:ch_background:prop:bg-inverse`, combine the image, reflected carrier
and literal exterior translation estimates and apply the existing coercive
difference-quotient theorem. The output is a bounded H¹ restriction of the
SAME `augmentedNormal (imageChannel c χmeas χsrc) T ψ |>.inverse`, with its
compatibility identity, H¹ membership implications and additive H¹/L² bound.
Self-adjointness follows from the literal augmented row and its Hilbert adjoint.

This is the first-order input for `HigherRegularity` and the concrete consumer
`jc-continuum-elliptic-bootstrap`. The following actual inputs remain with the
parent construction:

* `ImageGeometry` / `HistoryImage` supplies the image coefficient jets and the
  fixed cutoff construction supplies the value/first-jet bounds.
* `CanonicalConic` / `CanonicalBudgets` and
  `CarrierNormalRealization.SupportedShell` supply the full reflected real
  carrier-normal identities and their supported amplitude budgets, including
  the first additional derivative, for this same finite family.
* `jc-continuum-normal` supplies a positive coercive gap for this exact total
  normal. The row parent must instantiate the identities and budgets on its
  actual history before applying this result.

No image PDO remainder representation, commutator estimate, inverse regularity
or elliptic estimate is assumed. This conditional connector does not assert
that those geometric and coercivity inputs have been constructed.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
open JanetCartan.AmplitudeBound JanetCartan.Pseudodifferential
open JanetCartan.PeriodicLocalL2 JanetCartan.ContinuumRow

namespace JanetCartan.ContinuumCommutator.AugmentedFirstOrder

open PeriodicSobolevSpace

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The first-order input to the generic `HigherRegularity` consumer, constructed
for the actual image-carrier-exterior normal from primitive data
(`app:ch_background:eq:bg-commutator`, `app:ch_background:prop:bg-inverse`,
`app:ch_background:eq:bg-r-inverse` at order one).

One translation constant `B` and one radius `h₀` are chosen before all varying
coefficient arrays, cutoffs, carrier amplitudes, operators and histories, with
the common buffer `R + h₀ < 1 / 2`. The real carrier representation `hT` already
contains factor four; the exterior remains `(1 - ψ)²`. The only additional input
to the inverse construction is the positive coercive gap for this SAME normal.
The output `Q₁` is `periodicCoerciveInverseH1`, so forgetting H¹ recovers exactly
`E.inverse`. The final additive estimate separates the H¹ norm of the datum from
its L² norm. The module documentation names all actual input producers and the
parent's remaining instantiation obligations. -/
theorem exists_uniform_augmentedNormal_firstOrderInverse
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
      let E := augmentedNormal (imageChannel c χmeas χsrc) T ψ
      IsSelfAdjoint E ∧
      (∀ (i : Fin n) (h : ℝ), 0 < |h| → |h| ≤ h₀ →
        ‖periodicConjugationDifference E i h‖ ≤ B) ∧
      ∀ (γ : ℝ), 0 < γ → (∀ v, γ * ‖v‖ ^ 2 ≤ ⟪E v, v⟫) →
        (∀ v, E v ∈ periodicSobolevLevel n (Euclidean n) 1 →
          v ∈ periodicSobolevLevel n (Euclidean n) 1) ∧
        (∀ e, e ∈ periodicSobolevLevel n (Euclidean n) 1 →
          E.inverse e ∈ periodicSobolevLevel n (Euclidean n) 1) ∧
        ∃ Q₁ : PeriodicSobolevSpace n (Euclidean n) 1 →L[ℝ]
            PeriodicSobolevSpace n (Euclidean n) 1,
          (∀ u, toL2 1 (Q₁ u) = E.inverse (toL2 1 u)) ∧
          (∀ u, ‖Q₁ u‖ ≤ Real.sqrt n * γ⁻¹ * ‖u‖ +
            (1 + Real.sqrt n * (γ⁻¹ * B + 2 * h₀⁻¹)) * γ⁻¹ * ‖toL2 1 u‖) ∧
          ‖Q₁‖ ≤ Real.sqrt n * γ⁻¹ +
            (1 + Real.sqrt n * (γ⁻¹ * B + 2 * h₀⁻¹)) * γ⁻¹ := by
  obtain ⟨B, hB, h₀, hh₀, hbuffer, hbound⟩ :=
    exists_uniform_augmentedNormal_translation_bound hn R hR A hA0
      C K M S Km Ks Me Ke hC0 hK0 hM0 hS0 hKm0 hKs0 hMe0 hKe0
  refine ⟨B, hB, h₀, hh₀, hbuffer, ?_⟩
  intro c hc hC hK χmeas χsrc ψ hm hsrc he hM hS hKm hKs hMe hKe b hb hs hA T hT
  let E := augmentedNormal (imageChannel c χmeas χsrc) T ψ
  have htranslation : ∀ (i : Fin n) (h : ℝ), 0 < |h| → |h| ≤ h₀ →
      ‖periodicConjugationDifference E i h‖ ≤ B :=
    hbound c hc hC hK χmeas χsrc ψ hm hsrc he hM hS hKm hKs hMe hKe b hb hs hA T hT
  refine ⟨?_, htranslation, ?_⟩
  · exact CoerciveInverse.normalOperator_isSelfAdjoint
      (augmentedRow (imageChannel c χmeas χsrc) T ψ)
  intro γ hγ hgap
  refine ⟨mem_periodicSobolevLevel_one_of_coercive E hγ hgap hh₀ htranslation,
    inverse_mem_periodicSobolevLevel_one_of_coercive E hγ hgap hh₀ htranslation,
    periodicCoerciveInverseH1 E hγ hgap hh₀ htranslation,
    toL2_periodicCoerciveInverseH1 E hγ hgap hh₀ htranslation, ?_, ?_⟩
  · intro u
    have hbnd := norm_inverse_periodicSobolevSpace_one_le_of_coercive
      E hγ hgap hh₀ htranslation (toL2 1 u) (toL2_mem 1 u)
    change ‖ofL2 1 (E.inverse (toL2 1 u)) _‖ ≤ _
    simpa only [ofL2_toL2, abs_of_nonneg hB] using hbnd
  · simpa only [abs_of_nonneg hB] using
      norm_periodicCoerciveInverseH1_le E hγ hgap hh₀ htranslation

end JanetCartan.ContinuumCommutator.AugmentedFirstOrder
