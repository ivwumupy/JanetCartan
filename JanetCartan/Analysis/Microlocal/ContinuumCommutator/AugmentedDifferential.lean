module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.HigherRegularity.RealCommutator
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FiniteNormal

/-!
# Higher commutators of the literal augmented normal

For `app:ch_background:eq:bg-commutator`, add the constructed image commutator
to the carrier and exterior commutators using the exact finite normal identity.
The reflected real carrier amplitudes already contain the factor four. The
exterior is still `(1 - ψ)²`; the image normal needs no full PDO representation.

`ImageGeometry` / `HistoryImage` produces the coefficient jets with reserve two.
`CanonicalBudgets` and `CarrierNormalRealization.SupportedShell` produce the
supported carrier amplitudes, their primitive budgets and literal identities.
The row construction must instantiate these on the same finite family and
history. This module proves their analytic consequences, not that remaining
geometric instantiation. The consumer is `AugmentedRegularity`.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
open JanetCartan.AmplitudeBound JanetCartan.Pseudodifferential
open JanetCartan.PeriodicLocalL2 JanetCartan.ContinuumRow

namespace JanetCartan.ContinuumCommutator

open PeriodicSobolevSpace HigherRegularity.RealCommutator

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The weak derivative identity and single-high commutator bound for the SAME
augmented normal (`app:ch_background:eq:bg-commutator`). Constants precede the
varying coefficients, amplitudes, carriers and high profile. The carrier low
order is `2 * (n + 1) + 1`, the image low order is one, and the common fixed
shift is `2 * (n + 1) + b₀`. `P` and `Q` are fixed producer constants, not high
norms. In particular, products of high norms are not introduced by finite
assembly. The exact primitive inputs and their producers are listed above. -/
theorem exists_augmentedNormal_tame_commutators
    (hn : 0 < n) (R : ℝ) (hR : R < 1 / 2)
    (M : ι → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (χmeas χsrc ψ : C(Torus n, ℝ))
    (hm : IsSmoothPeriodic χmeas) (hsrc : IsSmoothPeriodic χsrc)
    (hext : IsSmoothPeriodic (1 - ψ : C(Torus n, ℝ)))
    (P Q : ℕ → ℝ) (hP : ∀ s, 0 ≤ P s) (hQ : ∀ s, 0 ≤ Q s) (b₀ : ℕ) :
    ∃ D : ℕ → ℝ, (∀ s, 0 ≤ D s) ∧
      ∀ (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
        (_hc : ∀ a, IsSmoothPeriodic (c a)) (H : ℕ → ℝ),
      (∀ s, 0 ≤ H s) → Monotone H →
      (∀ a j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤ L) →
      (∀ a j x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤
        P j * (1 + H (j + 2))) →
      ∀ (b : ι → Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
        (hb : ∀ a, ContDiff ℝ ∞ (Function.uncurry (b a)))
        (hs : ∀ a ξ i j, SupportedInCenteredBox R (fun z ↦ b a ξ z i j))
        (hM : ∀ a i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b a ξ z i j)
          (2 * (n + 1) + 1) (M a)),
      (∀ s a i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b a ξ z i j)
        (2 * (n + 1) + (s + 1))
        (Q s * (1 + H (s + 1 + (2 * (n + 1) + b₀))))) →
      ∀ (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n),
      (∀ a, (carrierChannel (T a)).comp (carrierChannel (T a)).adjoint =
        realOutputCompression (transferOperator
          (vectorTwoPositionL2Operator hn R (b a) (hb a) (hs a) (M a)
            (fun i j ξ is his ↦ hM a i j ξ is (Nat.le_succ_of_le his))))) →
      let E := augmentedNormal (imageChannel c χmeas χsrc) T ψ
      ∀ s, ∃ K : (is : List (Fin n)) → is.length = s + 1 →
          PeriodicSobolevSpace n (Euclidean n) s →L[ℝ] OutputL2 n,
        (∀ (is : List (Fin n)) (hlen : is.length = s + 1)
            (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f),
          HasPeriodicWeakDerivativeList is (E (toL2 s (ofSmooth s f hf)))
            (E (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f)
              (hf.coordinateDerivList is))) + K is hlen (ofSmooth s f hf))) ∧
        (∀ is hlen u, ‖K is hlen u‖ ≤ D s *
          (‖u‖ + (1 + H (s + 1 + (2 * (n + 1) + b₀))) * ‖toL2 s u‖)) := by
  classical
  obtain ⟨Di, hDi, himage⟩ :=
    ImageChannel.Differential.exists_imageNormal_tame_commutators
      χmeas χsrc hm hsrc hL P hP
  choose Dc hDc hcarrier using fun s ↦
    exists_sobolev_commutators_of_matrix_representation hn R hR s M (fun _ ↦ 1)
      (1 - ψ) hext
  refine ⟨fun s ↦ Di s + Dc s * (1 + Q s),
    fun s ↦ add_nonneg (hDi s).le (mul_nonneg (hDc s) (by linarith [hQ s])), ?_⟩
  intro c hc H hH hmono hlow hhigh b hb hs hM hbudget T hT
  dsimp only
  intro s
  let Ec := (∑ a, (carrierChannel (T a)).comp (carrierChannel (T a)).adjoint) +
    cutoffMultiplier ((1 - ψ) ^ 2)
  have hEc : Ec = (∑ a, (1 : ℝ) • realOutputCompression (transferOperator
      (vectorTwoPositionL2Operator hn R (b a) (hb a) (hs a) (M a)
        (fun i j ξ is his ↦ hM a i j ξ is (Nat.le_succ_of_le his))))) +
      cutoffMultiplier ((1 - ψ) ^ 2) := by
    simp only [Ec, one_smul, hT]
  obtain ⟨Ki, hi, hbi⟩ := himage c hc H hH hmono hlow hhigh s
  obtain ⟨Kc, hkc, hbc⟩ := hcarrier s b hb hs
    (Q s * (1 + H (s + 1 + (2 * (n + 1) + b₀)))) hM (hbudget s) Ec hEc
  refine ⟨fun is hlen ↦ Ki is hlen + Kc is hlen, ?_, ?_⟩
  · intro is hlen f hf
    have h := weakDerivativeList_add (hi is hlen f hf) (hkc is hlen f hf)
    rw [augmentedNormal_eq_sum, add_assoc]
    convert h using 1
    simp only [Ec, add_apply]
    abel
  · intro is hlen u
    let A := 1 + H (s + 1 + (2 * (n + 1) + b₀))
    have hA : 1 ≤ A := by dsimp [A]; linarith [hH (s + 1 + (2 * (n + 1) + b₀))]
    have hshift : 1 + H (s + 3) ≤ A :=
      add_le_add (le_refl 1) (hmono (show s + 3 ≤ s + 1 + (2 * (n + 1) + b₀) by omega))
    have hi' : ‖Ki is hlen u‖ ≤ Di s * (‖u‖ + A * ‖toL2 s u‖) :=
      (hbi is hlen u).trans (mul_le_mul_of_nonneg_left
        (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hshift (norm_nonneg _))) (hDi s).le)
    have hmax : max 1 (Q s * A) ≤ (1 + Q s) * A := by
      apply max_le <;> nlinarith [mul_nonneg (hQ s) (show 0 ≤ A by linarith)]
    have hc' : ‖Kc is hlen u‖ ≤ Dc s * (1 + Q s) * (‖u‖ + A * ‖toL2 s u‖) := by
      apply (hbc is hlen u).trans
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (hDc s)
      nlinarith [mul_le_mul_of_nonneg_right hmax (norm_nonneg (toL2 s u)),
        mul_nonneg (hQ s) (norm_nonneg u)]
    exact (norm_add_le _ _).trans ((add_le_add hi' hc').trans_eq (by ring))

end JanetCartan.ContinuumCommutator
