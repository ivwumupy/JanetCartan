module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.Limits
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.Iteration

/-!
# Finite nonlinear branch expansion from literal regularized pairings

For `app:ch_regular_base:eq:graph-derivative-transfer`, the finite sum is exactly
`fullAmplitudeDerivativeTerms`. Only the ordered-action definition is reused
from the PDO module; no linear-phase operator derivative theorem is used.

This deduction still requires the actual compact-frequency pairing identity.
The parent weak-transfer proof must discharge that analytic premise for forward
and reverse kernels. Closure of admissibility under both kinds of branch is
explicit. The finite-order variant requires realization only for the branches
through that order and is the version consumed by the final assembly.
-/

@[expose] public noncomputable section
open MeasureTheory Filter LineDeriv JanetCartan.Pseudodifferential
open scoped ContDiff SchwartzMap Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

private theorem admissible_fullAmplitudeDerivativeTerms
    (R : Fin n → FullAmplitude n r → FullAmplitude n r)
    (P : Fin n → Fin n → FullAmplitude n r → FullAmplitude n r)
    (Q : FullAmplitude n r → Prop)
    (hR : ∀ i A, Q A → Q (R i A)) (hP : ∀ i j A, Q A → Q (P i j A))
    (A : FullAmplitude n r) (hA : Q A) (is : List (Fin n))
    (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms R P A is) : Q p.1 := by
  induction is generalizing p with
  | nil =>
    simp only [fullAmplitudeDerivativeTerms, List.mem_singleton] at hp
    subst p
    exact hA
  | cons i is ih =>
    simp only [fullAmplitudeDerivativeTerms, List.mem_flatMap] at hp
    obtain ⟨q, hq, hp⟩ := hp
    have hqQ := ih q hq
    simp only [fullAmplitudeDerivativeStep, List.mem_cons, List.mem_ofFn] at hp
    rcases hp with rfl | ⟨j, rfl⟩
    · exact hR i q.1 hqQ
    · exact hP i j q.1 hqQ

/-- The shared finite branch sum is the weak derivative expansion once the
literal compact-frequency integration-by-parts identities have been supplied.
The first-derivative recurrence of the limiting operators is *proved* by the
limit lemma during this induction. This conditional deduction is not the
unconditional weak-transfer theorem: the final assembly owes `hpair`, and must
choose the actual forward or reverse coefficients and kernels.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem fullAmplitudeDerivativeTerms_expansion_of_regularized_pairings
    (K : FullAmplitude n r → (E → Fin r → ℂ) → E → Fin r → ℂ)
    (χ : ℕ → E → ℂ)
    (R : Fin n → FullAmplitude n r → FullAmplitude n r)
    (P : Fin n → Fin n → FullAmplitude n r → FullAmplitude n r)
    (T : FullAmplitude n r → H →L[ℂ] H) (Q : FullAmplitude n r → Prop)
    (hR : ∀ i A, Q A → Q (R i A)) (hP : ∀ i j A, Q A → Q (P i j A))
    (hreal : ∀ A, Q A → GraphDistributionalRealization K χ A (T A))
    (hpair : ∀ A, Q A → ∀ k i (u : graphTestSpace n r) (φ : 𝓢(E, ℂ)),
      (∫ x, partialDeriv φ x i • WithLp.toLp 2
        (K (frequencyCutFullAmplitude (χ k) A) (fun y ↦ (u.val y).ofLp) x)) =
      -((∫ x, φ x • WithLp.toLp 2
          (K (frequencyCutFullAmplitude (χ k) (R i A)) (fun y ↦ (u.val y).ofLp) x)) +
        ∑ j, ∫ x, φ x • WithLp.toLp 2
          (K (frequencyCutFullAmplitude (χ k) (P i j A))
            (fun y ↦ ((graphTestPartialDeriv j u).val y).ofLp) x)))
    (A : FullAmplitude n r) (hA : Q A) (u : graphTestSpace n r) (is : List (Fin n)) :
    orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
        (T A (graphTestToLp u) : 𝓢'(E, V)) =
      ((fullAmplitudeDerivativeTerms R P A is).map fun p ↦
        (T p.1 (graphTestToLp (orderedTransferAction graphTestPartialDeriv p.2 u)) :
          𝓢'(E, V))).sum := by
  induction is with
  | nil => simp [orderedTransferAction, fullAmplitudeDerivativeTerms]
  | cons i is ih =>
    simp only [orderedTransferAction, ih, fullAmplitudeDerivativeTerms]
    rw [← lineDerivOpCLM_apply (R := ℂ), map_list_sum]
    simp only [List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map,
      Function.comp_def]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    have hpQ := admissible_fullAmplitudeDerivativeTerms R P Q hR hP A hA is p hp
    have h := graph_distributional_derivative_of_regularized_pairings K χ p.1
      (R i p.1) (fun j ↦ P i j p.1) (T p.1) (T (R i p.1))
      (fun j ↦ T (P i j p.1)) (hreal p.1 hpQ) (hreal _ (hR i p.1 hpQ))
      (fun j ↦ hreal _ (hP i j p.1 hpQ))
      (orderedTransferAction graphTestPartialDeriv p.2 u) i
      (fun k φ ↦ hpair p.1 hpQ k i _ φ)
    simpa [fullAmplitudeDerivativeStep, List.map_ofFn, List.sum_ofFn,
      orderedTransferAction, Function.comp_def] using h

/-- The finite weak expansion needs realizations only for the actual branches
through the requested derivative order. In particular, qualitative smoothness
and support do not assert bounded L² realizability of arbitrary amplitudes.
The forward and literal-adjoint assembly in `WeakTransfer` supplies `hpair`
from actual compact-frequency integration by parts, and `hR`/`hP` from primitive
coefficient closure. Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem fullAmplitudeDerivativeTerms_expansion_of_branch_realizations
    (K : FullAmplitude n r → (E → Fin r → ℂ) → E → Fin r → ℂ)
    (χ : ℕ → E → ℂ)
    (R : Fin n → FullAmplitude n r → FullAmplitude n r)
    (P : Fin n → Fin n → FullAmplitude n r → FullAmplitude n r)
    (T : FullAmplitude n r → H →L[ℂ] H) (Q : FullAmplitude n r → Prop)
    (hR : ∀ i A, Q A → Q (R i A)) (hP : ∀ i j A, Q A → Q (P i j A))
    (hpair : ∀ A, Q A → ∀ k i (u : graphTestSpace n r) (φ : 𝓢(E, ℂ)),
      (∫ x, partialDeriv φ x i • WithLp.toLp 2
        (K (frequencyCutFullAmplitude (χ k) A) (fun y ↦ (u.val y).ofLp) x)) =
      -((∫ x, φ x • WithLp.toLp 2
          (K (frequencyCutFullAmplitude (χ k) (R i A)) (fun y ↦ (u.val y).ofLp) x)) +
        ∑ j, ∫ x, φ x • WithLp.toLp 2
          (K (frequencyCutFullAmplitude (χ k) (P i j A))
            (fun y ↦ ((graphTestPartialDeriv j u).val y).ofLp) x)))
    (A : FullAmplitude n r) (hA : Q A) (u : graphTestSpace n r) (is : List (Fin n))
    (hreal : ∀ js : List (Fin n), js.length ≤ is.length →
      ∀ p ∈ fullAmplitudeDerivativeTerms R P A js,
        GraphDistributionalRealization K χ p.1 (T p.1)) :
    orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
        (T A (graphTestToLp u) : 𝓢'(E, V)) =
      ((fullAmplitudeDerivativeTerms R P A is).map fun p ↦
        (T p.1 (graphTestToLp (orderedTransferAction graphTestPartialDeriv p.2 u)) :
          𝓢'(E, V))).sum := by
  induction is with
  | nil => simp [orderedTransferAction, fullAmplitudeDerivativeTerms]
  | cons i is ih =>
    have hprev := ih (fun js hj p hp ↦ hreal js (hj.trans (Nat.le_succ _)) p hp)
    simp only [orderedTransferAction, hprev, fullAmplitudeDerivativeTerms]
    rw [← lineDerivOpCLM_apply (R := ℂ), map_list_sum]
    simp only [List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map,
      Function.comp_def]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    have hpQ := admissible_fullAmplitudeDerivativeTerms R P Q hR hP A hA is p hp
    have hstep (q) (hq : q ∈ fullAmplitudeDerivativeStep R P i p) :
        q ∈ fullAmplitudeDerivativeTerms R P A (i :: is) :=
      List.mem_flatMap.mpr ⟨p, hp, hq⟩
    have hrem := hreal (i :: is) le_rfl (R i p.1, p.2)
      (hstep _ (List.mem_cons_self ..))
    have hdatum (j : Fin n) := hreal (i :: is) le_rfl (P i j p.1, j :: p.2)
      (hstep _ (by simp [fullAmplitudeDerivativeStep]))
    have h := graph_distributional_derivative_of_regularized_pairings K χ p.1
      (R i p.1) (fun j ↦ P i j p.1) (T p.1) (T (R i p.1))
      (fun j ↦ T (P i j p.1)) (hreal is (Nat.le_succ _) p hp) hrem hdatum
      (orderedTransferAction graphTestPartialDeriv p.2 u) i
      (fun k φ ↦ hpair p.1 hpQ k i _ φ)
    simpa [fullAmplitudeDerivativeStep, List.map_ofFn, List.sum_ofFn,
      orderedTransferAction, Function.comp_def] using h

end JanetCartan.FourierIntegral
