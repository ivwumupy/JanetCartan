module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.ParameterJetRealization

/-!
# The actual inverse profiles in the classical response interface

Reindex the uniform vector L² profiles of
`complex_inverse_parameter_envelopes_of_actual_finite_words` and realize
their exact classical parameter derivatives. The joint and almost-everywhere
inputs are constructed on the same solver by
`fixedSolverParameterEnvelope_joint_and_parameter_classes`.
The amplitude and natural derivative reserve remain unchanged.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff NNReal ENNReal

namespace JanetCartan.FixedDomainInverse

open Pseudodifferential

variable {n q : ℕ} {I P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "CF" => EuclideanSpace ℂ (Fin q)
local notation "H" => Lp CF 2 (volume : Measure E)

/-- Uniform profiles of the actual inverse L² family give one scalar Fourier
profile for its literal classical parameter derivatives, in the order used
by `fullPrimaryResponse_fixedSolver_profile_family`. The vector profiles are
the output of the same finite-word/inverse assembly; joint smoothness and
the original value identity are supplied by the same-solver realization.
No spatial or parameter derivative is lost, and an arbitrary family amplitude
such as `τ³ * T^(B+16)` stays outside every constant
(`app:ch_response:eq:response-graded-reduced`,
`app:ch_response:eq:response-graded-derivative`). -/
theorem exists_classical_parameter_matrix_profiles_of_L2_profiles
    {V : Set P} (hV : IsOpen V) (g : I → P → E → CF) (u : I → P → H)
    (hg : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (g i)) (V ×ˢ univ))
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) V)
    (hidentify : ∀ i c, c ∈ V → u i c =ᵐ[volume] g i c)
    (A K : I → ℝ) (reserve : ℕ)
    (hprofile : ∀ s k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
      ∀ v : Fin k → P, (∀ l, ‖v l‖ ≤ 1) →
        MemVectorFourierSobolev (s : ℝ) (iteratedFDeriv ℝ k (u i) c v) ∧
          vectorFourierSobolevNorm (s : ℝ) (iteratedFDeriv ℝ k (u i) c v) ≤
            C * A i * K i ^ (s+k-reserve)) :
    ∃ C : ℕ → ℕ → ℝ, (∀ k p, 0 ≤ C k p) ∧
      ∀ i c, c ∈ V → ∀ k p : ℕ, ∀ v : Fin k → P, (∀ l, ‖v l‖ ≤ 1) →
        ∃ ug : PiLp 2 (fun _ : Fin q ↦ Lp ℂ 2 (volume : Measure E)),
          (∀ j, ug j =ᵐ[volume] fun x ↦
            (iteratedFDeriv ℝ k (fun b ↦ g i b x) c v) j) ∧
          MemMatrixFourierSobolev (p : ℝ) ug ∧
          matrixFourierSobolevNorm (p : ℝ) ug ≤ C k p * A i * K i ^ (p+k-reserve) := by
  classical
  choose C hC hb using hprofile
  refine ⟨fun k p ↦ C p k, fun k p ↦ hC p k, ?_⟩
  intro i c hc k p v hv
  obtain ⟨ug, hae, _, hmem, hnorm⟩ := exists_matrixFourier_parameter_jet_class_of_joint_smooth
    hV (hg i) (hu i) (hidentify i) k v hc
  obtain ⟨hm, hbound⟩ := hb p k i c hc v hv
  exact ⟨ug, hae, (hmem p).mpr hm, (hnorm p).trans_le hbound⟩

end JanetCartan.FixedDomainInverse
