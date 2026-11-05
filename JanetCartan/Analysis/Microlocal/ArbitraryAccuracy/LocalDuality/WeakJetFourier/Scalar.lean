module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.RestrictionPairing
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.WeakJetFourier.Scalar.JetEvaluations

/-!
# Scalar Fourier regularity from genuine weak extensions

For `app:ch_regular_base:eq:negative-duality` and
`app:ch_regular:eq:inverse-remainder`, actual multilinear weak jets construct
all distributional coordinate derivatives. The integer Fourier derivative
comparison then supplies both membership and a uniform norm bound. The explicit
constant is `2 ^ N * (n + 1) ^ N`, including dimension and order zero.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.ArbitraryAccuracy

open LocalSobolev Pseudodifferential

/-- Genuine scalar weak extensions belong to the integer Fourier Sobolev space,
with a positive comparison constant fixed before the domain and the extension.
This supplies the scalar premise of `componentFourierSobolev_extension_bounds_of_scalar`
for `app:ch_regular_base:eq:negative-duality` and `app:ch_regular:eq:inverse-remainder`.
The actual distributional derivatives retain the `2π i ξⱼ` Fourier convention. -/
theorem scalarFourierSobolev_extension_bounds (n N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : Set (EuclideanSpace ℝ (Fin n))) (v : LocalL2 W ℂ)
      (e : SobolevExtension W N v),
      MemFourierSobolev (N : ℝ) e.toL2 ∧
        fourierSobolevNorm (N : ℝ) e.toL2 ≤ C * e.jetNorm := by
  refine ⟨(2 : ℝ) ^ N * ((n : ℝ) + 1) ^ N, by positivity, ?_⟩
  intro W v e
  obtain ⟨f, hf, hnorm⟩ := e.evaluatedJetL2_exists_integerDerivatives N 0
    (by omega) (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)
  rw [e.evaluatedJetL2_zero] at hf
  refine ⟨hf.memFourierSobolev, hf.fourierSobolevNorm_le.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left hnorm (by positivity)).trans_eq (mul_assoc _ _ _).symm

end JanetCartan.ArbitraryAccuracy
