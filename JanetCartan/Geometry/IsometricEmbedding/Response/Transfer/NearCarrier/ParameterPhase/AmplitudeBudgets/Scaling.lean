module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterPhase.Amplitude
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterPhase.AmplitudeBudgets.Calculus

/-!
# Physical and normalized covector jets

Exact scaling and cancellation for the primitive inputs to
`norm_iteratedFDeriv_normalizedParameterAmplitude_le`, as used in
`app:ch_response:thm:response-literal-transfer` and
`app:ch_response:eq:direct-envelope-profile`. The target space may itself consist
of multilinear physical jets; normalization acts only on the covector variable.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.ResponseTransfer

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Exact local finite-order identity `Dη^k f(ρ η) = ρ^k Dξ^k f(ρ η)`.
It also applies when `f` is an already differentiated physical amplitude, for
`app:ch_response:eq:direct-envelope-profile`. -/
theorem iteratedFDeriv_normalizedCovector_eq {f : Euclidean n → F}
    {V : Set (Euclidean n)} (hV : IsOpen V) {k : ℕ} (hf : ContDiffOn ℝ k f V)
    (ρ : ℝ) {η : Euclidean n} (hη : ρ • η ∈ V) :
    iteratedFDeriv ℝ k (fun ε ↦ f (ρ • ε)) η =
      ρ ^ k • iteratedFDeriv ℝ k f (ρ • η) := by
  let L : Euclidean n →L[ℝ] Euclidean n := ρ • ContinuousLinearMap.id ℝ _
  have hpre : IsOpen (L ⁻¹' V) := hV.preimage L.continuous
  have h := L.iteratedFDerivWithin_comp_right hf hV.uniqueDiffOn hpre.uniqueDiffOn
    hη (i := k) le_rfl
  rw [iteratedFDerivWithin_of_isOpen _ hpre hη,
    iteratedFDerivWithin_of_isOpen _ hV (show L η ∈ V from hη)] at h
  change iteratedFDeriv ℝ k (f ∘ L) η = _
  rw [h]
  ext v
  change iteratedFDeriv ℝ k f (ρ • η) (fun i ↦ ρ • v i) =
    ρ ^ k • iteratedFDeriv ℝ k f (ρ • η) v
  simpa using (iteratedFDeriv ℝ k f (ρ • η)).map_smul_univ (fun _ ↦ ρ) v

/-- Exact norm scaling, before cancellation of the primitive symbol weight in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_iteratedFDeriv_normalizedCovector_eq {f : Euclidean n → F}
    {V : Set (Euclidean n)} (hV : IsOpen V) {k : ℕ} (hf : ContDiffOn ℝ k f V)
    {ρ : ℝ} (hρ : 0 < ρ) {η : Euclidean n} (hη : ρ • η ∈ V) :
    ‖iteratedFDeriv ℝ k (fun ε ↦ f (ρ • ε)) η‖ =
      ρ ^ k * ‖iteratedFDeriv ℝ k f (ρ • η)‖ := by
  rw [iteratedFDeriv_normalizedCovector_eq hV hf ρ hη, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hρ.le k)]

/-- A physical covector symbol weight `M / ρ^k` gives a normalized jet budget
`M`, with no frequency loss (`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_iteratedFDeriv_normalizedCovector_le {f : Euclidean n → F}
    {V : Set (Euclidean n)} (hV : IsOpen V) {k : ℕ} (hf : ContDiffOn ℝ k f V)
    {ρ M : ℝ} (hρ : 0 < ρ) {η : Euclidean n} (hη : ρ • η ∈ V)
    (hjet : ‖iteratedFDeriv ℝ k f (ρ • η)‖ ≤ M / ρ ^ k) :
    ‖iteratedFDeriv ℝ k (fun ε ↦ f (ρ • ε)) η‖ ≤ M := by
  rw [norm_iteratedFDeriv_normalizedCovector_eq hV hf hρ hη]
  calc
    _ ≤ ρ ^ k * (M / ρ ^ k) := mul_le_mul_of_nonneg_left hjet (pow_nonneg hρ.le _)
    _ = M := by field_simp

/-- Evaluated normalized jets use exactly the checked carrier-covector
cancellation lemma. Direction slots can be carrier derivatives of any orders,
while `f` can already contain both physical derivatives
(`app:ch_response:thm:response-literal-transfer`). -/
theorem norm_normalizedCovector_mixedEvaluation_le {f : Euclidean n → F}
    {V : Set (Euclidean n)} (hV : IsOpen V) {k : ℕ} (hf : ContDiffOn ℝ k f V)
    {ρ M : ℝ} (hρ : 0 < ρ) {η : Euclidean n} (hη : ρ • η ∈ V)
    (hjet : ‖iteratedFDeriv ℝ k f (ρ • η)‖ ≤ M / ρ ^ k)
    (v : Fin k → Euclidean n) :
    ‖iteratedFDeriv ℝ k (fun ε ↦ f (ρ • ε)) η v‖ ≤ M * ∏ i, ‖v i‖ := by
  rw [iteratedFDeriv_normalizedCovector_eq hV hf ρ hη]
  have he : (ρ ^ k • iteratedFDeriv ℝ k f (ρ • η)) v =
      iteratedFDeriv ℝ k f (ρ • η) (fun i ↦ ρ • v i) := by
    simpa using ((iteratedFDeriv ℝ k f (ρ • η)).map_smul_univ (fun _ ↦ ρ) v).symm
  rw [he]
  exact norm_carrierCovector_multilinear_le _ v ρ M hρ hjet

end JanetCartan.ResponseTransfer
