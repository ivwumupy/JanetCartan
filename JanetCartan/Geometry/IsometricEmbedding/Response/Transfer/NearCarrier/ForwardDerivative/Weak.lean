module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ForwardDerivative.Regularized
public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Weak forward derivative transfer

Conditional on primitive analytic input for each literal frequency
regularization, the forward paragraph of
`app:ch_response:thm:response-literal-transfer` gives a weak derivative identity.
No output Sobolev membership is assumed. The producer of these inputs is
`jc-finite-fio-calculus`; the phase identity comes from
`jc-compatible-phase-geometry`. The parent `jc-response-near-carrier` must
instantiate them for the shifted selected amplitudes.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff SchwartzMap Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer
open FourierIntegral
variable {n r : ℕ}

/-- Analytic hypotheses on one actual regularization for the forward derivative
step in `app:ch_response:eq:direct-envelope-profile`. The fields are smoothness,
compact source support, the geometric phase identity, integrability and primitive
local domination. None asserts the transfer conclusion. -/
structure ForwardTransferRegularization (Φ : Euclidean n → Euclidean n → ℝ)
    (A : FullAmplitude n r)
    (B : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (u : Euclidean n → Fin r → ℂ) (j : Fin n) : Prop where
  phase_differentiable : ∀ δ, Differentiable ℝ (fun z ↦ Φ z δ)
  amplitude_smooth : ∀ δ, ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 δ)
  datum_smooth : ContDiff ℝ ∞ u
  datum_compact : HasCompactSupport u
  phase_identity : ∀ x δ, partialDeriv (fun z ↦ Φ z δ) x j = ∑ l, B x δ j l * δ l
  domination : ForwardKernelDomination Φ A u
  remainder_integrable : ∀ x, Integrable (fun δ ↦ ∫ y, graphOscillation Φ x y δ •
    (forwardRemainderAmplitude B A j x y δ).mulVec (u y))
  datum_integrable : ∀ x l, Integrable (fun δ ↦ ∫ y, graphOscillation Φ x y δ •
    (forwardDatumAmplitude B A j l x y δ).mulVec (partialDeriv u y l))
  base_pairing_integrable : ∀ φ : 𝓢(Euclidean n, ℂ),
    Integrable (fun x ↦ φ x • graphOperator Φ A u x)
  remainder_pairing_integrable : ∀ φ : 𝓢(Euclidean n, ℂ),
    Integrable (fun x ↦ φ x • graphOperator Φ (forwardRemainderAmplitude B A j) u x)
  datum_pairing_integrable : ∀ (φ : 𝓢(Euclidean n, ℂ)) l,
    Integrable (fun x ↦ φ x •
      graphOperator Φ (forwardDatumAmplitude B A j l) (fun y ↦ partialDeriv u y l) x)

/-- The pointwise derivative of the actual regularized graph, with both kinds
of transferred amplitude. Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem ForwardTransferRegularization.partialDeriv_graphOperator
    {Φ : Euclidean n → Euclidean n → ℝ} {A : FullAmplitude n r}
    {B : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ}
    {u : Euclidean n → Fin r → ℂ} {j : Fin n}
    (h : ForwardTransferRegularization Φ A B u j) (x : Euclidean n) :
    partialDeriv (graphOperator Φ A u) x j =
      graphOperator Φ (forwardRemainderAmplitude B A j) u x +
      ∑ l, graphOperator Φ (forwardDatumAmplitude B A j l) (fun y ↦ partialDeriv u y l) x := by
  rw [partialDeriv_graphOperator_forwardOutputAmplitude Φ A u h.phase_differentiable
    (fun y δ ↦ ((h.amplitude_smooth δ).comp (contDiff_id.prodMk contDiff_const)).differentiable
      (by simp)) h.domination]
  exact graphOperator_forwardOutputAmplitude_transfer Φ A B u x j h.amplitude_smooth
    h.datum_smooth h.datum_compact (h.phase_identity x)
    (h.remainder_integrable x) (h.datum_integrable x)

/-- Weak output derivative of the literal regularization, obtained by integration
by parts after deriving the pointwise transfer identity.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem ForwardTransferRegularization.weak_derivative
    {Φ : Euclidean n → Euclidean n → ℝ} {A : FullAmplitude n r}
    {B : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ}
    {u : Euclidean n → Fin r → ℂ} {j : Fin n}
    (h : ForwardTransferRegularization Φ A B u j) (φ : 𝓢(Euclidean n, ℂ)) :
    (∫ x, partialDeriv φ x j • graphOperator Φ A u x) =
      -((∫ x, φ x • graphOperator Φ (forwardRemainderAmplitude B A j) u x) +
        ∑ l, ∫ x, φ x •
          graphOperator Φ (forwardDatumAmplitude B A j l) (fun y ↦ partialDeriv u y l) x) := by
  have hid : Integrable (fun x ↦ φ x • partialDeriv (graphOperator Φ A u) x j) := by
    simp_rw [h.partialDeriv_graphOperator, smul_add, Finset.smul_sum]
    exact (h.remainder_pairing_integrable φ).add
      (integrable_finsetSum _ (fun l _ ↦ h.datum_pairing_integrable φ l))
  have hit : Integrable (fun x ↦ partialDeriv φ x j • graphOperator Φ A u x) := by
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv, partialDeriv] using
      h.base_pairing_integrable (LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ)) φ)
  have hh := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    hit hid (h.base_pairing_integrable φ) (fun x _ ↦ φ.differentiable x)
    (fun x _ ↦ (hasFDerivAt_graphOperator_of_domination Φ A u h.phase_differentiable
      (fun y δ ↦ ((h.amplitude_smooth δ).comp (contDiff_id.prodMk contDiff_const)).differentiable
        (by simp)) h.domination x).differentiableAt)
  change (∫ x, φ x • partialDeriv (graphOperator Φ A u) x j) =
    -(∫ x, partialDeriv φ x j • graphOperator Φ A u x) at hh
  simp_rw [h.partialDeriv_graphOperator, smul_add, Finset.smul_sum] at hh
  rw [integral_add (h.remainder_pairing_integrable φ)
    (integrable_finsetSum _ (fun l _ ↦ h.datum_pairing_integrable φ l)),
    integral_finsetSum _ (fun l _ ↦ h.datum_pairing_integrable φ l)] at hh
  exact (neg_eq_iff_eq_neg.mpr hh).symm

end JanetCartan.ResponseTransfer
