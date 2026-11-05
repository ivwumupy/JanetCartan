module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Carrier
public import JanetCartan.Analysis.Microlocal.FourierIntegral.Differential
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Full amplitudes for forward derivative transfer

The amplitudes in the forward paragraph of
`app:ch_response:thm:response-literal-transfer`, used in
`app:ch_response:eq:direct-envelope-profile`. The selected amplitude is translated
in the physical covector only; both physical positions and every weight remain.
The parent `jc-response-near-carrier` must supply the phase derivative identity.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer
open FourierIntegral
variable {n r : ℕ}

/-- The literal selected amplitude in the shifted physical covector of
`app:ch_response:thm:response-literal-transfer`. -/
def forwardSelectedAmplitude (A : FullAmplitude n r) (ζ : Euclidean n) (ρ : ℝ)
    (q : Euclidean n → ℂ) : FullAmplitude n r :=
  fun x y δ ↦ selectedAmplitude A ζ ρ q x y (ρ • ζ + δ)

/-- The amplitude multiplying the `l`th datum derivative in the forward step of
`app:ch_response:eq:direct-envelope-profile`. -/
def forwardDatumAmplitude (B : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (A : FullAmplitude n r) (j l : Fin n) : FullAmplitude n r :=
  fun x y δ ↦ (B x δ j l : ℂ) • A x y δ

/-- The remaining full two-position amplitude in the forward step of
`app:ch_response:eq:direct-envelope-profile`. Applying this to the selected
amplitude retains derivatives of every physical cutoff and weight. -/
def forwardRemainderAmplitude
    (B : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (A : FullAmplitude n r) (j : Fin n) : FullAmplitude n r :=
  fun x y δ ↦ partialDeriv (fun z ↦ A z y δ) x j +
    ∑ l, (B x δ j l : ℂ) • partialDeriv (fun z ↦ A x z δ) y l

/-- The full output derivative amplitude before source integration by parts,
used to establish the forward identity in
`app:ch_response:thm:response-literal-transfer`. -/
def forwardOutputAmplitude (Φ : Euclidean n → Euclidean n → ℝ)
    (A : FullAmplitude n r) (j : Fin n) : FullAmplitude n r :=
  fun x y δ ↦ partialDeriv (fun z ↦ A z y δ) x j +
    (Complex.I * ((partialDeriv (fun z ↦ Φ z δ) x j : ℝ) : ℂ)) • A x y δ

/-- Source derivative of the physical graph oscillation, with no extra `2π`.
Source: the forward integration by parts in
`app:ch_response:thm:response-literal-transfer`. -/
theorem partialDeriv_graphOscillation_source
    (Φ : Euclidean n → Euclidean n → ℝ) (x y δ : Euclidean n) (l : Fin n) :
    partialDeriv (fun z ↦ graphOscillation Φ x z δ) y l =
      -(Complex.I * (δ l : ℂ)) * graphOscillation Φ x y δ := by
  have hi : HasFDerivAt (fun z : Euclidean n ↦ inner ℝ z δ)
      (fderiv ℝ (fun z : Euclidean n ↦ inner ℝ z δ) y) y :=
    (differentiableAt_id.inner ℝ (differentiableAt_const δ)).hasFDerivAt
  have h := (((Complex.ofRealCLM.hasFDerivAt.comp y
    ((hasFDerivAt_const (Φ x δ) y).sub hi)).const_mul Complex.I).cexp).fderiv
  dsimp only [Function.comp_def, Pi.sub_apply, Complex.ofRealCLM_apply] at h
  unfold partialDeriv graphOscillation
  rw [h]
  simp [ContinuousLinearMap.comp_apply, fderiv_inner_apply,
    EuclideanSpace.inner_single_left, mul_comm]

/-- Output derivative of the physical graph oscillation. The only geometric
input here is differentiability of the phase; `dₓ ΔS = Bδ` is substituted by the
consumer of `app:ch_response:eq:direct-envelope-profile`. -/
theorem partialDeriv_graphOscillation_output
    (Φ : Euclidean n → Euclidean n → ℝ) (x y δ : Euclidean n) (j : Fin n)
    (hΦ : DifferentiableAt ℝ (fun z ↦ Φ z δ) x) :
    partialDeriv (fun z ↦ graphOscillation Φ z y δ) x j =
      (Complex.I * ((partialDeriv (fun z ↦ Φ z δ) x j : ℝ) : ℂ)) *
        graphOscillation Φ x y δ := by
  have h := (((Complex.ofRealCLM.hasFDerivAt.comp x
    (hΦ.hasFDerivAt.sub (hasFDerivAt_const (inner ℝ y δ) x))).const_mul
      Complex.I).cexp).fderiv
  dsimp only [Function.comp_def, Pi.sub_apply, Complex.ofRealCLM_apply] at h
  unfold partialDeriv graphOscillation
  rw [h]
  simp [ContinuousLinearMap.comp_apply, mul_comm]

/-- Coordinate Leibniz rule for the full matrix amplitude and datum. This is the
source differentiation used in `app:ch_response:eq:direct-envelope-profile`. -/
theorem partialDeriv_matrix_mulVec
    (a : Euclidean n → Matrix (Fin r) (Fin r) ℂ) (u : Euclidean n → Fin r → ℂ)
    (x : Euclidean n) (j : Fin n) (ha : DifferentiableAt ℝ a x)
    (hu : DifferentiableAt ℝ u x) :
    partialDeriv (fun y ↦ (a y).mulVec (u y)) x j =
      (partialDeriv a x j).mulVec (u x) + (a x).mulVec (partialDeriv u x j) := by
  have hs (i k : Fin r) : DifferentiableAt ℝ (fun y ↦ a y i k * u y k) x :=
    (differentiableAt_pi.mp (differentiableAt_pi.mp ha i) k).mul (differentiableAt_pi.mp hu k)
  have hd : DifferentiableAt ℝ (fun y ↦ (a y).mulVec (u y)) x := by
    apply differentiableAt_pi.mpr
    intro i
    change DifferentiableAt ℝ (fun y ↦ ∑ k, a y i k * u y k) x
    exact DifferentiableAt.fun_sum (fun k _ ↦ hs i k)
  ext i
  change (fderiv ℝ (fun y ↦ (a y).mulVec (u y)) x (EuclideanSpace.single j 1)) i = _
  have he := congrArg (fun L : Euclidean n →L[ℝ] ℂ ↦ L (EuclideanSpace.single j 1))
    (fderiv_apply hd i)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at he
  rw [← he]
  simp only [Matrix.mulVec, dotProduct]
  rw [fderiv_fun_sum (fun k _ ↦ hs i k)]
  simp only [sum_apply, fderiv_fun_mul (differentiableAt_pi.mp (differentiableAt_pi.mp ha i) _) (differentiableAt_pi.mp hu _),
    add_apply, smul_apply, smul_eq_mul,
    partialDeriv, Pi.add_apply, Finset.sum_add_distrib]
  simp only [fderiv_apply (differentiableAt_pi.mp ha i), fderiv_apply ha, fderiv_apply hu,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Matrix.mulVec, dotProduct]
  simp only [mul_comm]
  exact add_comm _ _

/-- Differentiation of the literal kernel, before moving derivatives to the
source in `app:ch_response:thm:response-literal-transfer`. -/
theorem partialDeriv_graphOscillation_mulVec_output
    (Φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (u : Euclidean n → Fin r → ℂ) (x y δ : Euclidean n) (j : Fin n)
    (hΦ : DifferentiableAt ℝ (fun z ↦ Φ z δ) x)
    (hA : DifferentiableAt ℝ (fun z ↦ A z y δ) x) :
    partialDeriv (fun z ↦ graphOscillation Φ z y δ • (A z y δ).mulVec (u y)) x j =
      graphOscillation Φ x y δ • (forwardOutputAmplitude Φ A j x y δ).mulVec (u y) := by
  have he : DifferentiableAt ℝ (fun z ↦ graphOscillation Φ z y δ) x :=
    ((Complex.ofRealCLM.differentiableAt.comp x
      (hΦ.sub (differentiableAt_const (inner ℝ y δ)))).const_mul _).cexp
  have hg : DifferentiableAt ℝ (fun z ↦ (A z y δ).mulVec (u y)) x := by
    apply differentiableAt_pi.mpr
    intro i
    change DifferentiableAt ℝ (fun z ↦ ∑ k, A z y δ i k * u y k) x
    exact DifferentiableAt.fun_sum (fun k _ ↦
      (differentiableAt_pi.mp (differentiableAt_pi.mp hA i) k).mul_const _)
  rw [partialDeriv_cutoff_mul _ _ x j he hg,
    partialDeriv_matrix_mulVec _ (fun _ ↦ u y) x j hA (differentiableAt_const _),
    partialDeriv_graphOscillation_output Φ x y δ j hΦ]
  simp only [forwardOutputAmplitude, partialDeriv, fderiv_const_apply, zero_apply,
    Matrix.mulVec_zero, add_zero, Matrix.add_mulVec, Matrix.smul_mulVec, smul_add, mul_smul]
  module

end JanetCartan.ResponseTransfer
