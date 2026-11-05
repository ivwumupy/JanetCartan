module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets.Literal
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.InactiveSource.EnvelopeJets
public import JanetCartan.Analysis.ContDiff.Norm.Products
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-!
# Original matrix amplitudes times supported Sobolev envelopes

This is the undifferentiated-external-amplitude step of
`app:ch_response:lem:energy-carrier-jets`. The source product rule uses only
one total derivative budget: the matrix uses scale `L`, the envelope uses
scale `K`, and `L ≤ K` gives one factor `K^k`. Sobolev embedding costs the
fixed reserve `n+1`, chosen before `k`.

The matrix input is an ORIGINAL amplitude slice, including both masks and
beta when instantiated for the elapsed graph. The subsequent primitive
producer must discharge that input; this lemma assumes no normalized-jet
profile and does not assert the positive-external-order endpoint.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
-- Unfold the Frobenius matrix topology wrappers when synthesizing operator norms.
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets
open Complement.InactiveSource JanetCartan.Pseudodifferential
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "M" => Matrix (Fin r) (Fin r) ℂ

/-- Frobenius matrix action with the SAME Euclidean vector bridge as the
published annular amplitudes (`app:ch_response:lem:energy-carrier-jets`). -/
def annularMatrixAction (r : ℕ) : Matrix (Fin r) (Fin r) ℂ →L[ℝ]
    EuclideanSpace ℂ (Fin r) →L[ℝ] EuclideanSpace ℂ (Fin r) :=
  (show (Matrix (Fin r) (Fin r) ℂ →ₗ[ℝ] EuclideanSpace ℂ (Fin r) →ₗ[ℝ]
    EuclideanSpace ℂ (Fin r)) from LinearMap.mk₂ ℝ (fun (A : Matrix (Fin r) (Fin r) ℂ) (v : EuclideanSpace ℂ (Fin r)) =>
    WithLp.toLp 2 (A.mulVec v.ofLp))
    (by intros; simp [Matrix.add_mulVec])
    (by intros; simp [Matrix.smul_mulVec])
    (by intros; simp [Matrix.mulVec_add])
    (by intros; simp [Matrix.mulVec_smul])).toContinuousBilinearMap

/-- The action is literal multiplication, not a replacement of the kernel.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem annularMatrixAction_apply (B : M) (v : F) :
    annularMatrixAction r B v = WithLp.toLp 2 (B.mulVec v.ofLp) := rfl

/-- Constants from the original matrix profile `B` and original envelope
Sobolev profile `C`; no carrier, scales, frequency or envelope is an argument.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
def sourceProductBudget (n r : ℕ) (B C : ℕ → ℝ) (k : ℕ) : ℝ :=
  ‖annularMatrixAction r‖ * ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * B i * envelopeJetProfileConstant n C (k - i)

/-- Nonnegative product constants for `norm_annularSourceIntegral_le`.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem sourceProductBudget_nonneg (B C : ℕ → ℝ) (hB : ∀ i, 0 ≤ B i) (k : ℕ) :
    0 ≤ sourceProductBudget n r B C k := by
  exact mul_nonneg (norm_nonneg (annularMatrixAction r)) (Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB i))
      (envelopeJetProfileConstant_nonneg n C (k - i)))

/-- Source derivatives of the original vector amplitude from original symbol
jets and the actual envelope Sobolev norms. The fixed loss `n+1` is independent
of source order and later integration order. The separate scales of
`app:ch_response:eq:direct-envelope-profile` remain explicit. -/
theorem norm_iteratedFDeriv_matrixAction_le_sobolev
    {B C : ℕ → ℝ} (hB : ∀ i, 0 ≤ B i)
    {A₀ H L K : ℝ} (hA : 0 ≤ A₀) (hH : 0 ≤ H)
    (hL : 0 ≤ L) (hLK : L ≤ K) (hK : 1 ≤ K)
    {b : E → M} (hb : ContDiff ℝ ∞ b)
    {a : E → F} (ha : ContDiff ℝ ∞ a) (hm : MemLp a 2 volume)
    (hmem : ∀ s : ℕ, MemVectorFourierSobolev (s : ℝ) (hm.toLp a))
    (hprofile : ∀ s : ℕ,
      vectorFourierSobolevNorm (s : ℝ) (hm.toLp a) ≤ C s * A₀ * K ^ s)
    (z : E) (k : ℕ)
    (hjet : ∀ i ≤ k, ‖iteratedFDeriv ℝ i b z‖ ≤ B i * H * L ^ i) :
    ‖iteratedFDeriv ℝ k (fun y => annularMatrixAction r (b y) (a y)) z‖ ≤
      sourceProductBudget n r B C k * (H * A₀ * K ^ (n + 1)) * K ^ k := by
  have hK0 := zero_le_one.trans hK
  apply ((annularMatrixAction r).norm_iteratedFDeriv_le_of_bilinear hb ha z
    (by simp : (k : ℕ∞ω) ≤ ∞)).trans
  unfold sourceProductBudget
  rw [mul_assoc, mul_assoc, Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro i hi
  have hik : i ≤ k := Finset.mem_range_succ_iff.mp hi
  have hBi := hB i
  have he := norm_iteratedFDeriv_le_envelope_profile ha.continuous hm hA hK
    hmem hprofile (k - i) z
  have hbi := (hjet i hik).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hL hLK i) (mul_nonneg (hB i) hH))
  calc
    _ ≤ (k.choose i : ℝ) * (B i * H * K ^ i) *
        (envelopeJetProfileConstant n C (k - i) * ((A₀ * K ^ (n + 1)) * K ^ (k - i))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hbi (Nat.cast_nonneg _)) he
        (norm_nonneg _) (by positivity)
    _ = (k.choose i : ℝ) * B i * envelopeJetProfileConstant n C (k - i) *
        (H * A₀ * K ^ (n + 1)) * K ^ (i + (k - i)) := by rw [pow_add]; ring
    _ = _ := by rw [Nat.add_sub_of_le hik]; ring

/-- The forward literal source amplitude uses precisely the previous product
estimate. This closes its envelope input from the original Sobolev profile;
the matrix profile still belongs to the primitive elapsed-symbol producer.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem norm_iteratedFDeriv_forwardAnnularSourceAmplitude_le_sobolev
    (A : FourierIntegral.FullAmplitude n r) (π : E → ℂ) (lam : ℝ)
    {a : E → F} (ha : ContDiff ℝ ∞ a) (hm : MemLp a 2 volume)
    (x ξ z : E) (B C : ℕ → ℝ) (hB : ∀ i, 0 ≤ B i)
    {A₀ H L K : ℝ} (hA : 0 ≤ A₀) (hH : 0 ≤ H)
    (hL : 0 ≤ L) (hLK : L ≤ K) (hK : 1 ≤ K)
    (hb : ContDiff ℝ ∞ (fun y => annularComplementAmplitude π lam A x y ξ))
    (hmem : ∀ s : ℕ, MemVectorFourierSobolev (s : ℝ) (hm.toLp a))
    (hprofile : ∀ s : ℕ,
      vectorFourierSobolevNorm (s : ℝ) (hm.toLp a) ≤ C s * A₀ * K ^ s)
    (k : ℕ) (hjet : ∀ i ≤ k,
      ‖iteratedFDeriv ℝ i (fun y => annularComplementAmplitude π lam A x y ξ) z‖ ≤
        B i * H * L ^ i) :
    ‖iteratedFDeriv ℝ k (forwardAnnularSourceAmplitude A π lam a x ξ) z‖ ≤
      sourceProductBudget n r B C k * (H * A₀ * K ^ (n + 1)) * K ^ k :=
  norm_iteratedFDeriv_matrixAction_le_sobolev hB hA hH hL hLK hK hb ha hm
    hmem hprofile z k hjet

/-- The same original-Sobolev product estimate for the literal adjoint, with
its conjugate-transposed matrix in the reversed physical positions.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem norm_iteratedFDeriv_adjointAnnularSourceAmplitude_le_sobolev
    (A : FourierIntegral.FullAmplitude n r) (π : E → ℂ) (lam : ℝ)
    {a : E → F} (ha : ContDiff ℝ ∞ a) (hm : MemLp a 2 volume)
    (x ξ z : E) (B C : ℕ → ℝ) (hB : ∀ i, 0 ≤ B i)
    {A₀ H L K : ℝ} (hA : 0 ≤ A₀) (hH : 0 ≤ H)
    (hL : 0 ≤ L) (hLK : L ≤ K) (hK : 1 ≤ K)
    (hb : ContDiff ℝ ∞ (fun y => (annularComplementAmplitude π lam A y x ξ).conjTranspose))
    (hmem : ∀ s : ℕ, MemVectorFourierSobolev (s : ℝ) (hm.toLp a))
    (hprofile : ∀ s : ℕ,
      vectorFourierSobolevNorm (s : ℝ) (hm.toLp a) ≤ C s * A₀ * K ^ s)
    (k : ℕ) (hjet : ∀ i ≤ k,
      ‖iteratedFDeriv ℝ i (fun y => (annularComplementAmplitude π lam A y x ξ).conjTranspose) z‖ ≤
        B i * H * L ^ i) :
    ‖iteratedFDeriv ℝ k (adjointAnnularSourceAmplitude A π lam a x ξ) z‖ ≤
      sourceProductBudget n r B C k * (H * A₀ * K ^ (n + 1)) * K ^ k :=
  norm_iteratedFDeriv_matrixAction_le_sobolev hB hA hH hL hLK hK hb ha hm
    hmem hprofile z k hjet

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets
