module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.Estimates.FiniteExpansion
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.Estimates.Extension
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.Estimates.JointExpansion
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.EnvelopeScale

/-!
# Conditional annular Sobolev estimates for every datum

This is the deduction in `app:ch_response:eq:direct-envelope-profile` from
literal finite weak expansions and branch L² bounds. The constants precede
scales, fields and realizations. The actual original-datum derivative words
and the exact coefficient/input order identity are retained throughout.

This is CONDITIONAL until the parent annular construction instantiates the
weak identities and bounds for `annularEnvelopeOperator` and its literal
Hilbert adjoint. The producers are annular weak transfer, the forward branch
primitive-jet construction plus modulation, and the reversed-branch bounds.
-/

@[expose] public noncomputable section
open MeasureTheory LineDeriv
open scoped SchwartzMap
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
open CompactTransfer FourierIntegral Pseudodifferential
open IsometricEmbedding.Response.NearCarrier.FiniteFiber
variable {n r : ℕ} {P M ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup M] [NormedSpace ℝ M] [Fintype ι]
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- The complete spatial Sobolev implication for the annular expansion,
including order zero and every Hˢ datum. Its constant precedes the basis,
scales and all varying realizations. The literal original-datum derivative is
`annularTestDatumWord_eq_original`; no final Sobolev estimate is an input.
Source: `app:ch_response:eq:direct-envelope-profile`, with the joint enumeration
from `new:eq:carrier-ibp`. -/
theorem exists_annular_sobolev_constant_all_data (s : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ Cs : ℝ, 0 < Cs ∧
      ∀ (b : OrthonormalBasis ι ℝ (CarrierVariables n))
        (L lam : ℝ) (p : ℤ), 1 ≤ L → 0 < lam →
      ∀ (T : JointTransferTerm n P M ι → H →L[ℂ] H) (U : H →L[ℂ] H),
      (∀ (u : graphTestSpace n r) (is : List (Fin n)), is.length ≤ s →
        orderedTransferAction (fun i => lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
          (U (graphTestToLp u) : 𝓢'(E, V)) =
        ((jointTransferTerms (M := M) b
          (is.map fun i => (EuclideanSpace.single i 1, (0 : P)))).map
          fun t => (T t (graphTestToLp (annularTestDatumWord t.datumWord u)) : 𝓢'(E, V))).sum) →
      (∀ is : List (Fin n), is.length ≤ s →
        ∀ t ∈ jointTransferTerms b (is.map fun i => (EuclideanSpace.single i 1, (0 : P))),
          ‖T t‖ ≤ C * lam ^ p * L ^ (is.length - t.datumWord.length)) →
      ∀ u : H, MemVectorFourierSobolev (s : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (U u) ∧
          vectorFourierSobolevNorm (s : ℝ) (U u) ≤
            Cs * lam ^ p *
              (∑ j ∈ Finset.range (s + 1), L ^ (s - j) * vectorFourierSobolevNorm (j : ℝ) u) := by
  let D := ((r : ℝ) * (n + 1 : ℝ) ^ s) *
    (((Fintype.card ι + 2 : ℕ) : ℝ) ^ s * C *
      ((r : ℝ) * (1 + (n : ℝ) * (2 * Real.pi)) ^ s))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨1 + (r : ℝ) * r * D, by positivity, ?_⟩
  intro b L lam p hL hlam T U hw hb u hu
  have ht (v : graphTestSpace n r) := annular_sobolev_of_compact_expansion s C hC b T
    L lam p hL hlam v (U (graphTestToLp v)) (hw v) hb
  have h := annular_vector_weighted_bound_of_compactSmooth U s (D * lam ^ p) L
    (by positivity) (by linarith) ht u hu
  refine ⟨h.1, h.2.trans ?_⟩
  have hS : 0 ≤ vectorSpatialEnvelopeProfile s L u := Finset.sum_nonneg fun j _ =>
    mul_nonneg (pow_nonneg (by linarith) _) (norm_nonneg _)
  change ((r : ℝ) * r * (D * lam ^ p)) * vectorSpatialEnvelopeProfile s L u ≤ _
  dsimp [vectorSpatialEnvelopeProfile] at hS ⊢
  nlinarith [mul_nonneg (zpow_nonneg hlam.le p) hS]

/-- Distinct coefficient and input scales convert the exact weighted profile
to the manuscript envelope. The original admissible window is retained in
the statement; the purely algebraic conversion uses only `1 ≤ L ≤ K`.
This is the profile step after the all-data theorem, not a branch estimate.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem annular_envelope_profile_of_weighted_bound
    (s : ℕ) {L K lam nu C A₀ : ℝ} (p : ℤ)
    (hL : 1 ≤ L) (hLK : L ≤ K) (_hKlam : K ≤ lam ^ (1 - nu))
    (_hnu : 0 < nu) (_hnu1 : nu < 1) (hC : 0 ≤ C) (hlam : 0 < lam)
    (D : ℕ → ℝ) (u w : H)
    (hw : MemVectorFourierSobolev (s : ℝ) w)
    (hb : vectorFourierSobolevNorm (s : ℝ) w ≤
      C * lam ^ p * vectorSpatialEnvelopeProfile s L u)
    (hu : ∀ j, j ≤ s → vectorFourierSobolevNorm (j : ℝ) u ≤ A₀ * D j * K ^ j) :
    w ∈ (Complement.vectorFourierSobolevScale (d := n) (I := Fin r)).level s ∧
      Complement.vectorFourierSobolevScale.gradeNorm s w ≤
        (C * ∑ j ∈ Finset.range (s + 1), D j) * lam ^ p * A₀ * K ^ s := by
  refine ⟨hw, ?_⟩
  rw [Complement.vectorFourierSobolevScale_gradeNorm s hw]
  apply hb.trans
  calc
    _ ≤ C * lam ^ p * (A₀ * (∑ j ∈ Finset.range (s + 1), D j) * K ^ s) :=
      mul_le_mul_of_nonneg_left (vectorSpatialEnvelopeProfile_le_K s hL hLK D u hu)
        (by positivity)
    _ = _ := by ring

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
