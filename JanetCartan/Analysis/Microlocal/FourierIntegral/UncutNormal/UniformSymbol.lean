module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.UncutNormal.CutoffJets
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.PrimitiveBounds

/-!
# A common primitive budget for compact and uncut cross symbols

This supplies the actual uniform majorant required by the PDO strong limit in
`app:ch_regular_base:eq:actual-normal-amplitude`. The cutoffs act on the original
amplitudes before inverse substitution, and every derivative cost is uniform in
the compact-frequency index. Whole-image geometry supplies the uncut shell inputs.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.UncutNormal
open NormalComparison LowBounds LowBounds.FrequencyCutoff
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- One bilinear budget for the full cross symbol and all of its actual compact
frequency regularizations. The constant precedes the original amplitudes and
all cutoff indices. No transported-cutoff or normal-symbol bound is assumed.
Consumer: `cross_eq_vectorTwoPositionL2Operator_of_realizes`, for
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem exists_uniform_cycleCrossNormalSymbol_bounds (M L : ℝ)
    {δ F : ℝ} (hδ : 0 < δ) (hF : 0 ≤ F) :
    ∃ C > 0, ∀ (X D : Set E) (S : E → E → ℝ) (A B : E → E → Mat)
      (η : E → E → E → E) (J : E → E → E → E →L[ℝ] E)
      (W K : Set (NormalVariables n)) (V : ℕ → Set (NormalVariables n)) (R α β : ℝ),
      0 ≤ α → 0 ≤ β → AveragedGradientChart S X D η J δ →
      PrimitiveNormalGeometry X D S A B η J W K →
      (∀ x ∈ X, ‖x‖ ≤ R) →
      (∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D,
        ‖averagedGradient S x y u‖ ≤ F * (1 + ‖u‖)) →
      (∀ l, PrimitiveNormalShellInputs A B η J ((2 : ℝ)^l)
        (primitiveNormalReserve n) M L δ α β
        (normalDyadicShell (bufferedNormalDomain X D S) l) (V l)) →
      GraphNormalAmplitudeBounds (cycleCrossNormalSymbol D S A B η J) R (C * α * β) ∧
      ∀ m, GraphNormalAmplitudeBounds
        (cycleCrossNormalSymbol D S (cutAmplitude A m) (cutAmplitude B m) η J)
        R (C * α * β) := by
  obtain ⟨C, hC, hbound⟩ := exists_cycleCrossNormalSymbol_bounds (n := n) (r := r) M L hδ
  obtain ⟨Kcut, hKcut, hcut⟩ :=
    exists_cutCrossAmplitude_primitiveNormalShellInputs (n := n) (r := r) hF
  refine ⟨C * (1 + Kcut^2), mul_pos hC (by positivity), ?_⟩
  intro X D S A B η J W K V R α β hα hβ chart geometry hR hgrowth hjets
  have hb := hbound X D S A B η J W K V R α β hα hβ geometry hR hjets
  obtain ⟨V', _, hc⟩ := hcut X D S η J M L δ chart hgrowth A B α β V hα hβ hjets
  constructor
  · refine ⟨hb.smooth, hb.support, fun ξ is hi z ↦ (hb.derivative ξ is hi z).trans ?_⟩
    gcongr
    nlinarith [sq_nonneg Kcut]
  · intro m
    have hm := hbound X D S (cutAmplitude A m) (cutAmplitude B m) η J W K V'
      R (Kcut * α) (Kcut * β) (mul_nonneg hKcut.le hα) (mul_nonneg hKcut.le hβ)
      (geometry.cutAmplitude m m) hR (hc m)
    refine ⟨hm.smooth, hm.support, fun ξ is hi z ↦ (hm.derivative ξ is hi z).trans ?_⟩
    calc
      C * (Kcut * α) * (Kcut * β) = C * Kcut^2 * α * β := by ring
      _ ≤ C * (1 + Kcut^2) * α * β := by gcongr; linarith

end JanetCartan.FourierIntegral.UncutNormal
