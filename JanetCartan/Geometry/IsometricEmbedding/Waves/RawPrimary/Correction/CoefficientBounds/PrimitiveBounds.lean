module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.CoefficientBounds.JetBounds

/-!
# Explicit finite loss in the primitive fields

The correction in `app:ch_waves:eq:primary-algebraic-correction` costs two
immersion derivatives and one derivative of the frame, phase gradient and
scalar. No estimate or regularity of the correction is an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.StressFrame

namespace JanetCartan.RawPrimary.CorrectionBounds
open NullTransport NullTransport.CoefficientBounds ProjectedStressFrame GeometricProfile
open ActualCarriers.ConstructedCarrierJets

variable {n N : ℕ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z]

omit [FiniteDimensional ℝ Z] in
/-- The primitive immersion jet and the first joint value jet are smooth
on the original open chart (`app:ch_waves:eq:WKB-grading`). -/
theorem contDiffOn_primitiveJet {U : Set (Euclidean n)} (hU : IsOpen U)
    {Ω : Set (Euclidean n × Z)} (hΩ : IsOpen Ω) (hx : MapsTo Prod.fst Ω U)
    {F : Euclidean n → Euclidean N} {v : Euclidean n × Z → Values n}
    (hF : ContDiffOn ℝ ∞ F U) (hv : ContDiffOn ℝ ∞ v Ω) :
    ContDiffOn ℝ ∞ (primitiveJet F v) Ω :=
  ((contDiffOn_stressJet hU hF).comp contDiffOn_fst hx).prodMk
    (hv.prodMk (hv.fderiv_of_isOpen hΩ (by simp)))

/-- The orthogonal correction has one high primitive norm with fixed losses
two and one. The compact physical domain, ball, low budgets and geometric gaps
determine the constants before any varying field or frequency
(`app:ch_waves:eq:WKB-grading`). -/
theorem exists_primitiveCorrection_tame
    (a : Euclidean n × Z) {ρ : ℝ} (hρ : 0 < ρ)
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hx : MapsTo Prod.fst (closedBall a ρ) K) (row col : Fin n)
    (M L : ℝ) {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (U : Set (Euclidean n)) (Ω : Set (Euclidean n × Z)),
        IsOpen U → IsOpen Ω → K ⊆ U → closedBall a ρ ⊆ Ω → MapsTo Prod.fst Ω U →
      ∀ (F : Euclidean n → Euclidean N) (v : Euclidean n × Z → Values n),
        ContDiffOn ℝ ∞ F U → ContDiffOn ℝ ∞ v Ω →
        cNorm (closedBall a ρ) 1 v ≤ L →
        (∀ x ∈ K, ‖stressJet F x‖ ≤ M) →
        (∀ x ∈ K, ∀ u, κ * ‖u‖ ^ 2 ≤ ‖fderiv ℝ F x u‖ ^ 2) →
        (∀ w ∈ closedBall a ρ, (symbolValue (v w)).det = 0) →
        (∀ w ∈ closedBall a ρ, δ ≤ |(symbolValue (v w)).adjugate row col|) →
        ∀ m, cNorm (closedBall a ρ) m (correctionJetValue col ∘ primitiveJet F v) ≤
          C m * (1 + cNorm K (m + 2) F + cNorm (closedBall a ρ) (m + 1) v) := by
  obtain ⟨C, hC, hb⟩ := exists_correctionJetValue_tame (N := N) a hρ row col M L hκ hδ
  obtain ⟨A, hA, ha⟩ := exists_cNorm_fixed_pullback_le (G := StressJet n N)
    (isCompact_closedBall a ρ) hK (ψ := Prod.fst) (fun _ _ ↦ contDiff_fst.contDiffAt) hx
  refine ⟨fun m ↦ C m * (1 + 2 * A m),
    fun m ↦ mul_pos (hC m) (by have := hA m; positivity), ?_⟩
  intro U Ω hU hΩ hKU hball hΩU F v hF hv hlow hM hmet hchar hminor m
  have hJ := (contDiffOn_stressJet hU hF).comp contDiffOn_fst hΩU
  have hout := hb Ω hΩ hball v (fun w ↦ stressJet F w.1) hv hJ hlow
    (fun w hw ↦ hM w.1 (hx hw)) (fun w hw ↦ hmet w.1 (hx hw)) hchar hminor m
  have hjet := cNorm_stressJet_le hK (fun x hx ↦ hF.contDiffAt (hU.mem_nhds (hKU hx))) m
  have hpull := ha (stressJet F)
    (fun x hx ↦ (contDiffOn_stressJet hU hF).contDiffAt (hU.mem_nhds (hKU hx))) m
  have hJhigh := hpull.trans (mul_le_mul_of_nonneg_left hjet (hA m).le)
  have htotal : 1 + cNorm (closedBall a ρ) m (fun w ↦ stressJet F w.1) +
      cNorm (closedBall a ρ) (m + 1) v ≤
      (1 + 2 * A m) * (1 + cNorm K (m + 2) F + cNorm (closedBall a ρ) (m + 1) v) := by
    have := hA m
    have := cNorm_nonneg K (m + 2) F
    have := cNorm_nonneg (closedBall a ρ) (m + 1) v
    dsimp only [Function.comp_def] at hJhigh
    nlinarith
  exact hout.trans ((mul_le_mul_of_nonneg_left htotal (hC m).le).trans_eq (by ring))

end JanetCartan.RawPrimary.CorrectionBounds
