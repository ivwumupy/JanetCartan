module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.Pdo
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.SourceCut

/-!
# Exact fixed-mask identities for the physical PDO

For the restriction costs in `app:ch_regular:lem:finite-chain`, an interior
plateau may be inserted at the original source mask without changing the
operator. Literal adjunction exchanges source and output. These are exact
kernel identities, not additional cutoffs in the operator definition.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization

open FourierIntegral FullLowBounds LowBounds CharacteristicTransport.CompleteResidual

variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ
local notation "H" => Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure E)

/-- Both original masks of the actual PDO fix interior plateaux exactly.
The literal test integral and density prove the identities, including for
the choice definition's zero case. The analytic realization and costs are
separately produced in `Pdo`. Consumer: restriction-scale costs in
`app:ch_regular:eq:chain-tail`. -/
theorem maskedPhysicalPDO_plateau_identities
    (χout χsource : E → ℂ) (c : E → E → Mat)
    (ψout ψsource : E → ℝ) (ho : Continuous ψout) (hs : ContDiff ℝ ∞ ψsource)
    (hob : ∀ x, ‖ψout x‖ ≤ 1) (hsb : ∀ x, ‖ψsource x‖ ≤ 1)
    (hop : ∀ x ∈ tsupport χout, ψout x = 1)
    (hsp : ∀ x ∈ tsupport χsource, ψsource x = 1) :
    (sourceCutMultiplier ψout ho hob).comp (maskedPhysicalPDO χout χsource c) =
        maskedPhysicalPDO χout χsource c ∧
      (maskedPhysicalPDO χout χsource c).comp
        (sourceCutMultiplier ψsource hs.continuous hsb) = maskedPhysicalPDO χout χsource c := by
  classical
  let S : E → E → ℝ := fun x ξ ↦ inner ℝ x ξ
  let A : FullAmplitude (d + 1) q := fun x z ξ ↦ (χout x * χsource z) • c x ξ
  let Q := maskedPhysicalPDO χout χsource c
  by_cases h : ∃ T : H →L[ℂ] H, ∀ u : graphTestSpace (d + 1) q,
      T (graphTestToLp u) =ᵐ[volume] graphTestOutput S A u
  · have ht (u : graphTestSpace (d + 1) q) :
        Q (graphTestToLp u) =ᵐ[volume] graphTestOutput S A u := by
      simpa only [Q, maskedPhysicalPDO, fullGraphOperator, S, A, dite_eq_left h] using h.choose_spec u
    have heo : (fun x z ξ ↦ (ψout x : ℂ) • A x z ξ) = A := by
      funext x z ξ
      by_cases hx : χout x = 0
      · simp [A, hx]
      · simp only [hop x (subset_tsupport χout hx), Complex.ofReal_one, one_smul]
    have hes : (fun x z ξ ↦ (ψsource z : ℂ) • A x z ξ) = A := by
      funext x z ξ
      by_cases hz : χsource z = 0
      · simp [A, hz]
      · simp only [hsp z (subset_tsupport χsource hz), Complex.ofReal_one, one_smul]
    constructor
    · apply DFunLike.coe_injective
      apply denseRange_graphTestToLp.equalizer
        ((sourceCutMultiplier ψout ho hob).comp Q).continuous Q.continuous
      funext u
      apply Lp.ext
      filter_upwards [sourceCutMultiplier_coeFn ψout ho hob (Q (graphTestToLp u)), ht u]
        with x hx hu
      change sourceCutMultiplier ψout ho hob (Q (graphTestToLp u)) x = Q (graphTestToLp u) x
      rw [hx, hu]
      change WithLp.toLp 2 ((ψout x : ℂ) • graphOperator S A (fun y ↦ (u.val y).ofLp) x) = _
      rw [← graphOperator_target_mul S A (fun y ↦ (ψout y : ℂ))
        (fun y ↦ (u.val y).ofLp) x, heo]
      rfl
    · apply DFunLike.coe_injective
      apply denseRange_graphTestToLp.equalizer
        (Q.comp (sourceCutMultiplier ψsource hs.continuous hsb)).continuous Q.continuous
      funext u
      change Q (sourceCutMultiplier ψsource hs.continuous hsb (graphTestToLp u)) = _
      rw [sourceCutMultiplier_graphTestToLp]
      apply Lp.ext
      filter_upwards [ht (sourceCutTest ψsource hs u), ht u] with x hx hy
      change Q (graphTestToLp (sourceCutTest ψsource hs u)) x = Q (graphTestToLp u) x
      rw [hx, hy]
      change WithLp.toLp 2 (graphOperator S A
        (fun y ↦ (ψsource y : ℂ) • (u.val y).ofLp) x) = graphTestOutput S A u x
      rw [congrFun (graphOperator_source_mul S A (fun y ↦ (ψsource y : ℂ))
        (fun y ↦ (u.val y).ofLp)) x, hes]
      rfl
  · have hz : Q = 0 := by
      exact dite_eq_right h
    change (sourceCutMultiplier ψout ho hob).comp Q = Q ∧
      Q.comp (sourceCutMultiplier ψsource hs.continuous hsb) = Q
    simp [hz]

/-- The literal adjoint has the original output plateau on its input.
No mask is commuted through the PDO: this is adjunction of the exact
left-mask identity (`app:ch_regular:lem:finite-chain`). -/
theorem maskedPhysicalPDO_adjoint_source_plateau
    (χout χsource : E → ℂ) (c : E → E → Mat)
    (ψout ψsource : E → ℝ) (ho : ContDiff ℝ ∞ ψout) (hs : ContDiff ℝ ∞ ψsource)
    (hob : ∀ x, ‖ψout x‖ ≤ 1) (hsb : ∀ x, ‖ψsource x‖ ≤ 1)
    (hop : ∀ x ∈ tsupport χout, ψout x = 1)
    (hsp : ∀ x ∈ tsupport χsource, ψsource x = 1) :
    (maskedPhysicalPDO χout χsource c).adjoint.comp
      (sourceCutMultiplier ψout ho.continuous hob) =
        (maskedPhysicalPDO χout χsource c).adjoint := by
  have h := (maskedPhysicalPDO_plateau_identities χout χsource c ψout ψsource
    ho.continuous hs hob hsb hop hsp).1
  have ha := congrArg ContinuousLinearMap.adjoint h
  simpa only [ContinuousLinearMap.adjoint_comp, sourceCutMultiplier_adjoint] using ha

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
