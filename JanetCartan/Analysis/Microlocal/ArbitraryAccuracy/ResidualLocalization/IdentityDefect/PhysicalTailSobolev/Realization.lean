module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalTailSobolev.Kernel
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.BoundedLocalizers
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.SourceCut

/-!
# Identification with the same bounded right localizer

The checked compact-symbol constructor supplies a left/right adjoint pair.
Density identifies any supplied left realization with that constructor, so
the physical-tail estimate applies to the SAME adjoint used by
`actualAngularPDO_sub_identity_comp_rightLocalizer_eq_tails`. No operator
estimate or Sobolev regularity is used for this identification.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Filter

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect

open FourierIntegral FiniteChain.Graph LowBounds

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- A supplied bounded left realization has the literal right-localizer
adjoint on every L² input. The actual producer is
`exists_bounded_physicalLocalizers`; compact-test density proves uniqueness
with the supplied `M`. Consumer: the SAME `M.adjoint` in both terminal
physical tails (`app:ch_regular:eq:resolved-angular-tail`). -/
theorem rightLocalizer_adjoint_ae_of_leftLocalizer
    {ρ : ℝ} (hρ : ρ ≠ 0) (mi : LocalizerSymbol n)
    (hi : Continuous mi) (his : HasCompactSupport mi) (M : H →L[ℂ] H)
    (hM : ∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → M u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) :
    ∀ u : H, M.adjoint u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x) := by
  obtain ⟨M₀, hleft, hright⟩ :=
    EvolutionIntegratedLocalization.exists_bounded_physicalLocalizers (q := r) hρ mi hi his
  have he : M = M₀ := by
    apply DFunLike.ext'
    apply denseRange_graphTestToLp.equalizer M.continuous M₀.continuous
    funext u
    have hint (i : Fin r) : Integrable (fun y ↦ graphTestToLp u y i) := by
      have hiu := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) i).integrable_comp
        (u.property.1.continuous.integrable_of_hasCompactSupport (μ := volume) u.property.2)
      apply hiu.congr
      filter_upwards [(graphTest_memLp u).coeFn_toLp] with y hy
      exact (congrArg (fun z : V ↦ z i) hy).symm
    exact Lp.ext ((hM _ hint).trans (hleft _ hint).symm)
  simpa only [he] using hright

/-- The all-data literal action supplied by the bounded-localizer
constructor agrees with the smooth representative on graph tests.
Consumer: `signedRightLocalizerPhysicalTail_graphTest_action`
(`app:ch_regular:eq:chain-tail`). -/
theorem rightLocalizer_graphTest_action_of_ae
    (ρ : ℝ) (mi : LocalizerSymbol n) (R : H →L[ℂ] H)
    (hR : ∀ u : H, R u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x))
    (u : graphTestSpace n r) :
    R (graphTestToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (rightLocalizer ρ mi (fun y ↦ (u.val y).ofLp) x) := by
  refine (hR _).trans (.of_forall (fun x ↦ ?_))
  apply congrArg (WithLp.toLp 2)
  unfold rightLocalizer graphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  apply integral_congr_ae
  filter_upwards [(graphTest_memLp u).coeFn_toLp] with y hy
  change graphTestToLp u y = u.val y at hy
  rw [hy]

/-- The multiplier defect composed with the original right localizer has
the literal signed physical-tail kernel on the dense graph tests. The
source variable stays inside the right symbol, and the physical Fourier
normalization is unchanged (`app:ch_regular:eq:resolved-angular-tail`). -/
theorem signedRightLocalizerPhysicalTail_graphTest_action
    {ρ : ℝ} (hρ : ρ ≠ 0) (mi : LocalizerSymbol n)
    (hi : Continuous mi) (his : HasCompactSupport mi)
    (χ : E → ℝ) (hχ : Continuous χ) (hχb : ∀ x, ‖χ x‖ ≤ 1)
    (R : H →L[ℂ] H)
    (hR : ∀ u : graphTestSpace n r, R (graphTestToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (rightLocalizer ρ mi (fun y ↦ (u.val y).ofLp) x))
    (u : graphTestSpace n r) :
    ((sourceCutMultiplier χ hχ hχb - 1).comp R) (graphTestToLp u) =ᵐ[volume]
      fun x ↦ ∫ y, signedRightLocalizerPhysicalTailKernel ρ mi χ x y • u.val y := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)
  have hint (x : E) :
      (∫ y, signedRightLocalizerPhysicalTailKernel ρ mi χ x y • u.val y) =
        ((χ x - 1 : ℝ) : ℂ) •
          (WithLp.toLp 2 (rightLocalizer ρ mi (fun y ↦ (u.val y).ofLp) x) : V) := by
    have he := e.symm.integral_comp_comm (μ := volume)
      (fun y ↦ signedRightLocalizerPhysicalTailKernel ρ mi χ x y • (u.val y).ofLp)
    change (∫ y, signedRightLocalizerPhysicalTailKernel ρ mi χ x y • u.val y) =
      e.symm (∫ y, signedRightLocalizerPhysicalTailKernel ρ mi χ x y • (u.val y).ofLp) at he
    rw [he, signedRightLocalizerPhysicalTailKernel_integral hρ mi hi his χ
      (fun y ↦ (u.val y).ofLp)
      (e.continuous.comp u.property.1.continuous), map_smul]
    rfl
  change (sourceCutMultiplier χ hχ hχb (R (graphTestToLp u)) - R (graphTestToLp u)) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_sub (sourceCutMultiplier χ hχ hχb (R (graphTestToLp u)))
      (R (graphTestToLp u)),
    sourceCutMultiplier_coeFn χ hχ hχb (R (graphTestToLp u)), hR u] with x hx hc hr
  rw [hx, Pi.sub_apply, hc, hr, hint]
  rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
