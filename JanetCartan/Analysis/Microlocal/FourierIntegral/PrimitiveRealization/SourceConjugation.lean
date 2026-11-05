module
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SupportedConjugation.Pairings
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.SourceCut
/-!
# The exact source commutator of the realized conjugation

The physical source mask preserves the compact smooth Euclidean test domain.
Its canonical-time commutator is the literal `-i ∂χ` multiplication term.
Applying the supported unregularized conjugation to the source-cut test retains
this term after the transport graph, in the order required by
`app:ch_regular_base:eq:actual-global-cutoff`.

`sourceCut_distributional_conjugation` consumes precisely the distributional
identity produced by `SupportedConjugation.exists_supported_twoTerm_distributional_conjugation`.
It is a deduction from that identity; the parent still supplies its actual
transport and primitive profiles. No estimate for the source commutator or its
integrated product is asserted here.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 120000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff SchwartzMap
namespace JanetCartan.FourierIntegral
open LowBounds SupportedConjugation
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "L²" => Lp V 2 (volume : Measure E)

/-- The literal canonical-time source commutator, as a compact smooth test.
Consumer: the source term in `app:ch_regular_base:eq:actual-global-cutoff`. -/
def sourceCutoffTimeCommutatorTest (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (t : Fin n) (u : graphTestSpace n r) : graphTestSpace n r :=
  ⟨fun x ↦ -Complex.I • (partialDeriv (fun y ↦ (χ y : ℂ)) x t • u.val x),
    ((((Complex.ofRealCLM.contDiff.comp hχ).fderiv_right (by simp)).clm_apply
      contDiff_const).smul u.property.1).const_smul (-Complex.I),
    (u.property.2.smul_left (f := fun x ↦ partialDeriv (fun y ↦ (χ y : ℂ)) x t)).smul_left (f := fun _ : E ↦ -Complex.I)⟩

/-- The exact Leibniz identity on the existing test space, retaining
`-i ∂χ` (`app:ch_regular_base:eq:actual-global-cutoff`). -/
theorem sourceTimeTest_sourceCutTest (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (t : Fin n) (u : graphTestSpace n r) :
    sourceTimeTest t (sourceCutTest χ hχ u) =
      sourceCutTest χ hχ (sourceTimeTest t u) + sourceCutoffTimeCommutatorTest χ hχ t u := by
  apply Subtype.ext
  funext x
  change -Complex.I • partialDeriv (fun y ↦ (χ y : ℂ) • u.val y) x t =
    (χ x : ℂ) • (-Complex.I • partialDeriv u.val x t) +
      -Complex.I • (partialDeriv (fun y ↦ (χ y : ℂ)) x t • u.val x)
  have hc : DifferentiableAt ℝ (fun y ↦ (χ y : ℂ)) x := (Complex.ofRealCLM.contDiff.comp hχ).differentiable (by simp) x
  have hu := u.property.1.differentiable (by simp) x
  simp only [partialDeriv, fderiv_fun_smul hc hu, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_add]
  rw [smul_comm (-Complex.I)]

/-- The same source commutator in the actual Euclidean vector L² space.
Consumer: the source-cut unregularized conjugation in
`app:ch_regular_base:eq:actual-global-cutoff`. -/
theorem sourceTimeTest_sourceCutMultiplier (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hb : ∀ x, ‖χ x‖ ≤ 1) (t : Fin n) (u : graphTestSpace n r) :
    graphTestToLp (sourceTimeTest t (sourceCutTest χ hχ u)) =
      sourceCutMultiplier χ hχ.continuous hb (graphTestToLp (sourceTimeTest t u)) +
        graphTestToLp (sourceCutoffTimeCommutatorTest χ hχ t u) := by
  rw [sourceTimeTest_sourceCutTest, map_add, sourceCutMultiplier_graphTestToLp]

private theorem coordinateDistribution_add (f g : L²) :
    coordinateDistribution (f + g) = coordinateDistribution f + coordinateDistribution g := by
  simp only [coordinateDistribution, ← Lp.toTemperedDistributionCLM_apply, map_add]

/-- Source-cut the supported distributional conjugation, retaining the exact
transport graph followed by the source commutator. The input identity is the
conclusion of `SupportedConjugation.exists_supported_twoTerm_distributional_conjugation`.
On its physical plateau the target transition is already absent; the source
term below is retained without a smoothing or vanishing assumption.
Source: `app:ch_regular_base:eq:actual-global-cutoff`.
Consumer: the complete residual assembly of
`app:ch_regular_base:prop:complete-residual`. -/
theorem sourceCut_distributional_conjugation
    (W : Set E) (hW : IsOpen W)
    (A : E → Fin n → Matrix (Fin r) (Fin r) ℂ) (B : E → Matrix (Fin r) (Fin r) ℂ)
    (hA : ∀ j i l, ContDiffOn ℝ ∞ (fun x ↦ A x j i l) W)
    (hB : ∀ i l, ContDiffOn ℝ ∞ (fun x ↦ B x i l) W)
    (T₂ Tᵤ Tᵣ : L² →L[ℂ] L²) (t : Fin n)
    (hconjugation : ∀ (u : graphTestSpace n r) (φ : 𝓢(E, ℂ))
      (hK : HasCompactSupport φ) (hs : tsupport φ ⊆ W) (i : Fin r),
      graphPhysicalDistributionPairing hW A B hA hB
          (coordinateDistribution (T₂ (graphTestToLp u))) φ hK hs i -
        coordinateDistribution (Tᵤ (graphTestToLp (sourceTimeTest t u))) φ i =
        coordinateDistribution (Tᵣ (graphTestToLp u)) φ i)
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hb : ∀ x, ‖χ x‖ ≤ 1)
    (u : graphTestSpace n r) (φ : 𝓢(E, ℂ))
    (hK : HasCompactSupport φ) (hs : tsupport φ ⊆ W) (i : Fin r) :
    let Mχ := sourceCutMultiplier (r := r) χ hχ.continuous hb;
    graphPhysicalDistributionPairing hW A B hA hB
        (coordinateDistribution ((T₂ ∘L Mχ) (graphTestToLp u))) φ hK hs i -
      coordinateDistribution ((Tᵤ ∘L Mχ) (graphTestToLp (sourceTimeTest t u))) φ i =
      coordinateDistribution ((Tᵣ ∘L Mχ) (graphTestToLp u)) φ i +
        coordinateDistribution (Tᵤ (graphTestToLp (sourceCutoffTimeCommutatorTest χ hχ t u))) φ i := by
  have h := hconjugation (sourceCutTest χ hχ u) φ hK hs i
  rw [sourceTimeTest_sourceCutMultiplier χ hχ hb] at h
  simp only [map_add, coordinateDistribution_add, add_apply,
    Pi.add_apply] at h
  dsimp only
  simp only [ContinuousLinearMap.comp_apply]
  rw [sourceCutMultiplier_graphTestToLp χ hχ hb u]
  linear_combination h

end JanetCartan.FourierIntegral
