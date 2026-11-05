module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.FieldProfile
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAlgebraic.InverseBounds

/-!
# Joint inverse profiles on the supplied selected family

Use the retained `RootBuffer` and the actual complement certificate on a
fixed compact set of directions. The coefficient functions are the selected
ones; neither roots nor finite covers are selected again. The actual support
of the complete source product must still be placed in these direction sets
when assembling the branch-three grade of `CompleteFactor`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.Characteristic ActualCarriers
open RegularSector.Characteristic.AlgebraicChart
open RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.RootFamily
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.FiniteMasks.ActualFamily RegularSector.FiniteAlgebraic

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "Coeff" => Fin (d + 1) → Mat
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}

/-- The SAME selected conic inverses have a common joint normalized profile
from the original coefficient profile, with reserve zero and order minus one.
The root input is the retained `RootBuffer`. `hcomp` is the original normalized
complement certificate evaluated on constant coefficient fields in the same
coefficient ball; its producer is
`FiniteAlgebraic.exists_finite_physical_evolution_and_algebraic_inverse`.
The final symbol application still has to prove that its actual normalized
directions belong to `Kξ`, without modifying the fixed doubled threshold.
No joint derivative estimate is an input. Consumer: the inverse factor of
branch three in `ResidualLocalization.exists_completePhysicalResidual_restriction_bound`
(`app:ch_regular:eq:high-amplitude`). -/
theorem exists_selected_conicBminus_joint_profile
    (f : ActualMaskFamily (d := d) Ω x RQ A₀ K M)
    (hΩ : IsOpen Ω) (hKΩ : closedBall x RQ ⊆ Ω)
    (hc : ∀ p : f.centers,
      let c := f.chart p
      RootBuffer c.index c.row c.col A₀ p.val.val c.root c.coefficientRadius c.rootRadius
        c.minorGap c.transportGap)
    (Kξ : f.centers → Set E) (hKξ : ∀ p : f.centers, IsCompact (Kξ p))
    (hpos : ∀ p : f.centers, ∀ ξ : E, ξ ∈ Kξ p → (f.chart p).radialSection (spatialPart ξ) ≠ 0)
    (hcomp : ∀ p : f.centers, ∀ A : Coeff, A ∈ closedBall A₀ f.coefficientRadius →
      ∀ ξ : E, ξ ∈ Kξ p →
      let c := f.chart p
      ((physicalCoordinates c.index).symm x, normalizeCovector c.radialSection ξ) ∈
        complementDomain c.index (fun _ : E ↦ A)
          (fieldRoot (coordinateSplit c.index) (fun _ : E ↦ A) c.root) c.row c.col
          (normalizedRootDomain c))
    (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ (Rstar : ℕ) (L ρ : ℝ), 1 ≤ L → 0 < ρ →
      ∀ Q : E → Coeff, ContDiffOn ℝ ∞ Q Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ A k * L ^ (k - Rstar)) →
      ∀ p : f.centers, ∀ v : E × E, physicalCoordinates (f.chart p).index v.1 ∈ closedBall x RQ →
        v.2 ∈ Kξ p → ∀ k,
        ‖iteratedFDeriv ℝ k (fun w : E × E ↦
          conicBminus (f.chart p).radialSection (f.chart p).index Q
            (fieldRoot (coordinateSplit (f.chart p).index) Q (f.chart p).root)
            (f.chart p).row (f.chart p).col w.1 (ρ • w.2)) v‖ ≤ ρ⁻¹ * C k * L ^ k := by
  classical
  let S : f.centers → Set (Coeff × E) := fun p ↦ closedBall A₀ f.coefficientRadius ×ˢ Kξ p
  have hs (p : f.centers) : IsCompact (S p) := (isCompact_closedBall _ _).prod (hKξ p)
  have hroot (p : f.centers) (v : Coeff × E) (hv : v ∈ S p) :
      ContDiffAt ℝ ∞ (f.chart p).root
        (v.1, spatialPart (normalizeCovector (f.chart p).radialSection v.2)) := by
    have hd := hcomp p v.1 hv.1 v.2 hv.2
    have hcoeff : v.1 ∈ closedBall A₀ (f.chart p).coefficientRadius :=
      closedBall_subset_closedBall (f.coefficientRadius_le p) hv.1
    have hfrequency : spatialPart (normalizeCovector (f.chart p).radialSection v.2) ∈
        closedBall (coordinateSplit (f.chart p).index p.val.val).2
          (min (f.chart p).coefficientRadius (f.chart p).rootRadius) :=
      ball_subset_closedBall hd.1.2
    exact ((hc p).2 (v.1, spatialPart (normalizeCovector (f.chart p).radialSection v.2))
      ⟨hcoeff, hfrequency⟩).1
  have hdomain (p : f.centers) (v : Coeff × E) (hv : v ∈ S p) :
      ((coefficientRootPencil (coordinateSplit (f.chart p).index) (f.chart p).root
          (v.1, spatialPart (normalizeCovector (f.chart p).radialSection v.2)),
        pencil v.1 ((coordinateSplit (f.chart p).index).symm (1, 0))),
          normalizeCovector (f.chart p).radialSection v.2 0 -
            (f.chart p).root (v.1, spatialPart (normalizeCovector (f.chart p).radialSection v.2))) ∈
        minorComplementDomain (f.chart p).row (f.chart p).col :=
    (hcomp p v.1 hv.1 v.2 hv.2).2
  choose D hD hbound using fun p ↦ exists_conicBminus_fieldRoot_joint_profile
    (f.chart p).radialSection (f.chart p).index (f.chart p).row (f.chart p).col
    (f.chart p).root (hs p) (fun v hv ↦ hpos p v.2 hv.2) (hroot p) (hdomain p) A hA
  refine ⟨fun k ↦ ∑ p, D p k, fun k ↦ Finset.sum_nonneg (fun p _ ↦ hD p k), ?_⟩
  intro Rstar L ρ hL hρ Q hQ hQrange hprofile p v hv hξ k
  apply (hbound p Rstar L ρ hL hρ x RQ Ω hΩ hKΩ Q hQ hprofile v hv
    ⟨hQrange (hKΩ hv), hξ⟩ k).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun p _ ↦ hD p k) (Finset.mem_univ p)) (inv_pos.mpr hρ).le)
      (pow_nonneg (zero_le_one.trans hL) k)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
