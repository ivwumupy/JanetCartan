module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.PhysicalAmplitude.Geometry
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.PhysicalAmplitude.Transfer
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.Profiles

/-!
# Physical joint grades of the retained direct residual

The original negative-order conic seminorms give physical joint derivatives
on the explicit domain containing the `Ua` constructed by
`exists_selected_elapsed_physical_carriers`. The same direct residual uses
both original coefficients multiplied by `chartOutputMask`, including the
full zeroth-order coefficient. All constants precede coefficients, slow
scale, source frequency and accuracy.

Consumer: `hauxAmplitudeGrades` in
`ResidualLocalization.exists_completePhysicalResidual_restriction_bound`.
Sources: `app:ch_regular:eq:initial-coefficient-profile`,
`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`, and
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteAssembly RegularSector.FiniteAlgebraic
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.Characteristic RegularSector.Characteristic.ResidualCoordinates
open Characteristic.ConicPhase Characteristic.ConicAmplitude Characteristic.UniformEvolution
open Characteristic.AmplitudeBounds Characteristic.EvolutionIntegral
open Characteristic.EvolutionIntegral.SymbolBudgets Characteristic.EvolutionIntegral.KernelIdentification
open JanetCartan.CharacteristicTransport.CompleteResidual
open PhysicalAmplitude
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Z" => RootState (Euclidean d)
local notation "Mat" => MetricTensor (d+1)

/-- A common profile for the physical joint derivatives of the SAME direct
residual. Its only analytic premises are the original coefficient profiles
and the smoothness, physical column identity, and original conic seminorms
published by `exists_finite_direct_operator_bounds`. The proof recovers the
angular matrix at high radius, transfers all covector derivatives, and
reinstates the literal radial collar and output mask. It uses no quantitative
bound for `selectedBufferedAmplitude` and preserves order minus one with
zero slow-scale offset. The explicit domain contains the geometry producer's
`Ua`, including all evaluation points for both orientations and the doubled
selected multiplier (`app:ch_regular:eq:high-amplitude`,
`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_selected_physicalResidual_profile
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hρb : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (ra rb : f.centers → ℝ) (hra : ∀ p, 0 < ra p) (hab : ∀ p, ra p ≤ rb p)
    (cost : f.centers → ℕ → ℝ) (hcost : ∀ p m, 0 < cost p m)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ Bbase : ℕ → ℝ, (∀ k, 0 ≤ Bbase k) ∧
      ∀ Rstar : ℕ, 10 ≤ Rstar → ∀ L : ℝ, 1 ≤ L →
      ∀ (Q : E → Fin (d+1) → Mat) (B : E → Mat),
      (∀ j, cNorm (closedBall x RQ) j Q ≤ A j * L ^ (j-Rstar)) →
      (∀ j, cNorm (closedBall x RQ) j B ≤ A j * L ^ (j-Rstar)) →
      ∀ (Φ : f.centers → Z × ℝ → Z) (Cchart : f.centers → OpenPartialHomeomorph T T)
        (angular : f.centers → Euclidean d → ℝ),
      let W := fun p j ↦ collared (f.chart p).radialSection (if j=0 then 0 else 1)
        (angular p) (selectedBufferedAmplitude f p Q B (Φ p) (Cchart p) j)
      (∀ p j, ContDiff ℝ ∞ (W p j)) →
      (∀ p, ∀ v : T, (f.chart p).timeMask =ᶠ[𝓝 v.1] (fun _ ↦ 1) →
        ∀ j : Fin (d+1), (fun k ↦ W p 2 v k j) =
          WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
            (fun y k ↦ W p 1 (physicalSlice (coordinateSplit (f.chart p).index)
              v.2.1 v.2.2.2 y) k j)
            ((coordinateSplit (f.chart p).index).symm (v.1, v.2.2.1))) →
      (∀ p j m,
        let e := coordinateSplit (f.chart p).index
        let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
        let J := bufferedJetSet (f.chart p).radialSection z
          ((f.chart p).bufferRadius/2) (ra p) (rb p)
        let a := selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p) j
        BoundedTwoTimeOrderSeminorm (if j=0 then 0 else 1) J m a ∧
          twoTimeOrderSeminorm (if j=0 then 0 else 1) J m a ≤
            cost p m * (1+cNorm (closedBall x RQ) (m+10) Q+
              cNorm (closedBall x RQ) (m+9) B)) →
      ∀ p,
        let c := f.chart p
        let e := coordinateSplit c.index
        let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
        let ε := retainedRadius c.targetRadius c.bufferRadius
        let Ac := fun y i ↦ chartOutputMask f p y • (coefficient c.index Q y i).map Complex.ofReal
        let Bc := fun y ↦ chartOutputMask f p y • (zeroth c.index B y).map Complex.ofReal
        let b := directRetardedAmplitudes Ac Bc
          (selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p) 0)
          (selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p) 1) true
        ∀ w ∈ bufferedBase z ε ×ˢ angularCone c.radialSection z.2.2 ε,
          (1/2 : ℝ) < ‖w.2‖ → ∀ k,
            ‖iteratedFDeriv ℝ k (SymbolBudgets.jointAmplitude b) w‖ ≤
              (1 + ‖w.2‖) ^ (-1 : ℝ) * Bbase k * L ^ k := by
  classical
  obtain ⟨D, hD, hprofile⟩ := exists_selected_amplitude_order_profile f ra rb cost hcost A hA
  have hmasks p := exists_residualMask_profile (chartPhysicalMasks_properties f p).1
    (chartPhysicalMasks_properties f p).2.2.1
  choose H hH hHbound using hmasks
  let z := fun p ↦ ((coordinateSplit (f.chart p).index x).1,
    ((coordinateSplit (f.chart p).index x).2, (coordinateSplit (f.chart p).index p.val.val).2))
  let ε := fun p ↦ retainedRadius (f.chart p).targetRadius (f.chart p).bufferRadius
  let C := fun p ↦ 3 * ra p * (1 + ‖(z p).2.2‖ + ε p)
  have hε p : 0 < ε p := (retainedRadius_bounds
    (f.chart p).targetRadius_pos (f.chart p).bufferRadius_pos).1
  have hC p : 0 ≤ C p := by dsimp only [C]; have := hra p; have := hε p; positivity
  have hnon p k := transferProfile_nonneg (hH p) hD (hC p) k
  refine ⟨fun k ↦ ∑ p, transferProfile (H p) D (C p) k,
    fun k ↦ Finset.sum_nonneg (fun p _ ↦ hnon p k), ?_⟩
  intro Rstar hRstar L hL Q B hQ hB Φ Cchart angular W hW hphysical hbudget p
    c e zp εp Ac Bc b w hw hn k
  have haux := selected_common_smooth_direct_residual f p (hρb p) (hsrcρ p)
    (0 : E → ℝ) (by simp) Q B (W p) (hW p) (hphysical p)
  have he : b = (fun t s y η ↦ chartOutputMask f p (timeSpacePoint t y) •
      W p 2 (t, (s, (y, η)))) := haux.1
  have hd := physical_covector_dilation_bounds c.radialSection zp (hε p)
    (retainedRadius_bounds c.targetRadius_pos c.bufferRadius_pos).2.2 (hra p) (hab p) hw hn
  have hb j := hprofile Rstar hRstar L hL Q B hQ hB Φ Cchart angular hbudget p (2 : Fin 3) j
  have hs : ContDiff ℝ ∞ (jointAmplitude (curryCharacteristicMatrix (W p 2))) :=
    (hW p 2).comp evolutionToCharacteristicPoint.contDiff
  have h := physical_joint_grade_of_retained_seminorm c.radialSection (angular p)
    (selectedBufferedAmplitude f p Q B (Φ p) (Cchart p) 2)
    (chartOutputMask f p) (chartPhysicalMasks_properties f p).1
    (H p) D (hH p) hD (hHbound p)
    (isCompact_bufferedJetSet c.radialSection zp (c.bufferRadius/2) (ra p) (rb p))
    hL hd.1 hd.2.2.1 (norm_pos_iff.mp (by linarith : 0 < ‖w.2‖)) hd.2.2.2.1 hd.2.2.2.2
    hs hb k
  rw [he]
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans hL) _)
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun p _ ↦ hnon p k) (Finset.mem_univ p)) (by positivity)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
