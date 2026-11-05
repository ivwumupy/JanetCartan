module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.ProtectionCertificates.FlowData
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.ProtectionCertificates.Geometry
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks

/-!
# Protection geometry of the retained finite family

These are deductions from the certificates returned by
`exists_finite_direct_operator_bounds_with_protection_certificates` on its
same roots and flows. The consumer is `exists_selectedSector_nested_proof_masks`
for `app:ch_regular:lem:finite-chain` and `app:ch_regular:thm:no-return`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedSectorProtection
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.Characteristic RegularSector.Characteristic.RootFamily
open RegularSector.Characteristic.AlgebraicChart RegularSector.Characteristic.UniformAmplitudes
open RegularSector.FiniteAssembly ProtectedMasks ActualCarriers
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "TP" => TwoTimePoint (Euclidean d)

/-- The original physical support is strictly inside its coefficient ball.
This places the fixed source cutoff in the initialized source ball when the
finite constructor is applied there (`app:ch_regular:thm:no-return`). -/
theorem selected_physical_core_subset_coefficient_ball
    (f : ActualMaskFamily Ω x RQ A₀ K M) :
    ball x f.physicalRadius ⊆ ball x RQ := by
  let v : E := (4 * f.physicalRadius) • EuclideanSpace.single 0 1
  have hr : 0 ≤ 4 * f.physicalRadius := mul_nonneg (by norm_num) f.physicalRadius_pos.le
  have hv : ‖v‖ = 4 * f.physicalRadius := by
    simp [v, norm_smul, EuclideanSpace.single, PiLp.norm_single, Real.norm_of_nonneg hr]
  have hy : x + v ∈ closedBall x (4 * f.physicalRadius) := by
    simp [mem_closedBall, dist_eq_norm, hv]
  have hRQ := f.physicalBall_coefficientDomain hy
  have hbound : 4 * f.physicalRadius ≤ RQ := by
    simpa [mem_closedBall, dist_eq_norm, hv] using hRQ
  exact ball_subset_ball (by linarith [f.physicalRadius_pos])

/-- A positive common normalized speed is selected from the already retained
local constants, before the current coefficient varies. Empty characteristic
families are included (`app:ch_regular:thm:no-return`). -/
theorem exists_selected_common_root_speed
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (T κ G : f.centers → ℝ) (cost : f.centers → ℕ → ℝ)
    (hc : ∀ p, LocalProtectionCertificate (f.chart p) (T p) (κ p) (G p) (cost p)) :
    ∃ κ₀ > (0 : ℝ), ∀ p, κ₀ ≤ κ p := by
  classical
  let D := 1 + ∑ p, (κ p)⁻¹
  have hκ p : 0 < κ p := (hc p).2.1
  have hD : 0 < D := by
    have := Finset.sum_nonneg (fun p (_ : p ∈ Finset.univ) ↦ (inv_pos.mpr (hκ p)).le)
    dsimp only [D]
    linarith
  refine ⟨D⁻¹, inv_pos.mpr hD, ?_⟩
  intro p
  have hp : (κ p)⁻¹ ≤ ∑ j, (κ j)⁻¹ :=
    Finset.single_le_sum (fun j _ ↦ (inv_pos.mpr (hκ j)).le) (Finset.mem_univ p)
  have hh : (κ p)⁻¹ ≤ D := by dsimp only [D]; linarith
  simpa only [one_div, inv_inv] using
    (one_div_le_one_div_of_le (inv_pos.mpr (hκ p)) hh)

/-- The full root-domain inputs of the conic mask construction follow from
its actual selected certificate. In particular the transverse derivative is
nonzero on the whole radially invariant domain, rather than only on the
initial root ball (`app:ch_regular:thm:no-return`). -/
theorem selected_root_mask_primitives
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {T κ G : ℝ} {cost : ℕ → ℝ}
    (hc : LocalProtectionCertificate (f.chart p) T κ G cost)
    (Q : E → Fin (d+1) → MetricTensor (d+1))
    (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph TP TP)
    (hd : SelectedProtectionData (f.chart p) T κ G cost Q Φ C) :
    let c := f.chart p
    let e := coordinateSplit c.index
    let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
    let h := fieldRoot e Q c.root
    let D := fieldDomain e Ω c.radialSection z.2.2 c.coefficientRadius
    closedBall z c.rootRadius ⊆ D ∧
    (∀ v ∈ D, v.2.2 ≠ 0 ∧ determinant (Q (e.symm (v.1, v.2.1)))
      (e.symm (h v, v.2.2)) = 0 ∧
      fderiv ℝ (determinant (Q (e.symm (v.1, v.2.1))))
        (e.symm (h v, v.2.2)) (e.symm (1, 0)) ≠ 0) ∧
    (∀ v ∈ closedBall z c.rootRadius,
      v.2.2 ∈ closedBall z.2.2 c.coefficientRadius ∧
      (1/2 : ℝ) ≤ c.radialSection v.2.2 ∧ |h v| ≤ c.radialSection v.2.2 * G) ∧
    (∀ v ∈ closedBall z c.rootRadius, e.symm (v.1, v.2.1) ∈ closedBall x RQ) ∧
    (∀ v ∈ D, κ ≤ |pencilRootSpeed Q e h v|) := by
  intro c e z h D
  have hstate := hc.2.2.2.2.2.2.2.2.1
  have hroot := hd.1
  refine ⟨fun v hv ↦ (hstate v hv).1, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have hr := hroot v hv
    refine ⟨hr.1, hr.2.1, ?_⟩
    intro hz
    have hs := hr.2.2.2.1
    change κ ≤ |pencilRootSpeed Q e h v| at hs
    simp only [pencilRootSpeed, hz, mul_zero, abs_zero] at hs
    exact (not_le_of_gt hc.2.1) hs
  · intro v hv
    exact ⟨(hstate v hv).2.2.1, (hstate v hv).2.2.2,
      (hroot v (hstate v hv).1).2.2.2.2⟩
  · exact fun v hv ↦ (hstate v hv).2.1
  · exact fun v hv ↦ (hroot v hv).2.2.2.1

/-- Every retained inverse segment, in either orientation and including its
endpoints, lies in the original selected root ball. This discharges the
whole-segment input of the integrated stationary relation and conic gradient
gaps (`app:ch_regular:lem:finite-chain`). -/
theorem selected_inverse_complete_segments
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {T κ G : ℝ} {cost : ℕ → ℝ}
    (Q : E → Fin (d+1) → MetricTensor (d+1))
    (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph TP TP)
    (hd : SelectedProtectionData (f.chart p) T κ G cost Q Φ C) :
    let e := coordinateSplit (f.chart p).index
    let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
    ∀ q ∈ C.target, ∀ u ∈ uIcc q.2.1 q.1,
      twoTimeState Φ (u, (C.symm q).2) ∈ closedBall z (f.chart p).rootRadius ∧
      (twoTimeState Φ (u, (C.symm q).2)).1 = u := by
  intro e z q hq u hu
  exact (hd.2.2.2.2.2.2.2.2.1 q hq u hu).2.2

end JanetCartan.ArbitraryAccuracy.SelectedSectorProtection
