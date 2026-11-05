module

public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.NegativeSourceIncidence.Phase

/-!
# The supplied conic root on the negative source incidence

Apply the retained simple-root uniqueness theorem at the actual negative
source covector. Homogeneity gives its characteristic equation. The same
supplied root, field and source parameters remain in every conclusion.
Consumer: negative stationary critical values for the reflected residual
letters in `app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse ArbitraryAccuracy
open RegularSector.Characteristic RegularSector.Characteristic.RootFamily
open RegularSector.Characteristic.AlgebraicChart
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open ResponseTransfer.RetainedFactors LeadingWave.FullModulation
variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
local notation "Coeff" => Fin (d + 1) → MetricTensor (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d

/-- The negative of the original full source satisfies the SAME retained root equation on
any entire compact incidence set in the constructed conic neighborhood. One
coefficient threshold precedes the current field and all source labels. The
homogeneity input is precisely the primitive field-root projection of
`UniformProtectionEvolution`; no stationary map or envelope is assumed.
The original phase, independent free covectors and their radial ranges remain
unchanged (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_uniform_negative_full_source_conic_root_domain
    (hframe : closedBall (0 : E) T.data.localReference.stateRadius ⊆ U)
    {i row col : Fin (d + 1)} {ξ : E} (hξ : ξ ≠ 0)
    (ℓ : Euclidean d →L[ℝ] ℝ) (hℓ : ℓ (coordinateSplit i ξ).2 = 1)
    {H : Coeff × Euclidean d → ℝ} {ε L μ ν : ℝ}
    (hε : 0 < ε) (hL : 0 < L) (hμ : 0 < μ) (hν : 0 < ν)
    (hH : RootBuffer i row col (cubeStress (d + 1)) ξ H ε L μ ν) :
    ∃ V : Set (Coeff × E), IsOpen V ∧ (cubeStress (d + 1), ξ) ∈ V ∧
      (∀ p ∈ V, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ V) ∧
      ∀ J : Set (E × Param), IsCompact J → J ⊆ domain T →
        (∀ w ∈ J, (cubeStress (d + 1), -T.reference.covector (0, w.2.2)) ∈ V) →
      ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧
        ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
        ∀ Ω : Set E,
          (∀ w ∈ fieldDomain (coordinateSplit i) Ω ℓ (coordinateSplit i ξ).2 ε,
            ∀ t : ℝ, 0 < t →
              fieldRoot (coordinateSplit i) Q.1 H (w.1, (w.2.1, t • w.2.2)) =
                t * fieldRoot (coordinateSplit i) Q.1 H w) →
        ∀ w ∈ J, w.1 ∈ Ω →
          let y := primaryCoordinateChange i w.1
          let θ := gradient (fun v ↦ T.negativeFullSourcePhaseInCoordinates i Q v w.2) y
          spacetimeRootState (y, θ) ∈
            fieldDomain (coordinateSplit i) Ω ℓ (coordinateSplit i ξ).2 ε ∧
          rootSuspension (fieldRoot (coordinateSplit i) Q.1 H) (y, θ) = 0 := by
  obtain ⟨V, hV, hbase, hcone, hmatch⟩ :=
    exists_retained_root_conic_characteristic_neighborhood hξ ℓ hℓ hε hL hμ hν hH
  refine ⟨V, hV, hbase, hcone, ?_⟩
  intro J hJ hJT hJV
  obtain ⟨δ, hδ, hδT, hpair⟩ :=
    T.exists_uniform_negative_full_source_pair_neighborhood hframe hJ hJT hV hJV
  refine ⟨δ, hδ, hδT, ?_⟩
  intro Q hQ Ω hhom w hw hwΩ y θ
  have hgrad : θ = primaryCoordinateChange i ((-phaseGradient T Q w.1 w.2.2)) := by
    dsimp only [θ, y]
    have hwphase : (w.1, w.2.2) ∈ phaseDomain T := hJT hw
    convert T.negativeFullSourcePhaseInCoordinates_gradient i Q (c := w.2)
      (x := primaryCoordinateChange i w.1) (by simpa using hwphase) using 1
    simp
  let e := coordinateSplit i
  let ζ := (-phaseGradient T Q w.1 w.2.2)
  let a := ℓ (e ζ).2
  have hm := hmatch _ (hpair Q hQ w hw)
  have ha : 0 < a := hm.1
  have hnorm : a⁻¹ • (e ζ).2 ∈ ball (e ξ).2 ε :=
    ball_subset_ball (min_le_left _ _) hm.2.2.1
  have hstate : spacetimeRootState (y, θ) =
      ((e w.1).1, ((e w.1).2, (e ζ).2)) := by
    rw [hgrad]
    exact spacetimeRootState_primaryCoordinateChange i w.1 ζ
  have hmem : spacetimeRootState (y, θ) ∈ fieldDomain e Ω ℓ (e ξ).2 ε := by
    rw [hstate]
    exact ⟨ha, by simpa using hwΩ, hnorm⟩
  refine ⟨hmem, ?_⟩
  have hscale := hhom _ hmem a⁻¹ (inv_pos.mpr ha)
  rw [hstate] at hscale
  simp only [fieldRoot, e, Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply] at hscale
  have heq : H (Q.1 w.1, a⁻¹ • (e ζ).2) = a⁻¹ * (e ζ).1 :=
    hm.2.2.2.mp (T.negative_full_source_characteristic Q (hJT hw))
  have hactual : H (Q.1 w.1, (e ζ).2) = (e ζ).1 := by
    apply mul_left_cancel₀ (inv_ne_zero ha.ne')
    exact hscale.symm.trans heq
  change θ 0 - fieldRoot e Q.1 H (spacetimeRootState (y, θ)) = 0
  rw [hstate, hgrad]
  simp only [primaryCoordinateChange_apply, timeSpacePoint_time, fieldRoot,
    Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply]
  exact sub_eq_zero.mpr hactual.symm

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
