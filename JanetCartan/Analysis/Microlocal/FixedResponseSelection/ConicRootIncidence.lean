module

public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.FullSourceIncidence

/-!
# Conic root matching for every original source incidence

A solver angular mask can meet several fixed source families and arbitrary
positive radii on the same ray. Extend the original retained root's unique
characteristic neighborhood by its radial normalization. Then the actual full
momentum comparison gives a single threshold on the entire compact source
incidence set. No primary patch or inverse is selected or identified.
Consumer: the same-family stationary selection for
`app:ch_response:eq:fixed-factor-transfer` and
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedFactors
open ActualCarriers RegularSector.Characteristic RootFamily AlgebraicChart
open CompatibleResponse
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Coeff" => Fin (d + 1) → MetricTensor (d + 1)

/-- Extend the characteristic neighborhood of the SAME retained root along
all positive covector rays. Matching is stated at its original radial section,
so no source covector is required to equal the chart anchor. This is the
algebraic input for every source incident to a selected angular mask
(`app:ch_response:eq:response-exact-phase`). -/
theorem exists_retained_root_conic_characteristic_neighborhood
    {i r c : Fin (d + 1)} {A₀ : Coeff} {ξ : E} (hξ : ξ ≠ 0)
    (ℓ : Euclidean d →L[ℝ] ℝ) (hℓ : ℓ (coordinateSplit i ξ).2 = 1)
    {H : Coeff × Euclidean d → ℝ} {ε L μ ν : ℝ}
    (hε : 0 < ε) (hL : 0 < L) (hμ : 0 < μ) (hν : 0 < ν)
    (hH : RootBuffer i r c A₀ ξ H ε L μ ν) :
    ∃ V : Set (Coeff × E), IsOpen V ∧ (A₀, ξ) ∈ V ∧
      (∀ p ∈ V, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ V) ∧
      ∀ p ∈ V,
        0 < ℓ (coordinateSplit i p.2).2 ∧
        p.1 ∈ ball A₀ ε ∧
        (ℓ (coordinateSplit i p.2).2)⁻¹ • (coordinateSplit i p.2).2 ∈
          ball (coordinateSplit i ξ).2 (min ε L) ∧
        (determinant p.1 p.2 = 0 ↔
          H (p.1, (ℓ (coordinateSplit i p.2).2)⁻¹ • (coordinateSplit i p.2).2) =
            (ℓ (coordinateSplit i p.2).2)⁻¹ * (coordinateSplit i p.2).1) := by
  obtain ⟨W, hW, hbase, hmatch⟩ :=
    exists_retained_root_characteristic_neighborhood hξ hε hL hμ hν hH
  let e := coordinateSplit i
  let R : Coeff × E → ℝ := fun p ↦ ℓ (e p.2).2
  let N : Coeff × E → Coeff × E := fun p ↦ (p.1, (R p)⁻¹ • p.2)
  let A : Set (Coeff × E) := {p | 0 < R p}
  have hR : Continuous R := ℓ.continuous.comp (e.continuous.comp continuous_snd).snd
  have hA : IsOpen A := isOpen_lt continuous_const hR
  have hN : ContinuousOn N A := by
    intro p hp
    exact (continuousAt_fst.prodMk
      ((hR.continuousAt.inv₀ hp.ne').smul continuousAt_snd)).continuousWithinAt
  refine ⟨A ∩ N ⁻¹' W, hN.isOpen_inter_preimage hA hW, ?_, ?_, ?_⟩
  · change 0 < ℓ (e ξ).2 ∧ (A₀, (ℓ (e ξ).2)⁻¹ • ξ) ∈ W
    simpa only [e, hℓ, inv_one, one_smul] using And.intro zero_lt_one hbase
  · intro p hp t ht
    have hRt : R (p.1, t • p.2) = t * R p := by
      simp only [R, map_smul, Prod.smul_snd, smul_eq_mul]
    refine ⟨show 0 < R (p.1, t • p.2) by rw [hRt]; exact mul_pos ht hp.1, ?_⟩
    have heq : N (p.1, t • p.2) = N p := by
      dsimp only [N]
      rw [hRt, mul_inv_rev, smul_smul]
      congr 2
      field_simp
    change N (p.1, t • p.2) ∈ W
    rw [heq]
    exact hp.2
  · intro p hp
    have hm := hmatch (N p) hp.2
    have hnonzero : (R p)⁻¹ ^ (d + 1) ≠ 0 := pow_ne_zero _ (inv_ne_zero hp.1.ne')
    have hdet : determinant p.1 ((R p)⁻¹ • p.2) = 0 ↔ determinant p.1 p.2 = 0 := by
      rw [determinant_smul, mul_eq_zero_iff_left hnonzero]
    refine ⟨hp.1, hm.2.1.1, ?_, ?_⟩
    · simpa only [N, R, e, map_smul, Prod.smul_snd] using hm.2.1.2
    · simpa only [N, R, e, map_smul, Prod.smul_snd, Prod.smul_fst, smul_eq_mul]
        using hdet.symm.trans hm.2.2

end JanetCartan.ResponseTransfer.RetainedFactors

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

/-- The original full source satisfies the SAME retained root equation on
any entire compact incidence set in the constructed conic neighborhood. One
coefficient threshold precedes the current field and all source labels. The
homogeneity input is precisely the primitive field-root projection of
`UniformProtectionEvolution`; no stationary map or envelope is assumed.
The original phase, independent free covectors and their radial ranges remain
unchanged (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_uniform_full_source_conic_root_domain
    (hframe : closedBall (0 : E) T.data.localReference.stateRadius ⊆ U)
    {i row col : Fin (d + 1)} {ξ : E} (hξ : ξ ≠ 0)
    (ℓ : Euclidean d →L[ℝ] ℝ) (hℓ : ℓ (coordinateSplit i ξ).2 = 1)
    {H : Coeff × Euclidean d → ℝ} {ε L μ ν : ℝ}
    (hε : 0 < ε) (hL : 0 < L) (hμ : 0 < μ) (hν : 0 < ν)
    (hH : RootBuffer i row col (cubeStress (d + 1)) ξ H ε L μ ν) :
    ∃ V : Set (Coeff × E), IsOpen V ∧ (cubeStress (d + 1), ξ) ∈ V ∧
      (∀ p ∈ V, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ V) ∧
      ∀ J : Set (E × Param), IsCompact J → J ⊆ domain T →
        (∀ w ∈ J, (cubeStress (d + 1), T.reference.covector (0, w.2.2)) ∈ V) →
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
          let θ := gradient (fun v ↦ T.fullSourcePhaseInCoordinates i Q v w.2) y
          spacetimeRootState (y, θ) ∈
            fieldDomain (coordinateSplit i) Ω ℓ (coordinateSplit i ξ).2 ε ∧
          rootSuspension (fieldRoot (coordinateSplit i) Q.1 H) (y, θ) = 0 := by
  obtain ⟨V, hV, hbase, hcone, hmatch⟩ :=
    exists_retained_root_conic_characteristic_neighborhood hξ ℓ hℓ hε hL hμ hν hH
  refine ⟨V, hV, hbase, hcone, ?_⟩
  intro J hJ hJT hJV
  obtain ⟨δ, hδ, hδT, hpair⟩ :=
    T.exists_uniform_full_source_pair_neighborhood hframe hJ hJT hV hJV
  refine ⟨δ, hδ, hδT, ?_⟩
  intro Q hQ Ω hhom w hw hwΩ y θ
  have hgrad : θ = primaryCoordinateChange i (phaseGradient T Q w.1 w.2.2) := by
    dsimp only [θ, y]
    have hwphase : (w.1, w.2.2) ∈ phaseDomain T := hJT hw
    convert T.fullSourcePhaseInCoordinates_gradient i Q (c := w.2)
      (x := primaryCoordinateChange i w.1) (by simpa using hwphase) using 1
    simp
  let e := coordinateSplit i
  let ζ := phaseGradient T Q w.1 w.2.2
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
    hm.2.2.2.mp (phase_characteristic T Q (hJT hw))
  have hactual : H (Q.1 w.1, (e ζ).2) = (e ζ).1 := by
    apply mul_left_cancel₀ (inv_ne_zero ha.ne')
    exact hscale.symm.trans heq
  change θ 0 - fieldRoot e Q.1 H (spacetimeRootState (y, θ)) = 0
  rw [hstate, hgrad]
  simp only [primaryCoordinateChange_apply, timeSpacePoint_time, fieldRoot,
    Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply]
  exact sub_eq_zero.mpr hactual.symm

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
