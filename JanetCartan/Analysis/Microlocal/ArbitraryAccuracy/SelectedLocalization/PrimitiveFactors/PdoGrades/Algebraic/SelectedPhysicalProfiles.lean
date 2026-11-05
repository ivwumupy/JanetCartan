module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.FirstJetProfile

/-!
# The selected complete physical inverse action has a joint profile

The actual constant-field complement certificates and retained root buffers
construct smooth compact coefficient/first-jet/full-covector functions. The
original profiles place the varying field in those compact sets. No joint
symbol estimate is a premise. This is the remaining physical-action factor
of the comparable branch-three symbol in `CompleteFactor`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.Characteristic ActualCarriers
open RegularSector.Characteristic.AlgebraicChart
open RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.RootFamily
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAlgebraic RegularSector.FinitePdo
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "CMat" => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
local notation "Coeff" => Fin (d + 1) → Mat
local notation "Jet" => Coeff × ((E →L[ℝ] Coeff) × Mat)
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}

/-- The complete physical coefficient action on the SAME selected inverses
has joint `C_k L^k` grades on the actual normalized multiplier support.
Both `Q` and the full `B` have their ORIGINAL coefficient profiles; `Rstar ≥ 1`
absorbs the first derivative and the final offset is zero. Constants precede
`Q,B,Rstar,L,ρ,threshold`. The only domain input is the actual retained
constant-field complement certificate at the original doubled threshold,
produced by `exists_finite_physical_evolution_and_algebraic_inverse`.
Consumer: multiplication by the two physical masks and the literal Fourier
multiplier in the branch-three comparable grade (`high-amplitude`,
`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_selected_coefficientPhysicalAction_joint_profile
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hΩ : IsOpen Ω) (hRQ : 0 ≤ RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (hc : ∀ p : f.centers,
      let c := f.chart p
      RootBuffer c.index c.row c.col A₀ p.val.val c.root c.coefficientRadius c.rootRadius
        c.minorGap c.transportGap)
    (hdom : ∀ p : f.centers, ∀ A' : Coeff, A' ∈ closedBall A₀ f.coefficientRadius →
      let c := f.chart p
      (physicalCoordinates c.index ⁻¹' Ω) ×ˢ
        (normalizeCovector c.radialSection '' tsupport
          (selectedEndpointMultiplier f p f.radialThreshold)) ⊆
        complementDomain c.index (fun _ : E ↦ A')
          (fieldRoot (coordinateSplit c.index) (fun _ : E ↦ A') c.root) c.row c.col
          (normalizedRootDomain c))
    (J : Set E) (hJ : IsCompact J) (hzero : (0 : E) ∉ J)
    (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ Rstar : ℕ, 1 ≤ Rstar → ∀ L : ℝ, 1 ≤ L →
      ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ A k * L ^ (k - Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ A k * L ^ (k - Rstar)) →
      ∀ (p : f.centers) (threshold ρ : ℝ), 0 < threshold → 0 < ρ →
      ∀ v : E × E, physicalCoordinates (f.chart p).index v.1 ∈ closedBall x RQ →
        v.2 ∈ J → v.2 ∈ tsupport (fun ξ ↦ selectedEndpointMultiplier f p threshold (ρ • ξ)) →
      ∀ k, ‖iteratedFDeriv ℝ k (fun w : E × E ↦
        coefficientConicPhysicalAction (f.chart p).radialSection (f.chart p).index
          (f.chart p).row (f.chart p).col (f.chart p).root
          ((Q (physicalCoordinates (f.chart p).index w.1),
            (fderiv ℝ Q (physicalCoordinates (f.chart p).index w.1),
              B (physicalCoordinates (f.chart p).index w.1))), w.2)) v‖ ≤ C k * L ^ k := by
  classical
  let S : f.centers → Set (Jet × E) := fun p ↦
    (closedBall A₀ f.coefficientRadius ×ˢ
      (closedBall (0 : E →L[ℝ] Coeff) (A 1) ×ˢ closedBall (0 : Mat) (A 0))) ×ˢ
      (J ∩ tsupport (selectedAlgebraicAngularLift f p))
  have hS p : IsCompact (S p) :=
    ((isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod
      (isCompact_closedBall _ _))).prod (hJ.inter_right (isClosed_tsupport _))
  have hs p z (hz : z ∈ S p) : ContDiffAt ℝ ∞
      (coefficientConicPhysicalAction (f.chart p).radialSection (f.chart p).index
        (f.chart p).row (f.chart p).col (f.chart p).root) z :=
    contDiffAt_coefficientConicPhysicalAction _ _ _ _ _ z
      (contDiffAt_selected_coefficientConicBminus_of_retained_domain f p hRQ hKΩ (hc p)
        z.1.1 hz.1.1 (hdom p z.1.1 hz.1.1) z.2 (fun he ↦ hzero (he ▸ hz.2.1)) hz.2.2)
  choose D hD hb using fun p ↦ exists_coefficientFirstJet_joint_profile (f.chart p).index
    (coefficientConicPhysicalAction (f.chart p).radialSection (f.chart p).index
      (f.chart p).row (f.chart p).col (f.chart p).root) (hS p) (hs p) A hA
  refine ⟨fun k ↦ ∑ p, D p k, fun k ↦ Finset.sum_nonneg (fun p _ ↦ hD p k), ?_⟩
  intro Rstar hR L hL Q B hQ hB hQr hQp hBp p threshold ρ ht hρ v hv hJv hβ k
  have hdf : ‖fderiv ℝ Q (physicalCoordinates (f.chart p).index v.1)‖ ≤ A 1 := by
    have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall x RQ)
      (fun y hy ↦ (hQ.contDiffAt (hΩ.mem_nhds (hKΩ hy))).of_le
        (show (1 : ℕ∞ω) ≤ ∞ by simp)) hv (le_refl 1)
    rw [norm_iteratedFDeriv_one] at hh
    exact hh.trans (by simpa only [Nat.sub_eq_zero_of_le hR, pow_zero, mul_one] using hQp 1)
  have hBv : ‖B (physicalCoordinates (f.chart p).index v.1)‖ ≤ A 0 := by
    have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall x RQ)
      (fun y hy ↦ (hB.contDiffAt (hΩ.mem_nhds (hKΩ hy))).of_le
        (show (0 : ℕ∞ω) ≤ ∞ by simp)) hv (le_refl 0)
    rw [norm_iteratedFDeriv_zero] at hh
    exact hh.trans (by simpa only [Nat.zero_sub, pow_zero, mul_one] using hBp 0)
  have hmem : ((Q (physicalCoordinates (f.chart p).index v.1),
      (fderiv ℝ Q (physicalCoordinates (f.chart p).index v.1),
        B (physicalCoordinates (f.chart p).index v.1))), v.2) ∈ S p := by
    refine ⟨⟨hQr (hKΩ hv), ?_, ?_⟩, hJv,
      tsupport_selectedEndpointMultiplier_normalized_subset f p ht hρ hβ⟩
    · simpa only [mem_closedBall, dist_zero_right] using hdf
    · simpa only [mem_closedBall, dist_zero_right] using hBv
  exact (hb p Rstar hR L hL x RQ Ω hΩ hKΩ Q B hQ hB hQp hBp v hv hmem k).trans
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun p _ ↦ hD p k)
      (Finset.mem_univ p)) (pow_nonneg (zero_le_one.trans hL) k))

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
