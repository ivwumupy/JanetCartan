module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.ComparableProfiles
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.SelectedPhysicalProfiles
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.NormalizedGerms
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.LocalCalculus
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.PhysicalCutoff.Multiplier
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.Diagonal

/-!
# Noncomparable physical grades from the retained geometric certificates

Restrict the proved comparable grade at unit normalized frequency to physical
slices. This removes the inverse-budget premise of the earlier physical
profile. The same doubled threshold, full symbol, and both masks are retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.Characteristic ActualCarriers
open RegularSector.Characteristic.AlgebraicChart RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.RootFamily RegularSector.Characteristic.EvolutionIntegral
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAlgebraic RegularSector.FinitePdo RegularSector.FiniteAssembly
open RegularSector.FiniteEvolution.PhysicalCutoff
open CharacteristicTransport.CompleteResidual ResidualLocalization FourierIntegral
open FourierIntegral.PrimitiveProfiles FiniteChain.Graph FiniteChain.Graph.KernelEstimates
open FiniteChain.Graph.PhysicalShells FiniteChain.Graph.PhysicalShells.Comparable
open FiniteChain.Graph.PhysicalShells.Noncomparable
open FiniteChain.Graph.KernelEstimates.NoncomparableGeometry FiniteChain.Retarded.KernelDecay
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "V" => JointVariables E
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}

/-- The physical noncomparable grade of the complete selected symbol follows
from the retained geometric certificates alone. No physical inverse budget or
joint-symbol bound remains as an assumption. The original source, full `B`,
both masks and literal adjunction are retained, with order minus one and zero
offset (`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`,
`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_selected_algebraic_noncomparable_profile_of_retained_domain
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
    (threshold : ℝ) (ht : f.radialThreshold ≤ threshold)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hos : tsupport output ⊆ ball x f.physicalRadius)
    (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ Rstar : ℕ, 1 ≤ Rstar → ∀ L ρ : ℝ, 1 ≤ L → 0 < ρ →
      ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ A k * L ^ (k - Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ A k * L ^ (k - Rstar)) →
      ∀ (p : f.centers) (backward low : Bool) j,
      ∀ ξ ∈ normalizedGraphCarrier ρ low j,
      ∀ z ∈ tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p), ∀ k,
        ‖iteratedFDeriv ℝ k (fun w : E × E ↦ orientedMaskedPDOAmplitude backward
          (endpointOutputMask f p output) (chartInputMask f p)
          (selectedAlgebraicSymbol f p (2*threshold) Q B 1) w.1 w.2 (ρ • ξ)) z‖ ≤
            (max 1 (branchRadius low j)) ^ (-1 : ℝ) * C k * L ^ k := by
  classical
  obtain ⟨C, hC, hcmp⟩ := exists_selected_algebraic_comparable_profile
    f hΩ hRQ hKΩ hc hdom threshold ht output ho hoc hos 1 1 zero_lt_one A hA
  refine ⟨fun k ↦ 2*C k, fun k ↦ mul_nonneg (by norm_num) (hC k), ?_⟩
  intro Rstar hR L ρ hL hρ Q B hQ hB hQr hQp hBp p backward low j ξ hξ z hz k
  let c := f.chart p
  let β := selectedEndpointMultiplier f p threshold
  let ζ := ρ • ξ
  let χo := endpointOutputMask f p output
  let χi := chartInputMask f p
  let symbol := selectedAlgebraicSymbol f p (2*threshold) Q B 1
  by_cases hβ : β ζ = 0
  · have he : (fun w : E × E ↦ orientedMaskedPDOAmplitude backward χo χi symbol w.1 w.2 ζ) = 0 := by
      funext w
      have hh := selected_algebraic_symbol_zero_of_multiplier_zero f p threshold Q B w.1 ζ hβ
      change symbol w.1 ζ = 0 at hh
      change orientedMaskedPDOAmplitude backward χo χi symbol w.1 w.2 ζ = (0 : CMat)
      cases backward <;> simp only [orientedMaskedPDOAmplitude, Bool.false_eq_true, ↓reduceIte,
        hh, smul_zero, Matrix.conjTranspose_zero]
    change ‖iteratedFDeriv ℝ k (fun w : E × E ↦ orientedMaskedPDOAmplitude backward χo χi symbol w.1 w.2 ζ) z‖ ≤ _
    rw [he]
    have hd0 : iteratedFDeriv ℝ k (0 : (E × E) → CMat) z = 0 :=
      congrFun (show iteratedFDeriv ℝ k (0 : (E × E) → CMat) = 0 from iteratedFDeriv_zero) z
    rw [hd0, norm_zero]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) (mul_nonneg (by norm_num) (hC k)))
      (pow_nonneg (zero_le_one.trans hL) k)
  let r := ‖ζ‖
  have htone : 1 ≤ threshold := f.radialThreshold_ge_one.trans ht
  have htpos : 0 < threshold := zero_lt_one.trans_le htone
  have hr : 1 ≤ r := by
    have hh := physical_multiplier_mem_collar c.index (f.angularMask p) (f.angularMask_support p)
      (fun η hη t ht ↦ c.smul_mem_angularNeighborhood hη ht)
      (hL := (by positivity : 0 < 2*threshold)) (subset_tsupport β hβ)
    change 1 ≤ ‖ζ‖
    linarith [hh.2]
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have hζne : ζ ≠ 0 := norm_pos_iff.mp hrpos
  let u := NormedSpace.normalize ζ
  have hu : ‖u‖ = 1 := NormedSpace.norm_normalize hζne
  have hru : r • u = ζ := NormedSpace.norm_smul_normalize ζ
  let v : V := (z, (u, u, 0))
  have hunitJ : u ∈ frequencyAnnulus (1 / (16*annulusFactor 1 1))
      (4 * max 1 (4*annulusFactor 1 1*1)) := by
    norm_num [frequencyAnnulus, annulusFactor, hu]
  have hv : v ∈ comparableJointCarrier 1 1 1 1
      ((Prod.fst '' (tsupport χo ×ˢ tsupport χi)) ×ˢ frequencyAnnulus
        (1 / (16*annulusFactor 1 1)) (4 * max 1 (4*annulusFactor 1 1*1)))
      (tsupport χo ×ˢ tsupport χi) (frequencyAnnulus 1 1) := by
    refine ⟨⟨hz, hunitJ, ?_, ?_⟩, ⟨⟨z, hz, rfl⟩, hunitJ⟩⟩
    · exact ⟨hu.ge, hu.le⟩
    · norm_num [mem_closedBall, annulusFactor, v]
  have hnorm := hcmp Rstar hR L r hL hr Q B hQ hB hQr hQp hBp p backward k v hv
  have hphys := endpointOutputMask_mem_algebraic_common_ball f p output hos hz.1
  have hus : u ∈ tsupport (fun η ↦ β (r • η)) := subset_tsupport _ (by change β (r • u) ≠ 0; rwa [hru])
  have hGs := contDiffAt_selected_coefficientConicBminus_of_retained_domain
    f p hRQ hKΩ (hc p) (Q (physicalCoordinates c.index z.1))
    (hQr (hKΩ hphys.2)) (hdom p _ (hQr (hKΩ hphys.2))) u
    (by intro he; simp only [he, norm_zero, zero_ne_one] at hu)
    (tsupport_selectedEndpointMultiplier_normalized_subset f p htpos hrpos hus)
  have hcs := contDiffAt_selected_algebraic_normalized_on_output f p ht hrpos Q B (z.1, u) hphys.1
    (hQ.contDiffAt (hΩ.mem_nhds (hKΩ hphys.2)))
    (hB.contDiffAt (hΩ.mem_nhds (hKΩ hphys.2))) hGs
  let F : V → CMat := fun w ↦ orientedMaskedPDOAmplitude backward χo χi symbol w.1.1 w.1.2 (r • w.2.1)
  have hF : ContDiffAt ℝ ∞ F v := by
    have hm : ContDiffAt ℝ ∞ (fun w : V ↦ χo w.1.1 * χi w.1.2) v :=
      (((endpointOutputMask_properties f p ho hoc hos).1.comp contDiff_fst.fst).mul
        ((chartPhysicalMasks_properties f p).2.1.comp contDiff_fst.snd)).contDiffAt
    have hs : ContDiffAt ℝ ∞ (fun w : V ↦ symbol w.1.1 (r • w.2.1)) v :=
      hcs.comp v (contDiffAt_fst.fst.prodMk contDiffAt_snd.fst)
    cases backward
    · exact hm.smul hs
    · let T : CMat ≃ₗᵢ[ℝ] CMat := {
        Matrix.conjTransposeLinearEquiv (Fin (d+1)) (Fin (d+1)) ℝ ℂ with
        norm_map' := Matrix.frobenius_norm_conjTranspose }
      exact T.contDiff.contDiffAt.comp v (hm.smul hs)
  let P : E × E →L[ℝ] V := ContinuousLinearMap.inl ℝ (E × E) (E × E × E)
  have hPnorm : ‖P‖ ≤ 1 := P.opNorm_le_bound zero_le_one (by intro w; simp [P])
  let a : V := (0, (u, u, 0))
  let g : V → CMat := fun w ↦ F (a + w)
  have ha : a + P z = v := by simp [a, P, v]
  have hg : ContDiffAt ℝ ∞ g (P z) := by
    apply (show ContDiffAt ℝ ∞ F (a + P z) from ha.symm ▸ hF).comp (P z)
      (contDiffAt_const.add contDiffAt_id)
  have he : (fun w : E × E ↦ orientedMaskedPDOAmplitude backward χo χi symbol w.1 w.2 ζ) = g ∘ P := by
    funext w
    simp only [g, F, P, a, Function.comp_apply, ContinuousLinearMap.inl_apply,
      Prod.mk_add_mk, zero_add, add_zero, hru]
  have hslice : ‖iteratedFDeriv ℝ k (fun w : E × E ↦ orientedMaskedPDOAmplitude backward
      χo χi symbol w.1 w.2 ζ) z‖ ≤ r⁻¹ * C k * L ^ k := by
    rw [he]
    apply (algebraic_norm_iteratedFDeriv_comp_linear_at_le P hg k).trans
    apply (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg P)
      hPnorm)).trans
    dsimp only [g]
    rw [iteratedFDeriv_comp_add_left, ha]
    simpa only [Real.rpow_neg_one] using hnorm
  have hlower := ((mem_normalizedGraphCarrier_iff hρ.ne' low j ξ).mp hξ).1
  have hmax : max 1 (branchRadius low j) ≤ 2*r :=
    max_le (by linarith) (by have := (graphLower_bounds low j).1; change _ ≤ ‖ρ • ξ‖ at hlower; dsimp [r, ζ]; linarith)
  have hweight : r⁻¹ ≤ 2 * (max 1 (branchRadius low j)) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one, ← div_eq_mul_inv, ← one_div]
    exact (div_le_div_iff₀ hrpos (by positivity)).mpr (by simpa only [one_mul] using hmax)
  exact hslice.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hweight (hC k)) (pow_nonneg (zero_le_one.trans hL) k)).trans_eq (by ring))

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
