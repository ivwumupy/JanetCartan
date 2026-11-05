module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReservedAlgebraicSymbol.NormalizedGerms
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReservedAlgebraicSymbol.MaskProducts
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.ComparableCarrier
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.PhysicalCutoff.Multiplier
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.Diagonal
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterPhase.AmplitudeBudgets

/-!
# Reserved profiles of the literal selected algebraic full amplitude

The original output and source masks, doubled radial multiplier, and annular
selector stay inside the actual selected symbol. The output mask puts the
entire source product on its proved plateau. Outside the closed mask supports
the full amplitude is locally zero. On those supports the retained inverse
and original coefficient profiles prove every joint jet bound.

Consumer: the primitive diagonal PDO estimates of
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open Set Metric Filter Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.FixedDomainInverse.ReservedAlgebraicSymbol

open ArbitraryAccuracy.SelectedLocalization ArbitraryAccuracy.ResidualLocalization
open RegularSector RegularSector.Characteristic ActualCarriers
open RegularSector.Characteristic.AlgebraicChart RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.RootFamily RegularSector.Characteristic.EvolutionIntegral
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAlgebraic RegularSector.FinitePdo RegularSector.FiniteAssembly
open RegularSector.FiniteEvolution.PhysicalCutoff
open FourierIntegral FourierIntegral.PrimitiveProfiles FiniteChain.Retarded.KernelDecay
open ResponseTransfer

variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "V" => E × E × E
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- The actual selected algebraic full amplitude has global joint smoothness
and the reserved profile `L^(k+1-Rstar)`. This includes both the solver symbol
and its full physical residual. The supplied inverse family, original masks,
and complete source product are unchanged. The only varying analytic inputs
are the ORIGINAL reserved profiles of `Q` and `B`
(`app:ch_response:eq:direct-envelope-profile`, `energy-complete-residual`). -/
theorem exists_selected_algebraic_forward_reserved_profiles
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
    (π : E → ℝ) (hπ : ContDiff ℝ ∞ π) (hcπ : HasCompactSupport π)
    (hzero : (0 : E) ∉ tsupport π)
    (Acoef : ℕ → ℝ) (hAcoef : ∀ k, 0 ≤ Acoef k) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ Rstar : ℕ, 1 ≤ Rstar → ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ →
      ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ Acoef k * L ^ (k-Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ Acoef k * L ^ (k-Rstar)) →
      ∀ (p : f.centers) (o : Fin 2),
        let A : FullAmplitude (d+1) (d+1) := fun y z ξ ↦
          π (ρ⁻¹ • ξ) • orientedMaskedPDOAmplitude false
            (endpointOutputMask f p output) (chartInputMask f p)
            (selectedAlgebraicSymbol f p (2*threshold) Q B o) y z ξ
        let α : V → CMat := normalizedFullAmplitude (ρ • A) ρ
        ContDiff ℝ ∞ α ∧ ∀ k v, ‖iteratedFDeriv ℝ k α v‖ ≤ C k * L ^ (k+1-Rstar) := by
  classical
  have hth : 1 ≤ threshold := f.radialThreshold_ge_one.trans ht
  have htpos : 0 < threshold := zero_lt_one.trans_le hth
  obtain ⟨D, hD, hcore⟩ := exists_selectedCoefficientAlgebraicAction_reserved_profile
    f hΩ hRQ hKΩ hc hdom (tsupport π) hcπ hzero Acoef hAcoef
  let X : f.centers → Set V := fun p ↦ tsupport (endpointOutputMask f p output) ×ˢ
    (tsupport (chartInputMask f p) ×ˢ tsupport π)
  have hX p : IsCompact (X p) := (endpointOutputMask_properties f p ho hoc hos).2.1.prod
    ((chartPhysicalMasks_properties f p).2.2.2.1.prod hcπ)
  let m : f.centers → V → ℂ := fun p v ↦ π v.2.2 •
    (endpointOutputMask f p output v.1 * chartInputMask f p v.2.1)
  have hm p : ContDiff ℝ ∞ (m p) := (hπ.comp contDiff_snd.snd).smul
    (((endpointOutputMask_properties f p ho hoc hos).1.comp contDiff_fst).mul
      ((chartPhysicalMasks_properties f p).2.1.comp contDiff_snd.fst))
  have hmsupport p : tsupport (m p) ⊆ X p := by
    intro v hv
    have hphys := tsupport_smul_subset_right (fun w : V ↦ π w.2.2)
      (fun w : V ↦ endpointOutputMask f p output w.1 * chartInputMask f p w.2.1) hv
    have hfreq := tsupport_smul_subset_left (fun w : V ↦ π w.2.2)
      (fun w : V ↦ endpointOutputMask f p output w.1 * chartInputMask f p w.2.1) hv
    exact ⟨tsupport_comp_subset_preimage _ continuous_fst (tsupport_mul_subset_left hphys),
      tsupport_comp_subset_preimage _ continuous_snd.fst (tsupport_mul_subset_right hphys),
      tsupport_comp_subset_preimage _ continuous_snd.snd hfreq⟩
  let β := fun p ↦ selectedEndpointMultiplier f p threshold
  let Jβ : Set (ℝ × E) := {0} ×ˢ tsupport π
  have hJβ : IsCompact Jβ := isCompact_singleton.prod hcπ
  have hβnorm p k : BoundedNormalizedSeminorm Jβ k (fun w : ℝ × E ↦ β p w.2) :=
    boundedNormalizedSeminorm_physical_dilatedConicMask (f.angularMask_smooth p)
      (f.chart p).index hth hJβ (fun w hw he ↦ hzero (he ▸ hw.2)) k
  let T := fun k ↦ ∑ p, cNorm (X p) k (m p)
  let G := fun k ↦ ∑ p, normalizedSeminorm Jβ k (fun w : ℝ × E ↦ β p w.2)
  have hT k : 0 ≤ T k := Finset.sum_nonneg (fun _ _ ↦ cNorm_nonneg _ _ _)
  have hG k : 0 ≤ G k := Finset.sum_nonneg (fun _ _ ↦ normalizedSeminorm_nonneg _ _ _)
  let C := derivativeConvolution T (derivativeConvolution G D)
  have hC k : 0 ≤ C k := derivativeConvolution_nonneg hT (derivativeConvolution_nonneg hG hD) k
  refine ⟨C, hC, ?_⟩
  intro Rstar hR L ρ hL hρ Q B hQ hB hQr hQp hBp p o A α
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  have hρne : ρ ≠ 0 := hρpos.ne'
  let P : V →L[ℝ] E × E := (ContinuousLinearMap.fst ℝ E (E × E)).prod
    ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E × E)))
  let Pβ : V →L[ℝ] ℝ × E := (0 : V →L[ℝ] ℝ).prod
    ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E × E)))
  have hP : ‖P‖ ≤ 1 := by
    apply P.opNorm_le_bound zero_le_one
    intro v
    change max ‖v.1‖ ‖v.2.2‖ ≤ 1 * ‖v‖
    rw [one_mul]
    exact max_le (norm_fst_le v) ((norm_snd_le v.2).trans (norm_snd_le v))
  have hPβ : ‖Pβ‖ ≤ 1 := by
    apply Pβ.opNorm_le_bound zero_le_one
    intro v
    change max ‖(0 : ℝ)‖ ‖v.2.2‖ ≤ 1 * ‖v‖
    simp only [norm_zero, max_eq_right (norm_nonneg _), one_mul]
    exact (norm_snd_le v.2).trans (norm_snd_le v)
  have haeq (v : V) : α v = ρ • (m p v •
      selectedAlgebraicSymbol f p (2*threshold) Q B o v.1 (ρ • v.2.2)) := by
    change ρ • (π (ρ⁻¹ • (ρ • v.2.2)) •
      ((endpointOutputMask f p output v.1 * chartInputMask f p v.2.1) •
        selectedAlgebraicSymbol f p (2*threshold) Q B o v.1 (ρ • v.2.2))) =
      ρ • ((π v.2.2 • (endpointOutputMask f p output v.1 * chartInputMask f p v.2.1)) •
        selectedAlgebraicSymbol f p (2*threshold) Q B o v.1 (ρ • v.2.2))
    rw [inv_smul_smul₀ hρne, smul_assoc]
  have hlocal (v : V) : ContDiffAt ℝ ∞ α v ∧
      ∀ k, ‖iteratedFDeriv ℝ k α v‖ ≤ C k * L ^ (k+1-Rstar) := by
    have hzeroGerm (he : α =ᶠ[𝓝 v] (0 : V → CMat)) :
        ContDiffAt ℝ ∞ α v ∧ ∀ k, ‖iteratedFDeriv ℝ k α v‖ ≤ C k * L ^ (k+1-Rstar) := by
      refine ⟨contDiffAt_const.congr_of_eventuallyEq he, ?_⟩
      intro k
      rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
      simp only [iteratedFDeriv_zero, Pi.zero_apply, norm_zero]
      exact mul_nonneg (hC k) (pow_nonneg (zero_le_one.trans hL) _)
    by_cases hv : v ∈ X p
    · have hvphys := endpointOutputMask_mem_algebraic_common_ball f p output hos hv.1
      let bρ : E → ℂ := fun ξ ↦ β p (ρ • ξ)
      by_cases hsupport : v.2.2 ∈ tsupport bρ
      · have hGs := contDiffAt_selected_coefficientConicBminus_of_retained_domain
          f p hRQ hKΩ (hc p) (Q (physicalCoordinates (f.chart p).index v.1))
          (hQr (hKΩ hvphys.2)) (hdom p _ (hQr (hKΩ hvphys.2))) v.2.2
          (fun he ↦ hzero (he ▸ hv.2.2))
          (tsupport_selectedEndpointMultiplier_normalized_subset f p htpos hρpos hsupport)
        have hq := hQ.contDiffAt (hΩ.mem_nhds (hKΩ hvphys.2))
        have hb := hB.contDiffAt (hΩ.mem_nhds (hKΩ hvphys.2))
        let F : E × E → CMat := fun w ↦ selectedCoefficientAlgebraicAction f p o
          ((Q (physicalCoordinates (f.chart p).index w.1),
            (fderiv ℝ Q (physicalCoordinates (f.chart p).index w.1),
              B (physicalCoordinates (f.chart p).index w.1))), w.2)
        have hF : ContDiffAt ℝ ∞ F (P v) :=
          contDiffAt_selectedCoefficientAlgebraicAction_of_fields f p o Q B (P v) hq hb hGs
        have hFp := hF.comp v P.contDiff.contDiffAt
        have hFjet j : ‖iteratedFDeriv ℝ j (F ∘ P) v‖ ≤ D j * L ^ (j-(Rstar-1)) := by
          apply (algebraic_norm_iteratedFDeriv_comp_linear_at_le P hF j).trans
          apply (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg P) hP)).trans
          simpa only [show j-(Rstar-1) = j+1-Rstar by omega] using
            hcore Rstar hR L hL Q B hQ hB hQr hQp hBp p o threshold ρ htpos hρpos
              (P v) hvphys.2 hv.2.2 hsupport j
        have hbs : ContDiff ℝ ∞ (fun w : V ↦ β p (ρ • w.2.2)) :=
          (selectedEndpointMultiplier_bounds f p threshold).1.comp (contDiff_snd.snd.const_smul ρ)
        have hbj j : ‖iteratedFDeriv ℝ j (fun w : V ↦ β p (ρ • w.2.2)) v‖ ≤
            G j * L ^ (j-(Rstar-1)) := by
          let g : ℝ × E → ℂ := normalizedField ρ (fun w : ℝ × E ↦ β p w.2)
          have hg : ContDiff ℝ ∞ g :=
            (selectedEndpointMultiplier_bounds f p threshold).1.comp (contDiff_snd.const_smul ρ)
          change ‖iteratedFDeriv ℝ j (g ∘ Pβ) v‖ ≤ _
          apply (algebraic_norm_iteratedFDeriv_comp_linear_at_le Pβ hg.contDiffAt j).trans
          apply (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg Pβ) hPβ)).trans
          have hmem : Pβ v ∈ Jβ := ⟨mem_singleton 0, hv.2.2⟩
          apply ((norm_iteratedFDeriv_le_cNorm hJβ (hg.of_le (by simp))
            hmem le_rfl).trans (cNorm_normalizedField_le (hβnorm p j) hρ)).trans
          exact (Finset.single_le_sum (fun p _ ↦ normalizedSeminorm_nonneg Jβ j
            (fun w : ℝ × E ↦ β p w.2)) (Finset.mem_univ p)).trans
              (le_mul_of_one_le_right (hG j) (one_le_pow₀ hL))
        have hmj j : ‖iteratedFDeriv ℝ j (m p) v‖ ≤ T j * L ^ (j-(Rstar-1)) :=
          (norm_iteratedFDeriv_le_cNorm (hX p) ((hm p).of_le (by simp)) hv le_rfl).trans
            ((Finset.single_le_sum (fun p _ ↦ cNorm_nonneg (X p) j (m p)) (Finset.mem_univ p)).trans
              (le_mul_of_one_le_right (hT j) (one_le_pow₀ hL)))
        have hprod j : ‖iteratedFDeriv ℝ j
            (fun w : V ↦ β p (ρ • w.2.2) • F (P w)) v‖ ≤
              derivativeConvolution G D j * L ^ (j-(Rstar-1)) :=
          norm_algebraic_mask_product_reserved_jet_le
            (f := fun w : V ↦ β p (ρ • w.2.2)) (g := fun w : V ↦ F (P w))
            hbs.contDiffAt hFp hG hD hL (Rstar-1) hbj hFjet j
        have hfull j : ‖iteratedFDeriv ℝ j
            (fun w : V ↦ m p w • (β p (ρ • w.2.2) • F (P w))) v‖ ≤
              C j * L ^ (j-(Rstar-1)) :=
          norm_algebraic_mask_product_reserved_jet_le
            (f := m p) (g := fun w : V ↦ β p (ρ • w.2.2) • F (P w))
            (hm p).contDiffAt (hbs.contDiffAt.smul hFp)
            hT (derivativeConvolution_nonneg hG hD) hL (Rstar-1) hmj hprod j
        have he := (selected_algebraic_normalized_eventuallyEq_selectedCoefficientAction
          f p o ht hρpos Q B (P v) hvphys.1 hq hGs).comp_tendsto P.continuous.continuousAt
        have hefull : α =ᶠ[𝓝 v] fun w : V ↦ m p w • (β p (ρ • w.2.2) • F (P w)) := by
          filter_upwards [he] with w hw
          change selectedAlgebraicSymbol f p (2*threshold) Q B o w.1 (ρ • w.2.2) =
            ρ⁻¹ • (β p (ρ • w.2.2) • F (P w)) at hw
          rw [haeq w, hw, smul_comm ρ (m p w), smul_inv_smul₀ hρne]
        refine ⟨((hm p).contDiffAt.smul (hbs.contDiffAt.smul hFp)).congr_of_eventuallyEq hefull, ?_⟩
        intro k
        rw [(hefull.iteratedFDeriv ℝ k).eq_of_nhds]
        simpa only [show k-(Rstar-1) = k+1-Rstar by omega] using hfull k
      · apply hzeroGerm
        have he := (notMem_tsupport_iff_eventuallyEq.mp hsupport).comp_tendsto
          (continuous_snd.snd.continuousAt : ContinuousAt (fun w : V ↦ w.2.2) v)
        filter_upwards [he] with w hw
        rw [haeq w, selected_algebraic_symbol_zero_of_original_multiplier_zero
          f p o threshold Q B w.1 (ρ • w.2.2) hw, smul_zero, smul_zero]
        rfl
    · apply hzeroGerm
      have hmnot : v ∉ tsupport (m p) := fun h ↦ hv (hmsupport p h)
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hmnot] with w hw
      change m p w = 0 at hw
      rw [haeq w, hw, zero_smul, smul_zero]
      rfl
  exact ⟨contDiff_iff_contDiffAt.mpr (fun v ↦ (hlocal v).1), fun k v ↦ (hlocal v).2 k⟩

end JanetCartan.FixedDomainInverse.ReservedAlgebraicSymbol
