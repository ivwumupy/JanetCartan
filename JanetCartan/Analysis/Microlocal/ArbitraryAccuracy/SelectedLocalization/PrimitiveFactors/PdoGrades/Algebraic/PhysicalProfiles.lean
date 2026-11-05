module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.Diagonal
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAlgebraic.SupportedBudgets.ProductBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicSymbols.WeightedPhysicalBudget
public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.Estimates
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedFactors

/-!
# Physical grades of the entire selected algebraic residual

The physical action differentiates the whole source--inverse product and
retains the full zeroth-order coefficient. The resulting weighted physical
seminorm gives the noncomparable input of `CompleteFactor`, with both masks
and literal adjunction. This does not supply normalized covariable grades.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.Characteristic ActualCarriers
open RegularSector.Characteristic.AlgebraicSymbols
open RegularSector.Characteristic.AlgebraicChart
open RegularSector.Characteristic.AmplitudeBounds RegularSector.FiniteEvolution
open AmplitudeBound
open RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.RootFamily
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAlgebraic RegularSector.FiniteAssembly RegularSector.FinitePdo
open CharacteristicTransport.CompleteResidual ResidualLocalization
open FiniteChain.Graph.PhysicalShells FiniteChain.Graph.PhysicalShells.Noncomparable
open FourierIntegral

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "CMat" => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
local notation "Coeff" => Fin (d + 1) → Mat

/-- Both physical masks, in their original positions, transfer a physical
symbol seminorm to the literal amplitude in either orientation. The constant
precedes the symbol and frequency. Consumer: the noncomparable branch-three
grade in `CompleteFactor` (`app:ch_regular:eq:high-amplitude`). -/
theorem exists_orientedPDO_physical_cNorm_cost
    (χout χsource : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hi : ContDiff ℝ ∞ χsource)
    (hco : HasCompactSupport χout) (hci : HasCompactSupport χsource)
    (x : E) (R : ℝ) (hcarrier : tsupport χout ⊆ closedBall x R) :
    ∃ T : ℕ → ℝ, (∀ k, 0 ≤ T k) ∧
      ∀ c : E → E → CMat, ContDiff ℝ ∞ (Function.uncurry c) →
      ∀ backward η k z, z ∈ tsupport χout ×ˢ tsupport χsource →
        ‖iteratedFDeriv ℝ k (fun w : E × E ↦
          orientedMaskedPDOAmplitude backward χout χsource c w.1 w.2 η) z‖ ≤
            T k * cNorm (closedBall x R) k (fun y ↦ c y η) := by
  let K := tsupport χout ×ˢ tsupport χsource
  let m : E × E → ℂ := fun w ↦ χout w.1 * χsource w.2
  have hm : ContDiff ℝ ∞ m := (ho.comp contDiff_fst).mul (hi.comp contDiff_snd)
  let T := fun k ↦ 2 ^ k * cNorm K k m
  refine ⟨T, fun k ↦ mul_nonneg (by positivity) (cNorm_nonneg _ _ _), ?_⟩
  intro c hc backward η k z hz
  have hs : ContDiff ℝ ∞ (fun y ↦ c y η) :=
    hc.comp (contDiff_id.prodMk contDiff_const)
  let P := ContinuousLinearMap.fst ℝ E E
  have hcore : ContDiff ℝ ∞ (fun w : E × E ↦ c w.1 η) := hs.comp P.contDiff
  have hj (j : ℕ) (hj : j ≤ k) :
      ‖iteratedFDeriv ℝ j (fun w : E × E ↦ c w.1 η) z‖ ≤
        cNorm (closedBall x R) k (fun y ↦ c y η) := by
    change ‖iteratedFDeriv ℝ j ((fun y ↦ c y η) ∘ P) z‖ ≤ _
    rw [P.iteratedFDeriv_comp_right hs z (by simp)]
    apply ((iteratedFDeriv ℝ j (fun y ↦ c y η) (P z)).norm_compContinuousLinearMap_le
      (fun _ ↦ P)).trans
    have hp : (∏ _ : Fin j, ‖P‖) ≤ 1 := Finset.prod_le_one₀
      (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ ContinuousLinearMap.norm_fst_le ℝ E E)
    exact (mul_le_of_le_one_right (norm_nonneg _) hp).trans
      (norm_iteratedFDeriv_le_cNorm (isCompact_closedBall _ _)
        (hs.of_le (by simp)) (hcarrier hz.1) hj)
  have hb : ‖iteratedFDeriv ℝ k (fun w : E × E ↦ m w • c w.1 η) z‖ ≤
      T k * cNorm (closedBall x R) k (fun y ↦ c y η) := by
    apply (norm_iteratedFDeriv_smul_le hm hcore z (by simp)).trans
    calc
      _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * cNorm K k m *
          cNorm (closedBall x R) k (fun y ↦ c y η) := by
        apply Finset.sum_le_sum
        intro j hmem
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left
            (norm_iteratedFDeriv_le_cNorm (hco.prod hci) (hm.of_le (by simp)) hz
              (Nat.le_of_lt_succ (Finset.mem_range.mp hmem))) (Nat.cast_nonneg _))
          (hj _ (Nat.sub_le k j)) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (cNorm_nonneg _ _ _))
      _ = _ := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        simp only [T, Nat.cast_pow, Nat.cast_ofNat]
  cases backward
  · exact hb
  · simpa only [orientedMaskedPDOAmplitude, ↓reduceIte,
      norm_iteratedFDeriv_transport_conjTranspose] using hb

/-- The actual graph annulus converts the inhomogeneous order-minus-one
weight to the required negative `branchRadius` weight, including contracting
annuli. No shell summability or kernel bound is assumed
(`app:ch_regular:eq:chain-tail`). -/
theorem algebraic_graph_weight_le {ρ : ℝ} (hρ : ρ ≠ 0)
    (low : Bool) (j : ℕ) {ξ : E} (hξ : ξ ∈ normalizedGraphCarrier ρ low j) :
    (1 + ‖ρ • ξ‖)⁻¹ ≤ 2 * (max 1 (branchRadius low j)) ^ (-1 : ℝ) := by
  have hn := ((mem_normalizedGraphCarrier_iff hρ low j ξ).mp hξ).1
  have hr := (graphLower_bounds low j).1
  have hw : max 1 (branchRadius low j) ≤ 2 * (1 + ‖ρ • ξ‖) :=
    max_le (by linarith [norm_nonneg (ρ • ξ)]) (by linarith)
  have hp : 0 < max 1 (branchRadius low j) := zero_lt_one.trans_le (le_max_left _ _)
  rw [Real.rpow_neg_one]
  apply (mul_le_mul_iff_of_pos_left (show 0 < 1 + ‖ρ • ξ‖ by positivity)).mp
  rw [mul_inv_cancel₀ (by positivity)]
  rw [← mul_assoc]
  apply (le_mul_inv_iff₀ hp).mpr
  simpa only [one_mul, mul_assoc, mul_comm, mul_left_comm] using hw

variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}

/-- Entry three of the actual four-symbol ledger is the complete selected
algebraic residual in either literal masked orientation. Rewriting this
function equality also rewrites its joint and physical derivatives; no
identification of a replacement symbol is needed. Consumer: the branch-three
PDO inputs of `CompleteFactor`
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem selected_algebraic_residual_amplitude_eq
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) (threshold : ℝ)
    (Q : E → Coeff) (B : E → Mat) (W₁ : TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (backward : Bool) :
    orientedMaskedPDOAmplitude backward (endpointOutputMask f p output) (chartInputMask f p)
      (directPDOSymbols
        (fun y a ↦ (coefficient (f.chart p).index Q y a).map Complex.ofReal)
        (fun y ↦ (zeroth (f.chart p).index B y).map Complex.ofReal) W₁
        (conicBminus (f.chart p).radialSection (f.chart p).index Q
          (fieldRoot (coordinateSplit (f.chart p).index) Q (f.chart p).root)
          (f.chart p).row (f.chart p).col)
        (conicSourceSymbol (f.chart p).radialSection (conicMask (f.spatialMask p))
          (f.chart p).sourceMask) (selectedEndpointMultiplier f p threshold) 3) =
      orientedMaskedPDOAmplitude backward (endpointOutputMask f p output) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*threshold) Q B 1) := by
  rw [selected_directPDOSymbols_eq_four_selected_symbols f p threshold Q B W₁]
  rfl

/-- Physical noncomparable grades for the SAME complete algebraic residual,
at the fixed doubled threshold. The inverse input is exactly the physical
inverse output of
`FiniteAlgebraic.exists_finite_physical_evolution_and_algebraic_inverse`;
`hdom` is its normalized complement certificate. The whole source product
and its full physical action are constructed here with the existing supported
budget producers. Thus neither a complete-symbol grade nor a kernel estimate
is assumed. Both original coefficient profiles and low bounds are retained.
The physical action uses one coefficient derivative; `1 ≤ Rstar` absorbs it,
so the final slow-scale offset is ZERO. Constants precede `Q,B,L,ρ`, the
threshold and accuracy and are uniform on the supplied finite family.
Consumer: the noncomparable symbol input of
`ResidualLocalization.exists_completePhysicalResidual_restriction_bound`
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`,
`app:ch_regular_base:eq:energy-complete-residual`). This is a physical estimate;
the comparable joint covariable estimate is a separate obligation. -/
theorem exists_selected_algebraic_noncomparable_profile
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hΩ : IsOpen Ω) (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω) (hM : 0 ≤ M)
    (hc : ∀ p : f.centers,
      let c := f.chart p
      RootBuffer c.index c.row c.col A₀ p.val.val c.root c.coefficientRadius c.rootRadius
        c.minorGap c.transportGap)
    (hsource : ∀ p : f.centers,
      MapsTo (rootPhysicalPosition (coordinateSplit (f.chart p).index))
        (tsupport (f.chart p).sourceMask) (closedBall x RQ))
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hos : tsupport output ⊆ ball x f.physicalRadius)
    (D : f.centers → ℕ → ℝ) (hD : ∀ p k, 0 < D p k)
    (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ (Rstar : ℕ), 1 ≤ Rstar → ∀ (L ρ : ℝ), 1 ≤ L → 0 < ρ →
      ∀ (threshold : ℝ), f.radialThreshold ≤ threshold →
      ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        cNorm (closedBall x RQ) (sectorLowOrder d) Q ≤ M →
        cNorm (closedBall x RQ) (sectorLowOrder d) B ≤ M →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ A k * L ^ (k - Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ A k * L ^ (k - Rstar)) →
      ∀ p : f.centers,
        let c := f.chart p
        let h := fieldRoot (coordinateSplit c.index) Q c.root
        let β := fun ζ ↦ (dilatedConicMask (f.angularMask p) (2*threshold)
          (physicalCoordinates c.index ζ) : ℂ)
        ((physicalCoordinates c.index ⁻¹' Ω) ×ˢ
          (normalizeCovector c.radialSection '' tsupport β) ⊆
          complementDomain c.index Q h c.row c.col (normalizedRootDomain c)) →
        (∀ ζ ∈ tsupport β,
          (∀ y ∈ closedBall ((physicalCoordinates c.index).symm x) RQ,
            ContDiffAt ℝ ∞ (fun y ↦ conicBminus c.radialSection c.index Q h
              c.row c.col y ζ) y) ∧
          ∀ k, (1 + ‖ζ‖) * cNorm (closedBall ((physicalCoordinates c.index).symm x) RQ) k
            (fun y ↦ conicBminus c.radialSection c.index Q h c.row c.col y ζ) ≤
              D p k * (1 + cNorm (closedBall x RQ) k Q)) →
      ∀ backward low j, ∀ ξ ∈ normalizedGraphCarrier ρ low j,
        ∀ z ∈ tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p), ∀ k,
          ‖iteratedFDeriv ℝ k (fun w : E × E ↦ orientedMaskedPDOAmplitude backward
            (endpointOutputMask f p output) (chartInputMask f p)
            (selectedAlgebraicSymbol f p (2*threshold) Q B 1) w.1 w.2 (ρ • ξ)) z‖ ≤
              (max 1 (branchRadius low j)) ^ (-1 : ℝ) * C k * L ^ k := by
  classical
  have hphysical (p : f.centers) : MapsTo (physicalCoordinates (f.chart p).index)
      (closedBall ((physicalCoordinates (f.chart p).index).symm x) RQ) (closedBall x RQ) := by
    intro y hy
    have he := norm_physicalCoordinates (f.chart p).index
      (y - (physicalCoordinates (f.chart p).index).symm x)
    simpa only [mem_closedBall, dist_eq_norm, map_sub,
      ContinuousLinearEquiv.apply_symm_apply] using he.le.trans (mem_closedBall.mp hy)
  have hmask (p : f.centers) :
      tsupport (endpointOutputMask f p output) ⊆
        closedBall ((physicalCoordinates (f.chart p).index).symm x) RQ := by
    intro y hy
    have he : dist (physicalCoordinates (f.chart p).index y) x =
        dist y ((physicalCoordinates (f.chart p).index).symm x) := by
      conv_lhs => arg 2; rw [← (physicalCoordinates (f.chart p).index).apply_symm_apply x]
      rw [dist_eq_norm, ← map_sub, norm_physicalCoordinates, dist_eq_norm]
    have ht := tsupport_comp_subset_preimage (fun y ↦ (output y : ℂ))
      (physicalCoordinates (f.chart p).index).continuous hy
    have hb := hos (tsupport_comp_subset Complex.ofReal_zero output ht)
    have hfour : physicalCoordinates (f.chart p).index y ∈ closedBall x (4*f.physicalRadius) :=
      (ball_subset_closedBall (ball_subset_ball (by linarith [f.physicalRadius_pos]) hb))
    simpa only [mem_closedBall, he] using f.physicalBall_coefficientDomain hfour
  choose T hT hmaskBound using fun p ↦ exists_orientedPDO_physical_cNorm_cost
    (endpointOutputMask f p output) (chartInputMask f p)
    (endpointOutputMask_properties f p ho hoc hos).1
    (chartPhysicalMasks_properties f p).2.1
    (endpointOutputMask_properties f p ho hoc hos).2.1
    (chartPhysicalMasks_properties f p).2.2.2.1 _ _ (hmask p)
  choose Db hDb hb using fun p ↦ exists_selected_sourceInverse_weighted_cNorm_bounds
    f p hRQ hKΩ (conicMask (f.spatialMask p)) (chartConicMask_properties f p).2.2 (D p) (hD p)
  choose Dp hDp hp using fun p ↦ exists_physicalSymbolApply_weighted_cNorm_transfer
    (f.chart p).index ((physicalCoordinates (f.chart p).index).symm x) hRQ x RQ
    (hphysical p) M (Db p) (hDb p)
  let Cp := fun p k ↦ 2 * T p k * Dp p k * (1 + 2 * A (k+1))
  have hCp p k : 0 ≤ Cp p k := by
    dsimp [Cp]
    have := hT p k
    have := hDp p k
    have := hA (k+1)
    positivity
  refine ⟨fun k ↦ ∑ p, Cp p k, fun k ↦ Finset.sum_nonneg (fun p _ ↦ hCp p k), ?_⟩
  intro Rstar hR L ρ hL hρ threshold _ Q B hQ hB hQrange hQlow hBlow hQprofile hBprofile
    p c h β hdom hinverse backward low j ξ hξ z hz k
  let b := directAlgebraicSymbol
    (conicBminus c.radialSection c.index Q h c.row c.col)
    (conicSourceSymbol c.radialSection (conicMask (f.spatialMask p)) c.sourceMask) β
  let pb := selectedAlgebraicSymbol f p (2*threshold) Q B 1
  obtain ⟨hout, hinput, hcout, hcinput, hcarrier⟩ := chartPhysicalMasks_properties f p
  obtain ⟨hsp, hspSupport, hspRange⟩ := chartConicMask_properties f p
  obtain ⟨_, _, _, _, _, _, hregular⟩ := exists_selected_algebraicSymbols_supported_budgets
    f p hΩ hRQ hKΩ (hc p) (hsource p) _ hsp hspSupport hspRange
    _ _ hout hinput hcout hcinput hcarrier M hM (D p) (hD p)
  have horder : 2 * (d+2) + 2 ≤ sectorLowOrder d := by
    have := (sectorLowOrder_bounds d).2.2
    omega
  have hreg := hregular (2*threshold) Q B hQ hB hQrange
    ((cNorm_mono_order horder).trans hQlow) ((cNorm_mono_order horder).trans hBlow) hdom hinverse
  have hbs : ContDiff ℝ ∞ (Function.uncurry b) := (hreg b (by simp only [b, Set.mem_insert_iff]; exact Or.inl rfl)).1
  have hpbs : ContDiff ℝ ∞ (Function.uncurry pb) := (hreg pb (by
    simp [pb, selectedAlgebraicSymbol])).1
  have hpBudget := hp p Ω hΩ hKΩ Q B b hQ hB hbs hpbs
    ((cNorm_mono_order (by have := sectorLowOrder_bounds d; omega : 1 ≤ sectorLowOrder d)).trans hQlow)
    ((cNorm_mono_order (Nat.zero_le _)).trans hBlow)
    (hb p (2*threshold) Q hdom hinverse).2 (ρ • ξ) k
  change (1 + ‖ρ • ξ‖) * cNorm (closedBall ((physicalCoordinates c.index).symm x) RQ) k
    (fun y ↦ pb y (ρ • ξ)) ≤ _ at hpBudget
  have hcoeff : 1 + cNorm (closedBall x RQ) (k+1) Q +
      cNorm (closedBall x RQ) (k+1) B ≤ (1 + 2 * A (k+1)) * L ^ k := by
    have he : k+1-Rstar ≤ k := by omega
    have hpow := pow_le_pow_right₀ hL he
    have hq := (hQprofile (k+1)).trans (mul_le_mul_of_nonneg_left hpow (hA _))
    have hb' := (hBprofile (k+1)).trans (mul_le_mul_of_nonneg_left hpow (hA _))
    nlinarith [one_le_pow₀ hL (n := k)]
  have hnorm := hmaskBound p pb hpbs backward (ρ • ξ) k z hz
  have hweighted : (1 + ‖ρ • ξ‖) *
      ‖iteratedFDeriv ℝ k (fun w : E × E ↦ orientedMaskedPDOAmplitude backward
        (endpointOutputMask f p output) (chartInputMask f p) pb w.1 w.2 (ρ • ξ)) z‖ ≤
          T p k * Dp p k * (1 + 2 * A (k+1)) * L ^ k := by
    calc
      _ ≤ (1 + ‖ρ • ξ‖) * (T p k * cNorm
          (closedBall ((physicalCoordinates c.index).symm x) RQ) k (fun y ↦ pb y (ρ • ξ))) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = T p k * ((1 + ‖ρ • ξ‖) * cNorm
          (closedBall ((physicalCoordinates c.index).symm x) RQ) k (fun y ↦ pb y (ρ • ξ))) := by ring
      _ ≤ T p k * (Dp p k * ((1 + 2 * A (k+1)) * L ^ k)) :=
        mul_le_mul_of_nonneg_left
          (hpBudget.trans (mul_le_mul_of_nonneg_left hcoeff (hDp p k).le)) (hT p k)
      _ = _ := by ring
  have hinv : _ ≤ (1 + ‖ρ • ξ‖)⁻¹ *
      (T p k * Dp p k * (1 + 2 * A (k+1)) * L ^ k) :=
    (le_inv_mul_iff₀ (by positivity : 0 < 1 + ‖ρ • ξ‖)).mpr hweighted
  apply hinv.trans
  calc
    _ ≤ (2 * (max 1 (branchRadius low j)) ^ (-1 : ℝ)) *
        (T p k * Dp p k * (1 + 2 * A (k+1)) * L ^ k) :=
      mul_le_mul_of_nonneg_right (algebraic_graph_weight_le hρ.ne' low j hξ) (by
        have := hT p k
        have := hDp p k
        have := hA (k+1)
        positivity)
    _ = (max 1 (branchRadius low j)) ^ (-1 : ℝ) * Cp p k * L ^ k := by dsimp [Cp]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun p _ ↦ hCp p k) (Finset.mem_univ p)) (by positivity)) (by positivity)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
