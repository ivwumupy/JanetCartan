module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalLetterProfiles
public import JanetCartan.Iteration.PhysicalPrimary.OriginalWordOrdinary
public import JanetCartan.Iteration.PhysicalPrimary.OriginalParameterRemainders
public import JanetCartan.Iteration.PhysicalPrimary.OriginalObservationPhase
public import JanetCartan.Iteration.PhysicalPrimary.OriginalHistoryFamily
public import JanetCartan.Iteration.PhysicalInitialization.OriginalColoredProtectionApplication
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualWordProfiles
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualWordProfiles.LocalIdentification
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.InitializedDecayApplication.MeanCorrectedSource.ObservedCore.Coordinates
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.SupportedSource
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalReservedWordsTemplate

/-! Actual finite-word term of `complex_inverse_parameter_envelopes_of_actual_finite_words`
(`app:ch_regular:lem:finite-chain`, `app:ch_response:eq:response-graded-reduced`). -/
@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16000
open Set MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.OriginalReservedWords
open FourierIntegral.FullLowBounds
open ResponseTransfer.DirectEvolution OriginalHistoryFamily
open ResponseTransfer ResponseTransfer.Complement ResponseTransfer.SourceNegative
open ResponseTransfer.DirectEvolution.AnnularSobolev ResponseTransfer.DirectEvolution.CompactTransfer
open FourierIntegral Pseudodifferential SmallSupport LocalSobolev
open RegularSector.Characteristic.RetardedLocalization

/-- Exact native compression reserve for the prescribed source reserve. -/
def phaseReserve (n rSource : ℕ) : ℕ := rSource + fullLowReserve n + 4
/-- Exact native coefficient reserve for the prescribed source reserve. -/
def coefficientReserve (n rSource : ℕ) : ℕ := phaseReserve n rSource + 10

/-- Shared original source and word orders, without an independent floor. -/
theorem word_orders {d r h : ℕ} (hh : r + 3*(d+1) + 20 ≤ h) :
    16 + r ≤ h ∧ 8 ≤ h ∧ RegularSector.FiniteEvolution.sectorLowOrder d + 2 ≤ h ∧
    8 ≤ coefficientReserve (d+1) r ∧ fullLowReserve (d+1)+2 < phaseReserve (d+1) r ∧
    r + fullLowReserve (d+1) + 4 ≤ phaseReserve (d+1) r ∧
    phaseReserve (d+1) r + 10 ≤ coefficientReserve (d+1) r ∧
    2 + coefficientReserve (d+1) r ≤ h := by
  simp only [coefficientReserve,phaseReserve,RegularSector.FiniteEvolution.sectorLowOrder,
    RegularSector.Characteristic.UniformEvolution.retardedCoefficientOrder,
    FourierIntegral.WholeImageGeometry.wholeImagePhaseReserve,
    FourierIntegral.LowBounds.primitiveNormalReserve,fullLowReserve_eq]
  repeat' apply And.intro <;> omega

/-- Inherit the selected `kMin` from the stronger history order. -/
theorem word_history_order {n r h k : ℕ} (hc : 2 + coefficientReserve n r ≤ h)
    (hh : RevisedScales.displacementLoss n + bandExponent * ((h:ℝ) + (n:ℝ)/2) + 2 < (k:ℝ)) :
    RevisedScales.displacementLoss n + bandExponent * ((coefficientReserve n r:ℝ) + (n:ℝ)/2) + 2 < (k:ℝ) := by
  have he : (coefficientReserve n r:ℝ) ≤ (h:ℝ) := by
    exact_mod_cast (show coefficientReserve n r ≤ h by omega)
  have hb : 0 ≤ bandExponent := by norm_num [bandExponent]
  have hm := mul_le_mul_of_nonneg_left (add_le_add_right he ((n:ℝ)/2)) hb
  linarith only [hh,hm]

/-- The actual native orthonormal basis is on the doubled carrier space. -/
def wordBasis (n : ℕ) := stdOrthonormalBasis ℝ (CarrierVariables n)
/-- A strict window compatible with the unmodified colored rates. -/
def windowExponent : ℝ := 1 / 4

theorem windowExponent_pos : 0 < windowExponent := by norm_num [windowExponent]
theorem windowExponent_lt_one : windowExponent < 1 := by norm_num [windowExponent]

/-- The original carrier exponent pays the strict window on the physical
frequency diagonal; the actual colored packet supplies the radial bound. -/
theorem colored_window_of_radial {Rinit radius : ℝ} (hR : 1 ≤ Rinit)
    (hrad : 1 ≤ radius) (j : ℕ) :
    let T := historyScale Rinit growthExponent j
    let τ := (radius * T ^ carrierExponent)⁻¹
    0 < τ ∧ 1 ≤ τ⁻¹ ∧ currentCoefficientScale Rinit j ≤ (τ⁻¹) ^ (1-windowExponent) := by
  intro T τ
  have hT : 1 ≤ T := hR.trans (le_historyScale hR j)
  have hpow : 1 ≤ T ^ carrierExponent := Real.one_le_rpow hT (by norm_num [carrierExponent])
  have hm : T ^ carrierExponent ≤ radius * T ^ carrierExponent := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hrad (zero_le_one.trans hpow)
  have htot := hpow.trans hm
  simp only [τ, inv_inv]
  refine ⟨inv_pos.mpr (zero_lt_one.trans_le htot),htot,?_⟩
  calc currentCoefficientScale Rinit j = T ^ coefficientExponent := rfl
       _ ≤ T ^ (carrierExponent*(1-windowExponent)) :=
         Real.rpow_le_rpow_of_exponent_le hT (by norm_num [coefficientExponent,carrierExponent,windowExponent])
       _ = (T ^ carrierExponent) ^ (1-windowExponent) :=
         Real.rpow_mul (zero_le_one.trans hT) _ _
       _ ≤ _ := Real.rpow_le_rpow (zero_le_one.trans hpow) hm (by norm_num [windowExponent])

/-- Dependent transport from the original prethreshold index; no default
history is required when the admitted set is empty. -/
theorem restrict_word_constant {d : ℕ} {Payload : Type} (B : ℝ) (k : ℕ) (T : ℝ)
    (sourceOK : RawIndex d Payload → Prop)
    (P : {i : RawIndex d Payload // Admitted B k windowExponent T i ∧ sourceOK i} → ℝ → Prop)
    (h : ∀ hne : Nonempty {i : RawIndex d Payload // Admitted B k windowExponent T i ∧ sourceOK i},
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i, P (admittedRetraction B k windowExponent T sourceOK hne i) C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, P y C := by
  classical
  by_cases hne : Nonempty {i : RawIndex d Payload // Admitted B k windowExponent T i ∧ sourceOK i}
  · obtain ⟨C,hC,hb⟩ := h hne
    refine ⟨C,hC,?_⟩
    intro y
    obtain ⟨i,rfl⟩ := admittedRetraction_surjective B k windowExponent T sourceOK hne y
    exact hb i
  · exact ⟨0,le_rfl,fun y ↦ (hne ⟨y⟩).elim⟩

/-- The complex source is the literal carrier times the small source, restricted
as in the observed remainder. No second χ₂ or tensor identity is assumed. -/
theorem original_forcing_class {d : ℕ} {W : Set (Euclidean (d+1))} (hW : MeasurableSet W)
    (χ₂ χ₃ : Euclidean (d+1) → ℝ) (h₂ : IsCompact (tsupport χ₂)) (h₃ : tsupport χ₃ ⊆ W)
    (a : Euclidean (d+1) × (Euclidean 3 × Euclidean d) → EuclideanSpace ℂ (Fin (d+1)))
    (ha : ContDiff ℝ ∞ a) (hs : ∀ w, w.1 ∉ tsupport χ₂ → a w = 0)
    (c : Euclidean 3 × Euclidean d) (φ : Euclidean (d+1) → ℝ) (hc : Continuous φ) (lam0 : ℝ)
    (he : modulatedSource χ₃ φ (fun x ↦ a (x,c)) lam0 = fun x ↦ carrier lam0 φ x • a (x,c)) :
    let raw := fun x ↦ carrier lam0 φ x • a (x,c)
    let datum := graphTestToLp (vectorOriginalDatumTest a ha h₂ hs [] c)
    ∀ hm : MemLp raw 2 volume,
      zeroExtend hW (restrictL2 W (hm.toLp raw)) = carrierMultiplication lam0 φ hc datum := by
  intro raw datum hm
  have hd : (datum : Euclidean (d+1) → EuclideanSpace ℂ (Fin (d+1))) =ᵐ[volume] fun x ↦ a (x,c) := by
    simpa only [datum, originalDatumDerivative, orderedTransferAction] using
      vectorOriginalDatumTest_toLp_ae a ha h₂ hs [] c
  have hu : (carrierMultiplication lam0 φ hc datum : Euclidean (d+1) → EuclideanSpace ℂ (Fin (d+1))) =ᵐ[volume] raw := by
    filter_upwards [carrierMultiplication_ae lam0 φ hc datum,hd] with x hx hax
    rw [hx,hax]
  have hmod : MemLp (modulatedSource χ₃ φ (fun x ↦ a (x,c)) lam0) 2 volume := he.symm ▸ hm
  have hLp := hmod.toLp_congr hm (Filter.EventuallyEq.of_eq he)
  rw [← hLp,zeroExtend_restrictL2_modulatedSource hW χ₃ φ (fun x ↦ a (x,c)) lam0 h₃ hmod,hLp]
  exact Lp.ext (hm.coeFn_toLp.trans hu.symm)

end JanetCartan.PhysicalPrimary.OriginalReservedWords

construct_original_reserved_word_threshold
construct_original_reserved_word_points
construct_original_reserved_word_raw_bounds
construct_original_reserved_word_bounds
construct_original_reserved_colored_window
