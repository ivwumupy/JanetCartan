module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity.ResidualWords.MeasuredCosts
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.LocalizerLow
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.LowBounds

/-!
# Uniform LOW bounds for the selected complete residual letters

The same protected-construction certificates and actual elliptic symbol budgets
bound each normalized conjugate pair, with physical measurements and literal
adjoints retained. The existing right-localizer kernel estimate then supplies
the polynomial LOW input of `finiteChain_observation_rapidDecayAt`, on the
original complex and real restriction spaces (`app:ch_regular:eq:chain-tail`).
These deductions retain the selected family; they do not select new operators
or assume the norm of a localized residual.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
open Characteristic Characteristic.EvolutionIntegral Characteristic.UniformEvolution
open Characteristic.RetardedLocalization Realization NormalizedSolver FiniteAssembly
open FiniteMasks.ActualFamily FiniteAlgebraic FinitePdo FiniteEvolution
open ArbitraryAccuracy.ResidualLocalization CharacteristicTransport.CompleteResidual
open Characteristic.PdoRealization AmplitudeBound
open Pseudodifferential ResponseTransfer LocalSobolev FourierIntegral FourierIntegral.LowBounds
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
local notation "H" => SpacetimeL2 d (d+1)
local notation "F" => EuclideanSpace ℂ (Fin (d+1))
local notation "RF" => EuclideanSpace ℝ (Fin (d+1))
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- The original physical PDO has the low bound of its exact cycle symbol
(`app:ch_regular_base:eq:actual-normal-amplitude`). -/
private theorem selected_maskedPDO_low_bound
    (χout χin : E → ℂ) (c : E → E → CMat) (R N : ℝ) (hN : 0 ≤ N)
    (hb : GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χout χin c) R N) :
    ‖maskedPhysicalPDO χout χin c‖ ≤
      (d+1 : ℝ)*(d+1)*(fixedBoxAmplitudeConstant (d+1) R*N) := by
  rw [maskedPhysicalPDO_eq_vectorTwoPositionL2Operator χout χin c R N hb,
    vectorTwoPositionL2Operator_eq_graphNormalL2Operator]
  simpa only [Nat.cast_add, Nat.cast_one] using
    norm_graphNormalL2Operator_le (Nat.succ_pos d) R _ hN hb

/-- The literal external half cancels the low cost of the whole conjugate
pair (`app:ch_regular_base:eq:real-sector-normalization`). -/
private theorem selected_normalizedPair_norm_le (T : H →L[ℂ] H) :
    ‖normalizedPair T‖ ≤ ‖T‖ := by
  have h := (norm_physicalPairedSectorSum_le_twice_sum {()}
    (fun _ : Unit ↦ (1/2 : ℂ) • T)).1
  have hhalf : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
  simpa only [Finset.sum_singleton, norm_smul, hhalf, ← mul_assoc,
    show (2 : ℝ)*(1/2) = 1 by norm_num, one_mul, normalizedPair] using h

/-- Both actual physical masks are contractions on the same Lebesgue L²
space (`app:ch_regular_base:eq:measured-adjoint`). -/
private theorem selected_measuredOperator_norm_le
    (μ ν : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1) (T : H →L[ℂ] H) :
    ‖measuredOperator μ ν hμ hν hμb hνb T‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖sourceCutMultiplier μ hμ hμb‖ *
        (‖T‖ * ‖sourceCutMultiplier ν hν hνb‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1*(‖T‖*1) := by
      gcongr
      · exact norm_sourceCutMultiplier_le μ hμ hμb
      · exact norm_sourceCutMultiplier_le ν hν hνb
    _ = _ := by ring

/-- Literal restriction and zero extension introduce no low norm factor
(`app:ch_regular:lem:finite-chain`). -/
private theorem selected_localRetardedOperator_norm_le
    {U : Set E} (hU : MeasurableSet U) (V : Set E) (T : H →L[ℂ] H) :
    ‖localRetardedOperator hU V T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  change ‖restrictL2 V (T (SmallSupport.zeroExtend hU u))‖ ≤ _
  exact ((restrictL2 V).le_of_opNorm_le (norm_restrictL2_le V) _).trans
    (by simpa only [one_mul, LinearIsometry.norm_map] using T.le_opNorm (SmallSupport.zeroExtend hU u))

/-- The real local compression is contractive on the same original domains
(`app:ch_regular_base:eq:real-sector-normalization`). -/
private theorem selected_localRealCompression_norm_le
    {U : Set E} (hU : MeasurableSet U) (V : Set E) (T : H →L[ℂ] H) :
    ‖localRealCompression hU V T‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖l2RealPart (ι := Fin (d+1)) (volume.restrict V)‖ *
        (‖localRetardedOperator hU V T‖ *
          ‖l2ComplexInclusion (ι := Fin (d+1)) (volume.restrict U)‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1*(‖T‖*1) := by
      gcongr
      · exact l2RealPart_norm_le _
      · exact selected_localRetardedOperator_norm_le hU V T
      · exact l2ComplexInclusion_norm_le _
    _ = _ := by ring

/-- The selected characteristic low budgets and actual elliptic symbol
producer give one constant for every complete residual letter, before the
varying threshold, coefficient fields, phase and physical measurements.
`hendpoint` and `hretarded` are the literal same-witness outputs of the
protected direct construction; the full-B algebraic input is its normal
symbol certificate. All reflected contributions are retained through the
external half and literal pair (`energy-complete-residual`, `chain-tail`). -/
theorem exists_selectedFullPairedResidualTerm_uniform_low_constants_with_signed
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω) (hM : 0 ≤ M)
    (Rbox Ralg Malg base : f.centers → ℝ) (D : f.centers → ℕ → ℝ)
    (hMalg : ∀ p, 0 ≤ Malg p) (hD : ∀ p n, 0 ≤ D p n) :
    ∃ low : ((f.centers × Fin 3) ⊕ Unit) → ℝ, (∀ a, 0 ≤ low a) ∧
      ∀ threshold ≥ f.radialThreshold,
      ∀ (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
        (_hos : tsupport output ⊆ ball x f.physicalRadius)
        (hib : ∀ y, ‖f.inputMask y‖ ≤ 1),
      ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        cNorm (closedBall x RQ) (2*(d+2)+2) Q ≤ M →
        cNorm (closedBall x RQ) (2*(d+2)+2) B ≤ M →
      ∀ (W₁ : f.centers → TwoTimeAmplitude d (d+1))
        (T : f.centers → H →L[ℂ] H) (Ψ : f.centers → TwoTimePhase d)
        (χout χsource : f.centers → E → ℂ) (hs : ∀ p, ContDiff ℝ ∞ (χsource p))
        (Dgain Gain cost : f.centers → ℕ → ℝ),
        (∀ p, EndpointPdoEstimates (f.chart p).index (closedBall x RQ) Q B
          (endpointOutputMask f p output) (chartInputMask f p)
          (selectedEndpointSymbol f p threshold Q (W₁ p)) (Rbox p) M (D p) (Dgain p) (Gain p)) →
        (∀ p, RetainedSignedRetardedBounds (closedBall x RQ) Q B
          (3*(f.chart p).maskRadius/4)
          ((coordinateSplit (f.chart p).index x).1-(f.chart p).maskRadius/2)
          (Ψ p) (twoTimePhysicalApply
            (fun y a ↦ (ResidualCoordinates.coefficient (f.chart p).index Q y a).map Complex.ofReal)
            (fun y ↦ (ResidualCoordinates.zeroth (f.chart p).index B y).map Complex.ofReal) (W₁ p))
          (χout p) (χsource p) (selectedEndpointMultiplier f p threshold) (hs p) 1
          (base p) (cost p) (T p)) →
        (∀ p, GraphNormalAmplitudeBounds
          (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
            (selectedAlgebraicSymbol f p (2*threshold) Q B 1)) (Ralg p) (Malg p)) →
      ∀ (μ ν : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
        (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
        (a : (f.centers × Fin 3) ⊕ Unit) (backward : Bool),
        let P := measuredOperator μ ν hμ hν hμb hνb
          (selectedFullPairedResidualTerm f hK threshold Q B W₁ output ho hob hib T a)
        let Pdir := if backward then P.adjoint else P
        ‖Pdir‖ ≤ low a ∧ (∀ (U V : Set E) (hU : MeasurableSet U),
          ‖localRetardedOperator hU V Pdir‖ ≤ low a ∧
          ‖localRealCompression hU V Pdir‖ ≤ low a) ∧
        ∀ reflected : Bool,
          let Ps := measuredOperator μ ν hμ hν hμb hνb
            (selectedFullPhysicalResidualTerm f hK threshold Q B W₁ output ho hob hib T (a, reflected))
          let Psdir := if backward then Ps.adjoint else Ps
          ‖Psdir‖ ≤ low a ∧ ∀ (U V : Set E) (hU : MeasurableSet U),
            ‖localRetardedOperator hU V Psdir‖ ≤ low a := by
  obtain ⟨Re, _, Ne, hNe, _, _, he⟩ :=
    EllipticComplement.exists_ellipticSymbols_pdo_budgets f hK hΩ hRQΩ
  let ce := (d+1 : ℝ)*(d+1)*(fixedBoxAmplitudeConstant (d+1) Re*Ne)
  let ca p := (d+1 : ℝ)*(d+1)*(fixedBoxAmplitudeConstant (d+1) (Ralg p)*Malg p)
  let cp p := (d+1 : ℝ)*(d+1)*(fixedBoxAmplitudeConstant (d+1) (Rbox p)*
    (D p (2*(d+2)+1)*(1+M+M)))
  let low : ((f.centers × Fin 3) ⊕ Unit) → ℝ :=
    Sum.elim (fun a ↦ ![cp a.1, max 0 (base a.1), ca a.1] a.2) (fun _ ↦ ce)
  have hce : 0 ≤ ce := mul_nonneg (by positivity)
    (mul_nonneg (fixedBoxAmplitudeConstant_nonneg _ _) hNe.le)
  have hca p : 0 ≤ ca p := mul_nonneg (by positivity)
    (mul_nonneg (fixedBoxAmplitudeConstant_nonneg _ _) (hMalg p))
  have hcp p : 0 ≤ cp p := mul_nonneg (by positivity)
    (mul_nonneg (fixedBoxAmplitudeConstant_nonneg _ _)
      (mul_nonneg (hD p _) (by positivity)))
  have hl a : 0 ≤ low a := by
    rcases a with ⟨p,j⟩ | ⟨⟩
    · fin_cases j <;> simp only [low, Sum.elim_inl, Matrix.cons_val_zero',
        Matrix.cons_val_succ', Matrix.cons_val_fin_one]
      · exact hcp p
      · exact le_max_left _ _
      · exact hca p
    · exact hce
  refine ⟨low, hl, ?_⟩
  intro threshold ht output ho hob hos hib Q B hQ hB hmap hQl hBl
    W₁ T Ψ χout χsource hs Dgain Gain cost hendpoint hretarded halg
    μ ν hμ hν hμb hνb a backward P Pdir
  have houtput (A : H →L[ℂ] H) : ‖(sourceCutMultiplier output ho hob).comp A‖ ≤ ‖A‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (norm_sourceCutMultiplier_le output ho hob) (norm_nonneg A))
  let S : ((f.centers × Fin 3) ⊕ Unit) → H →L[ℂ] H := Sum.elim
    (fun b ↦ FiniteEvolution.physicalOperator (f.chart b.1).index
      (selectedCommonChartResidualTerm f b.1 threshold Q B (W₁ b.1) output ho hob hib (T b.1) b.2))
    (fun _ ↦ (sourceCutMultiplier output ho hob).comp
      (EllipticComplement.ellipticResidual f hK threshold Q B))
  have hbase : ‖S a‖ ≤ low a := by
    cases a with
    | inl a =>
      rcases a with ⟨p,j⟩
      change ‖FiniteEvolution.physicalOperator (f.chart p).index
        (selectedCommonChartResidualTerm f p threshold Q B (W₁ p) output ho hob hib (T p) j)‖ ≤ _
      fin_cases j
      · exact (norm_physicalOperator_le _ _).trans
          (selected_maskedPDO_low_bound _ _ _ (Rbox p) _
            (mul_nonneg (hD p _) (by positivity)) (hendpoint p).1)
      · change ‖physicalOperator (f.chart p).index
          (selectedCommonChartRetarded f p output ho hob hib (T p))‖ ≤ max 0 (base p)
        rw [physicalOperator_selectedCommonChartRetarded]
        apply (houtput _).trans
        apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
        calc
          _ ≤ ‖physicalOperator (f.chart p).index (T p)‖*1 :=
            mul_le_mul_of_nonneg_left (norm_sourceCutMultiplier_le _ _ _) (norm_nonneg _)
          _ ≤ base p := by simpa only [mul_one] using (norm_physicalOperator_le _ _).trans (hretarded p).1
          _ ≤ _ := le_max_right _ _
      · change ‖physicalOperator (f.chart p).index ((1/Complex.I) •
          maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
            (selectedAlgebraicSymbol f p (2*threshold) Q B 1))‖ ≤ ca p
        have hsmul (z : ℂ) (A : H →L[ℂ] H) :
            physicalOperator (f.chart p).index (z • A) =
              z • physicalOperator (f.chart p).index A := by
          simp only [FiniteEvolution.physicalOperator, ContinuousLinearMap.comp_smul,
            ContinuousLinearMap.smul_comp]
        rw [hsmul]
        simp only [norm_smul, norm_div, norm_one, Complex.norm_I,
          div_self one_ne_zero, one_mul]
        rw [← commonOutput_comp_chartPDO f p output ho hob hos
          (selectedAlgebraicSymbol f p (2*threshold) Q B 1) (Ralg p) (Malg p) (halg p)]
        exact (houtput _).trans ((norm_physicalOperator_le _ _).trans
          (selected_maskedPDO_low_bound _ _ _ (Ralg p) (Malg p) (hMalg p) (halg p)))
    | inr a =>
      cases a
      change ‖(sourceCutMultiplier output ho hob).comp
        (EllipticComplement.ellipticResidual f hK threshold Q B)‖ ≤ _
      apply (houtput _).trans
      have hb := (he threshold ht Q B hQ hB hmap hQl hBl
        (EllipticComplement.ellipticResidualSymbol f hK threshold Q B) (Or.inr rfl)).1
      simpa only [low, Sum.elim_inr, ce, EllipticComplement.ellipticResidual, norm_smul, norm_div, norm_one,
        Complex.norm_I, div_self one_ne_zero, one_mul] using
        selected_maskedPDO_low_bound _ _ _ Re Ne hNe.le hb
  have heq : selectedFullPairedResidualTerm f hK threshold Q B W₁ output ho hob hib T a =
      normalizedPair (S a) := by
    cases a with
    | inl a =>
      exact selectedFullPairedResidualTerm_characteristic f hK threshold
        Q B W₁ output ho hob hib T a.1 a.2
    | inr a =>
      cases a
      exact selectedFullPairedResidualTerm_elliptic f hK threshold
        Q B W₁ output ho hob hib T
  have hraw : ‖selectedFullPairedResidualTerm f hK threshold Q B W₁ output ho hob hib T a‖ ≤ low a := by
    rw [heq]
    exact (selected_normalizedPair_norm_le _).trans hbase
  have hp : ‖Pdir‖ ≤ low a := by
    have hm := (selected_measuredOperator_norm_le μ ν hμ hν hμb hνb _).trans hraw
    cases backward
    · exact hm
    · simpa only [Pdir, ite_true, LinearIsometryEquiv.norm_map] using hm
  refine ⟨hp, (fun U V hU ↦ ⟨(selected_localRetardedOperator_norm_le hU V _).trans hp,
    (selected_localRealCompression_norm_le hU V _).trans hp⟩), ?_⟩
  intro reflected Ps Psdir
  have hhalf : ‖(1/2 : ℂ) • S a‖ ≤ low a := by
    rw [norm_smul, show ‖(1/2 : ℂ)‖ = (1/2 : ℝ) by norm_num]
    exact (mul_le_of_le_one_left (norm_nonneg _) (by norm_num)).trans hbase
  have hsigned : ‖selectedFullPhysicalResidualTerm f hK threshold Q B W₁ output ho hob hib T (a, reflected)‖ ≤ low a := by
    cases reflected with
    | false => exact hhalf
    | true =>
      apply ContinuousLinearMap.opNorm_le_bound _ (hl a)
      intro u
      change ‖star (((1/2 : ℂ) • S a) (star u))‖ ≤ _
      simpa only [norm_star] using (((1/2 : ℂ) • S a).le_of_opNorm_le hhalf (star u))
  have hps : ‖Psdir‖ ≤ low a := by
    have hm := (selected_measuredOperator_norm_le μ ν hμ hν hμb hνb _).trans hsigned
    cases backward
    · exact hm
    · simpa only [Psdir, ite_true, LinearIsometryEquiv.norm_map] using hm
  exact ⟨hps, fun U V hU ↦ (selected_localRetardedOperator_norm_le hU V _).trans hps⟩

/-- The original paired LOW bound is the projection of the same signed
construction (`app:ch_regular:lem:finite-chain`). -/
theorem exists_selectedFullPairedResidualTerm_uniform_low_constants
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω) (hM : 0 ≤ M)
    (Rbox Ralg Malg base : f.centers → ℝ) (D : f.centers → ℕ → ℝ)
    (hMalg : ∀ p, 0 ≤ Malg p) (hD : ∀ p n, 0 ≤ D p n) :
    ∃ low : ((f.centers × Fin 3) ⊕ Unit) → ℝ, (∀ a, 0 ≤ low a) ∧
      ∀ threshold ≥ f.radialThreshold,
      ∀ (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
        (_hos : tsupport output ⊆ ball x f.physicalRadius)
        (hib : ∀ y, ‖f.inputMask y‖ ≤ 1),
      ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        cNorm (closedBall x RQ) (2*(d+2)+2) Q ≤ M →
        cNorm (closedBall x RQ) (2*(d+2)+2) B ≤ M →
      ∀ (W₁ : f.centers → TwoTimeAmplitude d (d+1))
        (T : f.centers → H →L[ℂ] H) (Ψ : f.centers → TwoTimePhase d)
        (χout χsource : f.centers → E → ℂ) (hs : ∀ p, ContDiff ℝ ∞ (χsource p))
        (Dgain Gain cost : f.centers → ℕ → ℝ),
        (∀ p, EndpointPdoEstimates (f.chart p).index (closedBall x RQ) Q B
          (endpointOutputMask f p output) (chartInputMask f p)
          (selectedEndpointSymbol f p threshold Q (W₁ p)) (Rbox p) M (D p) (Dgain p) (Gain p)) →
        (∀ p, RetainedSignedRetardedBounds (closedBall x RQ) Q B
          (3*(f.chart p).maskRadius/4)
          ((coordinateSplit (f.chart p).index x).1-(f.chart p).maskRadius/2)
          (Ψ p) (twoTimePhysicalApply
            (fun y a ↦ (ResidualCoordinates.coefficient (f.chart p).index Q y a).map Complex.ofReal)
            (fun y ↦ (ResidualCoordinates.zeroth (f.chart p).index B y).map Complex.ofReal) (W₁ p))
          (χout p) (χsource p) (selectedEndpointMultiplier f p threshold) (hs p) 1
          (base p) (cost p) (T p)) →
        (∀ p, GraphNormalAmplitudeBounds
          (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
            (selectedAlgebraicSymbol f p (2*threshold) Q B 1)) (Ralg p) (Malg p)) →
      ∀ (μ ν : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
        (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
        (a : (f.centers × Fin 3) ⊕ Unit) (backward : Bool),
        let P := measuredOperator μ ν hμ hν hμb hνb
          (selectedFullPairedResidualTerm f hK threshold Q B W₁ output ho hob hib T a)
        let Pdir := if backward then P.adjoint else P
        ‖Pdir‖ ≤ low a ∧ ∀ (U V : Set E) (hU : MeasurableSet U),
          ‖localRetardedOperator hU V Pdir‖ ≤ low a ∧
          ‖localRealCompression hU V Pdir‖ ≤ low a := by
  obtain ⟨low, hl, hb⟩ := exists_selectedFullPairedResidualTerm_uniform_low_constants_with_signed
    f hK hΩ hRQΩ hM Rbox Ralg Malg base D hMalg hD
  refine ⟨low, hl, ?_⟩
  intro threshold ht output ho hob hos hib Q B hQ hB hmap hQl hBl
    W₁ T Ψ χout χsource hs Dgain Gain cost hendpoint hretarded halg
    μ ν hμ hν hμb hνb a backward
  have h := hb threshold ht output ho hob hos hib Q B hQ hB hmap hQl hBl
    W₁ T Ψ χout χsource hs Dgain Gain cost hendpoint hretarded halg
    μ ν hμ hν hμb hνb a backward
  exact ⟨h.1, h.2.1⟩

/-- Every measured selected residual letter, in either literal orientation,
has a polynomial LOW bound after the SAME right proof localizer, also on
both original restriction spaces. The retained symbol and retarded budgets
produce the factor bounds; the fixed smooth compact symbol produces the
localizer bound. Constants precede the varying coefficients, threshold,
frequency, measurements and domains. This discharges the per-letter `hlow`
input of `finiteChain_observation_rapidDecayAt` without assuming a localized
operator estimate (`app:ch_regular:lem:finite-chain`,
`app:ch_regular:eq:chain-tail`). -/
theorem exists_selectedFullPairedResidualTerm_localized_low_constants_with_signed
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω) (hM : 0 ≤ M)
    (Rbox Ralg Malg base : f.centers → ℝ) (D : f.centers → ℕ → ℝ)
    (hMalg : ∀ p, 0 ≤ Malg p) (hD : ∀ p n, 0 ≤ D p n)
    (mi : FiniteChain.Graph.LocalizerSymbol (d+1))
    (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi) :
    ∃ low : ((f.centers × Fin 3) ⊕ Unit) → ℝ, (∀ a, 0 ≤ low a) ∧
      ∀ threshold ≥ f.radialThreshold,
      ∀ (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
        (_hos : tsupport output ⊆ ball x f.physicalRadius)
        (hib : ∀ y, ‖f.inputMask y‖ ≤ 1),
      ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        cNorm (closedBall x RQ) (2*(d+2)+2) Q ≤ M →
        cNorm (closedBall x RQ) (2*(d+2)+2) B ≤ M →
      ∀ (W₁ : f.centers → TwoTimeAmplitude d (d+1))
        (T : f.centers → H →L[ℂ] H) (Ψ : f.centers → TwoTimePhase d)
        (χout χsource : f.centers → E → ℂ) (hs : ∀ p, ContDiff ℝ ∞ (χsource p))
        (Dgain Gain cost : f.centers → ℕ → ℝ),
        (∀ p, EndpointPdoEstimates (f.chart p).index (closedBall x RQ) Q B
          (endpointOutputMask f p output) (chartInputMask f p)
          (selectedEndpointSymbol f p threshold Q (W₁ p)) (Rbox p) M (D p) (Dgain p) (Gain p)) →
        (∀ p, RetainedSignedRetardedBounds (closedBall x RQ) Q B
          (3*(f.chart p).maskRadius/4)
          ((coordinateSplit (f.chart p).index x).1-(f.chart p).maskRadius/2)
          (Ψ p) (twoTimePhysicalApply
            (fun y a ↦ (ResidualCoordinates.coefficient (f.chart p).index Q y a).map Complex.ofReal)
            (fun y ↦ (ResidualCoordinates.zeroth (f.chart p).index B y).map Complex.ofReal) (W₁ p))
          (χout p) (χsource p) (selectedEndpointMultiplier f p threshold) (hs p) 1
          (base p) (cost p) (T p)) →
        (∀ p, GraphNormalAmplitudeBounds
          (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
            (selectedAlgebraicSymbol f p (2*threshold) Q B 1)) (Ralg p) (Malg p)) →
      ∀ (μ ν : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
        (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
        (a : (f.centers × Fin 3) ⊕ Unit) (backward : Bool),
        let P := measuredOperator μ ν hμ hν hμb hνb
          (selectedFullPairedResidualTerm f hK threshold Q B W₁ output ho hob hib T a)
        let Pdir := if backward then P.adjoint else P
        ∀ ρ : ℝ, 1 ≤ ρ → ∀ Mi : H →L[ℂ] H,
          (∀ u : H, Mi u =ᵐ[volume] fun y ↦ WithLp.toLp 2
            (FiniteChain.Graph.rightLocalizer ρ mi (fun z ↦ (u z).ofLp) y)) →
          (∀ u, ‖Pdir (Mi u)‖ ≤ low a * ρ^(d+1) * ‖u‖) ∧
          (∀ (U V : Set E) (hU : MeasurableSet U),
            (∀ u, ‖localRetardedOperator hU V Pdir (localRetardedOperator hU U Mi u)‖ ≤
              low a * ρ^(d+1) * ‖u‖) ∧
            (∀ u, ‖localRealCompression hU V Pdir (localRealCompression hU U Mi u)‖ ≤
              low a * ρ^(d+1) * ‖u‖)) ∧
          ∀ reflected : Bool,
            let Ps := measuredOperator μ ν hμ hν hμb hνb
              (selectedFullPhysicalResidualTerm f hK threshold Q B W₁ output ho hob hib T (a, reflected))
            let Psdir := if backward then Ps.adjoint else Ps
            (∀ u, ‖Psdir (Mi u)‖ ≤ low a * ρ^(d+1) * ‖u‖) ∧
            ∀ (U V : Set E) (hU : MeasurableSet U),
              ∀ u, ‖localRetardedOperator hU V Psdir (localRetardedOperator hU U Mi u)‖ ≤
                low a * ρ^(d+1) * ‖u‖ := by
  obtain ⟨rawLow, hrawLow, hraw⟩ :=
    exists_selectedFullPairedResidualTerm_uniform_low_constants_with_signed
      f hK hΩ hRQΩ hM Rbox Ralg Malg base D hMalg hD
  obtain ⟨C, hC, hc⟩ := exists_rightLocalizer_polynomial_low_bound (r := d+1) mi hi his
  refine ⟨fun a ↦ C * rawLow a, fun a ↦ mul_nonneg hC (hrawLow a), ?_⟩
  intro threshold ht output ho hob hos hib Q B hQ hB hmap hQl hBl
    W₁ T Ψ χout χsource hs Dgain Gain cost hendpoint hretarded halg
    μ ν hμ hν hμb hνb a backward P Pdir ρ hρ Mi hMi
  have hr := hraw threshold ht output ho hob hos hib Q B hQ hB hmap hQl hBl
    W₁ T Ψ χout χsource hs Dgain Gain cost hendpoint hretarded halg
    μ ν hμ hν hμb hνb a backward
  have hmi := hc ρ hρ Mi hMi
  have hbound {𝕜 X Y : Type} [NontriviallyNormedField 𝕜]
      [NormedAddCommGroup X] [NormedAddCommGroup Y]
      [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
      (S : X →L[𝕜] Y) (N : X →L[𝕜] X)
      (hS : ‖S‖ ≤ rawLow a) (hN : ‖N‖ ≤ C * ρ^(d+1)) (u : X) :
      ‖S (N u)‖ ≤ C * rawLow a * ρ^(d+1) * ‖u‖ := by
    calc
      _ ≤ rawLow a * ‖N u‖ := S.le_of_opNorm_le hS _
      _ ≤ rawLow a * (C * ρ^(d+1) * ‖u‖) :=
        mul_le_mul_of_nonneg_left (N.le_of_opNorm_le hN u) (hrawLow a)
      _ = _ := by ring
  refine ⟨hbound (𝕜 := ℂ) Pdir Mi hr.1 hmi, ?_, ?_⟩
  · intro U V hU
    exact ⟨hbound (𝕜 := ℝ) _ _ (hr.2.1 U V hU).1
        ((selected_localRetardedOperator_norm_le hU U Mi).trans hmi),
      hbound (𝕜 := ℝ) _ _ (hr.2.1 U V hU).2
        ((selected_localRealCompression_norm_le hU U Mi).trans hmi)⟩
  · intro reflected Ps Psdir
    have hsigned := hr.2.2 reflected
    exact ⟨hbound (𝕜 := ℂ) Psdir Mi hsigned.1 hmi,
      fun U V hU ↦ hbound (𝕜 := ℝ) _ _ (hsigned.2 U V hU)
        ((selected_localRetardedOperator_norm_le hU U Mi).trans hmi)⟩

/-- The original paired localized LOW bound is projected without changing
its domains or quantifiers (`app:ch_regular:eq:chain-tail`). -/
theorem exists_selectedFullPairedResidualTerm_localized_low_constants
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω) (hM : 0 ≤ M)
    (Rbox Ralg Malg base : f.centers → ℝ) (D : f.centers → ℕ → ℝ)
    (hMalg : ∀ p, 0 ≤ Malg p) (hD : ∀ p n, 0 ≤ D p n)
    (mi : FiniteChain.Graph.LocalizerSymbol (d+1))
    (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi) :
    ∃ low : ((f.centers × Fin 3) ⊕ Unit) → ℝ, (∀ a, 0 ≤ low a) ∧
      ∀ threshold ≥ f.radialThreshold,
      ∀ (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
        (_hos : tsupport output ⊆ ball x f.physicalRadius)
        (hib : ∀ y, ‖f.inputMask y‖ ≤ 1),
      ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        cNorm (closedBall x RQ) (2*(d+2)+2) Q ≤ M →
        cNorm (closedBall x RQ) (2*(d+2)+2) B ≤ M →
      ∀ (W₁ : f.centers → TwoTimeAmplitude d (d+1))
        (T : f.centers → H →L[ℂ] H) (Ψ : f.centers → TwoTimePhase d)
        (χout χsource : f.centers → E → ℂ) (hs : ∀ p, ContDiff ℝ ∞ (χsource p))
        (Dgain Gain cost : f.centers → ℕ → ℝ),
        (∀ p, EndpointPdoEstimates (f.chart p).index (closedBall x RQ) Q B
          (endpointOutputMask f p output) (chartInputMask f p)
          (selectedEndpointSymbol f p threshold Q (W₁ p)) (Rbox p) M (D p) (Dgain p) (Gain p)) →
        (∀ p, RetainedSignedRetardedBounds (closedBall x RQ) Q B
          (3*(f.chart p).maskRadius/4)
          ((coordinateSplit (f.chart p).index x).1-(f.chart p).maskRadius/2)
          (Ψ p) (twoTimePhysicalApply
            (fun y a ↦ (ResidualCoordinates.coefficient (f.chart p).index Q y a).map Complex.ofReal)
            (fun y ↦ (ResidualCoordinates.zeroth (f.chart p).index B y).map Complex.ofReal) (W₁ p))
          (χout p) (χsource p) (selectedEndpointMultiplier f p threshold) (hs p) 1
          (base p) (cost p) (T p)) →
        (∀ p, GraphNormalAmplitudeBounds
          (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
            (selectedAlgebraicSymbol f p (2*threshold) Q B 1)) (Ralg p) (Malg p)) →
      ∀ (μ ν : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
        (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
        (a : (f.centers × Fin 3) ⊕ Unit) (backward : Bool),
        let P := measuredOperator μ ν hμ hν hμb hνb
          (selectedFullPairedResidualTerm f hK threshold Q B W₁ output ho hob hib T a)
        let Pdir := if backward then P.adjoint else P
        ∀ ρ : ℝ, 1 ≤ ρ → ∀ Mi : H →L[ℂ] H,
          (∀ u : H, Mi u =ᵐ[volume] fun y ↦ WithLp.toLp 2
            (FiniteChain.Graph.rightLocalizer ρ mi (fun z ↦ (u z).ofLp) y)) →
          (∀ u, ‖Pdir (Mi u)‖ ≤ low a * ρ^(d+1) * ‖u‖) ∧
          ∀ (U V : Set E) (hU : MeasurableSet U),
            (∀ u, ‖localRetardedOperator hU V Pdir (localRetardedOperator hU U Mi u)‖ ≤
              low a * ρ^(d+1) * ‖u‖) ∧
            (∀ u, ‖localRealCompression hU V Pdir (localRealCompression hU U Mi u)‖ ≤
              low a * ρ^(d+1) * ‖u‖) := by
  obtain ⟨low, hl, hb⟩ := exists_selectedFullPairedResidualTerm_localized_low_constants_with_signed
    f hK hΩ hRQΩ hM Rbox Ralg Malg base D hMalg hD mi hi his
  refine ⟨low, hl, ?_⟩
  intro threshold ht output ho hob hos hib Q B hQ hB hmap hQl hBl
    W₁ T Ψ χout χsource hs Dgain Gain cost hendpoint hretarded halg
    μ ν hμ hν hμb hνb a backward P Pdir ρ hρ Mi hMi
  have h := hb threshold ht output ho hob hos hib Q B hQ hB hmap hQl hBl
    W₁ T Ψ χout χsource hs Dgain Gain cost hendpoint hretarded halg
    μ ν hμ hν hμb hνb a backward ρ hρ Mi hMi
  exact ⟨h.1, h.2.1⟩

end JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
