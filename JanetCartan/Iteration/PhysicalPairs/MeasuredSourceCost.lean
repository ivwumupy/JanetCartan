module
public import JanetCartan.Iteration.PhysicalPairs.SampledMask
public import JanetCartan.Iteration.PhysicalPairs.OriginalSignedData
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ObservedSourceInputs

/-! # Low norm of the actual once-measured signed stress

Obtain the norm hypotheses for the native observed chain **without applying
another bump to the already measured source**. A direct order-zero estimate of
the same two full derivative amplitudes controls its actual zero-extension on
the fixed compact. The local norm is its isometric pullback and complex inclusion
is contractive. `app:ch_regular:lem:finite-chain`, `app:ch_pairs:prop:pairs-lag-sum`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric MeasureTheory Filter
open scoped NNReal ENNReal ContDiff ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPairs.MeasuredSourceCost
open SmallSupport LocalSobolev SignedProductEstimates Sampling.BackgroundModulation ResponseSourceExtension ResponseTransfer.SourceNegative
open PhysicalInitialization.OriginalSampledObserved RegularSector.NormalizedResidualWords.ObservedChains
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
variable {d N : ℕ}
local notation "E" => Euclidean (d+1)
local notation "CV" => EuclideanSpace ℂ (Fin (d+1))

private theorem real_part_contracts {n : ℕ} (z : EuclideanSpace ℂ (Fin n)) : ‖euclideanRealPart z‖ ≤ ‖z‖ := by
  simpa only [one_mul] using (euclideanRealPart (ι := Fin n)).le_of_opNorm_le (euclideanRealPart_norm_le (ι := Fin n)) z

/-- The fixed price precedes EVERY frequency, label, history and normalized
phase. There is no chosen second pair, data cutoff, or L² bound hypothesis. -/
theorem exists_cost {S : Set E} (hS : IsCompact S) (X Y CQ C : ℕ → ℝ)
    (hX : ∀ j, 0 ≤ X j) (hY : ∀ j, 0 ≤ Y j) (hCQ : ∀ j, 0 ≤ CQ j) (hC : ∀ j, 0 ≤ C j) :
    ∃ D ≥ (0:ℝ), ∀ (U W : Set E) (_hU : IsOpen U) (hW : MeasurableSet W)
      (χ ψ : E → ℝ) (Q : E → Fin (d+1) → MetricTensor (d+1)) (A B : E → Matrix (Fin N) (Fin (d+1)) ℂ),
      ContDiffOn ℝ ∞ χ U → ContDiffOn ℝ ∞ ψ U → ContDiffOn ℝ ∞ Q U → ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ B U →
      tsupport χ ⊆ S → tsupport χ ⊆ U → ∀ (L : ℝ), 1 ≤ L →
      (∀ y ∈ U, ∀ j, ‖iteratedFDeriv ℝ j χ y‖ ≤ X j*L^j) → (∀ y ∈ U, ∀ j, ‖iteratedFDeriv ℝ j ψ y‖ ≤ Y j*L^j) →
      (∀ y ∈ U, ∀ j, ‖iteratedFDeriv ℝ j Q y‖ ≤ CQ j*L^j) → (∀ y ∈ U, ∀ j, ‖iteratedFDeriv ℝ j A y‖ ≤ C j*L^j) →
      (∀ y ∈ U, ∀ j, ‖iteratedFDeriv ℝ j B y‖ ≤ C j*L^j) → ∀ (minus : Bool) (φ : E → ℝ) (ρ : ℝ) (u : LocalL2 W E),
      zeroExtend hW u =ᵐ[volume] (fun y ↦ euclideanRealPart (SampledMask.reduced_wave χ ψ Q A B minus φ ρ y)) →
      ‖u‖ ≤ D ∧ ‖complexSource hW u‖ ≤ D := by
  obtain ⟨J,hJ,hall⟩ := exists_cutoff_reduced_signed_jet_constants (n := d+1) (N := N) X Y CQ C hX hY hCQ hC
  refine ⟨J 0*Real.sqrt (volume.real S),mul_nonneg (hJ 0) (Real.sqrt_nonneg _),?_⟩
  intro U W hU hW χ ψ Q A B hχ hψ hQ hA hB hχS hχU L hL hχj hψj hQj hAj hBj minus φ ρ u hu
  let a := fun y ↦ ψ y • ((1/2:ℝ) • complexStressContraction (Q y) (if minus then
    symmetricBilinearTensor (A y) ((B y).map conj) else symmetricBilinearTensor (A y) (B y)))
  let v := SampledMask.reduced_wave χ ψ Q A B minus φ ρ
  have hj := hall U hU L hL χ ψ Q A B hχ hψ hQ hA hB hχj hψj hQj hAj hBj
  have hz (y : E) (hy : y ∉ S) : euclideanRealPart (v y) = 0 := by
    have hh : χ y = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hχS h))
    simp only [v,SampledMask.reduced_wave,modulatedSource,hh,zero_smul,map_zero]
  have hyb (y : E) : ‖euclideanRealPart (v y)‖ ≤ J 0 := by
    by_cases hy : y ∈ U
    · have ha : ‖χ y • a y‖ ≤ J 0 := by
        cases minus
        · simpa only [a,Bool.false_eq_true,↓reduceIte,norm_iteratedFDeriv_zero,pow_zero,mul_one] using (hj y hy 0).1
        · simpa only [a,↓reduceIte,norm_iteratedFDeriv_zero,pow_zero,mul_one] using (hj y hy 0).2
      have hv : ‖v y‖ = ‖χ y • a y‖ := by
        change ‖modulatedSource χ φ a ρ y‖ = ‖χ y • a y‖
        rw [norm_smul,Real.norm_eq_abs]
        exact norm_modulatedSource χ φ a ρ y
      exact (real_part_contracts (v y)).trans (hv.le.trans ha)
    · have hh : χ y = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hχU h))
      simpa only [v,SampledMask.reduced_wave,modulatedSource,hh,zero_smul,map_zero,norm_zero] using hJ 0
  have hbound : ‖zeroExtend hW u‖ ≤ ‖indicatorConstLp (μ := volume) 2 hS.measurableSet hS.measure_ne_top (J 0)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hu,indicatorConstLp_coeFn (μ := volume) (p := 2) (hs := hS.measurableSet) (hμs := hS.measure_ne_top) (c := J 0)] with y hy hi
    rw [hy,hi]
    by_cases hyS : y ∈ S
    · simpa only [indicator_of_mem hyS,Real.norm_eq_abs,abs_of_nonneg (hJ 0)] using hyb y
    · simp only [indicator_of_notMem hyS,show euclideanRealPart (SampledMask.reduced_wave χ ψ Q A B minus φ ρ y) = 0 from hz y hyS,norm_zero,le_refl]
  have hn : ‖u‖ ≤ J 0*Real.sqrt (volume.real S) := by
    rw [← (zeroExtend hW).norm_map u]
    convert hbound using 1
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp only [Real.norm_eq_abs,abs_of_nonneg (hJ 0),ENNReal.toReal_ofNat,Real.sqrt_eq_rpow,one_div]
  exact ⟨hn,(complex_source_norm_le hW u).trans hn⟩
/-- The literal measured source is zero away from the inner bump; this
uses no assumption whatsoever about the initial smooth local datum. -/
theorem measured_support {D : Set E} {x : E} (χ₂ : ContDiffBump x) (v : FixedDomainInverse.smoothSource D E) :
    ∀ᵐ y ∂volume.restrict D, y ∉ tsupport (χ₂ : E → ℝ) → OriginalSignedData.innerDatum χ₂ v y = 0 :=
  cut_source_ae_zero_off_support χ₂ v.val
end JanetCartan.PhysicalPairs.MeasuredSourceCost
end

public meta section
set_option maxHeartbeats 600000
set_option maxRecDepth 16000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.MeasuredSourceCost
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.MeasuredSourceCost
private def data := `JanetCartan.PhysicalPairs.OriginalSignedData
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def world := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Source
private def mask := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def a (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
elab "publish_measured_support " piece:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (hist ++ `index)).type (some 49) fun p gf => do
    let fixed := gf.getAppArgs[:23].toArray
    let d := p[0]!
    let χ₂ := a (reg ++ `χ₂) fixed
    let center := (← inferType χ₂).appArg!
    let W := a (world ++ `W) fixed
    let hW := a (world ++ `W_measurable) fixed
    forallBoundedTelescope (← inferType (a (data ++ `uncut) p)) (some 1) fun wave _ => do
      let v := p ++ wave
      let u := a (data ++ `measured) v
      if piece.getNat == 0 then
        let pf := a (ns ++ `measured_support) #[d,W,center,χ₂,a (data ++ `uncut) v]
        let ty := (← inferType pf).replace fun e => if e.isAppOfArity (data ++ `innerDatum) 5 then some u else none
        discard <| store (ns ++ `native_support) v pf false (some ty)
      else
        let proof := a `JanetCartan.RegularSector.NormalizedResidualWords.ObservedChains.complex_source_plateau_of_support
          #[d,center,W,hW,χ₂,a (reg ++ `χ₃) fixed,a (mask ++ `χ₃_on_χ₂) fixed,u,a (ns ++ `native_support) v]
        discard <| store (ns ++ `outer_plateau) v proof
publish_measured_support 0
publish_measured_support 1
end JanetCartan.PhysicalPairs.MeasuredSourceCost
end
