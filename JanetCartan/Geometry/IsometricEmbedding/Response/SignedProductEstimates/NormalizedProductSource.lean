module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedSignedSource

/-!
# Actual ProductSum sources in the corrected angular-error estimate

Specialize the checked discrepancy estimate to the literal plus/minus sources.
The normalized phase is the sum/difference divided by its true frequency;
no signed pair is identified with a single Hamilton primary. The original
stress row, both source cutoffs and doubled plus diagonal are retained.
Consumer: `app:ch_pairs:eq:pairs-lag-one-error` and `UniformStep.SampledProduct`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.SignedProductEstimates
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open ResponseTransfer.SourceNegative Sampling.BackgroundModulation Pseudodifferential
open ArbitraryAccuracy ArbitraryAccuracy.ResidualLocalization LocalSobolev
open RegularSector.Characteristic.RetardedLocalization
variable {d N : ℕ} {Ω : Set (Euclidean (d+1))} {center : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => Lp V 2 (volume : Measure E)

variable {ι : Type*}

/-- Each literal reduced `ProductSum.plusSource` or `minusSource` has the
original stage-decaying corrected-source discrepancy, at every positive or
negative Sobolev order below the requested order. The plus diagonal is allowed;
only the difference diagonal is excluded. Constants precede the chosen
samples, phases, row and history. All analytic inputs are primitive signed
phase/amplitude jets and terminal coverage (`app:ch_pairs:prop:pairs-lag-sum`). -/
theorem exists_normalized_product_source_discrepancy_constants
    (f : ActualMaskFamily Ω center RQ A₀ K M) (hK : IsCompact K)
    (L₀ : ℝ) (hL₀ : f.radialThreshold ≤ L₀)
    {T : Set E} (hT : IsCompact T) (hTK : T ⊆ K) (hTneg : ∀ v ∈ T, -v ∈ T)
    {S : Set E} (hS : IsCompact S) (hScore : S ⊆ closedBall center f.physicalRadius)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1) (hop : ∀ y ∈ S, output y = 1)
    {a G cbeat : ℝ} (ha : 0 < a) (hG : 0 < G) (hbeat : 0 < cbeat)
    (Cscale : ℝ) (P X Y CQ C : ℕ → ℝ)
    (hP : ∀ r, 0 ≤ P r) (hX : ∀ r, 0 ≤ X r) (hY : ∀ r, 0 ≤ Y r)
    (hCQ : ∀ r, 0 ≤ CQ r) (hC : ∀ r, 0 ≤ C r) (s : ℕ) :
    ∃ Rmin : ℝ, 2 ≤ Rmin ∧ ∀ q : ℕ, ∃ D : ℝ, 0 ≤ D ∧
      ∀ (U : Set E), IsOpen U → S ⊆ U →
      ∀ (χ ψ : E → ℝ) (Q : E → Fin (d+1) → MetricTensor (d+1))
        (θ : ι → E → ℝ) (A : ι → E → Matrix (Fin N) (Fin (d+1)) ℂ)
        (minus : Bool) (i j : ι), (minus = true → i ≠ j) → ∀ R L ρ : ℝ,
      let φ := fun y ↦ (if minus then θ i y - θ j y else θ i y + θ j y) / ρ
      ContDiffOn ℝ ∞ χ U → ContDiffOn ℝ ∞ ψ U → ContDiffOn ℝ ∞ Q U →
      ContDiffOn ℝ ∞ φ U → ContDiffOn ℝ ∞ (A i) U → ContDiffOn ℝ ∞ (A j) U →
      tsupport χ ⊆ S → 1 ≤ L → Rmin ≤ R →
      cbeat * (R ^ carrierExponent * R ^ (-separationExponent)) ≤ ρ →
      L ≤ Cscale * R ^ (1+meanSlack) →
      (∀ y ∈ U, a ≤ ‖fderiv ℝ φ y‖ ∧ ‖fderiv ℝ φ y‖ ≤ G) →
      (∀ y ∈ U, NormedSpace.normalize (fderiv ℝ φ y) ∈ (InnerProductSpace.toDual ℝ E) '' T) →
      (∀ y ∈ S, ∀ r, 1 ≤ r → ‖iteratedFDeriv ℝ (r+1) φ y‖ ≤ P r * L^r) →
      (∀ y ∈ U, ∀ r, ‖iteratedFDeriv ℝ r χ y‖ ≤ X r * L^r) →
      (∀ y ∈ U, ∀ r, ‖iteratedFDeriv ℝ r ψ y‖ ≤ Y r * L^r) →
      (∀ y ∈ U, ∀ r, ‖iteratedFDeriv ℝ r Q y‖ ≤ CQ r * L^r) →
      (∀ y ∈ U, ∀ r, ‖iteratedFDeriv ℝ r (A i) y‖ ≤ C r * L^r) →
      (∀ y ∈ U, ∀ r, ‖iteratedFDeriv ℝ r (A j) y‖ ≤ C r * L^r) →
      let g := fun y ↦ WithLp.toLp 2 (AmbientResponse.cutoffSource ψ (AmbientResponse.stressSource Q
        (fun z ↦ χ z • (if minus then ProductSum.minusSource θ A i j z else ProductSum.plusSource θ A i j z))) y)
      ∃ hg : MemLp g 2 volume,
        (∀ t : ℝ, t ≤ s →
          let e := (realSource f hK L₀ output ho.continuous hob - 1) (hg.toLp g)
          MemComponentFourierSobolev (EuclideanSpace.basisFun (Fin (d+1)) ℝ) t e ∧
          componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin (d+1)) ℝ) t e ≤
            D * ((R ^ carrierExponent * R ^ (-separationExponent))^q)⁻¹) ∧
        ∀ (W : Set E) (hW : MeasurableSet W), tsupport χ ⊆ W → ∀ Vout : Set E,
          let localError := localRealCompression hW Vout
            (pairedSource f hK L₀ output ho.continuous hob - 1)
            ((hg.mono_measure (Measure.restrict_le_self (s := W))).toLp g)
          MemRestrictionSobolev Vout s localError ∧ restrictionSobolevNorm Vout s localError ≤
            D * ((R ^ carrierExponent * R ^ (-separationExponent))^q)⁻¹ := by
  obtain ⟨Rmin, hmin, htail⟩ := exists_normalized_signed_source_quadrature_constants (N := N)
    f hK L₀ hL₀ hT hTK hTneg hS hScore output ho hoc hob hop ha hG hbeat Cscale
    P X Y CQ C hP hX hY hCQ hC s
  refine ⟨Rmin, hmin, fun q ↦ ?_⟩
  obtain ⟨D, hD, hsource⟩ := htail q
  refine ⟨D, hD, ?_⟩
  intro U hU hSU χ ψ Q θ A minus i j _hdiag R L ρ φ hχ hψ hQ hφ hA hB hχS hL hR hρ hslow
    hband hprotected hphase hχb hψb hQb hAb hBb g
  have hRp : 0 < R := lt_of_lt_of_le (by norm_num) (hmin.trans hR)
  have hρpos : 0 < ρ := (mul_pos hbeat (by positivity)).trans_le hρ
  obtain ⟨hp, hm⟩ := hsource U hU hSU χ ψ φ Q (A i) (A j) R L ρ hχ hψ hQ hφ hA hB
    hχS hL hR hρ hslow hband hprotected hphase hχb hψb hQb hAb hBb
  have hfinish (b : E → V) (he : g = fun y ↦ euclideanRealPart (modulatedSource χ φ b ρ y))
      (hb : ∃ hg : MemLp (modulatedSource χ φ b ρ) 2 volume,
        (∀ t : ℝ, t ≤ s →
          let e := (realSource f hK L₀ output ho.continuous hob - 1)
            (l2RealPart volume (hg.toLp (modulatedSource χ φ b ρ)))
          MemComponentFourierSobolev (EuclideanSpace.basisFun (Fin (d+1)) ℝ) t e ∧
          componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin (d+1)) ℝ) t e ≤
            D * ((R ^ carrierExponent * R ^ (-separationExponent))^q)⁻¹) ∧
        ∀ (W : Set E) (hW : MeasurableSet W), tsupport χ ⊆ W → ∀ Vout : Set E,
          let localError := localRealCompression hW Vout
            (pairedSource f hK L₀ output ho.continuous hob - 1)
            (l2RealPart (volume.restrict W) (restrictL2 W (hg.toLp (modulatedSource χ φ b ρ))))
          MemRestrictionSobolev Vout s localError ∧ restrictionSobolevNorm Vout s localError ≤
            D * ((R ^ carrierExponent * R ^ (-separationExponent))^q)⁻¹) :
      ∃ hg : MemLp g 2 volume,
        (∀ t : ℝ, t ≤ s →
          let e := (realSource f hK L₀ output ho.continuous hob - 1) (hg.toLp g)
          MemComponentFourierSobolev (EuclideanSpace.basisFun (Fin (d+1)) ℝ) t e ∧
          componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin (d+1)) ℝ) t e ≤
            D * ((R ^ carrierExponent * R ^ (-separationExponent))^q)⁻¹) ∧
        ∀ (W : Set E) (hW : MeasurableSet W), tsupport χ ⊆ W → ∀ Vout : Set E,
          let localError := localRealCompression hW Vout
            (pairedSource f hK L₀ output ho.continuous hob - 1)
            ((hg.mono_measure (Measure.restrict_le_self (s := W))).toLp g)
          MemRestrictionSobolev Vout s localError ∧ restrictionSobolevNorm Vout s localError ≤
            D * ((R ^ carrierExponent * R ^ (-separationExponent))^q)⁻¹ := by
    obtain ⟨hb, hbound⟩ := hb
    let u := hb.toLp (modulatedSource χ φ b ρ)
    have hrep : l2RealPart volume u =ᵐ[volume] g := by
      rw [he]
      filter_upwards [euclideanRealPart.coeFn_compLpL u, hb.coeFn_toLp] with y hr hu
      exact hr.trans (congrArg euclideanRealPart hu)
    have hg : MemLp g 2 volume := (Lp.memLp (l2RealPart volume u)).ae_eq hrep
    have hu : hg.toLp g = l2RealPart volume u := by
      apply Lp.ext
      exact hg.coeFn_toLp.trans hrep.symm
    refine ⟨hg, ?_, ?_⟩
    · rw [hu]
      exact hbound.1
    · intro W hW hχW Vout
      have hloc : (hg.mono_measure (Measure.restrict_le_self (s := W))).toLp g =
          l2RealPart (volume.restrict W) (restrictL2 W u) := by
        apply Lp.ext
        filter_upwards [(hg.mono_measure (Measure.restrict_le_self (s := W))).coeFn_toLp,
          euclideanRealPart.coeFn_compLpL (restrictL2 W u), restrictL2_coeFn W u,
          ae_restrict_of_ae (euclideanRealPart.coeFn_compLpL u), ae_restrict_of_ae hrep]
          with y hg' hr hl hgr hgR
        change (l2RealPart (volume.restrict W) (restrictL2 W u)) y = _ at hr
        change (l2RealPart volume u) y = _ at hgr
        rw [hg', hr, hl, ← hgr, hgR]
      dsimp only
      rw [hloc]
      exact hbound.2 W hW hχW Vout
  cases minus with
  | false =>
    obtain ⟨hg, hb⟩ := hp
    apply hfinish _ (cutoff_stressSource_plus_eq_real_modulatedSource Q χ ψ θ A i j hρpos.ne')
    exact ⟨hg, by simpa only [one_smul] using hb 1 (by simp)⟩
  | true =>
    obtain ⟨hg, hb⟩ := hm
    apply hfinish _ (cutoff_stressSource_minus_eq_real_modulatedSource Q χ ψ θ A i j hρpos.ne')
    exact ⟨hg, by simpa only [one_smul] using hb 1 (by simp)⟩

end JanetCartan.SignedProductEstimates
