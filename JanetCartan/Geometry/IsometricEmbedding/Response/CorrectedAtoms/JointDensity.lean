module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.JointRegularity
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.ResponseDensity
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.SecondJet

/-!
# Density Lipschitz bounds for the literal corrected atoms

This applies the bilinear density estimate to the SAME raw, leading and response
amplitudes in `app:ch_response:eq:current-density-lipschitz`. Their linear maps
and raw/leading regularity are constructed, not additional premises. A single
auxiliary joint cutoff is chosen solely from the fixed compact observation set
and its open chart. Every jet there agrees with the original amplitudes, so no
cutoff cost or change of response/source enters the conclusion.

`HomogeneousRawBounds` derives the homogeneous scalar-span bounds from the
retained raw finite-jet budgets on a fixed primitive class with positive margin.
`RetainedDensity` substitutes them into this underlying bilinear deduction.
The fixed response's joint regularity and derivative bound remain analytic
producer obligations. This theorem does not assert their uniform instantiation
on initialized histories.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.CorrectedAtoms
open RawPrimary LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open PrimarySourceAdmission

/-- A fixed auxiliary joint cutoff extends chart amplitudes smoothly for the
density proof (`app:ch_response:eq:current-density-lipschitz`). -/
private theorem contDiff_jointCutoff {D E : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ψ : D → ℝ} {f : D → E} {O : Set D}
    (hψ : ContDiff ℝ ∞ ψ) (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (hs : tsupport ψ ⊆ O) : ContDiff ℝ ∞ (fun x ↦ ψ x • f x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport ψ
  · exact hψ.contDiffAt.smul (hf.contDiffAt (hO.mem_nhds (hs hx)))
  · apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp [hy]

/-- The auxiliary cutoff changes no jet on its plateau, for any amplitude or
order (`app:ch_response:eq:current-density-lipschitz`). -/
private theorem jointCutoff_eventuallyEq {D E : Type*} [TopologicalSpace D]
    [AddCommMonoid E] [Module ℝ E] (ψ : D → ℝ) (f : D → E)
    {x : D} (hx : x ∈ interior {y | ψ y = 1}) :
    (fun y ↦ ψ y • f y) =ᶠ[𝓝 x] f := by
  filter_upwards [isOpen_interior.mem_nhds hx] with y hy
  have he := (interior_subset : interior {y | ψ y = 1} ⊆ {y | ψ y = 1}) hy
  change ψ y = 1 at he
  change ψ y • f y = f y
  rw [he, one_smul]

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))

/-- The Hermitian density error of the literal corrected amplitude and its
original leading matrix (`app:ch_response:eq:current-density-lipschitz`). -/
def fullCorrectedDensityError (r : Euclidean (n - 1) × Euclidean 3 → ℝ) (τ : ℝ)
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) : Matrix (Fin n) (Fin n) ℝ :=
  hermitianTensor (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ w) -
    hermitianTensor (fullLeadingPrincipalMatrix T Q F row col Φ Y r w)

/-- The subtracted density is exactly the original real rank-one leading
tensor, with the same normal and phase covector. This identifies the density
used in the current-mean consumer (`app:ch_response:eq:current-density-lipschitz`,
`app:ch_waves:eq:arbitrary-b-amplitudes`). -/
theorem fullCorrectedDensityError_eq_rankOne
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ) (τ : ℝ)
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) (i j : Fin n) :
    fullCorrectedDensityError T Q F row col Φ Y χ B r τ w i j =
      hermitianTensor (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ w) i j -
        ‖LeadingWave.principalNormal (AmbientResponse.canonicalNormalCompletion F w.1)
          (phaseGradient T Q w.1 w.2.2) (fullLeadingCovector T Q F row col Φ Y r w)‖^2 *
            phaseGradient T Q w.1 w.2.2 i * phaseGradient T Q w.1 w.2.2 j := by
  change hermitianTensor (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ w) i j -
    hermitianTensor (fullLeadingPrincipalMatrix T Q F row col Φ Y r w) i j = _
  rw [fullLeadingPrincipalMatrix, hermitianTensor_ofReal,
    LeadingWave.principalMatrix_transpose_mul]

/-- The density Lipschitz bound for the SAME literal corrected atoms, jointly
in physical and carrier variables, on the unchanged compact observation set.
The initial-scalar jet budget `d` and constants precede `τ`. Raw estimates
`hleading,hprimary` belong to `RawPrimary`; `both-response-transfer` must supply
`hresponse,hresponseBound` for the same fixed `B`. Scalar linearity and raw/leading
regularity are discharged here. Neither the reference, response, source cutoff
nor leading tensor is reselected (`app:ch_response:eq:current-density-lipschitz`). -/
theorem cNorm_fullCorrectedDensityError_sub_le
    {Ω O K : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    {z₀ : Euclidean 3} {R Mᵣ m : ℝ}
    (hα : ∀ r ∈ primitiveInitialScalars (n := n) z₀ R Mᵣ m,
      ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hO : IsOpen O) (hOΩ : O ⊆ Ω) (hK : IsCompact K) (hKO : K ⊆ O)
    (hsrc : ∀ w ∈ O, ∀ x ∈ tsupport χ, (x, w.2) ∈ Ω)
    (Kr : Set (Euclidean (n - 1) × Euclidean 3)) (s d : ℕ)
    {C₀ Kpr Kresp : ℝ} (hC₀ : 0 ≤ C₀) (hKpr : 0 ≤ Kpr) (hKresp : 0 ≤ Kresp)
    {τ : ℝ} (hτ : 0 < τ) (hτ₁ : τ ≤ 1)
    (hresponse : ∀ r : initialScalarSpan (n := n) z₀ R Mᵣ m,
      ContDiffOn ℝ ∞ (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) O)
    (hleading : ∀ r : initialScalarSpan (n := n) z₀ R Mᵣ m,
      cNorm K s (fullLeadingPrincipalMatrix T Q F row col Φ Y r) ≤ C₀ * cNorm Kr d (r : Euclidean (n - 1) × Euclidean 3 → ℝ))
    (hprimary : ∀ r : initialScalarSpan (n := n) z₀ R Mᵣ m,
      cNorm K s (fullDerivativeAmplitude T Q F row col Φ Y r τ -
        fullLeadingPrincipalMatrix T Q F row col Φ Y r) ≤ Kpr * τ * cNorm Kr d (r : Euclidean (n - 1) × Euclidean 3 → ℝ))
    (hresponseBound : ∀ r : initialScalarSpan (n := n) z₀ R Mᵣ m,
      cNorm K s (fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B r τ) ≤
        Kresp * τ * cNorm Kr d (r : Euclidean (n - 1) × Euclidean 3 → ℝ))
    (r r' : initialScalarSpan (n := n) z₀ R Mᵣ m) :
    cNorm K s (fullCorrectedDensityError T Q F row col Φ Y χ B r τ -
      fullCorrectedDensityError T Q F row col Φ Y χ B r' τ) ≤
      (2 * (2 : ℝ)^s * (C₀ + Kpr + Kresp) * (Kpr + Kresp)) * τ *
        (cNorm Kr d (r : Euclidean (n - 1) × Euclidean 3 → ℝ) + cNorm Kr d (r' : Euclidean (n - 1) × Euclidean 3 → ℝ)) *
          cNorm Kr d ((r : Euclidean (n - 1) × Euclidean 3 → ℝ) -
            (r' : Euclidean (n - 1) × Euclidean 3 → ℝ)) := by
  obtain ⟨ψ, hψ, _hrange, _hcompact, hψO, hplateau⟩ :=
    CompatibleResponse.exists_compact_family_cutoff hK hO hKO
  have hB (a : initialScalarSpan (n := n) z₀ R Mᵣ m) (w) (hw : w ∈ tsupport ψ) :
      DifferentiableAt ℝ (fullPrimaryResponse T Q F row col Φ Y χ B τ a w.2) w.1 := by
    exact ((((hresponse a).contDiffAt (hO.mem_nhds (hψO hw))).comp w.1
      (f := fun x : Euclidean n ↦ (x, w.2))
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))
  obtain ⟨Apr, A₀, Yresp, hmaps⟩ := exists_cutoffFullAmplitudeLinearMaps T Q F row col Φ Y
    hΩ hspace hphase hF hi hrank hnonzero hα χ hχ hc B ψ (hψO.trans hOΩ)
    (fun w hw ↦ hsrc w (hψO hw)) hτ.ne' hB
  have hαspan (a : initialScalarSpan (n := n) z₀ R Mᵣ m) :=
    contDiffOn_scalarAmplitude_of_mem_initialScalarSpan T Q F row col Φ Y hα a.property
  have hpreg (a : initialScalarSpan (n := n) z₀ R Mᵣ m) : ContDiff ℝ s (Apr a) := by
    rw [(hmaps a).1]
    exact (contDiff_jointCutoff hψ hO ((contDiffOn_retainedDerivativeAmplitude
      T Q F row col Φ Y a hΩ hspace hphase hF hi hrank (hαspan a) hnonzero hτ.ne').mono hOΩ)
        hψO).of_le (by simp)
  have hlreg (a : initialScalarSpan (n := n) z₀ R Mᵣ m) : ContDiff ℝ s (A₀ a) := by
    rw [(hmaps a).2.1]
    exact (contDiff_jointCutoff hψ hO ((contDiffOn_retainedLeadingPrincipalMatrix
      T Q F row col Φ Y a hΩ hspace hphase hF hi hrank (hαspan a)).mono hOΩ)
        hψO).of_le (by simp)
  have hyreg (a : initialScalarSpan (n := n) z₀ R Mᵣ m) : ContDiff ℝ s (Yresp a) := by
    rw [(hmaps a).2.2]
    exact (contDiff_jointCutoff hψ hO (contDiffOn_fullPrimaryResponseDerivativeAmplitude
      T Q F row col Φ Y a hO (fun w hw ↦ hphase w (hOΩ hw)) χ B τ (hresponse a))
        hψO).of_le (by simp)
  have he (a : initialScalarSpan (n := n) z₀ R Mᵣ m) (x) (hx : x ∈ K) :
      (Apr a =ᶠ[𝓝 x] fullDerivativeAmplitude T Q F row col Φ Y a τ) ∧
      (A₀ a =ᶠ[𝓝 x] fullLeadingPrincipalMatrix T Q F row col Φ Y a) ∧
      (Yresp a =ᶠ[𝓝 x] fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B a τ) := by
    rw [(hmaps a).1, (hmaps a).2.1, (hmaps a).2.2]
    exact ⟨jointCutoff_eventuallyEq ψ _ (hplateau hx),
      jointCutoff_eventuallyEq ψ _ (hplateau hx), jointCutoff_eventuallyEq ψ _ (hplateau hx)⟩
  have hlb (a : initialScalarSpan (n := n) z₀ R Mᵣ m) :
      cNorm K s (A₀ a) ≤ C₀ * cNorm Kr d (a : Euclidean (n - 1) × Euclidean 3 → ℝ) := by
    rw [GeometricProfile.cNorm_eq_of_eventuallyEq (fun x hx ↦ (he a x hx).2.1) s]
    exact hleading a
  have hpb (a : initialScalarSpan (n := n) z₀ R Mᵣ m) :
      cNorm K s ((Apr - A₀) a) ≤ Kpr * (τ⁻¹)⁻¹ * cNorm Kr d (a : Euclidean (n - 1) × Euclidean 3 → ℝ) := by
    rw [LinearMap.sub_apply, GeometricProfile.cNorm_eq_of_eventuallyEq
      (fun x hx ↦ (he a x hx).1.sub (he a x hx).2.1) s, inv_inv]
    exact hprimary a
  have hyb (a : initialScalarSpan (n := n) z₀ R Mᵣ m) :
      cNorm K s (Yresp a) ≤ Kresp * (τ⁻¹)⁻¹ * cNorm Kr d (a : Euclidean (n - 1) × Euclidean 3 → ℝ) := by
    rw [GeometricProfile.cNorm_eq_of_eventuallyEq (fun x hx ↦ (he a x hx).2.2) s, inv_inv]
    exact hresponseBound a
  have hdensity (a : initialScalarSpan (n := n) z₀ R Mᵣ m) (x) (hx : x ∈ K) :
      atomicDensityError (Apr - Yresp) A₀ a =ᶠ[𝓝 x]
        fullCorrectedDensityError T Q F row col Φ Y χ B a τ := by
    filter_upwards [(he a x hx).1, (he a x hx).2.1, (he a x hx).2.2] with w hp hl hy
    simp only [atomicDensityError, LinearMap.sub_apply, Pi.sub_apply, hp, hl, hy,
      fullCorrectedDensityError, fullCorrectedDerivativeAmplitude]
  have hb := cNorm_atomicDensityError_sub_le_of_response Apr A₀ Yresp hK hpreg hlreg hyreg
    (fun a : initialScalarSpan (n := n) z₀ R Mᵣ m ↦ cNorm Kr d (a : Euclidean (n - 1) × Euclidean 3 → ℝ))
    (fun _ ↦ cNorm_nonneg _ _ _) hC₀ hKpr hKresp ((one_le_inv₀ hτ).mpr hτ₁)
    hlb hpb hyb r r'
  rw [GeometricProfile.cNorm_eq_of_eventuallyEq
    (fun x hx ↦ (hdensity r x hx).sub (hdensity r' x hx)) s] at hb
  simpa only [inv_inv, Submodule.coe_sub] using hb

end JanetCartan.CorrectedAtoms
