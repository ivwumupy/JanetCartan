module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.SmoothIdentification
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.CorrectedRawContinuity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.CanonicalPrefixMeasure

/-!
# Actual whole-source raw maps in the canonical construction

Instantiate the raw continuity witness with the existing whole-source
corrected derivative. The source-integral identity identifies this very map
with the corrected kernel, whose compactness supplies boundedness. The same
response, unit zero atom, detector, original wide prefixes and fixed inverse
then determine the canonical derivative and initial Fourier data
(`main:eq:old-canonical`, `main:eq:canonical-identity`).

Only qualitative full-band boundedness is claimed here. Uniform sharp raw
profiles and the common-event comparison remain necessary for the finite-run
estimates. No final canonical or current-mean estimate is a premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CurrentMean
open CanonicalAtomRealization CanonicalChange CanonicalDataBounds RawPrimary RawInputPartition
open CorrectedAtoms ResponseSourceExtension PrimarySourceAdmission
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ResponseSmoothParameters RetardedSobolev.Spaces AmplitudeBound

variable {n N J : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (χ : Euclidean n → ℝ)

variable {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (τ : ℝ) (z : Euclidean 3)
    {X : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    (hshift : ∀ p ∈ X ×ˢ V, (p.1, (z, T.reference.spatialPatch z + τ • p.2)) ∈ Ω)
    (hX : IsOpen X) (hV : IsOpen V)
    (hceil : Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ ξ, ‖d ξ‖ ≤ M)
    (hsrc : tsupport χ ⊆ X)

variable (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {core chart : Set (Euclidean n)} (Ξ : OutputCutoff core chart)
    (η : Euclidean n → ℝ)
    (Tresp : (Euclidean n → Fin n → ℝ) →ₗ[ℝ] (Euclidean n → Fin n → ℝ))
    (Sresp : (Euclidean n → Fin n → ℝ) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hS : ∀ h : compactSmoothSources (tsupport χ), ∀ x ∈ chart,
      DifferentiableAt ℝ (Sresp (AmbientResponse.correctedStressSource Q.1 η Tresp h)) x)
    (hchart : IsOpen chart) (hchartU : chart ⊆ U)
    (hSsmooth : ∀ h : compactSmoothSources (tsupport χ),
      ContDiffOn ℝ ∞ (Sresp (AmbientResponse.correctedStressSource Q.1 η Tresp h)) chart)

variable (ψ : Euclidean n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψX : tsupport ψ ⊆ X)
    {b : ℝ} (hcell : b < 1 / 2) (hbox : ∀ x ∈ tsupport ψ, ∀ i, |x i| ≤ b)

variable {d₀ : ℕ} (e : (ℝ × (Fin d₀ → ℝ)) ≃L[ℝ] Euclidean n)
    (hB : ∀ i j : Fin n, ∀ q : ℕ, ∃ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : supportedTests (e ⁻¹' tsupport χ), ∀ x ∈ X,
        ‖iteratedFDeriv ℝ q (tensorComponentResponse e (tsupport χ) (ambientExtension F (Subtype.val Q) η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ hS) i j u) x‖ ≤
          C * ‖ofTest s volume u.val‖)
    (hresponse : ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ (ambientExtension F (Subtype.val Q) η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ hS) τ r w.2 w.1) Ω)
    (hτ : τ ≠ 0)

include hB hresponse hτ

/-- The literal whole-source raw map supplies its own L² continuity witness,
by applying the checked response-integral identification and compact-kernel
bound (`app:ch_mean_pairs:defn:mean-canonical`). The same constant works for
all original prefixes. No bound for the whole-source map is assumed. -/
theorem exists_smoothWholeSourceCanonicalDerivative_l2_bound :
    let G := smoothWholeSourceCanonicalDerivative T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank
      hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
      hchart hchartU hSsmooth ψ hψ hψX hcell hbox
    ∃ CG : ℝ, 0 ≤ CG ∧
      (∀ v, periodicL2Norm (fun x ↦ (G v).val x ()) ≤ CG * ‖v‖) ∧
      ∀ (L : ℕ) (v : RefinedInput n J),
        periodicL2Norm (fun x ↦ (canonicalWidePrefixRawMap G L v).val x ()) ≤ CG * ‖v‖ := by
  dsimp only
  rw [smoothWholeSourceCanonicalDerivative_eq_smoothCorrectedWideDerivative T Q F row col Φ Y r χ
    hΩ hspace hphase hF hi hrank hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc
    hχ hc Ξ η Tresp Sresp hS hchart hchartU hSsmooth ψ hψ hψX hcell hbox e hB hresponse hτ]
  exact exists_smoothCorrectedWideDerivative_l2_bound T Q F row col Φ Y χ
    (ambientExtension F (Subtype.val Q) η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ hS)
    τ r z (T.reference.spatialPatch z)
    hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hX hV hceil
    hd hM hb ψ hψ hψX hcell hbox

/-- The original whole-source derivative and unit zero atom construct the
bounded canonical row and all its prefixes (`main:eq:old-canonical`). The
initial field, Fourier density and physical derivative use the SAME wide
adjoint datum. The continuity witnesses are constructed before the inverse
and varying target; no raw-map bound or realization equality is assumed. -/
theorem exists_wholeSourceCanonical_prefix_realization
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C) :
    let G := smoothWholeSourceCanonicalDerivative T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank
      hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
      hchart hchartU hSsmooth ψ hψ hψX hcell hbox
    let hcarrier : ∀ y ∈ X, (y, (z, T.reference.spatialPatch z)) ∈ Ω := by
      intro y hy
      have hzero : (0 : Euclidean (n - 1)) ∈ V :=
        hceil (Metric.mem_closedBall_self (by positivity))
      simpa using hshift (y, 0) ⟨hy, hzero⟩
    let base := smoothCorrectedZeroAtom T Q F row col Φ Y χ
      (ambientExtension F (Subtype.val Q) η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ hS)
      τ r z (T.reference.spatialPatch z)
      hΩ hspace hphase hF hi hrank hα hnonzero hresponse hcarrier hτ hX ψ hψ hψX hcell hbox
    ∃ CG : ℝ, ∃ hG : ∀ (_ : Unit) v, periodicL2Norm (fun x ↦ (G v).val x ()) ≤ CG * ‖v‖,
      0 ≤ CG ∧ ∀ (K : ℝ) (Q₀ : ContinuumRow.OutputL2 n →L[ℝ] ContinuumRow.OutputL2 n)
        (target : ContinuumRow.OutputL2 n),
      let Gcut := fun _ : Unit ↦ canonicalWidePrefixRawMap G (cutoffCount K)
      let hGcut : ∀ i v, periodicL2Norm (fun x ↦ (Gcut i v).val x ()) ≤ max CG 0 * ‖v‖ :=
        fun _ v ↦ periodicL2Norm_canonicalWidePrefixRawMap_le G CG (hG ()) (cutoffCount K) v
      let Awide := smoothRawCrossOperator base C hC (fun _ : Unit ↦ G) (fun _ ↦ CG) hG ()
      let Acut := smoothRawCrossOperator base C hC Gcut (fun _ ↦ max CG 0) hGcut
      let v := widePrefix n J (cutoffCount K) (Awide.adjoint (Q₀ target))
      CanonicalDataBounds.initialDatum (fun j : RefinedIndex J ↦ weightedRadialBand d j.1.val)
        (Acut ()) Q₀ target = weightedWideField d v ∧
      CanonicalDataBounds.fourierDensity (fun j : RefinedIndex J ↦ weightedRadialBand d j.1.val)
        (Acut ()) Q₀ target =ᵐ[volume] weightedWideDensity d v ∧
      ∀ x : Torus n, ψ (centeredTorusRepresentative x) = 1 →
        (smoothCanonicalDerivative Acut Gcut Q₀ target).val x () =
          wholeSourceCorrectedDerivative T Q F row col Φ Y r χ
            (ambientExtension F (Subtype.val Q) η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ hS)
            τ z d v (centeredTorusRepresentative x) := by
  let G := smoothWholeSourceCanonicalDerivative T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank
    hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
    hchart hchartU hSsmooth ψ hψ hψX hcell hbox
  obtain ⟨CG, hCG, hbound, _⟩ := exists_smoothWholeSourceCanonicalDerivative_l2_bound
    T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc
    hχ hc Ξ η Tresp Sresp hS hchart hchartU hSsmooth ψ hψ hψX hcell hbox e hB hresponse hτ
  let hG : ∀ (_ : Unit) v, periodicL2Norm (fun x ↦ (G v).val x ()) ≤ CG * ‖v‖ := fun _ ↦ hbound
  refine ⟨CG, hG, hCG, ?_⟩
  intro K Q₀ target
  refine ⟨?_, ?_, ?_⟩
  · exact (canonicalWidePrefix_fourierData_eq _ C hC (fun _ : Unit ↦ G) (fun _ ↦ CG) hG
      hd hM hb K (fun _ ↦ max CG 0) _ Q₀ target ()).1
  · exact (canonicalWidePrefix_fourierData_eq _ C hC (fun _ : Unit ↦ G) (fun _ ↦ CG) hG
      hd hM hb K (fun _ ↦ max CG 0) _ Q₀ target ()).2
  · intro x hx
    rw [smoothCanonicalDerivative_widePrefix_eq _ C hC (fun _ : Unit ↦ G) (fun _ ↦ CG) hG
      K (fun _ ↦ max CG 0) _ Q₀ target x ()]
    rw [smoothWholeSourceCanonicalDerivative_apply, hx, one_smul]

end JanetCartan.CurrentMean
