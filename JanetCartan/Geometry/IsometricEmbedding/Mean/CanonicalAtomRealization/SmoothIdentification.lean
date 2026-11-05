module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.Identification
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.Background

/-!
# One canonical smooth map for both physical formulas

For `app:ch_mean_pairs:defn:mean-canonical`, identify the existing whole-source
and corrected-atom smooth linear maps. The original slice cutoff, fixed ambient
response and raw Hilbert spaces are unchanged. The proved source-norm integral
interchange gives the literal derivative representation used by both canonical
consumers. The concrete unmasked zero atom supplies the same background.

The finite source-norm estimate is the fixed-inverse producer's existing tame
interface, specialized to order zero in the identification. Its constants are
chosen before the raw datum and varying target. No map or representation is
assumed, and no independent response or smooth field is chosen.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CanonicalAtomRealization
open RawPrimary RawInputPartition CorrectedAtoms ResponseSourceExtension PrimarySourceAdmission
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ResponseSmoothParameters RetardedSobolev.Spaces CurrentMean AmplitudeBound

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

include hB in
/-- Order zero of the SAME fixed response's tame estimate, with its constants
still before the source datum (`app:ch_response:prop:response-graded`). -/
private theorem canonicalResponse_zeroOrder_bound :
    ∀ i j : Fin n, ∃ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : supportedTests (e ⁻¹' tsupport χ), ∀ x ∈ X,
        ‖tensorComponentResponse e (tsupport χ) (ambientExtension F (Subtype.val Q) η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ hS) i j u x‖ ≤
          C * ‖ofTest s volume u.val‖ := by
  intro i j
  obtain ⟨s, C, hC, hb⟩ := hB i j 0
  exact ⟨s, C, hC, fun u x hx ↦ by simpa only [norm_iteratedFDeriv_zero] using hb u x hx⟩

include hB

/-- The actual whole-source construction and the corrected-atom construction
are literally the SAME real-linear smooth map, including the supplied slice
cutoff and the original raw Hilbert space. No representatives are selected
independently (`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem smoothWholeSourceCanonicalDerivative_eq_smoothCorrectedWideDerivative :
    smoothWholeSourceCanonicalDerivative T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank
      hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
      hchart hchartU hSsmooth ψ hψ hψX hcell hbox =
    smoothCorrectedWideDerivative T Q F row col Φ Y χ (ambientExtension F (Subtype.val Q) η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ hS) τ r z (T.reference.spatialPatch z)
      hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hX hV hceil
      hd hM hb ψ hψ hψX hcell hbox := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  funext x u
  change ψ (centeredTorusRepresentative x) •
      wholeSourceCorrectedDerivative T Q F row col Φ Y r χ (ambientExtension F (Subtype.val Q) η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ hS) τ z d v (centeredTorusRepresentative x) =
    ψ (centeredTorusRepresentative x) •
      correctedWideDerivative T Q F row col Φ Y χ (ambientExtension F (Subtype.val Q) η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ hS) τ r z (T.reference.spatialPatch z) d v
        (centeredTorusRepresentative x)
  by_cases hx : centeredTorusRepresentative x ∈ tsupport ψ
  · rw [wholeSourceCorrectedDerivative_eq_correctedWideDerivative T Q F row col Φ Y r
      hΩ hspace hphase hF hi hrank hα hnonzero τ z hshift hX hV hceil hd hM hb χ hsrc
      hχ hc e (ambientExtension F (Subtype.val Q) η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ hS) (canonicalResponse_zeroOrder_bound (hB := hB))
      hresponse v (hψX hx)]
  · simp [image_eq_zero_of_notMem_tsupport hx]

include hresponse hτ

/-- The actual whole-source smooth map has the literal corrected-atom
integral at every torus point, with precisely the supplied extension cutoff
(`app:ch_waves:eq:individual-representation`). -/
theorem smoothWholeSourceCanonicalDerivative_eq_cutIntegral (v : WideInput n J) (x : Torus n) :
    (smoothWholeSourceCanonicalDerivative T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank
      hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
      hchart hchartU hSsmooth ψ hψ hψX hcell hbox v).val x () =
      ψ (centeredTorusRepresentative x) •
        rawPrimaryDemodulatedIntegral (fun y ξ ↦ phase T Q y ξ)
          (fun y ξ ↦ fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ (ambientExtension F (Subtype.val Q) η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ hS) r τ (y, (z, ξ)))
          (T.reference.spatialPatch z) τ volume (weightedWideDensity d v)
          (centeredTorusRepresentative x) := by
  rw [smoothWholeSourceCanonicalDerivative_eq_smoothCorrectedWideDerivative T Q F row col Φ Y r χ
    hΩ hspace hphase hF hi hrank hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc
    hχ hc Ξ η Tresp Sresp hS hchart hchartU hSsmooth ψ hψ hψX hcell hbox e hB hresponse hτ]
  exact smoothCorrectedWideDerivative_eq_cutIntegral T Q F row col Φ Y χ (ambientExtension F (Subtype.val Q) η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ hS) τ r z
    (T.reference.spatialPatch z) hΩ hspace hphase hF hi hrank hα hnonzero hresponse
    hshift hτ hX hV hceil hd hM hb ψ hψ hψX hcell hbox v x

/-- The original canonical adjoint and inverse feed the SAME whole-source
map with its literal corrected-atom derivative integral. The source-norm
constants precede this varying target (`app:ch_mean_pairs:eq:mean-current-canonical`). -/
theorem smoothCanonicalDerivative_wholeSource_eq_integral
    (A : WideInput n J →L[ℝ] ContinuumRow.OutputL2 n)
    (Q₀ : ContinuumRow.OutputL2 n →L[ℝ] ContinuumRow.OutputL2 n)
    (target : ContinuumRow.OutputL2 n) (x : Torus n)
    (hx : ψ (centeredTorusRepresentative x) = 1) :
    (CanonicalChange.smoothCanonicalDerivative (fun _ : Unit ↦ A)
      (fun _ ↦ smoothWholeSourceCanonicalDerivative T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank
        hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
        hchart hchartU hSsmooth ψ hψ hψX hcell hbox) Q₀ target).val x () =
      rawPrimaryDemodulatedIntegral (fun y ξ ↦ phase T Q y ξ)
        (fun y ξ ↦ fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ (ambientExtension F (Subtype.val Q) η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ hS) r τ (y, (z, ξ)))
        (T.reference.spatialPatch z) τ volume (weightedWideDensity d (A.adjoint (Q₀ target)))
        (centeredTorusRepresentative x) := by
  change (smoothWholeSourceCanonicalDerivative T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank
      hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
      hchart hchartU hSsmooth ψ hψ hψX hcell hbox (A.adjoint (Q₀ target))).val x () = _
  rw [smoothWholeSourceCanonicalDerivative_eq_cutIntegral T Q F row col Φ Y r χ
    hΩ hspace hphase hF hi hrank hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc
    hχ hc Ξ η Tresp Sresp hS hchart hchartU hSsmooth ψ hψ hψX hcell hbox e hB hresponse hτ,
    hx, one_smul]

/-- The measured cross response retains the supplied background and the
whole-source map's actual integral. This connects to
`CanonicalChange.smoothCanonicalResponse_eq_measured_cross`
(`main:eq:canonical-identity`). -/
theorem wholeSourceSmoothCrossResponse_eq_integral
    (base : SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (v : WideInput n J) (x : Torus n) (hx : ψ (centeredTorusRepresentative x) = 1) :
    (CanonicalChange.smoothRawCrossResponse base C hC
      (fun _ : Unit ↦ smoothWholeSourceCanonicalDerivative T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank
        hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
        hchart hchartU hSsmooth ψ hψ hψX hcell hbox) () v).val x () =
      C x ((2 : ℝ) • mixedHermitianTensor (base.val x ())
        (rawPrimaryDemodulatedIntegral (fun y ξ ↦ phase T Q y ξ)
          (fun y ξ ↦ fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ (ambientExtension F (Subtype.val Q) η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ hS) r τ (y, (z, ξ)))
          (T.reference.spatialPatch z) τ volume (weightedWideDensity d v)
          (centeredTorusRepresentative x))) := by
  rw [CanonicalChange.smoothRawCrossResponse_apply,
    smoothWholeSourceCanonicalDerivative_eq_cutIntegral T Q F row col Φ Y r χ
      hΩ hspace hphase hF hi hrank hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc
      hχ hc Ξ η Tresp Sresp hS hchart hchartU hSsmooth ψ hψ hψX hcell hbox e hB hresponse hτ,
    hx, one_smul]

/-- The actual canonical cross response uses the original unit zero atom
and the SAME whole-source derivative. Carrier admission is deduced from
the original shifted frequency domain, so no extra background or independent
choice is required (`main:eq:canonical-identity`). -/
theorem wholeSourceSmoothCrossResponse_zeroAtom_eq_integral
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (v : WideInput n J) (x : Torus n) (hx : ψ (centeredTorusRepresentative x) = 1) :
    let hcarrier : ∀ y ∈ X, (y, (z, T.reference.spatialPatch z)) ∈ Ω := by
      intro y hy
      have hzero : (0 : Euclidean (n - 1)) ∈ V :=
        hceil (Metric.mem_closedBall_self (by positivity))
      simpa using hshift (y, 0) ⟨hy, hzero⟩
    (CanonicalChange.smoothRawCrossResponse
      (smoothCorrectedZeroAtom T Q F row col Φ Y χ
        (ambientExtension F (Subtype.val Q) η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ hS)
        τ r z (T.reference.spatialPatch z)
        hΩ hspace hphase hF hi hrank hα hnonzero hresponse hcarrier hτ hX ψ hψ hψX hcell hbox)
      C hC (fun _ : Unit ↦ smoothWholeSourceCanonicalDerivative T Q F row col Φ Y r χ
        hΩ hspace hphase hF hi hrank hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc
        hχ hc Ξ η Tresp Sresp hS hchart hchartU hSsmooth ψ hψ hψX hcell hbox) () v).val x () =
      C x ((2 : ℝ) • mixedHermitianTensor
        (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ
          (ambientExtension F (Subtype.val Q) η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ hS)
          r τ (centeredTorusRepresentative x, (z, T.reference.spatialPatch z)))
        (rawPrimaryDemodulatedIntegral (fun y ξ ↦ phase T Q y ξ)
          (fun y ξ ↦ fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ
            (ambientExtension F (Subtype.val Q) η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ hS)
            r τ (y, (z, ξ)))
          (T.reference.spatialPatch z) τ volume (weightedWideDensity d v)
          (centeredTorusRepresentative x))) := by
  dsimp only
  rw [wholeSourceSmoothCrossResponse_eq_integral T Q F row col Φ Y r χ
    hΩ hspace hphase hF hi hrank hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc
    hχ hc Ξ η Tresp Sresp hS hchart hchartU hSsmooth ψ hψ hψX hcell hbox e hB hresponse hτ
    _ C hC v x hx]
  change C x ((2 : ℝ) • mixedHermitianTensor (ψ _ • _) _) = _
  rw [hx, one_smul]

end JanetCartan.CanonicalAtomRealization

