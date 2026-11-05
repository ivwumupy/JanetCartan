module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalTailRealization.NativeEvent

/-!
# The sampled whole-source family on the original raw input

Assemble the existing whole-source smooth derivative and uncut zero atom at
the literal fixed sample nodes. Apply the proved whole-source component
identity at every grouped prefix. The source, response, shifts, weights and
full refined input are fixed before the prefix changes. This is the concrete
component identification required by the balanced native event and the
same-run raw-tail recurrence (`main:eq:old-canonical`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option autoImplicit false
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CanonicalTailRealization
open RawPrimary RawInputPartition CorrectedAtoms ResponseSourceExtension PrimarySourceAdmission
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ResponseSmoothParameters RetardedSobolev.Spaces CurrentMean AmplitudeBound
open CanonicalAtomRealization CanonicalRowComparison CanonicalChange Sampling Sampling.RawKernel
open SamplingKernelBounds SeparatedSampling Sampling.Realization

variable {Λ : Type*} [Fintype Λ] {n N J p : ℕ}
    (B : ℝ) (weights : Λ → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (shifts : Λ → Lattice → Point)


variable {P : Λ → Patch n} {U : Λ → Set (Euclidean n)} {hU : ∀ a, IsOpen (U a)}
    (T : ∀ a, PatchQuantitativeFamily (P a) (U a) (hU a))
    (Q : ∀ a, {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q (U a) ∧
      cNorm (Metric.closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < (T a).family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Λ → Fin n)
    (Φ Y : Λ → ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Λ → Euclidean (n - 1) × Euclidean 3 → ℝ)
    (χ : Euclidean n → ℝ)
    (τext : Λ → ((Fin 3 → Fin (p + 1)) × Point) → ℝ)
    (hτext₀ : ∀ a q, τext a q ≠ 0)


variable {Ω : Λ → Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : ∀ a, IsOpen (Ω a)) (hspace : ∀ a, ∀ v ∈ Ω a, v.1 ∈ U a)
    (hphase : ∀ a, ∀ v ∈ Ω a, (v.1, v.2.2) ∈ phaseDomain (T a))
    (hF : ∀ a, ContDiffOn ℝ ∞ F (U a)) (hi : ∀ a, IsImmersionOn F (U a))
    (hrank : ∀ a, HasFullNormalRankOn F (U a))
    (hα : ∀ a, ContDiffOn ℝ ∞ (scalarAmplitude (T a) (Q a) F (row a) (col a) (Φ a) (Y a) (r a)) (Ω a))
    (hnonzero : ∀ a, ∀ v ∈ Ω a,
      nullvector (T a) (Q a) (col a) v ≠ 0 ∧ conullvector (T a) (Q a) (row a) v ≠ 0)
    {X : Λ → Set (Euclidean n)} {V : Λ → Set (Euclidean (n - 1))}
    (hshift : ∀ i : (SampleIndex p B weights w h shifts), ∀ q ∈ X i.1 ×ˢ V i.1,
      (q.1, (WithLp.toLp 2 (node h (shifts i.1) i.2), (T i.1).reference.spatialPatch (WithLp.toLp 2 (node h
        (shifts i.1) i.2)) + τext i.1 (color p i.2.val.1, node h (shifts i.1) i.2) • q.2)) ∈ Ω i.1)
    (hX : ∀ a, IsOpen (X a)) (hV : ∀ a, IsOpen (V a))
    (hceil : ∀ a, Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V a)
    (d : Λ → Euclidean (n - 1) → ℂ) (M : Λ → ℝ)
    (hd : ∀ a, Continuous (d a)) (hM : ∀ a, 0 ≤ M a) (hb : ∀ a ξ, ‖d a ξ‖ ≤ M a)
    (hsrc : ∀ a, tsupport χ ⊆ X a)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {core chart : Set (Euclidean n)} (Ξ : OutputCutoff core chart)
    (η : Euclidean n → ℝ)
    (Tresp : (Euclidean n → Fin n → ℝ) →ₗ[ℝ] (Euclidean n → Fin n → ℝ))
    (Sresp : (Euclidean n → Fin n → ℝ) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hS : ∀ a, ∀ f : compactSmoothSources (tsupport χ), ∀ x ∈ chart,
      DifferentiableAt ℝ (Sresp (AmbientResponse.correctedStressSource (Q a).1 η Tresp f)) x)
    (hchart : IsOpen chart) (hchartU : ∀ a, chart ⊆ U a)
    (hSsmooth : ∀ a, ∀ f : compactSmoothSources (tsupport χ),
      ContDiffOn ℝ ∞ (Sresp (AmbientResponse.correctedStressSource (Q a).1 η Tresp f)) chart)
    (ψ : Euclidean n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψX : ∀ a, tsupport ψ ⊆ X a)
    {b : ℝ} (hcell : b < 1 / 2) (hbox : ∀ x ∈ tsupport ψ, ∀ i, |x i| ≤ b)


variable (hresponse : ∀ i : (SampleIndex p B weights w h shifts), ContDiffOn ℝ ∞
      (fun v ↦ fullPrimaryResponse (T i.1) (Q i.1) F (row i.1) (col i.1) (Φ i.1) (Y i.1) χ
        (ambientExtension F (Q i.1).1 η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ (hS i.1)) (τext i.1
          (color p i.2.val.1, node h (shifts i.1) i.2)) (r i.1) v.2 v.1) (Ω i.1))

/-- The original uncut zero atoms at the fixed sample nodes, assembled on the
literal sample index (`app:ch_mean_pairs:defn:mean-canonical`). -/
def wholeSourceSampledBase : SmoothPeriodicFamily n (SampleIndex p B weights w h shifts) (Matrix (Fin N) (Fin n)
  ℂ) := by
  let b₀ (i : (SampleIndex p B weights w h shifts)) : SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ) :=
    smoothCorrectedZeroAtom (O := X i.1) (Ω := Ω i.1) (T i.1) (Q i.1) F (row i.1) (col i.1)
    (Φ i.1) (Y i.1) χ (ambientExtension F (Q i.1).1 η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ (hS i.1))
      (τext i.1 (color p i.2.val.1, node h (shifts i.1) i.2)) (r i.1) (WithLp.toLp 2 (node h (shifts i.1) i.2))
    ((T i.1).reference.spatialPatch (WithLp.toLp 2 (node h (shifts i.1) i.2)))
    (hΩ i.1) (hspace i.1) (hphase i.1) (hF i.1) (hi i.1) (hrank i.1) (hα i.1)
    (hnonzero i.1) (hresponse i) (fun (x : Euclidean n) (hx : x ∈ X i.1) ↦ by
      have hz : (0 : Euclidean (n - 1)) ∈ V i.1 :=
        hceil i.1 (Metric.mem_closedBall_self (by positivity))
      simpa using hshift i (x, 0) ⟨hx, hz⟩)
    (hτext₀ i.1 ((color p i.2.val.1, node h (shifts i.1) i.2))) (hX i.1) ψ hψ (hψX i.1) hcell hbox
  exact ⟨fun x i ↦ (b₀ i).val x (), fun i ↦ (b₀ i).property ()⟩

/-- The same whole-source response at every grouped band prefix. Both refined
pieces are retained in one fixed input space (`main:eq:old-canonical`). -/
def wholeSourceSampledDerivative (L : ℕ) (i : (SampleIndex p B weights w h shifts)) :
    RefinedInput n J →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ) :=
  (smoothWholeSourceCanonicalDerivative (n := n) (N := N) (J := J)
    (X := X i.1) (V := V i.1) (Ω := Ω i.1) (T i.1) (Q i.1) F (row i.1) (col i.1)
    (Φ i.1) (Y i.1) (r i.1) χ (hΩ i.1) (hspace i.1) (hphase i.1)
    (hF i.1) (hi i.1) (hrank i.1) (hα i.1) (hnonzero i.1) (τext i.1 (color p i.2.val.1, node h (shifts i.1) i.2))
      (WithLp.toLp 2 (node h (shifts i.1) i.2))
    (hshift i) (hX i.1) (hV i.1) (hceil i.1) (hd i.1).measurable (hM i.1) (hb i.1)
    (hsrc i.1) hχ hc Ξ η Tresp Sresp (hS i.1) hchart (hchartU i.1) (hSsmooth i.1)
    ψ hψ (hψX i.1) hcell hbox).comp
      ((((widePrefix n J L).restrictScalars ℝ).toLinearMap).comp
        ((wideRefinement n J).symm.toLinearMap.restrictScalars ℝ))


variable {d₀ : ℕ} (e : (ℝ × (Fin d₀ → ℝ)) ≃L[ℝ] Euclidean n)
    (hB : ∀ a, ∀ i j : Fin n, ∀ q : ℕ, ∃ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : supportedTests (e ⁻¹' tsupport χ), ∀ x ∈ X a,
        ‖iteratedFDeriv ℝ q (tensorComponentResponse e (tsupport χ) (ambientExtension F (Q a).1 η Tresp Sresp
          (compactSmoothSources (tsupport χ)) Ξ (hS a)) i j u) x‖ ≤
          C * ‖ofTest s volume u.val‖)
    (Sext : Λ → ((Fin 3 → Fin (p + 1)) × Point) → Euclidean n → Euclidean (n - 1) → ℝ)
    (Vext : Λ → ((Fin 3 → Fin (p + 1)) × Point) → Euclidean n → Euclidean (n - 1) → Matrix (Fin N) (Fin n) ℂ)
    (ζext : Λ → ((Fin 3 → Fin (p + 1)) × Point) → Euclidean (n - 1))
    (hζext : ∀ a, Continuous (ζext a)) (hτext : ∀ a, Continuous (τext a))
    (hζsample : ∀ i : (SampleIndex p B weights w h shifts), ζext i.1 ((color p i.2.val.1, node h (shifts i.1)
      i.2)) = (T i.1).reference.spatialPatch (WithLp.toLp 2 (node h (shifts i.1) i.2)))
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (Cper : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (hCper : IsSmoothPeriodic Cper)
    (hmeasurement : ∀ x, Cper x = C (centeredTorusRepresentative x))
    (hplateau : ∀ x, Cper x ≠ 0 → ψ (centeredTorusRepresentative x) = 1)
    (hSext : ∀ a, Continuous (fun q : (((Fin 3 → Fin (p + 1)) × Point) × Euclidean n) × Euclidean (n - 1) ↦
      Sext a q.1.1 q.1.2 q.2))
    (hVext : ∀ a q x, Continuous (Vext a q x))
    (hphaseExt : ∀ i : (SampleIndex p B weights w h shifts), ∀ x, Cper x ≠ 0 → ∀ ξ ∈ V i.1,
      Sext i.1 ((color p i.2.val.1, node h (shifts i.1) i.2)) (centeredTorusRepresentative x)
        ((T i.1).reference.spatialPatch (WithLp.toLp 2 (node h (shifts i.1) i.2)) + τext i.1 (color p i.2.val.1,
          node h (shifts i.1) i.2) • ξ) =
        phase (T i.1) (Q i.1) (centeredTorusRepresentative x)
          ((T i.1).reference.spatialPatch (WithLp.toLp 2 (node h (shifts i.1) i.2)) + τext i.1 (color p i.2.val.1,
            node h (shifts i.1) i.2) • ξ))
    (hampExt : ∀ i : (SampleIndex p B weights w h shifts), ∀ x, Cper x ≠ 0 → ∀ ξ ∈ V i.1,
      Vext i.1 ((color p i.2.val.1, node h (shifts i.1) i.2)) (centeredTorusRepresentative x)
        ((T i.1).reference.spatialPatch (WithLp.toLp 2 (node h (shifts i.1) i.2)) + τext i.1 (color p i.2.val.1,
          node h (shifts i.1) i.2) • ξ) =
        fullCorrectedDerivativeAmplitude (T i.1) (Q i.1) F (row i.1) (col i.1) (Φ i.1) (Y i.1)
          χ (ambientExtension F (Q i.1).1 η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ (hS i.1)) (r i.1)
            (τext i.1 (color p i.2.val.1, node h (shifts i.1) i.2))
          (centeredTorusRepresentative x, (WithLp.toLp 2 (node h (shifts i.1) i.2),
            (T i.1).reference.spatialPatch (WithLp.toLp 2 (node h (shifts i.1) i.2)) + τext i.1 (color p
              i.2.val.1, node h (shifts i.1) i.2) • ξ)))
    (hcross : ∀ a, Continuous (fun q : (((Fin 3 → Fin (p + 1)) × Point) × Euclidean n) × Euclidean (n - 1) ↦
      complexCrossMeasurement (C q.1.2) (Vext a q.1.1 q.1.2 (ζext a q.1.1))
        (Vext a q.1.1 q.1.2 q.2)))
    (support : Set (Euclidean n)) (hsupport : IsCompact support)
    (hcrossSupport : ∀ a q x ξ, x ∉ support →
      complexCrossMeasurement (C x) (Vext a q x (ζext a q)) (Vext a q x ξ) = 0)
    (Bcross : ℝ) (hBcross : 0 ≤ Bcross)
    (hcrossBound : ∀ a q x ξ,
      ‖complexCrossMeasurement (C x) (Vext a q x (ζext a q)) (Vext a q x ξ)‖ ≤ Bcross)

include hB hζsample hmeasurement hplateau hVext hphaseExt hampExt

omit [Fintype Λ] in
/-- Each literal sampled whole-source smooth component is the original
raw-integral component. This applies the response producer on the SAME node
and every grouped prefix; no component identity is an input
(`main:eq:old-canonical`, `app:ch_mean_pairs:defn:mean-canonical`). -/
theorem wholeSourceSampled_rawCrossOperator_eq (L : ℕ) :
    let base := wholeSourceSampledBase B weights w h shifts T Q F row col Φ Y r χ τext hτext₀ hΩ hspace hphase hF
      hi hrank hα hnonzero hshift hX hceil Ξ η Tresp Sresp hS ψ hψ hψX hcell hbox hresponse
    let G := wholeSourceSampledDerivative B weights w h shifts T Q F row col Φ Y r χ τext hΩ hspace hphase hF hi
      hrank hα hnonzero hshift hX hV hceil d M hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS hchart hchartU hSsmooth ψ hψ
      hψX hcell hbox L
    let D := (fun a : Λ ↦ bandKernelData (J := J) (Sext a)
      (fun q x ξ ↦ complexCrossMeasurement (C x) (Vext a q x (ζext a q)) (Vext a q x ξ))
      (ζext a) (τext a) (d a) (hSext a) (hcross a) (hζext a) (hτext a) (hτext₀ a)
      (hd a) support hsupport (hcrossSupport a) Bcross (M a) hBcross (hM a) (hcrossBound a) (hb a))
    ∀ (CG : (SampleIndex p B weights w h shifts) → ℝ)
      (hG : ∀ i v, periodicL2Norm (fun x ↦ (G i v).val x ()) ≤ CG i * ‖v‖),
    smoothRawCrossOperator base Cper hCper G CG hG =
      rawIntegralSampledComponent B weights w h shifts
        (fun a color z ↦ refinedKernelPrefix (D a) L (color, z)) := by
  dsimp only
  intro CG hG
  funext i
  have hop := smoothRawCrossOperator_wholeSource_eq_rawIntegral_component
    (T i.1) (Q i.1) F (row i.1) (col i.1) (Φ i.1) (Y i.1) (r i.1) χ
    (hΩ i.1) (hspace i.1) (hphase i.1) (hF i.1) (hi i.1) (hrank i.1)
    (hα i.1) (hnonzero i.1) (τext i.1 (color p i.2.val.1, node h (shifts i.1) i.2)) (WithLp.toLp 2 (node h (shifts
      i.1) i.2))
    (hshift i) (hX i.1) (hV i.1) (hceil i.1) (hd i.1) (hM i.1) (hb i.1) (hsrc i.1)
    hχ hc Ξ η Tresp Sresp (hS i.1) hchart (hchartU i.1) (hSsmooth i.1)
    ψ hψ (hψX i.1) hcell hbox e (hB i.1) (hresponse i) (hτext₀ i.1 ((color p i.2.val.1, node h (shifts i.1) i.2)))
    ((color p i.2.val.1, node h (shifts i.1) i.2)) (Sext i.1) (Vext i.1) (ζext i.1) (τext i.1)
    (hζext i.1) (hτext i.1) (hτext₀ i.1) (hζsample i) rfl
    C Cper hCper hmeasurement hplateau (hSext i.1) (hVext i.1)
    (hphaseExt i) (hampExt i) (hcross i.1) support hsupport (hcrossSupport i.1)
    Bcross hBcross (hcrossBound i.1) L (fun _ : Unit ↦ CG i) (fun _ v ↦ hG i v)
  exact hop

/-- The literal complete smooth residual is the residual of the SAME
raw-integral sampled run. This applies the whole-source component equality
before telescoping, with one inverse and no resampling across cutoffs
(`main:eq:full-recursion`, `main:lem:mean-recurrence`). -/
theorem wholeSourceSampled_completeResidual_toL2_eq_run
    {W : ℝ} {Pweight : Λ → ℝ} (hw : WindowBounds p w W)
    (hweights : ∀ a, PatchBounds (weights a) B (Pweight a)) (hh : 0 ≤ h)
    (coeff : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hcoeff : ∀ a, IsSmoothPeriodic (coeff a : Torus n → ℝ))
    (χmeas χsrc ψext : C(Torus n, ℝ))
    (hm : IsSmoothPeriodic (χmeas : Torus n → ℝ))
    (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (hψext : IsSmoothPeriodic (ψext : Torus n → ℝ))
    (K : ℕ → ℝ) (hK : ∀ l, 1 ≤ K l) (carrierPlateau : ℝ)
    (Q₀ : ContinuumRow.OutputL2 n →L[ℝ] ContinuumRow.OutputL2 n) :
    let base := wholeSourceSampledBase B weights w h shifts T Q F row col Φ Y r χ τext hτext₀ hΩ hspace hphase hF
      hi hrank hα hnonzero hshift hX hceil Ξ η Tresp Sresp hS ψ hψ hψX hcell hbox hresponse
    let G := fun l ↦ wholeSourceSampledDerivative B weights w h shifts T Q F row col Φ Y r χ τext hΩ hspace hphase
      hF hi hrank hα hnonzero hshift hX hV hceil d M hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS hchart hchartU
      hSsmooth ψ hψ hψX hcell hbox (cutoffCount (carrierPlateau * K l))
    let Dkernel := (fun a : Λ ↦ bandKernelData (J := J) (Sext a)
      (fun q x ξ ↦ complexCrossMeasurement (C x) (Vext a q x (ζext a q)) (Vext a q x ξ))
      (ζext a) (τext a) (d a) (hSext a) (hcross a) (hζext a) (hτext a) (hτext₀ a)
      (hd a) support hsupport (hcrossSupport a) Bcross (M a) hBcross (hM a) (hcrossBound a) (hb a))
    let A := fun l ↦ rawIntegralSampledComponent B weights w h shifts
      (fun a color z ↦ refinedKernelPrefix (Dkernel a) (cutoffCount (carrierPlateau * K l)) (color, z))
    let μ := sampleWeight (p := p) B weights w h shifts
    ∀ (CG : ℕ → SampleIndex p B weights w h shifts → ℝ)
      (_hG : ∀ l i v, periodicL2Norm (fun x ↦ (G l i v).val x ()) ≤ CG l i * ‖v‖)
      (source : SmoothResidual n) (steps : ℕ),
    smoothResidualToL2 n
      (completeResidualRepresentative coeff hcoeff χmeas χsrc ψext hm hs hψext μ A
        (fun l ↦ smoothRawCrossResponse base Cper hCper (G l)) Q₀ K hK
        (fun l ↦ smoothCanonicalDerivative (A l) (G l) Q₀) Cper hCper source steps) =
      (MeanRecurrence.run Q₀.toLinearMap
        (fun l ↦ (completeCanonicalNormal coeff χmeas χsrc ψext μ (A l) (hK l)).toLinearMap)
        (fun l ↦ smoothCanonicalDerivative (A l) (G l) Q₀)
        (SmoothPeriodicFamily.measuredHermitianBilinear μ Cper hCper)
        (smoothResidualToL2 n source) steps).2 := by
  dsimp only
  intro CG hG source steps
  apply completeResidualRepresentative_toL2 coeff hcoeff χmeas χsrc ψext hm hs hψext
    (sampleWeight B weights w h shifts) (sampleWeight_nonneg shifts hw hweights hh)
  intro l i v
  have hop := wholeSourceSampled_rawCrossOperator_eq B weights w h shifts T Q F row col Φ Y r χ τext hτext₀
    hΩ hspace hphase hF hi hrank hα hnonzero hshift hX hV hceil d M hd hM hb hsrc hχ hc
    Ξ η Tresp Sresp hS hchart hchartU hSsmooth ψ hψ hψX hcell hbox hresponse e hB
    Sext Vext ζext hζext hτext hζsample C Cper hCper hmeasurement hplateau hSext hVext
    hphaseExt hampExt hcross support hsupport hcrossSupport Bcross hBcross hcrossBound
    (cutoffCount (carrierPlateau * K l)) (CG l) (hG l)
  exact congrArg (fun A ↦ A i v) hop

end JanetCartan.CanonicalTailRealization
