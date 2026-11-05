module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.SampledWholeSource

/-!
# Physical waves for the literal sampled whole-source maps

Retain the original sample node, color-dependent frequency, scalar, response,
source cutoff and zero atom. Their physical derivatives realize the existing
`wholeSourceSampledBase` and `wholeSourceSampledDerivative` on the supplied
common source plateau (`main:eq:old-canonical`, `app:ch_pairs:lem:pairs-ledger`).
These identities supply the physical family required by the canonical sum;
no realization or final-amplitude estimate is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set MeasureTheory Finset
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CurrentMean
open RawPrimary RawInputPartition CorrectedAtoms ResponseSourceExtension PrimarySourceAdmission
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ResponseSmoothParameters RetardedSobolev.Spaces AmplitudeBound UniformStep SmoothPeriodicFamily
open CanonicalAtomRealization CanonicalRowComparison CanonicalTailRealization CanonicalChange CanonicalDataBounds
open Sampling Sampling.RawKernel SamplingKernelBounds SeparatedSampling Sampling.Realization

variable {Λ : Type*} {n N J p : ℕ}
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

/-- The original phase at the actual sample node and its own frequency
(`app:ch_pairs:lem:pairs-ledger`). -/
def wholeSourceSampledPhase (i : SampleIndex p B weights w h shifts) (x : Euclidean n) : ℝ :=
  (T i.1).carrier (Q i.1) x (WithLp.toLp 2 (node h (shifts i.1) i.2)) /
    τext i.1 (color p i.2.val.1, node h (shifts i.1) i.2)

/-- The physical corrected unit zero atom at the SAME sample
(`app:ch_mean_pairs:defn:mean-canonical`). No Fourier mask is applied. -/
def wholeSourceSampledZeroWave (i : SampleIndex p B weights w h shifts) :
    Euclidean n → EuclideanSpace ℂ (Fin N) :=
  fullCorrectedPrimaryAtom (T i.1) (Q i.1) F (row i.1) (col i.1) (Φ i.1) (Y i.1) χ
    (ambientExtension F (Q i.1).1 η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ (hS i.1))
    (τext i.1 (color p i.2.val.1, node h (shifts i.1) i.2)) (r i.1)
    (WithLp.toLp 2 (node h (shifts i.1) i.2),
      (T i.1).reference.spatialPatch (WithLp.toLp 2 (node h (shifts i.1) i.2)))

/-- The physical whole-source wave on the original wide input at one fixed
sample (`main:eq:old-canonical`). It uses exactly the response and scalar of
`wholeSourceSampledDerivative`. -/
def wholeSourceSampledWave (i : SampleIndex p B weights w h shifts) (v : WideInput n J) :
    Euclidean n → EuclideanSpace ℂ (Fin N) :=
  wholeSourceCorrectedWave (T i.1) (Q i.1) F (row i.1) (col i.1) (Φ i.1) (Y i.1) (r i.1) χ
    (ambientExtension F (Q i.1).1 η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ (hS i.1))
    (τext i.1 (color p i.2.val.1, node h (shifts i.1) i.2))
    (WithLp.toLp 2 (node h (shifts i.1) i.2)) (d i.1) v

/-- The literal sampled zero atoms realize the SAME periodic base on the
original source plateau (`app:ch_pairs:lem:pairs-ledger`). This proves both
physical smoothness and the exact demodulated derivative identity. -/
theorem wholeSourceSampledBase_realizes_sampledAmplitude
    {Vsource : Set (Euclidean n)}
    (hsourceBox : ∀ x ∈ Vsource, ∀ a, |x a| < 1 - b)
    (hplateau : ∀ x ∈ Vsource, ψ x = 1) :
    let Zc := wholeSourceSampledZeroWave B weights w h shifts T Q F row col Φ Y r χ τext Ξ η Tresp Sresp hS
    let θ := wholeSourceSampledPhase B weights w h shifts T Q τext
    let base := wholeSourceSampledBase B weights w h shifts T Q F row col Φ Y r χ τext hτext₀ hΩ hspace
      hphase hF hi hrank hα hnonzero hshift hX hceil Ξ η Tresp Sresp hS
      ψ hψ hψX hcell hbox hresponse
    ∀ i, ContDiffOn ℝ ∞ (Zc i) Vsource ∧
      EqOn (sampledDerivativeAmplitude Zc θ i)
        (periodicLift (fun x ↦ base.val x i)) Vsource := by
  dsimp only
  intro i
  have hcarrier : ∀ x ∈ X i.1,
      (x, (WithLp.toLp 2 (node h (shifts i.1) i.2),
        (T i.1).reference.spatialPatch (WithLp.toLp 2 (node h (shifts i.1) i.2)))) ∈ Ω i.1 := by
    intro x hx
    have hz : (0 : Euclidean (n - 1)) ∈ V i.1 :=
      hceil i.1 (Metric.mem_closedBall_self (by positivity))
    simpa using hshift i (x, 0) ⟨hx, hz⟩
  exact correctedZeroAtom_realizes_sampledAmplitude (T i.1) (Q i.1) F (row i.1) (col i.1) (Φ i.1) (Y i.1)
    χ (ambientExtension F (Q i.1).1 η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ (hS i.1))
    (τext i.1 (color p i.2.val.1, node h (shifts i.1) i.2)) (r i.1)
    (WithLp.toLp 2 (node h (shifts i.1) i.2))
    ((T i.1).reference.spatialPatch (WithLp.toLp 2 (node h (shifts i.1) i.2)))
    (hΩ i.1) (hspace i.1) (hphase i.1) (hF i.1) (hi i.1) (hrank i.1) (hα i.1) (hnonzero i.1)
    (hresponse i) hcarrier (hτext₀ i.1 _) (hX i.1) ψ hψ (hψX i.1) hcell hbox hsourceBox hplateau

/-- Every original sampled raw prefix has its literal physical realization
on the common source plateau (`main:eq:old-canonical`). The sample-dependent
frequency and the two refined pieces are retained without resampling. -/
theorem wholeSourceSampledDerivative_realizes_sampledAmplitude
    {Vsource : Set (Euclidean n)}
    (hsourceBox : ∀ x ∈ Vsource, ∀ a, |x a| < 1 - b)
    (hplateau : ∀ x ∈ Vsource, ψ x = 1) (L : ℕ) :
    let G := wholeSourceSampledDerivative B weights w h shifts T Q F row col Φ Y r χ τext hΩ hspace hphase hF hi
      hrank hα hnonzero hshift hX hV hceil d M hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
      hchart hchartU hSsmooth ψ hψ hψX hcell hbox L
    let θ := wholeSourceSampledPhase B weights w h shifts T Q τext
    let W := fun i (v : RefinedInput n J) ↦
      wholeSourceSampledWave B weights w h shifts T Q F row col Φ Y r χ τext d Ξ η Tresp Sresp hS i
        (widePrefix n J L ((realWideRefinement n J).symm v))
    ∀ i v, ContDiffOn ℝ ∞ (W i v) Vsource ∧
      EqOn (sampledDerivativeAmplitude (fun _ : Unit ↦ W i v) (fun _ ↦ θ i) ())
        (periodicLift (fun x ↦ (G i v).val x ())) Vsource := by
  dsimp only
  intro i v
  exact wholeSourcePrefix_realizes_sampledAmplitude (T i.1) (Q i.1) F (row i.1) (col i.1) (Φ i.1) (Y i.1)
    (r i.1) χ (hΩ i.1) (hspace i.1) (hphase i.1) (hF i.1) (hi i.1) (hrank i.1)
    (hα i.1) (hnonzero i.1) (τext i.1 (color p i.2.val.1, node h (shifts i.1) i.2))
    (WithLp.toLp 2 (node h (shifts i.1) i.2))
    (hshift i) (hX i.1) (hV i.1) (hceil i.1) (hd i.1).measurable (hM i.1) (hb i.1)
    (hsrc i.1) hχ hc Ξ η Tresp Sresp (hS i.1) hchart (hchartU i.1) (hSsmooth i.1)
    ψ hψ (hψX i.1) hcell hbox hsourceBox hplateau L v

end JanetCartan.CurrentMean
