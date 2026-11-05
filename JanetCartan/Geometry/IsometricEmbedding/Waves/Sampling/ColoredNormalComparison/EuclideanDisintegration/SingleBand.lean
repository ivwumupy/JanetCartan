module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.EuclideanDisintegration.KernelColumns
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.Masks

/-!
# A single smooth band on literal Euclidean output

The common-kernel deduction for `app:ch_waves:eq:sampling-prefix-normal` and
`app:ch_waves:eq:colored-normal-comparison`. The input identification preserves
the original restricted Lebesgue measures. The primitive equality uses the
original normalized forward kernel and the square root of the fixed patch
weight. The carrier mask is the literal mask at `z₀ + Z u`. Every normal and
Fubini identity is a conclusion; zero patch weights require no division.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace JanetCartan.Sampling.ColoredNormalComparison.EuclideanDisintegration
open NormalComparison SamplingKernelBounds AmplitudeBound
open SeparatedSampling LatticeQuadrature BackgroundQuadrature

variable {n : ℕ} {G : UniformNormalGeometry n n} {C : ℕ → ℝ}

/-- The literal continuous slice operator on the unchanged restricted
transverse input and the full Euclidean output, expressed in finite fiber
coordinates (`app:ch_waves:eq:sampling-prefix-normal`). -/
def compactSliceOperator
    (Θ : Set (Euclidean (n - 1)))
    (b : ℝ → Fin n → Euclidean n → Euclidean (n - 1) → ℂ)
    (hb : ∀ s i, Continuous (Function.uncurry (b s i)))
    {X : Set (Euclidean n)} {U : Set (Euclidean (n - 1))}
    (hX : IsCompact X) (hU : IsCompact U)
    (hs : ∀ s i x θ, (x, θ) ∉ X ×ˢ U → b s i x θ = 0)
    (s : ℝ) : Lp ℂ 2 (volume.restrict Θ) →L[ℂ] NormalOutputL2 n n :=
  compactVectorKernelOperator Θ (hb s)
    (fun i ↦ HasCompactSupport.intro (hX.prod hU) (fun z hz ↦ hs s i z.1 z.2 hz))

private theorem output_weightedNormal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] NormalOutputL2 n n) (w : ℝ) :
    samplingOutputConjugation n ((w : ℂ) • (T ∘L T.adjoint)) =
      (w : ℂ) • (toSamplingOutput T ∘L (toSamplingOutput T).adjoint) := by
  exact (map_smul (samplingOutputConjugation n) (w : ℂ) (T ∘L T.adjoint)).trans
    (congrArg ((w : ℂ) • ·) (toSamplingOutput_normal T).symm)

private theorem real_weightedNormal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [InnerProductSpace ℝ H] [IsScalarTower ℝ ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] NormalOutputL2 n n) (w : ℝ) :
    samplingRealNormal n ((w : ℂ) • (T ∘L T.adjoint)) =
      w • (realQuadratureChannel (toSamplingOutput T) ∘L
        (realQuadratureChannel (toSamplingOutput T)).adjoint) := by
  calc
    _ = samplingRealNormal n (w • (T ∘L T.adjoint)) :=
      congrArg (samplingRealNormal n) (RCLike.real_smul_eq_coe_smul (K := ℂ) w
        (T ∘L T.adjoint)).symm
    _ = w • samplingRealNormal n (T ∘L T.adjoint) := (samplingRealNormal n).map_smul w _
    _ = _ := congrArg (w • ·) (toSamplingOutput_real_normal T).symm

variable (F : UniformNormalData G C) (K : ℝ) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
  (I : Set ℝ) (Θ : Set (Euclidean (n - 1)))
  (e : Euclidean n ≃ᵐ ℝ × Euclidean (n - 1))
  (he : MeasurePreserving e (volume.restrict G.D)
    ((volume.restrict I).prod (volume.restrict Θ)))
  (b : ℝ → Fin n → Euclidean n → Euclidean (n - 1) → ℂ)
  (hb : ∀ s i, Continuous (Function.uncurry (b s i)))
  {X : Set (Euclidean n)} {U : Set (Euclidean (n - 1))}
  (hX : IsCompact X) (hU : IsCompact U)
  (hs : ∀ s i x θ, (x, θ) ∉ X ×ˢ U → b s i x θ = 0)
  (ψ : Point → ℝ) (hψ : ∀ z, 0 ≤ ψ z)
  (z : ℝ → Point) (z₀ : Point) (Z : Euclidean n →L[ℝ] Point)
  (hz : ∀ u ∈ G.D, z₀ + Z u = z (e u).1)
  (hkernel : ∀ᵐ q ∂(volume.restrict I).prod (volume.restrict Θ), ∀ i : Fin n,
    (fun x ↦ normalizedOscillatoryKernel (normalOperatorScale n K) K (F.phase ε)
      (fun x u ↦ F.amplitude ε x u i) x (e.symm q)) =ᵐ[volume]
        fun x ↦ (Real.sqrt (ψ (z q.1)) : ℂ) * b q.1 i x q.2)
  (κ : ℝ → ℝ) (p : ℕ) (B h : ℝ) (c : Fin 3 → Fin (p + 1))
  (g : Lp ℂ ∞ (volume.restrict G.D))
  (hg : g =ᵐ[volume.restrict G.D] fun u ↦
    (coloredBlockMask p (integerCube (blockCutoff p B h)) (convolvedBoxWindow κ p)
      h c (z₀ + Z u) : ℂ))

include hε he hψ hz hkernel hg in
/-- The exact single-band weighted colored normal, with its Bochner
integrability proved from the common forward kernel. The input coordinate
map, the original normalized kernel, and the literal mask pullback are the
only identification premises. The same phase and amplitude occur at both
physical positions through their actual adjoint
(`app:ch_osc:eq:osc-exact-normal-kernel`,
`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem uniformNormal_eq_integral_compactSlice :
    let T := compactSliceOperator Θ b hb hX hU hs
    let w := fun s ↦ coloredBlockMask p (integerCube (blockCutoff p B h))
      (convolvedBoxWindow κ p) h c (z s) * ψ (z s)
    Integrable (fun s ↦ (w s : ℂ) • (T s ∘L (T s).adjoint)) (volume.restrict I) ∧
      F.uniformOscillatoryNormalOperator K g ε =
        ∫ s in I, (w s : ℂ) • (T s ∘L (T s).adjoint) := by
  let a := fun s ↦ compactCoordinateColumn (b s) (hb s) hX (hs s)
  have ha (s : ℝ) : MemLp (a s) 2 (volume.restrict Θ) :=
    memLp_compactCoordinateColumn (b s) (hb s) hX hU (hs s) Θ
  have hcol : ∀ᵐ q ∂(volume.restrict I).prod (volume.restrict Θ),
      uniformCoordinateColumn F K hε (e.symm q) = (Real.sqrt (ψ (z q.1)) : ℂ) • a q.1 q.2 := by
    filter_upwards [hkernel] with q hq
    ext i
    filter_upwards [uniformCoordinateColumn_coe F K hε (e.symm q) i,
      compactCoordinateColumn_coe (b q.1) (hb q.1) hX (hs q.1) q.2 i,
      hq i, Lp.coeFn_smul (Real.sqrt (ψ (z q.1)) : ℂ) ((a q.1 q.2) i)]
      with x hx hy hxy hsmul
    change _ = ((Real.sqrt (ψ (z q.1)) : ℂ) • (a q.1 q.2) i) x
    rw [hsmul, Pi.smul_apply, hx, hxy]
    change _ = (Real.sqrt (ψ (z q.1)) : ℂ) * ((a q.1 q.2) i) x
    rw [hy]
  have hmask : g =ᵐ[volume.restrict G.D] fun u ↦
      (coloredBlockMask p (integerCube (blockCutoff p B h)) (convolvedBoxWindow κ p)
        h c (z (e u).1) : ℂ) := by
    filter_upwards [hg, ae_restrict_mem G.isOpen_D.measurableSet] with u hu hD
    rw [hu, hz u hD]
  have hd := weighted_normal_disintegration_of_columns e he
    (memLp_uniformCoordinateColumn F K hε) ha (fun s ↦ ψ (z s))
    (fun s ↦ coloredBlockMask p (integerCube (blockCutoff p B h))
      (convolvedBoxWindow κ p) h c (z s)) (fun s ↦ hψ (z s)) hcol g hmask
  have hT (s : ℝ) : compactSliceOperator Θ b hb hX hU hs s = kernelSynthesis (ha s) :=
    compactVectorKernelOperator_eq_synthesis (b s) (hb s) hX hU (hs s) Θ
  dsimp only
  constructor
  · simpa only [hT] using hd.1
  · have hn : F.uniformOscillatoryNormalOperator K g ε =
        kernelSynthesis (memLp_uniformCoordinateColumn F K hε) ∘L multiplicationOperator g ∘L
          (kernelSynthesis (memLp_uniformCoordinateColumn F K hε)).adjoint :=
        congrArg (fun T : Lp ℂ 2 (volume.restrict G.D) →L[ℂ] NormalOutputL2 n n ↦
          T ∘L multiplicationOperator g ∘L T.adjoint)
          (uniformOscillatoryOperator_eq_synthesis F K hε)
    refine hn.trans (hd.2.trans ?_)
    apply integral_congr_ae
    apply Eventually.of_forall
    intro s
    dsimp only
    exact congrArg (fun T : Lp ℂ 2 (volume.restrict Θ) →L[ℂ] NormalOutputL2 n n ↦
      ((coloredBlockMask p (integerCube (blockCutoff p B h)) (convolvedBoxWindow κ p)
        h c (z s) * ψ (z s) : ℝ) : ℂ) • (T ∘L T.adjoint)) (hT s).symm

include hε he hψ hz hkernel hg in
set_option maxHeartbeats 800000 in
/-- Single-band disintegration on `SamplingKernelBounds.Output`, and on both
physical real quadratures. The real normal uses the published transfer with
exact factor four. The common primitive forward kernel supplies the complex
and real Bochner integrability (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem samplingNormal_eq_integral_compactSlice :
    let T := compactSliceOperator Θ b hb hX hU hs
    let w := fun s ↦ coloredBlockMask p (integerCube (blockCutoff p B h))
      (convolvedBoxWindow κ p) h c (z s) * ψ (z s)
    Integrable (fun s ↦ (w s : ℂ) •
      (toSamplingOutput (T s) ∘L (toSamplingOutput (T s)).adjoint)) (volume.restrict I) ∧
    samplingOutputConjugation n (F.uniformOscillatoryNormalOperator K g ε) =
      ∫ s in I, (w s : ℂ) •
        (toSamplingOutput (T s) ∘L (toSamplingOutput (T s)).adjoint) ∧
    Integrable (fun s ↦ w s •
      (realQuadratureChannel (toSamplingOutput (T s)) ∘L
        (realQuadratureChannel (toSamplingOutput (T s))).adjoint)) (volume.restrict I) ∧
    samplingRealNormal n (F.uniformOscillatoryNormalOperator K g ε) =
      ∫ s in I, w s •
        (realQuadratureChannel (toSamplingOutput (T s)) ∘L
          (realQuadratureChannel (toSamplingOutput (T s))).adjoint) := by
  let T := compactSliceOperator Θ b hb hX hU hs
  let w := fun s ↦ coloredBlockMask p (integerCube (blockCutoff p B h))
    (convolvedBoxWindow κ p) h c (z s) * ψ (z s)
  dsimp only
  obtain ⟨hi, heq⟩ := uniformNormal_eq_integral_compactSlice
    (n := n) (G := G) (C := C) (ε := ε) (X := X) (U := U) F K hε I Θ e he b hb hX hU hs
    ψ hψ z z₀ Z hz hkernel κ p B h c g hg
  have hc (s : ℝ) : samplingOutputConjugation n ((w s : ℂ) • (T s ∘L (T s).adjoint)) =
      (w s : ℂ) • (toSamplingOutput (T s) ∘L (toSamplingOutput (T s)).adjoint) := by
    exact output_weightedNormal (T s) (w s)
  have hr (s : ℝ) : samplingRealNormal n ((w s : ℂ) • (T s ∘L (T s).adjoint)) =
      w s • (realQuadratureChannel (toSamplingOutput (T s)) ∘L
        (realQuadratureChannel (toSamplingOutput (T s))).adjoint) := by
    exact real_weightedNormal (T s) (w s)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((integrable_samplingOutputConjugation_iff _).mpr hi).congr
      (Eventually.of_forall hc)
  · exact (congrArg (samplingOutputConjugation n) heq).trans
      ((samplingOutputConjugation_integral (volume.restrict I) _).trans
        (integral_congr_ae (Eventually.of_forall hc)))
  · exact (integrable_samplingRealNormal hi).congr (Eventually.of_forall hr)
  · exact (congrArg (samplingRealNormal n) heq).trans
      ((samplingRealNormal_integral hi).trans (integral_congr_ae (Eventually.of_forall hr)))

end JanetCartan.Sampling.ColoredNormalComparison.EuclideanDisintegration
