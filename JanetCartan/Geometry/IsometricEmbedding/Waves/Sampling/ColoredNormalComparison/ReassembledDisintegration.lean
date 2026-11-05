module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.EuclideanDisintegration
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.GroupedKernels
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.WideDilation

/-!
# Common kernels after smooth-band reassembly

For `app:ch_waves:eq:sampling-prefix-normal`, connect the Euclidean
single-band disintegration to the original wide-band kernels. The transverse
dilation is the existing `RawPrimary.SliceBounds` change of variables, built
from `RawInputDilation`. Its square-root Jacobian is explicit. The input chart
retains the support of the actual angular cutoff; the actual smooth
coefficient also vanishes outside its original wide band. No sharp indicator is differentiated.

The actual sampling producer supplies only the normalized forward-kernel
identity, the original smooth-band support, and the input coordinate map.
All operator-normal identities and their integrability are deductions.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory Set InnerProductSpace
open scoped ENNReal
namespace JanetCartan.Sampling.ColoredNormalComparison
open NormalComparison SamplingKernelBounds Pseudodifferential RawInputPartition
open EuclideanDisintegration RawPrimary.SliceBounds
open SeparatedSampling LatticeQuadrature BackgroundQuadrature

variable {n : ℕ} {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
  [LocallyCompactSpace P]

/-- The original wide-band column after its literal transverse dilation,
including the exact square-root Jacobian. The output is still Euclidean
Lebesgue L² (`app:ch_waves:eq:sampling-prefix-normal`). -/
def dilatedWideCoordinateColumn (D : BandKernelData P n) (j : ℕ) (z : P)
    (θ : Euclidean (n - 1)) : NormalOutputL2 n n :=
  (Real.sqrt (((2 : ℝ) ^ j) ^ (n - 1)) : ℂ) •
    finiteL2CoordinateIsometry volume (D.column z ((2 : ℝ) ^ j • θ))

/-- The fixed buffered input box and the original continuous raw kernel give
square integrability before any normal estimate
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem memLp_dilatedWideCoordinateColumn (D : BandKernelData P n) (j : ℕ) (z : P)
    {Θ : Set (Euclidean (n - 1))} (hΘ : IsCompact Θ) :
    MemLp (dilatedWideCoordinateColumn D j z) 2 (volume.restrict Θ) := by
  apply memLp_restrict_compact_column _ hΘ
  have hd : Continuous (fun θ : Euclidean (n - 1) ↦ D.column z ((2 : ℝ) ^ j • θ)) :=
    D.continuous_column.comp (continuous_const.prodMk
      ((continuous_id (X := Euclidean (n - 1))).const_smul ((2 : ℝ) ^ j)))
  exact ((finiteL2CoordinateIsometry volume).continuous.comp hd).const_smul
    (Real.sqrt (((2 : ℝ) ^ j) ^ (n - 1)) : ℂ)

omit [FirstCountableTopology P] [LocallyCompactSpace P] in
private theorem bandColumn_zero_of_kernel (D : BandKernelData P n) (z : P)
    (η : Euclidean (n - 1)) (h : ∀ x, D.kernel z η x = 0) : D.column z η = 0 := by
  apply Lp.ext
  filter_upwards [D.column_coe z η, Lp.coeFn_zero (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n))] with x hx hz
  exact hx.trans ((h x).trans hz.symm)

private theorem wideKernelOperator_normal_integral (D : BandKernelData P n) (j : ℕ) (z : P) :
    atomNormal (wideKernelOperator D j z) =
      ∫ η in wideBand n j, rankOne ℂ (D.column z η) (D.column z η) := by
  unfold atomNormal wideKernelOperator
  exact kernelSynthesis_normal_eq_integral (memLp_wideBand_column D j z)

/-- The dilated common kernel has exactly the original wide-band normal.
The support hypothesis concerns the forward kernel and is supplied by the
unchanged smooth radial coefficient. No normal equality is assumed
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem dilatedWideCoordinateColumn_normal (D : BandKernelData P n) (j : ℕ) (z : P)
    {Θ : Set (Euclidean (n - 1))} (hΘ : IsCompact Θ)
    (hinput : ∀ θ, θ ∉ Θ → ∀ x, D.kernel z ((2 : ℝ) ^ j • θ) x = 0)
    (hsupport : ∀ η, η ∉ wideBand n j → ∀ x, D.kernel z η x = 0) :
    samplingOutputConjugation n
      (kernelSynthesis (memLp_dilatedWideCoordinateColumn D j z hΘ) ∘L
        (kernelSynthesis (memLp_dilatedWideCoordinateColumn D j z hΘ)).adjoint) =
      atomNormal (wideKernelOperator D j z) := by
  let e := finiteL2CoordinateIsometry (I := Fin n) (volume : Measure (Euclidean n))
  have hr (θ : Euclidean (n - 1)) :
      samplingOutputConjugation n
        (rankOne ℂ (dilatedWideCoordinateColumn D j z θ)
          (dilatedWideCoordinateColumn D j z θ)) =
        (((2 : ℝ) ^ j) ^ (n - 1) : ℝ) •
          rankOne ℂ (D.column z ((2 : ℝ) ^ j • θ))
            (D.column z ((2 : ℝ) ^ j • θ)) := by
    ext1 f
    change e.symm (rankOne ℂ _ _ (e f)) = _
    simp only [dilatedWideCoordinateColumn, rankOne_apply, inner_smul_left,
      Complex.conj_ofReal, smul_smul]
    rewrite [mul_right_comm, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity),
      e.inner_map_map]
    simp only [map_smul, smul_apply, rankOne_apply]
    rewrite [e.symm_apply_apply]
    simpa only [Complex.real_smul] using
      (smul_assoc (((2 : ℝ) ^ j) ^ (n - 1))
        (inner ℂ (D.column z ((2 : ℝ) ^ j • θ)) f) (D.column z ((2 : ℝ) ^ j • θ)))
  have hi : (∫ θ in Θ, rankOne ℂ (D.column z ((2 : ℝ) ^ j • θ))
      (D.column z ((2 : ℝ) ^ j • θ))) =
      ∫ θ in wideBand n 0, rankOne ℂ (D.column z ((2 : ℝ) ^ j • θ))
        (D.column z ((2 : ℝ) ^ j • θ)) := by
    have hΘint : (∫ θ in Θ, rankOne ℂ (D.column z ((2 : ℝ) ^ j • θ))
        (D.column z ((2 : ℝ) ^ j • θ))) =
        ∫ θ, rankOne ℂ (D.column z ((2 : ℝ) ^ j • θ))
          (D.column z ((2 : ℝ) ^ j • θ)) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro θ hθ
      rewrite [bandColumn_zero_of_kernel D z _ (hinput θ hθ)]
      simp
    have hwide : (∫ θ in wideBand n 0, rankOne ℂ (D.column z ((2 : ℝ) ^ j • θ))
        (D.column z ((2 : ℝ) ^ j • θ))) =
        ∫ θ, rankOne ℂ (D.column z ((2 : ℝ) ^ j • θ))
          (D.column z ((2 : ℝ) ^ j • θ)) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro θ hθ
      have hη : (2 : ℝ) ^ j • θ ∉ wideBand n j := by
        intro ht
        apply hθ
        have hm : θ ∈ (fun θ : Euclidean (n - 1) ↦ (2 : ℝ) ^ j • θ) ⁻¹' wideBand n j := ht
        rwa [preimage_wideBand_smul] at hm
      rewrite [bandColumn_zero_of_kernel D z _ (hsupport _ hη)]
      simp
    exact hΘint.trans hwide.symm
  let f := fun η : Euclidean (n - 1) ↦ rankOne ℂ (D.column z η) (D.column z η)
  let jac : ℝ := ((2 : ℝ) ^ j) ^ (n - 1)
  have hjac : jac ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))
  have hscale (A : SamplingKernelBounds.Output n →L[ℂ] SamplingKernelBounds.Output n) :
      jac • (jac⁻¹ • A) = A :=
    (smul_smul jac jac⁻¹ A).trans
      ((congrArg (fun r : ℝ ↦ r • A) (mul_inv_cancel₀ hjac)).trans (one_smul ℝ A))
  have hnormal := kernelSynthesis_normal_eq_integral
    (memLp_dilatedWideCoordinateColumn D j z hΘ)
  have hconj := congrArg (samplingOutputConjugation n) hnormal
  have htransfer := samplingOutputConjugation_integral (n := n) (volume.restrict Θ)
    (fun θ ↦ rankOne ℂ (dilatedWideCoordinateColumn D j z θ)
      (dilatedWideCoordinateColumn D j z θ))
  have hpoint := integral_congr_ae (μ := volume.restrict Θ) (Filter.Eventually.of_forall hr)
  have hscalar := integral_smul (μ := volume.restrict Θ) jac
    (fun θ : Euclidean (n - 1) ↦ f ((2 : ℝ) ^ j • θ))
  have hrestrict := congrArg (fun A : SamplingKernelBounds.Output n →L[ℂ]
    SamplingKernelBounds.Output n ↦ jac • A) hi
  have hdilate := congrArg (fun A : SamplingKernelBounds.Output n →L[ℂ]
    SamplingKernelBounds.Output n ↦ jac • A) (integral_wideBand_smul (n := n) j f)
  exact hconj.trans (htransfer.trans (hpoint.trans (hscalar.trans
    (hrestrict.trans (hdilate.trans ((hscale (∫ η in wideBand n j, f η)).trans
      (wideKernelOperator_normal_integral D j z).symm))))))

variable {G : UniformNormalGeometry n n} {C : ℕ → ℝ}

/-- Single smooth-band disintegration into the original raw slice normals.
The primitive matching equality retains the Fourier normalization, the
square-root patch weight, the transverse Jacobian, and the same raw kernel.
The conclusion includes Bochner integrability on the slice measure; neither
normal equality nor integrability is a premise
(`app:ch_waves:eq:sampling-prefix-normal`,
`app:ch_waves:eq:colored-normal-comparison`). -/
theorem samplingNormal_eq_integral_wideKernel
    (F : UniformNormalData G C) (K : ℝ) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (D : BandKernelData P n) (j : ℕ) (q : ℝ → P)
    (I : Set ℝ) {Θ : Set (Euclidean (n - 1))} (hΘ : IsCompact Θ)
    (hinput : ∀ s θ, θ ∉ Θ → ∀ x, D.kernel (q s) ((2 : ℝ) ^ j • θ) x = 0)
    (hsupport : ∀ s η, η ∉ wideBand n j → ∀ x, D.kernel (q s) η x = 0)
    (e : Euclidean n ≃ᵐ ℝ × Euclidean (n - 1))
    (he : MeasurePreserving e (volume.restrict G.D)
      ((volume.restrict I).prod (volume.restrict Θ)))
    (ψ : Point → ℝ) (hψ : ∀ z, 0 ≤ ψ z)
    (z : ℝ → Point) (z₀ : Point) (Z : Euclidean n →L[ℝ] Point)
    (hz : ∀ u ∈ G.D, z₀ + Z u = z (e u).1)
    (hkernel : ∀ᵐ u ∂(volume.restrict I).prod (volume.restrict Θ), ∀ i : Fin n,
      (fun x ↦ normalizedOscillatoryKernel (normalOperatorScale n K) K (F.phase ε)
        (fun x w ↦ F.amplitude ε x w i) x (e.symm u)) =ᵐ[volume]
      fun x ↦ (Real.sqrt (ψ (z u.1)) : ℂ) *
        ((Real.sqrt (((2 : ℝ) ^ j) ^ (n - 1)) : ℂ) *
          D.kernel (q u.1) ((2 : ℝ) ^ j • u.2) x i))
    (κ : ℝ → ℝ) (p : ℕ) (B h : ℝ) (c : Fin 3 → Fin (p + 1))
    (g : Lp ℂ ∞ (volume.restrict G.D))
    (hg : g =ᵐ[volume.restrict G.D] fun u ↦
      (coloredBlockMask p (integerCube (blockCutoff p B h)) (convolvedBoxWindow κ p)
        h c (z₀ + Z u) : ℂ)) :
    let w := fun s ↦ coloredBlockMask p (integerCube (blockCutoff p B h))
      (convolvedBoxWindow κ p) h c (z s) * ψ (z s)
    Integrable (fun s ↦ w s • atomNormal (wideKernelOperator D j (q s)))
      (volume.restrict I) ∧
    samplingOutputConjugation n (F.uniformOscillatoryNormalOperator K g ε) =
      ∫ s in I, w s • atomNormal (wideKernelOperator D j (q s)) := by
  let a := fun s ↦ dilatedWideCoordinateColumn D j (q s)
  have ha (s : ℝ) : MemLp (a s) 2 (volume.restrict Θ) :=
    memLp_dilatedWideCoordinateColumn D j (q s) hΘ
  have hcol : ∀ᵐ u ∂(volume.restrict I).prod (volume.restrict Θ),
      uniformCoordinateColumn F K hε (e.symm u) =
        (Real.sqrt (ψ (z u.1)) : ℂ) • a u.1 u.2 := by
    filter_upwards [hkernel] with u hu
    ext i
    have hd := (finiteL2CoordinateIsometry_ae_iff volume
      (D.column (q u.1) ((2 : ℝ) ^ j • u.2))
      (D.kernel (q u.1) ((2 : ℝ) ^ j • u.2))).mp (D.column_coe _ _) i
    filter_upwards [uniformCoordinateColumn_coe F K hε (e.symm u) i, hd, hu i,
      Lp.coeFn_smul (Real.sqrt (ψ (z u.1)) : ℂ) ((a u.1 u.2) i),
      Lp.coeFn_smul (Real.sqrt (((2 : ℝ) ^ j) ^ (n - 1)) : ℂ)
        ((finiteL2CoordinateIsometry volume (D.column (q u.1) ((2 : ℝ) ^ j • u.2))) i)]
      with x hx hd hk hw hj
    change _ = ((Real.sqrt (ψ (z u.1)) : ℂ) • (a u.1 u.2) i) x
    rewrite [hw, Pi.smul_apply, hx, hk]
    change _ = (Real.sqrt (ψ (z u.1)) : ℂ) *
      (((Real.sqrt (((2 : ℝ) ^ j) ^ (n - 1)) : ℂ) •
        (finiteL2CoordinateIsometry volume (D.column (q u.1) ((2 : ℝ) ^ j • u.2))) i) x)
    rewrite [hj, Pi.smul_apply, hd]
    rfl
  have hmask : g =ᵐ[volume.restrict G.D] fun u ↦
      (coloredBlockMask p (integerCube (blockCutoff p B h)) (convolvedBoxWindow κ p)
        h c (z (e u).1) : ℂ) := by
    filter_upwards [hg, ae_restrict_mem G.isOpen_D.measurableSet] with u hu hD
    rewrite [hu, hz u hD]
    rfl
  obtain ⟨hi, hn⟩ := weighted_normal_disintegration_of_columns e he
    (memLp_uniformCoordinateColumn F K hε) ha (fun s ↦ ψ (z s))
    (fun s ↦ coloredBlockMask p (integerCube (blockCutoff p B h))
      (convolvedBoxWindow κ p) h c (z s)) (fun s ↦ hψ (z s)) hcol g hmask
  let w := fun s ↦ coloredBlockMask p (integerCube (blockCutoff p B h))
    (convolvedBoxWindow κ p) h c (z s) * ψ (z s)
  have ht (s : ℝ) : samplingOutputConjugation n
      ((w s : ℂ) • (kernelSynthesis (ha s) ∘L (kernelSynthesis (ha s)).adjoint)) =
        w s • atomNormal (wideKernelOperator D j (q s)) := by
    rewrite [map_smul, dilatedWideCoordinateColumn_normal D j (q s) hΘ (hinput s) (hsupport s)]
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) (w s)
      (atomNormal (wideKernelOperator D j (q s)))).symm
  dsimp only
  constructor
  · exact ((integrable_samplingOutputConjugation_iff _).mpr hi).congr
      (Filter.Eventually.of_forall ht)
  · rewrite [UniformNormalData.uniformOscillatoryNormalOperator,
      uniformOscillatoryOperator_eq_synthesis F K hε, hn]
    exact (samplingOutputConjugation_integral (n := n) (volume.restrict I)
      (fun s ↦ (w s : ℂ) • (kernelSynthesis (ha s) ∘L (kernelSynthesis (ha s)).adjoint))).trans
        (integral_congr_ae (Filter.Eventually.of_forall ht))

end JanetCartan.Sampling.ColoredNormalComparison
