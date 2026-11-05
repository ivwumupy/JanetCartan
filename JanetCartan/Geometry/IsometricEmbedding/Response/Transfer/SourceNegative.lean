module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.ShellLoss
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.ShellData
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.Mask
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.Normalization

/-!
# Negative Sobolev decay of the original source: assembly

The source is the literal `χ exp(iρφ) f` in the proof of
`app:ch_response:prop:response-graded`, immediately before
`app:ch_response:eq:response-graded-reduced`.

The L¹ and L² statements and the physical Fourier L² bound below are proved
from the raw geometry and actual Sobolev envelope. `ShellLoss` proves the
annular estimate with a sharp L² input and absorbs a fixed amplitude jet loss
only in the complementary tail. The Sobolev-to-jet deduction, concrete shell
instantiation, and weighted physical-frequency comparison are all proved from
the stated inputs. No negative estimate for residual outputs is assumed.

The geometric input is to be supplied by `jc-compatible-phase-geometry`, and
the actual Euclidean Sobolev envelope by `jc-leading-wave` or `jc-current-mean`.
Consumers `jc-response-transfer` and `jc-arbitrary-accuracy` must instantiate
these inputs; this conditional deduction does not construct the paper's response.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform

namespace JanetCartan.ResponseTransfer.SourceNegative

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

omit [CompleteSpace F] in
private theorem sqrt_integral_norm_sq_toLp {h : Euclidean n → F}
    (hh : MemLp h 2 volume) : Real.sqrt (∫ x, ‖h x‖ ^ 2) = ‖hh.toLp h‖ := by
  have he : (∫ x, ‖h x‖ ^ 2) = ‖hh.toLp h‖ ^ 2 := by
    calc
      _ = ∫ x, ‖(hh.toLp h) x‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hh.coeFn_toLp] with x hx
        rw [hx]
      _ = _ := by
        apply Complex.ofRealLI.injective
        simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using
          (L2.inner_def (𝕜 := ℂ) (hh.toLp h) (hh.toLp h)).symm
  rw [he, Real.sqrt_sq (norm_nonneg _)]

/-- The original source's physical Fourier L² bound, with the exact Plancherel
factor and no power of `K`. This supplies the annular input to
`source_negative_sobolev_with_l2` in `app:ch_response:prop:response-graded`. -/
theorem source_physicalFourier_l2_le
    {χ φ : Euclidean n → ℝ} {S : Set (Euclidean n)}
    {c G L : ℝ} {P X : ℕ → ℝ} (g : SourceGeometry χ φ S c G L P X)
    {f : Euclidean n → F} {hf : MemLp f 2 volume} {A K : ℝ} {C : ℕ → ℝ}
    (h : SobolevEnvelopeBounds f hf A K C) (ρ : ℝ) :
    Localization.fourierWeightedL2Norm volume 0 (fun ξ : Euclidean n ↦
      Localization.physicalFourierIntegral volume (modulatedSource χ φ f ρ)
        (InnerProductSpace.toDual ℝ (Euclidean n) ξ)) ≤
      (2 * Real.pi) ^ ((n : ℝ) / 2) * (X 0 * C 0 * A) := by
  have hm := source_memLp g hf ρ
  have hi := source_integrable g h.smooth.continuous ρ
  have hs := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  rw [Localization.fourierWeightedL2Norm_zero_physicalFourierIntegral hi hs,
    sqrt_integral_norm_sq_toLp hm]
  simpa only [Euclidean, finrank_euclideanSpace, Fintype.card_fin] using
    mul_le_mul_of_nonneg_left (source_norm_le g h ρ)
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
        ((Module.finrank ℝ (Euclidean n) : ℝ) / 2))

/-- The actual Fourier transform of the original L² source belongs to every
nonpositive Sobolev order. This is membership only; decay requires the full
source gap and the tail estimate (`app:ch_response:prop:response-graded`). -/
theorem source_negative_fourier_memLp
    {χ φ : Euclidean n → ℝ} {S : Set (Euclidean n)}
    {c G L : ℝ} {P X : ℕ → ℝ} (g : SourceGeometry χ φ S c G L P X)
    {f : Euclidean n → F} (hf : MemLp f 2 volume) (ρ : ℝ)
    {M : ℝ} (hM : 0 ≤ M) :
    MemLp (fun ξ ↦ Pseudodifferential.euclideanSobolevWeight (-M) ξ •
      (𝓕 ((source_memLp g hf ρ).toLp (modulatedSource χ φ f ρ)) :
        Lp (α := Euclidean n) F 2 volume) ξ) 2 volume := by
  apply (Lp.memLp (𝓕 ((source_memLp g hf ρ).toLp _))).mono
    ((Pseudodifferential.continuous_euclideanSobolevWeight (-M)).aestronglyMeasurable.smul
      (Lp.memLp _).aestronglyMeasurable)
  filter_upwards [] with ξ
  change ‖Pseudodifferential.euclideanSobolevWeight (-M) ξ •
    (𝓕 ((source_memLp g hf ρ).toLp (modulatedSource χ φ f ρ)) :
      Lp (α := Euclidean n) F 2 volume) ξ‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (Pseudodifferential.euclideanSobolevWeight_pos (-M) ξ)]
  have hw : Pseudodifferential.euclideanSobolevWeight (-M) ξ ≤ 1 := by
    simpa using Pseudodifferential.euclideanSobolevWeight_mono (neg_nonpos.mpr hM) ξ
  exact (mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans_eq (one_mul _)

/-- The unit point mass realizes the original source in the source-shell API
(`app:ch_response:prop:response-graded`). -/
theorem unitDirac_oscillatorySource_eq_modulatedSource
    (χ φ : Euclidean n → ℝ) (f : Euclidean n → F) (ρ : ℝ) :
    Localization.oscillatorySource (VectorMeasure.dirac () (1 : ℂ))
      (fun _ : Unit ↦ φ) (fun _ : Unit ↦ fun x ↦ χ x • f x) ρ =
      modulatedSource χ φ f ρ := by
  funext x
  simp only [Localization.oscillatorySource, Localization.complexMeasureIntegral,
    VectorMeasure.integral_dirac, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, one_smul]
  rw [← carrier_eq_phaseOscillation]
  exact smul_comm (carrier ρ φ x) (χ x) (f x)

/-- Choose enough integrations to absorb the fixed envelope loss in the tail
preceding `app:ch_response:eq:response-graded-reduced`. -/
def sourceDecayOrder (n N : ℕ) (θ : ℝ) : ℕ :=
  Classical.choose (exists_nat_gt
    (max ((n : ℝ) / 2) (((N : ℝ) + ((n : ℝ) + 1 + (n : ℝ) / 2)) / θ)))

/-- The chosen order meets both the tail integrability and loss absorption
requirements for `app:ch_response:prop:response-graded`. -/
theorem sourceDecayOrder_spec (n N : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    (n : ℝ) / 2 < sourceDecayOrder n N θ ∧
      (N : ℝ) + ((n : ℝ) + 1 + (n : ℝ) / 2) ≤ θ * sourceDecayOrder n N θ := by
  have hq := Classical.choose_spec (exists_nat_gt
    (max ((n : ℝ) / 2) (((N : ℝ) + ((n : ℝ) + 1 + (n : ℝ) / 2)) / θ)))
  refine ⟨(le_max_left _ _).trans_lt hq, ?_⟩
  have hh := (div_lt_iff₀ hθ).mp ((le_max_right _ _).trans_lt hq)
  exact (by simpa [sourceDecayOrder, mul_comm] using hh.le)

/-- The scale-independent constant in the original-source negative estimate.
Its displayed factors include both physical Plancherel and the `2π` dilation
back to the actual Fourier Sobolev norm (`app:ch_response:prop:response-graded`). -/
def modulatedSourceNegativeConstant (n N : ℕ) (S : Set (Euclidean n))
    (c G θ : ℝ) (P X C : ℕ → ℝ) : ℝ :=
  (2 * Real.pi) ^ ((N : ℝ) - (n : ℝ) / 2) *
    ((c / 8) ^ (-(N : ℝ)) * (2 * Real.pi) ^ ((n : ℝ) / 2) * (X 0 * C 0) +
      Localization.sourceTailConstant (EuclideanSpace.basisFun (Fin n) ℝ) S
        (c / 2) (2 * G) 1 P (cutoffEnvelopeJetConstant n X C) 0 (sourceDecayOrder n N θ))

/-- The constant for the original-source estimate is nonnegative
(`app:ch_response:prop:response-graded`). -/
theorem modulatedSourceNegativeConstant_nonneg (n N : ℕ) (S : Set (Euclidean n))
    (c G θ : ℝ) (P X C : ℕ → ℝ) (hc : 0 ≤ c)
    (hX : ∀ i, 0 ≤ X i) (hC : ∀ i, 0 ≤ C i) :
    0 ≤ modulatedSourceNegativeConstant n N S c G θ P X C := by
  unfold modulatedSourceNegativeConstant
  apply mul_nonneg (by positivity)
  apply add_nonneg
  · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity))
      (mul_nonneg (hX 0) (hC 0))
  · exact sourceTailConstant_nonneg _ _ _ _ _ _ _ _ _ zero_le_one
      (cutoffEnvelopeJetConstant_nonneg n hX hC)

/-- The original modulated source has `A ρ⁻ᴺ` decay in the actual Euclidean
Fourier Sobolev norm, as asserted immediately before
`app:ch_response:eq:response-graded-reduced`. All shell amplitude derivatives
are derived from the Sobolev envelope; no estimate for residual outputs is
assumed. Geometry and the actual envelope remain inputs of the parent producers.
The constant is independent of `χ`, `φ`, `f`, `A`, `L`, `K`, and `ρ`. -/
theorem modulatedSource_negative_sobolev
    {χ φ : Euclidean n → ℝ} {S : Set (Euclidean n)}
    {c G L : ℝ} {P X : ℕ → ℝ} (g : SourceGeometry χ φ S c G L P X)
    {f : Euclidean n → F} {hf : MemLp f 2 volume} {A K : ℝ} {C : ℕ → ℝ}
    (h : SobolevEnvelopeBounds f hf A K C) (hLK : L ≤ K)
    {ρ θ : ℝ} (hρ : 1 ≤ ρ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hgap : K ≤ ρ ^ (1 - θ)) (N : ℕ) :
    (eLpNorm (fun η ↦ Pseudodifferential.euclideanSobolevWeight (-(N : ℝ)) η •
      (𝓕 ((source_memLp g hf ρ).toLp (modulatedSource χ φ f ρ)) :
        Lp (α := Euclidean n) F 2 volume) η) 2 volume).toReal ≤
      modulatedSourceNegativeConstant n N S c G θ P X C * A * ρ ^ (-(N : ℝ)) := by
  have hKρ : K ≤ ρ := hgap.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hρ (show 1 - θ ≤ 1 by linarith))
  have hs := sourceGeometry_shellBounds g h hLK
  let ν : ComplexMeasure Unit := VectorMeasure.dirac () (1 : ℂ)
  have : IsFiniteMeasure ν.variation := by
    dsimp [ν]
    simp only [VectorMeasure.variation_dirac, enorm_one, one_smul]
    infer_instance
  have hmass : ν.variation.real Set.univ = 1 := by
    simp [ν, Measure.real, VectorMeasure.variation_dirac]
  have heq : Localization.oscillatorySource ν (fun _ : Unit ↦ φ)
      (fun _ : Unit ↦ fun x ↦ χ x • f x) ρ = modulatedSource χ φ f ρ :=
    unitDirac_oscillatorySource_eq_modulatedSource χ φ f ρ
  obtain ⟨π, hπ⟩ := exists_sourceShellMask (E := Euclidean n)
    (c := c / 2) (G := 2 * G) (ρ := ρ)
    (by linarith [g.lower_pos])
    (by linarith [g.lower_pos, g.lower_lt_upper]) (by linarith)
  obtain ⟨hq, horder⟩ := sourceDecayOrder_spec n N hθ₀
  have hzero := source_physicalFourier_l2_le g h ρ
  rw [← heq] at hzero
  have hneg := source_negative_sobolev_with_l2 hs ν
    (EuclideanSpace.basisFun (Fin n) ℝ) hρ hπ (M := (N : ℝ))
    (Nat.cast_nonneg N) hKρ hgap (sourceDecayOrder n N θ)
    (by simpa [Euclidean] using hq) (by simpa [Euclidean] using horder) hzero
  rw [heq, hmass] at hneg
  have hn := negative_fourier_norm_le_physical
    (source_integrable g h.smooth.continuous ρ) (source_memLp g hf ρ)
    (show 0 ≤ (N : ℝ) from Nat.cast_nonneg N)
  apply (hn.trans (mul_le_mul_of_nonneg_left hneg (by positivity))).trans_eq
  unfold modulatedSourceNegativeConstant
  rw [show c / 2 / 4 = c / 8 by ring]
  ring

/-- Scalar specialization in the existing `MemFourierSobolev` and
`fourierSobolevNorm` API, including membership, for the original-source
estimate before `app:ch_response:eq:response-graded-reduced`. -/
theorem modulatedSource_memFourierSobolev_and_norm_le
    {χ φ : Euclidean n → ℝ} {S : Set (Euclidean n)}
    {c G L : ℝ} {P X : ℕ → ℝ} (g : SourceGeometry χ φ S c G L P X)
    {f : Euclidean n → ℂ} {hf : MemLp f 2 volume} {A K : ℝ} {C : ℕ → ℝ}
    (h : SobolevEnvelopeBounds f hf A K C) (hLK : L ≤ K)
    {ρ θ : ℝ} (hρ : 1 ≤ ρ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hgap : K ≤ ρ ^ (1 - θ)) (N : ℕ) :
    Pseudodifferential.MemFourierSobolev (-(N : ℝ))
        ((source_memLp g hf ρ).toLp (modulatedSource χ φ f ρ)) ∧
      Pseudodifferential.fourierSobolevNorm (-(N : ℝ))
        ((source_memLp g hf ρ).toLp (modulatedSource χ φ f ρ)) ≤
        modulatedSourceNegativeConstant n N S c G θ P X C * A * ρ ^ (-(N : ℝ)) :=
  ⟨source_negative_fourier_memLp g hf ρ (Nat.cast_nonneg N),
    modulatedSource_negative_sobolev g h hLK hρ hθ₀ hθ₁ hgap N⟩

end JanetCartan.ResponseTransfer.SourceNegative
