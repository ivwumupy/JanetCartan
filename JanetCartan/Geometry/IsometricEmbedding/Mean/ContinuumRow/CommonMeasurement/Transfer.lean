module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement.Restriction
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement.Amplitude
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.Freezing.VectorMultipliers
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.VectorKernel

/-!
# Transfer of common measurement restriction

The physical multiplier and torus multiplier commute with the existing
normalized measure-preserving maps. Consequently the global reflected normal
of the SAME carrier restricts to the transfer of the two-sided physical
restriction. Its literal full matrix amplitude is identified on compact tests;
no new normal identity is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CommonMeasurement
open PeriodicLocalL2 ContinuumNormal Pseudodifferential AmplitudeBound
variable {n : ℕ}
local notation "H" => EuclideanL2 n (EuclideanSpace ℂ (Fin n))

/-- Output restriction commutes with physical-to-torus transfer, with the
existing normalized Haar measure (`app:ch_background:defn:bg-row`). -/
theorem complexMultiplier_toTorus (χ : C(Torus n, ℝ)) (β : Euclidean n → ℝ)
    (hβ : Continuous β) (hβs : HasCompactSupport β)
    (hχ : ∀ z, χ z = β (centeredTorusRepresentative z)) (f : H) :
    complexMultiplier χ (toTorus (𝕜 := ℂ) f) =
      toTorus (𝕜 := ℂ) (freezingVectorPhysicalMultiplier β hβ hβs f) := by
  apply Lp.ext
  filter_upwards [complexMultiplier_coeFn χ (toTorus (𝕜 := ℂ) f),
    toTorus_coe (𝕜 := ℂ) f,
    toTorus_coe (𝕜 := ℂ) (freezingVectorPhysicalMultiplier β hβ hβs f),
    measurePreserving_representative.quasiMeasurePreserving.ae_eq_comp
      (freezingVectorPhysicalMultiplier_coeFn β hβ hβs f).restrict] with z hm hf ht hp
  rw [hm, hf, ht]
  change (χ z : ℂ) • f (centeredTorusRepresentative z) =
    freezingVectorPhysicalMultiplier β hβ hβs f (centeredTorusRepresentative z)
  simp only [Function.comp_apply] at hp
  rw [hp, hχ, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

/-- The source transfer retains its half-open-cell indicator. No density or
Fourier normalization factor is inserted (`app:ch_background:eq:bg-T`). -/
theorem toEuclidean_complexMultiplier (χ : C(Torus n, ℝ)) (β : Euclidean n → ℝ)
    (hβ : Continuous β) (hβs : HasCompactSupport β)
    (hχ : ∀ z, χ z = β (centeredTorusRepresentative z)) (f : ComplexOutputL2 n) :
    toEuclidean (𝕜 := ℂ) (complexMultiplier χ f) =
      freezingVectorPhysicalMultiplier β hβ hβs (toEuclidean (𝕜 := ℂ) f) := by
  apply Lp.ext
  have hm := (ae_restrict_iff' measurableSet_halfOpenCell).mp
    (measurePreserving_quotient.quasiMeasurePreserving.ae
      (complexMultiplier_coeFn χ f))
  filter_upwards [toEuclidean_coe (𝕜 := ℂ) (complexMultiplier χ f),
    freezingVectorPhysicalMultiplier_coeFn β hβ hβs (toEuclidean (𝕜 := ℂ) f),
    toEuclidean_coe (𝕜 := ℂ) f, hm] with x ht hp hf hm
  rw [ht, hp, hf]
  by_cases hx : x ∈ halfOpenCell n
  · simp only [indicator_of_mem hx, periodicLift, Function.comp_apply]
    rw [hm hx, hχ, centeredTorusRepresentative_quotient hx,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  · simp [hx]

/-- Exact global operator transfer of the two physical cutoff factors
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem transferOperator_sandwich (χ : C(Torus n, ℝ)) (β : Euclidean n → ℝ)
    (hβ : Continuous β) (hβs : HasCompactSupport β)
    (hχ : ∀ z, χ z = β (centeredTorusRepresentative z)) (A : H →L[ℂ] H) :
    complexMultiplier χ ∘L transferOperator A ∘L complexMultiplier χ =
      transferOperator (freezingVectorPhysicalMultiplier β hβ hβs ∘L A ∘L
        freezingVectorPhysicalMultiplier β hβ hβs) := by
  ext1 f
  change complexMultiplier χ (toTorus (𝕜 := ℂ)
    (A (toEuclidean (𝕜 := ℂ) (complexMultiplier χ f)))) = _
  rw [complexMultiplier_toTorus χ β hβ hβs hχ,
    toEuclidean_complexMultiplier χ β hβ hβs hχ]
  rfl

/-- Restrict the supported producer's global reflected normal for the SAME
`U`. The reflected physical operator `A` already includes factor four;
restriction adds no further factor (`app:ch_background:eq:bg-real-symbol`). -/
theorem restrictCarrier_global_normal (χ : C(Torus n, ℝ)) (β : Euclidean n → ℝ)
    (hβ : Continuous β) (hβs : HasCompactSupport β)
    (hχ : ∀ z, χ z = β (centeredTorusRepresentative z))
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n) (A : H →L[ℂ] H)
    (hU : carrierChannel U ∘L (carrierChannel U).adjoint =
      realOutputCompression (transferOperator A)) :
    carrierChannel (restrictCarrier χ U) ∘L (carrierChannel (restrictCarrier χ U)).adjoint =
      realOutputCompression (transferOperator
        (freezingVectorPhysicalMultiplier β hβ hβs ∘L A ∘L
          freezingVectorPhysicalMultiplier β hβ hβs)) := by
  rw [carrierChannel_restrictCarrier_normal, hU, ← realOutputCompression_sandwich,
    transferOperator_sandwich χ β hβ hβs hχ]

/-- The physically restricted bounded matrix PDO realizes exactly the full
amplitude multiplied at BOTH physical positions. This proves its identity as
a bounded full-amplitude realization without assuming derivative budgets for
a newly introduced operator (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem physicalSandwich_ae_matrixFullAmplitudeOperator
    (hn : 0 < n) (R : ℝ)
    (b : Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j))
    (B : ℝ) (hB : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ b ξ z i j) (2 * (n + 1)) B)
    (β : Euclidean n → ℝ) (hβ : ContDiff ℝ ∞ β) (hβs : HasCompactSupport β)
    (f : Euclidean n → EuclideanSpace ℂ (Fin n))
    (hf : MemLp f 2 volume) (hfc : ContDiff ℝ ∞ f) (hfs : HasCompactSupport f) :
    (freezingVectorPhysicalMultiplier β hβ.continuous hβs ∘L
      vectorTwoPositionL2Operator hn R b hb hs B hB ∘L
      freezingVectorPhysicalMultiplier β hβ.continuous hβs) (hf.toLp f) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (matrixFullAmplitudeOperator
        (fun x y ξ ↦ restrictAmplitude b β ξ (pairedPosition x y)) (fun y j ↦ f y j) x) := by
  let g := fun y ↦ β y • f y
  have hgc : ContDiff ℝ ∞ g := hβ.smul hfc
  have hgs : HasCompactSupport g := hfs.smul_left (f := β)
  have hg : MemLp g 2 volume := hgc.continuous.memLp_of_hasCompactSupport hgs
  have he : freezingVectorPhysicalMultiplier β hβ.continuous hβs (hf.toLp f) = hg.toLp g := by
    apply Lp.ext
    filter_upwards [freezingVectorPhysicalMultiplier_coeFn β hβ.continuous hβs (hf.toLp f),
      hf.coeFn_toLp, hg.coeFn_toLp] with y hm hf' hg'
    rw [hm, hf', hg']
  simp only [ContinuousLinearMap.comp_apply, he]
  filter_upwards [freezingVectorPhysicalMultiplier_coeFn β hβ.continuous hβs
    (vectorTwoPositionL2Operator hn R b hb hs B hB (hg.toLp g)),
    vectorTwoPositionL2Operator_ae_matrixFullAmplitudeOperator hn R b hb hs B hB g hg
      (fun j ↦ ((contDiff_piLp 2).mp hgc j).of_le (by simp))
      (fun j ↦ hgs.comp_left (g := fun v : EuclideanSpace ℂ (Fin n) ↦ v j) rfl)] with x hm hk
  rw [hm, hk]
  apply PiLp.ext
  intro i
  change β x • matrixFullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y))
    (fun y j ↦ g y j) x i =
      matrixFullAmplitudeOperator (fun x y ξ ↦ restrictAmplitude b β ξ (pairedPosition x y))
        (fun y j ↦ f y j) x i
  rw [matrixFullAmplitudeOperator_restrictAmplitude]
  congr 1

end JanetCartan.ContinuumRow.CommonMeasurement
