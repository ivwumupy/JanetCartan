module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalTailRealization.RawNormal
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.NativeComparison
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalChange.RawReferenceBounds

/-!
# The balanced native reference on the original raw cutoff

For `main:eq:linear-two-errors`, the native-prefix producer identifies the
same original continuum carrier family. The sampling Fourier factor cancels
before the auxiliary and carrier normals are reassembled on the augmented
row. The carrier plateau is `c*K`; both auxiliary cutoffs remain `K`.
No reference-operator identity or raw-tail estimate is a hypothesis.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.CanonicalTailRealization
open ContinuumRow Sampling Sampling.Realization SamplingKernelBounds RawInputPartition
open RawCutoffBounds PeriodicLocalL2 AmplitudeBound SeparatedSampling
open CanonicalRowComparison AuxiliaryRawBand

variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I] {n N bands p : ℕ}
    (d : A → CarrierData n N)
    (ηb : A → I → Euclidean (n - 1)) (radius : A → I → ℝ)
    (hηb : ∀ a i, ηb a i ≠ 0) (hradius : ∀ a i, 0 < radius a i)
    (D₀ : A → BandKernelData (Fin bands × Point) n)
    (hfloor : ∀ a η, ‖η‖ ≤ 1 → (D₀ a).mask η = 0)
    (ψ : A → Point → ℝ) {B : ℝ} {P : A → ℝ}
    (hψ : ∀ a, PatchBounds (ψ a) B (P a)) (hc : ∀ a, Continuous (ψ a))
    (bump : A → I → Point → ℝ) (hbump : ∀ a i z, bump a i z ∈ Icc (0 : ℝ) 1)
    (hbc : ∀ a i, Continuous (bump a i))
    (hcover : ∀ a z, ψ a z ≠ 0 → ∀ η, (D₀ a).mask η ≠ 0 → ∃ i, bump a i z = 1 ∧
      NormedSpace.normalize η ∈ Metric.ball (NormedSpace.normalize (ηb a i))
        (CanonicalConic.angularWidth (ηb a i) (radius a i) / 4))
    (hDzero : ∀ a (j : Fin bands) z η, η ∉ wideBand n j.val →
      ∀ x, (D₀ a).kernel (j, z) η x = 0)
    (hkernel : ∀ a (j : Fin bands) x u,
      ((2 * Real.pi) ^ (-(n : ℝ) / 2) * carrierBand n j.val u) • carrierKernel (d a) x u =
        Real.sqrt (ψ a (carrierSamplingEquiv u.1)) •
          (D₀ a).kernel (j, carrierSamplingEquiv u.1) u.2 (centeredTorusRepresentative x))
    (hhigh : ∀ a t, t ≤ 1 → (d a).highCutoff t = 0)
    (U : A → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ a q, (U a).adjoint q =ᵐ[carrierMeasure n] carrierAdjointIntegral (d a) q)

/-- The actual balanced native reference in the raw-integral Fourier
convention, retaining the given image/exterior auxiliary normal and every
original grouped band (`app:ch_mean_pairs:eq:mean-normal-comparison`). -/
def balancedNativeReference
    (coeff : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψext : C(Torus n, ℝ)) {K : ℝ} (hK : 1 ≤ K) (c : ℝ) :
    OutputL2 n →L[ℝ] OutputL2 n :=
  cutAuxiliaryNormal coeff χmeas χsrc ψext hK +
    (((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹) ^ 2 • transferOperator
      ((4 : ℝ) • realOutputCompression
        (∑ label : A × ((s : Finset I) × s), ∫ z : Point,
          balancedCarrierSubsetWeight (ψ label.1) (bump label.1) label.2.1 z • atomNormal
            (Real.sqrt label.2.1.card • refinedKernelPrefix
              (jointSubsetKernel (ηb label.1) (radius label.1) (hηb label.1) (hradius label.1)
                (D₀ label.1) (hfloor label.1) label.2.1 label.2.2) (cutoffCount (c * K)) z)))

include hψ hc hbump hbc hcover hDzero hkernel hhigh hU in
/-- The Fourier normalization cancels on the original carrier normal
produced by the SAME balanced native kernels. Both auxiliary cutoffs remain
unchanged (`main:eq:linear-two-errors`). -/
theorem balancedNativeReference_eq_originalNormal
    (coeff : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψext : C(Torus n, ℝ)) {K : ℝ} (hK : 1 ≤ K) (c : ℝ)
    (hL : cutoffCount (c * K) ≤ bands) :
    balancedNativeReference ηb radius hηb hradius D₀ hfloor ψ bump coeff χmeas χsrc ψext hK c =
      cutAuxiliaryNormal coeff χmeas χsrc ψext hK + ∑ a,
        (carrierChannel (U a)).comp ((carrierSquaredCutoff (roundedCarrierMask n (c * K))).comp
          (carrierChannel (U a)).adjoint) := by
  rw [balancedNativeReference, family_balancedNativePrefix_normal_eq_original d ηb radius
    hηb hradius D₀ hfloor ψ hψ hc bump hbump hbc hcover hDzero hkernel hhigh U hU (c * K) hL]
  have hnz : (2 * Real.pi) ^ (-(n : ℝ) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos (by positivity : 0 < 2 * Real.pi) _).ne'
  rw [smul_smul, ← mul_pow, inv_mul_cancel₀ hnz, one_pow, one_smul]

include hψ hc hbump hbc hcover hDzero hkernel hhigh hU in
/-- The native balanced reference is exactly the squared raw cutoff on the
ORIGINAL augmented row. Both auxiliary cutoffs are `K` and the carrier mask
is the rounded mask at `c*K`. The normalization cancels using the proved
native-prefix identity (`main:eq:linear-two-errors`). -/
theorem balancedNativeReference_eq_rawSquaredCutoff
    (coeff : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψext : C(Torus n, ℝ)) {K : ℝ} (hK : 1 ≤ K) (c : ℝ)
    (hL : cutoffCount (c * K) ≤ bands) :
    balancedNativeReference ηb radius hηb hradius D₀ hfloor ψ bump coeff χmeas χsrc ψext hK c =
      (augmentedRow (imageChannel coeff χmeas χsrc) U ψext).comp
        ((rawSquaredCutoffCLM hK (fun _ ↦ roundedCarrierMask n (c * K))).comp
          (augmentedRow (imageChannel coeff χmeas χsrc) U ψext).adjoint) := by
  rw [balancedNativeReference_eq_originalNormal d ηb radius hηb hradius D₀ hfloor
    ψ hψ hc bump hbump hbc hcover hDzero hkernel hhigh U hU coeff χmeas χsrc ψext hK c hL]
  rw [← cutAuxiliaryNormal_add_cutCarrierNormals_eq_rawSquaredCutoff]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  ext1 q
  exact (cutCarrier_normal_apply (U a) (roundedCarrierMask n (c * K)) q).symm

include hψ hc hbump hbc hcover hDzero hkernel hhigh hU

/-- The exact application form consumed by the original-band recurrence's
`hreferenceEq`. It follows from the native kernel producer; no new reference
identification is assumed (`main:lem:mean-recurrence`). -/
theorem balancedNativeReference_apply
    (coeff : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψext : C(Torus n, ℝ)) {K : ℝ} (hK : 1 ≤ K) (c : ℝ)
    (hL : cutoffCount (c * K) ≤ bands) (q : OutputL2 n) :
    balancedNativeReference ηb radius hηb hradius D₀ hfloor ψ bump coeff χmeas χsrc ψext hK c q =
      augmentedRow (imageChannel coeff χmeas χsrc) U ψext
        (rawSquaredCutoff K (fun _ ↦ roundedCarrierMask n (c * K))
          ((augmentedRow (imageChannel coeff χmeas χsrc) U ψext).adjoint q)) := by
  rw [balancedNativeReference_eq_rawSquaredCutoff d ηb radius hηb hradius D₀ hfloor
    ψ hψ hc bump hbump hbc hcover hDzero hkernel hhigh U hU coeff χmeas χsrc ψext hK c hL]
  rfl

/-- The actual native reference has the original row's squared norm bound.
The raw-mask contractivity is proved from the constructed rounded masks
(`main:prop:canonical`, `main:lem:mean-recurrence`). -/
theorem norm_balancedNativeReference_le
    (coeff : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψext : C(Torus n, ℝ)) {K : ℝ} (hK : 1 ≤ K) (c : ℝ)
    (hL : cutoffCount (c * K) ≤ bands) :
    ‖balancedNativeReference ηb radius hηb hradius D₀ hfloor ψ bump
      coeff χmeas χsrc ψext hK c‖ ≤
        ‖augmentedRow (imageChannel coeff χmeas χsrc) U ψext‖ ^ 2 := by
  rw [balancedNativeReference_eq_rawSquaredCutoff d ηb radius hηb hradius D₀ hfloor
    ψ hψ hc bump hbump hbc hcover hDzero hkernel hhigh U hU coeff χmeas χsrc ψext hK c hL]
  exact CanonicalChange.norm_rawReferenceNormal_le_rowNorm_sq _ hK _
    (fun _ ↦ roundedCarrierMask_mem n (c * K))

/-- Apply the actual original inverse to the balanced native reference, with
carrier plateau `c*K` and both auxiliary cutoffs `K`. The ONLY remaining
domain input is regularity of this SAME raw adjoint-inverse datum
(`main:eq:linear-two-errors`). -/
theorem balancedNativeReference_inverse_error_le_raw_norm
    (coeff : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψext : C(Torus n, ℝ)) {γ c K : ℝ} (hγ : 0 < γ)
    (hgap : ∀ q, γ * ‖q‖ ^ 2 ≤
      ‖(augmentedRow (imageChannel coeff χmeas χsrc) U ψext).adjoint q‖ ^ 2)
    (hcpos : 0 < c) (hK : 1 ≤ K) (hcK : 1 ≤ c * K)
    (hL : cutoffCount (c * K) ≤ bands) {s : ℕ} (r : OutputL2 n)
    (hmem : CoerciveInverse.rightInverse
      (augmentedRow (imageChannel coeff χmeas χsrc) U ψext) r ∈
        (CarrierSobolev.augmentedInputSobolevScale n A).level s) :
    let A₀ := augmentedRow (imageChannel coeff χmeas χsrc) U ψext
    ‖r - balancedNativeReference ηb radius hηb hradius D₀ hfloor ψ bump
      coeff χmeas χsrc ψext hK c ((CoerciveInverse.normalOperator A₀).inverse r)‖ ≤
      (‖A₀‖ * max 1 (c ^ (-(s : ℝ)))) * K ^ (-(s : ℝ)) *
        (CarrierSobolev.augmentedInputSobolevScale n A).gradeNorm s
          (CoerciveInverse.rightInverse A₀ r) := by
  dsimp only
  rw [balancedNativeReference_apply d ηb radius hηb hradius D₀ hfloor
    ψ hψ hc bump hbump hbc hcover hDzero hkernel hhigh U hU coeff χmeas χsrc ψext hK c hL]
  exact reference_error_scaled_rounded_le_raw_norm _ hγ hgap hcpos hK hcK r hmem

/-- The actual balanced native reference satisfies the one-high tail bound
on the same original inverse. The exact plateau loss `max 1 (c^(-s))` is
retained for the recurrence threshold (`main:lem:mean-recurrence`). -/
theorem balancedNativeReference_inverse_error_le_one_high
    (G : GradedScale (OutputL2 n))
    (coeff : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψext : C(Torus n, ℝ)) {γ c K : ℝ} (hγ : 0 < γ)
    (hgap : ∀ q, γ * ‖q‖ ^ 2 ≤
      ‖(augmentedRow (imageChannel coeff χmeas χsrc) U ψext).adjoint q‖ ^ 2)
    (hcpos : 0 < c) (hK : 1 ≤ K) (hcK : 1 ≤ c * K)
    (hL : cutoffCount (c * K) ≤ bands) {s : ℕ} (r : OutputL2 n)
    {dInv k T : ℝ} (hk : 0 ≤ k) (hT : 0 ≤ T)
    (hinvmem : (CoerciveInverse.normalOperator
      (augmentedRow (imageChannel coeff χmeas χsrc) U ψext)).inverse r ∈ G.level s)
    (hinv : G.gradeNorm s ((CoerciveInverse.normalOperator
      (augmentedRow (imageChannel coeff χmeas χsrc) U ψext)).inverse r) ≤
        dInv * (G.gradeNorm s r + T ^ s * ‖r‖))
    (hraw : ∀ v, v ∈ G.level s →
      (augmentedRow (imageChannel coeff χmeas χsrc) U ψext).adjoint v ∈
        (CarrierSobolev.augmentedInputSobolevScale n A).level s ∧
      (CarrierSobolev.augmentedInputSobolevScale n A).gradeNorm s
        ((augmentedRow (imageChannel coeff χmeas χsrc) U ψext).adjoint v) ≤
          k * (G.gradeNorm s v + T ^ s * ‖v‖)) :
    let A₀ := augmentedRow (imageChannel coeff χmeas χsrc) U ψext
    ‖r - balancedNativeReference ηb radius hηb hradius D₀ hfloor ψ bump
      coeff χmeas χsrc ψext hK c ((CoerciveInverse.normalOperator A₀).inverse r)‖ ≤
      (‖A₀‖ * max 1 (c ^ (-(s : ℝ))) * (k * (dInv + γ⁻¹))) *
        K ^ (-(s : ℝ)) * (G.gradeNorm s r + T ^ s * ‖r‖) := by
  dsimp only
  rw [balancedNativeReference_apply d ηb radius hηb hradius D₀ hfloor
    ψ hψ hc bump hbump hbc hcover hDzero hkernel hhigh U hU coeff χmeas χsrc ψext hK c hL]
  exact reference_error_scaled_rounded_le_one_high G _ hγ hgap hcpos hK hcK r
    hk hT hinvmem hinv hraw

end JanetCartan.CanonicalTailRealization
