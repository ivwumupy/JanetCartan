module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalTailRealization.NativeReference
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalChange.WholeSourceComponent

/-!
# The balanced raw-integral sample and the original inverse

The raw-integral components are precisely the continuous operators identified
by `CanonicalChange.smoothRawCrossOperator_wholeSource_eq_rawIntegral_component`.
Apply the SAME balanced event and native-prefix identity before estimating the
complete linear error. The finite sample, original inverse and residual stay
fixed, and the carrier cutoff `c*K` never replaces either auxiliary cutoff `K`.

The supplied event and colored transport estimates are the outputs required
from `both-sampling` and `both-canonical-row-comparison`. The actual same-row
inverse profiles remain with `both-continuum-inverse`. No component or reference
operator equality is an input (`main:eq:linear-two-errors`).
-/

set_option maxHeartbeats 800000
@[expose] public noncomputable section
open Set MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.CanonicalTailRealization
open ContinuumRow Sampling Sampling.Realization SamplingKernelBounds RawInputPartition
open RawCutoffBounds PeriodicLocalL2 AmplitudeBound SeparatedSampling
open CanonicalRowComparison AuxiliaryRawBand CurrentMean

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

variable (w : ℝ → ℝ) {W h : ℝ} (hw : WindowBounds p w W) (hh : 0 ≤ h)
    (ξ : A × ((s : Finset I) × s) → ShiftSpace p B h)
    (D : A × ((s : Finset I) × s) →
      BandKernelData (Fin bands × ((Fin 3 → Fin (p + 1)) × Point)) n)
    (coeff : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψext : C(Torus n, ℝ))
    {K carrierPlateau : ℝ} (hK : 1 ≤ K) (hL : cutoffCount (carrierPlateau * K) ≤ bands)
    {samplingError transportError : ℝ}
    (hevent : ‖familyDeviation p B
      (fun c : A × ((s : Finset I) × s) ↦
        balancedCarrierSubsetWeight (ψ c.1) (bump c.1) c.2.1) w h
      (fun c color z ↦ refinedKernelPrefix (D c) (cutoffCount (carrierPlateau * K)) (color, z)) ξ‖ ≤
        samplingError)
    (htransport : ‖(∑ c : A × ((s : Finset I) × s),
      patchMeanNormal p B (balancedCarrierSubsetWeight (ψ c.1) (bump c.1) c.2.1) w h
        (fun color z ↦ refinedKernelPrefix (D c) (cutoffCount (carrierPlateau * K)) (color, z))) -
      (∑ c : A × ((s : Finset I) × s), ∫ z : Point,
        balancedCarrierSubsetWeight (ψ c.1) (bump c.1) c.2.1 z • atomNormal
          (Real.sqrt c.2.1.card • refinedKernelPrefix
            (jointSubsetKernel (ηb c.1) (radius c.1) (hηb c.1) (hradius c.1)
              (D₀ c.1) (hfloor c.1) c.2.1 c.2.2) (cutoffCount (carrierPlateau * K)) z))‖ ≤ transportError)

include hψ hc hbump hbc hcover hDzero hkernel hhigh hU hw hh hevent htransport hL

/-- The complete actual raw-integral normal is close to the identified native
reference, for the SAME shifts and every grouped prefix. The unchanged image
and exterior outputs use cutoff `K`; only carriers use `c*K`
(`app:ch_mean_pairs:eq:mean-normal-comparison`). -/
theorem balancedNative_completeCanonicalNormal_sub_reference_le :
    let weights := fun label : A × ((s : Finset I) × s) ↦
      balancedCarrierSubsetWeight (ψ label.1) (bump label.1) label.2.1
    let μ := sampleWeight (p := p) B weights w h (fun label ↦ extendedShift (ξ label))
    let component := rawIntegralSampledComponent B weights w h (fun label ↦ extendedShift (ξ label))
      (fun label color z ↦ refinedKernelPrefix (D label) (cutoffCount (carrierPlateau * K)) (color, z))
    ‖completeCanonicalNormal coeff χmeas χsrc ψext μ component hK -
      balancedNativeReference ηb radius hηb hradius D₀ hfloor ψ bump coeff χmeas χsrc ψext hK carrierPlateau‖ ≤
      (((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹) ^ 2 * (4 * (samplingError + transportError)) := by
  dsimp only
  rw [balancedNativeReference_eq_originalNormal d ηb radius hηb hradius D₀ hfloor
    ψ hψ hc bump hbump hbc hcover hDzero hkernel hhigh U hU coeff χmeas χsrc ψext hK carrierPlateau hL]
  exact balancedNative_rawIntegral_normal_sub_original_le d ηb radius hηb hradius D₀ hfloor
    ψ hψ hc bump hbump hbc hcover hDzero hkernel hhigh U hU w hw hh ξ D
    (cutAuxiliaryNormal coeff χmeas χsrc ψext hK) (carrierPlateau * K) hL hevent htransport

/-- The linear error splits into the SAME sampled-reference comparison and
original raw tail. Inverse regularity and raw-adjoint profiles are the named
continuum producer's quantitative inputs. The exact plateau loss remains
visible and no finite sampled operator is inverted
(`main:eq:linear-two-errors`, `main:lem:mean-recurrence`). -/
theorem balancedNative_rawIntegral_inverse_error_le_one_high
    (G : GradedScale (OutputL2 n)) {γ : ℝ} (hγ : 0 < γ)
    (hgap : ∀ q, γ * ‖q‖ ^ 2 ≤
      ‖(augmentedRow (imageChannel coeff χmeas χsrc) U ψext).adjoint q‖ ^ 2)
    (hcpos : 0 < carrierPlateau) (hcK : 1 ≤ carrierPlateau * K) {s : ℕ} {dInv k T : ℝ}
    (hk : 0 ≤ k) (hT : 0 ≤ T) (r : OutputL2 n)
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
    let weights := fun label : A × ((s : Finset I) × s) ↦
      balancedCarrierSubsetWeight (ψ label.1) (bump label.1) label.2.1
    let μ := sampleWeight (p := p) B weights w h (fun label ↦ extendedShift (ξ label))
    let component := rawIntegralSampledComponent B weights w h (fun label ↦ extendedShift (ξ label))
      (fun label color z ↦ refinedKernelPrefix (D label) (cutoffCount (carrierPlateau * K)) (color, z))
    let A₀ := augmentedRow (imageChannel coeff χmeas χsrc) U ψext
    ‖r - completeCanonicalNormal coeff χmeas χsrc ψext μ component hK
      ((CoerciveInverse.normalOperator A₀).inverse r)‖ ≤
      ((((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹) ^ 2 *
        (4 * (samplingError + transportError))) * γ⁻¹ * ‖r‖ +
      (‖A₀‖ * max 1 (carrierPlateau ^ (-(s : ℝ))) * (k * (dInv + γ⁻¹))) *
        K ^ (-(s : ℝ)) * (G.gradeNorm s r + T ^ s * ‖r‖) := by
  dsimp only
  let A₀ := augmentedRow (imageChannel coeff χmeas χsrc) U ψext
  let Q₀ := (CoerciveInverse.normalOperator A₀).inverse
  let E₀ := balancedNativeReference ηb radius hηb hradius D₀ hfloor ψ bump
    coeff χmeas χsrc ψext hK carrierPlateau
  let weights := fun label : A × ((s : Finset I) × s) ↦
    balancedCarrierSubsetWeight (ψ label.1) (bump label.1) label.2.1
  let μ := sampleWeight (p := p) B weights w h (fun label ↦ extendedShift (ξ label))
  let component := rawIntegralSampledComponent B weights w h (fun label ↦ extendedShift (ξ label))
    (fun label color z ↦ refinedKernelPrefix (D label) (cutoffCount (carrierPlateau * K)) (color, z))
  let E := completeCanonicalNormal coeff χmeas χsrc ψext μ component hK
  let δ := (((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹) ^ 2 * (4 * (samplingError + transportError))
  have hcomparison : ‖E - E₀‖ ≤ δ :=
    balancedNative_completeCanonicalNormal_sub_reference_le d ηb radius hηb hradius D₀ hfloor
      ψ hψ hc bump hbump hbc hcover hDzero hkernel hhigh U hU w hw hh ξ D
      coeff χmeas χsrc ψext hK hL hevent htransport
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hcomparison
  have htail := balancedNativeReference_inverse_error_le_one_high d ηb radius hηb hradius D₀ hfloor
    ψ hψ hc bump hbump hbc hcover hDzero hkernel hhigh U hU G coeff χmeas χsrc ψext
    hγ hgap hcpos hK hcK hL r hk hT hinvmem hinv hraw
  have hQ := CoerciveInverse.norm_inverse_apply_le (CoerciveInverse.normalOperator A₀)
    hγ (CoerciveInverse.normalOperator_gap A₀ hgap) r
  change ‖r - E (Q₀ r)‖ ≤ _
  calc
    _ ≤ ‖(E₀ - E) (Q₀ r)‖ + ‖r - E₀ (Q₀ r)‖ := by
      have he : r - E (Q₀ r) = (E₀ - E) (Q₀ r) + (r - E₀ (Q₀ r)) := by
        simp only [sub_apply]
        abel
      rw [he]
      exact norm_add_le _ _
    _ ≤ δ * γ⁻¹ * ‖r‖ +
        (‖A₀‖ * max 1 (carrierPlateau ^ (-(s : ℝ))) * (k * (dInv + γ⁻¹))) *
          K ^ (-(s : ℝ)) * (G.gradeNorm s r + T ^ s * ‖r‖) := by
      apply add_le_add _ htail
      calc
        _ ≤ ‖E₀ - E‖ * ‖Q₀ r‖ := (E₀ - E).le_opNorm _
        _ ≤ δ * (γ⁻¹ * ‖r‖) :=
          mul_le_mul (by rwa [norm_sub_rev]) hQ (norm_nonneg _) hδ
        _ = _ := by ring

omit hevent htransport hL hw hh in
/-- For every retained recurrence prefix, the reference-identification
premise of `CurrentMean.exists_admissible_history_canonicalRawTail_bound`
is discharged on the SAME native family. The cutoff sequence and continuum
row are fixed before the update index (`main:lem:mean-recurrence`). -/
theorem balancedNative_allPrefix_reference_apply
    (cutoffs : ℕ → ℝ) (hcutoffs : ∀ l, 1 ≤ cutoffs l) (steps : ℕ)
    (hceilings : ∀ l < steps, cutoffCount (carrierPlateau * cutoffs l) ≤ bands) :
    ∀ l < steps, ∀ q : OutputL2 n,
      balancedNativeReference ηb radius hηb hradius D₀ hfloor ψ bump
        coeff χmeas χsrc ψext (hcutoffs l) carrierPlateau q =
      augmentedRow (imageChannel coeff χmeas χsrc) U ψext
        (rawSquaredCutoff (cutoffs l)
          (fun _ ↦ roundedCarrierMask n (carrierPlateau * cutoffs l))
          ((augmentedRow (imageChannel coeff χmeas χsrc) U ψext).adjoint q)) := by
  intro l hl q
  exact balancedNativeReference_apply d ηb radius hηb hradius D₀ hfloor ψ hψ hc
    bump hbump hbc hcover hDzero hkernel hhigh U hU coeff χmeas χsrc ψext
    (hcutoffs l) carrierPlateau (hceilings l hl) q

omit hevent htransport hL in
/-- The SAME event and raw-integral row supply all comparison premises of
`CurrentMean.exists_admissible_history_canonicalRawTail_bound`. No sample,
reference, row or inverse is selected after the varying prefix. The
whole-source component equality rewrites its smooth components to these
literal `rawIntegralSampledComponent`s
(`main:lem:mean-recurrence`, `app:ch_mean_pairs:eq:mean-normal-comparison`). -/
theorem balancedNative_allPrefix_completeCanonicalNormal_sub_reference_le
    (cutoffs : ℕ → ℝ) (hcutoffs : ∀ l, 1 ≤ cutoffs l) (steps : ℕ)
    (hceilings : ∀ l < steps, cutoffCount (carrierPlateau * cutoffs l) ≤ bands)
    (hevents : ∀ l < steps, ‖familyDeviation p B
      (fun label : A × ((s : Finset I) × s) ↦
        balancedCarrierSubsetWeight (ψ label.1) (bump label.1) label.2.1) w h
      (fun label color z ↦ refinedKernelPrefix (D label)
        (cutoffCount (carrierPlateau * cutoffs l)) (color, z)) ξ‖ ≤ samplingError)
    (htransports : ∀ l < steps, ‖(∑ label : A × ((s : Finset I) × s),
      patchMeanNormal p B (balancedCarrierSubsetWeight (ψ label.1) (bump label.1) label.2.1) w h
        (fun color z ↦ refinedKernelPrefix (D label)
          (cutoffCount (carrierPlateau * cutoffs l)) (color, z))) -
      (∑ label : A × ((s : Finset I) × s), ∫ z : Point,
        balancedCarrierSubsetWeight (ψ label.1) (bump label.1) label.2.1 z • atomNormal
          (Real.sqrt label.2.1.card • refinedKernelPrefix
            (jointSubsetKernel (ηb label.1) (radius label.1) (hηb label.1) (hradius label.1)
              (D₀ label.1) (hfloor label.1) label.2.1 label.2.2)
                (cutoffCount (carrierPlateau * cutoffs l)) z))‖ ≤ transportError) :
    let weights := fun label : A × ((s : Finset I) × s) ↦
      balancedCarrierSubsetWeight (ψ label.1) (bump label.1) label.2.1
    let μ := sampleWeight (p := p) B weights w h (fun label ↦ extendedShift (ξ label))
    ∀ l < steps,
      ‖completeCanonicalNormal coeff χmeas χsrc ψext μ
        (rawIntegralSampledComponent B weights w h (fun label ↦ extendedShift (ξ label))
          (fun label color z ↦ refinedKernelPrefix (D label)
            (cutoffCount (carrierPlateau * cutoffs l)) (color, z))) (hcutoffs l) -
        balancedNativeReference ηb radius hηb hradius D₀ hfloor ψ bump
          coeff χmeas χsrc ψext (hcutoffs l) carrierPlateau‖ ≤
      (((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹) ^ 2 * (4 * (samplingError + transportError)) := by
  dsimp only
  intro l hl
  exact balancedNative_completeCanonicalNormal_sub_reference_le d ηb radius hηb hradius D₀ hfloor
    ψ hψ hc bump hbump hbc hcover hDzero hkernel hhigh U hU w hw hh ξ D
    coeff χmeas χsrc ψext (hcutoffs l) (hceilings l hl) (hevents l hl) (htransports l hl)

end JanetCartan.CanonicalTailRealization
