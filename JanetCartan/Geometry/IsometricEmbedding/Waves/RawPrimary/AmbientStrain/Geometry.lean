module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.StrainIdentity
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.ComplexWKB.Operator

/-!
# The actual geometric half-strain identity

Convert the projected normal-kernel basis into the ambient tensor frame used
by the response reconstruction. Apply its proved geometric strain identity
to both quadratures of the actual reduced operator. The consumer is the
full primary atom in `app:ch_waves:eq:WKB-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
open Set
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.RawPrimary
open StressFrame ProjectedStressFrame ResponseTransfer NullTransport

/-- The basis produced by `exists_projectedStress_basis_of_cNorm_closeness`
is independent and spanning in the ambient Frobenius tensor space, as needed
for `app:ch_waves:eq:exact-half-strain`. -/
theorem projectedStress_tensorFrame_of_kernel_basis {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x : Euclidean n}
    (hbasis : ∃ b : Module.Basis (Fin n) ℝ (StressFrame.symmetricNormalMap F x).ker,
      ∀ i, ((b i : SymmetricTensor n) : MetricTensor n) = projectedStress F x i) :
    LinearIndependent ℝ (projectedStress F x) ∧
      (Submodule.span ℝ (range (projectedStress F x)) : Set (MetricTensor n)) =
        stressSpace F x := by
  obtain ⟨b, hb⟩ := hbasis
  let L : (StressFrame.symmetricNormalMap F x).ker →ₗ[ℝ] MetricTensor n :=
    (symmetricTensorSubmodule n).subtype.comp (StressFrame.symmetricNormalMap F x).ker.subtype
  have hLb : L ∘ b = projectedStress F x := funext hb
  have hind := b.linearIndependent
  refine ⟨?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    apply (Fintype.linearIndependent_iff (v := fun i : Fin n ↦ b i)).mp hind c
    apply Subtype.ext
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul, ZeroMemClass.coe_zero, hb] using hc
  · have hs := congrArg (Submodule.map L) b.span_eq
    rw [Submodule.map_span, ← range_comp, hLb, Submodule.map_top] at hs
    rw [hs]
    ext H
    constructor
    · rintro ⟨v, rfl⟩
      exact (mem_symmetricNormalMap_ker F x v.val).mp v.property
    · intro hH
      let S : SymmetricTensor n := ⟨H, hH.1⟩
      exact ⟨⟨S, (mem_symmetricNormalMap_ker F x S).mpr hH⟩, rfl⟩

/-- The precise `C⁶` frame threshold selected by the geometric producer.
The common raw-family neighborhood must be intersected with this threshold
before choosing its single reference (`app:ch_waves:eq:WKB-residual`). -/
def ambientStrainFrameThreshold {n : ℕ} (hn : 5 ≤ n) : ℝ :=
  Classical.choose (exists_projectedStress_basis_of_cNorm_closeness hn)

/-- Positivity of the retained frame threshold for
`app:ch_waves:eq:exact-half-strain`. -/
theorem ambientStrainFrameThreshold_pos {n : ℕ} (hn : 5 ≤ n) :
    0 < ambientStrainFrameThreshold hn :=
  (Classical.choose_spec (exists_projectedStress_basis_of_cNorm_closeness hn)).1

/-- The Gram gap belonging to the SAME frame threshold, for the inverse-Gram
multiplier in `app:ch_waves:eq:WKB-residual`. -/
def ambientStrainFrameGramGap {n : ℕ} (hn : 5 ≤ n) : ℝ :=
  Classical.choose
    (Classical.choose_spec (exists_projectedStress_basis_of_cNorm_closeness hn)).2

/-- The retained Gram gap is positive (`app:ch_waves:eq:WKB-strain`). -/
theorem ambientStrainFrameGramGap_pos {n : ℕ} (hn : 5 ≤ n) :
    0 < ambientStrainFrameGramGap hn :=
  (Classical.choose_spec
    (Classical.choose_spec (exists_projectedStress_basis_of_cNorm_closeness hn)).2).1

/-- The SAME projected frame and threshold give a uniform quantitative Gram
gap. This is the low inverse input for `app:ch_waves:eq:WKB-strain`; independence
alone would not supply a uniform inverse bound. -/
theorem projectedStress_gram_energy_of_cNorm_closeness {n : ℕ} (hn : 5 ≤ n)
    {F : Euclidean n → Euclidean (embeddingDimension n)}
    {s K : Set (Euclidean n)} (hs : IsOpen s) (hK : IsCompact K) (hKs : K ⊆ s)
    (hF : ContDiffOn ℝ ∞ F s) (hi : IsImmersionOn F s)
    (hrank : HasFullNormalRankOn F s)
    (hclose : ∀ i, cNorm K 6 (fun x ↦ projectedStress F x i - cubeStress n i) <
      ambientStrainFrameThreshold hn)
    {x : Euclidean n} (hx : x ∈ K) (c : Euclidean n) :
    ambientStrainFrameGramGap hn * (∑ i, (c i)^2) ≤
      ∑ i, ∑ j, c i * c j * WKB.stressGram (projectedStress F x) i j :=
  ((Classical.choose_spec
    (Classical.choose_spec (exists_projectedStress_basis_of_cNorm_closeness hn)).2).2
      F s K hs hK hKs hF hi hrank hclose x hx).2 c

/-- Closeness on the parent's actual compact construction set gives every
frame hypothesis of the complex strain transfer. No independent frame is
chosen (`app:ch_waves:eq:exact-half-strain`). -/
theorem projectedStress_tensorFrame_of_cNorm_closeness {n : ℕ} (hn : 5 ≤ n)
    {F : Euclidean n → Euclidean (embeddingDimension n)}
    {s K : Set (Euclidean n)} (hs : IsOpen s) (hK : IsCompact K) (hKs : K ⊆ s)
    (hF : ContDiffOn ℝ ∞ F s) (hi : IsImmersionOn F s)
    (hrank : HasFullNormalRankOn F s)
    (hclose : ∀ i, cNorm K 6 (fun x ↦ projectedStress F x i - cubeStress n i) <
      ambientStrainFrameThreshold hn)
    {x : Euclidean n} (hx : x ∈ K) :
    (∀ i, (projectedStress F x i).IsSymm) ∧
      LinearIndependent ℝ (projectedStress F x) ∧
      (Submodule.span ℝ (range (projectedStress F x)) : Set (MetricTensor n)) =
        stressSpace F x := by
  obtain ⟨γ, _, hframe⟩ :=
    (Classical.choose_spec (exists_projectedStress_basis_of_cNorm_closeness hn)).2
  have hb := (hframe F s K hs hK hKs hF hi hrank hclose x hx).1
  refine ⟨?_, projectedStress_tensorFrame_of_kernel_basis hb⟩
  obtain ⟨b, hb⟩ := hb
  intro i
  rw [← hb i]
  exact (b i).val.property

/-- The actual complex zero-source reconstruction has twice the inverse-Gram
reconstruction of its full covariant reduced operator. The geometric identity
and differentiability of both real quadratures are derived, not assumed
(`app:ch_waves:eq:exact-half-strain`). -/
theorem completedVariationComplex_zero_strain_eq_reconstruction {n N : ℕ}
    {F : Euclidean n → Euclidean N}
    {u : Euclidean n → EuclideanSpace ℂ (Fin n)}
    {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (hu : ContDiffOn ℝ ∞ u s)
    (hi : IsImmersionOn F s) (hrank : HasFullNormalRankOn F s)
    {x : Euclidean n} (hx : x ∈ s)
    (Q : Euclidean n → Fin n → MetricTensor n)
    (hQsym : ∀ i, (Q x i).IsSymm)
    (hQ : LinearIndependent ℝ (Q x))
    (hspan : (Submodule.span ℝ (range (Q x)) : Set (MetricTensor n)) = stressSpace F x) :
    WKB.complexLinearizedMetric F (completedVariationComplex F u 0) x =
      (2 : ℂ) • WKB.stressReconstruction (Q x)
        (fun i ↦ complexReducedOperator F Q u x i) := by
  have hud := (hu.contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)
  have he := completedVariationComplex_error_eq_full_residual (h := 0) hs hF hu hi hrank
    (contDiffOn_const (c := (0 : Matrix (Fin n) (Fin n) ℂ))) hx
    (show (0 : Matrix (Fin n) (Fin n) ℂ).IsSymm by simp [Matrix.IsSymm]) hQ hspan
    (fun y i ↦ -complexReducedOperator F Q u y i) 0
    (fun i ↦ by
      simpa [reducedOperator, tensorPairing] using
        (complexReducedOperator_re F Q hQsym hud i).symm)
    (fun i ↦ by
      simpa [reducedOperator, tensorPairing] using
        (complexReducedOperator_im F Q hQsym hud i).symm)
  simp only [Pi.zero_apply, sub_zero, LinearMap.zero_apply, zero_sub, neg_neg] at he
  convert he using 1

end JanetCartan.RawPrimary
