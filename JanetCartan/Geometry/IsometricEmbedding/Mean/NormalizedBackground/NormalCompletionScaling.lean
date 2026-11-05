module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Scaling
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Completion
public import JanetCartan.Geometry.IsometricEmbedding.Normal.RankStability.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.Reconstruction
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.CompactFamily

/-!
# Scaling canonical normal completion and the principal normal family

The normal-completion and principal-normal identities in
`app:ch_background:eq:bg-Nsigma`, for the source dilation in `main:eq:normalized`.
The proof uses the actual geometric normal equation and its uniqueness, not an
assumed inverse family. Full normal rank is required only at the corresponding
positive-scale point of the unscaled reference.

For `app:ch_background:prop:bg-normalized`, smooth covector and amplitude fields
on an explicit space/carrier domain give a jointly smooth normalized pullback.
It agrees with the actual principal normal for the amplitude scaled by `σ` and
has a spatially constant zero slice. Only this pullback is extended to zero;
no rank assertion is made about `sourceDilation F 0`.

The leading-wave producer must supply the smooth covector and amplitude fields
and identify the transported data with their indicated pullbacks. The consumer
`Mean.NormalizedBackground` must instantiate these hypotheses and the domain
containment; this module does not construct a phase or a null transport.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
open scoped JanetCartan.NormalRankStability JanetCartan.TensorFrobenius
open Set

namespace JanetCartan

namespace AmbientResponse

/-- `app:ch_background:eq:bg-Nsigma`: the canonical normal completion of the
actual source dilation scales by `σ⁻¹`. Uniqueness of the geometric normal
equation proves the identity; immersion is not needed for this pointwise step. -/
theorem smul_canonicalNormalCompletion_sourceDilation {n N : ℕ}
    {F : Euclidean n → Euclidean N} {σ : ℝ}
    (hσ : 0 < σ) (hF : ContDiff ℝ ∞ F) (x : Euclidean n)
    (hrank : Set.range (normalMap F (σ • x)) =
      (normalSpace F (σ • x) : Set (Euclidean N))) (H : MetricTensor n) :
    σ • canonicalNormalCompletion (sourceDilation F σ) x H =
      canonicalNormalCompletion F (σ • x) H := by
  have hrankσ : Set.range (normalMap (sourceDilation F σ) x) =
      (normalSpace (sourceDilation F σ) x : Set (Euclidean N)) := by
    rw [normalMap_sourceDilation_range hσ hF,
      normalSpace_sourceDilation hσ (hF.differentiable (by simp) _)]
    exact hrank
  let w := canonicalNormalCompletion (sourceDilation F σ) x H
  have hw : w ∈ normalSpace F (σ • x) := by
    rw [← normalSpace_sourceDilation hσ (hF.differentiable (by simp) _)]
    exact canonicalNormalCompletion_mem_normalSpace _ _ _
  have hpair : normalPairing (sourceDilation F σ) (fun _ ↦ w) x =
      normalPairing F (fun _ ↦ σ • w) (σ • x) := by
    ext i j
    simp [normalPairing, secondFundamentalForm_sourceDilation hσ hF,
      real_inner_smul_left, inner_smul_right]
  have heq := canonicalNormalCompletion_normal_equation hrankσ H
  change normalMap (sourceDilation F σ) x
    (normalPairing (sourceDilation F σ) (fun _ ↦ w) x) = _ at heq
  rw [normalMap_sourceDilation hσ hF, normalMap_sourceDilation hσ hF, hpair] at heq
  apply ambientNormalOperator_injective hrank
  rw [ambientNormalOperator_canonicalNormalCompletion hrank H,
    ambientNormalOperator_apply, tangentProjection_eq_zero_of_mem_normalSpace
      ((normalSpace F (σ • x)).smul_mem σ hw), add_zero]
  exact (smul_right_injective (M := Euclidean N) (ne_of_gt hσ)) heq

end AmbientResponse

namespace NormalizedBackground

open AmbientResponse LeadingWave

/-- `app:ch_background:eq:bg-Nsigma`: multiplying the amplitude by the source
scale cancels the inverse scale in the actual canonical principal normal. -/
theorem principalNormal_sourceDilation_scaled_amplitude {n N : ℕ}
    {F : Euclidean n → Euclidean N} {σ : ℝ}
    (hσ : 0 < σ) (hF : ContDiff ℝ ∞ F) (x : Euclidean n)
    (hrank : Set.range (normalMap F (σ • x)) =
      (normalSpace F (σ • x) : Set (Euclidean N))) (ξ b : Euclidean n) :
    principalNormal (canonicalNormalCompletion (sourceDilation F σ) x) ξ (σ • b) =
      principalNormal (canonicalNormalCompletion F (σ • x)) ξ b := by
  rw [principalNormal_smul]
  exact smul_canonicalNormalCompletion_sourceDilation hσ hF x hrank
    (symmetricProduct ξ b)

/-- `app:ch_background:eq:bg-Nsigma`: for explicit pulled-back covectors and
scaled pulled-back amplitudes, the principal normal is literally the regular
normalized pullback of the unscaled canonical principal-normal family. -/
theorem principalNormal_sourceDilation_eq_normalizedPullback {n N : ℕ} {Z : Type*}
    {F : Euclidean n → Euclidean N} {σ : ℝ}
    (ξ b : Euclidean n × Z → Euclidean n)
    (hσ : 0 < σ) (hF : ContDiff ℝ ∞ F) (x : Euclidean n) (z : Z)
    (hrank : Set.range (normalMap F (σ • x)) =
      (normalSpace F (σ • x) : Set (Euclidean N))) :
    principalNormal (canonicalNormalCompletion (sourceDilation F σ) x)
        (ξ (σ • x, z)) (σ • b (σ • x, z)) =
      normalizedPullback
        (fun p ↦ principalNormal (canonicalNormalCompletion F p.1) (ξ p) (b p))
        (σ, (x, z)) :=
  principalNormal_sourceDilation_scaled_amplitude hσ hF x hrank _ _

/-- `app:ch_background:prop:bg-normalized`: the unscaled canonical principal
normal is jointly smooth in space and carrier variables. The geometric domain
is open, and the coefficient domain explicitly projects into it. Smoothness is
derived from the actual canonical completion, not assumed for the output. -/
theorem contDiffOn_canonicalPrincipalNormal {n N : ℕ}
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : Euclidean n → Euclidean N} {s : Set (Euclidean n)}
    {U : Set (Euclidean n × Z)} {ξ b : Euclidean n × Z → Euclidean n}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s)
    (himm : IsImmersionOn F s) (hrank : HasFullNormalRankOn F s)
    (hU : MapsTo Prod.fst U s)
    (hξ : ContDiffOn ℝ ∞ ξ U) (hb : ContDiffOn ℝ ∞ b U) :
    ContDiffOn ℝ ∞ (fun p ↦ principalNormal (canonicalNormalCompletion F p.1)
      (ξ p) (b p)) U := by
  have hL : ContDiffOn ℝ ∞
      (fun x ↦ (canonicalNormalCompletion F x).toContinuousLinearMap) s := by
    apply contDiffOn_clm_apply.mpr
    intro H
    exact contDiffOn_canonicalNormalCompletion hs hF contDiffOn_const himm hrank
  have hH : ContDiffOn ℝ ∞ (fun p ↦ symmetricProduct (ξ p) (b p)) U := by
    let L : (Fin n → Fin n → ℝ) →ₗ[ℝ] MetricTensor n := LinearMap.id
    let C : (Fin n → Fin n → ℝ) →L[ℝ] MetricTensor n :=
      ⟨L, L.continuous_of_finiteDimensional⟩
    apply C.contDiff.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    have hij := ((contDiffOn_piLp 2).mp hξ i).mul ((contDiffOn_piLp 2).mp hb j)
    have hji := ((contDiffOn_piLp 2).mp hb i).mul ((contDiffOn_piLp 2).mp hξ j)
    exact (hij.add hji).div_const 2
  exact (hL.comp contDiffOn_fst hU).clm_apply hH

/-- `app:ch_background:prop:bg-normalized`: joint smoothness of the regular
principal-normal pullback on any domain whose dilation lies in the coefficient
domain. This formula is meaningful at scale zero and at negative scales too. -/
theorem contDiffOn_normalizedPrincipalNormal {n N : ℕ}
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : Euclidean n → Euclidean N} {s : Set (Euclidean n)}
    {U : Set (Euclidean n × Z)} {D : Set (ℝ × (Euclidean n × Z))}
    {ξ b : Euclidean n × Z → Euclidean n}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s)
    (himm : IsImmersionOn F s) (hrank : HasFullNormalRankOn F s)
    (hU : MapsTo Prod.fst U s)
    (hξ : ContDiffOn ℝ ∞ ξ U) (hb : ContDiffOn ℝ ∞ b U)
    (hD : MapsTo (fun p : ℝ × (Euclidean n × Z) ↦ (p.1 • p.2.1, p.2.2)) D U) :
    ContDiffOn ℝ ∞
      (normalizedPullback
        (fun p ↦ principalNormal (canonicalNormalCompletion F p.1) (ξ p) (b p))) D :=
  (contDiffOn_normalizedPullback
    (contDiffOn_canonicalPrincipalNormal hs hF himm hrank hU hξ hb)).mono hD

/-- `app:ch_background:prop:bg-normalized`: on an open coefficient domain the
regular pullback is smooth at every zero-scale point over that domain. This is
smoothness through zero, without a full-rank zero-scale reference. -/
theorem contDiffAt_normalizedPrincipalNormal_zero {n N : ℕ}
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : Euclidean n → Euclidean N} {s : Set (Euclidean n)}
    {U : Set (Euclidean n × Z)} {ξ b : Euclidean n × Z → Euclidean n}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s)
    (himm : IsImmersionOn F s) (hrank : HasFullNormalRankOn F s)
    (hU : MapsTo Prod.fst U s) (hUopen : IsOpen U)
    (hξ : ContDiffOn ℝ ∞ ξ U) (hb : ContDiffOn ℝ ∞ b U)
    (x : Euclidean n) (z : Z) (hz : (0, z) ∈ U) :
    ContDiffAt ℝ ∞
      (normalizedPullback
        (fun p ↦ principalNormal (canonicalNormalCompletion F p.1) (ξ p) (b p)))
      (0, (x, z)) := by
  have hd : Continuous (fun p : ℝ × (Euclidean n × Z) ↦ (p.1 • p.2.1, p.2.2)) :=
    (continuous_fst.smul continuous_snd.fst).prodMk continuous_snd.snd
  have hmem : (0, (x, z)) ∈
      {p : ℝ × (Euclidean n × Z) | (p.1 • p.2.1, p.2.2) ∈ U} := by
    simpa using hz
  exact (contDiffOn_normalizedPullback
    (contDiffOn_canonicalPrincipalNormal hs hF himm hrank hU hξ hb) _ hmem).contDiffAt
      ((hUopen.preimage hd).mem_nhds hmem)

/-- `app:ch_background:prop:bg-normalized`: a concrete smooth extension of the
actual positive-scale principal normals, with its frozen zero value. The
extension is the normalized pullback; the hypotheses concern only the unscaled
geometry, the input covectors/amplitudes, and explicit domain containment.
The leading-wave producer must still identify its fields with these inputs. -/
theorem exists_smooth_principalNormal_sourceDilation_extension {n N : ℕ}
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : Euclidean n → Euclidean N} {s : Set (Euclidean n)}
    {U : Set (Euclidean n × Z)} {D : Set (ℝ × (Euclidean n × Z))}
    {ξ b : Euclidean n × Z → Euclidean n}
    (hs : IsOpen s) (hF : ContDiff ℝ ∞ F)
    (himm : IsImmersionOn F s) (hrank : HasFullNormalRankOn F s)
    (hU : MapsTo Prod.fst U s)
    (hξ : ContDiffOn ℝ ∞ ξ U) (hb : ContDiffOn ℝ ∞ b U)
    (hD : MapsTo (fun p : ℝ × (Euclidean n × Z) ↦ (p.1 • p.2.1, p.2.2)) D U) :
    ∃ ν : ℝ × (Euclidean n × Z) → Euclidean N,
      ContDiffOn ℝ ∞ ν D ∧
      (∀ p ∈ D, 0 < p.1 → ν p =
        principalNormal (canonicalNormalCompletion (sourceDilation F p.1) p.2.1)
          (ξ (p.1 • p.2.1, p.2.2)) (p.1 • b (p.1 • p.2.1, p.2.2))) ∧
      (∀ x z, ν (0, (x, z)) =
        principalNormal (canonicalNormalCompletion F 0) (ξ (0, z)) (b (0, z))) := by
  refine ⟨normalizedPullback
    (fun p ↦ principalNormal (canonicalNormalCompletion F p.1) (ξ p) (b p)),
    contDiffOn_normalizedPrincipalNormal hs hF.contDiffOn himm hrank hU hξ hb hD, ?_, ?_⟩
  · intro p hp hσ
    exact (principalNormal_sourceDilation_eq_normalizedPullback ξ b hσ hF p.2.1 p.2.2
      (hrank _ (hU (hD hp)))).symm
  · intro x z
    exact normalizedPullback_zero _ x z

end NormalizedBackground
end JanetCartan
