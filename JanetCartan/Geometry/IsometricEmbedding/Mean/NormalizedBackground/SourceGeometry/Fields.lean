module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.SmoothPhase
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Transport
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Normal

/-!
# The actual normalized geometric fields

Connections between the constructed source phase/transport and the canonical
normal, principal matrix, second form and completion in
`app:ch_background:eq:bg-Nsigma`. The seed scalar is supplied by the positive
characteristic construction. The selected adjugate indices are unchanged.
-/

@[expose] public noncomputable section

open Set Matrix
open scoped ContDiff Matrix.Norms.Frobenius
open scoped JanetCartan.NormalRankStability JanetCartan.TensorFrobenius

namespace JanetCartan.NormalizedBackground.SourceGeometry

open NullTransport NullTransport.FlowAmplitude LeadingWave AmbientResponse

variable {n N : ℕ} {Z : Type}

/-- The smooth amplitude and its nonzero pencil-null value required by
`exists_common_source_geometry_bounds` follow from the actual selected adjugate
column and positive seed scalar (`app:ch_waves:thm:leading`). -/
theorem selected_seedAmplitude_properties
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : Euclidean n → Euclidean N} {U : Set (Euclidean n)} {V : Set Z}
    (hU : IsOpen U) (hV : IsOpen V) (hF : ContDiffOn ℝ ∞ F U)
    (hflat : ∀ x ∈ U, inducedMetric F x = 1) (hrank : HasFullNormalRankOn F U)
    {S : Euclidean n × Z → ℝ} (hS : ContDiffOn ℝ ∞ S (U ×ˢ V))
    {α : Euclidean n × Z → ℝ} (hα : ContDiffOn ℝ ∞ α (U ×ˢ V))
    (row col time : Fin n)
    (hpos : ∀ p ∈ U ×ˢ V, 0 < α p)
    (hchar : ∀ p ∈ U ×ˢ V, ((projectedPhaseGeometry F S row col time).symbol p).det = 0)
    (hminor : ∀ p ∈ U ×ˢ V,
      ((projectedPhaseGeometry F S row col time).symbol p).adjugate row col ≠ 0) :
    let b := fun p ↦ α p • (projectedPhaseGeometry F S row col time).kernel p
    ContDiffOn ℝ ∞ b (U ×ˢ V) ∧ ∀ p ∈ U ×ˢ V,
      ActualCarriers.pencil (ProjectedStressFrame.projectedStress F p.1)
        (gradient (fun y ↦ S (y, p.2)) p.1) *ᵥ (fun j ↦ b p j) = 0 ∧ b p ≠ 0 := by
  have hk := contDiffOn_projectedPhaseGeometry_kernel hU hF hflat hrank
    (contDiffOn_phase_positionGradient hU hV hS) row col time
  refine ⟨hα.smul hk, ?_⟩
  intro p hp
  constructor
  · change (projectedPhaseGeometry F S row col time).symbol p *ᵥ
      (α p • rightNullvector ((projectedPhaseGeometry F S row col time).symbol p) col) = 0
    rw [Matrix.mulVec_smul, mulVec_rightNullvector (hchar p hp), smul_zero]
  · apply smul_ne_zero (ne_of_gt (hpos p hp))
    intro hz
    exact rightNullvector_ne_zero (hminor p hp)
      (congrArg (fun v : Euclidean n ↦ fun j ↦ v j) hz)

/-- The literal principal normal of the constructed phase and amplitude is
the regular seed pullback (`app:ch_background:eq:bg-Nsigma`). -/
theorem principalNormal_sourcePhase_sourceAmplitude
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    {S : Euclidean n × Z → ℝ} (b : Euclidean n × Z → Euclidean n)
    {ρ : ℝ} (hρ : 0 < ρ) {x : Euclidean n} {z : Z}
    (hrank : Set.range (normalMap F (ρ • x)) =
      (normalSpace F (ρ • x) : Set (Euclidean N)))
    (hS : DifferentiableAt ℝ (fun y ↦ S (y, z)) (ρ • x)) :
    principalNormal (canonicalNormalCompletion (sourceDilation F ρ) x)
      (gradient (fun y ↦ sourcePhase S ρ (y, z)) x) (sourceAmplitude b ρ (x, z)) =
      normalizedPullback (fun p ↦ principalNormal (canonicalNormalCompletion F p.1)
        (gradient (fun y ↦ S (y, p.2)) p.1) (b p)) (ρ, (x, z)) := by
  rw [gradient_sourcePhase_position hρ.ne' hS]
  exact principalNormal_sourceDilation_scaled_amplitude hρ hF x hrank _ _

/-- The actual principal matrix has the same pullback identity as its two
factors; no field of an assumed normalized family is used
(`app:ch_background:eq:bg-Nsigma`). -/
theorem principalMatrix_sourcePhase_sourceAmplitude
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    {S : Euclidean n × Z → ℝ} (b : Euclidean n × Z → Euclidean n)
    {ρ : ℝ} (hρ : 0 < ρ) {x : Euclidean n} {z : Z}
    (hrank : Set.range (normalMap F (ρ • x)) =
      (normalSpace F (ρ • x) : Set (Euclidean N)))
    (hS : DifferentiableAt ℝ (fun y ↦ S (y, z)) (ρ • x)) :
    principalMatrix
      (principalNormal (canonicalNormalCompletion (sourceDilation F ρ) x)
        (gradient (fun y ↦ sourcePhase S ρ (y, z)) x) (sourceAmplitude b ρ (x, z)))
      (gradient (fun y ↦ sourcePhase S ρ (y, z)) x) =
    normalizedPullback (fun p ↦ principalMatrix
      (principalNormal (canonicalNormalCompletion F p.1)
        (gradient (fun y ↦ S (y, p.2)) p.1) (b p))
      (gradient (fun y ↦ S (y, p.2)) p.1)) (ρ, (x, z)) := by
  rw [principalNormal_sourcePhase_sourceAmplitude hF b hρ hrank hS,
    gradient_sourcePhase_position hρ.ne' hS]
  rfl

/-- Smoothness of the actual seed principal matrix, used for the normalized
matrix extension and its mixed derivatives
(`app:ch_background:prop:bg-normalized`). -/
theorem contDiffOn_canonicalPrincipalMatrix
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : Euclidean n → Euclidean N} {U : Set (Euclidean n)} {V : Set Z}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (himm : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {ξ b : Euclidean n × Z → Euclidean n}
    (hξ : ContDiffOn ℝ ∞ ξ (U ×ˢ V)) (hb : ContDiffOn ℝ ∞ b (U ×ˢ V)) :
    ContDiffOn ℝ ∞ (fun p ↦ principalMatrix
      (principalNormal (canonicalNormalCompletion F p.1) (ξ p) (b p)) (ξ p)) (U ×ˢ V) := by
  have hν := contDiffOn_canonicalPrincipalNormal hU hF himm hrank
    (U := U ×ˢ V) (fun _ hp ↦ hp.1) hξ hb
  let L : (Fin N → Fin n → ℝ) →ₗ[ℝ] Matrix (Fin N) (Fin n) ℝ := LinearMap.id
  let C : (Fin N → Fin n → ℝ) →L[ℝ] Matrix (Fin N) (Fin n) ℝ :=
    ⟨L, L.continuous_of_finiteDimensional⟩
  apply C.contDiff.comp_contDiffOn
  apply contDiffOn_pi.mpr
  intro a
  apply contDiffOn_pi.mpr
  intro i
  exact (((contDiffOn_piLp 2).mp hν a).mul ((contDiffOn_piLp 2).mp hξ i)).neg

/-- The normalized second form is a smooth pullback on the seed rank domain,
and agrees with `ρ⁻¹ B_{Gρ}` at positive scales. Only this field is extended at
zero (`app:ch_background:prop:bg-normalized`). -/
theorem normalized_secondFundamentalForm_extension
    {F : Euclidean n → Euclidean N} {U : Set (Euclidean n)}
    (hU : IsOpen U) (hF : ContDiff ℝ ∞ F) (himm : IsImmersionOn F U)
    (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun q : ℝ × Euclidean n ↦ secondFundamentalForm F (q.1 • q.2) i j)
      {q | q.1 • q.2 ∈ U} ∧
    ∀ ρ : ℝ, 0 < ρ → ∀ x : Euclidean n,
      ρ⁻¹ • secondFundamentalForm (sourceDilation F ρ) x i j =
        secondFundamentalForm F (ρ • x) i j := by
  refine ⟨(contDiffOn_secondFundamentalForm_of_smooth hU hF.contDiffOn himm i j).comp
    (contDiff_fst.smul contDiff_snd).contDiffOn (fun _ hq ↦ hq), ?_⟩
  intro ρ hρ x
  rw [secondFundamentalForm_sourceDilation hρ hF]
  simp [smul_smul, hρ.ne']

/-- The actual normalized canonical completion extends smoothly as an operator
on the same seed domain. This is an operator identity, with no arbitrary
inverse-family assumption (`app:ch_background:eq:bg-Nsigma`). -/
theorem normalized_canonicalNormalCompletion_extension
    {F : Euclidean n → Euclidean N} {U : Set (Euclidean n)}
    (hU : IsOpen U) (hF : ContDiff ℝ ∞ F)
    (himm : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U) :
    ContDiffOn ℝ ∞ (fun q : ℝ × Euclidean n ↦
      (canonicalNormalCompletion F (q.1 • q.2)).toContinuousLinearMap)
      {q | q.1 • q.2 ∈ U} ∧
    ∀ ρ : ℝ, 0 < ρ → ∀ x : Euclidean n, ρ • x ∈ U →
      ρ • (canonicalNormalCompletion (sourceDilation F ρ) x).toContinuousLinearMap =
        (canonicalNormalCompletion F (ρ • x)).toContinuousLinearMap := by
  have hc : ContDiffOn ℝ ∞ (fun x ↦ (canonicalNormalCompletion F x).toContinuousLinearMap) U := by
    apply contDiffOn_clm_apply.mpr
    intro H
    exact contDiffOn_canonicalNormalCompletion hU hF.contDiffOn contDiffOn_const himm hrank
  refine ⟨hc.comp (contDiff_fst.smul contDiff_snd).contDiffOn (fun _ hq ↦ hq), ?_⟩
  intro ρ hρ x hx
  apply ContinuousLinearMap.ext
  intro H
  exact smul_canonicalNormalCompletion_sourceDilation hρ hF x (hrank _ hx) H

/-- The normalized second form, completion operator and principal matrix
have all mixed derivative bounds on the same already chosen scale and buffers.
Together with their exact identities above, this supplies the remaining
geometric fields of `app:ch_background:prop:bg-normalized`. No new scale is
chosen after the derivative order. -/
theorem normalized_geometric_fields_joint_bounds
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : Euclidean n → Euclidean N} {U B D : Set (Euclidean n)} {V K : Set Z}
    (hU : IsOpen U) (hB : IsOpen B) (hV : IsOpen V)
    (hF : ContDiff ℝ ∞ F) (himm : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {ξ b : Euclidean n × Z → Euclidean n}
    (hξ : ContDiffOn ℝ ∞ ξ (U ×ˢ V)) (hb : ContDiffOn ℝ ∞ b (U ×ˢ V))
    {r : ℝ} (hr : 0 < r) (hD : IsCompact D) (hDB : D ⊆ B)
    (hK : IsCompact K) (hKV : K ⊆ V)
    (hmaps : ∀ ρ ∈ Ioo (-2 * r) (2 * r), MapsTo (fun x ↦ ρ • x) B U)
    (i j : Fin n) :
    let Q := fun q : ℝ × (Euclidean n × Z) ↦
      (secondFundamentalForm F (q.1 • q.2.1) i j,
       (canonicalNormalCompletion F (q.1 • q.2.1)).toContinuousLinearMap,
       normalizedPullback (fun p ↦ principalMatrix
         (principalNormal (canonicalNormalCompletion F p.1) (ξ p) (b p)) (ξ p)) q)
    ContDiffOn ℝ ∞ Q (Ioo (-2 * r) (2 * r) ×ˢ B ×ˢ V) ∧
      ∀ s : ℕ, ∃ C > 0, ∀ ρ ∈ Icc (0 : ℝ) r, ∀ x ∈ D, ∀ z ∈ K,
        ‖iteratedFDeriv ℝ s Q (ρ, (x, z))‖ ≤ C := by
  have hII := (normalized_secondFundamentalForm_extension hU hF himm i j).1.comp
    (contDiffOn_fst.prodMk contDiffOn_snd.fst)
    (show MapsTo (fun q : ℝ × (Euclidean n × Z) ↦ (q.1, q.2.1))
      (Ioo (-2 * r) (2 * r) ×ˢ B ×ˢ V) {q | q.1 • q.2 ∈ U} from
      fun _ hq ↦ hmaps _ hq.1 hq.2.1)
  have hN := (normalized_canonicalNormalCompletion_extension hU hF himm hrank).1.comp
    (contDiffOn_fst.prodMk contDiffOn_snd.fst)
    (show MapsTo (fun q : ℝ × (Euclidean n × Z) ↦ (q.1, q.2.1))
      (Ioo (-2 * r) (2 * r) ×ˢ B ×ˢ V) {q | q.1 • q.2 ∈ U} from
      fun _ hq ↦ hmaps _ hq.1 hq.2.1)
  have hA := (contDiffOn_normalizedPullback
    (contDiffOn_canonicalPrincipalMatrix hU hF.contDiffOn himm hrank hξ hb)).mono
      (show (Ioo (-2 * r) (2 * r) ×ˢ B ×ˢ V) ⊆
        {q : ℝ × (Euclidean n × Z) | (q.1 • q.2.1, q.2.2) ∈ U ×ˢ V} from
        fun _ hq ↦ ⟨hmaps _ hq.1 hq.2.1, hq.2.2⟩)
  have hQ := hII.prodMk (hN.prodMk hA)
  refine ⟨hQ, ?_⟩
  intro s
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (hD.prod hK)).exists_bound_of_continuousOn
    ((ContinuousOn.continuousOn_iteratedFDeriv hQ
      (isOpen_Ioo.prod (hB.prod hV)) (by simp)).mono
        (show Icc (0 : ℝ) r ×ˢ D ×ˢ K ⊆ Ioo (-2 * r) (2 * r) ×ˢ B ×ˢ V from by
          intro q hq
          exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, hDB hq.2.1, hKV hq.2.2⟩))
  exact ⟨|C| + 1, by positivity, fun ρ hρ x hx z hz ↦
    (hC (ρ, (x, z)) ⟨hρ, hx, hz⟩).trans ((le_abs_self C).trans (by linarith))⟩

end JanetCartan.NormalizedBackground.SourceGeometry
