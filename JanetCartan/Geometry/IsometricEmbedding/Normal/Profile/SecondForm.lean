module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Metric
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.SecondJet
public import JanetCartan.Geometry.IsometricEmbedding.Normal.SmoothProjection
public import JanetCartan.Geometry.IsometricEmbedding.Normal.RankStability.Geometry

/-!
# The second fundamental form as a tame second-jet coefficient

The rational formulas of `app:ch_background:eq:bg-frame-tame` are evaluated on
the actual derivatives. Compact immersive jet ranges supply the metric inverse
gap. The resulting estimate has one high norm and the exact fixed shift two.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.GeometricProfile

/-- `app:ch_waves:defn:geometry`: immersion makes the first-jet Gram metric invertible. -/
theorem firstJetMetric_isUnit_of_injective {n N : ℕ}
    {L : Euclidean n →L[ℝ] Euclidean N} (hL : Function.Injective L) :
    IsUnit (firstJetMetric L) := by
  have hi : Function.Injective (fderiv ℝ (L : Euclidean n → Euclidean N) 0) := by
    simpa using hL
  have hu := (inducedMetric_posDef hi).isUnit
  change IsUnit (firstJetMetric (fderiv ℝ (L : Euclidean n → Euclidean N) 0)) at hu
  simpa using hu

private def metricEntry {n : ℕ} (i j : Fin n) : MetricTensor n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) j).comp
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ Fin n → ℝ) i))

/-- `app:ch_waves:eq:ambient-normal-inverse`: the rational first-jet formula
for normal projection, as an operator on the fixed ambient Euclidean space. -/
def firstJetNormalProjection {n N : ℕ} (L : Euclidean n →L[ℝ] Euclidean N) :
    Euclidean N →L[ℝ] Euclidean N :=
  ContinuousLinearMap.id ℝ _ - ∑ i, ∑ j,
    (firstJetMetric L)⁻¹ i j •
      (innerSL ℝ (L (EuclideanSpace.single j 1))).smulRight
        (L (EuclideanSpace.single i 1))

/-- `app:ch_background:defn:bg-geometry`: the explicit projected Hessian as
a function of first and second derivatives. -/
def secondJetSecondForm {n N : ℕ} (J : SecondJet (Euclidean n) (Euclidean N))
    (i j : Fin n) : Euclidean N :=
  firstJetNormalProjection J.1 (J.2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))

/-- `app:ch_waves:eq:ambient-normal-inverse`: identification with actual
orthogonal projection at every immersive first jet. -/
theorem firstJetNormalProjection_eq {n N : ℕ} {f : Euclidean n → Euclidean N}
    {x : Euclidean n} (hf : Function.Injective (fderiv ℝ f x)) :
    firstJetNormalProjection (fderiv ℝ f x) = normalProjection f x := by
  ext w : 1
  rw [normalProjection_eq_sub_tangentProjection, tangentProjection_eq_sum hf]
  change _ = w - ∑ i, ∑ j, ((firstJetMetric (fderiv ℝ f x))⁻¹ i j *
    inner ℝ (fderiv ℝ f x (EuclideanSpace.single j 1)) w) •
      fderiv ℝ f x (EuclideanSpace.single i 1)
  simp [firstJetNormalProjection, smul_smul]

/-- `app:ch_background:eq:bg-frame-tame`: the projection formula is smooth
near every nonsingular first jet. -/
theorem contDiffAt_firstJetNormalProjection {n N : ℕ}
    {L : Euclidean n →L[ℝ] Euclidean N} (hL : IsUnit (firstJetMetric L)) :
    ContDiffAt ℝ ∞ (@firstJetNormalProjection n N) L := by
  apply contDiffWithinAt_clm_apply.mpr
  intro w
  have he : (fun J : Euclidean n →L[ℝ] Euclidean N ↦ firstJetNormalProjection J w) =
      (fun J ↦ w - ∑ i, ∑ j, ((firstJetMetric J)⁻¹ i j *
        inner ℝ (J (EuclideanSpace.single j 1)) w) • J (EuclideanSpace.single i 1)) := by
    funext J
    simp [firstJetNormalProjection, smul_smul]
  rw [he]
  apply contDiffAt_const.sub
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  have hc := (metricEntry i j).contDiff.contDiffAt.comp _
    (contDiffAt_firstJetMetric_inv hL)
  exact (hc.mul ((contDiffAt_id.clm_apply contDiffAt_const).inner ℝ contDiffAt_const)).smul
    (contDiffAt_id.clm_apply contDiffAt_const)

/-- `app:ch_background:eq:bg-frame-tame`: the second-form coefficient is
smooth near every jet with nonsingular metric. -/
theorem contDiffAt_secondJetSecondForm {n N : ℕ}
    {J : SecondJet (Euclidean n) (Euclidean N)} (hJ : IsUnit (firstJetMetric J.1))
    (i j : Fin n) : ContDiffAt ℝ ∞ (fun K ↦ secondJetSecondForm K i j) J :=
  ((contDiffAt_firstJetNormalProjection hJ).comp J contDiffAt_fst).clm_apply
    ((contDiffAt_snd.clm_apply contDiffAt_const).clm_apply contDiffAt_const)

/-- `app:ch_background:defn:bg-geometry`: the rational second-jet formula
agrees with the existing second fundamental form of a smooth immersion. -/
theorem secondJetSecondForm_eq {n N : ℕ} {f : Euclidean n → Euclidean N}
    (hf : ContDiff ℝ ∞ f) {x : Euclidean n}
    (hi : Function.Injective (fderiv ℝ f x)) (i j : Fin n) :
    secondJetSecondForm (secondJet f x) i j = secondFundamentalForm f x i j := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  rw [secondJetSecondForm, secondJet, firstJetNormalProjection_eq hi,
    secondFundamentalForm_eq_normalProjection]
  congr 1
  unfold partialDeriv
  rw [fderiv_clm_apply (hd.differentiable (by simp)).differentiableAt
    (differentiableAt_const _)]
  simp

/-- `app:ch_background:eq:bg-frame-tame`: the actual second form has one
high map norm, with the fixed shift two, uniformly over a compact immersive
second-jet range. No generic coefficient profile or interpolation is assumed. -/
theorem exists_cNorm_secondFundamentalForm_le_closedBall
    {n N : ℕ} (x : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    {t : Set (SecondJet (Euclidean n) (Euclidean N))} (ht : IsCompact t)
    (htimm : ∀ J ∈ t, Function.Injective J.1) (r : ℕ) (i j : Fin n) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Euclidean n → Euclidean N, ContDiff ℝ ∞ f →
      Set.MapsTo (secondJet f) (Metric.closedBall x ρ) t →
        cNorm (Metric.closedBall x ρ) r (fun y ↦ secondFundamentalForm f y i j) ≤
          C * (1 + cNorm (Metric.closedBall x ρ) (r + 2) f) := by
  have hu : ∀ J ∈ t, IsUnit (firstJetMetric J.1) := by
    intro J hJ
    have hi : Function.Injective (fderiv ℝ (J.1 : Euclidean n → Euclidean N) 0) := by
      simpa using htimm J hJ
    have hu := (inducedMetric_posDef hi).isUnit
    change IsUnit (firstJetMetric (fderiv ℝ (J.1 : Euclidean n → Euclidean N) 0)) at hu
    simpa using hu
  obtain ⟨C, hC, hbound⟩ := exists_cNorm_secondJet_comp_le_closedBall x hρ ht
    (fun J hJ ↦ (contDiffAt_secondJetSecondForm (hu J hJ) i j).of_le
      (by simp : (r : ℕ∞ω) ≤ ∞))
  refine ⟨C, hC, fun f hf hft ↦ ?_⟩
  have he : cNorm (Metric.closedBall x ρ) r (fun y ↦ secondFundamentalForm f y i j) =
      cNorm (Metric.closedBall x ρ) r ((fun J ↦ secondJetSecondForm J i j) ∘ secondJet f) := by
    apply cNorm_eq_of_eventuallyEq
    intro y hy
    have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
    have hi : ∀ᶠ z in 𝓝 y, Function.Injective (fderiv ℝ f z) :=
      hd.continuous.continuousAt.eventually
        (ContinuousLinearMap.isOpen_injective.mem_nhds (htimm _ (hft hy)))
    filter_upwards [hi] with z hz
    exact (secondJetSecondForm_eq hf hz i j).symm
  rw [he]
  exact hbound f hf hft

open scoped NormalRankStability

/-- `app:ch_waves:defn:geometry`: the ambient normal map obtained by
contracting a tensor with the rational second-jet formula. -/
def secondJetNormalMap {n N : ℕ} (J : SecondJet (Euclidean n) (Euclidean N)) :
    MetricTensor n →L[ℝ] Euclidean N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun H ↦ ∑ i, ∑ j, H i j • secondJetSecondForm J i j
      map_add' := fun H K ↦ by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c H ↦ by simp [mul_smul, Finset.smul_sum] }

/-- `app:ch_background:defn:bg-geometry`: the jet formula is the actual
ambient second-form contraction, in the established Frobenius norm. -/
theorem secondJetNormalMap_eq {n N : ℕ} {f : Euclidean n → Euclidean N}
    (hf : ContDiff ℝ ∞ f) {x : Euclidean n}
    (hi : Function.Injective (fderiv ℝ f x)) :
    secondJetNormalMap (secondJet f x) = NormalRankStability.ambientNormalMap f x := by
  ext H : 1
  change (∑ i, ∑ j, H i j • secondJetSecondForm (secondJet f x) i j) =
    ∑ i, ∑ j, H i j • secondFundamentalForm f x i j
  simp_rw [secondJetSecondForm_eq hf hi]

/-- `app:ch_background:eq:bg-frame-tame`: smoothness of the actual ambient
normal-map coefficient follows from its finite second-jet sum. -/
theorem contDiffAt_secondJetNormalMap {n N : ℕ}
    {J : SecondJet (Euclidean n) (Euclidean N)} (hJ : IsUnit (firstJetMetric J.1)) :
    ContDiffAt ℝ ∞ (@secondJetNormalMap n N) J := by
  apply contDiffWithinAt_clm_apply.mpr
  intro H
  change ContDiffAt ℝ ∞ (fun K ↦ ∑ i, ∑ j, H i j • secondJetSecondForm K i j) J
  exact ContDiffAt.sum fun i _ ↦ ContDiffAt.sum fun j _ ↦
    (contDiffAt_secondJetSecondForm hJ i j).const_smul _

end JanetCartan.GeometricProfile
