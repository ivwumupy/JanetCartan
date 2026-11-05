module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry.PhaseExtension

/-!
# The full sampling Jacobian on the complete radial support

The full integral quotient rescales epsilon as well as the covector. Its
Jacobian nevertheless has exactly one radial factor. This transfers the
actual local determinant gap to the entire prescribed positive radial interval,
including epsilon zero, using the SAME retained Hamilton phase.

The consumer is the `jacobian_gap` field of the full sampling normal geometry
in `app:ch_waves:setup:oscillatory`. Global injectivity and common image buffers
on that enlarged support are separate obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.FullNormalGeometry
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison NormalComparison ContinuumRow.CanonicalConic
open MeanNormalBound.CanonicalGap RawKernel
open ContinuumNormalReduction.ConicChart

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})

/-- The full averaged-gradient differential is conjugate to the actual chart
differential even at epsilon zero. This uses the published phase identification,
not equality of independently constructed charts
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem det_averagedGradient_normalizedFullPhase (v : Euclidean 2) (ε : ℝ)
    (x y u : Euclidean (m + 1)) :
    (fderiv ℝ (averagedGradient (normalizedFullPhase T Q v ε) x y) u).det =
      (fderiv ℝ (fullChartFamily (current T Q) (spatialCarrier T)
        (fullPhaseParameters T ε v x y)) ((adaptedSliceCoordinates T).equiv u)).det := by
  let c := (adaptedSliceCoordinates T).equiv
  let f := fullChartFamily (current T Q) (spatialCarrier T)
    (fullPhaseParameters T ε v x y)
  have he : averagedGradient (normalizedFullPhase T Q v ε) x y = c.symm ∘ f ∘ c := by
    funext w
    apply c.injective
    exact (averagedGradient_normalizedFullPhase T Q v ε x y w).trans
      (c.apply_symm_apply _).symm
  rw [he, c.symm.comp_fderiv, c.comp_right_fderiv]
  exact LinearMap.det_conj (fderiv ℝ f (c u)).toLinearMap c.symm.toLinearEquiv

/-- The literal sampling coordinates preserve the absolute full-chart
Jacobian. The input is the original `(s,theta)` variable
(`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem abs_det_literalFullPhase (v : Euclidean 2) (ε : ℝ)
    (x y u : Euclidean (m + 1)) :
    |(fderiv ℝ (averagedGradient
      (fun x w ↦ normalizedFullPhase T Q v ε x (canonicalInputCoordinates T w)) x y) u).det| =
      |(fderiv ℝ (fullChartFamily (current T Q) (spatialCarrier T)
        (fullPhaseParameters T ε v x y))
          ((adaptedSliceCoordinates T).equiv (canonicalInputCoordinates T u))).det| := by
  rw [averagedGradient_abs_det_canonicalInputCoordinates,
    det_averagedGradient_normalizedFullPhase]

private def radialInputEquiv (a : ℝ) (ha : a ≠ 0) :
    Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1) :=
  let c := (adaptedSliceCoordinates T).equiv
  c.trans ((ContinuousLinearEquiv.equivOfInverse
    (radialLinearMap (E := Euclidean m) a) (radialLinearMap (E := Euclidean m) a⁻¹)
    (by intro w; ext <;> simp [radialScale, smul_smul, ha])
    (by intro w; ext <;> simp [radialScale, smul_smul, ha])).trans c.symm)

private theorem radialInputEquiv_apply (a : ℝ) (ha : a ≠ 0)
    (u : Euclidean (m + 1)) : radialInputEquiv T a ha u = radialInput T a u := rfl

private theorem det_radialInputEquiv (a : ℝ) (ha : a ≠ 0) :
    (radialInputEquiv T a ha).toLinearEquiv.toLinearMap.det = a ^ m := by
  have he := LinearMap.det_conj (radialLinearMap (E := Euclidean m) a).toLinearMap
    (adaptedSliceCoordinates T).equiv.symm.toLinearEquiv
  change (radialInputEquiv T a ha).toLinearEquiv.toLinearMap.det =
    (radialLinearMap (E := Euclidean m) a).det at he
  rw [he, det_radialLinearMap]
  simp

/-- Exact degree-one radial Jacobian law for the full, nonhomogeneous
Hamilton quotient. Epsilon changes to `epsilon * a`; the formula also holds
at zero. No differentiability assumption is needed for these total derivatives
(`app:ch_seed:eq:seed-quotient-integral`). -/
theorem det_averagedGradient_radialInput (v : Euclidean 2) (ε : ℝ)
    {a : ℝ} (ha : a ≠ 0) (x y u : Euclidean (m + 1)) :
    (fderiv ℝ (averagedGradient (normalizedFullPhase T Q v ε) x y)
      (radialInput T a u)).det =
      a * (fderiv ℝ (averagedGradient (normalizedFullPhase T Q v (ε * a)) x y) u).det := by
  let c := radialInputEquiv T a ha
  let f := averagedGradient (normalizedFullPhase T Q v ε) x y
  let g := averagedGradient (normalizedFullPhase T Q v (ε * a)) x y
  have he : f ∘ c = a • g :=
    funext fun w ↦ averagedGradient_radialInput T Q v ε a x y w
  have hd : (fderiv ℝ f (c u)).comp c.toContinuousLinearMap = a • fderiv ℝ g u := by
    rw [← c.comp_right_fderiv, he, fderiv_const_smul_field]
    rfl
  have hdet := congrArg ContinuousLinearMap.det hd
  change LinearMap.det ((fderiv ℝ f (c u)).toLinearMap.comp c.toLinearEquiv.toLinearMap) =
    LinearMap.det (a • (fderiv ℝ g u).toLinearMap) at hdet
  rw [LinearMap.det_comp, LinearMap.det_smul, det_radialInputEquiv] at hdet
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hdet
  apply mul_right_cancel₀ (pow_ne_zero m ha)
  change (fderiv ℝ f (c u)).det * a ^ m = (a * (fderiv ℝ g u).det) * a ^ m
  rw [hdet, pow_succ]
  ring

omit Q in
/-- An actual positive determinant gap on the ENTIRE radially dilated outer
input core, from primitive `C6` closeness and frozen incidence transversality.
The data radius, epsilon radius and gap precede the current frame and every
spectator and radial label. Both caps are arbitrary. The original coefficient
domain and the SAME retained Hamilton chart are used throughout
(`app:ch_seed:prop:seed-phase-charts`, `app:ch_waves:setup:oscillatory`). -/
theorem exists_radial_literalFullPhase_jacobian_gap {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean (m + 1)} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {rmax emax amin amax : ℝ} (hrmax : 0 < rmax) (hemax : 0 < emax)
    (hamin : 0 < amin) (ha : amin ≤ amax) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    ∃ r > (0 : ℝ), r ≤ rmax ∧ ∃ s > (0 : ℝ), s ≤ r ∧
      3 * r < T.family.radius / 8 ∧
      (closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
        carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
    ∃ e > (0 : ℝ), e ≤ emax ∧ ∃ δ > (0 : ℝ), ∃ γ > (0 : ℝ),
      ∀ Q,
        cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress (m + 1)) < δ →
      ∀ ε ∈ Icc 0 e, ∀ v ∈ closedBall (spectatorCenter z₀) (s / 2),
        ∀ x ∈ closedBall 0 (s / 2), ∀ y ∈ closedBall 0 (s / 2),
        ∀ u ∈ radialSamplingSupport T z₀ ηb (2 * r) amin amax,
          γ ≤ |(fderiv ℝ (averagedGradient
            (fun x w ↦ normalizedFullPhase T Q v ε x
              (canonicalInputCoordinates T w)) x y) u).det| := by
  dsimp only
  have hamax : 0 < amax := hamin.trans_le ha
  obtain ⟨r, hr, hrcap, s, hs, hsr, hphys, hcarrier, e, he, hecap, δ, hδ, _, _,
    cF, hcF, bF, _, V, L, _, _, _, _, hall⟩ :=
    exists_buffered_normalizedFullPhase_gap T hP hz₀ hk hinc hd hrmax
      (mul_pos hemax hamax)
  refine ⟨r, hr, hrcap, s, hs, hsr, hphys, hcarrier,
    e / amax, div_pos he hamax, (div_le_iff₀ hamax).mpr hecap,
    δ, hδ, amin * cF, mul_pos hamin hcF, ?_⟩
  intro Q hQ ε hε v hv x hx y hy u hu
  obtain ⟨⟨a, w⟩, ⟨ha', hw⟩, heq⟩ := hu
  have hapos : 0 < a := hamin.trans_le ha'.1
  have hεa : ε * a ∈ Icc 0 e :=
    ⟨mul_nonneg hε.1 hapos.le,
      (mul_le_mul_of_nonneg_left ha'.2 hε.1).trans
        ((le_div_iff₀ hamax).mp hε.2)⟩
  rw [averagedGradient_abs_det_canonicalInputCoordinates, ← heq,
    det_averagedGradient_radialInput T Q v ε hapos.ne', abs_mul, abs_of_pos hapos,
    det_averagedGradient_normalizedFullPhase]
  exact mul_le_mul ha'.1
    (((hall Q hQ).1.differential_bounds _
      (fullPhaseParameters_mem T hs he hεa hv hx hy) _ hw).2.2) hcF.le hapos.le

end JanetCartan.Sampling.FullNormalGeometry
