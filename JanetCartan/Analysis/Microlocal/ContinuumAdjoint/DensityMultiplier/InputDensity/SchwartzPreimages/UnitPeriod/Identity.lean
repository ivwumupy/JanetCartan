module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputDensity.SchwartzPreimages.UnitPeriod.Basic

/-!
# Pointwise identification of the parameter inverse

Fubini and ordinary Fourier inversion identify the unit-period partial
transform in `app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`. The kernel is constructed from the
actual compact physical test, with a cutoff supplied by its compact support.
Its joint Schwartz bounds and the Schwartz marginal construction remain
separate obligations of `exists_unitPeriodSchwartz_compactSmooth`.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform Set
open scoped SchwartzMap RealInnerProductSpace ContDiff

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev

variable {n : ℕ}

/-- Fubini factorization of the full unit-period Fourier integral. The
parameter inversion below consumes this identity; all dimensions, including
zero transverse dimension, use ordinary Lebesgue measure
(`app:ch_background:prop:bg-adjoint`). -/
theorem unitPeriod_fullFourier_eq_iterated (f : 𝓢(InitialSpace n, ℂ)) (ξ : InitialSpace n) :
    (𝓕 f) ξ = 𝓕 (fun z : ParameterSpace ↦
      𝓕 (fun y : Euclidean (n - 1) ↦ f (WithLp.toLp 2 (z, y))) ξ.snd) ξ.fst := by
  have hg : Integrable (fun p : ParameterSpace × Euclidean (n - 1) ↦
      f (WithLp.toLp 2 p)) volume := by
    exact (WithLp.volume_preserving_toLp ParameterSpace (Euclidean (n - 1))).integrable_comp
      f.integrable.aestronglyMeasurable |>.mpr f.integrable
  have hi : Integrable (fun p : ParameterSpace × Euclidean (n - 1) ↦
      Real.fourierChar (-⟪WithLp.toLp 2 p, ξ⟫) • f (WithLp.toLp 2 p)) volume := by
    apply hg.norm.mono'
    · exact (by fun_prop : Continuous (fun p : ParameterSpace × Euclidean (n - 1) ↦
        Real.fourierChar (-⟪WithLp.toLp 2 p, ξ⟫) • f (WithLp.toLp 2 p))).aestronglyMeasurable
    · filter_upwards [] with p
      simp
  rw [SchwartzMap.fourier_coe, Real.fourier_eq,
    ← (WithLp.volume_preserving_toLp ParameterSpace (Euclidean (n - 1))).integral_comp
      (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod _ hi, Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [WithLp.prod_inner_apply]
  change (Real.fourierChar (-(⟪z, ξ.fst⟫ + ⟪y, ξ.snd⟫)) : ℂ) * _ = _
  rw [neg_add, AddChar.map_add_eq_mul]
  simp only [Circle.coe_mul, mul_assoc]

/-- Continuity of the actual partial Fourier integral in the parameter
variables, used by pointwise Fourier inversion
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem continuous_unitPeriodPartialIntegral_parameter (φ : carrierInitialTestSpace n) (η : Euclidean (n - 1)) :
    Continuous (fun z : ParameterSpace ↦ unitPeriodPartialIntegral φ (WithLp.toLp 2 (z, η))) := by
  let f := unitPeriodPhysicalSchwartz φ
  have hc : HasCompactSupport (f : InitialSpace n → ℂ) :=
    φ.property.2.comp_homeomorph (initialCoordinatesLinear n).symm.toHomeomorph
  let K : Set (Euclidean (n - 1)) := WithLp.snd '' tsupport (f : InitialSpace n → ℂ)
  have hK : IsCompact K := hc.image (by fun_prop)
  have hs (z : ParameterSpace) (y : Euclidean (n - 1)) (hy : y ∉ K) :
      f (WithLp.toLp 2 (z, y)) = 0 := by
    by_contra h
    apply hy
    exact ⟨WithLp.toLp 2 (z, y), subset_tsupport _ h, rfl⟩
  change Continuous (fun z : ParameterSpace ↦ 𝓕 (fun y ↦ f (WithLp.toLp 2 (z, y))) η)
  simp only [Real.fourier_eq]
  rw [← continuousOn_univ]
  apply continuousOn_integral_of_compact_support hK
  · exact (by fun_prop : Continuous (fun p : ParameterSpace × Euclidean (n - 1) ↦
      Real.fourierChar (-⟪p.2, η⟫) • f (WithLp.toLp 2 p))).continuousOn
  · intro z y _ hy
    rw [hs z y hy, smul_zero]

/-- The compact parameter support of the physical test makes every
frequency slice of the partial transform integrable in the parameters
(`app:ch_background:prop:bg-adjoint`). -/
theorem integrable_unitPeriodPartialIntegral_parameter (φ : carrierInitialTestSpace n) (η : Euclidean (n - 1)) :
    Integrable (fun z : ParameterSpace ↦ unitPeriodPartialIntegral φ (WithLp.toLp 2 (z, η))) := by
  let f := unitPeriodPhysicalSchwartz φ
  have hc : HasCompactSupport (f : InitialSpace n → ℂ) :=
    φ.property.2.comp_homeomorph (initialCoordinatesLinear n).symm.toHomeomorph
  apply (continuous_unitPeriodPartialIntegral_parameter φ η).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (hc.image (by fun_prop : Continuous
    (WithLp.fst : InitialSpace n → ParameterSpace)))
  intro z hz
  by_contra h
  have hs (y : Euclidean (n - 1)) : f (WithLp.toLp 2 (z, y)) = 0 := by
    by_contra hy
    exact h ⟨WithLp.toLp 2 (z, y), subset_tsupport _ hy, rfl⟩
  apply hz
  change 𝓕 (fun y ↦ f (WithLp.toLp 2 (z, y))) η = 0
  simp [hs, Real.fourier_eq]

/-- Inverting the parameter frequencies of the full Schwartz transform
recovers the literal partial Fourier integral pointwise. This supplies the
identification, independently of the joint Schwartz bounds, for
`exists_unitPeriodSchwartz_compactSmooth`
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem unitPeriod_inverseParameter_fullFourier (φ : carrierInitialTestSpace n) (x : InitialSpace n) :
    𝓕⁻ (unitPeriodParameterSlice (𝓕 (unitPeriodPhysicalSchwartz φ)) x.snd) x.fst =
      unitPeriodPartialIntegral φ x := by
  have he : (unitPeriodParameterSlice (𝓕 (unitPeriodPhysicalSchwartz φ)) x.snd :
      ParameterSpace → ℂ) =
      𝓕 (fun z : ParameterSpace ↦ unitPeriodPartialIntegral φ (WithLp.toLp 2 (z, x.snd))) := by
    funext z
    exact unitPeriod_fullFourier_eq_iterated (unitPeriodPhysicalSchwartz φ) (WithLp.toLp 2 (z, x.snd))
  rw [SchwartzMap.fourierInv_coe, he]
  rw [(continuous_unitPeriodPartialIntegral_parameter φ x.snd).fourierInv_fourier_eq
    (integrable_unitPeriodPartialIntegral_parameter φ x.snd) (he ▸ (unitPeriodParameterSlice
      (𝓕 (unitPeriodPhysicalSchwartz φ)) x.snd).integrable)]
  rfl

/-- A constructed Schwartz cutoff leaves the partial transform unchanged,
since the physical test has compact parameter support. This is the cutoff
used by `exists_unitPeriodCutoffKernel_representation`
(`app:ch_background:prop:bg-adjoint`). -/
theorem exists_unitPeriodParameterCutoff (φ : carrierInitialTestSpace n) :
    ∃ χ : 𝓢(ParameterSpace, ℂ), ∀ x : InitialSpace n,
      χ x.fst * unitPeriodPartialIntegral φ x = unitPeriodPartialIntegral φ x := by
  let f := unitPeriodPhysicalSchwartz φ
  have hc : HasCompactSupport (f : InitialSpace n → ℂ) :=
    φ.property.2.comp_homeomorph (initialCoordinatesLinear n).symm.toHomeomorph
  let K : Set ParameterSpace := WithLp.fst '' tsupport (f : InitialSpace n → ℂ)
  have hK : IsCompact K := hc.image (by fun_prop)
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn (f := id) continuous_id.continuousOn
  let b : ContDiffBump (0 : ParameterSpace) :=
    ⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩
  let χ : 𝓢(ParameterSpace, ℂ) :=
    (b.hasCompactSupport.smul_right (f' := fun _ ↦ (1 : ℂ))).toSchwartzMap
      (b.contDiff.smul contDiff_const)
  refine ⟨χ, fun x ↦ ?_⟩
  by_cases hx : x.fst ∈ K
  · have hb : b x.fst = 1 := by
      apply b.one_of_mem_closedBall
      change dist x.fst 0 ≤ max R 0 + 1
      rw [dist_zero_right]
      exact (hR _ hx).trans ((le_max_left R 0).trans (by linarith))
    change (b x.fst • (1 : ℂ)) * _ = _
    rw [hb, one_smul, one_mul]
  · have hs (y : Euclidean (n - 1)) : f (WithLp.toLp 2 (x.fst, y)) = 0 := by
      by_contra hy
      exact hx ⟨WithLp.toLp 2 (x.fst, y), subset_tsupport _ hy, rfl⟩
    have hz : unitPeriodPartialIntegral φ x = 0 := by
      change 𝓕 (fun y ↦ f (WithLp.toLp 2 (x.fst, y))) x.snd = 0
      simp [hs, Real.fourier_eq]
    rw [hz, mul_zero]

/-- The actual partial transform is the integral of a constructed oscillatory
kernel. Joint Schwartz bounds for this kernel and preservation under
integration are still required for `exists_unitPeriodSchwartz_compactSmooth`;
this identity alone makes no Schwartz-preservation claim
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem exists_unitPeriodCutoffKernel_representation (φ : carrierInitialTestSpace n) :
    ∃ χ : 𝓢(ParameterSpace, ℂ), ∀ x : InitialSpace n,
      (∫ z : ParameterSpace,
        unitPeriodCutoffKernel χ (𝓕 (unitPeriodPhysicalSchwartz φ)) (x, z)) =
      unitPeriodPartialIntegral φ x := by
  obtain ⟨χ, hχ⟩ := exists_unitPeriodParameterCutoff φ
  refine ⟨χ, fun x ↦ ?_⟩
  rw [integral_unitPeriodCutoffKernel, unitPeriod_inverseParameter_fullFourier, hχ]

end JanetCartan.ContinuumAdjoint.DensityMultiplier
