module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.Smooth.Correction
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.LocalParameters
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.FiberMaps

/-!
# Every compact test source in the fixed inverse domain

The existing Lebesgue-preserving retarded coordinates and their proved norm
comparison admit every compact smooth test to the original restriction scale.
A fixed real fibre map includes both quadratures and every reduced component.
The source is not an atomic subfamily: every test is admitted with one constant
at each order, for the source-continuity step of
`app:ch_response:thm:response-literal-transfer`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped ContDiff
namespace JanetCartan.FixedDomainInverse
open LocalSobolev ResponseTransfer RetardedSobolev.Spaces

variable {d : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
local notation "E" => Euclidean (d + 1)

/-- Restrict the original scalar test to the unchanged Lebesgue domain, in
its fixed physical coordinates (`app:ch_response:thm:response-literal-transfer`). -/
def retardedScalarTestRestriction (W : Set E) : Test d →ₗ[ℝ] LocalL2 W ℂ where
  toFun f := ((memLp_retardedTestFunction f).restrict W).toLp (retardedTestFunction f)
  map_add' f g := by
    change ((memLp_retardedTestFunction (f+g)).restrict W).toLp _ = _
    have he : retardedTestFunction (f+g) = retardedTestFunction f + retardedTestFunction g := rfl
    simp only [he]
    exact MemLp.toLp_add ((memLp_retardedTestFunction f).restrict W)
      ((memLp_retardedTestFunction g).restrict W)
  map_smul' a f := by
    change ((memLp_retardedTestFunction (a • f)).restrict W).toLp _ = _
    have he : retardedTestFunction (a • f) = a • retardedTestFunction f := rfl
    simp only [he]
    exact MemLp.toLp_const_smul a ((memLp_retardedTestFunction f).restrict W)

/-- The literal local L² source, with its original physical coordinates and
Lebesgue measure (`app:ch_regular:thm:exact-correction`). The real fibre map
is fixed before the source and can be either scalar quadrature in any channel. -/
def retardedTestSourceL2 (W : Set E) (L : ℂ →L[ℝ] F) : Test d →ₗ[ℝ] LocalL2 W F :=
  (L.compLpL 2 (volume.restrict W)).toLinearMap.comp (retardedScalarTestRestriction W)

omit [FiniteDimensional ℝ F] in
/-- The admitted L² class has exactly the prescribed physical representative
(`app:ch_response:thm:response-literal-transfer`). -/
theorem retardedTestSourceL2_coeFn (W : Set E) (L : ℂ →L[ℝ] F) (f : Test d) :
    retardedTestSourceL2 W L f =ᵐ[volume.restrict W]
      fun y ↦ L (f.val (retardedCoordinates d y)) := by
  filter_upwards [L.coeFn_compLpL (retardedScalarTestRestriction W f),
    ((memLp_retardedTestFunction f).restrict W).coeFn_toLp] with y hy hf
  exact hy.trans (congrArg L hf)

private def retardedTestSourceExtension (W : Set E) (L : ℂ →L[ℝ] F)
    (s : ℕ) (f : Test d) : SobolevExtension W s (retardedTestSourceL2 W L f) := by
  let e := (retardedTestToLocalL2_mem f s).some
  let eL := e.mapCLM L
  have he : e.toFun =ᵐ[volume] retardedTestFunction f := by
    simpa only [Measure.restrict_univ] using e.restrict_eq.trans (retardedTestToLocalL2_ae f)
  refine { eL with restrict_eq := ?_ }
  exact Filter.EventuallyEq.trans (ae_restrict_of_ae (he.fun_comp L))
    (retardedTestSourceL2_coeFn W L f).symm

/-- All smooth compact tests belong to every original restriction level,
with a bound in the existing finite retarded source-jet norm. Constants precede
the measurement domain, fibre map and every source
(`app:ch_response:thm:response-literal-transfer`, `app:not:fourier`). -/
theorem exists_retardedTestSourceL2_sobolev_constants :
    ∃ D : ℕ → ℝ, (∀ s, 0 ≤ D s) ∧
      ∀ (W : Set E) (L : ℂ →L[ℝ] F) (s : ℕ) (f : Test d),
        MemRestrictionSobolev W s (retardedTestSourceL2 W L f) ∧
          restrictionSobolevNorm W s (retardedTestSourceL2 W L f) ≤
            (‖L‖ * D s) * ‖ofTest s volume f‖ := by
  choose D hD hb using exists_retardedTestToLocalL2_gradeNorm_le_mul_ofTest_norm d
  refine ⟨D, hD, ?_⟩
  intro W L s f
  let e := (retardedTestToLocalL2_mem f s).some
  have he := (e.jetNorm_mapCLM_le L)
  have hgrade := hb s f
  rw [retardedTestToLocalL2_gradeNorm_eq_jetL2Norm] at hgrade
  rw [← retardedTest_extension_jetNorm_eq f e] at hgrade
  refine ⟨⟨retardedTestSourceExtension W L s f⟩,
    (restrictionSobolevNorm_le (retardedTestSourceExtension W L s f)).trans ?_⟩
  change (e.mapCLM L).jetNorm ≤ _
  exact he.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hgrade (norm_nonneg L))

/-- One real linear admission map into the existing smooth-source subspace,
used by the same fixed inverse at every order. All membership obligations are
proved above; no source-regularity field is assumed
(`app:ch_regular:thm:exact-correction`). -/
def retardedTestSmoothSource (W : Set E) (L : ℂ →L[ℝ] F) :
    Test d →ₗ[ℝ] smoothSource W F :=
  (retardedTestSourceL2 W L).codRestrict (smoothSource W F) fun f s ↦
    (exists_retardedTestSourceL2_sobolev_constants (d := d) (F := F)).choose_spec.2
      W L s f |>.1

/-- The admitted smooth source retains the literal L² class
(`app:ch_regular:thm:exact-correction`). -/
@[simp] theorem retardedTestSmoothSource_coe (W : Set E) (L : ℂ →L[ℝ] F) (f : Test d) :
    (retardedTestSmoothSource W L f : LocalL2 W F) = retardedTestSourceL2 W L f := rfl

omit [FiniteDimensional ℝ F] in
/-- The original supported source is retained under the fixed coordinate
conversion and real fibre map. This is the support needed by the parameter
and source-superposition consumers (`app:ch_response:cor:current-atoms`). -/
theorem retardedTestSmoothSource_tsupport_subset
    (L : ℂ →L[ℝ] F) {K : Set (ℝ × (Fin d → ℝ))} (hK : IsClosed K)
    (f : supportedTests K) :
    tsupport (fun y : E ↦ L (f.val.val (retardedCoordinates d y))) ⊆
      retardedCoordinates d ⁻¹' K := by
  apply closure_minimal _ (hK.preimage (retardedCoordinates d).continuous)
  intro y hy
  by_contra hn
  apply hy
  have hz : f.val.val (retardedCoordinates d y) = 0 :=
    image_eq_zero_of_notMem_tsupport fun hs ↦ hn (f.property hs)
  change L (f.val.val (retardedCoordinates d y)) = 0
  rw [hz, map_zero]

/-- When the original source support lies in the fixed measurement domain,
zero extension of its admitted class recovers the same whole-space source.
This identifies the source used by the inverse with the source used in
finite-band superposition (`app:ch_regular:eq:inverse-remainder`,
`app:ch_response:thm:response-literal-transfer`). -/
theorem retardedTestSmoothSource_zeroExtend_coeFn
    {W : Set E} (hW : MeasurableSet W) (L : ℂ →L[ℝ] F)
    {K : Set (ℝ × (Fin d → ℝ))} (hK : IsClosed K)
    (hKW : retardedCoordinates d ⁻¹' K ⊆ W) (f : supportedTests K) :
    SmallSupport.zeroExtend hW (retardedTestSmoothSource W L f.val : LocalL2 W F)
      =ᵐ[volume] fun y ↦ L (f.val.val (retardedCoordinates d y)) := by
  have he := (ae_restrict_iff' hW).mp (retardedTestSourceL2_coeFn W L f.val)
  have hs := retardedTestSmoothSource_tsupport_subset L hK f
  filter_upwards [SmallSupport.zeroExtend_coeFn hW
    (retardedTestSmoothSource W L f.val : LocalL2 W F), he] with y hy hey
  rw [hy]
  by_cases hyW : y ∈ W
  · exact (indicator_of_mem hyW _).trans (hey hyW)
  · rw [indicator_of_notMem hyW]
    exact (image_eq_zero_of_notMem_tsupport (fun hz ↦ hyW (hKW (hs hz)))).symm

end JanetCartan.FixedDomainInverse
