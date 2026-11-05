module

public import JanetCartan.Iteration.PhysicalMean.CanonicalCoreStrain

/-!
# Exact residual of the same initialized physical field

Consumer: the source forcing from new:eq:mean-source and the completed mean
error transfer. The literal initialized raw sum, full base plus canonical
family, same source operators and source representative are kept throughout.
The initial forcing/background term remains explicit, so this theorem does
not assume the desired source profile or the background cancellation. That
cancellation is produced by PhysicalBackground.physicalDensityMean_core_cancellation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean
open CurrentMean SmoothPeriodicFamily CanonicalChange ContinuumRow CarrierSobolev
  ProjectedStressFrame PhysicalBackground

/-- Actual source residual equals the full physical residual with its explicit
initial forcing term. The linear-response and quadratic identities are proved
internally on the original plateau, not assumed. Substituting the original
continuum cancellation and `g=r_init+C(eR/b²)` removes precisely the displayed
initial term (`new:eq:reduced-mean-identity`). -/
theorem fixedSourceResidual_eq_initializedCoreDefect
    {n N : ℕ} {ι ν : Type*} [Fintype ι] [Fintype ν]
    {Raw : ι → Type*} [∀ i, NormedAddCommGroup (Raw i)]
    [∀ i, InnerProductSpace ℝ (Raw i)] [∀ i, CompleteSpace (Raw i)]
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, IsSmoothPeriodic (c j : Torus n → ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ))
    (hm : IsSmoothPeriodic (χmeas : Torus n → ℝ))
    (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ)) (hψ : IsSmoothPeriodic (ψ : Torus n → ℝ))
    (U : ν → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (Q₀ : OutputL2 n →L[ℝ] OutputL2 n)
    (hreg : ∀ (e : SmoothResidual n) (s : ℕ),
      (augmentedRow (imageChannel c χmeas χsrc) U ψ).adjoint
        (Q₀ (smoothResidualToL2 n e)) ∈ augmentedInputLevel n ν s)
    (μ : ι → ℝ) (base : SmoothPeriodicFamily n ι (Matrix (Fin N) (Fin n) ℂ))
    (C : Torus n → MetricTensor n →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (A : ∀ i, Raw i →L[ℝ] OutputL2 n)
    (G : ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (initial : AugmentedInput n ν) (hi : ∀ s, initial ∈ augmentedInputLevel n ν s)
    {F : Euclidean n → Euclidean N} (X₀ : Euclidean n → Euclidean n)
    {W core : Set (Euclidean n)} (hW : IsOpen W) (hcore : IsOpen core) (hsub : core ⊆ W)
    (hF : ContDiffOn ℝ ∞ F W) (hX₀ : ContDiffOn ℝ ∞ X₀ W)
    (himm : IsImmersionOn F W) (hrank : HasFullNormalRankOn F W)
    (hcoeff : ∀ x ∈ core, ∀ j, c j (torusQuotient x) = GeometricProfile.geometricReducedCoefficients F x j)
    (hmeas : ∀ x ∈ core, χmeas (torusQuotient x) = 1)
    (hext : ∀ x ∈ core, ψ (torusQuotient x) = 1)
    (hCeq : ∀ x ∈ core, ∀ T i, C (torusQuotient x) T i = tensorPairing (projectedStress F x i) T)
    (g e : SmoothResidual n) {x : Euclidean n} (hx : x ∈ core) (i : Fin n) :
    let E := fixedSourceLinear c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg μ base C hC A G
    let Q := fixedSourceQuadratic μ C hC A G Q₀
    let change := (augmentedRow (imageChannel c χmeas χsrc) U ψ).adjoint (Q₀ (smoothResidualToL2 n e))
    (sourceResidual E Q g e).val (torusQuotient x) () i =
      g.val (torusQuotient x) () i + tensorPairing (projectedStress F x i)
        (linearizedMetric F (baseVariation χsrc initial F X₀) x + weightedHermitianTensor μ base.val (torusQuotient x)) -
      tensorPairing (projectedStress F x i)
        (linearizedMetric F (baseVariation χsrc (initial+change) F X₀) x +
          weightedHermitianTensor μ (base+fixedSourceDerivative A G Q₀ e).val (torusQuotient x)) := by
  intro E Q change
  let aux := preparationAuxiliaryField χsrc
    ((imageChannel c χmeas χsrc).adjoint (Q₀ (smoothResidualToL2 n e))) F (fun _ ↦ 1)
  have him (s : ℕ) : (imageChannel c χmeas χsrc).adjoint (Q₀ (smoothResidualToL2 n e)) ∈
      periodicSobolevLevel n (Euclidean n) s := by
    rw [← AuxiliaryRawBand.augmentedAdjoint_image (imageChannel c χmeas χsrc) U ψ]
    exact ((mem_augmentedInputLevel_iff s _).mp (hreg e s)).1
  have hfield : baseVariation χsrc (initial+change) F X₀ = baseVariation χsrc initial F X₀ + aux := by
    simpa only [change, aux, AuxiliaryRawBand.augmentedAdjoint_image] using
      baseVariation_add_eq_same_auxiliary χsrc hs initial change hi (hreg e) F X₀
  have hbase := contDiffOn_baseVariation χsrc hs initial hi hW hF hX₀ himm
  have haux : ContDiffOn ℝ ∞ aux W :=
    contDiffOn_preparationAuxiliaryField χsrc hs _ him hW hF himm contDiffOn_const
  have hstrain : linearizedMetric F (baseVariation χsrc (initial+change) F X₀) x =
      linearizedMetric F (baseVariation χsrc initial F X₀) x+linearizedMetric F aux x := by
    rw [hfield]
    exact linearizedMetric_add_apply
      ((hbase.contDiffAt (hW.mem_nhds (hsub hx))).differentiableAt (by simp))
      ((haux.contDiffAt (hW.mem_nhds (hsub hx))).differentiableAt (by simp))
  have hlinear := fixedSourceLinear_eq_strain_add_cross_on_core c hc χmeas χsrc ψ hm hs hψ
    U Q₀ hreg μ base C hC A G hW hcore hsub hF himm hrank hcoeff hmeas hext hCeq e hx i
  have hpairAdd (S T : MetricTensor n) : tensorPairing (projectedStress F x i) (S+T) =
      tensorPairing (projectedStress F x i) S + tensorPairing (projectedStress F x i) T := by
    simp only [tensorPairing, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  have hpairSub (S T : MetricTensor n) : tensorPairing (projectedStress F x i) (S-T) =
      tensorPairing (projectedStress F x i) S - tensorPairing (projectedStress F x i) T := by
    simp only [tensorPairing, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have hself := congrArg (fun T : Torus n → MetricTensor n ↦ tensorPairing (projectedStress F x i) (T (torusQuotient x)))
    (weightedHermitianTensor_add_sub μ base.val (fixedSourceDerivative A G Q₀ e).val)
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, hpairAdd, hpairSub] at hself
  change g.val (torusQuotient x) () i -
    (fixedSourceLinear c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg μ base C hC A G e).val (torusQuotient x) () i -
    (fixedSourceQuadratic μ C hC A G Q₀ e e).val (torusQuotient x) () i = _
  rw [hlinear, fixedSourceQuadratic_self_apply, hCeq x hx, hstrain]
  change g.val (torusQuotient x) () i - tensorPairing (projectedStress F x i)
    (linearizedMetric F aux x+(2 : ℝ) • weightedHermitianBilinear μ base.val
      (fixedSourceDerivative A G Q₀ e).val (torusQuotient x)) - _ = _
  simp only [Submodule.coe_add, hpairAdd]
  linarith only [hself]

end JanetCartan.PhysicalMean
