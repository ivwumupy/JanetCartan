module

public import JanetCartan.Iteration.PhysicalMean.CanonicalSource
public import JanetCartan.Iteration.PhysicalBackground.Field

/-!
# The actual source operator is physical strain only on the original core

Consumer: the reduced physical residual in PhysicalMean.Completion and the
SAME fixed-cutoff finite Picard run. The full auxiliary output is retained
globally; its exterior summand vanishes only on the prescribed plateau.
The measured cross response has its literal factor two, whereas the full
quadratic self tensor has factor one. No linear-response success premise,
new initializer, or cut inverse is introduced.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean
open CurrentMean SmoothPeriodicFamily CanonicalChange ContinuumRow CarrierSobolev
  ProjectedStressFrame

variable {n N : ℕ} {ι : Type*} [Fintype ι]
    {Raw : ι → Type*} [∀ i, NormedAddCommGroup (Raw i)]
    [∀ i, InnerProductSpace ℝ (Raw i)] [∀ i, CompleteSpace (Raw i)]

/-- The actual full quadratic source is the measured Hermitian self tensor,
with factor ONE and every original sample/cross-shell term (`new:eq:mean-operators`). -/
theorem fixedSourceQuadratic_self_apply (μ : ι → ℝ)
    (C : Torus n → MetricTensor n →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (A : ∀ i, Raw i →L[ℝ] OutputL2 n)
    (G : ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (e : SmoothResidual n) (z : Torus n) :
    (fixedSourceQuadratic μ C hC A G Q₀ e e).val z () =
      C z (weightedHermitianTensor μ (fixedSourceDerivative A G Q₀ e).val z) := by
  change C z (∑ i, μ i • mixedHermitianTensor
    ((fixedSourceDerivative A G Q₀ e).val z i) ((fixedSourceDerivative A G Q₀ e).val z i)) = _
  simp only [mixedHermitianTensor_self, weightedHermitianTensor]

/-- The actual fixed source E is the strain of the SAME uncut image update
plus its FULL measured cross response. The original exterior output is NOT
identified with strain globally: the statement is restricted to the given
common plateau (`new:eq:reduced-mean-identity`). -/
theorem fixedSourceLinear_eq_strain_add_cross_on_core {ν : Type*} [Fintype ν]
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
    {F : Euclidean n → Euclidean N} {W core : Set (Euclidean n)}
    (hW : IsOpen W) (hcore : IsOpen core) (hsub : core ⊆ W)
    (hF : ContDiffOn ℝ ∞ F W) (himm : IsImmersionOn F W) (hrank : HasFullNormalRankOn F W)
    (hcoeff : ∀ x ∈ core, ∀ j, c j (torusQuotient x) = GeometricProfile.geometricReducedCoefficients F x j)
    (hmeas : ∀ x ∈ core, χmeas (torusQuotient x) = 1)
    (hext : ∀ x ∈ core, ψ (torusQuotient x) = 1)
    (hCeq : ∀ x ∈ core, ∀ T i, C (torusQuotient x) T i = tensorPairing (projectedStress F x i) T)
    (e : SmoothResidual n) {x : Euclidean n} (hx : x ∈ core) (i : Fin n) :
    (fixedSourceLinear c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg μ base C hC A G e).val (torusQuotient x) () i =
      tensorPairing (projectedStress F x i)
        (linearizedMetric F (preparationAuxiliaryField χsrc
          ((imageChannel c χmeas χsrc).adjoint (Q₀ (smoothResidualToL2 n e))) F (fun _ ↦ 1)) x +
        (2 : ℝ) • weightedHermitianBilinear μ base.val (fixedSourceDerivative A G Q₀ e).val (torusQuotient x)) := by
  have him (s : ℕ) : (imageChannel c χmeas χsrc).adjoint (Q₀ (smoothResidualToL2 n e)) ∈
      periodicSobolevLevel n (Euclidean n) s := by
    rw [← AuxiliaryRawBand.augmentedAdjoint_image (imageChannel c χmeas χsrc) U ψ]
    exact ((mem_augmentedInputLevel_iff s _).mp (hreg e s)).1
  have hout (s : ℕ) : exteriorChannel ψ (Q₀ (smoothResidualToL2 n e)) ∈
      periodicSobolevLevel n (Euclidean n) s := by
    rw [← AuxiliaryRawBand.augmentedAdjoint_exterior (imageChannel c χmeas χsrc) U ψ]
    exact ((mem_augmentedInputLevel_iff s _).mp (hreg e s)).2.2
  have haux := uncutAuxiliaryRepresentative_eq_strain_on_core c hc χmeas χsrc ψ hm hs hψ
    ((imageChannel c χmeas χsrc).adjoint (Q₀ (smoothResidualToL2 n e)))
    (exteriorChannel ψ (Q₀ (smoothResidualToL2 n e))) him hout
    hW hcore hsub hF himm (χout := fun _ ↦ 1) (fun _ _ ↦ rfl) hcoeff hmeas hext hx i
  have hstress := ImageGeometry.geometricCubeStress_val_eq_projectedStress
    ((hF.contDiffAt (hW.mem_nhds (hsub hx))).of_le (by simp)) (hrank x (hsub hx)) i
  rw [hstress] at haux
  have hcross := congrArg (fun f : SmoothResidual n ↦ f.val (torusQuotient x) () i)
    (smoothCanonicalResponse_eq_measured_cross μ base C hC A G Q₀ (smoothResidualToL2 n e))
  change (uncutAuxiliaryRepresentative c hc χmeas χsrc ψ hm hs hψ _ _ him hout).val
    (torusQuotient x) () i +
    (smoothCanonicalResponse μ A (smoothRawCrossResponse base C hC G) Q₀ (smoothResidualToL2 n e)).val
      (torusQuotient x) () i = _
  rw [haux, hcross]
  change _ + C (torusQuotient x)
    ((2 : ℝ) • weightedHermitianBilinear μ base.val (fixedSourceDerivative A G Q₀ e).val
      (torusQuotient x)) i = _
  rw [hCeq x hx]
  simp only [tensorPairing, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

private theorem sourceCovector_add (χsrc : C(Torus n, ℝ))
    (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ)) (u v : OutputL2 n)
    (hu : ∀ s, u ∈ periodicSobolevLevel n (Euclidean n) s)
    (hv : ∀ s, v ∈ periodicSobolevLevel n (Euclidean n) s) :
    preparationCovector χsrc (u+v) = preparationCovector χsrc u + preparationCovector χsrc v := by
  have huv (s : ℕ) : u+v ∈ periodicSobolevLevel n (Euclidean n) s :=
    (periodicSobolevLevel n (Euclidean n) s).add_mem (hu s) (hv s)
  have hsmooth := isSmoothPeriodic_preparationCovector χsrc hs (u+v) huv
  have husmooth := isSmoothPeriodic_preparationCovector χsrc hs u hu
  have hvsmooth := isSmoothPeriodic_preparationCovector χsrc hs v hv
  have hsum := preparationCovector_ae χsrc hs (u+v) huv
  rw [map_add, map_add] at hsum
  have he : preparationCovector χsrc (u+v) =ᵐ[volume]
      preparationCovector χsrc u + preparationCovector χsrc v := by
    filter_upwards [hsum, preparationCovector_ae χsrc hs u hu,
      preparationCovector_ae χsrc hs v hv,
      Lp.coeFn_add (periodicBesselInverse (cutoffMultiplier χsrc u))
        (periodicBesselInverse (cutoffMultiplier χsrc v))] with x hsum hu hv hadd
    change _ = preparationCovector χsrc u x + preparationCovector χsrc v x
    rw [← hsum, hadd, Pi.add_apply, hu, hv]
  exact Measure.eq_of_ae_eq he hsmooth.1 (husmooth.1.add hvsmooth.1)

/-- The literal initialized raw sum gives the SAME physical base plus its
uncut auxiliary image field. Both raw representatives have genuine Sobolev
membership; no independently chosen initializer or inverse is identified
(`new:eq:reduced-mean-identity`). -/
theorem baseVariation_add_eq_same_auxiliary {ν : Type*} [Fintype ν]
    (χsrc : C(Torus n, ℝ)) (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (initial change : AugmentedInput n ν)
    (hi : ∀ s, initial ∈ augmentedInputLevel n ν s)
    (hd : ∀ s, change ∈ augmentedInputLevel n ν s)
    (F : Euclidean n → Euclidean N) (X₀ : Euclidean n → Euclidean n) :
    PhysicalBackground.baseVariation χsrc (initial+change) F X₀ =
      PhysicalBackground.baseVariation χsrc initial F X₀ +
        preparationAuxiliaryField χsrc change.fst.fst F (fun _ ↦ 1) := by
  have hcov := sourceCovector_add χsrc hs initial.fst.fst change.fst.fst
    (fun s ↦ ((mem_augmentedInputLevel_iff s initial).mp (hi s)).1)
    (fun s ↦ ((mem_augmentedInputLevel_iff s change).mp (hd s)).1)
  funext x
  change PositiveBackground.tangentVariation F X₀ x + AuxiliaryRealization.tangentialField F
      (periodicLift (preparationCovector χsrc (initial.fst.fst+change.fst.fst))) x = _
  rw [hcov]
  simp only [PhysicalBackground.baseVariation, preparationAuxiliaryField,
    AuxiliaryRealization.tangentialField, tangentLift, periodicLift, Function.comp_apply, Pi.add_apply,
    Pi.smul_apply, PiLp.add_apply, mul_add, add_smul, Finset.sum_add_distrib, smul_add, one_smul]
  abel

end JanetCartan.PhysicalMean
