module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.FixedSolver
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Stress.Reduced.Formula
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.WeakEquation

/-!
# The complete residual of the same fixed smooth solver

The physical equation and right-hand side exported by
`FixedDomainInverse.exists_finite_direct_smooth_fixed_inverse` are connected to
the geometric full strain. The geometric principal pencil and the entire
Christoffel contraction are used literally. The original corrected L² source
and paired angular source discrepancy remain in the residual; no identity
angular operator is substituted.

The consumers are the corrected-atom strain assertion and the actual
`UniformHistoryCorrection` producer. Actual stationary-family selection and
the quantitative residual estimate are still external producer obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.CorrectedAtoms
open CharacteristicTransport.CompleteResidual NullTransport GeometricProfile
open PrimarySourceAdmission AmbientResponse FixedDomainInverse LocalSobolev ResponseSourceExtension

/-- The direct solver's physical action is the actual covariant reduced strain,
including the negative Christoffel contraction. This identifies the accepted
physical equation with the ambient reconstruction consumer
(`app:ch_waves:eq:reduced-symbol`, `app:ch_regular:eq:exact-physical`). -/
theorem physicalWeakApply_geometric_eq {n N : ℕ} (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n)
    {u : Euclidean n → Euclidean n} {x : Euclidean n}
    (hQ : ∀ i, (Q x i).IsSymm) (hu : DifferentiableAt ℝ u x) (i : Fin n) :
    physicalWeakApply
      (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1))
      (fun y ↦ reducedZerothCoefficient F (Q y) y)
      (fun y ↦ (euclideanComplexInclusion (u y)).ofLp)
      (fderiv ℝ (fun y ↦ (euclideanComplexInclusion (u y)).ofLp)) x i =
      (reducedOperator F Q u x i : ℂ) := by
  have hv (j : Fin n) : DifferentiableAt ℝ (fun y ↦ (u y j : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x ((differentiableAt_piLp 2).mp hu j)
  have hd (j : Fin n) : fderiv ℝ (fun y ↦ (u y j : ℂ)) x =
      Complex.ofRealCLM.comp (fderiv ℝ (fun y ↦ u y j) x) :=
    (Complex.ofRealCLM.hasFDerivAt.comp x
      (((differentiableAt_piLp 2).mp hu j).hasFDerivAt)).fderiv
  have hp (a j : Fin n) : ActualCarriers.pencil (Q x) (EuclideanSpace.single a 1) i j =
      principalCoefficient (Q x) a i j := by
    simp [ActualCarriers.pencil, principalCoefficient, (hQ i).apply j a]
  rw [reducedOperator_eq_coefficients F Q u x hQ]
  change physicalWeakApply _ _ (fun y j ↦ (u y j : ℂ))
    (fderiv ℝ (fun y j ↦ (u y j : ℂ))) x i = _
  simp [physicalWeakApply, fderiv_pi hv, hd, hp, partialDeriv, Complex.real_smul]

variable {n N : ℕ} (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
    {S U W core chart O : Set (Euclidean n)} (hU : IsOpen U)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U)

/-- Inverse-Gram reconstruction of the SAME smooth fixed solver's complete
right-hand side. The sole differential equation input is precisely the
pointwise physical equation exported by the accepted direct inverse
(`app:ch_response:eq:response-full-identity`). -/
theorem fixedSmoothSolverAmbientExtension_error_eq_inverseGram
    (solver right : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v)) (Ξ : OutputCutoff core chart)
    (hchart : IsOpen chart) (hF : ContDiffOn ℝ ∞ F chart)
    (hi : IsImmersionOn F chart) (hrank : HasFullNormalRankOn F chart)
    (hphysical : ∀ v, EqOn (physicalWeakApply
      (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1))
      (fun y ↦ reducedZerothCoefficient F (Q y) y)
      (fun y ↦ (euclideanComplexInclusion (solver v y)).ofLp)
      (fderiv ℝ (fun y ↦ (euclideanComplexInclusion (solver v y)).ofLp)))
      (fun y ↦ (euclideanComplexInclusion (right v y)).ofLp) O)
    (h : compactSmoothSources S) {x : Euclidean n} (hx : x ∈ core) (hxO : x ∈ O)
    (hsymm : ((h : MetricField n) x).IsSymm) (hQsymm : ∀ i, (Q x i).IsSymm)
    (hQlin : LinearIndependent ℝ (Q x))
    (hspan : (Submodule.span ℝ (range (Q x)) : Set (MetricTensor n)) = stressSpace F x) :
    linearizedMetric F
      (fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ h) x -
        (h : MetricField n) x =
      (2 : ℝ) • ∑ i, ∑ j, ((stressGram (Q x))⁻¹ i j *
        (right (cutoffStressSmoothSource Q η hU hQ hη hSU h) x j -
          stressSource Q h x j)) • Q x i := by
  let v := cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU h
  have hξ : x ∈ {y | Ξ.toFun y = 1} := interior_subset (Ξ.plateau hx)
  have hxc : x ∈ chart := Ξ.support_chart (subset_tsupport _ (by
    change Ξ.toFun x ≠ 0
    rw [show Ξ.toFun x = 1 from hξ]
    exact one_ne_zero))
  have hu : ContDiffOn ℝ ∞ (solver v) chart := (hsolver v).contDiffOn
  have hp (j : Fin n) : tensorPairing (Q x j) (symmCovariantDeriv F (solver v) x) =
      right v x j := by
    have he := congrFun (hphysical v hxO) j
    rw [physicalWeakApply_geometric_eq F Q hQsymm
      ((hsolver v).differentiable (by simp) x)] at he
    exact Complex.ofReal_injective (by
      simpa only [reducedOperator, euclideanComplexInclusion_apply] using he)
  have hw := contDiffOn_canonicalNormalCompletion hchart hF
    ((contDiffOn_symmCovariantDeriv hchart hF hu hi).sub
      (h.property.1.contDiffOn.const_smul (1 / 2 : ℝ))) hi hrank
  have he := strain_error_eq_inverseGram hchart hF hu hw hi
    (fun y _ ↦ canonicalNormalCompletion_mem_normalSpace F y _) hxc hsymm
    (canonicalNormalCompletion_normal_equation (hrank x hxc) _) hQlin hspan
  change linearizedMetric F (completedVariation F (solver v) h) x -
    (h : MetricField n) x = _ at he
  rw [linearizedMetric_fixedSmoothSolverAmbientExtension_eq
    F Q η hU hQ hη hSU solver hsolver Ξ h hx]
  simp only [hp] at he
  exact he

omit F in
/-- For the SAME admitted source, the direct inverse's right-hand side minus
the original stress is the entire paired angular discrepancy on its original
corrected L² class. This discharges source identification in the preceding
full-strain formula; the angular discrepancy is not discarded
(`app:ch_regular:eq:exact-physical`, `app:ch_response:eq:response-full-identity`). -/
theorem smoothRight_cutoffStress_residual_ae
    (right : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (Corr : LocalL2 W (Euclidean n) →L[ℝ] LocalL2 W (Euclidean n))
    (A : Lp (Euclidean n) 2 (volume : Measure (Euclidean n)) →L[ℝ]
      Lp (Euclidean n) 2 (volume : Measure (Euclidean n)))
    (hW : MeasurableSet W) (hSW : S ⊆ W) (hplateau : S ⊆ {x | η x = 1})
    (hright : ∀ v : smoothSource W (Euclidean n), right v =ᵐ[volume.restrict O]
      (SmallSupport.zeroExtend hW (v : LocalL2 W (Euclidean n)) +
        A (SmallSupport.zeroExtend hW (Corr v)) - SmallSupport.zeroExtend hW (Corr v)))
    (h : compactSmoothSources S) :
    (fun x ↦ right (cutoffStressSmoothSource Q η hU hQ hη hSU h) x -
      WithLp.toLp 2 (stressSource Q h x)) =ᵐ[volume.restrict O]
      (fun x ↦ A (SmallSupport.zeroExtend hW
        (Corr (cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU h))) x -
        SmallSupport.zeroExtend hW
          (Corr (cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU h)) x) := by
  let v := cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU h
  let z := SmallSupport.zeroExtend hW (Corr v)
  have hcut : euclideanCutoffStressSource Q η h =
      fun y ↦ WithLp.toLp 2 (stressSource Q h y) := by
    funext y
    change WithLp.toLp 2 (cutoffSource η (stressSource Q h) y) = _
    rw [cutoffSource_stressSource_eq Q η h
      (fun x hx ↦ hplateau (h.property.2.2 (subset_tsupport _ hx)))]
  have hsrc := zeroExtend_cutoffStressSmoothSource_coeFn Q η hU hQ hη hSU hW hSW h
  rw [hcut] at hsrc
  filter_upwards [hright v, ae_restrict_of_ae hsrc] with x hx hs
  change right v x - WithLp.toLp 2 (stressSource Q h x) = A z x - z x
  rw [hx]
  change (SmallSupport.zeroExtend hW (v : LocalL2 W (Euclidean n)) x + A z x - z x) -
    WithLp.toLp 2 (stressSource Q h x) = _
  rw [hs]
  abel

/-- The full ambient strain equals the inverse-Gram reconstruction of the
ENTIRE paired angular discrepancy on the original output core. Both input
identities are the two conclusions for `solver,right` of the accepted direct
inverse; source admission and geometric reconstruction are discharged here
(`app:ch_response:eq:response-full-identity`). -/
theorem fixedSmoothSolverAmbientExtension_error_eq_full_residual_ae
    (solver right : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v)) (Ξ : OutputCutoff core chart)
    (hchart : IsOpen chart) (hF : ContDiffOn ℝ ∞ F chart)
    (hi : IsImmersionOn F chart) (hrank : HasFullNormalRankOn F chart)
    (Corr : LocalL2 W (Euclidean n) →L[ℝ] LocalL2 W (Euclidean n))
    (A : Lp (Euclidean n) 2 (volume : Measure (Euclidean n)) →L[ℝ]
      Lp (Euclidean n) 2 (volume : Measure (Euclidean n)))
    (hW : MeasurableSet W) (hSW : S ⊆ W) (hplateau : S ⊆ {x | η x = 1})
    (hphysical : ∀ v, EqOn (physicalWeakApply
      (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1))
      (fun y ↦ reducedZerothCoefficient F (Q y) y)
      (fun y ↦ (euclideanComplexInclusion (solver v y)).ofLp)
      (fderiv ℝ (fun y ↦ (euclideanComplexInclusion (solver v y)).ofLp)))
      (fun y ↦ (euclideanComplexInclusion (right v y)).ofLp) O)
    (hright : ∀ v : smoothSource W (Euclidean n), right v =ᵐ[volume.restrict O]
      (SmallSupport.zeroExtend hW (v : LocalL2 W (Euclidean n)) +
        A (SmallSupport.zeroExtend hW (Corr v)) - SmallSupport.zeroExtend hW (Corr v)))
    (hcore : MeasurableSet core) (hcoreO : core ⊆ O)
    (h : compactSmoothSources S) (hsymm : ∀ x ∈ core, ((h : MetricField n) x).IsSymm)
    (hQsymm : ∀ x ∈ core, ∀ i, (Q x i).IsSymm)
    (hQlin : ∀ x ∈ core, LinearIndependent ℝ (Q x))
    (hspan : ∀ x ∈ core,
      (Submodule.span ℝ (range (Q x)) : Set (MetricTensor n)) = stressSpace F x) :
    (fun x ↦ linearizedMetric F
      (fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ h) x -
        (h : MetricField n) x) =ᵐ[volume.restrict core]
      (fun x ↦ (2 : ℝ) • ∑ i, ∑ j, ((stressGram (Q x))⁻¹ i j *
        (A (SmallSupport.zeroExtend hW
          (Corr (cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU h))) x j -
          SmallSupport.zeroExtend hW
            (Corr (cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU h)) x j)) • Q x i) := by
  have he := smoothRight_cutoffStress_residual_ae Q η hU hQ hη hSU
    right Corr A hW hSW hplateau hright h
  filter_upwards [ae_restrict_mem hcore,
    ae_restrict_of_ae_restrict_of_subset hcoreO he] with x hx hex
  rw [fixedSmoothSolverAmbientExtension_error_eq_inverseGram F Q η hU hQ hη hSU
    solver right hsolver Ξ hchart hF hi hrank hphysical h hx (hcoreO hx)
    (hsymm x hx) (hQsymm x hx) (hQlin x hx) (hspan x hx)]
  have hj (j : Fin n) := congrArg (fun v : Euclidean n ↦ v j) hex
  simp only [PiLp.sub_apply] at hj
  simp_rw [hj]

end JanetCartan.CorrectedAtoms
