module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.ResidualReconstruction
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.CoefficientNorms

/-!
# Sobolev control of the complete fixed-response strain

The smooth right-hand side of the accepted direct solver represents exactly
the paired angular discrepancy on the original corrected L² source. This
identification proves restriction Sobolev membership and transfers its actual
norm to the full ambient strain. The original stress projection, source
plateau, inverse, source measure and output core are unchanged.

The constants from local Sobolev embedding precede every geometric field and
source. The differentiated inverse-Gram multiplier remains explicit until the
actual history profile is substituted. Decay of the complete angular residual
is still required from the fixed-response and arbitrary-accuracy producers.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory Filter
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CorrectedAtoms
open PrimarySourceAdmission AmbientResponse ResponseSourceExtension FixedDomainInverse LocalSobolev
open RegularSector.FiniteAssembly.CoefficientNorms CharacteristicTransport.CompleteResidual

/-- The original source plateau identifies the uncut stress with the admitted
compact smooth source, so the direct solver's right-hand-side residual is
smooth (`app:ch_regular:eq:exact-physical`). -/
private theorem contDiff_smoothRight_stressResidual {n : ℕ}
    (Q : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
    {S U W : Set (Euclidean n)} (hU : IsOpen U)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U) (hplateau : S ⊆ {x | η x = 1})
    (right : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hsmooth : ∀ v, ContDiff ℝ ∞ (right v)) (h : compactSmoothSources S) :
    ContDiff ℝ ∞ (fun x ↦ right (cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU h) x -
      WithLp.toLp 2 (stressSource Q h x)) := by
  have hcut : euclideanCutoffStressSource Q η h =
      fun x ↦ WithLp.toLp 2 (stressSource Q h x) := by
    funext x
    change WithLp.toLp 2 (cutoffSource η (stressSource Q h) x) = _
    rw [cutoffSource_stressSource_eq Q η h
      (fun y hy ↦ hplateau (h.property.2.2 (subset_tsupport _ hy)))]
  have hh := (hsmooth (cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU h)).sub
    (contDiff_euclideanCutoffStressSource Q η hU hQ hη hSU h)
  simpa only [hcut] using hh

/-- The complete angular discrepancy on the SAME corrected L² source has all
restriction Sobolev orders on the original norm ball. Its actual smooth
right-hand-side representative obeys the local Sobolev estimate. Membership
is proved from the accepted smooth right-hand side, not assumed about an
angular operator (`app:ch_response:eq:response-full-identity`). -/
theorem exists_smoothRight_fullResidual_cNorm_bound (n s : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (Q : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
        (S U W O : Set (Euclidean n)) (hU : IsOpen U)
        (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
        (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U),
      ∀ (right : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n)),
      (∀ v, ContDiff ℝ ∞ (right v)) →
      ∀ (Corr : LocalL2 W (Euclidean n) →L[ℝ] LocalL2 W (Euclidean n))
        (A : Lp (Euclidean n) 2 (volume : Measure (Euclidean n)) →L[ℝ]
          Lp (Euclidean n) 2 (volume : Measure (Euclidean n)))
        (hW : MeasurableSet W), S ⊆ W → S ⊆ {x | η x = 1} →
      (∀ v : smoothSource W (Euclidean n), right v =ᵐ[volume.restrict O]
        (SmallSupport.zeroExtend hW (v : LocalL2 W (Euclidean n)) +
          A (SmallSupport.zeroExtend hW (Corr v)) - SmallSupport.zeroExtend hW (Corr v))) →
      ∀ (x : Euclidean n) (r R : ℝ), 0 < r → r < R → ball x R ⊆ O →
      ∀ h : compactSmoothSources S,
      let z := SmallSupport.zeroExtend hW (Corr (cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU h))
      let e := A z - z
      let eV := ((Lp.memLp e).restrict (ball x R)).toLp e
      (∀ m, MemRestrictionSobolev (ball x R) m eV) ∧
      cNorm (closedBall x r) s
        (fun y ↦ right (cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU h) y -
          WithLp.toLp 2 (stressSource Q h y)) ≤
        C * restrictionSobolevNorm (ball x R) (s+n+1) eV := by
  obtain ⟨C, hC, hbound⟩ := exists_cNorm_le_restrictionSobolevNorm (F := Euclidean n) n s
  refine ⟨C, hC, ?_⟩
  intro Q η S U W O hU hQ hη hSU right hsmooth Corr A hW hSW hplateau hright
    x r R hr hrR hVO h
  dsimp only
  let z := SmallSupport.zeroExtend hW (Corr (cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU h))
  let e := A z - z
  let eV := ((Lp.memLp e).restrict (ball x R)).toLp e
  let f := fun y ↦ right (cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU h) y -
    WithLp.toLp 2 (stressSource Q h y)
  have hf : ContDiff ℝ ∞ f := contDiff_smoothRight_stressResidual Q η hU hQ hη hSU
    hplateau right hsmooth h
  have he : f =ᵐ[volume.restrict (ball x R)] e := by
    have hh : f =ᵐ[volume.restrict (ball x R)] (fun y ↦ A z y - z y) :=
      ae_restrict_of_ae_restrict_of_subset hVO
      (smoothRight_cutoffStress_residual_ae Q η hU hQ hη hSU
        right Corr A hW hSW hplateau hright h)
    have hsub : (fun y ↦ e y) =ᵐ[volume.restrict (ball x R)] (fun y ↦ A z y - z y) :=
      ae_restrict_of_ae (Lp.coeFn_sub (A z) z)
    exact hh.trans hsub.symm
  have heV : f =ᵐ[volume.restrict (ball x R)] eV :=
    he.trans (MemLp.coeFn_toLp _).symm
  have hR : 0 < R := hr.trans hrR
  have hclass : smoothCoefficientL2 isOpen_univ hR (subset_univ (closedBall x R)) f
      hf.contDiffOn = eV := by
    apply Lp.ext
    exact (smoothCoefficientL2_coeFn isOpen_univ hR (subset_univ (closedBall x R)) f
      hf.contDiffOn).trans heV
  have hmem (m : ℕ) : MemRestrictionSobolev (ball x R) m eV := by
    rw [← hclass]
    exact smoothCoefficientL2_memRestrictionSobolev isOpen_univ hR
      (subset_univ (closedBall x R)) f hf.contDiffOn m
  exact ⟨hmem, hbound x r R hr hrR f hf.contDiffOn eV heV (hmem _)⟩

/-- The full strain of the SAME ambient extension is controlled by the exact
complete angular L² residual in the original restriction norm. The explicit
multiplier seminorm preserves the high geometry dependence; its history
profile is supplied by `exists_history_fullStressResidualReconstruction_profiles`.
No full-strain bound or residual Sobolev membership is a premise
(`app:ch_response:eq:response-full-identity`, `app:ch_response:cor:current-atoms`). -/
theorem exists_fixedSmoothSolver_fullStrain_cNorm_bound (n s : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) (F : Euclidean n → Euclidean N)
      (Q : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
      (S U W O core chart : Set (Euclidean n)) (hU : IsOpen U)
      (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
      (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U)
      (solver right : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))
      (hsolver : ∀ v, ContDiff ℝ ∞ (solver v)),
      (∀ v, ContDiff ℝ ∞ (right v)) →
      ∀ Ξ : OutputCutoff core chart, IsOpen chart → ContDiffOn ℝ ∞ F chart →
      IsImmersionOn F chart → HasFullNormalRankOn F chart →
      ∀ (Corr : LocalL2 W (Euclidean n) →L[ℝ] LocalL2 W (Euclidean n))
        (A : Lp (Euclidean n) 2 (volume : Measure (Euclidean n)) →L[ℝ]
          Lp (Euclidean n) 2 (volume : Measure (Euclidean n)))
        (hW : MeasurableSet W), S ⊆ W → S ⊆ {x | η x = 1} →
      (∀ v, EqOn (physicalWeakApply
        (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1))
        (fun y ↦ GeometricProfile.reducedZerothCoefficient F (Q y) y)
        (fun y ↦ (euclideanComplexInclusion (solver v y)).ofLp)
        (fderiv ℝ (fun y ↦ (euclideanComplexInclusion (solver v y)).ofLp)))
        (fun y ↦ (euclideanComplexInclusion (right v y)).ofLp) O) →
      (∀ v : smoothSource W (Euclidean n), right v =ᵐ[volume.restrict O]
        (SmallSupport.zeroExtend hW (v : LocalL2 W (Euclidean n)) +
          A (SmallSupport.zeroExtend hW (Corr v)) - SmallSupport.zeroExtend hW (Corr v))) →
      ∀ (x : Euclidean n) (r R : ℝ), 0 < r → r < R →
      ball x R ⊆ O → ball x R ⊆ core → ball x R ⊆ U →
      (∀ y ∈ ball x R, ∀ i, (Q y i).IsSymm) →
      (∀ y ∈ ball x R, LinearIndependent ℝ (Q y)) →
      (∀ y ∈ ball x R,
        (Submodule.span ℝ (range (Q y)) : Set (MetricTensor n)) = stressSpace F y) →
      ∀ h : compactSmoothSources S, (∀ y ∈ ball x R, ((h : MetricField n) y).IsSymm) →
      let B := fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ
      let z := SmallSupport.zeroExtend hW (Corr (cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU h))
      let e := A z - z
      let eV := ((Lp.memLp e).restrict (ball x R)).toLp e
      cNorm (closedBall x r) s (linearizedMetric F (B h) - (h : MetricField n)) ≤
        ((s+1 : ℝ) * (2 : ℝ)^s) *
          cNorm (closedBall x r) s (fun y ↦ fullStressResidualReconstruction (Q y)) *
          (C * restrictionSobolevNorm (ball x R) (s+n+1) eV) := by
  obtain ⟨C, hC, hbound⟩ := exists_smoothRight_fullResidual_cNorm_bound n s
  refine ⟨C, hC, ?_⟩
  intro N F Q η S U W O core chart hU hQ hη hSU solver right hsolver hsmooth Ξ
    hchart hF hi hrank Corr A hW hSW hplateau hphysical hright x r R hr hrR hVO hVcore hVU
    hQsymm hQlin hspan h hsymm
  dsimp only
  let B := fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ
  let f := fun y ↦ right (cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU h) y -
    WithLp.toLp 2 (stressSource Q h y)
  have hf : ContDiff ℝ ∞ f := contDiff_smoothRight_stressResidual Q η hU hQ hη hSU
    hplateau right hsmooth h
  have he : cNorm (closedBall x r) s (linearizedMetric F (B h) - (h : MetricField n)) =
      cNorm (closedBall x r) s (fun y ↦ fullStressResidualReconstruction (Q y) (f y)) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq
    intro y hy
    filter_upwards [isOpen_ball.mem_nhds (closedBall_subset_ball hrR hy)] with w hw
    rw [fullStressResidualReconstruction_apply]
    simpa only [f, B, Pi.sub_apply, PiLp.sub_apply, PiLp.toLp_apply] using
      fixedSmoothSolverAmbientExtension_error_eq_inverseGram F Q η hU hQ hη hSU solver right
        hsolver Ξ hchart hF hi hrank hphysical h (hVcore hw) (hVO hw)
        (hsymm w hw) (hQsymm w hw) (hQlin w hw) (hspan w hw)
  rw [he]
  have hrec := cNorm_fullStressResidualReconstruction_le (isCompact_closedBall x r) isOpen_ball
    (closedBall_subset_ball hrR) Q ((contDiffOn_pi.mpr hQ).mono hVU) hQlin f hf.contDiffOn s
  have hnorm := (hbound Q η S U W O hU hQ hη hSU right hsmooth Corr A hW hSW hplateau
    hright x r R hr hrR hVO h).2
  have hcoeff : 0 ≤ cNorm (closedBall x r) s
      (fun y ↦ fullStressResidualReconstruction (Q y)) := cNorm_nonneg _ _ _
  exact hrec.trans (mul_le_mul_of_nonneg_left hnorm (by positivity))

end JanetCartan.CorrectedAtoms
