module

public import JanetCartan.Iteration.PhysicalNormalInverse.StrongRawCap
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedTransport.FullComparison

/-!
# Pre-source transport geometry on the original incidence root

The normal-composition producer uses `OriginalBoundary.T`, its actual incident
root and the literal quarter-normalized original direction. Both radial and
angular normalization therefore agree with the original selector. The shared
working radius is supplied once by `PhysicalSampling`; it is not reselected.
All geometric buffers precede source σ, immersion budgets, gaps and profiles.
Consumers are the ONE joint-cutoff/aExtra minimum and the corrected colored
normal term of `MeanFrontend.current_mean_defect_le_three_terms`
(`app:ch_waves:eq:colored-normal-comparison`, `new:sec:order-of-choices`).
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalNormalInverse.OriginalTransport
open PhysicalSeed ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalConic
open FullPhaseCharts Sampling Sampling.CorrectedTransport LeadingWave.FullModulation

/-- The selector's quarter-normalized covector has the same actual incident
root and a nonzero transverse derivative. This closes the scalar, measured and
transport factories' static incidence inputs before any source contraction. -/
theorem quarter_incidence_facts {n : ℕ} (hn : 5 ≤ n)
    (q : IncidenceCenter (OriginalBoundary.D hn))
    (l : Fin ((OriginalBoundary.D hn).patchCount q.1.1)) :
    let D := OriginalBoundary.D hn
    let T := OriginalBoundary.T hn ⟨q.1.1, l⟩
    let zRoot := D.roots q.1.1 l q.1.2
    let kbase := (1 / 4 : ℝ) • q.1.2
    kbase ≠ 0 ∧ incidence kbase ((D.patches q.1.1 l).toFun zRoot) = 0 ∧
      fderiv ℝ (fun z ↦ incidence kbase ((D.patches q.1.1 l).toFun z)) zRoot
        (EuclideanSpace.single 0 1) ≠ 0 ∧
      T.data.adapted.embedding.toContinuousLinearMap.adjoint kbase ≠ 0 := by
  dsimp only
  let D := OriginalBoundary.D hn
  let T := OriginalBoundary.T hn ⟨q.1.1, l⟩
  have hD := OriginalBoundary.hD hn
  have hP := (hD.2.2.2.2.1 q.1.1 l).1
  have hz := ((hD.2.2.2.2.1 q.1.1 l).2.2.1 q.1.2 q.2.2).1
  have hk0 : q.1.2 ≠ 0 := by
    intro hzero
    have hs := q.2.1
    simp [hzero] at hs
  have hinc0 : incidence q.1.2 ((D.patches q.1.1 l).toFun (D.roots q.1.1 l q.1.2)) = 0 :=
    ((hD.2.2.2.2.1 q.1.1 l).2.2.1 q.1.2 q.2.2).2.2.2
  have hd0 : fderiv ℝ (fun z ↦ incidence q.1.2 ((D.patches q.1.1 l).toFun z))
      (D.roots q.1.1 l q.1.2) (EuclideanSpace.single 0 1) ≠ 0 :=
    abs_pos.mp (hD.1.trans_le ((hD.2.2.2.2.1 q.1.1 l).2.2.2 q.1.2 q.2.2 _
      (fun j ↦ (hz j).le)))
  let kbase := (1 / 4 : ℝ) • q.1.2
  have hk : kbase ≠ 0 := smul_ne_zero (by norm_num) hk0
  have hscale : (fun z : Euclidean 3 ↦ incidence kbase ((D.patches q.1.1 l).toFun z)) =
      (1 / 4 : ℝ) • (fun z : Euclidean 3 ↦ incidence q.1.2 ((D.patches q.1.1 l).toFun z)) := by
    funext z
    simp [kbase, incidence, Finset.mul_sum, mul_assoc]
  have hinc : incidence kbase ((D.patches q.1.1 l).toFun (D.roots q.1.1 l q.1.2)) = 0 := by
    calc
      _ = (1 / 4 : ℝ) • incidence q.1.2
          ((D.patches q.1.1 l).toFun (D.roots q.1.1 l q.1.2)) :=
        congrFun hscale (D.roots q.1.1 l q.1.2)
      _ = 0 := by rw [hinc0, smul_zero]
  have hdiff : DifferentiableAt ℝ
      (fun z ↦ incidence q.1.2 ((D.patches q.1.1 l).toFun z)) (D.roots q.1.1 l q.1.2) := by
    by_contra hnot
    apply hd0
    rw [fderiv_zero_of_not_differentiableAt hnot]
    rfl
  have hd : fderiv ℝ (fun z ↦ incidence kbase ((D.patches q.1.1 l).toFun z))
      (D.roots q.1.1 l q.1.2) (EuclideanSpace.single 0 1) ≠ 0 := by
    rw [hscale, fderiv_const_smul hdiff]
    simpa only [smul_apply, smul_eq_mul] using
      mul_ne_zero (by norm_num : (1 / 4 : ℝ) ≠ 0) hd0
  exact ⟨hk, hinc, hd, FrozenIncidence.tangential_direction_ne_zero T hP hz hk hinc⟩

-- Every notation argument is explicit. Only Lean's unsupported eager let-syntax
-- precheck is bypassed; ordinary elaboration and kernel checking remain strict.
set_option quotPrecheck false in
local notation "originalTransportProof(" p ", " hn ", " q ", " l ", " hρ ", " hcarrier ", " hphase ")" =>
  (let T := OriginalBoundary.T hn ⟨q.1.1, l⟩
   let hD := OriginalBoundary.hD hn
   let hP := (hD.2.2.2.2.1 q.1.1 l).1
   let hz := ((hD.2.2.2.2.1 q.1.1 l).2.2.1 q.1.2 q.2.2).1
   let hfacts := quarter_incidence_facts hn q l
   let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint ((1 / 4 : ℝ) • q.1.2)
   let hηnorm : 0 < ‖ηb‖ := norm_pos_iff.mpr hfacts.2.2.2
   let hamin : 0 < (1 / 2 : ℝ) / ‖ηb‖ := div_pos (by norm_num) hηnorm
   let hamax : (1 / 2 : ℝ) / ‖ηb‖ ≤ 2 / ‖ηb‖ :=
     div_le_div_of_nonneg_right (by norm_num) hηnorm.le
   exists_correctedColoredCrossBandData_transport_bound_before_immersion_bounds
     (p := p) (rmax := 1) (emax := 1) (xmax := 1)
     T hP hz hfacts.1 hfacts.2.1 hfacts.2.2.1 hρ (by norm_num) (by norm_num) (by norm_num)
     hamin hamax hcarrier hphase)

/-- Actual quarter-normalized original-root comparison geometry. All incidence
inputs are closed. The ONE supplied working radius precedes the returned
buffers; every source-dependent budget follows them. -/
theorem geometry {m p : ℕ} (hn : 5 ≤ m + 1)
    (q : IncidenceCenter (OriginalBoundary.D hn))
    (l : Fin ((OriginalBoundary.D hn).patchCount q.1.1))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hcarrier : closedBall ((OriginalBoundary.D hn).roots q.1.1 l q.1.2) (2 * ρ) ⊆
      parameterInterior (2 * ((OriginalBoundary.D hn).patches q.1.1 l).radius))
    (hphase : closedBall
      ((0 : Euclidean (m + 1)),
        ((OriginalBoundary.D hn).roots q.1.1 l q.1.2,
          (OriginalBoundary.T hn ⟨q.1.1, l⟩).reference.spatialPatch
            ((OriginalBoundary.D hn).roots q.1.1 l q.1.2)))
      (2 * ρ) ⊆ domain (OriginalBoundary.T hn ⟨q.1.1, l⟩)) :
    type_of% (originalTransportProof(p, hn, q, l, hρ, hcarrier, hphase)) :=
  originalTransportProof(p, hn, q, l, hρ, hcarrier, hphase)

end JanetCartan.PhysicalNormalInverse.OriginalTransport
