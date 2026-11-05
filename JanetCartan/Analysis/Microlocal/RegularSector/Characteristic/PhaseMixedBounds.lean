module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PhaseExtension

/-!
# Actual mixed inverse bounds on the elapsed slab

The temporal row of the elapsed mixed matrix is a second phase derivative.
A compact bound for the single smooth joint extension controls that row;
the original spatial half-gap controls the triangular determinant. Thus the
mixed inverse bound is derived for the actual phase, without assuming a
bound for the temporal shear. Constants here concern one local coefficient
array, not a uniform coefficient family or a normalized symbol class.
Source: `app:ch_regular_base:lem:retarded-kernel` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic
open FourierIntegral EvolutionIntegral
variable {d : ℕ}

private theorem continuous_elapsedTimeMixed {F : TwoTimePoint (Euclidean d) → ℝ} (hF : ContDiff ℝ ∞ F) :
    Continuous (fun p : ℝ × ((ℝ × Euclidean d) × Euclidean d) ↦
      fun j : Fin d ↦ partialDeriv
        (elapsedTimeDerivative (fun t s y η ↦ F (t, (s, (y, η)))) p.1 p.2.1) p.2.2 j) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply ContDiffAt.continuousAt (𝕜 := ℝ) (n := ∞)
  apply contDiffAt_pi.mpr
  intro j
  have hs : ContDiff ℝ ∞ (fun p : ℝ × ((ℝ × Euclidean d) × Euclidean d) ↦
      F (p.2.1.1, (p.2.1.1 - p.1, (p.2.1.2, p.2.2)))) := by fun_prop
  have hx : ContDiffAt ℝ ∞
      (fun p : ℝ × ((ℝ × Euclidean d) × Euclidean d) ↦
        elapsedTimeDerivative (fun t s y η ↦ F (t, (s, (y, η)))) p.1 p.2.1 p.2.2) p := by
    have h := hs.contDiffAt.comp (p, p.2.1)
      (contDiffAt_fst.fst.prodMk (contDiffAt_snd.prodMk contDiffAt_fst.snd.snd))
    exact (h.fderiv contDiffAt_snd.fst (by simp)).clm_apply contDiffAt_const
  have h := hx.comp (p, p.2.2)
    (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.fst.prodMk contDiffAt_snd))
  exact (h.fderiv contDiffAt_snd.snd (by simp)).clm_apply contDiffAt_const

private theorem exists_elapsedTimeMixed_bound
    {F : TwoTimePoint (Euclidean d) → ℝ} (hF : ContDiff ℝ ∞ F)
    (z : RootState (Euclidean d)) (ε : ℝ) :
    ∃ L > 0, ∀ r ∈ Icc 0 ε, ∀ x ∈ elapsedPhysicalBox z ε, ∀ η ∈ ball z.2.2 ε,
      ‖fun j : Fin d ↦ partialDeriv
        (elapsedTimeDerivative (fun t s y η ↦ F (t, (s, (y, η)))) r (x 0, spatialPart x)) η j‖ ≤ L := by
  let K := Icc 0 ε ×ˢ
    ((closedBall z.1 ε ×ˢ closedBall z.2.1 ε) ×ˢ closedBall z.2.2 ε)
  have hK : IsCompact K := isCompact_Icc.prod
    (((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).prod (isCompact_closedBall _ _))
  obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn (continuous_elapsedTimeMixed hF).continuousOn
  refine ⟨|L| + 1, by positivity, ?_⟩
  intro r hr x hx η hη
  exact (hL (r, ((x 0, spatialPart x), η))
    ⟨hr, ⟨ball_subset_closedBall hx.1, ball_subset_closedBall hx.2⟩, ball_subset_closedBall hη⟩).trans
      (by linarith [le_abs_self L])

/-- Positive determinant and finite Frobenius inverse bounds for every elapsed
time and every temporal frequency on the actual local spatial chart. The
spatial half-gap is supplied by `exists_buffered_physical_pencil_kernel`;
the temporal row bound is proved here from the same smooth phase. No
whole-image inverse estimate is postulated.
Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem exists_curriedTwoTimePhase_elapsed_mixed_bounds
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {z : RootState (Euclidean d)} {ε : ℝ} (hε : 0 < ε)
    (hbuffer : closedBall (z.1, z) (2 * ε) ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hnear : ∀ q ∈ closedBall (z.1, z) (2 * ε), ‖twoTimePhaseMixed C q - 1‖ ≤ 1 / 2) :
    ∃ κ > 0, ∃ B > 0, ∀ r ∈ Icc 0 ε, ∀ x ∈ elapsedPhysicalBox z ε,
      ∀ ξ : Euclidean (d + 1), spatialPart ξ ∈ ball z.2.2 ε →
        IsUnit (mixedPhaseMatrix (elapsedPhase (curriedTwoTimePhase C) r) x ξ).det ∧
        κ ≤ |(mixedPhaseMatrix (elapsedPhase (curriedTwoTimePhase C) r) x ξ).det| ∧
        ‖(mixedPhaseMatrix (elapsedPhase (curriedTwoTimePhase C) r) x ξ)⁻¹‖ ≤ B := by
  obtain ⟨F, hF, he⟩ := exists_smooth_twoTimePhase_extension C isClosed_closedBall hbuffer hs
  let Ψ : TwoTimePhase d := fun t s y η ↦ F (t, (s, (y, η)))
  obtain ⟨L, _, hL⟩ := exists_elapsedTimeMixed_bound hF z ε
  obtain ⟨κ, hκ, B, hB, hb⟩ := exists_elapsedPhase_mixed_bounds d L
  have hfs : ContDiff ℝ ∞
      (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦ Ψ p.1.1 p.1.2 p.2.1 p.2.2) :=
    hF.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))
  have hfn : ∀ r ∈ Icc 0 ε, ∀ x ∈ elapsedPhysicalBox z ε, ∀ η ∈ ball z.2.2 ε,
      ‖mixedPhaseMatrix (Ψ (x 0) (x 0 - r)) (spatialPart x) η - 1‖ ≤ 1 / 2 := by
    intro r hr x hx η hη
    have hq := elapsedPoint_mem_twoTime_buffer hε hr hx hη
    have hc : Continuous (fun p : Euclidean d × Euclidean d ↦
        (x 0, (x 0 - r, p))) := continuous_const.prodMk (continuous_const.prodMk continuous_id)
    have hg : Function.uncurry (Ψ (x 0) (x 0 - r)) =ᶠ[𝓝 (spatialPart x, η)]
        Function.uncurry (curriedTwoTimePhase C (x 0) (x 0 - r)) :=
      (he _ hq).comp_tendsto (hc.tendsto (spatialPart x, η))
    rw [SupportedSobolev.mixedPhaseMatrix_eq_of_eventuallyEq hg]
    exact hnear (x 0, (x 0 - r, (spatialPart x, η))) hq
  have hbound := hb Ψ ε (elapsedPhysicalBox z ε) (ball z.2.2 ε) isOpen_ball
    (fun _ _ _ _ _ _ ↦ hfs.contDiffAt) hfn hL
  refine ⟨κ, hκ, B, hB, ?_⟩
  intro r hr x hx ξ hξ
  have hm := SupportedSobolev.mixedPhaseMatrix_eq_of_eventuallyEq
    (elapsedPhase_eventuallyEq_of_twoTime_extension C hε he hr hx hξ)
  rw [← hm]
  exact hbound r hr x hx ξ hξ

end JanetCartan.RegularSector.Characteristic
