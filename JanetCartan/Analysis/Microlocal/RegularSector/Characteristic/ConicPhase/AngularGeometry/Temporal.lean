module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.AngularGeometry.Elapsed

/-!
# Actual temporal shear bound on normalized representatives

The proof uses the compactness argument of `PhaseMixedBounds` on the same
smooth extension of the same chart. Equality of the full elapsed mixed
matrices transfers its temporal row bound to every ray of the cone.
Consumer: the inverse bounds of `app:ch_regular_base:lem:retarded-kernel`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ConicPhase
open FourierIntegral EvolutionIntegral
variable {d : ℕ}

private theorem continuous_extension_timeMixed
    {F : TwoTimePoint (Euclidean d) → ℝ} (hF : ContDiff ℝ ∞ F) :
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

/-- The temporal shear is actually bounded on the full cone. Compactness
is used only for the fixed normalized representatives, before quantifying
over elapsed times, physical points, and every positive radial scale. The
input is the original local smooth phase and its full differential, with
no temporal bound assumed (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem exists_conic_elapsedTimeMixed_bound (ℓ : Euclidean d →L[ℝ] ℝ)
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {z : RootState (Euclidean d)} {ε : ℝ} (hε : 0 < ε)
    (hbuffer : closedBall (z.1, z) (2 * ε) ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hdiff : ∀ q ∈ C.target,
      HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) :
    ∃ L > 0, ∀ r ∈ Icc 0 ε, ∀ x ∈ elapsedPhysicalBox z ε,
      ∀ η ∈ angularCone ℓ z.2.2 ε,
        ‖fun j : Fin d ↦ partialDeriv
          (elapsedTimeDerivative (curriedPhase ℓ C) r (x 0, spatialPart x)) η j‖ ≤ L := by
  obtain ⟨F, hF, he⟩ := exists_smooth_twoTimePhase_extension C isClosed_closedBall hbuffer hs
  let Ψ : TwoTimePhase d := fun t s y η ↦ F (t, (s, (y, η)))
  let K := Icc 0 ε ×ˢ
    ((closedBall z.1 ε ×ˢ closedBall z.2.1 ε) ×ˢ closedBall z.2.2 ε)
  have hK : IsCompact K := isCompact_Icc.prod
    (((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).prod (isCompact_closedBall _ _))
  obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn (continuous_extension_timeMixed hF).continuousOn
  refine ⟨|L| + 1, by positivity, ?_⟩
  intro r hr x hx η hη
  let ξ : Euclidean (d + 1) := WithLp.toLp 2 (Fin.cases 0 η.ofLp)
  have hξ : spatialPart ξ = η := by ext i; rfl
  let ζ : Euclidean (d + 1) := (ℓ η)⁻¹ • ξ
  have hζ : spatialPart ζ = (ℓ η)⁻¹ • η := by
    change spatialPartCLM ((ℓ η)⁻¹ • ξ) = _
    rw [map_smul, spatialPartCLM_apply, hξ]
  have hζball : spatialPart ζ ∈ ball z.2.2 ε := hζ ▸ hη.2
  have hmatrix : mixedPhaseMatrix (elapsedPhase (curriedPhase ℓ C) r) x ξ =
      mixedPhaseMatrix (elapsedPhase Ψ r) x ζ := by
    have hc := mixedPhaseMatrix_elapsed_eq_normalize ℓ hε hbuffer hs hdiff hr hx
      (show spatialPart ξ ∈ angularCone ℓ z.2.2 ε from hξ ▸ hη)
    rw [hξ] at hc
    exact hc.trans (SupportedSobolev.mixedPhaseMatrix_eq_of_eventuallyEq
      (elapsedPhase_eventuallyEq_of_twoTime_extension C hε he hr hx hζball)).symm
  have hc := mixedPhaseMatrix_elapsedPhase_of_contDiff (curriedPhase ℓ C) r x ξ
    (isOpen_angularCone ℓ z.2.2 ε) (show spatialPart ξ ∈ angularCone ℓ z.2.2 ε from hξ ▸ hη)
    (fun θ hθ ↦ contDiffAt_elapsedSpatialPhase _ r
      (contDiffAt_curriedPhase_elapsed ℓ hε hbuffer hs hr hx hθ))
  have hfs : ContDiff ℝ ∞
      (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦ Ψ p.1.1 p.1.2 p.2.1 p.2.2) :=
    hF.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))
  have hf := mixedPhaseMatrix_elapsedPhase_of_contDiff Ψ r x ζ isOpen_univ (mem_univ _)
    (fun _ _ ↦ contDiffAt_elapsedSpatialPhase Ψ r hfs.contDiffAt)
  have hrow : (fun j : Fin d ↦ partialDeriv
      (elapsedTimeDerivative (curriedPhase ℓ C) r (x 0, spatialPart x)) η j) =
      fun j : Fin d ↦ partialDeriv
        (elapsedTimeDerivative Ψ r (x 0, spatialPart x)) ((ℓ η)⁻¹ • η) j := by
    funext j
    have hj := congrArg (fun A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ↦ A 0 j.succ) hmatrix
    simpa only [hc, hf, Fin.cases_zero, Fin.cases_succ, hξ, hζ] using hj
  rw [hrow]
  exact (hL (r, ((x 0, spatialPart x), (ℓ η)⁻¹ • η))
    ⟨hr, ⟨ball_subset_closedBall hx.1, ball_subset_closedBall hx.2⟩,
      ball_subset_closedBall hη.2⟩).trans (by linarith [le_abs_self L])

end JanetCartan.RegularSector.Characteristic.ConicPhase
