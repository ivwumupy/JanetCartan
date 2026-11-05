module

public import JanetCartan.Analysis.Microlocal.FullSourceStationary.SmoothBranch
public import JanetCartan.Analysis.Microlocal.FullSourceStationary.ZeroTime

/-!
# A uniform stationary interval for the full source

The original low phase budgets and diagonal margin fix the interval before the
varying phase and retained chart. Quantitative contraction constructs stationary
points; the parameter-dependent IFT gives their smoothness in elapsed time,
physical position, all three source labels, and the independent covector.
The actual history budgets are supplied by `JointProfiles`.
Consumer: `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Topology InnerProductSpace

namespace JanetCartan.FullSourceStationary
open CompatibleResponse ArbitraryAccuracy RegularSector.Characteristic ConicPhase EvolutionIntegral
open ResponseTransfer.DirectEvolution ResponseTransfer.RetainedFactors
open EvolutionIntegral.KernelIdentification
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "W" => CarrierVariables (d + 1)
local notation "P" => ℝ × (E × (Euclidean 3 × Euclidean d))
local notation "TT" => TwoTimePoint (Euclidean d)

/-- Uniform smooth stationary branches for both literal orientations of the
same retained conic phase. Only primitive phase jets and original geometric
buffers are inputs. The common positive time precedes the primary phase,
flow and chart witnesses; there is no frequency-dependent restriction.
The branch is smooth on an open neighborhood of `[0, τ] × U₀`, stationary
there, and stays within half the supplied diagonal margin. Consumer: the
`hw0` and `hcrit` inputs of the forward and adjoint integrated envelope;
zero critical value is a separate parent obligation
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_uniform_full_source_conic_stationary_branches
    (U₀ : Set (E × (Euclidean 3 × Euclidean d))) (hU₀ : IsOpen U₀)
    {ρ T Bₚ B₂ B₃ : ℝ} (hρ : 0 < ρ) (hT : 0 < T)
    (hBₚ : 0 ≤ Bₚ) (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃) :
    ∃ τ > 0, τ ≤ T ∧
      Icc (0 : ℝ) τ ×ˢ U₀ ⊆ Ioo (-2 * τ) (2 * τ) ×ˢ U₀ ∧
    ∀ (φ : E → (Euclidean 3 × Euclidean d) → ℝ) (Ω : Set (E × (Euclidean 3 × Euclidean d))),
      IsOpen Ω → ContDiffOn ℝ ∞ (Function.uncurry φ) Ω → U₀ ⊆ Ω →
      (∀ q ∈ U₀, ‖iteratedFDeriv ℝ 2 (Function.uncurry φ) q‖ ≤ Bₚ) →
    ∀ (ℓ : Euclidean d →L[ℝ] ℝ)
      (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
      (C : OpenPartialHomeomorph TT TT),
      (C : TT → TT) = twoTimeProjection Φ →
    ∀ (z : RootState (Euclidean d)) (b : ℝ),
      C.source = ball (z.1, z) b → (∀ v ∈ ball z b, Φ (v, 0) = v) →
      (∀ q ∈ U₀, elapsedChartPoint 0 q.1 (gradient (fun y ↦ φ y q.2) q.1) ∈
        domain ℓ C.target) →
    ∀ (V K : Set (FullSourcePoint d)), IsOpen V → IsCompact K → K ⊆ V →
      (∀ q ∈ U₀, (Icc (-T) T ×ˢ {q}) ×ˢ
        closedBall (WithLp.toLp 2 (q.1, gradient (fun y ↦ φ y q.2) q.1)) (4 * ρ) ⊆ K) →
      (∀ adj : Bool, ContDiffOn ℝ ∞ (fullSourceJointPhase adj (curriedPhase ℓ C) φ) V) →
      (∀ adj : Bool, cNorm K 2 (fullSourceJointPhase adj (curriedPhase ℓ C) φ) ≤ B₂ ∧
        cNorm K 3 (fullSourceJointPhase adj (curriedPhase ℓ C) φ) ≤ B₃) →
    ∀ D : Set W,
      (∀ q ∈ U₀, closedBall
        (WithLp.toLp 2 (q.1, gradient (fun y ↦ φ y q.2) q.1)) (4 * ρ) ⊆ D) →
    ∃ κ : Bool → P → W, ∀ adj : Bool,
      ContDiffOn ℝ ∞ (κ adj) (Ioo (-2 * τ) (2 * τ) ×ˢ U₀) ∧
      (∀ q ∈ U₀, κ adj (0, q) = WithLp.toLp 2 (q.1, gradient (fun y ↦ φ y q.2) q.1)) ∧
      ∀ p ∈ Ioo (-2 * τ) (2 * τ) ×ˢ U₀,
        κ adj p ∈ D ∧
        gradient (fun w ↦ fullSourceJointPhase adj (curriedPhase ℓ C) φ (p, w))
          (κ adj p) = 0 ∧
        dist (κ adj p) (WithLp.toLp 2 (p.2.1, gradient (fun y ↦ φ y p.2.2) p.2.1)) ≤ ρ / 2 := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
  let M := ‖e.symm.toContinuousLinearMap‖ * (1 + Bₚ) * ‖e.toContinuousLinearMap‖
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨r, hr, τ, hτ, hrρ, hτT, hτr, hsmall₃, hsmall₂⟩ :=
    exists_retained_stationary_radii hρ hT hM hB₂ hB₃
  refine ⟨τ, hτ, by linarith, ?_, ?_⟩
  · rintro ⟨t, q⟩ ⟨ht, hq⟩
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hq⟩
  intro φ Ω hΩ hφ hUΩ hprimary ℓ Φ C hC z b hsource hi hgraph V K hV hK hKV
    hbuffer hsmooth hbudget D hD
  let a : E × (Euclidean 3 × Euclidean d) → W := fun q ↦
    WithLp.toLp 2 (q.1, gradient (fun y ↦ φ y q.2) q.1)
  let A : E × (Euclidean 3 × Euclidean d) → W ≃L[ℝ] W := fun q ↦
    retainedDiagonalHessianEquiv (fderiv ℝ (gradient (fun y ↦ φ y q.2)) q.1)
  let U : Set P := Ioo (-2 * τ) (2 * τ) ×ˢ U₀
  have hU : IsOpen U := isOpen_Ioo.prod hU₀
  have ha : ContinuousOn a U₀ :=
    e.symm.continuous.comp_continuousOn
      (continuousOn_fst.prodMk ((contDiffOn_full_source_gradient hΩ hφ).continuousOn.mono hUΩ))
  have hat : ContinuousOn (fun p : P ↦ a p.2) U :=
    ha.comp continuousOn_snd (fun _ hp ↦ hp.2)
  have hbuf q (hq : q ∈ U₀) :
      (Icc (-T) T ×ˢ {q}) ×ˢ closedBall (a q) (2 * r) ⊆ K := by
    rintro p ⟨hp, hw⟩
    exact hbuffer q hq ⟨hp, closedBall_subset_closedBall (by linarith) hw⟩
  have htime p (hp : p ∈ U) : |p.1| ≤ T ∧ |p.1| ≤ 2 * r := by
    have ht : |p.1| ≤ 2 * τ := abs_le.mpr ⟨by linarith [hp.1.1], hp.1.2.le⟩
    exact ⟨ht.trans hτT, ht.trans (by linarith)⟩
  have hinit adj q (hq : q ∈ U₀) :
      gradient (fun w ↦ fullSourceJointPhase adj (curriedPhase ℓ C) φ ((0, q), w)) (a q) = 0 :=
    full_source_conic_zeroTime_stationary adj ℓ hC hsource hi φ q
      (((hφ.contDiffAt (hΩ.mem_nhds (hUΩ hq))).comp q.1
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)) (hgraph q hq)
  have hlinear adj q (hq : q ∈ U₀) :
      fderiv ℝ (gradient (fun w ↦
        fullSourceJointPhase adj (curriedPhase ℓ C) φ ((0, q), w))) (a q) =
          (A q).toContinuousLinearMap :=
    full_source_conic_zeroTime_hessian adj ℓ hC hsource hi hΩ hφ q
      (w := a q) (hUΩ hq) (hgraph q hq)
      (by simpa [fullSourceGraphPoint, a, elapsedChartPoint] using hgraph q hq)
  have hinverse q (hq : q ∈ U₀) : ‖(A q).symm.toContinuousLinearMap‖ ≤ M := by
    have hb := (full_source_conic_zeroTime_stationary_inverse_bound false ℓ hC hsource hi
      hΩ hφ (hUΩ hq) (hprimary q hq) (hgraph q hq)).2
    rw [hlinear false q hq, ContinuousLinearMap.ringInverse_eq_inverse,
      ContinuousLinearMap.inverse_equiv] at hb
    exact hb
  have hjet (adj : Bool) (j : ℕ) p (hp : p ∈ K) :
      ‖iteratedFDeriv ℝ j (fullSourceJointPhase adj (curriedPhase ℓ C) φ) p‖ ≤
        cNorm K j (fullSourceJointPhase adj (curriedPhase ℓ C) φ) :=
    norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun v hv ↦ ((hsmooth adj).contDiffAt (hV.mem_nhds (hKV hv))).of_le (by simp)) hp le_rfl
  have hbranches (adj : Bool) : ∃ κ : P → W,
      ContDiffOn ℝ ∞ κ U ∧
      (∀ p ∈ U, κ p ∈ closedBall (a p.2) (r / 2) ∧
        gradient (fun w ↦ fullSourceJointPhase adj (curriedPhase ℓ C) φ (p, w)) (κ p) = 0) ∧
      ∀ p ∈ U, ∀ w ∈ closedBall (a p.2) (2 * r),
        gradient (fun v ↦ fullSourceJointPhase adj (curriedPhase ℓ C) φ (p, v)) w = 0 ↔
          κ p = w := by
    apply exists_smooth_full_source_stationary_branch_of_contraction hV (hsmooth adj) hU
      (fun p ↦ a p.2) hat (fun p ↦ A p.2) hr
    · intro p hp w hw
      exact hKV (hbuf p.2 hp.2 ⟨⟨abs_le.mp (htime p hp).1, rfl⟩, hw⟩)
    · intro p hp w hw
      exact ((full_source_stationary_normalized_estimates hV (hsmooth adj) p.2 (a p.2) (A p.2)
        hT.le hr.le hM hB₂ hB₃ (hlinear adj p.2 hp.2) (hinverse p.2 hp.2) (hinit adj p.2 hp.2)
        ((hbuf p.2 hp.2).trans hKV)
        (fun v hv ↦ (hjet adj 2 v (hbuf p.2 hp.2 hv)).trans (hbudget adj).1)
        (fun v hv ↦ (hjet adj 3 v (hbuf p.2 hp.2 hv)).trans (hbudget adj).2)
        (htime p hp).1 (htime p hp).2).1 w hw).trans hsmall₃
    · intro p hp
      apply (exists_full_source_stationary_point_of_low_jets hV (hsmooth adj) p.2 (a p.2) (A p.2)
        hT.le hr hM hB₂ hB₃ (hlinear adj p.2 hp.2) (hinverse p.2 hp.2) (hinit adj p.2 hp.2)
        ((hbuf p.2 hp.2).trans hKV)
        (fun v hv ↦ (hjet adj 2 v (hbuf p.2 hp.2 hv)).trans (hbudget adj).1)
        (fun v hv ↦ (hjet adj 3 v (hbuf p.2 hp.2 hv)).trans (hbudget adj).2)
        (htime p hp).1 (htime p hp).2 hsmall₃ ?_).2
      exact (mul_le_mul_of_nonneg_left
        (abs_le.mpr ⟨by linarith [hp.1.1], hp.1.2.le⟩) (mul_nonneg hM hB₂)).trans hsmall₂
  choose κ hκs hκ hκunique using hbranches
  refine ⟨κ, fun adj ↦ ⟨hκs adj, ?_, ?_⟩⟩
  · intro q hq
    have hqU : ((0 : ℝ), q) ∈ U := ⟨⟨by linarith, by linarith⟩, hq⟩
    exact (hκunique adj (0, q) hqU (a q) (mem_closedBall_self (by positivity))).mp
      (hinit adj q hq)
  · intro p hp
    obtain ⟨hclose, hstat⟩ := hκ adj p hp
    refine ⟨hD p.2 hp.2 (closedBall_subset_closedBall (by linarith) hclose), hstat, ?_⟩
    exact le_trans hclose (by linarith)

end JanetCartan.FullSourceStationary
