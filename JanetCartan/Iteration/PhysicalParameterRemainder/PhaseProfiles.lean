module

public import JanetCartan.Iteration.PhysicalParameterRemainder.FullPhase
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Phase.Extension

/-!
# Joint profiles of the supplied physical phase extension

The pre-reference source geometry has already chosen the cutoff. Applying the
actual history phase producer on that cutoff's complete support and extending
with that same cutoff gives global joint bounds. The original source and
observation phase therefore use one function, including every cutoff shoulder.

Consumer: both phase inputs of
`exists_observed_parameter_remainders_of_original_profiles`,
`app:ch_response:eq:response-graded-reduced` and
`app:ch_regular:eq:inverse-remainder`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalParameterRemainder

open ActualCarriers FrozenMenu CurrentFullPhase ResponsePrimarySources
open CompatibleResponse
open GeometricProfile ProtectedFlow LeadingWave.FullModulation
open ResponseTransfer.GradedPrimitives
open JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily

/-- The initializer's supplied phase cutoff has global joint profiles on the
SAME extended history coefficients. No new cutoff, full phase, coefficient
extension or inverse is selected. The constants precede all histories, full
source parameters and physical points. In particular they apply on both the
original source support and the observation phase support
(`app:ch_response:eq:response-graded-reduced`,
`app:ch_regular:eq:inverse-remainder`). -/
theorem exists_physical_retainedPhaseExtension_joint_profiles
    {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (θ : Euclidean (d + 1) × (Euclidean 3 × Euclidean d) → ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hcθ : HasCompactSupport θ) (hsθ : tsupport θ ⊆ domain T)
    (G : FlatReference (d + 1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (ext : BallExtension.Parameters (Euclidean (d + 1)))
    (hextcenter : ext.center = 0) (hextradius : ext.radius = r)
    {Cband : ℝ} (hband : 1 ≤ Cband)
    {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : RevisedScales.displacementLoss (d + 1) +
      bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < kMin) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ H : ℕ → ℝ, (∀ j, 0 ≤ H j) ∧
      IsCompact (Prod.fst '' tsupport θ) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (stage : ℕ)
        (u : Fin stage → SchwartzMap (Euclidean (d + 1)) (Euclidean (embeddingDimension (d + 1))))
        (ell : Fin stage → ℕ), RevisedGlobal.IsAdmissibleHistory Cband R₀ kMin u ell →
      ∀ Q, Q.1 = extendedProjectedStress ext (RevisedGlobal.finiteMap G.map u) →
      let φ := fun c x ↦ retainedPhaseExtension T Q θ x c
      ContDiff ℝ ∞ (Function.uncurry φ) ∧
        (∀ c, tsupport (φ c) ⊆ Prod.fst '' tsupport θ) ∧
        ∀ c x j, ‖iteratedFDeriv ℝ j (Function.uncurry φ) (c,x)‖ ≤
          H j * currentCoefficientScale R₀ stage ^ j := by
  have hid (y : Euclidean (d + 1)) :
      (primaryCoordinateChange (0 : Fin (d + 1))).symm y = y :=
    (RegularSector.Characteristic.coordinateSplit (0 : Fin (d + 1))).symm_apply_apply y
  obtain ⟨S, hS, A, hA, hphase⟩ := T.exists_physical_history_full_source_phase_profiles
    0 hcθ (fun q hq ↦ by rw [hid]; exact hsθ hq)
    G hr hrR hR ext hextcenter hextradius hband hStar (Rstar := 0) (by omega) horder
  choose B hB hjetθ using fun j ↦ hcθ.exists_bound_iteratedFDeriv hθ j
  let H := bilinearConstant
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) B A
  have hH j : 0 ≤ H j := by
    dsimp only [H, bilinearConstant]
    exact mul_nonneg (norm_nonneg
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)) (Finset.sum_nonneg fun i _ ↦
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB i)) (hA (j - i)))
  have hX : IsCompact (Prod.fst '' tsupport θ) := hcθ.image continuous_fst
  refine ⟨S, hS, H, hH, hX, ?_⟩
  intro R₀ hR₀ stage u ell hu Q hQ φ
  let f := Function.uncurry (retainedPhaseExtension T Q θ)
  have hf : ContDiff ℝ ∞ f := contDiff_retainedPhaseExtension T Q hθ hsθ
  have hφ : ContDiff ℝ ∞ (Function.uncurry φ) :=
    hf.comp (contDiff_snd.prodMk contDiff_fst)
  have hL : 1 ≤ currentCoefficientScale R₀ stage :=
    one_le_currentCoefficientScale (by linarith [hS.trans hR₀]) stage
  refine ⟨hφ, ?_, ?_⟩
  · intro c
    apply closure_minimal _ hX.isClosed
    intro x hx
    refine ⟨(x,c), ?_, rfl⟩
    apply subset_tsupport
    intro hz
    apply hx
    change θ (x,c) • phase T Q x c.2 = 0
    rw [hz, zero_smul]
  · intro c x j
    have hraw : ContDiffOn ℝ ∞ (fun w : Euclidean (d + 1) × (Euclidean 3 × Euclidean d) ↦
        phase T Q w.1 w.2.2) (domain T) := RawPrimary.contDiffOn_fullPhase T Q (fun _ h ↦ h)
    have hb (k : ℕ) (w : Euclidean (d + 1) × (Euclidean 3 × Euclidean d))
        (hw : w ∈ tsupport θ) :
        ‖iteratedFDeriv ℝ k (fun z ↦ phase T Q z.1 z.2.2) w‖ ≤
          A k * currentCoefficientScale R₀ stage ^ k := by
      have hh := hphase R₀ hR₀ stage u ell hu Q hQ k
      simp only [Nat.sub_zero, fullSourcePhaseInCoordinates, hid] at hh
      exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hcθ
        (fun z hz ↦ (hraw.contDiffAt ((isOpen_domain T).mem_nhds (hsθ hz))).of_le
          (by simp)) hw le_rfl).trans hh
    have hglobal : ‖iteratedFDeriv ℝ j f (x,c)‖ ≤ H j * currentCoefficientScale R₀ stage ^ j := by
      have he : f = cutoffExtension θ
          (fun w : Euclidean (d + 1) × (Euclidean 3 × Euclidean d) ↦ phase T Q w.1 w.2.2) := by
        funext w
        rfl
      rw [he]
      simpa only [H, Nat.sub_zero] using
        norm_jet_cutoffExtension_le (isOpen_domain T) hθ hsθ hraw B A hB hA hL 0 j
          (fun k _ z ↦ hjetθ k k le_rfl z)
          (fun k _ z hz ↦ by simpa only [Nat.sub_zero] using hb k z hz) le_rfl (x,c)
    have hswap := (LinearIsometryEquiv.prodComm ℝ (Euclidean 3 × Euclidean d) (Euclidean (d + 1))).norm_iteratedFDeriv_comp_right f (c,x) j
    exact hswap.le.trans hglobal

end JanetCartan.PhysicalParameterRemainder
