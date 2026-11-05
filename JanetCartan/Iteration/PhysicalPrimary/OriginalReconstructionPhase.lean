module

public import JanetCartan.Iteration.PhysicalParameterRemainder.PhaseProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.InitializedRealization.ClassicalReconstruction

/-!
# Sharp retained-phase profiles for the actual uncut reconstruction

The ordinary observation phase only retained reserve zero. Reconstruction of
an r-reserved physical response needs reserve r+1 for the full joint phase,
so one physical phase derivative still retains r. This leaf applies the
existing physical full-source phase theorem with its actual arbitrary reserve,
then the SAME fixed phase cutoff, including its shoulders.
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalPrimary.OriginalReconstructionPhase
open ActualCarriers FrozenMenu CurrentFullPhase ResponsePrimarySources
open CompatibleResponse GeometricProfile ProtectedFlow LeadingWave.FullModulation
open ResponseTransfer.GradedPrimitives
open JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily

/-- Preserve an arbitrary reserve through the original retained-phase cutoff.
The constants precede the physical Schwartz history and the SAME allowed
extension. With reserve r+1, this produces the phase-gradient input of
`completedVariationComplex_joint_response_graded` at reserve r
(`app:ch_response:eq:response-reconstruction-grading`). -/
theorem exists_physical_retained_phase_reserved_profiles
    {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (θ : Euclidean (d + 1) × (Euclidean 3 × Euclidean d) → ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hcθ : HasCompactSupport θ) (hsθ : tsupport θ ⊆ domain T)
    (G : FlatReference (d + 1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (ext : BallExtension.Parameters (Euclidean (d + 1)))
    (hextcenter : ext.center = 0) (hextradius : ext.radius = r)
    {Cband : ℝ} (hband : 1 ≤ Cband)
    {rStar reserve kMin : ℕ} (hStar : 8 ≤ rStar) (hreserve : reserve+3 ≤ rStar)
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
          H j * currentCoefficientScale R₀ stage ^ (j-reserve) := by
  have hid (y : Euclidean (d + 1)) :
      (primaryCoordinateChange (0 : Fin (d + 1))).symm y = y :=
    (RegularSector.Characteristic.coordinateSplit (0 : Fin (d + 1))).symm_apply_apply y
  obtain ⟨S, hS, A, hA, hphase⟩ := T.exists_physical_history_full_source_phase_profiles
    0 hcθ (fun q hq ↦ by rw [hid]; exact hsθ hq)
    G hr hrR hR ext hextcenter hextradius hband hStar hreserve horder
  choose B hB hjetθ using fun j ↦ hcθ.exists_bound_iteratedFDeriv hθ j
  let H := bilinearConstant
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) B A
  have hH j : 0 ≤ H j := by
    dsimp only [H, bilinearConstant]
    exact mul_nonneg (norm_nonneg
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)) (Finset.sum_nonneg fun i _ ↦
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB i)) (hA (j-i)))
  have hX : IsCompact (Prod.fst '' tsupport θ) := hcθ.image continuous_fst
  refine ⟨S,hS,H,hH,hX,?_⟩
  intro R₀ hR₀ stage u ell hu Q hQ φ
  let f := Function.uncurry (retainedPhaseExtension T Q θ)
  have hf : ContDiff ℝ ∞ f := contDiff_retainedPhaseExtension T Q hθ hsθ
  have hφ : ContDiff ℝ ∞ (Function.uncurry φ) :=
    hf.comp (contDiff_snd.prodMk contDiff_fst)
  have hL : 1 ≤ currentCoefficientScale R₀ stage :=
    one_le_currentCoefficientScale (by linarith [hS.trans hR₀]) stage
  refine ⟨hφ,?_,?_⟩
  · intro c
    apply closure_minimal _ hX.isClosed
    intro x hx
    refine ⟨(x,c),?_,rfl⟩
    apply subset_tsupport
    intro hz
    apply hx
    change θ (x,c) • phase T Q x c.2 = 0
    rw [hz,zero_smul]
  · intro c x j
    have hraw : ContDiffOn ℝ ∞ (fun w : Euclidean (d+1) × (Euclidean 3 × Euclidean d) ↦
        phase T Q w.1 w.2.2) (domain T) := RawPrimary.contDiffOn_fullPhase T Q (fun _ h ↦ h)
    have hb (k : ℕ) (w : Euclidean (d+1) × (Euclidean 3 × Euclidean d))
        (hw : w ∈ tsupport θ) :
        ‖iteratedFDeriv ℝ k (fun z ↦ phase T Q z.1 z.2.2) w‖ ≤
          A k * currentCoefficientScale R₀ stage ^ (k-reserve) := by
      have hh := hphase R₀ hR₀ stage u ell hu Q hQ k
      simp only [fullSourcePhaseInCoordinates,hid] at hh
      exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hcθ
        (fun z hz ↦ (hraw.contDiffAt ((isOpen_domain T).mem_nhds (hsθ hz))).of_le
          (by simp)) hw le_rfl).trans hh
    have hglobal : ‖iteratedFDeriv ℝ j f (x,c)‖ ≤
        H j * currentCoefficientScale R₀ stage ^ (j-reserve) := by
      have he : f = cutoffExtension θ
          (fun w : Euclidean (d+1) × (Euclidean 3 × Euclidean d) ↦ phase T Q w.1 w.2.2) := by
        funext w
        rfl
      rw [he]
      simpa only [H] using norm_jet_cutoffExtension_le (isOpen_domain T) hθ hsθ hraw
        B A hB hA hL reserve j (fun k _ z ↦ hjetθ k k le_rfl z)
        (fun k _ z hz ↦ hb k z hz) le_rfl (x,c)
    have hswap := (LinearIsometryEquiv.prodComm ℝ (Euclidean 3 × Euclidean d)
      (Euclidean (d+1))).norm_iteratedFDeriv_comp_right f (c,x) j
    exact hswap.le.trans hglobal

/-- A parameter-first phase with one extra joint reserve supplies every
complex physical-gradient coefficient at the intended reconstruction reserve.
The coordinate swap and real-to-complex inclusion are isometries, so the only
cost is the already paid single physical derivative. -/
theorem parameter_phase_reserved_gradient {d : ℕ}
    {φ : (Euclidean 3 × Euclidean d) → Euclidean (d+1) → ℝ}
    {H : ℕ → ℝ} {K : ℝ} {reserve : ℕ}
    (hφ : ContDiff ℝ ∞ (Function.uncurry φ))
    (hjet : ∀ c x j, ‖iteratedFDeriv ℝ j (Function.uncurry φ) (c,x)‖ ≤
      H j * K^(j-(reserve+1))) :
    (∀ i : Fin (d+1), ContDiff ℝ ∞
      (fun q : Euclidean (d+1) × (Euclidean 3 × Euclidean d) ↦
        ((partialDeriv (φ q.2) q.1 i : ℝ) : ℂ))) ∧
    ∀ i : Fin (d+1), ∀ m q,
      ‖iteratedFDeriv ℝ m
        (fun p : Euclidean (d+1) × (Euclidean 3 × Euclidean d) ↦
          ((partialDeriv (φ p.2) p.1 i : ℝ) : ℂ)) q‖ ≤
        H (m+1) * K^(m-reserve) := by
  let f := fun q : Euclidean (d+1) × (Euclidean 3 × Euclidean d) ↦ φ q.2 q.1
  have hf : ContDiff ℝ ∞ f := hφ.comp (contDiff_snd.prodMk contDiff_fst)
  have hpartial (i : Fin (d+1)) : ContDiff ℝ ∞
      (fun p : Euclidean (d+1) × (Euclidean 3 × Euclidean d) ↦
        partialDeriv (φ p.2) p.1 i) :=
    contDiffOn_univ.mp (CanonicalAtomRealization.contDiffOn_physical_fderiv_of_joint
      isOpen_univ hf.contDiffOn (EuclideanSpace.single i 1))
  refine ⟨fun i ↦ Complex.ofRealCLM.contDiff.comp (hpartial i),?_⟩
  intro i m q
  rcases q with ⟨x,c⟩
  change ‖iteratedFDeriv ℝ m (Complex.ofRealLI ∘
    (fun p ↦ partialDeriv (φ p.2) p.1 i)) (x,c)‖ ≤ _
  rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left (hpartial i).contDiffAt (by simp)]
  apply (CanonicalAtomRealization.norm_iteratedFDeriv_physical_fderiv_le_joint
    isOpen_univ hf.contDiffOn (EuclideanSpace.single i 1)
    (by simp [EuclideanSpace.single,PiLp.norm_single]) m (mem_univ (x,c))).trans
  have hswap := (LinearIsometryEquiv.prodComm ℝ (Euclidean (d+1))
    (Euclidean 3 × Euclidean d)).norm_iteratedFDeriv_comp_right (Function.uncurry φ) (x,c) (m+1)
  apply hswap.le.trans
  simpa [Prod.swap, Nat.add_sub_add_right,LinearIsometryEquiv.prodComm_apply] using hjet c x (m+1)

end JanetCartan.PhysicalPrimary.OriginalReconstructionPhase
