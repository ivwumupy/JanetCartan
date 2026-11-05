module

public import JanetCartan.Iteration.PhysicalParameterRemainder.FullPhase
public import JanetCartan.Iteration.PhysicalEllipticWords.Coefficients
public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.GradientBand

/-!
# Original full source phase for the physical elliptic letters

The supplied original phase cutoff is retained. No second representative is
chosen. Actual physical histories supply all reserved jets and the low C² bound
needed by the complete endpoint/algebraic PDO application.
Consumer: `app:ch_response:eq:direct-envelope-profile`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalEllipticWords
open ActualCarriers ActualCarriers.CurrentFullPhase HamiltonPhase FrozenMenu
open ResponseTransfer ResponseTransfer.RetainedFactors CompatibleResponse
open GeometricProfile ProtectedFlow ProjectedStressFrame LeadingWave.FullModulation

variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
local notation "Par" => Euclidean 3 × Euclidean d

/-- Preserve the original phase cutoff and derive the actual complete-window
profiles, including the scale-independent C² bound. All constants precede the
history, source parameters, and differentiation order. -/
theorem exists_history_elliptic_phase_profiles (i : Fin (d + 1))
    (χp : E × Par → ℝ) (hχp : ContDiff ℝ ∞ χp)
    (hχdomain : ∀ q ∈ tsupport χp,
      ((primaryCoordinateChange i).symm q.1, q.2.2) ∈ phaseDomain T)
    {KP : Set (E × Par)} (hKP : IsCompact KP)
    (hKD : ∀ q ∈ KP, ((primaryCoordinateChange i).symm q.1, q.2.2) ∈ phaseDomain T)
    (hχone : ∀ q ∈ KP, χp =ᶠ[𝓝 q] (fun _ ↦ 1))
    (G : FlatReference (d + 1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0)
    (hextradius : ext.radius = r) {Cband : ℝ} (hband : 1 ≤ Cband)
    {rStar reserve kMin : ℕ} (hStar : 8 ≤ rStar) (hreserve : reserve + 3 ≤ rStar)
    (hreserve2 : 2 ≤ reserve)
    (horder : RevisedScales.displacementLoss (d + 1) +
      bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < (kMin : ℝ)) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ A : ℕ → ℝ, (∀ k, 0 ≤ A k) ∧ ∀ Q,
      let φ := fun q : E × Par ↦ χp q * T.fullSourcePhaseInCoordinates i Q q.1 q.2
      ContDiff ℝ ∞ φ ∧
        (∀ q ∈ KP, φ =ᶠ[𝓝 q] Function.uncurry (T.fullSourcePhaseInCoordinates i Q)) ∧
        ∀ R₀, S ≤ R₀ →
        ∀ (j : ℕ) (u : Fin j → SchwartzMap E (Euclidean (embeddingDimension (d + 1))))
          (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory Cband R₀ kMin u ell →
        Q.1 = extendedProjectedStress ext (RevisedGlobal.finiteMap G.map u) →
        cNorm KP 2 φ ≤ A 2 ∧
          (∀ k, cNorm KP k φ ≤ A k * currentCoefficientScale R₀ j ^ (k - reserve)) ∧
          ∀ k q, q ∈ KP → ‖iteratedFDeriv ℝ k φ q‖ ≤
            A k * currentCoefficientScale R₀ j ^ (k - reserve) := by
  let Ω := (fun q : E × Par ↦ ((primaryCoordinateChange i).symm q.1, q.2.2)) ⁻¹' phaseDomain T
  have hΩ : IsOpen Ω := isOpen_ball.preimage
    (((primaryCoordinateChange i).symm.continuous.comp continuous_fst).prodMk continuous_snd.snd)
  obtain ⟨S, hS, A, hA, hp⟩ := T.exists_physical_history_full_source_phase_profiles
    i hKP hKD G hr hrR hR ext hextcenter hextradius hband hStar hreserve horder
  refine ⟨S, hS, A, hA, ?_⟩
  intro Q φ
  have hraw := T.fullSourcePhaseInCoordinates_smooth i Q (Ω := Ω) (fun _ h ↦ h)
  have hφ : ContDiff ℝ ∞ φ := by
    apply contDiff_iff_contDiffAt.mpr
    intro q
    by_cases hq : q ∈ tsupport χp
    · exact hχp.contDiffAt.mul (hraw.contDiffAt (hΩ.mem_nhds (hχdomain q hq)))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hq] with b hb
      exact mul_eq_zero_of_left hb _
  have he q (hq : q ∈ KP) : φ =ᶠ[𝓝 q] Function.uncurry (T.fullSourcePhaseInCoordinates i Q) := by
    filter_upwards [hχone q hq] with b hb
    change χp b * _ = _
    rw [hb, one_mul]
    rfl
  refine ⟨hφ, he, ?_⟩
  intro R₀ hR₀ j u ell hu hQ
  have hb k : cNorm KP k φ ≤ A k * currentCoefficientScale R₀ j ^ (k - reserve) := by
    rw [cNorm_eq_of_eventuallyEq he k]
    exact hp R₀ hR₀ j u ell hu Q hQ k
  refine ⟨?_, hb, ?_⟩
  · simpa only [Nat.sub_eq_zero_of_le hreserve2, pow_zero, mul_one] using hb 2
  · intro k q hq
    exact (norm_iteratedFDeriv_le_cNorm hKP (hφ.of_le (by simp)) hq le_rfl).trans (hb k)

end JanetCartan.PhysicalEllipticWords
