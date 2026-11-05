module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.Quadrature
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.RoughBounds.Matching
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.TransportComparison.Realized

/-!
# Three background estimates for the SAME actual retained family

Construct the carrier tensor and its compact Lebesgue-L2 classes from the
original immersion/scalar profiles and retained primitive outputs. The literal
eta-zero differential is identified before applying quadrature, physical rough
bounds and the inverse-frequency transport comparison. All auxiliary carrier
and physical extensions disappear under the original measurements.

Consumers: `app:ch_waves:eq:background-quadrature`,
`app:ch_waves:eq:background-quadrature-rough`, and the adjacent `O(λ⁻¹)` estimate.
The common finite-family selection belongs to the sampling parent; its retained
inputs are supplied by `RawPrimary.exists_finite_retained_graded_raw_family_with_primitives`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.RetainedBackground
open RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ProjectedStressFrame AmbientResponse ResponseTransfer MeasuredAmplitude
open SeparatedSampling LatticeQuadrature BackgroundQuadrature

/-- Actual retained background estimates at the manuscript's order `p=2*n-1`.
The original input profiles produce every classical and L2 regularity/jet
obligation. The SAME L2 family represents the original localized differential
under `ψ`, and its zero endpoint represents the original transported tensor.
The rough estimate is stated directly for the original localized differential.
All constants precede the varying fields, frequencies, radial labels and `L`;
all realizations use the unchanged window, weights and original measures.
Sources: `app:ch_waves:eq:background-quadrature`,
`app:ch_waves:eq:background-quadrature-rough`, and their adjacent comparison. -/
theorem exists_retainedBackground_estimates
    {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hcarrier : closedBall a.2.1 (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    {K : Set (Euclidean (m + 1))} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius ⊆ K)
    (hspace : closedBall a.1 (2 * ρ) ⊆ K)
    (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (I : Set (Euclidean ((m + 1) - 1) × Euclidean 3))
    {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (AF Ar E Γ : ℕ → ℝ) (hAF : ∀ j, 0 ≤ AF j) (hAr : ∀ j, 0 ≤ Ar j)
    (hE : ∀ j, 0 < E j) (hΓ : ∀ j, 0 < Γ j)
    (χ : Euclidean (m + 1) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (ψ : SeparatedSampling.Point → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hχsupport : Function.support χ ⊆ closedBall a.1 (ρ / 2))
    (hψsupport : ∀ z, ψ z ≠ 0 → (WithLp.toLp 2 z,
      T.reference.spatialPatch (WithLp.toLp 2 z)) ∈ closedBall a.2 (ρ / 4))
    {Bpatch Ppatch : ℝ} (hpatch : SeparatedSampling.PatchBounds ψ Bpatch Ppatch)
    {kernel : ℝ → ℝ} (hkc : HasCompactSupport kernel) (hks : ContDiff ℝ ∞ kernel)
    (hkm : ∫ t, kernel t = 1) (hkn : ∀ t, 0 ≤ kernel t)
    (hksupport : Function.support kernel ⊆ Icc (-(1 / 4)) (1 / 4)) :
    ∃ A : ℕ → ℝ, (∀ j, 0 < A j) ∧
      ∀ (F : Euclidean (m + 1) → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ hlow : cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (m + 1)) < T.family.threshold,
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      ∀ (row col : Fin (m + 1))
        (Φ Y : ℝ × (Euclidean ((m + 1) - 1) × (Euclidean 3 × Euclidean ((m + 1) - 1))) →
          Euclidean ((m + 1) - 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))
        (r : Euclidean ((m + 1) - 1) × Euclidean 3 → ℝ)
        (Ω : Set (Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))),
      IsOpen Ω → closedBall a (2 * ρ) ⊆ Ω →
      ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω →
      (∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0) →
      (∀ j,
        let J := closedBall a ρ
        let b₀ := fullLeadingCovector T Q F row col Φ Y r
        let ξ := fun w : Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)) ↦
          phaseGradient T Q w.1 w.2.2
        let ν := fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
        let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
        cNorm J j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J j b₀ +
          cNorm J j ν + cNorm J j V + cNorm J j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
            E j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) r)) →
      (∀ j, cNorm (closedBall a ρ) j (fullCorrectionCovector T Q F row col Φ Y r) ≤
        Γ j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) r)) →
      ∀ (RF Rr rpar : ℕ) (L : ℝ), 1 ≤ L →
      2 * (m + 1) - 1 < rpar →
      14 + (rpar + 2) ≤ RF → 14 + (rpar + 2) ≤ Rr →
      HasDerivativeProfile K F RF L AF → HasDerivativeProfile I r Rr L Ar →
      let H := retainedBackgroundCarrier T a hρ Q F row col Φ Y r χ
      let f := fun q : ℝ × (SeparatedSampling.Point × Euclidean (m + 1)) ↦
        H q.1 q.2.1 q.2.2
      let J := closedBall a.1 (3 * ρ / 4)
      let p := 2 * (m + 1) - 1
      ∃ hHs : ContDiff ℝ ∞ f,
      ∃ hSs : ∀ τ z x, x ∉ J → H τ z x = 0,
      let HL := backgroundL2 (isCompact_closedBall a.1 (3 * ρ / 4)) hHs hSs
      (∀ τ, τ ≠ 0 → ∀ z,
        (ψ z • HL (τ, z)) =ᵐ[volume]
          fun x ↦ ψ z • localizedBackground T Q F row col Φ Y r χ τ (WithLp.toLp 2 z) x) ∧
      (∀ z, (ψ z • HL (0, z)) =ᵐ[volume]
        fun x ↦ ψ z • localizedTransportBackground T Q F row col Φ Y r χ
          (WithLp.toLp 2 z) x) ∧
      ∀ (R : (Fin 3 → Fin (p + 1)) → ℝ), (∀ c, 1 ≤ R c) →
      ∀ (lam : ℝ), 1 ≤ lam →
      let τ := fun c ↦ (R c * lam)⁻¹
      ∀ (h : ℝ), 0 < h → h ≤ 1 →
      ∀ (shifts : Lattice → Point), (∀ q i, 0 ≤ shifts q i ∧ shifts q i < h) →
      (‖(∑ a ∈ samples p Bpatch ψ (convolvedBoxWindow kernel p) h shifts,
          weight ψ (convolvedBoxWindow kernel p) h shifts a •
            HL (τ (color p a.1), node h shifts a)) -
        ∑ c, ∫ z : Point,
          coloredBlockMask p (integerCube (blockCutoff p Bpatch h))
            (convolvedBoxWindow kernel p) h c z • (ψ z • HL (τ c, z))‖ ≤
        (backgroundQuadratureConstant p Bpatch *
          CompactTensor.physicalL2Constant (isCompact_closedBall a.1 (3 * ρ / 4)) * A p) * h ^ p) ∧
      (‖(∑ c, ∫ z : Point,
          coloredBlockMask p (integerCube (blockCutoff p Bpatch h))
            (convolvedBoxWindow kernel p) h c z • (ψ z • HL (τ c, z))) -
        ∫ z : Point, ψ z • HL (0, z)‖ ≤
        ((∫ z, ψ z) * (CompactTensor.physicalL2Constant
          (isCompact_closedBall a.1 (3 * ρ / 4)) * A 1)) * lam⁻¹) ∧
      (∀ (D : Set (Euclidean (m + 1))) (k : ℕ), IsCompact D →
        cNorm D k (fun x ↦
          (∑ a ∈ samples p Bpatch ψ (convolvedBoxWindow kernel p) h shifts,
            weight ψ (convolvedBoxWindow kernel p) h shifts a •
              localizedBackground T Q F row col Φ Y r χ (τ (color p a.1))
                (WithLp.toLp 2 (node h shifts a)) x) -
          ∑ c, ∫ z : Point,
            coloredBlockMask p (integerCube (blockCutoff p Bpatch h))
              (convolvedBoxWindow kernel p) h c z •
                (ψ z • localizedBackground T Q F row col Φ Y r χ (τ c) (WithLp.toLp 2 z) x)) ≤
          (2 * (countConstant p Bpatch * Ppatch) *
            (∑ j ∈ Finset.range (k + 1), A j)) * L ^ k) := by
  obtain ⟨A, hA, hprod⟩ := exists_retainedBackgroundCarrier_budgets
    (N := N) T hP a hρ hcarrier hK hKU hball hspace hphase I hγ hκ
    AF Ar E Γ hAF hAr hE hΓ χ hχ ψ hψ hχsupport hψsupport
  refine ⟨A, hA, ?_⟩
  intro F hF hi hrank hmetric hnormal hlow Q row col Φ Y r Ω hΩ hflow hα hnonzero
    hleading hcorrection RF Rr rpar L hL hreserve hRF hRr hpF hpr H f J p
  obtain ⟨hsmooth, _, hsupport, hjets, hmatch⟩ :=
    hprod F hF hi hrank hmetric hnormal hlow row col Φ Y r Ω hΩ hflow hα hnonzero
      hleading hcorrection RF Rr rpar L hL hRF hRr hpF hpr
  have hS : ∀ τ z x, x ∉ J → H τ z x = 0 := by
    intro τ z x hx
    exact image_eq_zero_of_notMem_tsupport (fun hh ↦ hx ((hsupport τ z).1 hh))
  refine ⟨hsmooth, hS, ?_⟩
  let HL := backgroundL2 (isCompact_closedBall a.1 (3 * ρ / 4)) hsmooth hS
  have hAE (τ : ℝ) (z : Point) : (ψ z • HL (τ, z)) =ᵐ[volume]
      fun x ↦ ψ z • H τ z x := by
    filter_upwards [backgroundL2_ae (isCompact_closedBall a.1 (3 * ρ / 4))
      hsmooth hS τ z, Lp.coeFn_smul (ψ z) (HL (τ, z))] with x hx hy
    rw [hy]
    change ψ z • HL (τ, z) x = ψ z • H τ z x
    rw [hx]
  refine ⟨?_, ?_, ?_⟩
  · intro τ hτ z
    exact (hAE τ z).trans (Eventually.of_forall fun x ↦ hmatch τ hτ z x)
  · intro z
    apply (hAE 0 z).trans (Eventually.of_forall ?_)
    intro x
    exact weighted_retainedBackgroundCarrier_zero T a hρ Q F row col Φ Y r
      χ ψ hχsupport hψsupport z x
  · intro R hR lam hlam τ h hh hh₁ shifts hshifts
    have hp : 0 < p := by dsimp [p]; omega
    have hτ (c) : τ c ∈ Icc (-1 : ℝ) 1 := by
      have hprod : 1 ≤ R c * lam := one_le_mul_of_one_le_of_one_le (hR c) hlam
      exact ⟨le_trans (by norm_num) (inv_nonneg.mpr (by linarith)),
        inv_le_one_of_one_le₀ hprod⟩
    have hτne (c) : τ c ≠ 0 :=
      inv_ne_zero (mul_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one (hR c)))
        (ne_of_gt (lt_of_lt_of_le zero_lt_one hlam)))
    have hju : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ z x j,
        ‖iteratedFDeriv ℝ j f (τ, (z, x))‖ ≤ A j * L ^ (j - rpar) :=
      fun τ hτ z x j ↦ (hjets τ hτ z x j).1
    have hjw : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ z x j,
        ‖iteratedFDeriv ℝ j (fun q ↦ ψ q.2.1 • f q) (τ, (z, x))‖ ≤
          A j * L ^ (j - rpar) := fun τ hτ z x j ↦ (hjets τ hτ z x j).2
    refine ⟨?_, ?_, ?_⟩
    · exact norm_retainedBackground_quadrature_le (isCompact_closedBall a.1 (3 * ρ / 4))
        hsmooth hS hkc hks hkm hkn hksupport hp hpatch hψ (fun j ↦ (hA j).le)
        hL hreserve.le hjw τ hτ hh hh₁ shifts hshifts
    · exact norm_backgroundL2_colored_sub_transport_le (isCompact_closedBall a.1 (3 * ρ / 4))
        hsmooth hS hkc hks hkm hkn hksupport hp hpatch hψ.continuous
        (fun j ↦ (hA j).le) hL (by omega) hju R hR hlam hh hh₁
    · intro D k hD
      let G := fun c z x ↦ localizedBackground T Q F row col Φ Y r χ (τ c) (WithLp.toLp 2 z) x
      have heq (x) :
          ((∑ a ∈ samples p Bpatch ψ (convolvedBoxWindow kernel p) h shifts,
            weight ψ (convolvedBoxWindow kernel p) h shifts a •
              H (τ (color p a.1)) (node h shifts a) x) -
          ∑ c, ∫ z : Point,
            coloredBlockMask p (integerCube (blockCutoff p Bpatch h))
              (convolvedBoxWindow kernel p) h c z • (ψ z • H (τ c) z x)) =
          ((∑ a ∈ samples p Bpatch ψ (convolvedBoxWindow kernel p) h shifts,
            weight ψ (convolvedBoxWindow kernel p) h shifts a •
              G (color p a.1) (node h shifts a) x) -
          ∑ c, ∫ z : Point,
            coloredBlockMask p (integerCube (blockCutoff p Bpatch h))
              (convolvedBoxWindow kernel p) h c z • (ψ z • G c z x)) := by
        rw [background_sample_eq_of_weighted_eq Bpatch (convolvedBoxWindow kernel p) h shifts
          (fun c z ↦ hmatch (τ c) (hτne c) z x),
          background_colored_eq_of_weighted_eq (integerCube (blockCutoff p Bpatch h))
            (convolvedBoxWindow kernel p) h (fun c z ↦ hmatch (τ c) (hτne c) z x)]
      have hsliced (c) : ContDiff ℝ ∞
          (fun q : Euclidean (m + 1) × Point ↦ H (τ c) q.2 q.1) := by
        exact hsmooth.comp
          (f := fun q : Euclidean (m + 1) × Point ↦ (τ c, (q.2, q.1)))
          (contDiff_const.prodMk (contDiff_snd.prodMk contDiff_fst))
      have hr := cNorm_background_sample_sub_colored_profile_le (r := k)
        (convolvedBoxWindow_bounds (hks.continuous.integrable_of_hasCompactSupport hkc)
          hkm hkn hksupport hp) (contDiff_convolvedBoxWindow hkc hks p)
        hpatch hψ (fun c ↦ H (τ c)) hsliced
        (fun j ↦ (hA j).le) hL
        (fun j _ c z x ↦ (norm_iteratedFDeriv_carrierPhysicalSlice_le hsmooth (τ c) z x j).trans
          (hju (τ c) (hτ c) z x j)) hD hh hh₁ shifts
      simp_rw [heq] at hr
      simpa only [one_pow, mul_one] using hr

end JanetCartan.Sampling.RetainedBackground
