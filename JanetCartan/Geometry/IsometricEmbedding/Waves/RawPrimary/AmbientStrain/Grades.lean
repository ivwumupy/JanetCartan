module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmbientStrain.Estimates
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Profiles

/-!
# Cubic joint strain grade of the SAME primary atom

For `app:ch_waves:eq:WKB-strain`, the reserve-fourteen correction budget is
supplied by `exists_fullCorrectionCovector_transport_bounds` and retained by
`exists_finite_actual_corrected_family`. The original immersion and scalar
profiles supply its low norm and all high norms. The actual projected
reconstruction, including its inverse Gram, is estimated here. The exact
ambient identity is derived from the leading outputs, not assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.RawPrimary
open ProjectedStressFrame GeometricProfile NullTransport
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

/-- The complete joint ambient strain grade for the SAME `fullPrimaryAtom`.
The constants precede the immersion, initial scalar, scale and frequency.
The only quantitative correction input is exactly the reserve-fourteen
budget exported by `exists_finite_actual_corrected_family`; it is not an
ambient strain estimate. The `rpar + 2` primitive allowance pays for the
physical derivative of that correction. A joint jet of order `j + k`
controls every mixed physical/parameter derivative of those orders, in the
Frobenius tensor norm (`app:ch_waves:eq:WKB-strain`). The parent must apply
this on its single initialized reference and its original finite family. -/
theorem exists_fullPrimaryStrain_joint_grade
    {n : ℕ} (hn : 5 ≤ n) {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    {ρ : ℝ} (hρ : 0 < ρ) {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hx : MapsTo Prod.fst (closedBall a ρ) K) (M : ℝ)
    {κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (AF Ar Γ : ℕ → ℝ) (hAF : ∀ m, 0 ≤ AF m) (hAr : ∀ m, 0 ≤ Ar m)
    (hΓ : ∀ m, 0 ≤ Γ m) :
    ∃ C : ℕ → ℕ → ℝ, (∀ j k, 0 < C j k) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
        (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < T.family.threshold})
        (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
          Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
        (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
        (Kr : Set (Euclidean (n - 1) × Euclidean 3))
        (Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))),
        Q.1 = projectedStress F → IsOpen Ω → closedBall a ρ ⊆ Ω →
        MapsTo Prod.fst Ω K →
        (∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T) →
        ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
        cNorm K 14 F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖^2 ≤ ‖fderiv ℝ F x v‖^2) →
        (∀ x ∈ K, ∀ v ∈ normalSpace F x,
          κnormal * ‖v‖ ≤ ‖normalPairing F (fun _ ↦ v) x‖) →
        (∀ i, cNorm K 6 (fun x ↦ projectedStress F x i - cubeStress n i) <
          ambientStrainFrameThreshold hn) →
        ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω →
        (∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0) →
        (∀ w ∈ Ω, conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
          (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2) •
            nullvector T Q col (x, w.2)) w.1 = 0) →
        (∀ m, cNorm (closedBall a ρ) m (fullCorrectionCovector T Q F row col Φ Y r) ≤
          Γ m * (1 + cNorm K (m + 14) F + cNorm Kr (m + 14) r)) →
        ∀ (RF Rr rpar : ℕ) (L : ℝ),
          HasDerivativeProfile K F RF L AF → HasDerivativeProfile Kr r Rr L Ar →
          1 ≤ L → 14 + (rpar + 2) ≤ RF → 14 + (rpar + 2) ≤ Rr →
          ∀ j k, k ≤ rpar → ∀ w ∈ closedBall a ρ, ∀ τ : ℝ, 0 < τ →
            ‖iteratedFDeriv ℝ (j + k)
              (fullPrimaryStrainAmplitude T Q F row col Φ Y r τ) w‖ ≤
              C j k * τ^3 * L^j := by
  let B : ℕ → ℝ := fun m ↦ Γ m * (1 + AF (m + 14) + Ar (m + 14))
  have hB (m) : 0 ≤ B m := mul_nonneg (hΓ m) (by have := hAF (m + 14); have := hAr (m + 14); positivity)
  obtain ⟨D, hD, hbound⟩ := AmbientStrain.exists_projected_reconstruction_bounds
    hn a hρ hK hx M (B 1) hκmet hκnormal
  let C : ℕ → ℕ → ℝ := fun j k ↦ 2 * D (j + k) * (1 + AF (j + k + 2) + B (j + k + 1))
  refine ⟨C, fun j k ↦ by
    dsimp [C]
    have := hD (j + k)
    have := hAF (j + k + 2)
    have := hB (j + k + 1)
    positivity, ?_⟩
  intro F Q row col Φ Y r Kr Ω hprojected hΩ hball hΩK hphase hF hi hrank hFM
    hmet hnormal hclose hα hnonzero htransport hbudget RF Rr rpar L hpF hpr hL hRF hRr
    j k hk w hw τ hτ
  have hspace : MapsTo Prod.fst Ω U := fun y hy ↦ hKU (hΩK hy)
  let b := fullCorrectionCovector T Q F row col Φ Y r
  have hb : ContDiffOn ℝ ∞ b Ω := contDiffOn_fullCorrectionCovector_of_leading_outputs
    T Q F row col Φ Y r hΩ (fun y hy ↦ hspace hy) hphase hF hi hα hnonzero
  have hp : HasDerivativeProfile (closedBall a ρ) b (rpar + 2) L B :=
    AmplitudeGrades.profile_of_two_input_budget hpF hpr hL hAF hAr hΓ hRF hRr hbudget
  have hlow : cNorm (closedBall a ρ) 1 b ≤ B 1 := by
    simpa only [show 1 - (rpar + 2) = 0 by omega, pow_zero, mul_one] using hp 1
  have hout := hbound U Ω hU hΩ hKU hball hspace F b hF hi hrank hb
    ((cNorm_mono_order (by omega)).trans hFM) hlow hmet hnormal hclose (j + k)
  let E := fun y : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
    WKB.stressReconstruction (projectedStress F y.1)
      (fun i ↦ complexReducedOperator F (projectedStress F) (fun x ↦ b (x, y.2)) y.1 i)
  have hE : ∀ y ∈ closedBall a ρ, ContDiffAt ℝ ∞ E y := hout.2
  have hFn : cNorm K (j + k + 2) F ≤ AF (j + k + 2) * L^j :=
    (hpF _).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (by omega : j + k + 2 - RF ≤ j)) (hAF _))
  have hbn : cNorm (closedBall a ρ) (j + k + 1) b ≤ B (j + k + 1) * L^j :=
    (hp _).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (by omega : j + k + 1 - (rpar + 2) ≤ j)) (hB _))
  have hEn : ‖iteratedFDeriv ℝ (j + k) E w‖ ≤
      D (j + k) * (1 + AF (j + k + 2) + B (j + k + 1)) * L^j := by
    apply (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a ρ)
      (fun y hy ↦ (hE y hy).of_le (by simp)) hw le_rfl).trans
    apply hout.1.trans
    exact (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (one_le_pow₀ hL) hFn) hbn) (hD _).le).trans_eq (by ring)
  have he : fullPrimaryStrainAmplitude T Q F row col Φ Y r τ =ᶠ[𝓝 w]
      (fun y ↦ ((2 : ℂ) * (τ : ℂ)^3) • E y) := by
    filter_upwards [hΩ.mem_nhds (hball hw)] with y hy
    have hh := fullPrimaryAtom_demodulated_strain_of_leading_outputs
      T Q row col Φ Y r hn F hprojected hK hKU hclose hΩ
        (fun y hy ↦ hspace hy) hphase hF hi hrank hα hnonzero htransport hy (hΩK hy) hτ.ne'
    simpa only [E, b, hprojected] using hh
  rw [(he.iteratedFDeriv (𝕜 := ℝ) (n := j + k)).eq_of_nhds,
    iteratedFDeriv_const_smul_apply' ((hE w hw).of_le (by simp)), norm_smul]
  have hnorm : ‖(2 : ℂ) * (τ : ℂ)^3‖ = 2 * τ^3 := by
    rw [norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
  rw [hnorm]
  exact (mul_le_mul_of_nonneg_left hEn (by positivity : 0 ≤ 2 * τ^3)).trans_eq
    (by dsimp [C]; ring)

end JanetCartan.RawPrimary
