module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.ActualDensity
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.ActualReconstruction
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.LocalConstruction
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.TameBounds

/-!
# Actual positive local amplitudes with joint tame estimates

This instantiates the amplitude estimate with the literal projected-frame
coefficient and flow outputs. All constants, the minor and the working cylinder
precede the immersion and prescribed initial datum. The phase and null column
remain those of the same `PatchQuantitativeFamily`.

This closes the local positive-transport and amplitude part of
`app:ch_waves:thm:leading` and `app:ch_waves:eq:joint-tame`. The full leading
construction also needs the principal-normal gap, reconstruction estimates,
full modulation parameters and finite common-domain assembly.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace JanetCartan.LeadingWave
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame NullTransport
open ActualFlow FlowAmplitude AmbientResponse ResponseTransfer

/-- Actual local positive null amplitude, including its joint reserve-thirteen
estimate. Only primitive immersion/normal gaps, projected-frame closeness,
fixed C12 immersion and C5 initial-data budgets are inputs. Every coefficient,
flow and amplitude hypothesis of the analytic deduction is discharged using
the same actual constructor (`app:ch_waves:thm:leading`). -/
theorem exists_actual_local_leading_wave {n N : ℕ} (hn : 2 ≤ n)
    {P : Patch n} {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    {M₁₂ Mᵣ κmet κnormal m₀ : ℝ} (hM₁₂ : 0 ≤ M₁₂) (hMᵣ : 0 ≤ Mᵣ)
    (hκmet : 0 < κmet) (hκnormal : 0 < κnormal) (hm₀ : 0 < m₀)
    (z : Euclidean 3) (hz : z ∈ parameterCube P.radius) :
    ∃ row col : Fin n, ∃ R η τ a g : ℝ, ∃ B : ℕ → ℝ,
      0 < R ∧ 0 < η ∧ 0 < τ ∧ 0 < a ∧ 0 < g ∧ (∀ j, 0 < B j) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 12 F ≤ M₁₂ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < η →
        ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
        let p₀ := ((0 : Euclidean (n - 1)), z)
        ∃ D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
        ∃ Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
          IsOpen D ∧
          Ioo (-τ) τ ×ˢ ball p₀ (R / 32) ⊆ D ∧
          D ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 4) ∧
          C ⁻¹' D ⊆ (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
            parameterInterior (3 * P.radius / 2) ∧
          (∀ w ∈ C ⁻¹' D,
            carrierNullvector T Q col w ≠ 0 ∧ carrierConullvector T Q row w ≠ 0 ∧
            carrierConullvector T Q row w ᵥ*
              reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) = 0 ∧
            carrierAdaptedDenominator T Q row col w ≠ 0 ∧
            g ≤ |carrierAdaptedDenominator T Q row col w|) ∧
          ∀ (r : Euclidean (n - 1) × Euclidean 3 → ℝ),
            ContDiffOn ℝ ∞ r (ball p₀ (R / 4)) →
            cNorm (closedBall p₀ (R / 8)) 5 r ≤ Mᵣ →
            (∀ p ∈ ball p₀ (R / 8), m₀ ≤ r p) →
            let α := carrierScalarAmplitude T Q F row col Φ Y r
            let b := fun w ↦ α w • carrierNullvector T Q col w
            ContDiffOn ℝ ∞ α (C ⁻¹' D) ∧ ContDiffOn ℝ ∞ b (C ⁻¹' D) ∧
              (∀ p ∈ ball p₀ (R / 8), α (T.data.adapted.embedding p.1, p.2) = r p) ∧
              (∀ w ∈ C ⁻¹' D, a ≤ α w) ∧
              (∀ w ∈ C ⁻¹' D, b w ≠ 0) ∧
              (∀ w ∈ C ⁻¹' D,
                fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (carrierTransportDirection T Q row col w) +
                  carrierTransportPotential T Q F row col w * α w = 0) ∧
              (∀ w ∈ C ⁻¹' D,
                reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
                  (fun j ↦ b w j) = 0) ∧
              (∀ w ∈ C ⁻¹' D, carrierConullvector T Q row w ⬝ᵥ reducedOperator F Q.1
                (fun x ↦ b (x, w.2)) w.1 = 0) ∧
              (∀ j,
                cNorm (C.symm '' (Icc (-τ / 2) (τ / 2) ×ˢ closedBall p₀ (R / 64))) j α +
                  cNorm (C.symm '' (Icc (-τ / 2) (τ / 2) ×ˢ closedBall p₀ (R / 64))) j b ≤
                  B j * (1 + cNorm K (j + 13) F +
                    cNorm (closedBall p₀ (R / 8)) (j + 13) r)) ∧
              (∀ w ∈ C ⁻¹' D,
                determinant (Q.1 w.1) (T.carrierGradient Q w.1 w.2) = 0 ∧
                (1 / 2 : ℝ) • linearizedMetric F
                    (reconstruction F (canonicalNormalCompletion F) (fun x ↦ b (x, w.2))) w.1 =
                  stressProjection F w.1 (symmCovariantDeriv F (fun x ↦ b (x, w.2)) w.1) ∧
                (∀ τ' : ℝ, τ' ≠ 0 →
                  completedVariationComplex F
                    (fun x ↦ (τ' : ℂ) ^ 2 •
                      Complex.exp (Complex.I * (T.carrier Q x w.2 : ℂ) / (τ' : ℂ)) •
                        euclideanComplexInclusion (b (x, w.2))) 0 w.1 =
                    Complex.exp (Complex.I * (T.carrier Q w.1 w.2 : ℂ) / (τ' : ℂ)) •
                      ((Complex.I * (τ' : ℂ)) • euclideanComplexInclusion
                        (principalNormal (canonicalNormalCompletion F w.1)
                          (T.carrierGradient Q w.1 w.2) (b w)) +
                      (τ' : ℂ) ^ 2 • euclideanComplexInclusion
                        (reconstruction F (canonicalNormalCompletion F) (fun x ↦ b (x, w.2)) w.1))) ∧
                hermitianTensor ((principalMatrix
                    (principalNormal (canonicalNormalCompletion F w.1)
                      (T.carrierGradient Q w.1 w.2) (b w))
                    (T.carrierGradient Q w.1 w.2)).map Complex.ofReal) =
                  fun i j ↦ ‖principalNormal (canonicalNormalCompletion F w.1)
                    (T.carrierGradient Q w.1 w.2) (b w)‖ ^ 2 *
                      T.carrierGradient Q w.1 w.2 i * T.carrierGradient Q w.1 w.2 j) := by
  classical
  obtain ⟨row, col, ρ, R, η, τ, g, A, H, hρ, hR, hη, hτ, hg, hA, hH, hbuffer₀, hτR₀, hactual⟩ :=
    exists_projected_local_positive_amplitude hn hP T hK hKU hball M₁₂ hκmet hκnormal z hz
  let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  let a := m₀ * Real.exp (-(A 0 * (1 + M₁₂)) * τ)
  have ha : 0 < a := mul_pos hm₀ (Real.exp_pos _)
  obtain ⟨B, hB, htame⟩ := exists_carrierScalarAmplitude_joint_tame (N := N)
    T K z hρ hR hτ hτR₀ hbuffer₀ A H hA hH hM₁₂ hMᵣ
  refine ⟨row, col, R, η, τ, a, g, B, hR, hη, hτ, ha, hg, hB, ?_⟩
  intro F hF hi hrank hFlow hmet hnormal hclose
  have hFfour : cNorm K 4 F ≤ M₁₂ := (cNorm_mono_order (by omega)).trans hFlow
  have hFfive : cNorm K 5 F ≤ M₁₂ := (cNorm_mono_order (by omega)).trans hFlow
  obtain ⟨hlow, D, Φ, Y, hD, hsmall, hbig, hphys, _hΦ, _hY, hΦD, hYU,
    _hΦ₀, _hYΦ, _hΦY, _hcarrier, _hYcarrier, _hvelocity, hnull, hcoeff, hflow,
    hreg, hΦbuffer, hYbuffer, _hbuffer, _hτR, hgap, hsol⟩ :=
    hactual F hF hi hrank hFfour hmet hnormal hclose
  refine ⟨hlow, D, Φ, Y, hD, hsmall, hbig, hphys,
    (fun w hw ↦ ⟨(hnull w hw).1, (hnull w hw).2.1, (hnull w hw).2.2.1,
      (hnull w hw).2.2.2, (hgap w hw).1⟩), ?_⟩
  intro r hr hrLow hrmin
  have hrsmall := hr.mono (ball_subset_ball (by linarith : R / 8 ≤ R / 4))
  obtain ⟨hα, hb, hinit, hpos, _hcompact, hpde, hsymbol, hreduce, hlower⟩ :=
    hsol r hrsmall (fun p hp ↦ hm₀.trans_le (hrmin p hp))
  refine ⟨hα, hb, hinit, hlower m₀ M₁₂ hm₀.le hFfive hrmin, ?_, hpde, hsymbol,
    hreduce, ?_, ?_⟩
  · intro w hw
    exact smul_ne_zero (ne_of_gt (hpos w hw)) (hnull w hw).1
  · exact htame _ F row col D Φ Y r hsmall hbig hΦD hYU
      hΦbuffer hYbuffer hreg hcoeff hflow hr hFlow hrLow
  · have hΩ : IsOpen (C ⁻¹' D) := hD.preimage C.continuous
    have hΩU : C ⁻¹' D ⊆ U ×ˢ univ :=
      fun _ hw ↦ ⟨hKU (interior_subset (hphys hw).1.2), mem_univ _⟩
    have hΩphase : C ⁻¹' D ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
        parameterInterior (2 * P.radius) := by
      intro w hw
      exact ⟨(hphys hw).1.1, fun i ↦ ((hphys hw).2 i).trans_le (by linarith [hP.1])⟩
    have hident := actual_carrier_reconstruction_identities hP T hF hi hrank hlow
      hΩ hΩU hΩphase hb
    intro w hw
    exact ⟨(hident w hw).1, (hident w hw).2.1, (hident w hw).2.2,
      principalNormal_hermitianTensor F w.1 _ _⟩

end JanetCartan.LeadingWave
