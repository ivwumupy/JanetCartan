module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmbientStrain.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.FullRegularity
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.LeadingAssembly

/-!
# Exact ambient cubic residual of the actual primary atom

The SAME `fullPrimaryAtom` is differentiated and reconstructed using the
actual projected stress frame. Both quadratures and every Christoffel term
are retained. The common family must satisfy the explicitly retained frame
threshold on its construction set; no ambient strain identity is an input.

Sources: `app:ch_waves:eq:exact-half-strain`, `app:ch_waves:eq:WKB-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Matrix
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open NullTransport ProjectedStressFrame ResponseTransfer

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)

/-- The literal demodulated full strain of the constructed primary atom,
with the Frobenius tensor norm (`app:ch_waves:eq:WKB-strain`). -/
def fullPrimaryStrainAmplitude (τ : ℝ)
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) :
    Matrix (Fin n) (Fin n) ℂ :=
  Complex.exp (-Complex.I * (phase T Q w.1 w.2.2 : ℂ) / (τ : ℂ)) •
    WKB.complexLinearizedMetric F
      (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (x, w.2.2)) w.1

variable {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}

/-- Exact demodulated ambient strain from the actual leading outputs and
projected-frame admission. The frame basis, geometric half-strain and all
physical differentiability are deduced. The result retains the original
`x,z,ζ`, selected row/column, factor two, and exact `τ³`
(`app:ch_waves:eq:WKB-residual`). -/
theorem fullPrimaryAtom_demodulated_strain_of_leading_outputs
    (hn : 5 ≤ n) (F : Euclidean n → Euclidean (embeddingDimension n))
    (hprojected : Q.1 = projectedStress F)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hclose : ∀ i, cNorm K 6 (fun x ↦ projectedStress F x i - cubeStress n i) <
      ambientStrainFrameThreshold hn)
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (htransport : ∀ w ∈ Ω, conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
      (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2) •
        nullvector T Q col (x, w.2)) w.1 = 0)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hw : w ∈ Ω) (hwK : w.1 ∈ K) {τ : ℝ} (hτ : τ ≠ 0) :
    fullPrimaryStrainAmplitude T Q F row col Φ Y r τ w =
      ((2 : ℂ) * (τ : ℂ)^3) • WKB.stressReconstruction (Q.1 w.1)
        (fun i ↦ complexReducedOperator F Q.1
          (fun x ↦ fullCorrectionCovector T Q F row col Φ Y r (x, w.2)) w.1 i) := by
  have hframe := projectedStress_tensorFrame_of_cNorm_closeness hn hU hK hKU
    hF hi hrank hclose hwK
  rw [← hprojected] at hframe
  let u : Euclidean n → EuclideanSpace ℂ (Fin n) :=
    twoTermWave τ⁻¹ (fun x ↦ phase T Q x w.2.2)
      (fun x ↦ euclideanComplexInclusion (fullLeadingCovector T Q F row col Φ Y r (x, w.2)))
      (fun x ↦ fullCorrectionCovector T Q F row col Φ Y r (x, w.2))
  let s : Set (Euclidean n) := {x | (x, w.2) ∈ Ω}
  have hs : IsOpen s := hΩ.preimage (continuous_id.prodMk continuous_const)
  have hsU : s ⊆ U := fun x hx ↦ hspace (x, w.2) hx
  have hujoint := contDiffOn_joint_twoTermWave τ⁻¹
    (contDiffOn_fullPhase T Q hphase)
    (euclideanComplexInclusion.contDiff.comp_contDiffOn
      (contDiffOn_fullLeadingCovector T Q F row col Φ Y r hspace hphase hα))
    (contDiffOn_fullCorrectionCovector_of_leading_outputs
      T Q F row col Φ Y r hΩ hspace hphase hF hi hα hnonzero)
  have hu : ContDiffOn ℝ ∞ u s := hujoint.comp
    (contDiffOn_id.prodMk contDiffOn_const) (fun _ hx ↦ hx)
  have hmetric := completedVariationComplex_zero_strain_eq_reconstruction hs
    (hF.mono hsU) hu (fun x hx ↦ hi x (hsU hx)) (fun x hx ↦ hrank x (hsU hx))
    hw Q.1 hframe.1 hframe.2.1 hframe.2.2
  have hred := fullTwoTermWave_reduced_residual_tau_of_leading_outputs
    T Q F row col Φ Y r hΩ hspace hphase hF hi hα hnonzero htransport hw hframe.1 hτ
  have hred' : (fun i ↦ complexReducedOperator F Q.1 u w.1 i) =
      Complex.exp (Complex.I * (phase T Q w.1 w.2.2 : ℂ) / (τ : ℂ)) •
        ((τ : ℂ)^3 • (fun i ↦ complexReducedOperator F Q.1
          (fun x ↦ fullCorrectionCovector T Q F row col Φ Y r (x, w.2)) w.1 i)) := by
    funext i
    exact congrArg (fun v : EuclideanSpace ℂ (Fin n) ↦ v i) hred
  change Complex.exp (-Complex.I * (phase T Q w.1 w.2.2 : ℂ) / (τ : ℂ)) •
    WKB.complexLinearizedMetric F (completedVariationComplex F u 0) w.1 = _
  rw [hmetric, hred', map_smul, map_smul]
  have hc : Complex.exp (-Complex.I * (phase T Q w.1 w.2.2 : ℂ) / (τ : ℂ)) *
      Complex.exp (Complex.I * (phase T Q w.1 w.2.2 : ℂ) / (τ : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 1
    congr 1
    ring
  calc
    _ = ((2 : ℂ) * (τ : ℂ)^3) •
        ((Complex.exp (-Complex.I * (phase T Q w.1 w.2.2 : ℂ) / (τ : ℂ)) *
          Complex.exp (Complex.I * (phase T Q w.1 w.2.2 : ℂ) / (τ : ℂ))) •
            WKB.stressReconstruction (Q.1 w.1)
              (fun i ↦ complexReducedOperator F Q.1
                (fun x ↦ fullCorrectionCovector T Q F row col Φ Y r (x, w.2)) w.1 i)) := by
      simp only [smul_smul]
      congr 1
      ring
    _ = _ := by rw [hc, one_smul]

end JanetCartan.RawPrimary
