module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.InitializedRealization.ClassicalCoordinates
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.Displacement

/-!
# The primary amplitude norms from its literal coordinate bounds

The consumer is `fullPrimaryResponse_fixedSolver_joint_graded`. Keep the
linear response as a parameter while converting its already reconstructed
coordinate jets to the original amplitude norms. The caller applies the
actual same-solver reconstruction before invoking this finite-dimensional
deduction; no new response or source is selected.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.CanonicalAtomRealization

open CorrectedAtoms RawPrimary LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1))) →
      Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1)))
    (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (scalar : Euclidean (n-1) × Euclidean 3 → ℝ) (τ : ℝ)
    (φ : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → ℝ)

/-- Transfer the reconstructed coordinates to the existing primary
amplitudes on the original phase, preserving the truncated derivative
reserve. This is the finite-dimensional last step in
`app:ch_response:eq:current-atomic-amplitudes`; its concrete caller supplies
both coordinate bounds from the actual normalized inverse. -/
theorem fullPrimaryResponse_amplitudes_of_coordinate_profiles
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n-1)))}
    (hΩ : IsOpen Ω)
    (hphase : ∀ p ∈ Ω, (p.1,p.2.2) ∈ phaseDomain T)
    (hφobs : ∀ p ∈ Ω, φ p = phase T Q p.1 p.2.2)
    (hresponse : ContDiffOn ℝ ∞
      (fun p ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ scalar p.2 p.1) Ω)
    (D E : ℕ → ℝ) (hD : ∀ r, 0 ≤ D r) (hE : ∀ r, 0 ≤ E r)
    {size K : ℝ} (hsize : 0 ≤ size) (hτ : 0 < τ) (hK : 1 ≤ K)
    (reserve m : ℕ)
    (hdisp : ∀ l r, r ≤ m+1 → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p ↦
        (waveCarrier (-τ⁻¹) (fun x ↦ φ (x,p.2)) p.1 •
          fullPrimaryResponse T Q F row col Φ Y χ B τ scalar p.2 p.1) l) q‖ ≤
        D r * (τ^2*size) * K^(r-reserve))
    (hderiv : ∀ l i r, r ≤ m → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p ↦
        (waveCarrier (-τ⁻¹) (fun x ↦ φ (x,p.2)) p.1 •
          fderiv ℝ (fullPrimaryResponse T Q F row col Φ Y χ B τ scalar p.2)
            p.1 (EuclideanSpace.single i 1)) l) q‖ ≤
        E r * (τ*size) * K^(r-reserve)) :
    ContDiffOn ℝ ∞ (fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B scalar τ) Ω ∧
      ∀ J : Set (Euclidean n × (Euclidean 3 × Euclidean (n-1))), J ⊆ Ω →
        (∀ r ≤ m+1, cNorm J r
          (fullPrimaryResponseDisplacementAmplitude T Q F row col Φ Y χ B scalar τ) ≤
            ((N : ℝ) * ∑ j ∈ Finset.range (r+1), D j) * (τ^2*size) * K^(r-reserve)) ∧
        (∀ r ≤ m, ∀ p ∈ J, ‖iteratedFDeriv ℝ r
          (fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B scalar τ) p‖ ≤
            (N*n : ℕ) * E r * (τ*size) * K^(r-reserve)) ∧
        (∀ r ≤ m, cNorm J r
          (fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B scalar τ) ≤
            ((N*n : ℕ) * ∑ j ∈ Finset.range (r+1), E j) * (τ*size) * K^(r-reserve)) := by
  have hdispsmooth : ContDiffOn ℝ ∞
      (fullPrimaryResponseDisplacementAmplitude T Q F row col Φ Y χ B scalar τ) Ω :=
    contDiffOn_fullPrimaryResponseDisplacementAmplitude T Q F row col Φ Y
      χ B scalar hphase τ hresponse
  have hderivsmooth : ContDiffOn ℝ ∞
      (fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B scalar τ) Ω :=
    contDiffOn_fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y
      scalar hΩ hphase χ B τ hresponse
  have hcarrier p (hp : p ∈ Ω) :
      Complex.exp (-Complex.I * (phase T Q p.1 p.2.2 / τ : ℝ)) =
        waveCarrier (-τ⁻¹) (fun x ↦ φ (x,p.2)) p.1 := by
    rw [← hφobs p hp]
    unfold waveCarrier
    congr 1
    simp only [div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  have hdispB l r (hr : r ≤ m+1) p (hp : p ∈ Ω) :
      ‖iteratedFDeriv ℝ r (fun q ↦
        fullPrimaryResponseDisplacementAmplitude T Q F row col Φ Y χ B scalar τ q l) p‖ ≤
        D r * (τ^2*size) * K^(r-reserve) := by
    have he : (fun q ↦ fullPrimaryResponseDisplacementAmplitude
        T Q F row col Φ Y χ B scalar τ q l) =ᶠ[𝓝 p]
        (fun q ↦ (waveCarrier (-τ⁻¹) (fun x ↦ φ (x,q.2)) q.1 •
          fullPrimaryResponse T Q F row col Φ Y χ B τ scalar q.2 q.1) l) := by
      filter_upwards [hΩ.mem_nhds hp] with q hq
      simp only [fullPrimaryResponseDisplacementAmplitude, hcarrier q hq]
    rw [(he.iteratedFDeriv ℝ r).eq_of_nhds]
    exact hdisp l r hr p hp
  have hderivB l i r (hr : r ≤ m) p (hp : p ∈ Ω) :
      ‖iteratedFDeriv ℝ r (fun q ↦
        fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B scalar τ q l i) p‖ ≤
        E r * (τ*size) * K^(r-reserve) := by
    have he : (fun q ↦ fullPrimaryResponseDerivativeAmplitude
        T Q F row col Φ Y χ B scalar τ q l i) =ᶠ[𝓝 p]
        (fun q ↦ (waveCarrier (-τ⁻¹) (fun x ↦ φ (x,q.2)) q.1 •
          fderiv ℝ (fullPrimaryResponse T Q F row col Φ Y χ B τ scalar q.2)
            q.1 (EuclideanSpace.single i 1)) l) := by
      filter_upwards [hΩ.mem_nhds hp] with q hq
      simp only [fullPrimaryResponseDerivativeAmplitude, hcarrier q hq,
        Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, partialDeriv]
    rw [(he.iteratedFDeriv ℝ r).eq_of_nhds]
    exact hderiv l i r hr p hp
  refine ⟨hderivsmooth,?_⟩
  intro J hJ
  refine ⟨?_,?_,?_⟩
  · intro r hr
    exact (fullParameterVector_cNorm_le_coordinate_profile hΩ hdispsmooth D hD
      (mul_nonneg (pow_nonneg hτ.le _) hsize) hK reserve r
      (fun l j hj ↦ hdispB l j (hj.trans hr)) hJ).2
  · intro r hr p hp
    exact (fullParameterMatrix_cNorm_le_coordinate_profile hΩ hderivsmooth E hE
      (mul_nonneg hτ.le hsize) hK reserve r
      (fun l i j hj ↦ hderivB l i j (hj.trans hr)) hJ).1 r le_rfl p hp
  · intro r hr
    exact (fullParameterMatrix_cNorm_le_coordinate_profile hΩ hderivsmooth E hE
      (mul_nonneg hτ.le hsize) hK reserve r
      (fun l i j hj ↦ hderivB l i j (hj.trans hr)) hJ).2

end JanetCartan.CanonicalAtomRealization
