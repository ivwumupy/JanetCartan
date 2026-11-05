module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.CompletionAssembly.PrimaryProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.Displacement
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.PhaseJets

/-!
# Physical jets of the literal corrected primary atom

Freeze the original carrier parameter in the corrected displacement envelope,
then restore the same phase. Joint-to-physical restriction costs no derivative
or dimension factor. The actual phase grades and the radial frequency bound
give the physical atom estimate used by the canonical source integral.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.UniformStep

open CorrectedAtoms RawPrimary LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

/-- Apply the original corrected displacement envelope and phase grades to
the SAME physical atom (`app:ch_response:cor:current-atoms`,
`main:eq:joint-physical-profile`). `fullCorrectedDisplacementAmplitude_joint_bounds`
produces `hdisplacement`; `ResponsePrimarySources.exists_fullPhase_physical_grades`
produces `hphaseJets`. The finite radial menu supplies `hfrequency`.
Consumer: `norm_iteratedFDeriv_finalCanonicalPrimary_originalScale_le`, followed
by `exists_originalMesh_primary_profiles`. -/
theorem corrected_primary_physical_jets_of_joint_envelope
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    {τ : ℝ} (hτ : τ ≠ 0)
    (hresponse : ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) Ω)
    {O : Set (Euclidean n)} (hO : IsOpen O)
    (param : Euclidean 3 × Euclidean (n - 1))
    (hOΩ : ∀ x ∈ O, (x, param) ∈ Ω)
    (a s : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (hs : ∀ j, 0 ≤ s j)
    {lam L Cfreq : ℝ} (hlam : 1 ≤ lam) (hL : 0 ≤ L) (hLlam : L ≤ lam)
    (hCfreq : 0 ≤ Cfreq) (hfrequency : |τ⁻¹| ≤ Cfreq * lam)
    (hdisplacement : ∀ j, ∀ x ∈ O,
      ‖iteratedFDeriv ℝ j
        (fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ B r τ) (x, param)‖ ≤
          a j * L ^ j)
    (hphaseJets : ∀ j, ∀ x ∈ O,
      ‖iteratedFDeriv ℝ (j + 1) (fun y ↦ phase T Q y param.2) x‖ ≤ s j * L ^ j) :
    ContDiffOn ℝ ∞ (fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r param) O ∧
      ∀ q, ∀ x ∈ O,
        ‖iteratedFDeriv ℝ q (fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r param) x‖ ≤
          ((2 : ℝ) ^ q * RawPrimary.atomJetConstant a (fun j ↦ Cfreq * s (j - 1)) q) *
            lam ^ q := by
  have hA := contDiffOn_fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ B r
    hΩ hspace hphase hF hi hrank hα hnonzero hτ hresponse
  have hAslice : ContDiffOn ℝ ∞
      (fun x : Euclidean n ↦
        fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ B r τ (x, param)) O :=
    hA.comp (contDiffOn_id.prodMk contDiffOn_const) hOΩ
  have hphaseSlice : ContDiffOn ℝ ∞ (fun x : Euclidean n ↦ phase T Q x param.2) O :=
    (RawPrimary.contDiffOn_fullPhase T Q hphase).comp
      (contDiffOn_id.prodMk contDiffOn_const) hOΩ
  have hphysicalDisplacement : ∀ j, ∀ x ∈ O,
      ‖iteratedFDeriv ℝ j
        (fun y ↦ fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ B r τ (y, param)) x‖ ≤
          a j * L ^ j := by
    intro j x hx
    exact (AmplitudeGrades.norm_iteratedFDeriv_physical_slice_le hΩ hA (hOΩ x hx) j).trans
      (hdisplacement j x hx)
  have hscaledPhase : ∀ j : ℕ, 1 ≤ j → ∀ x ∈ O,
      ‖iteratedFDeriv ℝ j (fun y ↦ phase T Q y param.2 / τ) x‖ ≤
        (Cfreq * s (j - 1)) * lam * L ^ (j - 1) := by
    intro j hj x hx
    have hgrade : ‖iteratedFDeriv ℝ j (fun y ↦ phase T Q y param.2) x‖ ≤
        s (j - 1) * L ^ (j - 1) := by
      cases j with
      | zero => omega
      | succ i => exact hphaseJets i x hx
    have he : (fun y ↦ phase T Q y param.2 / τ) =
        τ⁻¹ • (fun y ↦ phase T Q y param.2) := by
      ext y
      simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [he, iteratedFDeriv_const_smul_apply
      ((hphaseSlice.contDiffAt (hO.mem_nhds hx)).of_le (by simp)),
      norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ (Cfreq * lam) * (s (j - 1) * L ^ (j - 1)) :=
        mul_le_mul hfrequency hgrade (norm_nonneg _)
          (mul_nonneg hCfreq (zero_le_one.trans hlam))
      _ = _ := by ring
  have hmod : Set.EqOn
      (fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r param)
      (fun x ↦ Complex.exp (Complex.I * (phase T Q x param.2 / τ : ℝ)) •
        fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ B r τ (x, param)) O := by
    intro x hx
    exact fullCorrectedPrimaryAtom_eq_modulated T Q F row col Φ Y χ B r
      hΩ hspace hphase hF hi hα hnonzero hτ (w := (x, param)) (hOΩ x hx)
  exact primary_physical_jets_of_displacement_envelope (n := n) (N := N) hO
    (fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r param)
    (fun x ↦ phase T Q x param.2 / τ)
    (fun x ↦ fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ B r τ (x, param))
    (hphaseSlice.div_const τ) hAslice hmod
    a (fun j ↦ Cfreq * s (j - 1)) ha (fun j ↦ mul_nonneg hCfreq (hs _))
    hlam hL hLlam hphysicalDisplacement hscaledPhase

end JanetCartan.UniformStep
