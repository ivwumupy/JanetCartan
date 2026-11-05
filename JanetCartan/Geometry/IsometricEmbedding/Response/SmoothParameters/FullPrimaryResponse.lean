module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SmoothParameters.TensorResponse
public import JanetCartan.Geometry.IsometricEmbedding.Response.SmoothParameters.FullPrimarySource

/-!
# Joint regularity of the full primary response

Discharge the joint-output premise of CorrectedAtoms from the SAME fixed
response's all-order tame bounds (`app:ch_response:cor:current-atoms`). The
source is the literal complete cutoff strain of the retained raw atom. The
parameter chart is the projection of the consumer's original open chart; no
source cutoff, reference, row, phase, or response is changed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.ResponseSmoothParameters
open RetardedSobolev.Spaces CorrectedAtoms ResponseSourceExtension PrimarySourceAdmission
open RawPrimary LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

variable {d n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)

/-- Joint smoothness of the SAME full primary response on the exact open chart
used by `CorrectedAtoms.cNorm_fullCorrectedDensityError_sub_le`. The source's
joint regularity and admission are proved from the retained geometry. Only
the actual fixed inverse's spatial smoothness and finite-order tame bounds
remain producer inputs (`app:ch_response:thm:response-literal-transfer`). -/
theorem contDiffOn_fullPrimaryResponse_of_tame
    {Ω O : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
    {L : Set (Euclidean n)} (hL : IsCompact L)
    (hO : IsOpen O) (hout : ∀ w ∈ O, w.1 ∈ interior L)
    (hsrc : ∀ w ∈ O, ∀ x ∈ tsupport χ, (x, w.2) ∈ Ω)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (hBreg : ∀ h : compactSmoothSources (tsupport χ), ContDiff ℝ ∞ (B h))
    (hB : ∀ i j : Fin n, ∀ q : ℕ, ∃ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : supportedTests (e ⁻¹' tsupport χ), ∀ x ∈ L,
        ‖iteratedFDeriv ℝ q (tensorComponentResponse e (tsupport χ) B i j u) x‖ ≤
          C * ‖ofTest s volume u.val‖) (τ : ℝ) :
    ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) O := by
  let V : Set (Euclidean 3 × Euclidean (n - 1)) := Prod.snd '' O
  have hV : IsOpen V := isOpenMap_snd _ hO
  have hsrc' : ∀ c ∈ V, ∀ x ∈ tsupport χ, (x, c) ∈ Ω := by
    rintro c ⟨w, hw, rfl⟩ x hx
    exact hsrc w hw x hx
  let f := fun c : Euclidean 3 × Euclidean (n - 1) ↦ complexAtomicSource F χ
    (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ r c.1 (x, c.2))
  have hf : ContDiffOn ℝ ∞ (fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
      f w.2 w.1) (univ ×ˢ V) :=
    contDiffOn_fullPrimaryAtom_source T Q F row col Φ Y r hΩ hspace hphase
      hF hi hrank hα hnonzero χ hχ hV hsrc' τ
  have hs : ∀ c ∈ V, tsupport (f c) ⊆ tsupport χ :=
    fun c _ ↦ tsupport_smul_subset_left χ _
  have hh := contDiffOn_tensorResponse e
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 3) (m := n - 1))
    hc hL isOpen_interior interior_subset hV B hBreg hB f hf hs
  exact hh.mono (fun w hw ↦ ⟨hout w hw, ⟨w, hw, rfl⟩⟩)

/-- The consumer's demodulated physical response derivative is jointly smooth
from the actual fixed response bounds, without a joint-output premise
(`app:ch_response:eq:current-atomic-amplitudes`). The phase and response are
the same ones occurring in the literal density error. -/
theorem contDiffOn_fullPrimaryResponseDerivativeAmplitude_of_tame
    {Ω O : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
    {L : Set (Euclidean n)} (hL : IsCompact L)
    (hO : IsOpen O) (hOΩ : O ⊆ Ω) (hout : ∀ w ∈ O, w.1 ∈ interior L)
    (hsrc : ∀ w ∈ O, ∀ x ∈ tsupport χ, (x, w.2) ∈ Ω)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (hBreg : ∀ h : compactSmoothSources (tsupport χ), ContDiff ℝ ∞ (B h))
    (hB : ∀ i j : Fin n, ∀ q : ℕ, ∃ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : supportedTests (e ⁻¹' tsupport χ), ∀ x ∈ L,
        ‖iteratedFDeriv ℝ q (tensorComponentResponse e (tsupport χ) B i j u) x‖ ≤
          C * ‖ofTest s volume u.val‖) (τ : ℝ) :
    ContDiffOn ℝ ∞ (fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B r τ) O :=
  CorrectedAtoms.contDiffOn_fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y r
    hO (fun w hw ↦ hphase w (hOΩ hw)) χ B τ
    (contDiffOn_fullPrimaryResponse_of_tame T Q F row col Φ Y r hΩ hspace hphase hF hi
      hrank hα hnonzero χ hχ hc e hL hO hout hsrc B hBreg hB τ)

end JanetCartan.ResponseSmoothParameters
