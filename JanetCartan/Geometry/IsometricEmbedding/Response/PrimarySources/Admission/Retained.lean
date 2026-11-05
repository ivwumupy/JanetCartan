module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Admission.Strain
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmbientStrain.Exact

/-!
# Source admission on the retained primary chart

Use the SAME `T,Q,F,row,col,Φ,Y,r`, free covector and cutoff. The local smoothness input
`hatom` below is an output of
`RawPrimary.exists_finite_retained_raw_primary_family`; the finite-family
assembly must instantiate them. No response estimate is assumed here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Metric MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PrimarySourceAdmission
open RawPrimary LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ResponseSourceExtension

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}

/-- Admission of both actual primary strain quadratures on the entire original
source support (`app:ch_response:cor:current-atoms`). Local atom smoothness is the output
of the same retained raw constructor; no global smoothness is assumed. -/
theorem fullPrimaryAtom_source_mem
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hF : ContDiffOn ℝ ∞ F U) (τ : ℝ)
    (hatom : ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (w.1, w.2.2)) Ω)
    (z : Euclidean 3) (ξ : Euclidean (n - 1))
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : ∀ x ∈ tsupport χ, (x, (z, ξ)) ∈ Ω) :
    tensorFieldRealPart (fun x ↦ χ x • WKB.complexLinearizedMetric F
      (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r z (y, ξ)) x) ∈
        compactSmoothSources (tsupport χ) ∧
    tensorFieldImagPart (fun x ↦ χ x • WKB.complexLinearizedMetric F
      (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r z (y, ξ)) x) ∈
        compactSmoothSources (tsupport χ) := by
  let O : Set (Euclidean n) := {x | (x, (z, ξ)) ∈ Ω}
  have ho : IsOpen O := hΩ.preimage (continuous_id.prodMk continuous_const)
  have hOU : O ⊆ U := fun x hx ↦ hspace (x, (z, ξ)) hx
  apply cutoff_strain_quadratures_mem (F := F)
    (W := fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r z (y, ξ))
    (O := O) hχ hc ho (hF.mono hOU) ?_ hs
  exact hatom.comp (f := fun x : Euclidean n ↦ (x, (z, ξ)))
    (contDiffOn_id.prodMk contDiffOn_const) (fun _ hx ↦ hx)

/-- The original closed working ball supplies the source buffer for every
fixed cutoff and retained carrier label. No smaller source support is substituted
(`app:ch_response:thm:response-compatible-choice`). -/
theorem source_support_in_retained_chart
    {center : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} {σ : ℝ}
    (hσ : 0 < σ) (hbuffer : closedBall center (2 * σ) ⊆ Ω)
    {χ : Euclidean n → ℝ} {z : Euclidean 3} {ξ : Euclidean (n - 1)}
    (hs : ∀ x ∈ tsupport χ, (x, (z, ξ)) ∈ closedBall center σ) :
    ∀ x ∈ tsupport χ, (x, (z, ξ)) ∈ Ω :=
  fun x hx ↦ hbuffer ((closedBall_subset_closedBall (by linarith : σ ≤ 2 * σ)) (hs x hx))

/-- The complete source can be remodulated from the literal strain amplitude;
this identity includes all orthogonal-correction and Christoffel terms
(`app:ch_waves:eq:WKB-residual`). -/
theorem fullPrimaryAtom_source_eq_remodulated (τ : ℝ) (z : Euclidean 3)
    (ξ : Euclidean (n - 1)) (χ : Euclidean n → ℝ) :
    (fun x ↦ χ x • WKB.complexLinearizedMetric F
      (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r z (y, ξ)) x) =
    (fun x ↦ χ x • (Complex.exp (Complex.I * (phase T Q x ξ : ℂ) / (τ : ℂ)) •
      fullPrimaryStrainAmplitude T Q F row col Φ Y r τ (x, (z, ξ)))) := by
  funext x
  simp only [fullPrimaryStrainAmplitude, smul_smul, ← Complex.exp_add]
  have he : Complex.I * (phase T Q x ξ : ℂ) / (τ : ℂ) +
      -Complex.I * (phase T Q x ξ : ℂ) / (τ : ℂ) = 0 := by ring
  rw [he, Complex.exp_zero, one_smul]

end JanetCartan.PrimarySourceAdmission
