module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.Background
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.CanonicalSampledAmplitude

/-!
# The actual zero atom in the sampled amplitude

The supplied corrected carrier atom is the same zero Fourier atom that
provides the canonical background. Its physical derivative realizes that
background on the original cutoff plateau. No mask is applied to the
zero atom (`app:ch_mean_pairs:defn:mean-canonical`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.CurrentMean
open CanonicalAtomRealization CorrectedAtoms RawPrimary UniformStep AmplitudeBound
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (τ : ℝ) (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (z : Euclidean 3) (ζ : Euclidean (n - 1))
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (hresponse : ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) Ω)
    {O : Set (Euclidean n)} (hcarrier : ∀ x ∈ O, (x, (z, ζ)) ∈ Ω)
    (hτ : τ ≠ 0) (hO : IsOpen O)
    (ψ : Euclidean n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hs : tsupport ψ ⊆ O)
    {b : ℝ} (hcell : b < 1 / 2) (hbox : ∀ x ∈ tsupport ψ, ∀ i, |x i| ≤ b)

/-- The original corrected unit zero atom supplies both physical smoothness
and the exact canonical background amplitude on its supplied plateau
(`app:ch_mean_pairs:defn:mean-canonical`, `app:ch_pairs:lem:pairs-ledger`).
The carrier phase, response and scalar are the same on both sides. -/
theorem correctedZeroAtom_realizes_sampledAmplitude
    {Vsource : Set (Euclidean n)}
    (hsourceBox : ∀ x ∈ Vsource, ∀ i, |x i| < 1 - b)
    (hplateau : ∀ x ∈ Vsource, ψ x = 1) :
    let base := smoothCorrectedZeroAtom T Q F row col Φ Y χ B τ r z ζ
      hΩ hspace hphase hF hi hrank hα hnonzero hresponse hcarrier hτ hO ψ hψ hs hcell hbox
    let Zc := fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r (z, ζ)
    ContDiffOn ℝ ∞ Zc Vsource ∧
      EqOn (sampledDerivativeAmplitude (fun _ : Unit ↦ Zc) (fun _ x ↦ phase T Q x ζ / τ) ())
        (periodicLift (fun x ↦ base.val x ())) Vsource := by
  have hsource : Vsource ⊆ O := by
    intro x hx
    exact hs (subset_tsupport ψ (by rw [Function.mem_support, hplateau x hx]; exact one_ne_zero))
  constructor
  · have hmap : ContDiffOn ℝ ∞ (fun x : Euclidean n ↦ (x, (z, ζ))) Vsource :=
      contDiffOn_id.prodMk contDiffOn_const
    have hw := (contDiffOn_fullCorrectedPrimaryAtom_joint T Q F row col Φ Y χ B r
      hΩ hspace hphase hF hi hrank hα hnonzero τ hresponse).comp hmap
        (fun _ hx ↦ hcarrier _ (hsource hx))
    simpa only [Function.comp_def] using hw
  · intro x hx
    have hp := preparationMatrixPeriodization_eq_of_lt
      (fun p : Euclidean n × ContinuumRow.CarrierParameter ↦ ψ p.1 •
        fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ (p.1, (z, ζ))) hcell
      (fun y _ hy ↦ hbox y (subset_tsupport ψ (by
        intro hzero
        exact hy (by simp [hzero])))) x 0 (hsourceBox x hx)
    change _ = ψ (centeredTorusRepresentative (torusQuotient x)) •
      fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ
        (centeredTorusRepresentative (torusQuotient x), (z, ζ))
    change ψ (centeredTorusRepresentative (torusQuotient x)) •
      fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ
        (centeredTorusRepresentative (torusQuotient x), (z, ζ)) = _ at hp
    rw [hp, hplateau x hx, one_smul,
      fullCorrectedDerivativeAmplitude_eq_demodulated T Q F row col Φ Y χ B r
        hΩ hspace hphase hF hi hrank hα hnonzero hτ (hcarrier x (hsource hx))
        (((hresponse.contDiffAt (hΩ.mem_nhds (hcarrier x (hsource hx)))).comp x
          (f := fun y : Euclidean n ↦ (y, (z, ζ)))
          (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))]
    have hph : wavePhase (-(phase T Q x ζ / τ)) =
        Complex.exp (-Complex.I * (phase T Q x ζ / τ : ℝ)) := by
      unfold wavePhase
      congr 1
      push_cast
      ring
    unfold sampledDerivativeAmplitude
    rw [hph]
    rfl

end JanetCartan.CurrentMean
