module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.SmoothMap

/-!
# The unmasked zero-atom background

The background in `app:ch_mean_pairs:defn:mean-canonical` evaluates the SAME
corrected amplitude at the original carrier. It has no annular half weight,
detector mask, high-pass mask, or band ceiling. The physical extension uses
the supplied slice cutoff, just as the canonical derivative does.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CanonicalAtomRealization

open RawPrimary CorrectedAtoms CurrentMean AmplitudeBound
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

include hΩ hspace hphase hF hi hrank hα hnonzero hresponse hcarrier hτ hO hψ hs hcell hbox

/-- The separate zero Fourier atom is smooth on the same periodic extension.
Its regularity is obtained from the actual corrected amplitude
(`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem isSmoothPeriodic_cutCorrectedZeroAtom :
    IsSmoothPeriodic (fun x ↦ ψ (centeredTorusRepresentative x) •
      fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ
        (centeredTorusRepresentative x, (z, ζ))) := by
  have ha := contDiffOn_fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r
    hΩ hspace hphase hF hi hrank hα hnonzero hτ hresponse
  have hA : ContDiffOn ℝ ∞
      (fun x ↦ fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ (x, (z, ζ))) O :=
    ha.comp (contDiffOn_id.prodMk contDiffOn_const) hcarrier
  have hh := preparationMatrixExtension_regular ψ hψ hO hs hcell hbox
    (fun p ↦ fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ (p.1, (z, ζ)))
    (hA.comp contDiffOn_fst (fun _ hp ↦ hp.1))
  exact ⟨hh.1.comp (continuous_id.prodMk (continuous_const (y := 0))),
    hh.2.comp (contDiff_id.prodMk (contDiff_const (c := 0)))⟩

/-- The concrete background used alongside the constructed `G`, retaining
the zero atom independently of all varying raw bands and masks
(`app:ch_mean_pairs:defn:mean-canonical`). -/
def smoothCorrectedZeroAtom : SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ) :=
  ⟨fun x _ ↦ ψ (centeredTorusRepresentative x) •
    fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ
      (centeredTorusRepresentative x, (z, ζ)),
    fun _ ↦ isSmoothPeriodic_cutCorrectedZeroAtom T Q F row col Φ Y χ B τ r z ζ
      hΩ hspace hphase hF hi hrank hα hnonzero hresponse hcarrier hτ hO ψ hψ hs hcell hbox⟩

/-- The background is the original zero-atom integral, with unit Dirac mass
and no Fourier-input mask (`app:ch_waves:eq:individual-representation`). -/
theorem smoothCorrectedZeroAtom_eq_dirac (x : Torus n) :
    (smoothCorrectedZeroAtom T Q F row col Φ Y χ B τ r z ζ
      hΩ hspace hphase hF hi hrank hα hnonzero hresponse hcarrier hτ hO ψ hψ hs hcell hbox).val x () =
      ψ (centeredTorusRepresentative x) •
        rawPrimaryDemodulatedIntegral (fun y η ↦ phase T Q y η)
          (fun y η ↦ fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ (y, (z, η)))
          ζ τ (Measure.dirac 0) (fun _ ↦ 1) (centeredTorusRepresentative x) := by
  rw [rawPrimaryDemodulatedIntegral_zero_atom, one_smul]
  rfl

/-- On the measurement plateau, this is exactly the demodulated derivative
of the SAME corrected atom at the carrier. This identifies the background
used in `main:eq:canonical-identity` without selecting another field. -/
theorem smoothCorrectedZeroAtom_eq_derivative (x : Torus n)
    (hx : ψ (centeredTorusRepresentative x) = 1) :
    (smoothCorrectedZeroAtom T Q F row col Φ Y χ B τ r z ζ
      hΩ hspace hphase hF hi hrank hα hnonzero hresponse hcarrier hτ hO ψ hψ hs hcell hbox).val x () =
      Complex.exp (-Complex.I * (phase T Q (centeredTorusRepresentative x) ζ / τ : ℝ)) •
        (fun i j ↦ partialDeriv (fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r (z, ζ))
          (centeredTorusRepresentative x) j i) := by
  have hxO := hs (subset_tsupport ψ (by rw [Function.mem_support, hx]; exact one_ne_zero))
  change ψ _ • fullCorrectedDerivativeAmplitude _ _ _ _ _ _ _ _ _ _ _ _ = _
  rw [hx, one_smul]
  apply fullCorrectedDerivativeAmplitude_eq_demodulated T Q F row col Φ Y χ B r
    hΩ hspace hphase hF hi hrank hα hnonzero hτ (hcarrier _ hxO)
  exact ((hresponse.contDiffAt (hΩ.mem_nhds (hcarrier _ hxO))).comp _
    (f := fun y : Euclidean n ↦ (y, (z, ζ)))
    (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)

/-- The existing measured cross-response constructor uses precisely the
uncut zero atom and the constructed raw integral on the measurement
plateau. This supplies the literal component fields to
`CanonicalChange.smoothCanonicalResponse_eq_measured_cross`
(`main:eq:canonical-identity`). -/
theorem smoothRawCrossResponse_corrected_eq_integral
    {J : ℕ} {V : Set (Euclidean (n - 1))} (hV : IsOpen V)
    (hshift : ∀ p ∈ O ×ˢ V, (p.1, (z, ζ + τ • p.2)) ∈ Ω)
    (hceil : Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (v : RawInputPartition.WideInput n J) (x : Torus n)
    (hx : ψ (centeredTorusRepresentative x) = 1) :
    (CanonicalChange.smoothRawCrossResponse
      (smoothCorrectedZeroAtom T Q F row col Φ Y χ B τ r z ζ
        hΩ hspace hphase hF hi hrank hα hnonzero hresponse hcarrier hτ hO ψ hψ hs hcell hbox)
      C hC (fun _ : Unit ↦ smoothCorrectedWideDerivative T Q F row col Φ Y χ B τ r z ζ
        hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hO hV hceil
        hd hM hb ψ hψ hs hcell hbox) () v).val x () =
      C x ((2 : ℝ) • mixedHermitianTensor
        (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ
          (centeredTorusRepresentative x, (z, ζ)))
        (rawPrimaryDemodulatedIntegral (fun y η ↦ phase T Q y η)
          (fun y η ↦ fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ (y, (z, η)))
          ζ τ volume (RawInputPartition.weightedWideDensity d v) (centeredTorusRepresentative x))) := by
  rw [CanonicalChange.smoothRawCrossResponse_apply,
    smoothCorrectedWideDerivative_eq_integral T Q F row col Φ Y χ B τ r z ζ
      hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hO hV hceil
      hd hM hb ψ hψ hs hcell hbox v x hx]
  change C x ((2 : ℝ) • mixedHermitianTensor (ψ _ • _) _) = _
  rw [hx, one_smul]

end JanetCartan.CanonicalAtomRealization
