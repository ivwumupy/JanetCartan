module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.FullRegularity

/-!
# The full-modulation raw integral on its original wide input

Apply the actual phase, scalar and correction regularity to the literal
Lebesgue superposition. This closes the atomic smoothness, displacement
smoothness and derivative-interchange inputs in
`app:ch_waves:eq:individual-representation`. The original masks, complex
quadratures and Hilbert norm are retained. The common family constructor
supplies the scalar/nullvector outputs and the shifted chart containment;
the quantitative coefficient and slice bounds remain separate obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase RawInputPartition

variable {n N J : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (τ : ℝ) (z : Euclidean 3)
    {X : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    (hshift : ∀ p ∈ X ×ˢ V, (p.1, (z, T.reference.spatialPatch z + τ • p.2)) ∈ Ω)

include hΩ hspace hphase hF hi hrank hα hnonzero hshift

/-- Actual joint regularity on the shifted chart, used by the raw integral.
The carrier and correction remain the original formulas
(`app:ch_waves:eq:individual-representation`). -/
theorem contDiffOn_shiftedFullPrimaryAtom :
    ContDiffOn ℝ ∞ (fun p ↦ fullPrimaryAtom T Q F row col Φ Y τ r z
      (p.1, T.reference.spatialPatch z + τ • p.2)) (X ×ˢ V) := by
  have hmap : ContDiffOn ℝ ∞
      (fun p : Euclidean n × Euclidean (n - 1) ↦
        (p.1, (z, T.reference.spatialPatch z + τ • p.2))) (X ×ˢ V) :=
    contDiffOn_fst.prodMk (contDiffOn_const.prodMk
      (contDiffOn_const.add (contDiffOn_snd.const_smul τ)))
  have ht := (contDiffOn_fullPrimaryAtom_of_leading_outputs T Q F row col Φ Y r τ
    hΩ hspace hphase hF hi hrank hα hnonzero).comp hmap hshift
  exact ht

variable (hX : IsOpen X) (hV : IsOpen V)
    (hVceil : Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)

include hX hV hVceil hd hM hb

/-- Every original wide-band Hilbert input gives the SAME smooth full raw
field, with no regularity requirement on the datum
(`app:ch_waves:thm:individual`). -/
theorem contDiffOn_fullPrimaryWave (v : WideInput n J) :
    ContDiffOn ℝ ∞ (fullPrimaryWave T Q F row col Φ Y τ r z d v) X :=
  contDiffOn_wideSuperposition hX hV hVceil
    (contDiffOn_shiftedFullPrimaryAtom T Q F row col Φ Y r
      hΩ hspace hphase hF hi hrank hα hnonzero τ z hshift) hd hM hb v

omit hX hV in
/-- The literal full raw integral is additive on the original Hilbert
input; integrability is proved from the actual atoms
(`app:ch_waves:eq:WKB-W`). -/
theorem fullPrimaryWave_add (v v' : WideInput n J) {x : Euclidean n} (hx : x ∈ X) :
    fullPrimaryWave T Q F row col Φ Y τ r z d (v + v') x =
      fullPrimaryWave T Q F row col Φ Y τ r z d v x +
        fullPrimaryWave T Q F row col Φ Y τ r z d v' x :=
  wideSuperposition_add hVceil
    (contDiffOn_shiftedFullPrimaryAtom T Q F row col Φ Y r
      hΩ hspace hphase hF hi hrank hα hnonzero τ z hshift).continuousOn hd hM hb v v' hx

omit hΩ hspace hphase hF hi hrank hα hnonzero hshift hX hV hVceil hM in
/-- Complex scaling of the actual raw integral preserves both quadratures
(`app:ch_waves:eq:WKB-W`). -/
theorem fullPrimaryWave_smul (c : ℂ) (v : WideInput n J) (x : Euclidean n) :
    fullPrimaryWave T Q F row col Φ Y τ r z d (c • v) x =
      c • fullPrimaryWave T Q F row col Φ Y τ r z d v x :=
  wideSuperposition_smul _ hd hb c v x

/-- The exact demodulated derivative of the SAME full raw wave. All local
analytic inputs of `canonicalWideWave_derivative_representation` are
discharged from the actual phase and retained leading outputs; the Lebesgue
density, masks and both quadratures are unchanged
(`app:ch_waves:eq:individual-representation`). -/
theorem fullPrimaryWave_derivative_representation (hτ : τ ≠ 0)
    (v : WideInput n J) {x : Euclidean n} (hx : x ∈ X) (e : Euclidean n) :
    Complex.exp (-Complex.I * (T.carrier Q x z / τ : ℝ)) •
        fderiv ℝ (fullPrimaryWave T Q F row col Φ Y τ r z d v) x e =
      rawPrimaryDemodulatedIntegral (fun y ξ ↦ phase T Q y ξ)
        (fun y ξ ↦ waveFirstAmplitude τ⁻¹ (fun t ↦ phase T Q t ξ)
          (fun t ↦ fullDisplacementAmplitude T Q F row col Φ Y r τ (t, (z, ξ))) y e)
        (T.reference.spatialPatch z) τ volume (weightedWideDensity d v) x := by
  have hs := contDiffOn_fullPhase T Q hphase
  have ha := (euclideanComplexInclusion (ι := Fin n)).contDiff.comp_contDiffOn
    (contDiffOn_fullLeadingCovector T Q F row col Φ Y r hspace hphase hα)
  have hb₁ := contDiffOn_fullCorrectionCovector_of_leading_outputs
    T Q F row col Φ Y r hΩ hspace hphase hF hi hα hnonzero
  have hA := contDiffOn_fullDisplacementAmplitude_of_leading_outputs
    T Q F row col Φ Y r hτ hΩ hspace hphase hF hi hrank hα hnonzero
  have hslice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {f : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → E}
      (hf : ContDiffOn ℝ ∞ f Ω) {η : Euclidean (n - 1)} (hη : η ∈ V) :
      ContDiffOn ℝ ∞ (fun y ↦ f (y, (z, T.reference.spatialPatch z + τ • η))) X :=
    hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun y hy ↦ hshift (y, η) ⟨hy, hη⟩)
  exact canonicalWideWave_derivative_representation F hτ
    (fun p ↦ phase T Q p.1 p.2)
    (fun p ↦ euclideanComplexInclusion (fullLeadingCovector T Q F row col Φ Y r (p.1, (z, p.2))))
    (fun p ↦ fullCorrectionCovector T Q F row col Φ Y r (p.1, (z, p.2)))
    (T.reference.spatialPatch z) hX hV hVceil
    (contDiffOn_shiftedFullPrimaryAtom T Q F row col Φ Y r
      hΩ hspace hphase hF hi hrank hα hnonzero τ z hshift)
    (fun η hη ↦ (hslice hs hη).differentiableOn (by simp))
    (fun η hη ↦ (hslice ha hη).differentiableOn (by simp))
    (fun η hη ↦ (hslice hb₁ hη).differentiableOn (by simp)) hd hM hb v hx
    (fun η hη ↦ ((hslice hA hη).contDiffAt (hX.mem_nhds hx)).differentiableAt (by simp)) e

end JanetCartan.RawPrimary
