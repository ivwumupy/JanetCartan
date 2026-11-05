module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.FullSuperposition
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Polynomial.Formulas
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.PhysicalBounds.Atoms

/-!
# Frobenius matrix representation of the actual raw differential

The coordinatewise identity already proved for the literal raw integral is
assembled into the SAME matrix amplitude used by the physical and Sobolev
estimates. Integrability is derived from the original wide Hilbert density
and smoothness on the buffered chart. No change of input or output norm is
made (`app:ch_waves:eq:individual-representation`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase RawInputPartition
open AmplitudeGrades.Polynomial

/-- The actual raw differential, as a Frobenius matrix, is the integral of
its literal derivative amplitude. The smooth amplitude premise is supplied
by `exists_finite_actual_graded_raw_family` on the SAME flows and scalar
(`app:ch_waves:eq:individual-representation`). -/
theorem fullPrimaryWave_differentialMatrix_representation
    {n N J : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
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
    {τ : ℝ} (hτ : τ ≠ 0)
    (hA : ContDiffOn ℝ ∞ (fullDerivativeAmplitude T Q F row col Φ Y r τ) Ω)
    (z : Euclidean 3) {X : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    (hX : IsOpen X) (hV : IsOpen V) (hζ : T.reference.spatialPatch z ∈ V)
    (hproduct : ∀ p ∈ X ×ˢ V, (p.1, (z, p.2)) ∈ Ω)
    (hshift : ∀ η ∈ closedBall 0 ((2 : ℝ) ^ J), T.reference.spatialPatch z + τ • η ∈ V)
    {d : Euclidean (n - 1) → ℂ} {Md : ℝ}
    (hd : Measurable d) (hMd : 0 ≤ Md) (hdb : ∀ η, ‖d η‖ ≤ Md)
    (v : WideInput n J) {x : Euclidean n} (hx : x ∈ X) :
    Complex.exp (-Complex.I * (T.carrier Q x z / τ : ℝ)) •
        AmplitudeGrades.Polynomial.differentialMatrix n N (fderiv ℝ (fullPrimaryWave T Q F row col Φ Y τ r z d v) x) =
      rawPrimaryDemodulatedIntegral (fun y ξ ↦ phase T Q y ξ)
        (fun y ξ ↦ fullDerivativeAmplitude T Q F row col Φ Y r τ (y, (z, ξ)))
        (T.reference.spatialPatch z) τ volume (weightedWideDensity d v) x := by
  let Vη := {η | T.reference.spatialPatch z + τ • η ∈ V}
  have hVη : IsOpen Vη := hV.preimage (by fun_prop)
  have hs : ∀ p ∈ X ×ˢ Vη,
      (p.1, (z, T.reference.spatialPatch z + τ • p.2)) ∈ Ω :=
    fun p hp ↦ hproduct (p.1, T.reference.spatialPatch z + τ • p.2) ⟨hp.1, hp.2⟩
  have hmap : ContDiffOn ℝ ∞
      (fun p : Euclidean n × Euclidean (n - 1) ↦ (p.1, (z, p.2))) (X ×ˢ V) :=
    contDiffOn_fst.prodMk (contDiffOn_const.prodMk contDiffOn_snd)
  have hS : ContDiffOn ℝ ∞ (Function.uncurry (fun y ξ ↦ phase T Q y ξ)) (X ×ˢ V) :=
    (contDiffOn_fullPhase T Q hphase).comp
      hmap hproduct
  have hA' : ContDiffOn ℝ ∞ (Function.uncurry
      (fun y ξ ↦ fullDerivativeAmplitude T Q F row col Φ Y r τ (y, (z, ξ)))) (X ×ˢ V) :=
    hA.comp hmap hproduct
  have hB := contDiffOn_rawPrimaryDemodulatedAtom (Ω := Vη) hS hA' hζ (fun _ h ↦ h)
  have hI := integrable_wideSuperposition hshift hB.continuousOn hd hMd hdb v hx
  have hI' : Integrable (fun η ↦
      Complex.exp (Complex.I * (rawPrimaryPhaseDifference (fun y ξ ↦ phase T Q y ξ)
        (T.reference.spatialPatch z) τ x η : ℝ)) •
      (weightedWideDensity d v η • fullDerivativeAmplitude T Q F row col Φ Y r τ
        (x, (z, T.reference.spatialPatch z + τ • η)))) :=
    hI.congr (Filter.Eventually.of_forall fun η ↦ smul_comm _ _ _)
  ext i j
  let column : Matrix (Fin N) (Fin n) ℂ →L[ℂ] EuclideanSpace ℂ (Fin N) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun M ↦ WithLp.toLp 2 (fun i ↦ M i j)
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
  have hcolumn : column
      (rawPrimaryDemodulatedIntegral (fun y ξ ↦ phase T Q y ξ)
        (fun y ξ ↦ fullDerivativeAmplitude T Q F row col Φ Y r τ (y, (z, ξ)))
        (T.reference.spatialPatch z) τ volume (weightedWideDensity d v) x) =
      rawPrimaryDemodulatedIntegral (fun y ξ ↦ phase T Q y ξ)
        (fun y ξ ↦ waveFirstAmplitude τ⁻¹ (fun t ↦ phase T Q t ξ)
          (fun t ↦ fullDisplacementAmplitude T Q F row col Φ Y r τ (t, (z, ξ)))
            y (EuclideanSpace.single j 1))
        (T.reference.spatialPatch z) τ volume (weightedWideDensity d v) x := by
    unfold rawPrimaryDemodulatedIntegral
    rw [← column.integral_comp_comm hI']
    apply integral_congr_ae
    filter_upwards [] with η
    ext k
    rfl
  have hrep := fullPrimaryWave_derivative_representation T Q F row col Φ Y r
    hΩ hspace hphase hF hi hrank hα hnonzero τ z hs hX hVη hshift
      hd hMd hdb hτ v hx (EuclideanSpace.single j 1)
  exact (congrArg (fun u : EuclideanSpace ℂ (Fin N) ↦ u i) hrep).trans
    (congrArg (fun u : EuclideanSpace ℂ (Fin N) ↦ u i) hcolumn).symm

end JanetCartan.RawPrimary
