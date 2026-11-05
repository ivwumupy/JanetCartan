module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.SupportedCancellation

/-!
# The supported conic leading endpoint

The upper endpoint is the original source symbol times the SAME oblique
projector, at every frequency. On the chart this is the actual signed row's
initial value. Outside the chart the compact source mask vanishes. The
auxiliary output-time cutoff is removed only on its plateau.
Consumer: `CompleteResidual.completeResidual_operators_of_graph_regularizations`.
Source: `app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Matrix
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ResidualCoordinates
open EvolutionIntegral EvolutionIntegral.KernelIdentification AmplitudeBounds
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "T" => TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d + 1)

/-- The source symbol after the SAME fixed radial continuation and auxiliary
frequency plateau. On the support of the original right multiplier that
plateau is one. Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
def conicSourceSymbol (ℓ : Euclidean d →L[ℝ] ℝ) (ρ : Euclidean d → ℝ)
    (σ : RootState (Euclidean d) → ℝ) (x : E) (η : Euclidean d) : ℂ :=
  (ρ η : ℂ) * sourceSymbol σ x ((ℓ η)⁻¹ • η)

/-- Global endpoint equality for the actual supported leading matrix. The
only initial-value hypothesis is the exact local column output from
`exists_pencil_leading_amplitude`; no global leading-endpoint identity is
assumed. The same-flow initial condition is produced by
`flow_initial_of_diagonal_outputs`. Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem supported_leading_endpoint
    (ℓ : Euclidean d →L[ℝ] ℝ) (i : Fin (d + 1))
    (Q : E → Fin (d + 1) → Mat) (B : E → Mat)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph T T) (hC : (C : T → T) = twoTimeProjection Φ)
    (r c : Fin (d + 1)) (σ : RootState (Euclidean d) → ℝ)
    (I : Set ℝ) (U : Set (Euclidean d × Euclidean d))
    (hbox : I ×ˢ (I ×ˢ U) ⊆ C.source) (hi : ∀ w ∈ I ×ˢ U, Φ (w, 0) = w)
    (hσI : tsupport σ ⊆ I ×ˢ U) (κ : ℝ → ℝ) (ρ : Euclidean d → ℝ)
    (hinit : ∀ w ∈ I ×ˢ U, ∀ j,
      pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j (w.1, w) =
      (σ w * minorLeftNullvector (rootPencil (coordinateSplit i) Q h w)
        (rootTimeCoefficient (coordinateSplit i) Q w) r c j) •
          minorRightNullvector (rootPencil (coordinateSplit i) Q h w) r c)
    (x : E) (hκ : κ (x 0) = 1) (η : Euclidean d) :
    let V := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))
    let F := fun p : T ↦ bufferedAmplitude V κ (leading i Q B h Φ C r c σ)
      p.1 p.2.1 p.2.2.1 p.2.2.2
    (coefficient i Q x 0).map Complex.ofReal *
      curryCharacteristicMatrix (supportedConicMatrix ℓ 0 ρ F)
        (x 0) (x 0) (spatialPart x) η =
      conicSourceSymbol ℓ ρ σ x η • projector i Q h r c x ((ℓ η)⁻¹ • η) := by
  dsimp only
  let V := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))
  let w := rootState x ((ℓ η)⁻¹ • η)
  have hmem (hw : w ∈ I ×ˢ U) : (w.1, w) ∈ V := by
    have hs : (w.1, w) ∈ C.source := hbox ⟨hw.1, hw⟩
    have he : C (w.1, w) = (w.1, w) := by
      simp [hC, twoTimeProjection, twoTimeState, hi w hw]
    have hinv : C.symm (w.1, w) = (w.1, w) := by simpa only [he] using C.left_inv hs
    refine ⟨he ▸ C.map_source hs, ?_⟩
    change C.symm (w.1, w) ∈ I ×ˢ (I ×ˢ U)
    rw [hinv]
    exact ⟨hw.1, hw⟩
  by_cases hp : (w.1, w) ∈ V
  · obtain ⟨ht, hs, hη, hy⟩ := twoTimeChart_inverse_coordinates hC hp.1
    have hstate : twoTimeState Φ (C.symm (w.1, w)) = (C.symm (w.1, w)).2 := by
      simp only [twoTimeState, ht, hs, sub_self, hi _ hp.2.2]
    rw [hstate] at hy
    have hinv : C.symm (w.1, w) = (w.1, w) := Prod.ext ht (Prod.ext hs (Prod.ext hy hη))
    have hw : w ∈ I ×ˢ U := by simpa only [hinv] using hp.2.2
    have hend := leading_endpoint i Q B h Φ C r c σ x ((ℓ η)⁻¹ • η) (hinit w hw)
    have hbuf : bufferedAmplitude V κ (leading i Q B h Φ C r c σ)
        (x 0) (x 0) (spatialPart x) ((ℓ η)⁻¹ • η) =
        leading i Q B h Φ C r c σ (x 0) (x 0) (spatialPart x) ((ℓ η)⁻¹ • η) := by
      change V.indicator _ (w.1, w) = _
      rw [indicator_of_mem hp]
      simp only [w, rootState, hκ, Complex.ofReal_one, one_smul]
    change (coefficient i Q x 0).map Complex.ofReal *
      (ρ η • ((ℓ η)⁻¹ ^ 0 • bufferedAmplitude V κ (leading i Q B h Φ C r c σ)
        (x 0) (x 0) (spatialPart x) ((ℓ η)⁻¹ • η))) = _
    rw [pow_zero, one_smul, hbuf, Matrix.mul_smul, hend]
    ext k j
    simp only [conicSourceSymbol, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    ring
  · have hz : σ w = 0 := by
      by_contra hn
      exact hp (hmem (hσI (subset_tsupport σ hn)))
    have hbuf : bufferedAmplitude V κ (leading i Q B h Φ C r c σ)
        (x 0) (x 0) (spatialPart x) ((ℓ η)⁻¹ • η) = 0 := indicator_of_notMem hp _
    change (coefficient i Q x 0).map Complex.ofReal *
      (ρ η • ((ℓ η)⁻¹ ^ 0 • bufferedAmplitude V κ (leading i Q B h Φ C r c σ)
        (x 0) (x 0) (spatialPart x) ((ℓ η)⁻¹ • η))) = _
    simp [hbuf, conicSourceSymbol, sourceSymbol, show σ (rootState x ((ℓ η)⁻¹ • η)) = 0 from hz]

end JanetCartan.RegularSector.Characteristic.ResidualCoordinates
