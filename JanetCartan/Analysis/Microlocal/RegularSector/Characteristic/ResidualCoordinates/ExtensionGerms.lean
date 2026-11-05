module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.SupportedConic

/-!
# Physical differentiation of supported extensions

Physical derivatives depend on germs, with the source time and covector
frozen. These lemmas transfer the actual conic column producer through its
supported extension. The auxiliary frequency cutoff is constant in physical
variables; the auxiliary output-time cutoff is removed only on its plateau.
Consumer: `supported_conic_column_cancellation`.
Source: `app:ch_regular_base:eq:two-term-null-identity` and
`app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ResidualCoordinates
open EvolutionIntegral EvolutionIntegral.KernelIdentification AmplitudeBounds
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d n : ℕ}
local notation "T" => TwoTimePoint (Euclidean d)
local notation "E" => Euclidean (d + 1)
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "FV" => Fin n → ℂ

/-- The physical operator is unchanged by equality on a neighborhood,
including its zeroth-order term. Source: `app:ch_regular_base:eq:two-term-null-identity`. -/
theorem firstOrderApply_eq_of_germ
    (A : E → Fin (d + 1) → Mat) (B : E → Mat) {u v : E → FV} {x : E}
    (hu : u =ᶠ[𝓝 x] v) :
    WKB.firstOrderApply (fun y a ↦ (A y a).mulVecLin) (fun y ↦ (B y).mulVecLin) u x =
      WKB.firstOrderApply (fun y a ↦ (A y a).mulVecLin) (fun y ↦ (B y).mulVecLin) v x := by
  simp only [WKB.firstOrderApply, partialDeriv, hu.fderiv_eq, hu.eq_of_nhds]

private theorem firstOrderApply_const_smul
    (A : E → Fin (d + 1) → Mat) (B : E → Mat) (z : ℂ) (u : E → FV) (x : E) :
    WKB.firstOrderApply (fun y a ↦ (A y a).mulVecLin) (fun y ↦ (B y).mulVecLin)
      (fun y ↦ z • u y) x =
      z • WKB.firstOrderApply (fun y a ↦ (A y a).mulVecLin) (fun y ↦ (B y).mulVecLin) u x := by
  have hd : fderiv ℝ (fun y ↦ z • u y) x = z • fderiv ℝ u x :=
    congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := u) z) x
  simp only [WKB.firstOrderApply, partialDeriv, hd, _root_.smul_apply,
    map_smul, Finset.smul_sum, smul_add]

/-- The differentiated matrix of an extension is exactly the scalar multiple
of the original differentiated matrix when their physical germs agree.
This requires no assumed derivative agreement.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem twoTimePhysicalApply_eq_of_scaled_germ
    (A : E → Fin (d + 1) → Mat) (B : E → Mat)
    (W V : TwoTimeAmplitude d n) (z : ℂ) (s : ℝ) (η : Euclidean d) (x : E)
    (hW : (fun y ↦ W (y 0) s (spatialPart y) η) =ᶠ[𝓝 x]
      fun y ↦ z • V (y 0) s (spatialPart y) η) :
    twoTimePhysicalApply A B W (x 0) s (spatialPart x) η =
      z • twoTimePhysicalApply A B V (x 0) s (spatialPart x) η := by
  have hx : timeSpacePoint (x 0) (spatialPart x) = x :=
    timeSpaceMeasurableEquiv.symm_apply_apply x
  have hd : fderiv ℝ (fun y ↦ W (y 0) s (spatialPart y) η) x =
      z • fderiv ℝ (fun y ↦ V (y 0) s (spatialPart y) η) x :=
    hW.fderiv_eq.trans (congrFun (fderiv_const_smul_field (𝕜 := ℝ)
      (f := fun y ↦ V (y 0) s (spatialPart y) η) z) x)
  simp only [twoTimePhysicalApply, physicalSymbolApply, hx, partialDeriv, hd,
    _root_.smul_apply, hW.eq_of_nhds, Matrix.mul_smul,
    Finset.smul_sum, smul_add]

/-- Cancellation transfers through a phase germ and constant physical
scaling of both amplitudes. The local equation here is consumed directly
from `conic_column_cancellation`, not supplied by a new kernel record.
Source: `app:ch_regular_base:eq:two-term-null-identity`. -/
theorem column_cancellation_of_scaled_germs
    (A : E → Fin (d + 1) → Mat) (B : E → Mat)
    (Ψ G : TwoTimePhase d) (W₀ W₁ V₀ V₁ : TwoTimeAmplitude d n)
    (z : ℂ) (s : ℝ) (η : Euclidean d) (x : E) (j : Fin n)
    (hG : (fun y ↦ G (y 0) s (spatialPart y) η) =ᶠ[𝓝 x]
      fun y ↦ Ψ (y 0) s (spatialPart y) η)
    (h₀ : (fun y ↦ V₀ (y 0) s (spatialPart y) η) =ᶠ[𝓝 x]
      fun y ↦ z • W₀ (y 0) s (spatialPart y) η)
    (h₁ : (fun y ↦ V₁ (y 0) s (spatialPart y) η) =ᶠ[𝓝 x]
      fun y ↦ z • W₁ (y 0) s (spatialPart y) η)
    (hid : WKB.firstOrderApply (fun y a ↦ (A y a).mulVecLin) (fun y ↦ (B y).mulVecLin)
      (fun y ↦ Complex.exp (Complex.I * (Ψ (y 0) s (spatialPart y) η : ℂ)) •
        (fun k ↦ (W₀ + W₁) (y 0) s (spatialPart y) η k j)) x =
      Complex.exp (Complex.I * (Ψ (x 0) s (spatialPart x) η : ℂ)) •
        (fun k ↦ twoTimePhysicalApply A B W₁ (x 0) s (spatialPart x) η k j)) :
    WKB.firstOrderApply (fun y a ↦ (A y a).mulVecLin) (fun y ↦ (B y).mulVecLin)
      (fun y ↦ Complex.exp (Complex.I * (G (y 0) s (spatialPart y) η : ℂ)) •
        (fun k ↦ (V₀ + V₁) (y 0) s (spatialPart y) η k j)) x =
      Complex.exp (Complex.I * (G (x 0) s (spatialPart x) η : ℂ)) •
        (fun k ↦ twoTimePhysicalApply A B V₁ (x 0) s (spatialPart x) η k j) := by
  have he : (fun y ↦ Complex.exp (Complex.I * (G (y 0) s (spatialPart y) η : ℂ)) •
      (fun k ↦ (V₀ + V₁) (y 0) s (spatialPart y) η k j)) =ᶠ[𝓝 x]
      fun y ↦ z • (Complex.exp (Complex.I * (Ψ (y 0) s (spatialPart y) η : ℂ)) •
        (fun k ↦ (W₀ + W₁) (y 0) s (spatialPart y) η k j)) := by
    filter_upwards [hG, h₀, h₁] with y hy h₀y h₁y
    ext k
    simp only [Pi.add_apply, Matrix.add_apply, hy, h₀y, h₁y, Matrix.smul_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  rw [firstOrderApply_eq_of_germ A B he, firstOrderApply_const_smul, hid,
    twoTimePhysicalApply_eq_of_scaled_germ A B V₁ W₁ z s η x h₁, hG.eq_of_nhds]
  ext k
  simp only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Off both supported amplitudes, the entire oscillatory kernel and `P W₁`
vanish as germs, regardless of the auxiliary phase's value there. No
smoothness or phase identity outside the carrier is needed.
Source: `app:ch_regular_base:eq:two-term-null-identity`. -/
theorem column_cancellation_of_zero_germs
    (A : E → Fin (d + 1) → Mat) (B : E → Mat) (G : TwoTimePhase d)
    (V₀ V₁ : TwoTimeAmplitude d n) (s : ℝ) (η : Euclidean d) (x : E) (j : Fin n)
    (h₀ : (fun y ↦ V₀ (y 0) s (spatialPart y) η) =ᶠ[𝓝 x] 0)
    (h₁ : (fun y ↦ V₁ (y 0) s (spatialPart y) η) =ᶠ[𝓝 x] 0) :
    WKB.firstOrderApply (fun y a ↦ (A y a).mulVecLin) (fun y ↦ (B y).mulVecLin)
      (fun y ↦ Complex.exp (Complex.I * (G (y 0) s (spatialPart y) η : ℂ)) •
        (fun k ↦ (V₀ + V₁) (y 0) s (spatialPart y) η k j)) x =
      Complex.exp (Complex.I * (G (x 0) s (spatialPart x) η : ℂ)) •
        (fun k ↦ twoTimePhysicalApply A B V₁ (x 0) s (spatialPart x) η k j) := by
  have he : (fun y ↦ Complex.exp (Complex.I * (G (y 0) s (spatialPart y) η : ℂ)) •
      (fun k ↦ (V₀ + V₁) (y 0) s (spatialPart y) η k j)) =ᶠ[𝓝 x] 0 := by
    filter_upwards [h₀, h₁] with y h₀y h₁y
    ext k
    simp [h₀y, h₁y]
  have hz : twoTimePhysicalApply A B V₁ (x 0) s (spatialPart x) η = 0 := by
    have hg : (fun y ↦ V₁ (y 0) s (spatialPart y) η) =ᶠ[𝓝 x]
        fun y ↦ (0 : ℂ) • V₁ (y 0) s (spatialPart y) η := by
      filter_upwards [h₁] with y hy
      simpa using hy
    simpa using twoTimePhysicalApply_eq_of_scaled_germ A B V₁ V₁ 0 s η x hg
  rw [firstOrderApply_eq_of_germ A B he, hz]
  ext k
  simp [WKB.firstOrderApply, partialDeriv]

/-- The same compact chart extension becomes a constant physical scaling
of the actual conic matrix on the output-time plateau. Source:
`app:ch_regular_base:eq:two-term-null-identity`. -/
theorem supportedConic_buffered_slice_germ
    (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ) (ρ : Euclidean d → ℝ)
    {V : Set T} (hV : IsOpen V) (κ : ℝ → ℝ) (W : TwoTimeAmplitude d (d + 1))
    (s : ℝ) (η : Euclidean d) (x : E) (hℓ : ℓ η ≠ 0)
    (hp : ConicPhase.normalize ℓ (x 0, (s, (spatialPart x, η))) ∈ V)
    (hκ : κ =ᶠ[𝓝 (x 0)] fun _ ↦ 1) :
    (fun y ↦ supportedConicMatrix ℓ o ρ
      (fun p ↦ bufferedAmplitude V κ W p.1 p.2.1 p.2.2.1 p.2.2.2)
      (y 0, (s, (spatialPart y, η)))) =ᶠ[𝓝 x]
      fun y ↦ (ρ η : ℂ) • ConicAmplitude.extend ℓ o
        (fun p ↦ W p.1 p.2.1 p.2.2.1 p.2.2.2) (y 0, (s, (spatialPart y, η))) := by
  have hsl : ContinuousAt (fun y : E ↦ (y 0, (s, (spatialPart y, η)))) x :=
    (contDiff_physicalSlice (coordinateSplit (0 : Fin (d + 1))) s η).continuous.continuousAt
  have hn := (ConicPhase.contDiffAt_normalize ℓ hℓ).continuousAt.comp hsl
  have hv := hn.preimage_mem_nhds (hV.mem_nhds hp)
  have ht := hκ.comp_tendsto (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).continuous.continuousAt
  filter_upwards [hv, ht] with y hy hκy
  change κ (y 0) = 1 at hκy
  change (y 0, (s, (spatialPart y, (ℓ η)⁻¹ • η))) ∈ V at hy
  simp only [supportedConicMatrix, ConicAmplitude.extend, bufferedAmplitude,
    ConicPhase.normalize, indicator_of_mem hy, hκy, Complex.ofReal_one, one_smul]
  ext k j
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

end JanetCartan.RegularSector.Characteristic.ResidualCoordinates
