module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.PhysicalCoordinates
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Vector

/-!
# Fourier transport through the selected physical coordinate permutation

The actual volume-preserving permutation acts on the frequency variable by the
same orthogonal map. Extend the integral identity from Schwartz functions to
literal Lebesgue L² by density, then use the radial Bessel weight. The finite
complex fiber and the cycle Fourier normalization are unchanged. These are the
coordinate identities consumed by the finite physical solver's estimates in
`app:ch_regular_base:eq:sector-theorem-solution` and
`app:ch_regular_base:eq:sector-theorem-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory FourierTransform
open scoped SchwartzMap
namespace JanetCartan.RegularSector.FiniteEvolution
open Characteristic.ResidualCoordinates Characteristic.EvolutionIntegral Pseudodifferential
variable {d q : ℕ}
local notation "Dom" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d q
local notation "L²" => Lp ℂ 2 (volume : Measure Dom)

/-- The dual action of the physical permutation in the cycle Fourier integral.
The unit Jacobian and preserved inner product are those of the actual map;
source: `app:ch_regular_base:eq:fixed-time-representation` in `paper-v2.tex`. -/
theorem fourier_comp_physicalCoordinates (i : Fin (d+1))
    (f : Dom → EuclideanSpace ℂ (Fin q)) (ξ : Dom) :
    𝓕 (f ∘ physicalCoordinates i) ξ = 𝓕 f (physicalCoordinates i ξ) :=
  Real.fourier_comp_linearIsometry (physicalCoordinateIsometry i) f ξ

/-- The manuscript's unnormalized physical Fourier transform has exactly the
same dual coordinate action. Its `2π` frequency rescaling is retained
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem sourceInputFourierTransform_physicalCoordinates (i : Fin (d+1))
    (f : 𝓢(Dom, Fin q → ℂ)) (ξ : Dom) :
    FourierIntegral.sourceInputFourierTransform
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (physicalCoordinates i) f) ξ =
    FourierIntegral.sourceInputFourierTransform f (physicalCoordinates i ξ) := by
  change 𝓕 ((f : Dom → Fin q → ℂ) ∘ physicalCoordinates i) ((2 * Real.pi)⁻¹ • ξ) =
    𝓕 (f : Dom → Fin q → ℂ) ((2 * Real.pi)⁻¹ • physicalCoordinates i ξ)
  exact (Real.fourier_comp_linearIsometry (physicalCoordinateIsometry i) f _).trans
    (congrArg (𝓕 (f : Dom → Fin q → ℂ))
      ((physicalCoordinateIsometry i).map_smul _ _))

private abbrev coordinatePullback {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (i : Fin (d+1)) :
    Lp F 2 (volume : Measure Dom) →ₗᵢ[ℂ] Lp F 2 (volume : Measure Dom) :=
  Lp.compMeasurePreservingₗᵢ ℂ (physicalCoordinates i)
    (measurePreserving_physicalCoordinates i)

private theorem coordinatePullback_schwartz {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (i : Fin (d+1)) (f : 𝓢(Dom, F)) :
    coordinatePullback i (f.toLp 2) =
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (physicalCoordinates i) f).toLp 2 := by
  apply Lp.ext
  have h := (measurePreserving_physicalCoordinates i).quasiMeasurePreserving.ae_eq_comp
    (f.coeFn_toLp 2)
  exact (Lp.coeFn_compMeasurePreserving _ _).trans
    (h.trans ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (physicalCoordinates i) f).coeFn_toLp 2).symm)

private theorem coordinatePullback_fourier {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (i : Fin (d+1))
    (u : Lp F 2 (volume : Measure Dom)) :
    𝓕 (coordinatePullback i u) = coordinatePullback i (𝓕 u) := by
  have he : (fun u : Lp F 2 (volume : Measure Dom) ↦ 𝓕 (coordinatePullback i u)) =
      (fun u : Lp F 2 (volume : Measure Dom) ↦ coordinatePullback i (𝓕 u)) := by
    apply (SchwartzMap.denseRange_toLpCLM (E := Dom) (F := F) (p := 2)
      ENNReal.ofNat_ne_top).equalizer
      (continuous_fourier.comp (coordinatePullback i).continuous)
      ((coordinatePullback i).continuous.comp continuous_fourier)
    funext f
    change 𝓕 (coordinatePullback i (f.toLp 2)) = coordinatePullback i (𝓕 (f.toLp 2))
    rw [coordinatePullback_schwartz, SchwartzMap.toLp_fourier_eq,
      SchwartzMap.toLp_fourier_eq, coordinatePullback_schwartz]
    congr 1
    ext ξ
    simp only [SchwartzMap.fourier_coe, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Function.comp_apply]
    exact Real.fourier_comp_linearIsometry (physicalCoordinateIsometry i) f ξ
  exact congrFun he u

/-- Fourier transport on the existing finite-vector Lebesgue L² classes,
proved by Schwartz density (`fixed-time-representation`). -/
theorem physicalPullbackL2_fourier (i : Fin (d+1)) (u : H) :
    𝓕 (physicalPullbackL2 i u) = physicalPullbackL2 i (𝓕 u) :=
  coordinatePullback_fourier i u

/-- The inverse coordinate transport has the inverse dual action, with the
same Fourier normalization (`app:ch_regular_base:eq:measured-adjoint`). -/
theorem physicalPullbackL2_symm_fourier (i : Fin (d+1)) (u : H) :
    𝓕 ((physicalPullbackL2 i).symm u) = (physicalPullbackL2 i).symm (𝓕 u) := by
  apply (physicalPullbackL2 i).injective
  rw [← physicalPullbackL2_fourier, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.apply_symm_apply]

private theorem coordinate_physicalPullback (i : Fin (d+1)) (u : H) (a : Fin q) :
    finiteL2CoordinateIsometry volume (physicalPullbackL2 i u) a =
      coordinatePullback i (finiteL2CoordinateIsometry volume u a) := by
  apply Lp.ext
  have h := (measurePreserving_physicalCoordinates i).quasiMeasurePreserving.ae_eq_comp
    (finiteL2Coordinates_apply_ae volume u a)
  filter_upwards [finiteL2Coordinates_apply_ae volume (physicalPullbackL2 i u) a,
    physicalPullbackL2_coeFn i u, Lp.coeFn_compMeasurePreserving
      (finiteL2CoordinateIsometry volume u a) (measurePreserving_physicalCoordinates i), h]
    with x hx hy hz hw
  exact hx.trans ((congrArg (fun v : EuclideanSpace ℂ (Fin q) ↦ v a) hy).trans
    (hw.symm.trans hz.symm))

private theorem weighted_coordinatePullback (i : Fin (d+1)) (s : ℝ) (u : L²) :
    weightedL2Fourier s (coordinatePullback i u) =ᵐ[volume]
      weightedL2Fourier s u ∘ physicalCoordinates i := by
  have h := Lp.coeFn_compMeasurePreserving (𝓕 u) (measurePreserving_physicalCoordinates i)
  filter_upwards [h] with ξ hξ
  simp only [weightedL2Fourier, coordinatePullback_fourier, Function.comp_apply]
  change (coordinatePullback i (𝓕 u)) ξ = (𝓕 u) (physicalCoordinates i ξ) at hξ
  rw [hξ]
  congr 1
  exact congrArg (fun r : ℝ ↦ (1 + r^2) ^ (s/2))
    ((physicalCoordinateIsometry i).norm_map ξ).symm

private theorem scalar_mem_coordinatePullback (i : Fin (d+1)) (s : ℝ) (u : L²) :
    MemFourierSobolev s (coordinatePullback i u) ↔ MemFourierSobolev s u := by
  unfold MemFourierSobolev
  rw [memLp_congr_ae (weighted_coordinatePullback i s u)]
  have h := (physicalCoordinates i).toHomeomorph.measurableEmbedding.memLp_map_measure_iff
    (g := weightedL2Fourier s u) (p := 2) (μ := volume)
  change MemLp (weightedL2Fourier s u) 2
    (Measure.map (physicalCoordinates i) volume) ↔
      MemLp (weightedL2Fourier s u ∘ physicalCoordinates i) 2 volume at h
  rw [(measurePreserving_physicalCoordinates i).map_eq] at h
  exact h.symm

private theorem scalar_norm_coordinatePullback (i : Fin (d+1)) (s : ℝ) (u : L²) :
    fourierSobolevNorm s (coordinatePullback i u) = fourierSobolevNorm s u := by
  unfold fourierSobolevNorm
  rw [eLpNorm_congr_ae (weighted_coordinatePullback i s u),
    eLpNorm_comp_measurePreserving (aestronglyMeasurable_weightedL2Fourier s u)
      (measurePreserving_physicalCoordinates i)]

/-- Physical pullback preserves the existing Sobolev membership at every real
order, including both signs of every integer (`sector-theorem-residual`). -/
@[simp] theorem memVectorFourierSobolev_physicalPullbackL2
    (i : Fin (d+1)) (s : ℝ) (u : H) :
    MemVectorFourierSobolev s (physicalPullbackL2 i u) ↔ MemVectorFourierSobolev s u := by
  unfold MemVectorFourierSobolev MemMatrixFourierSobolev
  simp only [coordinate_physicalPullback, scalar_mem_coordinatePullback]

/-- The physical permutation introduces no constant in the signed Fourier
Sobolev norm (`sector-theorem-solution`, `sector-theorem-residual`). -/
@[simp] theorem vectorFourierSobolevNorm_physicalPullbackL2
    (i : Fin (d+1)) (s : ℝ) (u : H) :
    vectorFourierSobolevNorm s (physicalPullbackL2 i u) = vectorFourierSobolevNorm s u := by
  unfold vectorFourierSobolevNorm matrixFourierSobolevNorm
  simp only [coordinate_physicalPullback, scalar_norm_coordinatePullback]

/-- Inverse pullback preserves the same signed Sobolev membership; no change
of L² model or distribution completion (`measured-adjoint`). -/
@[simp] theorem memVectorFourierSobolev_physicalPullbackL2_symm
    (i : Fin (d+1)) (s : ℝ) (u : H) :
    MemVectorFourierSobolev s ((physicalPullbackL2 i).symm u) ↔
      MemVectorFourierSobolev s u := by
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    (memVectorFourierSobolev_physicalPullbackL2 i s ((physicalPullbackL2 i).symm u)).symm

/-- Inverse transport retains the exact signed Fourier Sobolev norm
(`app:ch_regular_base:eq:measured-adjoint`). -/
@[simp] theorem vectorFourierSobolevNorm_physicalPullbackL2_symm
    (i : Fin (d+1)) (s : ℝ) (u : H) :
    vectorFourierSobolevNorm s ((physicalPullbackL2 i).symm u) = vectorFourierSobolevNorm s u := by
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    (vectorFourierSobolevNorm_physicalPullbackL2 i s ((physicalPullbackL2 i).symm u)).symm

end JanetCartan.RegularSector.FiniteEvolution
