module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FourierAssembly.Tests

/-!
# Extension of vector graph estimates to all Sobolev inputs

For `app:ch_regular_base:eq:fio-input`, apply the proved scalar compact-smooth
extension to the finitely many blocks of a supplied bounded vector L² operator.
The fixed fiber factor is harmless; no output membership or density premise is
assumed. This is consumed by `jc-deduce-fio-strong-sobolev`.
-/

@[expose] public noncomputable section
open MeasureTheory JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound
open scoped ContDiff
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- Isometric insertion into one vector L² coordinate, for the density
extension of `app:ch_regular_base:eq:fio-input`. -/
def graphL2CoordinateInjection (a : Fin r) : L² →ₗᵢ[ℂ] H :=
  (finiteL2CoordinateIsometry volume).symm.toLinearIsometry.comp (coordinateInjection a)

private theorem scalar_sobolevNorm_zero (s : ℝ) : fourierSobolevNorm (d := n) s 0 = 0 := by
  have he : weightedL2Fourier (d := n) s 0 = 0 := by
    funext x
    simp [weightedL2Fourier]
  simp [fourierSobolevNorm, he]

/-- A single coordinate has exactly its scalar Fourier norm, for the
blockwise compact-test extension of `app:ch_regular_base:eq:fio-input`. -/
theorem graphL2CoordinateInjection_sobolevNorm (s : ℝ) (a : Fin r) (u : L²) :
    vectorFourierSobolevNorm s (graphL2CoordinateInjection a u) = fourierSobolevNorm s u := by
  classical
  change matrixFourierSobolevNorm s
    (finiteL2CoordinateIsometry volume ((finiteL2CoordinateIsometry volume).symm
      (coordinateInjection a u))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  have he : (WithLp.toLp 2 (fun b ↦ fourierSobolevNorm s (coordinateInjection a u b)) :
      EuclideanSpace ℝ (Fin r)) = PiLp.single 2 a (fourierSobolevNorm s u) := by
    ext b
    by_cases hb : b = a
    · subst b; simp [coordinateInjection]
    · simp [coordinateInjection, hb, scalar_sobolevNorm_zero]
  rw [matrixFourierSobolevNorm, he, PiLp.norm_single, Real.norm_eq_abs,
    abs_of_nonneg (fourierSobolevNorm_nonneg _ _)]

/-- A scalar compact smooth test inserted into one fiber coordinate is an
actual `graphTestSpace` test. Source: extension of `app:ch_regular_base:eq:fio-input`. -/
theorem graphL2CoordinateInjection_compactSmooth (a : Fin r) (g : E → ℂ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ∃ u : graphTestSpace n r, graphTestToLp u = graphL2CoordinateInjection a
      ((hg.continuous.memLp_of_hasCompactSupport hc).toLp g) := by
  let L : ℂ →ₗᵢ[ℂ] V := coordinateInjection a
  let u : graphTestSpace n r := ⟨fun x ↦ L (g x),
    (L.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp hg, hc.comp_left L.map_zero⟩
  refine ⟨u, ?_⟩
  apply (finiteL2CoordinateIsometry volume).injective
  change finiteL2CoordinateIsometry volume (graphTestToLp u) =
    finiteL2CoordinateIsometry volume ((finiteL2CoordinateIsometry volume).symm
      (coordinateInjection a ((hg.continuous.memLp_of_hasCompactSupport hc).toLp g)))
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply PiLp.ext
  intro b
  apply Lp.ext
  filter_upwards [finiteL2Coordinates_apply_ae volume (graphTestToLp u) b,
    (graphTest_memLp u).coeFn_toLp,
    (hg.continuous.memLp_of_hasCompactSupport hc).coeFn_toLp] with x hx hy hz
  have hx' : (finiteL2CoordinateIsometry volume (graphTestToLp u) b) x = (u.val x) b :=
    hx.trans (congrArg (fun z : V ↦ z b) hy)
  classical
  by_cases hb : b = a
  · subst b
    have ht : (finiteL2CoordinateIsometry volume (graphTestToLp u) a) x = g x := by
      simpa [u, L, coordinateInjection] using hx'
    simpa [coordinateInjection] using ht.trans hz.symm
  · simpa [coordinateInjection, u, L, hb] using hx'

/-- A compact-test vector tame estimate extends to every natural-order vector
Sobolev input of a supplied bounded L² operator. The proof uses the checked
scalar density/extension theorem on actual operator blocks, with fixed factor
`r²`; it proves output membership. Source: `app:ch_regular_base:eq:fio-input`. -/
theorem graph_vector_bound_of_compactSmooth (T : H →L[ℂ] H)
    (s : ℕ) (t C Hhigh : ℝ) (hC : 0 ≤ C) (hH : 0 ≤ Hhigh)
    (htest : ∀ u : graphTestSpace n r,
      MemVectorFourierSobolev t (T (graphTestToLp u)) ∧
        vectorFourierSobolevNorm t (T (graphTestToLp u)) ≤
          C * (vectorFourierSobolevNorm (s : ℝ) (graphTestToLp u) + Hhigh * ‖graphTestToLp u‖))
    (u : H) (hu : MemVectorFourierSobolev (s : ℝ) u) :
    MemVectorFourierSobolev t (T u) ∧
      vectorFourierSobolevNorm t (T u) ≤ ((r : ℝ) * r * C) *
        (vectorFourierSobolevNorm (s : ℝ) u + Hhigh * ‖u‖) := by
  classical
  let Q := finiteL2CoordinateIsometry (I := Fin r) (volume : Measure E)
  let B : Fin r → Fin r → L² →L[ℂ] L² := fun a b ↦
    (PiLp.proj 2 (fun _ : Fin r ↦ L²) a).comp
      (Q.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (T.comp (graphL2CoordinateInjection b).toContinuousLinearMap))
  have hblock (a b : Fin r) (f : L²) (hf : MemFourierSobolev (s : ℝ) f) :
      MemFourierSobolev t (B a b f) ∧
        fourierSobolevNorm t (B a b f) ≤ C * (fourierSobolevNorm (s : ℝ) f + Hhigh * ‖f‖) := by
    apply fourierSobolev_operator_bound_of_compactSmooth_nat (B a b) s t C Hhigh _ f hf
    intro g hg hc
    obtain ⟨v, hv⟩ := graphL2CoordinateInjection_compactSmooth (n := n) b g hg hc
    have h := htest v
    rw [hv] at h
    refine ⟨h.1 a, ?_⟩
    have hn := h.2
    rw [graphL2CoordinateInjection_sobolevNorm, LinearIsometry.norm_map] at hn
    exact (fourierSobolevNorm_coordinate_le t (Q (T (graphL2CoordinateInjection b
      ((hg.continuous.memLp_of_hasCompactSupport hc).toLp g)))) a).trans hn

  have he : vectorMatrixL2Operator B u = T u := by
    apply Q.injective
    rw [finiteL2CoordinateIsometry_vectorMatrixL2Operator]
    apply PiLp.ext
    intro a
    rw [matrixOperator_apply]
    change ∑ b, (Q (T (graphL2CoordinateInjection b (Q u b)))) a = Q (T u) a
    have hsum : ∑ b, graphL2CoordinateInjection b (Q u b) = u := by
      apply Q.injective
      rw [map_sum]
      change (∑ b, Q (Q.symm (coordinateInjection b (Q u b)))) = Q u
      simp only [LinearIsometryEquiv.apply_symm_apply]
      apply PiLp.ext
      intro b
      have he : (∑ a, coordinateInjection a (Q u a)) b =
          ∑ a, coordinateInjection a (Q u a) b := by
        simpa only [PiLp.proj_apply] using map_sum (PiLp.proj (𝕜 := ℂ) 2 _ b)
          (fun a ↦ coordinateInjection a (Q u a)) Finset.univ
      rw [he, Finset.sum_eq_single b]
      · simp [coordinateInjection]
      · intro c _ hcb
        simp [coordinateInjection, hcb]
      · simp
    calc
      _ = (Q (T (∑ b, graphL2CoordinateInjection b (Q u b)))) a := by
        simp only [map_sum]
        simpa only [PiLp.proj_apply] using
          (map_sum (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ L²) a)
            (fun b ↦ Q (T (graphL2CoordinateInjection b (Q u b)))) Finset.univ).symm
      _ = _ := by rw [hsum]
  have h := vectorMatrixL2Operator_fourierSobolev_bound B (s : ℝ) t C Hhigh hC hH hblock u hu
  simpa only [he, Fintype.card_fin] using h

end JanetCartan.FourierIntegral
