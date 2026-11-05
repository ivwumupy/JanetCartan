module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FourierAssembly.Extension
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.FiniteFiber.Bounds

/-!
# Density extension preserving the annular weighted profile

Compact smooth density in Hˢ, scalar Fourier closedness, and the existing
finite-fiber isometry extend the exact weighted estimate in
`app:ch_response:eq:direct-envelope-profile`. No density or output membership
is an extra input in the all-data annular assembly.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
open FourierIntegral Pseudodifferential AmplitudeBound
open IsometricEmbedding.Response.NearCarrier
open IsometricEmbedding.Response.NearCarrier.FiniteFiber
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- The weighted finite sum passes to every scalar Hˢ input by actual compact
smooth approximation. Consumer: the finite-fiber extension of
`app:ch_response:eq:direct-envelope-profile`. -/
theorem annular_scalar_weighted_bound_of_compactSmooth
    (T : L² →L[ℂ] L²) (s : ℕ) (t C L : ℝ)
    (htest : ∀ (g : E → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g),
      let v := (hg.continuous.memLp_of_hasCompactSupport hc).toLp g
      MemFourierSobolev t (T v) ∧
        fourierSobolevNorm t (T v) ≤ C * spatialEnvelopeSobolevProfile s L v)
    (u : L²) (hu : MemFourierSobolev (s : ℝ) u) :
    MemFourierSobolev t (T u) ∧
      fourierSobolevNorm t (T u) ≤ C * spatialEnvelopeSobolevProfile s L u := by
  obtain ⟨g, hg, hc, hm, hlim, hL2⟩ := exists_compactSmooth_fourierSobolev_nat_tendsto s u hu
  let v : ℕ → L² := fun k => ((hg k).continuous.memLp_of_hasCompactSupport (hc k)).toLp (g k)
  have hnorm (j : ℕ) (hj : j ∈ Finset.range (s + 1)) :
      Tendsto (fun k => fourierSobolevNorm (j : ℝ) (v k)) atTop
        (𝓝 (fourierSobolevNorm (j : ℝ) u)) := by
    have hjs : (j : ℝ) ≤ s := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    apply tendsto_fourierSobolevNorm_of_sub (fun k => (hm k).mono hjs) (hu.mono hjs)
    exact squeeze_zero (fun _ => fourierSobolevNorm_nonneg _ _)
      (fun k => fourierSobolevNorm_mono ((hm k).sub hu) hjs) hlim
  apply memFourierSobolev_and_norm_le_of_tendsto t
    (T.continuous.continuousAt.tendsto.comp hL2) (fun k => (htest (g k) (hg k) (hc k)).1)
    ((tendsto_finsetSum (Finset.range (s + 1))
      (fun j hj => (hnorm j hj).const_mul (L ^ (s - j)))).const_mul C)
  exact fun k => (htest (g k) (hg k) (hc k)).2

/-- Every vector compact-test weighted estimate extends to all Hˢ inputs
of the SAME bounded L² operator. The fixed factor `r²` comes only from
finite coordinate summation. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem annular_vector_weighted_bound_of_compactSmooth
    (T : H →L[ℂ] H) (s : ℕ) (C L : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (htest : ∀ u : graphTestSpace n r,
      MemVectorFourierSobolev (s : ℝ) (T (graphTestToLp u)) ∧
        vectorFourierSobolevNorm (s : ℝ) (T (graphTestToLp u)) ≤
          C * vectorSpatialEnvelopeProfile s L (graphTestToLp u))
    (u : H) (hu : MemVectorFourierSobolev (s : ℝ) u) :
    MemVectorFourierSobolev (s : ℝ) (T u) ∧
      vectorFourierSobolevNorm (s : ℝ) (T u) ≤
        ((r : ℝ) * r * C) * vectorSpatialEnvelopeProfile s L u := by
  classical
  let Q := finiteL2CoordinateIsometry (I := Fin r) (volume : Measure E)
  let B : Fin r → Fin r → L² →L[ℂ] L² := fun a b =>
    (PiLp.proj 2 (fun _ : Fin r => L²) a).comp
      (Q.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (T.comp (graphL2CoordinateInjection b).toContinuousLinearMap))
  have hblock (a b : Fin r) (f : L²) (hf : MemFourierSobolev (s : ℝ) f) :
      MemFourierSobolev (s : ℝ) (B a b f) ∧
        fourierSobolevNorm (s : ℝ) (B a b f) ≤ C * spatialEnvelopeSobolevProfile s L f := by
    apply annular_scalar_weighted_bound_of_compactSmooth (B a b) s s C L _ f hf
    intro g hg hc
    obtain ⟨v, hv⟩ := graphL2CoordinateInjection_compactSmooth (n := n) b g hg hc
    have h := htest v
    rw [hv] at h
    refine ⟨h.1 a, ?_⟩
    have hn := h.2
    simp only [vectorSpatialEnvelopeProfile, graphL2CoordinateInjection_sobolevNorm] at hn
    exact (fourierSobolevNorm_coordinate_le (s : ℝ) (Q (T (graphL2CoordinateInjection b
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
          (fun a => coordinateInjection a (Q u a)) Finset.univ
      rw [he, Finset.sum_eq_single b]
      · simp [coordinateInjection]
      · intro c _ hcb
        simp [coordinateInjection, hcb]
      · simp
    calc
      _ = (Q (T (∑ b, graphL2CoordinateInjection b (Q u b)))) a := by
        simp only [map_sum]
        simpa only [PiLp.proj_apply] using
          (map_sum (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r => L²) a)
            (fun b => Q (T (graphL2CoordinateInjection b (Q u b)))) Finset.univ).symm
      _ = _ := by rw [hsum]
  have h := vectorMatrix_weighted_bound B s hL hC hblock u hu
  simpa only [he, Fintype.card_fin, vectorSpatialEnvelopeProfile] using h

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
