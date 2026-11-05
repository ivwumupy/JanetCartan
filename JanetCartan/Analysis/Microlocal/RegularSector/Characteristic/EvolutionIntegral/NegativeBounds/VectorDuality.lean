module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PdoRealization.Duality
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FourierAssembly.Extension

/-!
# Finite vector duality for the direct retarded factors

The scalar weighted Fourier duality proof is applied to the actual coordinate
blocks of a vector L² operator. The only loss is the fixed fiber factor `q²`.
Consumer: the primitive retarded specialization of
`app:ch_regular_base:eq:negative-duality`, including its `H⁻¹ → L²` endpoint.
All data here are actual Euclidean Lebesgue L² classes, not a distribution
completion of the negative Sobolev space.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ComplexInnerProductSpace
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral
open Pseudodifferential FourierIntegral AmplitudeBound PdoRealization
variable {n q : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin q)
local notation "L²" => Lp ℂ 2 (volume : Measure E)
local notation "H₂" => Lp V 2 (volume : Measure E)

private theorem injection_mem {s : ℝ} (i : Fin q) (u : L²)
    (hu : MemFourierSobolev s u) :
    MemVectorFourierSobolev s (graphL2CoordinateInjection i u) := by
  classical
  change ∀ j, MemFourierSobolev s
    (finiteL2CoordinateIsometry volume ((finiteL2CoordinateIsometry volume).symm
      (coordinateInjection i u)) j)
  rw [LinearIsometryEquiv.apply_symm_apply]
  intro j
  by_cases hj : j = i
  · subst j
    simpa [coordinateInjection] using hu
  · simpa [coordinateInjection, hj] using (show MemFourierSobolev (d := n) s 0 from by
      have he : weightedL2Fourier (d := n) s 0 = 0 := by
        funext x
        simp [weightedL2Fourier]
      simp [MemFourierSobolev, he])

private theorem injection_adjoint_apply (i : Fin q) (u : H₂) :
    (graphL2CoordinateInjection i).toContinuousLinearMap.adjoint u =
      finiteL2CoordinateIsometry volume u i := by
  classical
  apply ext_inner_left ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [← finiteL2Coordinates_inner]
  change inner ℂ (finiteL2CoordinateIsometry volume
    ((finiteL2CoordinateIsometry volume).symm (coordinateInjection i g)))
      (finiteL2CoordinateIsometry volume u) = _
  rw [LinearIsometryEquiv.apply_symm_apply, PiLp.inner_apply]
  rw [Finset.sum_eq_single i]
  · simp [coordinateInjection]
  · intro j _ hji
    simp [coordinateInjection, hji]
  · simp

/-- Positive tame bounds for the literal adjoint imply negative bounds for
the same finite vector operator. This uses the scalar theorem
`negativeFourierSobolev_tame_bound_of_adjoint`, with fixed factor `q²` and
one linear high quantity. Source: `app:ch_regular_base:eq:negative-duality`.
Consumer: `retarded_negative_integer_bounds_of_positive`.
-/
theorem negativeVectorFourierSobolev_tame_bound_of_adjoint {s t C H : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (T : H₂ →L[ℂ] H₂)
    (hT : ∀ g, MemVectorFourierSobolev s g →
      MemVectorFourierSobolev t (T.adjoint g) ∧
        vectorFourierSobolevNorm t (T.adjoint g) ≤
          C * (vectorFourierSobolevNorm s g + H * ‖g‖))
    (f : H₂) :
    MemVectorFourierSobolev (-s) (T f) ∧
      vectorFourierSobolevNorm (-s) (T f) ≤
        ((q : ℝ) * q * C) * (1 + H) * vectorFourierSobolevNorm (-t) f := by
  classical
  let Q := finiteL2CoordinateIsometry (I := Fin q) (volume : Measure E)
  let B : Fin q → Fin q → L² →L[ℂ] L² := fun i j ↦
    (graphL2CoordinateInjection i).toContinuousLinearMap.adjoint.comp
      (T.comp (graphL2CoordinateInjection j).toContinuousLinearMap)
  have happ (i j : Fin q) (g : L²) :
      B i j g = Q (T (graphL2CoordinateInjection j g)) i :=
    injection_adjoint_apply i _
  have hadj (i j : Fin q) (g : L²) :
      (B i j).adjoint g = Q (T.adjoint (graphL2CoordinateInjection i g)) j := by
    simp only [B, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      injection_adjoint_apply]
    rfl
  have hblock (i j : Fin q) (g : L²) (_hg : MemFourierSobolev (-t) g) :
      MemFourierSobolev (-s) (B i j g) ∧
        fourierSobolevNorm (-s) (B i j g) ≤
          (C * (1 + H)) * (fourierSobolevNorm (-t) g + 0 * ‖g‖) := by
    have hp (v : L²) (hv : MemFourierSobolev s v) :
        MemFourierSobolev t ((B i j).adjoint v) ∧
          fourierSobolevNorm t ((B i j).adjoint v) ≤
            C * (fourierSobolevNorm s v + H * ‖v‖) := by
      rw [hadj]
      have h := hT _ (injection_mem i v hv)
      refine ⟨h.1 j, ?_⟩
      have hn := (fourierSobolevNorm_coordinate_le t
        (Q (T.adjoint (graphL2CoordinateInjection i v))) j).trans h.2
      simpa only [graphL2CoordinateInjection_sobolevNorm, LinearIsometry.norm_map] using hn
    simpa only [zero_mul, add_zero] using
      negativeFourierSobolev_tame_bound_of_adjoint hs ht hC hH (B i j) hp g
  have he : vectorMatrixL2Operator B f = T f := by
    apply Q.injective
    rw [finiteL2CoordinateIsometry_vectorMatrixL2Operator]
    apply PiLp.ext
    intro i
    rw [matrixOperator_apply]
    simp only [happ]
    have hsum : ∑ j, graphL2CoordinateInjection j (Q f j) = f := by
      apply Q.injective
      rw [map_sum]
      change (∑ j, Q (Q.symm (coordinateInjection j (Q f j)))) = Q f
      simp only [LinearIsometryEquiv.apply_symm_apply]
      apply PiLp.ext
      intro j
      have he : (∑ i, coordinateInjection i (Q f i)) j =
          ∑ i, coordinateInjection i (Q f i) j := by
        simpa only [PiLp.proj_apply] using map_sum (PiLp.proj (𝕜 := ℂ) 2 _ j)
          (fun i ↦ coordinateInjection i (Q f i)) Finset.univ
      rw [he, Finset.sum_eq_single j]
      · simp [coordinateInjection]
      · intro k _ hkj
        simp [coordinateInjection, hkj]
      · simp
    calc
      _ = (Q (T (∑ j, graphL2CoordinateInjection j (Q f j)))) i := by
        simp only [map_sum]
        simpa only [PiLp.proj_apply] using
          (map_sum (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin q ↦ L²) i)
            (fun j ↦ Q (T (graphL2CoordinateInjection j (Q f j)))) Finset.univ).symm
      _ = _ := by rw [hsum]
  have hf : MemVectorFourierSobolev (-t) f :=
    fun _ ↦ memFourierSobolev_of_nonpos (neg_nonpos.mpr ht) _
  have h := vectorMatrixL2Operator_fourierSobolev_bound B (-t) (-s)
    (C * (1 + H)) 0 (by positivity) le_rfl hblock f hf
  simpa only [he, Fintype.card_fin, zero_mul, add_zero, mul_assoc] using h

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral
