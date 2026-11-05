module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedOperator
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.PhysicalOutput

/-!
# All-order transfer of the differentiated raw realization

For `app:ch_waves:eq:individual-raw-slice`, physical unit directions are
contractive in the retained adapted product norm. The literal all-order chain
rule and actual measure/Frobenius isometry transfer the constructed derivative
operators to derivatives of the SAME physical field.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.SliceBounds
open ActualCarriers.FrozenPhaseReference SingleChannel

variable {n m s : ℕ} {ξ : Euclidean n} (a : AdaptedSection ξ)

/-- A physical unit direction is a unit direction in the actual adapted
product norm; no dimension-dependent rescaling is needed in the branch input
(`app:ch_seed:prop:seed-phase-charts`, `app:ch_waves:eq:individual-raw-slice`). -/
theorem norm_adaptedPhysicalCoordinates_symm_le (x : Euclidean n) :
    ‖(adaptedPhysicalCoordinates a).symm x‖ ≤ ‖x‖ := by
  change ‖WithLp.ofLp ((adaptedSpacetimeEquiv a).symm x)‖ ≤ ‖x‖
  rw [Prod.norm_def, max_le_iff]
  exact ⟨(WithLp.norm_fst_le ℝ _).trans_eq ((adaptedSpacetimeEquiv a).symm.norm_map x),
    (WithLp.norm_snd_le ℝ _).trans_eq ((adaptedSpacetimeEquiv a).symm.norm_map x)⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- All mixed physical derivatives, including time, transform by the actual
linear coordinate map. This identity holds without differentiability premises
because the coordinate map is a continuous linear equivalence
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem iteratedFDeriv_adaptedPhysicalCoordinates_directions
    (f : Euclidean n → F) (q : ℝ × Euclidean (n - 1)) (v : Fin s → Euclidean n) :
    iteratedFDeriv ℝ s (f ∘ adaptedPhysicalCoordinates a) q
        (fun i ↦ (adaptedPhysicalCoordinates a).symm (v i)) =
      iteratedFDeriv ℝ s f (adaptedPhysicalCoordinates a q) v := by
  have h := (NullTransport.ActualFlow.adaptedCoordinates a).symm.iteratedFDerivWithin_comp_right
    f uniqueDiffOn_univ (x := q) (Set.mem_univ _) s
  simp only [preimage_univ, iteratedFDerivWithin_univ] at h
  change iteratedFDeriv ℝ s (f ∘ (NullTransport.ActualFlow.adaptedCoordinates a).symm) q
    (fun i ↦ NullTransport.ActualFlow.adaptedCoordinates a (v i)) = _
  rw [h]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  rfl

/-- The same chain rule commutes with Frobenius component flattening.
This connects the Euclidean-vector derivative output to the physical matrix
jet (`app:ch_waves:eq:individual-raw-slice`). -/
theorem iteratedFDeriv_matrixChannel_adapted_directions
    (f : Euclidean n → Matrix (Fin m) (Fin n) ℂ)
    (q : ℝ × Euclidean (n - 1)) (v : Fin s → Euclidean n) :
    iteratedFDeriv ℝ s (fun y ↦ matrixChannelEquiv m n (f (adaptedPhysicalCoordinates a y))) q
        (fun i ↦ (adaptedPhysicalCoordinates a).symm (v i)) =
      matrixChannelEquiv m n (iteratedFDeriv ℝ s f (adaptedPhysicalCoordinates a q) v) := by
  let e := (matrixChannelEquiv m n).toContinuousLinearEquiv
  let eR : Matrix (Fin m) (Fin n) ℂ ≃L[ℝ] EuclideanSpace ℂ (Fin (m * n)) :=
    { toLinearEquiv := e.toLinearEquiv.restrictScalars ℝ
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  change iteratedFDeriv ℝ s (eR ∘ (f ∘ adaptedPhysicalCoordinates a)) q _ = _
  rw [eR.iteratedFDeriv_comp_left]
  change eR (iteratedFDeriv ℝ s (f ∘ adaptedPhysicalCoordinates a) q _) = _
  rw [iteratedFDeriv_adaptedPhysicalCoordinates_directions]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Transfer the actual directional derivative operator supplied by
`exists_rawSliceDifferentiatedOperator` to the physical matrix derivative.
The only premise about that operator is its proved representative identity;
the output is the literal unnormalized derivative of the SAME physical field.
The Fourier scalar is undone exactly once, using the existing
`physicalRawSliceOperator` (`app:ch_waves:eq:individual-raw-slice`). -/
theorem physicalRawSliceOperator_coeFn_derivative
    (T : E →L[ℂ] Lp (EuclideanSpace ℂ (Fin (m * n))) 2
      (volume : Measure (ℝ × Euclidean (n - 1))))
    (f : Euclidean n → Matrix (Fin m) (Fin n) ℂ) (hf : ContDiff ℝ ∞ f)
    (u : E) (v : Fin s → Euclidean n)
    (hT : T u =ᵐ[volume] fun q ↦ iteratedFDeriv ℝ s
      (fun y ↦ (2 * Real.pi) ^ (-(n : ℝ) / 2) •
        matrixChannelEquiv m n (f (adaptedPhysicalCoordinates a y))) q
          (fun i ↦ (adaptedPhysicalCoordinates a).symm (v i))) :
    physicalRawSliceOperator a T u =ᵐ[volume] fun x ↦ iteratedFDeriv ℝ s f x v := by
  let g : (ℝ × Euclidean (n - 1)) → EuclideanSpace ℂ (Fin (m * n)) :=
    fun y ↦ matrixChannelEquiv m n (f (adaptedPhysicalCoordinates a y))
  have hg : ContDiff ℝ ∞ g := by
    have hcomp : ContDiff ℝ ∞ (f ∘ (NullTransport.ActualFlow.adaptedCoordinates a).symm) :=
      hf.comp (NullTransport.ActualFlow.adaptedCoordinates a).symm.contDiff
    exact ((matrixChannelEquiv m n).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp hcomp
  have hT' : T u =ᵐ[volume] fun q ↦ (2 * Real.pi) ^ (-(n : ℝ) / 2) •
      matrixChannelEquiv m n (iteratedFDeriv ℝ s f (adaptedPhysicalCoordinates a q) v) := by
    refine hT.trans (Filter.Eventually.of_forall ?_)
    intro q
    change iteratedFDeriv ℝ s (fun y ↦ (2 * Real.pi) ^ (-(n : ℝ) / 2) • g y) q _ = _
    rw [iteratedFDeriv_const_smul_apply' (hg.contDiffAt.of_le (by simp)), smul_apply]
    congr 1
    exact iteratedFDeriv_matrixChannel_adapted_directions a f q v
  have hc : (2 * Real.pi) ^ ((n : ℝ) / 2) * (2 * Real.pi) ^ (-(n : ℝ) / 2) = 1 := by
    rw [neg_div, Real.rpow_neg (by positivity)]
    exact mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _))
  change ((((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ) • physicalMatrixL2Equiv a m (T u)) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_smul (((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ)
      (physicalMatrixL2Equiv a m (T u)), physicalMatrixL2Equiv_coeFn a m (T u),
    (adaptedPhysicalCoordinates_symm_measurePreserving a).quasiMeasurePreserving.ae hT']
    with x hx hy hz
  rw [hx]
  change (((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ) • physicalMatrixL2Equiv a m (T u) x = _
  rw [hy, hz, Complex.coe_smul]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) ((2 * Real.pi) ^ (-(n : ℝ) / 2)), map_smul]
  simp only [LinearIsometryEquiv.symm_apply_apply, MeasurableEquiv.apply_symm_apply]
  rw [← RCLike.real_smul_eq_coe_smul (K := ℂ) ((2 * Real.pi) ^ (-(n : ℝ) / 2)),
    smul_smul, hc, one_smul]

end JanetCartan.RawPrimary.SliceBounds
