module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorEnvelope.Estimates
public import JanetCartan.Analysis.Operator.GradedInverse.Scale

/-!
# The vector Fourier Sobolev graded scale

The adapter used by `HasEnvelopeProfile` and `completeComplement_observations`
in `app:ch_response:thm:response-literal-transfer`. Its base is the original
Euclidean vector L² space, its levels are exactly `MemVectorFourierSobolev`,
and its norms on members are exactly `vectorFourierSobolevNorm`.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open JanetCartan.Pseudodifferential
namespace JanetCartan.ResponseTransfer.Complement
variable {d : ℕ} {I : Type*} [Fintype I]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "VL2" => Lp (EuclideanSpace ℂ I) 2 (volume : Measure E)
local notation "L2" => Lp ℂ 2 (volume : Measure E)

private theorem weightedL2Fourier_real_smul (s c : ℝ) (f : L2) :
    weightedL2Fourier s (c • f) =ᵐ[volume] c • weightedL2Fourier s f := by
  have h : 𝓕 (c • f) = c • 𝓕 f :=
    map_smul ((fourierCLM ℂ L2).restrictScalars ℝ) c f
  filter_upwards [Lp.coeFn_smul c (𝓕 f)] with ξ hξ
  simp only [weightedL2Fourier, h, hξ, Pi.smul_apply]
  exact smul_comm _ _ _

private theorem coordinate_real_smul (c : ℝ) (f : VL2) (i : I) :
    finiteL2CoordinateIsometry volume (c • f) i =
      c • finiteL2CoordinateIsometry volume f i := by
  have h := LinearMapClass.map_smul_of_tower (finiteL2CoordinateIsometry volume) c f
  exact congrArg (fun g ↦ g i) h

/-- The exact Sobolev subspace at a real order, used to build the natural-order
scale for `app:ch_response:thm:response-literal-transfer`. -/
def vectorFourierSobolevLevel (s : ℝ) : Submodule ℝ VL2 where
  carrier := {f | MemVectorFourierSobolev s f}
  zero_mem' := by
    intro i
    simp only [map_zero, PiLp.zero_apply]
    have hz : weightedL2Fourier (d := d) s 0 = 0 := by
      funext ξ
      simp [weightedL2Fourier]
    change MemLp (weightedL2Fourier s 0) 2 volume
    rw [hz]
    exact MemLp.zero
  add_mem' := by
    intro f g hf hg i
    simpa only [map_add, PiLp.add_apply] using (hf i).add (hg i)
  smul_mem' := by
    intro c f hf i
    rw [coordinate_real_smul]
    exact ((hf i).const_smul c).ae_eq (weightedL2Fourier_real_smul s c _).symm

/-- Each member's weighted coordinate is an actual L² function, supplying the
weighted linear realization in `app:ch_response:thm:response-literal-transfer`. -/
theorem vectorFourierSobolevLevel_coordinate_mem (s : ℝ)
    (f : vectorFourierSobolevLevel (d := d) (I := I) s) (i : I) :
    MemLp (weightedL2Fourier s (finiteL2CoordinateIsometry volume f.val i)) 2 volume :=
  f.property i

/-- Weighted Fourier coordinates of an actual member of a Sobolev level.
Their Hilbert norm supplies the scale seminorm without additional analytic
assumptions (`app:ch_response:thm:response-literal-transfer`). -/
def vectorWeightedFourier (s : ℝ) :
    vectorFourierSobolevLevel (d := d) (I := I) s →ₗ[ℝ]
      PiLp 2 (fun _ : I ↦ L2) where
  toFun f := WithLp.toLp 2 (fun i ↦ (vectorFourierSobolevLevel_coordinate_mem s f i).toLp _)
  map_add' f g := by
    apply PiLp.ext
    intro i
    change (vectorFourierSobolevLevel_coordinate_mem s (f + g) i).toLp _ =
      (vectorFourierSobolevLevel_coordinate_mem s f i).toLp _ + (vectorFourierSobolevLevel_coordinate_mem s g i).toLp _
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    simpa only [Submodule.coe_add, map_add, PiLp.add_apply, Pi.add_def] using
      weightedL2Fourier_add_ae s (finiteL2CoordinateIsometry volume f.val i)
        (finiteL2CoordinateIsometry volume g.val i)
  map_smul' c f := by
    apply PiLp.ext
    intro i
    change (vectorFourierSobolevLevel_coordinate_mem s (c • f) i).toLp _ = c • (vectorFourierSobolevLevel_coordinate_mem s f i).toLp _
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    simpa only [Submodule.coe_smul, coordinate_real_smul] using
      weightedL2Fourier_real_smul s c (finiteL2CoordinateIsometry volume f.val i)

/-- Exact weighted-coordinate norm, consumed by the scale adapter for
`app:ch_response:thm:response-literal-transfer`. -/
theorem norm_vectorWeightedFourier (s : ℝ)
    (f : vectorFourierSobolevLevel (d := d) (I := I) s) :
    ‖vectorWeightedFourier s f‖ = vectorFourierSobolevNorm s f.val := by
  have hsq : ‖vectorWeightedFourier s f‖ ^ 2 = vectorFourierSobolevNorm s f.val ^ 2 := by
    rw [vectorFourierSobolevNorm, matrixFourierSobolevNorm_sq, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro i _
    change ‖(vectorFourierSobolevLevel_coordinate_mem s f i).toLp _‖ ^ 2 = _
    rw [Lp.norm_toLp]
    rfl
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Monotonicity of the actual vector Sobolev norms, required by the graded
scale in `app:ch_response:thm:response-literal-transfer`. -/
theorem vectorFourierSobolevNorm_mono {s t : ℝ} {f : VL2}
    (hf : MemVectorFourierSobolev t f) (hst : s ≤ t) :
    vectorFourierSobolevNorm s f ≤ vectorFourierSobolevNorm t f := by
  simpa only [one_mul] using
    vectorFourierSobolevNorm_le_of_coordinate_bounds zero_le_one f f
      (fun i ↦ by simpa only [one_mul] using fourierSobolevNorm_mono (hf i) hst)

/-- The concrete scale on the SAME Euclidean vector L² space used by the
literal forward/reverse complement operators. This is the input adapter for
`HasEnvelopeProfile` and `completeComplement_observations`
(`app:ch_response:thm:response-literal-transfer`). -/
def vectorFourierSobolevScale : GradedScale VL2 where
  level s := vectorFourierSobolevLevel s
  level_zero := by
    ext f
    change MemVectorFourierSobolev (0 : ℕ) f ↔ True
    simp only [Nat.cast_zero, iff_true]
    exact fun i ↦ memFourierSobolev_zero _
  antitone_level := by
    intro s t h f hf i
    exact (hf i).mono (by exact_mod_cast h)
  seminorm s := (normSeminorm ℝ (PiLp 2 (fun _ : I ↦ L2))).comp (vectorWeightedFourier s)
  seminorm_zero f := by
    change ‖vectorWeightedFourier (0 : ℕ) f‖ = ‖f.val‖
    simp only [norm_vectorWeightedFourier, Nat.cast_zero, vectorFourierSobolevNorm_zero]
  monotone_seminorm := by
    intro s t h f
    change ‖vectorWeightedFourier s
      ⟨f.val, fun i ↦ (f.property i).mono (by exact_mod_cast h)⟩‖ ≤
        ‖vectorWeightedFourier t f‖
    rw [norm_vectorWeightedFourier, norm_vectorWeightedFourier]
    exact vectorFourierSobolevNorm_mono f.property (by exact_mod_cast h)

/-- The levels are exactly the existing Fourier Sobolev memberships, for
`app:ch_response:thm:response-literal-transfer`. -/
@[simp] theorem mem_vectorFourierSobolevScale (s : ℕ) (f : VL2) :
    f ∈ (vectorFourierSobolevScale (d := d) (I := I)).level s ↔
      MemVectorFourierSobolev s f := Iff.rfl

/-- Exact equality of scale and Fourier norms on members, as required when
instantiating `HasEnvelopeProfile` and the complement assembly
(`app:ch_response:thm:response-literal-transfer`). -/
theorem vectorFourierSobolevScale_gradeNorm (s : ℕ) {f : VL2}
    (hf : MemVectorFourierSobolev s f) :
    (vectorFourierSobolevScale (d := d) (I := I)).gradeNorm s f =
      vectorFourierSobolevNorm s f := by
  rw [(vectorFourierSobolevScale (d := d) (I := I)).gradeNorm_eq hf]
  exact norm_vectorWeightedFourier s ⟨f, hf⟩

end JanetCartan.ResponseTransfer.Complement
