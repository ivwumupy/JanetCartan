module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Vector
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.IntegerDerivatives
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.Iteration

/-!
# Coordinate reconstruction for the graph Sobolev estimate

These are downstream Fourier deductions for `app:ch_regular_base:eq:fio-input`.
In particular, the gain-one criterion assumes actual distributional first
 derivatives and their Sobolev membership, but only L² for the original output.
Its consumer is the order-minus-one assembly in `jc-deduce-fio-strong-sobolev`.
-/

@[expose] public noncomputable section
open MeasureTheory LineDeriv JanetCartan.Pseudodifferential
open scoped SchwartzMap
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- Coordinate projection commutes with the L² distribution embedding in
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem graphL2_coordinate_distribution (u : H) (a : Fin r) (φ : 𝓢(E, ℂ)) :
    ((finiteL2CoordinateIsometry volume u a : L²) : 𝓢'(E, ℂ)) φ =
      ((u : 𝓢'(E, V)) φ) a := by
  simp only [Lp.toTemperedDistribution_apply]
  let L := PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) a
  have hi : Integrable (fun x ↦ φ x • u x) volume :=
    memLp_one_iff_integrable.mp ((φ.memLp 2 volume).smul (Lp.memLp u))
  calc
    _ = ∫ x, L (φ x • u x) := by
      apply integral_congr_ae
      filter_upwards [finiteL2Coordinates_apply_ae volume u a] with x hx
      change φ x • (finiteL2CoordinateIsometry volume u a) x = φ x • (u x) a
      exact congrArg (fun z : ℂ ↦ φ x • z) hx
    _ = _ := L.integral_comp_comm hi

/-- An actual vector weak derivative gives actual scalar weak derivatives,
with the same Lebesgue measure and coordinate normalization, for
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem graphL2_coordinate_derivative {u v : H} {i : Fin n}
    (h : lineDerivOp (EuclideanSpace.single i (1 : ℝ)) (u : 𝓢'(E, V)) =
      (v : 𝓢'(E, V))) (a : Fin r) :
    HasEuclideanL2CoordinateDerivative i
      (finiteL2CoordinateIsometry volume u a) (finiteL2CoordinateIsometry volume v a) := by
  ext φ
  change ((finiteL2CoordinateIsometry volume u a : L²) : 𝓢'(E, ℂ))
    (-lineDerivOp (EuclideanSpace.basisFun (Fin n) ℝ i) φ) = _
  rw [graphL2_coordinate_distribution, graphL2_coordinate_distribution]
  simpa only [EuclideanSpace.basisFun_apply, TemperedDistribution.lineDerivOp_apply_apply] using
    congrArg (fun z : V ↦ z a) (congrArg (fun T : 𝓢'(E, V) ↦ T φ) h)

/-- Scalar reconstruction from the low norm and first derivatives, used in the
vector gain-one deduction of `app:ch_regular_base:eq:fio-input`. No order-`s`
regularity of `u` is assumed. -/
theorem graph_scalar_reconstruction (s : ℕ) (u : L²) (v : Fin n → L²)
    (hv : ∀ i, MemFourierSobolev (s : ℝ) (v i))
    (hd : ∀ i, HasEuclideanL2CoordinateDerivative i u (v i)) :
    MemFourierSobolev ((s : ℝ) + 1) u ∧
      fourierSobolevNorm ((s : ℝ) + 1) u ≤
        ‖u‖ + (s + 1 : ℝ) * ∑ i, fourierSobolevNorm (s : ℝ) (v i) := by
  induction s with
  | zero =>
    simp only [Nat.cast_zero] at hv ⊢
    refine ⟨(memFourierSobolev_zero u).of_coordinateDerivatives (by norm_num) hv hd, ?_⟩
    simpa using fourierSobolevNorm_le_coordinateDerivatives (by norm_num)
      (memFourierSobolev_zero u) hv hd
  | succ s ih =>
    have hle : (s : ℝ) ≤ (↑(s + 1) : ℝ) := by exact_mod_cast Nat.le_succ s
    obtain ⟨hu, hn⟩ := ih (fun i ↦ (hv i).mono hle)
    have hu' : MemFourierSobolev (↑(s + 1) : ℝ) u := by simpa using hu
    refine ⟨hu'.of_coordinateDerivatives (by positivity) hv hd, ?_⟩
    have hn' : fourierSobolevNorm (↑(s + 1) : ℝ) u ≤
        ‖u‖ + (s + 1 : ℝ) * ∑ i, fourierSobolevNorm (↑(s + 1) : ℝ) (v i) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hn.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i _ ↦ fourierSobolevNorm_mono (hv i) hle))
        (show (0 : ℝ) ≤ s + 1 by positivity)))
    calc
      _ ≤ fourierSobolevNorm (↑(s + 1) : ℝ) u +
          ∑ i, fourierSobolevNorm (↑(s + 1) : ℝ) (v i) :=
        fourierSobolevNorm_le_coordinateDerivatives (by positivity) hu' hv hd
      _ ≤ _ := by push_cast at hn' ⊢; nlinarith

/-- Vector reconstruction from actual first coordinate derivatives and the low
L² norm. This closes the Fourier gain-one step after
`app:ch_regular_base:eq:graph-derivative-transfer`; the first derivative identities
are supplied by the parent's first-output construction. -/
theorem graph_vector_reconstruction (s : ℕ) (u : H) (v : Fin n → H)
    (hv : ∀ i, MemVectorFourierSobolev (s : ℝ) (v i))
    (hd : ∀ i, lineDerivOp (EuclideanSpace.single i (1 : ℝ)) (u : 𝓢'(E, V)) =
      (v i : 𝓢'(E, V))) :
    MemVectorFourierSobolev ((s : ℝ) + 1) u ∧
      vectorFourierSobolevNorm ((s : ℝ) + 1) u ≤
        (r : ℝ) * (‖u‖ + (s + 1 : ℝ) * ∑ i, vectorFourierSobolevNorm (s : ℝ) (v i)) := by
  have hc (a : Fin r) := graph_scalar_reconstruction s
    (finiteL2CoordinateIsometry volume u a)
    (fun i ↦ finiteL2CoordinateIsometry volume (v i) a)
    (fun i ↦ hv i a) (fun i ↦ graphL2_coordinate_derivative (hd i) a)
  refine ⟨fun a ↦ (hc a).1, ?_⟩
  calc
    _ ≤ ∑ a, fourierSobolevNorm ((s : ℝ) + 1) (finiteL2CoordinateIsometry volume u a) :=
      matrixFourierSobolevNorm_le_sum _ _
    _ ≤ ∑ _a : Fin r, (‖u‖ + (s + 1 : ℝ) *
        ∑ i, vectorFourierSobolevNorm (s : ℝ) (v i)) := by
      apply Finset.sum_le_sum
      intro a _
      apply (hc a).2.trans
      apply add_le_add
      · simpa using PiLp.norm_apply_le (finiteL2CoordinateIsometry volume u) a
      · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ ↦
          fourierSobolevNorm_coordinate_le _ _ a)) (by positivity)
    _ = _ := by simp [mul_add]

end JanetCartan.FourierIntegral
