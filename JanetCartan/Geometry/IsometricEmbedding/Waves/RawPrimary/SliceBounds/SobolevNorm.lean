module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.Realization
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.PhysicalDerivatives

/-!
# From the actual directional realizations to the full weak-jet norm

The consumer is the primitive-input Sobolev slice theorem for
`app:ch_waves:eq:individual-raw-slice`. Only a dimension-and-order factor is
introduced when the Cartesian directional realizations control the Fréchet
jet norm. The original wide-input and dyadic constants are unchanged.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.RawPrimary.SliceBounds

variable {n j s : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem norm_rawSliceJet_le_basis_sum (A : (Euclidean n) [×j]→L[ℝ] F) :
    ‖A‖ ≤ ∑ a : Fin j → Fin n, ‖A (fun k ↦ EuclideanSpace.basisFun (Fin n) ℝ (a k))‖ := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  intro v
  have hv : v = fun k ↦ ∑ i, b.repr (v k) i • b i := by
    funext k
    exact (b.sum_repr (v k)).symm
  calc
    ‖A v‖ = ‖∑ a : Fin j → Fin n, (∏ k, b.repr (v k) (a k)) •
        A (fun k ↦ b (a k))‖ := by
      conv_lhs => rw [hv, A.map_sum]
      simp only [A.map_smul_univ]
    _ ≤ ∑ a : Fin j → Fin n, ‖(∏ k, b.repr (v k) (a k)) •
        A (fun k ↦ b (a k))‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin j → Fin n, ‖A (fun k ↦ b (a k))‖ * ∏ k, ‖v k‖ := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_smul, norm_prod, mul_comm]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
      intro k _
      exact (PiLp.norm_apply_le (b.repr (v k)) (a k)).trans_eq (b.repr.norm_map _)
    _ = _ := (Finset.sum_mul ..).symm

/-- Actual Cartesian L² realizations bound the full Fréchet L² jet. Used to
assemble the physical Sobolev bound from the constructed derivative channels,
without replacing the Frobenius norm by a component maximum
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem eLpNorm_rawSliceJet_le_cartesian_realizations
    (J : Euclidean n → (Euclidean n) [×j]→L[ℝ] F) (hJ : MemLp J 2 volume)
    (T : (Fin j → Fin n) → Lp F 2 (volume : Measure (Euclidean n)))
    (hT : ∀ a, T a =ᵐ[volume] fun x ↦
      J x (fun k ↦ EuclideanSpace.basisFun (Fin n) ℝ (a k))) :
    (eLpNorm J 2 volume).toReal ≤ ∑ a, ‖T a‖ := by
  classical
  let f (a : Fin j → Fin n) (x : Euclidean n) :=
    J x (fun k ↦ EuclideanSpace.basisFun (Fin n) ℝ (a k))
  have hf (a) : MemLp (f a) 2 volume := (memLp_congr_ae (hT a)).mp (Lp.memLp (T a))
  have hsum : MemLp (fun x ↦ ∑ a, ‖f a x‖) 2 volume :=
    memLp_finsetSum Finset.univ (fun a _ ↦ (hf a).norm)
  have hmono : eLpNorm J 2 volume ≤ eLpNorm (fun x ↦ ∑ a, ‖f a x‖) 2 volume := by
    apply eLpNorm_mono_ae hJ.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
    exact norm_rawSliceJet_le_basis_sum (J x)
  have htriangle := eLpNorm_sum_le (μ := (volume : Measure (Euclidean n))) (p := 2)
    (f := fun a x ↦ ‖f a x‖) (s := Finset.univ) (by norm_num)
  have ht := ENNReal.toReal_mono
    (show (∑ a, eLpNorm (fun x ↦ ‖f a x‖) 2 volume) ≠ ⊤ from
      ne_of_lt (ENNReal.sum_lt_top.mpr fun a _ ↦ (hf a).norm.eLpNorm_lt_top)) htriangle
  rw [ENNReal.toReal_sum (fun a _ ↦ (hf a).norm.eLpNorm_ne_top)] at ht
  calc
    (eLpNorm J 2 volume).toReal ≤
        (eLpNorm (fun x ↦ ∑ a, ‖f a x‖) 2 volume).toReal :=
      ENNReal.toReal_mono hsum.eLpNorm_ne_top hmono
    _ ≤ ∑ a, (eLpNorm (fun x ↦ ‖f a x‖) 2 volume).toReal := by
      have heq : (∑ a, fun x ↦ ‖f a x‖) = (fun x ↦ ∑ a, ‖f a x‖) := by
        funext x
        exact Finset.sum_apply x _ _
      simpa only [heq] using ht
    _ = ∑ a, ‖T a‖ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [eLpNorm_norm (f a) (hf a).aestronglyMeasurable, ← eLpNorm_congr_ae (hT a)]
      rfl

/-- The full weak-jet norm has the sharp frequency exponent once the actual
Cartesian realizations have been constructed. This finite-dimensional assembly
is instantiated by the primitive raw slice constructor, and is not an analytic
premise of that constructor (`app:ch_waves:eq:individual-raw-slice`). -/
theorem rawSliceExtension_jetNorm_le
    {Q : Set (Euclidean n)} {u : LocalSobolev.LocalL2 Q F}
    (e : LocalSobolev.SobolevExtension Q s u)
    (T : (j : ℕ) → (Fin j → Fin n) → Lp F 2 (volume : Measure (Euclidean n)))
    (hT : ∀ j ≤ s, ∀ a, T j a =ᵐ[volume] fun x ↦
      e.jet j x (fun k ↦ EuclideanSpace.basisFun (Fin n) ℝ (a k)))
    {D : ℕ → ℝ} (hD : ∀ j, 0 ≤ D j) {K R : ℝ} (hK : 1 ≤ K) (hR : 0 ≤ R)
    (hbound : ∀ j ≤ s, ∀ a, ‖T j a‖ ≤ D j * K ^ ((j : ℝ) + 1 / 2) * R) :
    e.jetNorm ≤ (∑ j ∈ Finset.range (s + 1), (n : ℝ) ^ j * D j) *
      K ^ ((s : ℝ) + 1 / 2) * R := by
  classical
  unfold LocalSobolev.SobolevExtension.jetNorm
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjs : j ≤ s := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  calc
    (eLpNorm (e.jet j) 2 volume).toReal ≤ ∑ a, ‖T j a‖ :=
      eLpNorm_rawSliceJet_le_cartesian_realizations _ (e.memLp_jet j hjs) (T j) (hT j hjs)
    _ ≤ ∑ _a : Fin j → Fin n, D j * K ^ ((s : ℝ) + 1 / 2) * R := by
      apply Finset.sum_le_sum
      intro a _
      apply (hbound j hjs a).trans
      apply mul_le_mul_of_nonneg_right _ hR
      apply mul_le_mul_of_nonneg_left _ (hD j)
      exact Real.rpow_le_rpow_of_exponent_le hK (add_le_add_left (by exact_mod_cast hjs) _)
    _ = (n : ℝ) ^ j * D j * K ^ ((s : ℝ) + 1 / 2) * R := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow]
      ring

end JanetCartan.RawPrimary.SliceBounds
