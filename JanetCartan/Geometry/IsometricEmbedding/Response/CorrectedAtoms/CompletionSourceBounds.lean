module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.FixedSolver
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.JetComposition
public import JanetCartan.Analysis.ContDiff.Norm.Products

/-!
# Homogeneous source estimate for canonical completion

The fixed ambient response uses the actual tangent lift and canonical normal
inverse of the supplied immersion. The first-order formula is linear in the
covector jet and tensor datum, including every Christoffel term. Its smooth
coefficient field gives a homogeneous finite source bound with one derivative
on the covector. This closes the completion step for the SAME fixed inverse
in `app:ch_response:eq:response-full-map`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CorrectedAtoms
open AmbientResponse

private abbrev CompletionData (n : ℕ) :=
  Euclidean n × ((Euclidean n →L[ℝ] Euclidean n) × MetricTensor n)

/-- The literal zeroth/first-order coefficient map of
`app:ch_response:eq:response-full-map`; internal to its source bound. -/
private def completionJetOperator {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) : CompletionData n →L[ℝ] Euclidean N :=
  LinearMap.toContinuousLinearMap {
    toFun z := (∑ i, ∑ j, ((inducedMetric F x)⁻¹ i j * z.1 j) • partialDeriv F x i) +
      canonicalNormalCompletion F x (fun i j ↦
        ((z.2.1 (EuclideanSpace.single i 1)) j + (z.2.1 (EuclideanSpace.single j 1)) i) / 2 -
          ∑ k, christoffel F x i j k * z.1 k - (1 / 2 : ℝ) * z.2.2 i j)
    map_add' z w := by
      simp only [Prod.fst_add, Prod.snd_add, PiLp.add_apply, add_apply,
        Matrix.add_apply, mul_add, add_smul, Finset.sum_add_distrib]
      have ht : (fun i j ↦
          (((z.2.1 (EuclideanSpace.single i 1)) j + (w.2.1 (EuclideanSpace.single i 1)) j) +
            ((z.2.1 (EuclideanSpace.single j 1)) i + (w.2.1 (EuclideanSpace.single j 1)) i)) / 2 -
          ((∑ k, christoffel F x i j k * z.1 k) + (∑ k, christoffel F x i j k * w.1 k)) -
          ((1/2 : ℝ) * z.2.2 i j + (1/2 : ℝ) * w.2.2 i j)) =
        (fun i j ↦ ((z.2.1 (EuclideanSpace.single i 1)) j +
          (z.2.1 (EuclideanSpace.single j 1)) i) / 2 -
          ∑ k, christoffel F x i j k * z.1 k - (1/2 : ℝ) * z.2.2 i j) +
        (fun i j ↦ ((w.2.1 (EuclideanSpace.single i 1)) j +
          (w.2.1 (EuclideanSpace.single j 1)) i) / 2 -
          ∑ k, christoffel F x i j k * w.1 k - (1/2 : ℝ) * w.2.2 i j) := by
        ext i j; simp only [Pi.add_apply]; ring
      rw [ht, map_add]
      abel
    map_smul' a z := by
      change (∑ i, ∑ j, ((inducedMetric F x)⁻¹ i j * (a * z.1 j)) • partialDeriv F x i) +
        canonicalNormalCompletion F x (fun i j ↦
          (a * (z.2.1 (EuclideanSpace.single i 1)) j + a * (z.2.1 (EuclideanSpace.single j 1)) i) / 2 -
          ∑ k, christoffel F x i j k * (a * z.1 k) - (1/2 : ℝ) * (a * z.2.2 i j)) = _
      have ht : (fun i j ↦
          (a * (z.2.1 (EuclideanSpace.single i 1)) j + a * (z.2.1 (EuclideanSpace.single j 1)) i) / 2 -
          ∑ k, christoffel F x i j k * (a * z.1 k) - (1/2 : ℝ) * (a * z.2.2 i j)) =
        a • (fun i j ↦ ((z.2.1 (EuclideanSpace.single i 1)) j +
          (z.2.1 (EuclideanSpace.single j 1)) i) / 2 -
          ∑ k, christoffel F x i j k * z.1 k - (1/2 : ℝ) * z.2.2 i j) := by
        ext i j
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [show (∑ k, christoffel F x i j k * (a * z.1 k)) =
          a * ∑ k, christoffel F x i j k * z.1 k by rw [Finset.mul_sum]; congr 1; funext k; ring]
        ring
      rw [ht, map_smul, smul_add]
      congr 1
      simp only [Finset.smul_sum, smul_smul, RingHom.id_apply, mul_left_comm] }

/-- The coefficient map contains the actual canonical normal completion and
Christoffel connection (`app:ch_response:eq:response-full-map`). -/
private theorem completionJetOperator_eq {n N : ℕ} (F : Euclidean n → Euclidean N)
    {u : Euclidean n → Euclidean n} (h : MetricField n) {x : Euclidean n}
    (hu : DifferentiableAt ℝ u x) :
    completionJetOperator F x (u x, fderiv ℝ u x, h x) = completedVariation F u h x := by
  have hd (i j : Fin n) : partialDeriv (fun y ↦ u y j) x i =
      (fderiv ℝ u x (EuclideanSpace.single i 1)) j := by
    exact congrArg (fun L : Euclidean n →L[ℝ] ℝ ↦ L (EuclideanSpace.single i 1))
      (((EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp x hu.hasFDerivAt).fderiv)
  change _ + canonicalNormalCompletion F x _ = _ + canonicalNormalCompletion F x _
  congr 1
  congr 1
  ext i j
  simp only [symmCovariantDeriv, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, hd]


/-- Smoothness of the actual first-order coefficient map follows from the
retained immersion and normal-rank gaps (`app:ch_response:prop:response-ambient`). -/
private theorem contDiffOn_completionJetOperator {n N : ℕ}
    {F : Euclidean n → Euclidean N} {U : Set (Euclidean n)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U) :
    ContDiffOn ℝ ∞ (completionJetOperator F) U := by
  apply contDiffOn_clm_apply.mpr
  intro z
  let entry (i j : Fin n) : MetricTensor n →L[ℝ] ℝ :=
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) j).comp
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ Fin n → ℝ) i)).toContinuousLinearMap
  have hchrist (i j k : Fin n) : ContDiffOn ℝ ∞ (fun x ↦ christoffel F x i j k) U := by
    have hm (a b : Fin n) : ContDiffOn ℝ ∞ (fun x ↦ inducedMetric F x a b) U :=
      (entry a b).contDiff.comp_contDiffOn (contDiffOn_inducedMetric hU hF)
    have hp (a b c : Fin n) : ContDiffOn ℝ ∞
        (fun x ↦ partialDeriv (fun y ↦ inducedMetric F y a b) x c) U :=
      ((hm a b).fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply
        (contDiffOn_const (c := EuclideanSpace.single c 1))
    have hinv (a b : Fin n) : ContDiffOn ℝ ∞ (fun x ↦ (inducedMetric F x)⁻¹ a b) U :=
      (entry a b).contDiff.comp_contDiffOn (contDiffOn_inverse_inducedMetric hU hF hi)
    unfold christoffel
    apply contDiffOn_const.mul
    apply ContDiffOn.sum
    intro l _
    exact (hinv k l).mul (((hp j l i).add (hp i l j)).sub (hp i j l))
  dsimp only [completionJetOperator, LinearMap.toContinuousLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
  apply ContDiffOn.add
  · apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro j _
    exact ((entry i j).contDiff.comp_contDiffOn
      (contDiffOn_inverse_inducedMetric hU hF hi)).mul contDiffOn_const |>.smul
        (contDiffOn_partialDeriv hU hF i)
  · apply contDiffOn_canonicalNormalCompletion hU hF _ hi hrank
    apply (show (Fin n → Fin n → ℝ) →L[ℝ] MetricTensor n from
      { LinearMap.id with cont := continuous_id }).contDiff.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    exact (contDiffOn_const.sub (ContDiffOn.sum fun k _ ↦
      (hchrist i j k).mul contDiffOn_const)).sub contDiffOn_const

/-- The actual canonical tangent-normal completion is homogeneous in the
solved covector and tensor source, with exactly one derivative on the
covector. Its coefficient constant is chosen before both inputs. Consumer:
finite source bounds for the SAME ambient response
(`app:ch_response:eq:response-full-map`, `app:ch_response:prop:response-ambient`). -/
theorem exists_completedVariation_jet_bound {n N : ℕ}
    {F : Euclidean n → Euclidean N} {K U : Set (Euclidean n)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Euclidean n → Euclidean n) (h : MetricField n),
      ContDiff ℝ ∞ u → ContDiff ℝ ∞ h → ∀ x ∈ K,
        ‖iteratedFDeriv ℝ q (completedVariation F u h) x‖ ≤
          C * (cNorm K (q + 1) u + cNorm K q h) := by
  let A := completionJetOperator F
  have hA : ContDiffOn ℝ ∞ A U := contDiffOn_completionJetOperator hU hF hi hrank
  refine ⟨(2 : ℝ)^q * cNorm K q A, mul_nonneg (by positivity) (cNorm_nonneg _ _ _), ?_⟩
  intro u h hu hh x hx
  let J : Euclidean n → CompletionData n := fun y ↦ (u y, fderiv ℝ u y, h y)
  have hdu : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hJ : ContDiff ℝ ∞ J := hu.prodMk (hdu.prodMk hh)
  have heq : (fun y ↦ A y (J y)) = completedVariation F u h := by
    funext y
    exact completionJetOperator_eq F h ((hu.differentiable (by simp)).differentiableAt)
  let B := ContinuousLinearMap.id ℝ (CompletionData n →L[ℝ] Euclidean N)
  have hb := B.norm_iteratedFDerivWithin_le_of_bilinear hA hJ.contDiffOn
    hU.uniqueDiffOn (hKU hx) (n := q) (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ hU (hKU hx)] at hb
  change ‖iteratedFDeriv ℝ q (fun y ↦ A y (J y)) x‖ ≤ _ at hb
  rw [heq] at hb
  have hcoef (i : ℕ) (hi : i ≤ q) : ‖iteratedFDeriv ℝ i A x‖ ≤ cNorm K q A :=
    norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun y hy ↦ (hA.contDiffAt (hU.mem_nhds (hKU hy))).of_le (by simp)) hx hi
  have hjet (j : ℕ) (hj : j ≤ q) : ‖iteratedFDeriv ℝ j J x‖ ≤
      cNorm K (q+1) u + cNorm K q h := by
    rw [show J = fun y ↦ (u y, (fderiv ℝ u y, h y)) from rfl,
      iteratedFDeriv_prodMk hu.contDiffAt (hdu.prodMk hh).contDiffAt (by simp : (j : ℕ∞ω) ≤ ∞),
      ContinuousMultilinearMap.opNorm_prod,
      iteratedFDeriv_prodMk hdu.contDiffAt hh.contDiffAt (by simp : (j : ℕ∞ω) ≤ ∞),
      ContinuousMultilinearMap.opNorm_prod, norm_iteratedFDeriv_fderiv]
    exact max_le
      ((norm_iteratedFDeriv_le_cNorm hK (hu.of_le (by simp)) hx (by omega : j ≤ q+1)).trans
        (le_add_of_nonneg_right (cNorm_nonneg _ _ _)))
      (max_le
        ((norm_iteratedFDeriv_le_cNorm hK (hu.of_le (by simp)) hx (by omega : j+1 ≤ q+1)).trans
          (le_add_of_nonneg_right (cNorm_nonneg _ _ _)))
        ((norm_iteratedFDeriv_le_cNorm hK (hh.of_le (by simp)) hx hj).trans
          (le_add_of_nonneg_left (cNorm_nonneg _ _ _))))
  have hsum : ∑ i ∈ Finset.range (q+1), (q.choose i : ℝ) = (2 : ℝ)^q := by
    exact_mod_cast Nat.sum_range_choose q
  apply hb.trans
  calc
    _ ≤ 1 * ∑ i ∈ Finset.range (q+1), (q.choose i : ℝ) *
        cNorm K q A * (cNorm K (q+1) u + cNorm K q h) := by
      apply mul_le_mul
      · exact ContinuousLinearMap.norm_id_le
      · apply Finset.sum_le_sum
        intro i hi
        have hiq : i ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hcoef i hiq) (Nat.cast_nonneg _))
          (hjet (q-i) (Nat.sub_le _ _)) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (cNorm_nonneg _ _ _))
      · positivity
      · norm_num
    _ = _ := by rw [one_mul, ← Finset.sum_mul, ← Finset.sum_mul, hsum]

end JanetCartan.CorrectedAtoms
