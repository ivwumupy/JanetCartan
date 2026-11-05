module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.PrimitiveBounds.Shells
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion.JointJets

/-!
# Normalized jets of the actual source Fourier coefficients

For `app:ch_regular_base:thm:actual-calculus`, Step 1, the ordered physical
coordinate estimates in `SourceExpansion` control the multilinear matrix jets
required by `LowBounds.PrimitiveNormalShellInputs.leftJets` and `.rightJets`.
The conversion costs no additional derivatives. The total reserve is `3 * n + 4`,
independent of the requested Sobolev order in
`app:ch_regular_base:eq:graph-derivative-transfer`.

The scale comparison `ρ ≤ c * (1 + ‖ρ • u‖)` is a geometric input on the
normalized inverse range. Its producer is the averaged-gradient growth bound,
together with the normalized output shell and inverse equations. This file
proves the amplitude estimates, including zero symbol budget; it does not
construct the coefficient operators or the full graph realization.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Matrix.Norms.Frobenius
open JanetCartan JanetCartan.FourierIntegral JanetCartan.FourierIntegral.SourceExpansion
open AmplitudeBound
namespace JanetCartan.FourierIntegral.FullLowBounds
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

private theorem scalarCoefficientJet_eq_iteratedFDeriv {f : E × E → ℂ} (hf : ContDiff ℝ ∞ f) (k : ℕ)
    (w : Fin k → Fin n ⊕ Fin n) (z : E × E) :
    scalarCoefficientJet (List.ofFn w) f z =
      iteratedFDeriv ℝ k f z (fun i ↦ coefficientDirection (w i)) := by
  induction k generalizing z with
  | zero => simp [scalarCoefficientJet, iteratedFDeriv_zero_apply]
  | succ k ih =>
    rw [List.ofFn_succ, scalarCoefficientJet]
    rw [funext (ih (fun i ↦ w i.succ))]
    symm
    apply DifferentiableAt.iteratedFDeriv_succ_apply_left'
    exact hf.differentiable_iteratedFDeriv (m := k) (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)) z

private theorem matrixCoefficientJet_eq_iteratedFDeriv {f : E × E → Mat} (hf : ContDiff ℝ ∞ f) (k : ℕ)
    (w : Fin k → Fin n ⊕ Fin n) (z : E × E) :
    matrixCoefficientJet (List.ofFn w) (fun x η ↦ f (x,η)) z.1 z.2 =
      iteratedFDeriv ℝ k f z (fun i ↦ coefficientDirection (w i)) := by
  ext i j
  have hs := (matrixEntryEvaluation i j).iteratedFDeriv_comp_left (x := z) hf.contDiffAt (i := k) (by simp)
  change scalarCoefficientJet (List.ofFn w) (fun p ↦ f p i j) z = _
  exact (scalarCoefficientJet_eq_iteratedFDeriv ((matrixEntryEvaluation i j).contDiff.comp hf) k w z).trans
    (congrArg (fun T ↦ T (fun a ↦ coefficientDirection (w a))) hs)

private def coefficientCoordinate (z : E × E) : Fin n ⊕ Fin n → ℝ
  | .inl i => z.1 i
  | .inr i => z.2 i

private theorem sum_coefficientDirection (z : E × E) :
    ∑ a : Fin n ⊕ Fin n, coefficientCoordinate z a • coefficientDirection a = z := by
  classical
  rw [Fintype.sum_sum_type]
  apply Prod.ext <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sum, Prod.snd_sum,
      Prod.smul_fst, Prod.smul_snd, coefficientCoordinate, coefficientDirection,
      smul_zero, Finset.sum_const_zero, add_zero, zero_add]
  all_goals
    ext i
    simp [Pi.single_apply, mul_ite]

private theorem norm_coefficientCoordinate_le (z : E × E) (a : Fin n ⊕ Fin n) :
    ‖coefficientCoordinate z a‖ ≤ ‖z‖ := by
  cases a with
  | inl i => exact (PiLp.norm_apply_le z.1 i).trans (norm_fst_le z)
  | inr i => exact (PiLp.norm_apply_le z.2 i).trans (norm_snd_le z)

private theorem norm_multilinear_le_coordinates {k : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E × E) Mat) {B : ℝ}
    (hB : 0 ≤ B)
    (hb : ∀ w : Fin k → Fin n ⊕ Fin n, ‖T (fun i ↦ coefficientDirection (w i))‖ ≤ B) :
    ‖T‖ ≤ (2 * (n : ℝ)) ^ k * B := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have he : T v = ∑ w : Fin k → Fin n ⊕ Fin n,
      (∏ i, coefficientCoordinate (v i) (w i)) •
        T (fun i ↦ coefficientDirection (w i)) := by
    have hv : v = fun i ↦ ∑ a : Fin n ⊕ Fin n,
        coefficientCoordinate (v i) a • coefficientDirection a :=
      funext fun i ↦ (sum_coefficientDirection (v i)).symm
    conv_lhs => rw [hv]
    rw [T.map_sum]
    exact Finset.sum_congr rfl fun w _ ↦ T.map_smul_univ _ _
  rw [he]
  calc
    _ ≤ ∑ w : Fin k → Fin n ⊕ Fin n,
        ‖(∏ i, coefficientCoordinate (v i) (w i)) •
          T (fun i ↦ coefficientDirection (w i))‖ := norm_sum_le _ _
    _ ≤ ∑ _w : Fin k → Fin n ⊕ Fin n, (∏ i, ‖v i‖) * B := by
      apply Finset.sum_le_sum
      intro w _
      rw [norm_smul, norm_prod]
      exact mul_le_mul
        (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦
          norm_coefficientCoordinate_le (v i) (w i)) (hb w) (norm_nonneg _) (by positivity)
    _ = _ := by simp [Fintype.card_sum, Nat.cast_pow, Nat.cast_add]; ring

private def coefficientDilation (ρ : ℝ) : E × E →L[ℝ] E × E :=
  (ContinuousLinearMap.fst ℝ E E).prod (ρ • ContinuousLinearMap.snd ℝ E E)

private def directionScale (ρ : ℝ) (a : Fin n ⊕ Fin n) : ℝ :=
  if a.isRight then ρ else 1

private theorem coefficientDilation_direction (ρ : ℝ) (a : Fin n ⊕ Fin n) :
    coefficientDilation ρ (coefficientDirection a) =
      directionScale ρ a • coefficientDirection a := by
  cases a <;> simp [coefficientDilation, coefficientDirection, directionScale]

private theorem prod_directionScale (ρ : ℝ) {k : ℕ} (w : Fin k → Fin n ⊕ Fin n) :
    ∏ i, directionScale ρ (w i) = ρ ^ ((List.ofFn w).filter Sum.isRight).length := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.prod_univ_succ, ih, List.ofFn_succ]
    cases w 0 <;> simp [directionScale, pow_succ, mul_comm]

/-- Coordinate bounds control the normalized Fréchet derivative, with a geometric
comparison between the shell radius and the original covector size. Source: `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem norm_iteratedFDeriv_normalized_coefficient_le
    {a : E → E → Mat} (ha : ContDiff ℝ ∞ (Function.uncurry a))
    {N : ℕ} {B : ℝ} (hb : HasCoefficientSymbolBound a N B)
    {ρ c : ℝ} (hρ : 0 ≤ ρ) (hc : 1 ≤ c)
    (z : E × E) (hz : ρ ≤ c * (1 + ‖ρ • z.2‖)) {k : ℕ} (hk : k ≤ N) :
    ‖iteratedFDeriv ℝ k (fun p : E × E ↦ a p.1 (ρ • p.2)) z‖ ≤
      (2 * (n : ℝ)) ^ k * (c ^ k * B) := by
  have hB : 0 ≤ B := by
    have h := hb [] (by simp) 0 0
    simp only [coefficientCovectorWeight, List.filter_nil, List.length_nil, pow_zero,
      one_mul] at h
    exact (norm_nonneg _).trans h
  apply norm_multilinear_le_coordinates _ (mul_nonneg (pow_nonneg (zero_le_one.trans hc) _) hB)
  intro w
  have he := (coefficientDilation (n := n) ρ).iteratedFDeriv_comp_right ha z (i := k) (by simp)
  have hdir : iteratedFDeriv ℝ k (fun p : E × E ↦ a p.1 (ρ • p.2)) z
        (fun i ↦ coefficientDirection (w i)) =
      ρ ^ ((List.ofFn w).filter Sum.isRight).length •
        matrixCoefficientJet (List.ofFn w) a z.1 (ρ • z.2) := by
    change iteratedFDeriv ℝ k (Function.uncurry a ∘ coefficientDilation ρ) z _ = _
    rw [he]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      coefficientDilation_direction]
    rw [ContinuousMultilinearMap.map_smul_univ, prod_directionScale]
    exact congrArg (fun Q : Mat ↦ ρ ^ ((List.ofFn w).filter Sum.isRight).length • Q)
      (matrixCoefficientJet_eq_iteratedFDeriv ha k w (z.1, ρ • z.2)).symm
  rw [hdir, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hρ _)]
  have hb' := hb (List.ofFn w) (by simpa using hk) z.1 (ρ • z.2)
  have hm : ((List.ofFn w).filter Sum.isRight).length ≤ k :=
    (List.length_filter_le _ _).trans_eq List.length_ofFn
  calc
    _ ≤ (c * (1 + ‖ρ • z.2‖)) ^ ((List.ofFn w).filter Sum.isRight).length *
        ‖matrixCoefficientJet (List.ofFn w) a z.1 (ρ • z.2)‖ := by gcongr
    _ = c ^ ((List.ofFn w).filter Sum.isRight).length *
        (coefficientCovectorWeight (List.ofFn w) (ρ • z.2) *
          ‖matrixCoefficientJet (List.ofFn w) a z.1 (ρ • z.2)‖) := by
      rw [mul_pow]; dsimp [coefficientCovectorWeight]; ring
    _ ≤ c ^ ((List.ofFn w).filter Sum.isRight).length * B := by gcongr
    _ ≤ c ^ k * B := by gcongr


private theorem norm_iteratedFDeriv_comp_contraction_le
    {f : E × E → Mat} (hf : ContDiff ℝ ∞ f)
    (P : NormalVariables n →L[ℝ] E × E) (hP : ∀ v, ‖P v‖ ≤ ‖v‖)
    (k : ℕ) (z : NormalVariables n) :
    ‖iteratedFDeriv ℝ k (f ∘ P) z‖ ≤ ‖iteratedFDeriv ℝ k f (P z)‖ := by
  rw [P.iteratedFDeriv_comp_right hf z (by simp)]
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  apply (ContinuousMultilinearMap.le_opNorm _ _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ hP (v i)

private def leftNormalProjection : NormalVariables n →L[ℝ] E × E :=
  (ContinuousLinearMap.fst ℝ E (E × E)).prod
    ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E × E)))

private def rightNormalProjection : NormalVariables n →L[ℝ] E × E :=
  ContinuousLinearMap.snd ℝ E (E × E)

private theorem leftNormalProjection_apply (z : NormalVariables n) :
    leftNormalProjection z = (z.1, z.2.2) := rfl

private theorem rightNormalProjection_apply (z : NormalVariables n) :
    rightNormalProjection z = z.2 := rfl

/-- The left normalized matrix jet bound used by the primitive low construction. Source: `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem norm_iteratedFDeriv_normalized_left_le
    {a : E → E → Mat} (ha : ContDiff ℝ ∞ (Function.uncurry a))
    {N : ℕ} {B : ℝ} (hb : HasCoefficientSymbolBound a N B)
    {ρ c : ℝ} (hρ : 0 ≤ ρ) (hc : 1 ≤ c)
    (z : NormalVariables n) (hz : ρ ≤ c * (1 + ‖ρ • z.2.2‖))
    {k : ℕ} (hk : k ≤ N) :
    ‖iteratedFDeriv ℝ k (fun q : NormalVariables n ↦
      normalizedNormalMatrix ρ 0 a q.1 q.2.2) z‖ ≤
        (2 * (n : ℝ)) ^ k * (c ^ k * B) := by
  have hf : ContDiff ℝ ∞ (fun p : E × E ↦ a p.1 (ρ • p.2)) :=
    ha.comp (contDiff_fst.prodMk (contDiff_snd.const_smul ρ))
  have hp (v : NormalVariables n) : ‖leftNormalProjection v‖ ≤ ‖v‖ := by
    change max ‖v.1‖ ‖v.2.2‖ ≤ ‖v‖
    exact max_le (norm_fst_le v) ((norm_snd_le v.2).trans (norm_snd_le v))
  have h := norm_iteratedFDeriv_comp_contraction_le hf leftNormalProjection hp k z
  simp only [Function.comp_def, leftNormalProjection_apply] at h
  simp only [normalizedNormalMatrix, neg_zero, Real.rpow_zero, one_smul]
  exact h.trans (norm_iteratedFDeriv_normalized_coefficient_le ha hb hρ hc
    (z.1, z.2.2) hz hk)

/-- The right normalized matrix jet bound used by the primitive low construction. Source: `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem norm_iteratedFDeriv_normalized_right_le
    {a : E → E → Mat} (ha : ContDiff ℝ ∞ (Function.uncurry a))
    {N : ℕ} {B : ℝ} (hb : HasCoefficientSymbolBound a N B)
    {ρ c : ℝ} (hρ : 0 ≤ ρ) (hc : 1 ≤ c)
    (z : NormalVariables n) (hz : ρ ≤ c * (1 + ‖ρ • z.2.2‖))
    {k : ℕ} (hk : k ≤ N) :
    ‖iteratedFDeriv ℝ k (fun q : NormalVariables n ↦
      normalizedNormalMatrix ρ 0 a q.2.1 q.2.2) z‖ ≤
        (2 * (n : ℝ)) ^ k * (c ^ k * B) := by
  have hf : ContDiff ℝ ∞ (fun p : E × E ↦ a p.1 (ρ • p.2)) :=
    ha.comp (contDiff_fst.prodMk (contDiff_snd.const_smul ρ))
  have h := norm_iteratedFDeriv_comp_contraction_le hf rightNormalProjection norm_snd_le k z
  simp only [Function.comp_def, rightNormalProjection_apply] at h
  simp only [normalizedNormalMatrix, neg_zero, Real.rpow_zero, one_smul]
  exact h.trans (norm_iteratedFDeriv_normalized_coefficient_le ha hb hρ hc z.2 hz hk)


/-- Smoothness of the actual coefficient in the Frobenius matrix space. Source: `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem contDiff_matrixCoefficient (A : FullAmplitude n r)
    (hA : ContDiff ℝ ∞ (fun p : E × E × E ↦ A p.1 p.2.1 p.2.2))
    (ℓ : ℝ) (k : Fin n → ℤ) :
    ContDiff ℝ ∞ (Function.uncurry (matrixCoefficient ℓ A k)) := by
  classical
  have he : Function.uncurry (matrixCoefficient ℓ A k) = fun p : E × E ↦
      ∑ i : Fin r, ∑ j : Fin r,
        matrixCoefficient ℓ A k p.1 p.2 i j • (Matrix.single i j 1 : Mat) := by
    funext p
    ext i j
    simp [Matrix.single, Matrix.sum_apply, ite_and, Function.uncurry_def]
  rw [he]
  exact ContDiff.sum fun i _ ↦ ContDiff.sum fun j _ ↦
    (contDiff_matrixCoefficient_entry A hA ℓ k i j).smul contDiff_const


/-- One constant for every normalized jet through the prescribed low order. Source: `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
def normalizedCoefficientJetConstant (n N : ℕ) (c : ℝ) : ℝ :=
  max 1 (2 * (n : ℝ)) ^ N * c ^ N

/-- The common normalized jet constant is positive under the geometric scale comparison. Source: `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem normalizedCoefficientJetConstant_pos (N : ℕ) {c : ℝ} (hc : 1 ≤ c) :
    0 < normalizedCoefficientJetConstant n N c := by
  unfold normalizedCoefficientJetConstant
  have : 0 < c := zero_lt_one.trans_le hc
  positivity

/-- Converting the source coefficient bounds to the two actual primitive shell slots. Source: `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem normalized_coefficient_jets_le
    {a : E → E → Mat} (ha : ContDiff ℝ ∞ (Function.uncurry a))
    {N : ℕ} {B : ℝ} (hb : HasCoefficientSymbolBound a N B)
    {ρ c : ℝ} (hρ : 0 ≤ ρ) (hc : 1 ≤ c)
    (z : NormalVariables n) (hz : ρ ≤ c * (1 + ‖ρ • z.2.2‖))
    {k : ℕ} (hk : k ≤ N) :
    ‖iteratedFDeriv ℝ k (fun q : NormalVariables n ↦
      normalizedNormalMatrix ρ 0 a q.1 q.2.2) z‖ ≤
        normalizedCoefficientJetConstant n N c * B ∧
    ‖iteratedFDeriv ℝ k (fun q : NormalVariables n ↦
      normalizedNormalMatrix ρ 0 a q.2.1 q.2.2) z‖ ≤
        normalizedCoefficientJetConstant n N c * B := by
  have hB : 0 ≤ B := (mul_nonneg (coefficientCovectorWeight_pos [] (0 : E)).le
    (norm_nonneg _)).trans (hb [] (by simp) 0 0)
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hbound : (2 * (n : ℝ)) ^ k * (c ^ k * B) ≤
      normalizedCoefficientJetConstant n N c * B := by
    unfold normalizedCoefficientJetConstant
    rw [← mul_assoc]
    gcongr
    calc
      (2 * (n : ℝ)) ^ k ≤ max 1 (2 * (n : ℝ)) ^ k := by gcongr; exact le_max_right _ _
      _ ≤ max 1 (2 * (n : ℝ)) ^ N := pow_le_pow_right₀ (le_max_left _ _) hk
  exact ⟨(norm_iteratedFDeriv_normalized_left_le ha hb hρ hc z hz hk).trans hbound,
    (norm_iteratedFDeriv_normalized_right_le ha hb hρ hc z hz hk).trans hbound⟩

/-- The total low reserve is fixed before every requested Sobolev output order. Source: `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
def fullLowReserve (n : ℕ) : ℕ :=
  LowBounds.primitiveNormalReserve n + lowReserve n

/-- Explicit dimension dependence of the full low reserve. Source: `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem fullLowReserve_eq (n : ℕ) : fullLowReserve n = 3 * n + 4 := by
  simp only [fullLowReserve, LowBounds.primitiveNormalReserve, lowReserve]
  omega

/-- Original full-amplitude jets supply both normalized coefficient jet budgets,
with the exact summable source decay retained. Source: `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem normalized_matrixCoefficient_jets_le
    (hn : 0 < n) {R ℓ : ℝ} (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2)
    (A : FullAmplitude n r)
    (hs : ∀ x η i j, SupportedInCenteredBox R (fun y ↦ A x y η i j))
    (hA : ContDiff ℝ ∞ (fun p : E × E × E ↦ A p.1 p.2.1 p.2.2))
    {B : ℝ} (hb : HasFullSourceSymbolBound A (fullLowReserve n) B)
    (m : Fin n → ℤ) {ρ c : ℝ} (hρ : 0 ≤ ρ) (hc : 1 ≤ c)
    (z : NormalVariables n) (hz : ρ ≤ c * (1 + ‖ρ • z.2.2‖))
    {k : ℕ} (hk : k ≤ LowBounds.primitiveNormalReserve n) :
    let b := normalizedCoefficientJetConstant n (LowBounds.primitiveNormalReserve n) c *
      ((r : ℝ)^2 * coefficientConstant n (lowReserve n) ℓ * B * decayWeight (lowReserve n) m)
    ‖iteratedFDeriv ℝ k (fun q : NormalVariables n ↦
      normalizedNormalMatrix ρ 0 (matrixCoefficient ℓ A m) q.1 q.2.2) z‖ ≤ b ∧
    ‖iteratedFDeriv ℝ k (fun q : NormalVariables n ↦
      normalizedNormalMatrix ρ 0 (matrixCoefficient ℓ A m) q.2.1 q.2.2) z‖ ≤ b :=
  normalized_coefficient_jets_le (contDiff_matrixCoefficient A hA ℓ m)
    (hasCoefficientSymbolBound_matrixCoefficient_lowReserve hn hℓ hR A hs hA
      (LowBounds.primitiveNormalReserve n) hb m) hρ hc z hz hk

end JanetCartan.FourierIntegral.FullLowBounds

