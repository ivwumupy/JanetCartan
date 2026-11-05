module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.InactiveDerivatives.UniformPhase.Spatial

/-!
# Direction-independent source budgets

For `app:ch_response:thm:response-literal-transfer`, constants must also be
uniform over unit parameter directions. We majorize the existing finite
coefficient budget by that same budget evaluated at scalar unit directions.
No differentiated phase or envelope bounds are inputs.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.UniformPhase
open MixedGrades InactiveSource Pseudodifferential
variable {p d r : ℕ}
local notation "P" => Euclidean p
local notation "E" => Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin r)

private theorem coefficientBudget_le_unit {H Q : ℕ → ℝ}
    (hH : ∀ j, 0 ≤ H j) (hQ : ∀ j, 0 ≤ Q j)
    (k : ℕ) (v : Fin k → P) (hv : ∀ i, ‖v i‖ ≤ 1)
    (b : CarrierJetBranch k) (j : ℕ) :
    carrierCoefficientBudget H Q k v b j ≤
      carrierCoefficientBudget H Q k (fun _ ↦ (1 : ℝ)) b j := by
  induction k generalizing j with
  | zero => exact le_rfl
  | succ k ih =>
    cases b with
    | inl b =>
      simp only [carrierCoefficientBudget, norm_one, one_mul]
      calc
        _ ≤ 1 * carrierCoefficientBudget H Q k (Fin.tail v) b (j + 1) :=
          mul_le_mul_of_nonneg_right (hv 0) (carrierCoefficientBudget_nonneg hH hQ _ _ _ _)
        _ = _ := one_mul _
        _ ≤ _ := ih (Fin.tail v) (fun i ↦ hv i.succ) b (j + 1)
    | inr b =>
      simp only [carrierCoefficientBudget, norm_one, one_mul]
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          ((mul_le_mul_of_nonneg_right (hv 0) (hH _)).trans_eq (one_mul _))
          (Nat.cast_nonneg _))
        (ih (Fin.tail v) (fun i ↦ hv i.succ) b (j - i))
        (carrierCoefficientBudget_nonneg hH hQ _ _ _ _)
        (mul_nonneg (Nat.cast_nonneg _) (hH _))

/-- Unit-direction polynomial budget through parameter order `k`, computed
entirely from primitive phase constants. Consumer: the common Sobolev source
profile in `app:ch_response:thm:response-literal-transfer`. -/
def unitPolynomialBudget (H : ℕ → ℝ) (k j : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (k + 1), ∑ b : CarrierJetBranch l,
    carrierCoefficientBudget H (fun i ↦ if i = 0 then 1 else 0)
      l (fun _ ↦ (1 : ℝ)) b j

/-- Nonnegativity of the uniform finite phase budget. Source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem unitPolynomialBudget_nonneg {H : ℕ → ℝ} (hH : ∀ j, 0 ≤ H j)
    (k j : ℕ) : 0 ≤ unitPolynomialBudget H k j := by
  exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
    carrierCoefficientBudget_nonneg hH (fun i ↦ by split_ifs <;> positivity) _ _ _ _

private theorem polynomialBudget_le_unit {H : ℕ → ℝ} (hH : ∀ j, 0 ≤ H j)
    (k : ℕ) (vs : List P) (hlen : vs.length ≤ k)
    (hv : ∀ w ∈ vs, ‖w‖ ≤ 1) (j : ℕ) :
    sourcePolynomialBudget H vs j ≤ unitPolynomialBudget H k j := by
  apply (Finset.sum_le_sum (fun b _ ↦ coefficientBudget_le_unit hH
    (fun i ↦ by split_ifs <;> positivity) vs.length vs.get
      (fun i ↦ hv _ (List.get_mem ..)) b j)).trans
  unfold unitPolynomialBudget
  apply Finset.single_le_sum (a := vs.length)
    (f := fun l ↦ ∑ b : CarrierJetBranch l,
      carrierCoefficientBudget H (fun i ↦ if i = 0 then 1 else 0)
        l (fun _ ↦ (1 : ℝ)) b j) _ (Finset.mem_range_succ_iff.mpr hlen)
  intro l _
  exact Finset.sum_nonneg fun b _ ↦
    carrierCoefficientBudget_nonneg hH (fun i ↦ by split_ifs <;> positivity) l
      (fun _ ↦ (1 : ℝ)) b j

private theorem splitting_directions {vs : List P} {s : List P × List P}
    (hs : s ∈ parameterLeibnizSplittings vs) (hv : ∀ w ∈ vs, ‖w‖ ≤ 1) :
    (∀ w ∈ s.1, ‖w‖ ≤ 1) ∧ (∀ w ∈ s.2, ‖w‖ ≤ 1) := by
  induction vs generalizing s with
  | nil =>
    simp only [parameterLeibnizSplittings, List.mem_singleton] at hs
    subst s
    simp
  | cons v vs ih =>
    have ht : ∀ w ∈ vs, ‖w‖ ≤ 1 := fun w hw ↦ hv w (by simp [hw])
    have h0 := hv v (by simp)
    simp only [parameterLeibnizSplittings, List.mem_append, List.mem_map] at hs
    rcases hs with ⟨t, ht', rfl⟩ | ⟨t, ht', rfl⟩
    · refine ⟨?_, (ih ht' ht).2⟩
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact h0
      · exact (ih ht' ht).1 w hw
    · refine ⟨(ih ht' ht).1, ?_⟩
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact h0
      · exact (ih ht' ht).2 w hw

private theorem splittings_length (vs : List P) :
    (parameterLeibnizSplittings vs).length = 2 ^ vs.length := by
  induction vs with
  | nil => simp [parameterLeibnizSplittings]
  | cons v vs ih => simp [parameterLeibnizSplittings, ih, pow_succ, Nat.mul_two]

/-- A common spatial source budget, independent of every unit direction tuple.
Only source parameter orders through `k` and source spatial orders through
`j+d+1` occur. Phase orders are at most `j+k`. Source:
`app:ch_response:thm:response-literal-transfer`. -/
def unitSpatialBudget (d : ℕ) (H : ℕ → ℝ) (C : ℕ → ℕ → ℝ) (k j : ℕ) : ℝ :=
  (2 : ℝ) ^ k * ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * unitPolynomialBudget H k i *
      (∑ l ∈ Finset.range (k + 1), envelopeJetProfileConstant d (C l) (j - i))

/-- Nonnegativity of the common spatial source budget. Source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem unitSpatialBudget_nonneg {H : ℕ → ℝ} (hH : ∀ j, 0 ≤ H j)
    (C : ℕ → ℕ → ℝ) (k j : ℕ) : 0 ≤ unitSpatialBudget d H C k j := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (unitPolynomialBudget_nonneg hH _ _))
    (Finset.sum_nonneg fun l _ ↦ envelopeJetProfileConstant_nonneg _ _ _)

private theorem spatialBudget_le_unit {H : ℕ → ℝ} (hH : ∀ j, 0 ≤ H j)
    (C : ℕ → ℕ → ℝ) (vs : List P) (hv : ∀ w ∈ vs, ‖w‖ ≤ 1) (j : ℕ) :
    sourceLeibnizSpatialBudget (d := d) (sourcePolynomialBudget H)
      (fun ws ↦ C ws.length) vs j ≤ unitSpatialBudget d H C vs.length j := by
  unfold sourceLeibnizSpatialBudget unitSpatialBudget
  calc
    _ ≤ ((parameterLeibnizSplittings vs).map (fun _ ↦
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * unitPolynomialBudget H vs.length i *
          (∑ l ∈ Finset.range (vs.length + 1), envelopeJetProfileConstant d (C l) (j - i)))).sum := by
      apply List.sum_le_sum
      intro t ht
      have hord := parameterLeibnizSplittings_orders ht
      have hdir := splitting_directions ht hv
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (polynomialBudget_le_unit hH _ t.1 (by omega) hdir.1 i)
          (Nat.cast_nonneg _))
        (Finset.single_le_sum (fun l _ ↦ envelopeJetProfileConstant_nonneg _ _ _)
          (Finset.mem_range_succ_iff.mpr (show t.2.length ≤ vs.length by omega)))
        (envelopeJetProfileConstant_nonneg _ _ _)
        (mul_nonneg (Nat.cast_nonneg _) (unitPolynomialBudget_nonneg hH _ _))
    _ = _ := by simp [List.map_const', splittings_length, nsmul_eq_mul]

/-- Uniformity over all unit parameter directions of the actual normalized
carrier derivative, from original source-jet profiles and primitive phase
bounds only. The constant is fixed before phase, scale, source and directions;
`j+k` is the exact phase reserve. Source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem norm_parameterCarrierJet_spatial_le_unit
    {V B : Set P} {U S : Set E} (hV : IsOpen V) (hU : IsOpen U)
    (hBV : B ⊆ V) (hS : IsCompact S) (hSU : S ⊆ U)
    (H : ℕ → ℝ) (hH : ∀ m, 0 ≤ H m) (C : ℕ → ℕ → ℝ)
    (k : ℕ) (ρ A K : ℝ) (hρ : 1 ≤ ρ) (hA : 0 ≤ A) (hK : 1 ≤ K)
    {φ : P → E → ℝ} (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ U))
    {f : P → E → F} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (V ×ˢ univ))
    (hs : ∀ a ∈ V, tsupport (f a) ⊆ S) {c : P} (hc : c ∈ B)
    (hm : ∀ vs : List P, MemLp (fun x ↦ parameterListJet (fun a ↦ f a x) vs c) 2 volume)
    (hmem : ∀ vs (j : ℕ), MemVectorFourierSobolev (j : ℝ) ((hm vs).toLp _))
    (hprofile : ∀ vs, vs.length ≤ k → (∀ w ∈ vs, ‖w‖ ≤ 1) → ∀ j : ℕ,
      vectorFourierSobolevNorm (j : ℝ) ((hm vs).toLp _) ≤
        C vs.length j * (A * K ^ vs.length) * K ^ j)
    (v : Fin k → P) (hv : ∀ i, ‖v i‖ ≤ 1) (j : ℕ)
    (hphase : ∀ x ∈ S, ∀ m ≤ j + k,
      ‖iteratedFDeriv ℝ m (Function.uncurry φ) (c, x)‖ ≤ H m * K ^ m)
    (x : E) :
    ‖iteratedFDeriv ℝ j (parameterCarrierJet ρ φ f k v c) x‖ ≤
      unitSpatialBudget d H C k j * (A * ρ ^ k * K ^ (k + d + 1)) * K ^ j := by
  have hvs : ∀ w ∈ List.ofFn v, ‖w‖ ≤ 1 := by simpa using hv
  have hprofile' : ∀ vs, vs ∈ (parameterLeibnizSplittings (List.ofFn v)).map Prod.snd →
      ∀ j : ℕ, vectorFourierSobolevNorm (j : ℝ) ((hm vs).toLp _) ≤
        C vs.length j * (A * K ^ vs.length) * K ^ j := by
    intro vs hvs'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hvs'
    have hord := parameterLeibnizSplittings_orders ht
    rw [List.length_ofFn] at hord
    exact hprofile t.2 (by omega) (splitting_directions ht hvs).2
  apply (norm_parameterCarrierJet_spatial_le hV hU hBV hS hSU H hH k v
    (fun vs ↦ C vs.length) ρ A K hρ hA hK hφ hf hs hc hm hmem
    hprofile' j hphase x).trans
  have hb := spatialBudget_le_unit (d := d) hH C (List.ofFn v) hvs j
  rw [List.length_ofFn] at hb
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hb (by positivity)) (by positivity)

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.UniformPhase
