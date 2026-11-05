module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicSymbols.ConicInverse
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.AffinePullback

/-!
# Physical jets of the original source times the conic inverse

The source is the literal `conicSourceSymbol`; neither its angular dependence
nor its radial mask is replaced. Constants depend on the fixed smooth source
on a compact normalized buffer. They precede the coefficient field.
Consumer: the algebraic PDO and its full physical derivative in
`app:ch_regular_base:eq:energy-complete-residual` of `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.AlgebraicSymbols
open ResidualCoordinates RootFamily ActualCarriers EvolutionIntegral
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "CMat" => Matrix (Fin q) (Fin q) ℂ

/-- The local Leibniz estimate retains every derivative of the scalar mask.
This is the fixed-mask multiplication used in `complement-symbol` and
`energy-complete-residual`; only smooth germs on the compact set are needed. -/
theorem cNorm_complex_smul_le_of_contDiffAt
    {K : Set E} (hK : IsCompact K) (m : ℕ)
    {f : E → ℂ} {g : E → CMat}
    (hf : ∀ x ∈ K, ContDiffAt ℝ m f x)
    (hg : ∀ x ∈ K, ContDiffAt ℝ m g x) :
    cNorm K m (fun x ↦ f x • g x) ≤
      (m + 1 : ℝ) * 2 ^ m * cNorm K m f * cNorm K m g := by
  have hb (k : ℕ) (hk : k ≤ m) (x : E) (hx : x ∈ K) :
      ‖iteratedFDeriv ℝ k (fun y ↦ f y • g y) x‖ ≤
        2 ^ m * cNorm K m f * cNorm K m g := by
    obtain ⟨U, hU, hxU, hfU⟩ := (hf x hx).contDiffOn' le_rfl (by simp)
    obtain ⟨V, hV, hxV, hgV⟩ := (hg x hx).contDiffOn' le_rfl (by simp)
    simp only [insert_eq_of_mem (mem_univ x), univ_inter] at hfU hgV
    have h := norm_iteratedFDerivWithin_smul_le
      (hfU.mono (inter_subset_left (t := V))) (hgV.mono (inter_subset_right (s := U)))
      (hU.inter hV).uniqueDiffOn ⟨hxU, hxV⟩ (n := k) (by exact_mod_cast hk)
    simp_rw [iteratedFDerivWithin_of_isOpen _ (hU.inter hV) ⟨hxU, hxV⟩] at h
    apply h.trans
    calc
      _ ≤ ∑ j ∈ Finset.range (k + 1),
          (k.choose j : ℝ) * cNorm K m f * cNorm K m g := by
        apply Finset.sum_le_sum
        intro j hj
        have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left
            (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hf hx (hjk.trans hk))
            (Nat.cast_nonneg _))
          (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hg hx ((Nat.sub_le k j).trans hk))
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (cNorm_nonneg _ _ _))
      _ = 2 ^ k * cNorm K m f * cNorm K m g := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        norm_cast
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hk) (cNorm_nonneg _ _ _))
        (cNorm_nonneg _ _ _)
  have h := cNorm_le_sum_of_bounds
    (fun _ _ ↦ mul_nonneg (mul_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ m)
      (cNorm_nonneg K m f)) (cNorm_nonneg K m g)) hb
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, mul_assoc] using h

/-- A fixed frequency scalar has its exact norm cost on physical jets.
Used for the unchanged right multiplier in `complement-symbol`. -/
theorem cNorm_const_complex_smul {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
    {K : Set E} (m : ℕ) (a : ℂ) {f : E → F}
    (hf : ∀ x ∈ K, ContDiffAt ℝ m f x) :
    cNorm K m (fun x ↦ a • f x) = ‖a‖ * cNorm K m f := by
  unfold cNorm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have he : (fun x ↦ ‖iteratedFDeriv ℝ j (fun y ↦ a • f y) x‖) '' K =
      (fun t : ℝ ↦ ‖a‖ • t) '' ((fun x ↦ ‖iteratedFDeriv ℝ j f x‖) '' K) := by
    rw [Set.image_image]
    apply Set.image_congr
    intro x hx
    rw [iteratedFDeriv_const_smul_apply' ((hf x hx).of_le (by exact_mod_cast hjm)), norm_smul]
    rfl
  rw [he, Set.image_smul, Real.sSup_smul_of_nonneg (norm_nonneg a), smul_eq_mul]

/-- The fixed smooth source has uniform physical seminorms over its compact
normalized angular buffer. This bounds the original mask, not the inverse.
Consumer: `exists_conicAlgebraicSymbol_weighted_cNorm_bounds`, for
`app:ch_regular_base:eq:complement-symbol`. -/
theorem exists_sourceSymbol_physical_cNorm_bounds
    (x : E) (R : ℝ) {Kη : Set (Euclidean d)} (hKη : IsCompact Kη)
    (σ : RootState (Euclidean d) → ℝ) (hσ : ContDiff ℝ ∞ σ) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧ ∀ η ∈ Kη, ∀ m,
      cNorm (closedBall x R) m (fun y ↦ sourceSymbol σ y η) ≤ C m := by
  let L : E →L[ℝ] E × Euclidean d := (ContinuousLinearMap.id ℝ E).prod 0
  let f : E × Euclidean d → ℂ := fun p ↦ sourceSymbol σ p.1 p.2
  have hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp (hσ.comp
    ((((coordinateSplit 0).contDiff.comp contDiff_fst).fst).prodMk
      ((((coordinateSplit 0).contDiff.comp contDiff_fst).snd).prodMk contDiff_snd)))
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro y
    simp [L]
  let J := closedBall x R ×ˢ Kη
  refine ⟨fun m ↦ 1 + cNorm J m f, fun m ↦ by linarith [cNorm_nonneg J m f], ?_⟩
  intro η hη m
  have h := SymbolBudgets.cNorm_preAffine_contraction_le L hL (0, η)
    ((isCompact_closedBall x R).prod hKη) isOpen_univ (subset_univ _)
    hf.contDiffOn (K := closedBall x R) (fun y hy ↦ by simpa [L] using And.intro hy hη) m
  have h' : cNorm (closedBall x R) m (fun y ↦ sourceSymbol σ y η) ≤ cNorm J m f := by
    simpa [L, f, J] using h
  exact h'.trans (le_add_of_nonneg_left zero_le_one)

end JanetCartan.RegularSector.Characteristic.AlgebraicSymbols
