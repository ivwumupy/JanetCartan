module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.MixedGrades.OrderedSpatial

/-!
# Grades of the actual normalized full amplitude

The finite polynomial and primitive selector estimates are combined with the
original full matrix amplitude. The resulting constant contains no frequency,
parameter value, datum, or regularization index. The extracted power is `2*k`,
independently of all physical derivative orders. Consumer: `GraphDecay.hAj`.
Source: `app:ch_response:thm:response-literal-transfer`.
-/

@[expose] public noncomputable section

open Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.MixedGrades

open FourierIntegral NormalComparison

variable {n r : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => Euclidean n

/-- The finite Leibniz budget for the normalized actual jet. Only primitive
phase, selector, carrier and full-amplitude profiles occur. Source:
`app:ch_response:thm:response-literal-transfer`. -/
def complementaryFullJetBudget (H Q Z R : ℕ → ℝ) (k : ℕ) (v : Fin k → P) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
    (∑ b : CarrierJetBranch k, carrierCoefficientBudget H (complementarySelectorBudget Q Z) k v b i) *
      R (j - i)

omit [NormedSpace ℝ P] in
/-- The finite full-amplitude budget is nonnegative, as required by GraphDecay.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem complementaryFullJetBudget_nonneg {H Q Z R : ℕ → ℝ}
    (hH : ∀ j, 0 ≤ H j) (hR : ∀ j, 0 ≤ R j) (k : ℕ) (v : Fin k → P) (j : ℕ) :
    0 ≤ complementaryFullJetBudget H Q Z R k v j := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun b _ ↦
    carrierCoefficientBudget_nonneg hH (complementarySelectorBudget_nonneg Q Z) k v b i))
    (hR _)

/-- The real primitive phase and its imaginary version have identical joint
jet norms. Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem norm_iteratedFDeriv_imaginaryPhase {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] {f : X → ℝ} {x : X}
    (hf : ContDiffAt ℝ ∞ f x) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun z ↦ Complex.I * (f z : ℂ)) x‖ =
      ‖iteratedFDeriv ℝ j f x‖ := by
  change ‖iteratedFDeriv ℝ j (fun z ↦ Complex.I • (Complex.ofRealLI ∘ f) z) x‖ = _
  have hfc : ContDiffAt ℝ j (Complex.ofRealLI ∘ f) x :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp x hf).of_le (by simp)
  rw [iteratedFDeriv_const_smul_apply' hfc,
    norm_smul, Complex.norm_I, one_mul,
    Complex.ofRealLI.norm_iteratedFDeriv_comp_left hf (by simp)]

/-- Joint physical/parameter grades of the actual normalized full jet at a
point in the smooth parameter neighborhood. Only finitely many original
primitive jets through `j+k` are inputs. In particular the moving selector
bound is proved rather than postulated. Source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem norm_iteratedFDeriv_normalizedComplementaryCarrierJet_joint_le
    {A : FullAmplitude n r} {q : E → ℂ} {ζ : P → E} {ψ : P → E → E → ℝ}
    {C : Set P} (hC : IsOpen C) (hζ : ContDiffOn ℝ ∞ ζ C) (hq : ContDiff ℝ ∞ q)
    (hψ : ContDiffOn ℝ ∞ (fun p : P × (E × E) ↦ ψ p.1 p.2.1 p.2.2)
      (C ×ˢ Set.univ))
    (hA : ∀ η, ContDiff ℝ ∞ (fun w : E × E ↦ A w.1 w.2 η))
    (H Q Z R : ℕ → ℝ) (hH : ∀ i, 0 ≤ H i)
    {L ρ : ℝ} (hL : 1 ≤ L) (hρ : 1 ≤ ρ) (hLρ : L ≤ ρ)
    (b k : ℕ) (v : Fin k → P) (j : ℕ) {c : P} (hc : c ∈ C) (x y η : E)
    (hψjet : ∀ i ≤ j + k, ‖iteratedFDeriv ℝ i
      (fun p : P × (E × E) ↦ ψ p.1 p.2.1 p.2.2) (c, (x, y))‖ ≤ H i * L ^ i)
    (hqjet : ∀ i ≤ j + k, ∀ δ, ‖iteratedFDeriv ℝ i q δ‖ ≤ Q i)
    (hζjet : ∀ i, 1 ≤ i → i ≤ j + k → ‖iteratedFDeriv ℝ i ζ c‖ ≤ Z i * L ^ i)
    (hAjet : ∀ i ≤ j, ‖iteratedFDeriv ℝ i (fun w : E × E ↦ A w.1 w.2 η) (x, y)‖ ≤
      R i * L ^ (b + i)) :
    ‖iteratedFDeriv ℝ j (fun p : P × (E × E) ↦
      normalizedComplementaryCarrierJet A q ζ ψ ρ k v p.1 p.2.1 p.2.2 η) (c, (x, y))‖ ≤
      complementaryFullJetBudget H Q Z R k v j * L ^ (b + j) := by
  let φ : P → (E × E) → ℂ := fun d w ↦ Complex.I * (ψ d w.1 w.2 : ℂ)
  let a : P → (E × E) → ℂ := fun d _ ↦ 1 - q (ρ⁻¹ • η - ζ d)
  let s : P × (E × E) → ℂ := fun p ↦ ((ρ : ℂ) ^ (2 * k))⁻¹ •
    ∑ e : CarrierJetBranch k, (ρ : ℂ) ^ carrierJetDegree e *
      carrierJetCoefficient (fun d ↦ φ d p.2) (fun d ↦ a d p.2) k v e p.1
  have hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (C ×ˢ Set.univ) :=
    contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hψ)
  have ha : ContDiffOn ℝ ∞ (Function.uncurry a) (C ×ˢ Set.univ) :=
    contDiffOn_const.sub (hq.comp_contDiffOn
      (contDiffOn_const.sub (hζ.comp contDiffOn_fst (fun _ hp ↦ hp.1))))
  have hs : ContDiffOn ℝ ∞ s (C ×ˢ Set.univ) :=
    (ContDiffOn.sum (s := Finset.univ) (fun e _ ↦ contDiffOn_const.mul
      (contDiffOn_carrierJetCoefficient_joint hC isOpen_univ hφ ha k v e))).const_smul _
  have hρ0 : ρ ≠ 0 := ne_of_gt (zero_lt_one.trans_le hρ)
  have he : (fun p : P × (E × E) ↦
      normalizedComplementaryCarrierJet A q ζ ψ ρ k v p.1 p.2.1 p.2.2 η) =ᶠ[𝓝 (c, (x, y))]
      (fun p ↦ s p • A p.2.1 p.2.2 η) := by
    filter_upwards [(hC.prod isOpen_univ).mem_nhds ⟨hc, Set.mem_univ _⟩] with p hp
    have hpψ : ContDiffOn ℝ ∞ (fun d ↦ ψ d p.2.1 p.2.2) C :=
      hψ.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hd ↦ ⟨hd, Set.mem_univ _⟩)
    rw [normalizedComplementaryCarrierJet,
      complementaryCarrierJet_eq_polynomial A hC hζ hq hρ0 k v hp.1 p.2.1 p.2.2 η hpψ,
      smul_smul]
    rfl
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
  have hprod := norm_iteratedFDerivWithin_smul_le hs
    ((hA η).comp_contDiffOn contDiffOn_snd) (hC.prod isOpen_univ).uniqueDiffOn
    (x := (c, (x, y))) ⟨hc, Set.mem_univ _⟩ (n := j) (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ (hC.prod isOpen_univ)
    (show (c, (x, y)) ∈ C ×ˢ Set.univ from ⟨hc, Set.mem_univ _⟩)] at hprod
  apply hprod.trans
  unfold complementaryFullJetBudget
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hij : i ≤ j := Finset.mem_range_succ_iff.mp hi
  have hsj := norm_iteratedFDeriv_normalizedCarrierPolynomial_joint_le hC isOpen_univ hφ ha
    H (complementarySelectorBudget Q Z) hH (complementarySelectorBudget_nonneg Q Z)
    (zero_le_one.trans hL) hρ hLρ (z := (c, (x, y))) ⟨hc, Set.mem_univ _⟩ (j + k)
    (fun t ht ↦ by
      change ‖iteratedFDeriv ℝ t (fun p : P × (E × E) ↦
        Complex.I * (ψ p.1 p.2.1 p.2.2 : ℂ)) (c, (x, y))‖ ≤ _
      rw [norm_iteratedFDeriv_imaginaryPhase
        (hψ.contDiffAt ((hC.prod isOpen_univ).mem_nhds ⟨hc, Set.mem_univ _⟩))]
      exact hψjet t ht)
    (fun t ht ↦ norm_iteratedFDeriv_complementarySelector_joint_le hC hζ hq Q Z hL hc
      (ρ⁻¹ • η) (x, y) t (fun u hu ↦ hqjet u (hu.trans ht))
      (fun u hu hut ↦ hζjet u hu (hut.trans ht))) k v i (by omega)
  have hAj := ParameterAmplitudeBudget.norm_jet_comp_contraction_le
    (ContinuousLinearMap.snd ℝ P (E × E))
    (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun p ↦ by simpa using norm_snd_le p))
    isOpen_univ ((hA η).contDiffOn.of_le (show ((j - i : ℕ) : ℕ∞ω) ≤ ∞ by simp))
    le_rfl (p := (c, (x, y))) (Set.mem_univ _)
  have hAb := hAj.trans (hAjet (j - i) (by omega))
  have hB : 0 ≤ ∑ e : CarrierJetBranch k,
      carrierCoefficientBudget H (complementarySelectorBudget Q Z) k v e i :=
    Finset.sum_nonneg fun e _ ↦
      carrierCoefficientBudget_nonneg hH (complementarySelectorBudget_nonneg Q Z) k v e i
  calc
    _ ≤ (j.choose i : ℝ) *
        ((∑ e : CarrierJetBranch k,
          carrierCoefficientBudget H (complementarySelectorBudget Q Z) k v e i) * L ^ i) *
        (R (j - i) * L ^ (b + (j - i))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hsj (Nat.cast_nonneg _)) hAb
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hB (by positivity)))
    _ = _ := by
      have hexp : i + (b + (j - i)) = b + j := by omega
      rw [← hexp, pow_add]
      ring

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.MixedGrades
