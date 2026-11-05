module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.Expansion

/-!
# Actual finite sum of compact oscillatory integrals

The finite sum after `paper-v2.tex`, `new:eq:carrier-ibp`, with integrability
proved separately for each amplitude/input branch. This lets the consumer of
`app:ch_response:eq:direct-envelope-profile` apply its fixed-phase low estimate
to each actual branch. No operator estimate is used here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer

variable {n : ℕ} {P M V F ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup M] [NormedSpace ℝ M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [Fintype ι]

/-- Each enumerated oscillatory term is integrable on the actual joint
Lebesgue space, using the original compact support and local smoothness.
Source: the finite sum following `new:eq:carrier-ibp`. -/
theorem integrable_oscillation_jointTransferTerm
    (b : OrthonormalBasis ι ℝ (CarrierVariables n)) (B : M →L[ℝ] V →L[ℝ] F)
    {f : (Euclidean n × P) → CarrierVariables n → ℝ}
    {w₀ : (Euclidean n × P) → CarrierVariables n}
    {U : Set (Euclidean n × P)} {D K : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    {α : (Euclidean n × P) → CarrierVariables n → M} {a : Euclidean n × P → V}
    (hα : ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D)) (ha : ContDiff ℝ ∞ a)
    (hs : ∀ q ∈ U, Function.support (α q) ⊆ K)
    (hA : ∀ e, ContDiffOn ℝ ∞ (Function.uncurry (transferCoefficient f w₀ e)) (U ×ˢ D))
    (ρ : ℝ) (es : List (Euclidean n × P)) (t : JointTransferTerm n P M ι)
    (ht : t ∈ jointTransferTerms b es) {q : Euclidean n × P} (hq : q ∈ U) :
    Integrable (fun w => oscillation f ρ q w • jointTransferTermValue b B f w₀ α a t q w) := by
  have hj := (contDiffOn_oscillation hf ρ).smul
    (contDiffOn_jointTransferTermValue b B hU hD hα hA ha t)
  apply integrable_of_support_subset hD hK hKD
    (hj.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hw => ⟨hq, hw⟩))
  exact (Function.support_smul_subset_right _ _).trans
    (support_jointTransferTermValue b B f w₀ a hU hK.isClosed hs es t ht q hq)

omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] in
private theorem integral_list_sum {J : Type} (l : List J) (g : J → CarrierVariables n → F)
    (hg : ∀ t ∈ l, Integrable (g t)) :
    Integrable (fun w => (l.map fun t => g t w).sum) ∧
      (∫ w, (l.map fun t => g t w).sum) = (l.map fun t => ∫ w, g t w).sum := by
  induction l with
  | nil => simp
  | cons t ts ih =>
    obtain ⟨his, he⟩ := ih (fun u hu => hg u (by simp [hu]))
    have hit := hg t (by simp)
    simp only [List.map_cons, List.sum_cons]
    exact ⟨hit.add his, (integral_add hit his).trans (congrArg (fun x => (∫ w, g t w) + x) he)⟩

/-- Splitting the finite expansion into actual integrals is justified by
compact support, with multiplicities preserved. Combined with
`orderedTransferAction_integral_eq_jointTransferTerms` and
`jointTransferTerms_order_budget`, this is the finite identity and exact
`k+j=q` count used after `new:eq:carrier-ibp`. -/
theorem integral_oscillation_jointTransferTerms_eq_sum
    (b : OrthonormalBasis ι ℝ (CarrierVariables n)) (B : M →L[ℝ] V →L[ℝ] F)
    {f : (Euclidean n × P) → CarrierVariables n → ℝ}
    {w₀ : (Euclidean n × P) → CarrierVariables n}
    {U : Set (Euclidean n × P)} {D K : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    {α : (Euclidean n × P) → CarrierVariables n → M} {a : Euclidean n × P → V}
    (hα : ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D)) (ha : ContDiff ℝ ∞ a)
    (hs : ∀ q ∈ U, Function.support (α q) ⊆ K)
    (hA : ∀ e, ContDiffOn ℝ ∞ (Function.uncurry (transferCoefficient f w₀ e)) (U ×ˢ D))
    (ρ : ℝ) (es : List (Euclidean n × P)) {q : Euclidean n × P} (hq : q ∈ U) :
    (∫ w, oscillation f ρ q w •
      ((jointTransferTerms b es).map fun t => jointTransferTermValue b B f w₀ α a t q w).sum) =
    ((jointTransferTerms b es).map fun t =>
      ∫ w, oscillation f ρ q w • jointTransferTermValue b B f w₀ α a t q w).sum := by
  have he (l : List (JointTransferTerm n P M ι)) (w : CarrierVariables n) :
      oscillation f ρ q w • (l.map fun t => jointTransferTermValue b B f w₀ α a t q w).sum =
        (l.map fun t => oscillation f ρ q w • jointTransferTermValue b B f w₀ α a t q w).sum := by
    induction l with
    | nil => simp
    | cons t ts ih => simp only [List.map_cons, List.sum_cons, smul_add, ih]
  simp_rw [he]
  exact (integral_list_sum _ _ (fun t ht =>
    integrable_oscillation_jointTransferTerm b B hU hD hK hKD hf hα ha hs hA ρ es t ht hq)).2

end JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer
