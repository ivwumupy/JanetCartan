module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.SymbolBounds.PrimitiveBounds

/-!
# Joint spatial and frequency jets of primitive adjoint expressions

For `app:ch_background:prop:bg-adjoint`, the fixed symbol reserve includes
frequency derivatives. Smoothness is local, allowing the normalized angular
factor to be singular at zero. The expression still differentiates only in
carrier/measurement directions; frequency variables enter through its primitive.
-/

@[expose] public noncomputable section
open scoped ContDiff
open Filter Topology
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow
variable {n : ℕ}

/-- Variables for the full symbol reserve in `app:ch_background:prop:bg-adjoint`. -/
abbrev AdjointSymbolPoint (n : ℕ) := AdjointJetPoint n × Euclidean (n-1)

/-- Local Leibniz bound used for the angular jets in
`app:ch_background:prop:bg-adjoint`. -/
theorem adjoint_local_product_jet_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : E → ℂ} {p : E} (q : ℕ)
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p) :
    ‖iteratedFDeriv ℝ q (fun y ↦ f y * g y) p‖ ≤
      ∑ i ∈ Finset.range (q+1), (q.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f p‖ * ‖iteratedFDeriv ℝ (q-i) g p‖ := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn (m := (q : ℕ∞ω)) (by simp) (by simp)
  obtain ⟨v, hv, hgv⟩ := hg.contDiffOn (m := (q : ℕ∞ω)) (by simp) (by simp)
  obtain ⟨w, hw, hwo, hpw⟩ := mem_nhds_iff.mp (inter_mem hu hv)
  have hfw := hfu.mono (hw.trans Set.inter_subset_left)
  have hgw := hgv.mono (hw.trans Set.inter_subset_right)
  have h := norm_iteratedFDerivWithin_mul_le hfw hgw hwo.uniqueDiffOn hpw (le_refl (q : ℕ∞ω))
  simpa only [iteratedFDerivWithin_of_isOpen _ hwo hpw] using h

/-- Adding the frequency variable does not increase a spatial primitive jet.
This supplies the eta-independent L,V, flow, and scalar-graph profiles in the
full symbol reserve of `app:ch_background:prop:bg-adjoint`. -/
theorem adjoint_spatial_jet_lift_bound {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : AdjointJetPoint n → F) (hf : ContDiff ℝ ∞ f)
    (q : ℕ) (p : AdjointSymbolPoint n) :
    ‖iteratedFDeriv ℝ q (fun p : AdjointSymbolPoint n ↦ f p.1) p‖ ≤
      ‖iteratedFDeriv ℝ q f p.1‖ := by
  let pr := ContinuousLinearMap.fst ℝ (AdjointJetPoint n) (Euclidean (n-1))
  have hpr : ‖pr‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    change ‖v.1‖ ≤ 1 * max ‖v.1‖ ‖v.2‖
    simpa only [one_mul] using le_max_left ‖v.1‖ ‖v.2‖
  change ‖iteratedFDeriv ℝ q (f ∘ pr) p‖ ≤ _
  rw [pr.iteratedFDeriv_comp_right hf p (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  have hp : (∏ _ : Fin q, ‖pr‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ hpr)
  simpa [pr] using mul_le_mul_of_nonneg_left hp
    (norm_nonneg (iteratedFDeriv ℝ q f p.1))

namespace AdjointCoefficientExpression

/-- Evaluate with frequency included in the domain of the jets; a derivative
node remains in direction `(h,0)` (`app:ch_background:eq:bg-derivative-trade`). -/
def evaluateSymbol
    (L : CarrierParameter → Euclidean n → Euclidean (n-1) → Euclidean n)
    (V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n) (a : AdjointAmplitude n) :
    AdjointCoefficientExpression n → AdjointSymbolPoint n → ℂ
  | .amplitude => fun p ↦ a p.1.1 p.1.2 p.2
  | .field d j => fun p ↦ branchField L V d j p.1
  | .add e f => fun p ↦ e.evaluateSymbol L V a p + f.evaluateSymbol L V a p
  | .neg e => fun p ↦ -e.evaluateSymbol L V a p
  | .mul e f => fun p ↦ e.evaluateSymbol L V a p * f.evaluateSymbol L V a p
  | .deriv h e => fun p ↦ fderiv ℝ (e.evaluateSymbol L V a) p (h,0)

/-- Joint smoothness is inherited locally from the primitive amplitude and
eta-independent fields (`app:ch_background:prop:bg-adjoint`). -/
theorem contDiffAt_evaluateSymbol (L V a) (p : AdjointSymbolPoint n)
    (ha : ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦ a p.1.1 p.1.2 p.2) p)
    (hfield : ∀ d j, ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦
      branchField L V d j p.1) p)
    (e : AdjointCoefficientExpression n) : ContDiffAt ℝ ∞ (e.evaluateSymbol L V a) p := by
  induction e with
  | amplitude => exact ha
  | field d j => exact hfield d j
  | add e f he hf => exact he.add hf
  | neg e he => exact he.neg
  | mul e f he hf => exact he.mul hf
  | deriv h e he => exact (he.fderiv_right (by simp)).clm_apply contDiffAt_const

/-- Joint evaluation agrees with the actual coefficient expression at every
frequency where the primitive is smooth (`app:ch_background:prop:bg-adjoint`). -/
theorem evaluateSymbol_eq_evaluate (L V a) (η : Euclidean (n-1))
    (ha : ∀ p, ContDiffAt ℝ ∞
      (fun p : AdjointSymbolPoint n ↦ a p.1.1 p.1.2 p.2) (p,η))
    (hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j))
    (e : AdjointCoefficientExpression n) (p : AdjointJetPoint n) :
    e.evaluateSymbol L V a (p,η) = e.evaluate L V a η p := by
  induction e generalizing p with
  | amplitude | field => rfl
  | add e f he hf => exact congrArg₂ (· + ·) (he p) (hf p)
  | neg e he => exact congrArg Neg.neg (he p)
  | mul e f he hf => exact congrArg₂ (· * ·) (he p) (hf p)
  | deriv h e he =>
      have hs := e.contDiffAt_evaluateSymbol L V a (p,η) (ha p)
        (fun d j ↦ (hfield d j).contDiffAt.comp _ contDiffAt_fst)
      have hi : HasFDerivAt (fun v : AdjointJetPoint n ↦ (v,η))
          ((ContinuousLinearMap.id ℝ (AdjointJetPoint n)).prod 0) p :=
        (hasFDerivAt_id p).prodMk (hasFDerivAt_const η p)
      have hd := (hs.differentiableAt (by simp)).hasFDerivAt.comp p hi
      have heq : (fun p ↦ e.evaluateSymbol L V a (p,η)) = e.evaluate L V a η := funext he
      have hd' := congrArg (fun A : AdjointJetPoint n →L[ℝ] ℂ ↦ A h) hd.fderiv
      simpa [evaluateSymbol, evaluate, Function.comp_def, heq] using hd'.symm

/-- Primitive interpolation profiles imply mixed-jet bounds, with exactly
`degree + q` in the exponent. Only primitive jets through that order are
required. This is the one-high budget in
`app:ch_background:prop:bg-adjoint`, before geometric instantiation. -/
theorem norm_iteratedFDeriv_evaluateSymbol_le_profile (L V a)
    (p : AdjointSymbolPoint n)
    (ha : ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦ a p.1.1 p.1.2 p.2) p)
    (hfield : ∀ d j, ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦ branchField L V d j p.1) p) (R : ℕ) (B : ℕ → ℝ) (hB : ∀ q, 0 ≤ B q)
    {H T : ℝ} (hH : 1 ≤ H) (hT : 0 < T)
    (hamp : ∀ i ≤ R, ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦ a p.1.1 p.1.2 p.2) p‖ ≤
      B i * H ^ ((i : ℝ) / T))
    (ds : List (InitialCarrierDerivative n))
    (hcoeff : ∀ d ∈ ds, ∀ j i, i ≤ R → ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦ branchField L V d j p.1) p‖ ≤
      B i * H ^ ((i : ℝ) / T))
    (e : AdjointCoefficientExpression n) (hdirs : e.UsesDirections ds)
    (q : ℕ) (hq : e.degree + q ≤ R) :
    ‖iteratedFDeriv ℝ q (e.evaluateSymbol L V a) p‖ ≤
      e.jetConstant B q * H ^ (((e.degree + q : ℕ) : ℝ) / T) := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have smooth (e : AdjointCoefficientExpression n) := contDiffAt_evaluateSymbol L V a p ha hfield e
  have mono (e : AdjointCoefficientExpression n) (q b : ℕ) (hb : e.degree + q ≤ b) :
      e.jetConstant B q * H ^ (((e.degree + q : ℕ) : ℝ) / T) ≤
        e.jetConstant B q * H ^ ((b : ℝ) / T) := by
    apply mul_le_mul_of_nonneg_left _ (jetConstant_nonneg B hB e q)
    apply Real.rpow_le_rpow_of_exponent_le hH
    exact div_le_div_of_nonneg_right (by exact_mod_cast hb) hT.le
  induction e generalizing q with
  | amplitude => simpa [evaluateSymbol, degree, jetConstant] using hamp q (by simpa [degree] using hq)
  | field d j =>
      simpa [evaluateSymbol, degree, jetConstant] using
        hcoeff d hdirs j q (by simpa [degree] using hq)
  | add e f he hf =>
      have hqe : e.degree + q ≤ R := (Nat.add_le_add_right (le_max_left _ _) q).trans hq
      have hqf : f.degree + q ≤ R := (Nat.add_le_add_right (le_max_right _ _) q).trans hq
      have he' := (he hdirs.1 q hqe).trans (mono e q _
        (Nat.add_le_add_right (le_max_left e.degree f.degree) q))
      have hf' := (hf hdirs.2 q hqf).trans (mono f q _
        (Nat.add_le_add_right (le_max_right e.degree f.degree) q))
      dsimp only [evaluateSymbol]
      rw [show (fun p ↦ e.evaluateSymbol L V a p + f.evaluateSymbol L V a p) =
          e.evaluateSymbol L V a + f.evaluateSymbol L V a from rfl,
        iteratedFDeriv_add_apply ((smooth e).of_le (by simp)) ((smooth f).of_le (by simp))]
      exact (norm_add_le _ _).trans ((add_le_add he' hf').trans_eq (by
        simp only [jetConstant, degree, add_mul]))
  | neg e he =>
      change ‖iteratedFDeriv ℝ q (-e.evaluateSymbol L V a) p‖ ≤ _
      rw [iteratedFDeriv_neg]
      simpa only [Pi.neg_apply, norm_neg, degree, jetConstant] using he hdirs q hq
  | mul e f he hf =>
      apply (adjoint_local_product_jet_bound q (smooth e) (smooth f)).trans
      simp only [jetConstant, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      have hiq : i ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hqe : e.degree + i ≤ R := by simp only [degree] at hq; omega
      have hqf : f.degree + (q-i) ≤ R := by simp only [degree] at hq; omega
      calc
        _ ≤ (q.choose i : ℝ) *
            (e.jetConstant B i * H ^ (((e.degree + i : ℕ) : ℝ) / T)) *
            (f.jetConstant B (q-i) * H ^ (((f.degree + (q-i) : ℕ) : ℝ) / T)) := by
          apply mul_le_mul
            (mul_le_mul_of_nonneg_left (he hdirs.1 i hqe) (Nat.cast_nonneg _))
            (hf hdirs.2 (q-i) hqf)
            (norm_nonneg _)
          exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
            (jetConstant_nonneg B hB e i) (Real.rpow_nonneg hHpos.le _))
        _ = _ := by
          simp only [degree, Nat.cast_add, Nat.cast_sub hiq]
          rw [show (q.choose i : ℝ) * (e.jetConstant B i * H ^ ((e.degree + i) / T)) *
              (f.jetConstant B (q-i) * H ^ ((f.degree + (q-i)) / T)) =
              ((q.choose i : ℝ) * e.jetConstant B i * f.jetConstant B (q-i)) *
                (H ^ ((e.degree + i) / T) * H ^ ((f.degree + (q-i)) / T)) by ring,
            ← Real.rpow_add hHpos]
          congr 2
          ring
  | deriv h e he =>
      have hqe : e.degree + (q+1) ≤ R := by simpa [degree, Nat.add_assoc, Nat.add_comm 1] using hq
      have hd := norm_iteratedFDeriv_clm_apply_const
        ((smooth e).fderiv_right (by simp))
        (show (q : ℕ∞ω) ≤ ∞ by simp) (c := (h, (0 : Euclidean (n-1)))) (x := p)
      rw [norm_iteratedFDeriv_fderiv] at hd
      rw [show ‖(h, (0 : Euclidean (n-1)))‖ = ‖h‖ by
        change max ‖h‖ ‖(0 : Euclidean (n-1))‖ = ‖h‖
        rw [norm_zero, max_eq_left (norm_nonneg h)]] at hd
      exact hd.trans ((mul_le_mul_of_nonneg_left (he hdirs (q+1) hqe) (norm_nonneg h)).trans_eq
        (by simp [jetConstant, degree, Nat.add_assoc, Nat.add_comm 1, mul_assoc]))


/-- Frequency reparametrization changes only the original primitive, since
all expression derivatives are spatial (`app:ch_background:prop:bg-adjoint`). -/
theorem evaluate_frequency_reparam (L V a) (ν : Euclidean (n-1) → Euclidean (n-1))
    (e : AdjointCoefficientExpression n) (η : Euclidean (n-1)) :
    e.evaluate L V (fun z x ξ ↦ a z x (ν ξ)) η = e.evaluate L V a (ν η) := by
  induction e with
  | amplitude | field => rfl
  | add e f he hf | mul e f he hf => simp only [evaluate, he, hf]
  | neg e he | deriv h e he => simp only [evaluate, he]

/-- Local identity with the actual frequency-dependent expression; this
allows transfer of all symbol jets, not only values
(`app:ch_background:prop:bg-adjoint`). -/
theorem evaluateSymbol_eventuallyEq (L V a)
    (ν : Euclidean (n-1) → Euclidean (n-1))
    (U : Set (Euclidean (n-1))) (hU : IsOpen U)
    (ha : ∀ η ∈ U, ∀ p, ContDiffAt ℝ ∞
      (fun p : AdjointSymbolPoint n ↦ a p.1.1 p.1.2 (ν p.2)) (p,η))
    (hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j))
    (e : AdjointCoefficientExpression n) (p : AdjointSymbolPoint n) (hp : p.2 ∈ U) :
    e.evaluateSymbol L V (fun z x η ↦ a z x (ν η)) =ᶠ[𝓝 p]
      (fun p : AdjointSymbolPoint n ↦ e.evaluate L V a (ν p.2) p.1) := by
  filter_upwards [(continuous_snd.isOpen_preimage U hU).mem_nhds hp] with v hv
  rw [e.evaluateSymbol_eq_evaluate L V _ v.2 (ha v.2 hv) hfield,
    e.evaluate_frequency_reparam]

end AdjointCoefficientExpression
end JanetCartan.ContinuumAdjoint.DerivativeKernels
