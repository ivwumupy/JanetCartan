module

public import JanetCartan.Analysis.Operator.RetardedSobolev.Spaces.Classical

/-!
# Comparison with the classical mixed energy

The finite product norm used for the completion is equivalent to the actual
sum of squared L² derivatives in `app:ch_osc:prop:osc-retarded-tube`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff BigOperators

namespace JanetCartan.RetardedSobolev.Spaces

/-- Sum of the actual squared L² derivatives, for the measure under consideration
(`app:ch_osc:prop:osc-retarded-tube`). -/
def jetEnergy {d : ℕ} (m : ℕ) (μ : Measure ((Fin d → ℝ) × ℝ))
    (f : (ℝ × (Fin d → ℝ)) → ℂ) : ℝ :=
  ∑ i : JetIndex d m, ∫ p, ‖jet i f p‖ ^ 2 ∂μ

/-- Coordinate directions give precisely the parent's mixed energy on a time strip
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem jetEnergy_eq_mixedSobolevEnergy {d : ℕ} (m : ℕ)
    (ν : Measure (Fin d → ℝ)) (a b : ℝ) (f : (ℝ × (Fin d → ℝ)) → ℂ) :
    jetEnergy m (ν.prod (volume.restrict (Icc a b))) f =
      mixedSobolevEnergy (fun i : Fin d ↦ Pi.single i 1) ν a b m f := by
  simp only [jetEnergy, Fintype.sum_sigma, Fintype.sum_prod_type, jet,
    mixedSobolevEnergy, timeSobolevEnergy, Function.comp_def]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro word _
  exact Fin.sum_univ_eq_sum_range (fun j ↦ ∫ p : (Fin d → ℝ) × ℝ,
    ‖timeJet j (transverseJet (List.ofFn (fun q ↦ Pi.single (word q) 1)) f)
      (p.2, p.1)‖ ^ 2 ∂ν.prod (volume.restrict (Icc a b))) (m - k.val + 1)

private theorem tsupport_timeJet_subset {d : ℕ} {f : ℝ × (Fin d → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (j : ℕ) : tsupport (timeJet j f) ⊆ tsupport f := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [timeJet_succ, timeDeriv_eq_fderiv ((contDiff_timeJet hf j).differentiable (by simp))]
    exact (tsupport_fderiv_apply_subset ℝ (1, 0)).trans ih

private theorem tsupport_transverseJet_subset {d : ℕ} {f : ℝ × (Fin d → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (vs : List (Fin d → ℝ)) :
    tsupport (transverseJet vs f) ⊆ tsupport f := by
  induction vs with
  | nil => exact Subset.rfl
  | cons v vs ih =>
    rw [transverseJet, transverseDeriv_eq_fderiv v
      ((contDiff_transverseJet hf vs).differentiable (by simp))]
    exact (tsupport_fderiv_apply_subset ℝ (0, v)).trans ih

/-- Every mixed jet vanishes off the support of the smooth field
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem jet_eq_zero_off_tsupport {d m : ℕ} (i : JetIndex d m)
    {f : ℝ × (Fin d → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (p : (Fin d → ℝ) × ℝ) (hp : (p.2, p.1) ∉ tsupport f) : jet i f p = 0 := by
  have hs := (tsupport_timeJet_subset (contDiff_transverseJet hf
    (List.ofFn (fun j ↦ Pi.single (i.2.1 j) 1))) i.2.2.val).trans
      (tsupport_transverseJet_subset hf _)
  exact Function.notMem_support.mp (fun h ↦ hp (hs (subset_tsupport _ h)))

/-- For smooth fields supported in the time strip, the global derivative energy
is exactly the parent's mixed energy (`app:ch_osc:prop:osc-retarded-tube`). This
passes cutoff estimates on a strip to the ambient completion. -/
theorem jetEnergy_prod_eq_mixedSobolevEnergy_of_support {d : ℕ} (m : ℕ)
    (ν : Measure (Fin d → ℝ)) [SFinite ν] (a b : ℝ)
    {f : ℝ × (Fin d → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : tsupport f ⊆ Icc a b ×ˢ univ) :
    jetEnergy m (ν.prod volume) f =
      mixedSobolevEnergy (fun i : Fin d ↦ Pi.single i 1) ν a b m f := by
  rw [← jetEnergy_eq_mixedSobolevEnergy]
  unfold jetEnergy
  apply Finset.sum_congr rfl
  intro i _
  have hμ : (ν.prod volume).restrict (univ ×ˢ Icc a b) =
      ν.prod (volume.restrict (Icc a b)) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [← hμ]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  have hz := jet_eq_zero_off_tsupport i hf p (fun h ↦ hp ⟨mem_univ _, (hs h).1⟩)
  simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)]

/-- The L² norm of each classical jet is its actual integral energy
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem norm_jetMap_apply_sq {d m : ℕ} (μ : Measure ((Fin d → ℝ) × ℝ))
    [IsFiniteMeasureOnCompacts μ] (f : Test d) (i : JetIndex d m) :
    ‖jetMap m μ f i‖ ^ 2 = ∫ p, ‖jet i f p‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(jet_memLp μ i f).coeFn_toLp] with p hp
  simp [jetMap, hp]

/-- Exact sum formula for the actual derivative energy
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem jetEnergy_eq_sum_norm_sq {d : ℕ} (m : ℕ) (μ : Measure ((Fin d → ℝ) × ℝ))
    [IsFiniteMeasureOnCompacts μ] (f : Test d) :
    jetEnergy m μ f = ∑ i : JetIndex d m, ‖jetMap m μ f i‖ ^ 2 := by
  simp only [jetEnergy, norm_jetMap_apply_sq]

/-- Comparison constants for the finite product norm and the derivative energy
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem jetMap_norm_comparison {d : ℕ} (m : ℕ) (μ : Measure ((Fin d → ℝ) × ℝ))
    [IsFiniteMeasureOnCompacts μ] (f : Test d) :
    ‖jetMap m μ f‖ ^ 2 ≤ jetEnergy m μ f ∧
      jetEnergy m μ f ≤ (Fintype.card (JetIndex d m) : ℝ) * ‖jetMap m μ f‖ ^ 2 := by
  rw [jetEnergy_eq_sum_norm_sq]
  constructor
  · have hn : 0 ≤ ∑ i : JetIndex d m, ‖jetMap m μ f i‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    have hb : ‖jetMap m μ f‖ ≤ Real.sqrt (∑ i : JetIndex d m, ‖jetMap m μ f i‖ ^ 2) := by
      apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
      intro i
      have hi := Finset.single_le_sum (f := fun i : JetIndex d m ↦ ‖jetMap m μ f i‖ ^ 2)
        (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i)
      nlinarith [Real.sq_sqrt hn, Real.sqrt_nonneg (∑ i : JetIndex d m, ‖jetMap m μ f i‖ ^ 2),
        norm_nonneg (jetMap m μ f i)]
    nlinarith [Real.sq_sqrt hn, norm_nonneg (jetMap m μ f)]
  · calc
      _ ≤ ∑ _i : JetIndex d m, ‖jetMap m μ f‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm _ i) _
      _ = _ := by simp

/-- A classical derivative-energy estimate yields the precise norm bound needed
by completion (`app:ch_osc:prop:osc-retarded-tube`). -/
theorem jetMap_bound_of_energy_bound {d e m n : ℕ}
    (μ : Measure ((Fin d → ℝ) × ℝ)) (ν : Measure ((Fin e → ℝ) × ℝ))
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (T : Test d →ₗ[ℂ] Test e) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ f, jetEnergy n ν (T f) ≤ C * jetEnergy m μ f) (f : Test d) :
    ‖jetMap n ν (T f)‖ ≤
      Real.sqrt (C * (Fintype.card (JetIndex d m) : ℝ)) * ‖jetMap m μ f‖ := by
  have h := (jetMap_norm_comparison n ν (T f)).1.trans ((hT f).trans
    (mul_le_mul_of_nonneg_left (jetMap_norm_comparison m μ f).2 hC))
  have hs := Real.sq_sqrt (show 0 ≤ C * (Fintype.card (JetIndex d m) : ℝ) by positivity)
  have hp : 0 ≤ Real.sqrt (C * (Fintype.card (JetIndex d m) : ℝ)) * ‖jetMap m μ f‖ := by
    positivity
  nlinarith [sq_nonneg (‖jetMap n ν (T f)‖ -
    Real.sqrt (C * (Fintype.card (JetIndex d m) : ℝ)) * ‖jetMap m μ f‖)]

end JanetCartan.RetardedSobolev.Spaces
