module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.PrimitiveGrades.Coordinates

/-!
# Physical base grades of the elapsed phase

In the noncomparable graph branches the frequency is physical and frozen.
The time pairing is affine in both physical positions, so all its derivatives
of order at least two vanish. The original two-time base grades therefore
supply `Pbase` with no added constant, including the bounded graph branches.
Consumer: `exists_graph_factor_sobolev_bound_of_primitive_grades`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Topology
namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization.PrimitiveGrades
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open FourierIntegral.FullAmplitudePrimitiveBudget.Local
variable {d : ℕ}

private theorem iteratedFDeriv_affine_time_zero
    (ξ : Euclidean (d + 1)) (r : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (z : Euclidean (d + 1) × Euclidean (d + 1)) :
    iteratedFDeriv ℝ (k + 1)
      (fun v : Euclidean (d + 1) × Euclidean (d + 1) => (v.1 0 - r) * ξ 0) z = 0 := by
  let l := (ξ 0) • ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (d + 1)) 0).comp
    (ContinuousLinearMap.fst ℝ (Euclidean (d + 1)) (Euclidean (d + 1))))
  have he : (fun v : Euclidean (d + 1) × Euclidean (d + 1) => (v.1 0 - r) * ξ 0) =
      fun v => l v + (-r * ξ 0) := by
    funext v
    change (v.1 0 - r) * ξ 0 = ξ 0 * v.1 0 + (-r * ξ 0)
    ring
  have hd : (fun v => fderiv ℝ (fun v => l v + (-r * ξ 0)) v) = fun _ => l := by
    funext v
    exact (l.hasFDerivAt.add_const _).fderiv
  rw [he, iteratedFDeriv_succ_eq_comp_right, hd,
    iteratedFDeriv_const_of_ne (by omega)]
  exact (continuousMultilinearCurryRightEquiv' ℝ k
    (Euclidean (d + 1) × Euclidean (d + 1)) ℝ).symm.map_zero

/-- Higher physical-base derivatives of the literal elapsed phase are
bounded by the corresponding original two-time base derivative. The lower
time remains exactly `t-r`. The open-chart inclusion is produced by the
two-time flow geometry (`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem norm_iteratedFDeriv_elapsedPhase_base_le
    {U : Set (TwoTimePoint d)} (hU : IsOpen U) (Ψ : TwoTimePhase d)
    (hΨ : ContDiffOn ℝ ∞ (jointPhase Ψ) U)
    (r : ℝ) (ξ : Euclidean (d + 1))
    (z : Euclidean (d + 1) × Euclidean (d + 1))
    (hz : elapsedPoint r (z, ξ) ∈ U) (k : ℕ) (hk : 1 ≤ k) :
    ‖iteratedFDeriv ℝ (k + 1) (fun v : Euclidean (d + 1) × Euclidean (d + 1) =>
      elapsedPhase Ψ r v.1 ξ) z‖ ≤
    ‖iteratedFDeriv ℝ (k + 1)
      (fun v : ℝ × ℝ × Euclidean d => Ψ v.1 v.2.1 v.2.2 (spatialPart ξ))
      (z.1 0, z.1 0 - r, spatialPart z.1)‖ := by
  let V := (fun v : ℝ × ℝ × Euclidean d => (v, spatialPart ξ)) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_id.prodMk continuous_const)
  let f := fun v : ℝ × ℝ × Euclidean d => Ψ v.1 v.2.1 v.2.2 (spatialPart ξ)
  have hf : ContDiffOn ℝ ∞ f V :=
    hΨ.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hv => hv)
  have hv : elapsedBaseLinear z + (0, -r, 0) ∈ V := by
    simpa [V, elapsedBaseLinear, elapsedPoint_eq, sub_eq_add_neg] using hz
  have hp := norm_iteratedFDeriv_affine_contraction_le elapsedBaseLinear
    norm_elapsedBaseLinear_le (0, -r, 0) hV hf hv (k + 1)
  have hs : ContDiffAt ℝ ∞ (fun v => f (elapsedBaseLinear v + (0, -r, 0))) z :=
    (hf.contDiffAt (hV.mem_nhds hv)).comp z
      (elapsedBaseLinear.contDiff.add contDiff_const).contDiffAt
  have ht : ContDiff ℝ ∞
      (fun v : Euclidean (d + 1) × Euclidean (d + 1) => (v.1 0 - r) * ξ 0) := by
    fun_prop
  have he : (fun v : Euclidean (d + 1) × Euclidean (d + 1) => elapsedPhase Ψ r v.1 ξ) =
      (fun v : Euclidean (d + 1) × Euclidean (d + 1) => (v.1 0 - r) * ξ 0) +
        (fun v => f (elapsedBaseLinear v + (0, -r, 0))) := by
    funext v
    simp [elapsedPhase, f, elapsedBaseLinear, sub_eq_add_neg]
  rw [he, iteratedFDeriv_add_apply (ht.contDiffAt.of_le (by simp)) (hs.of_le (by simp)),
    iteratedFDeriv_affine_time_zero ξ r k hk z, zero_add]
  simpa [f, elapsedBaseLinear, sub_eq_add_neg] using hp

/-- The physical `Pbase` input follows with the original profile, at every
physical covector, including frequencies below one. The primitive premise is
the original two-time base phase grade of `app:ch_regular:eq:high-phase`,
whose producer is the phase construction and common graded profiles. No
phase homogeneity or bound for the elapsed phase is assumed. -/
theorem elapsedPhase_physicalBase_grade
    (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k) {L : ℝ} (hL : 0 ≤ L)
    {U : Set (TwoTimePoint d)} (hU : IsOpen U) (Ψ : TwoTimePhase d)
    (hΨ : ContDiffOn ℝ ∞ (jointPhase Ψ) U)
    (hbudget : ∀ η v, (v, η) ∈ U → ∀ k, 1 ≤ k →
      ‖iteratedFDeriv ℝ (k + 1)
        (fun w : ℝ × ℝ × Euclidean d => Ψ w.1 w.2.1 w.2.2 η) v‖ ≤
          ‖η‖ * B k * L ^ k)
    (r : ℝ) (ξ : Euclidean (d + 1))
    (z : Euclidean (d + 1) × Euclidean (d + 1))
    (hz : elapsedPoint r (z, ξ) ∈ U) (k : ℕ) (hk : 1 ≤ k) :
    ‖iteratedFDeriv ℝ (k + 1) (fun v : Euclidean (d + 1) × Euclidean (d + 1) =>
      elapsedPhase Ψ r v.1 ξ) z‖ ≤ ‖ξ‖ * B k * L ^ k := by
  apply (norm_iteratedFDeriv_elapsedPhase_base_le hU Ψ hΨ r ξ z hz k hk).trans
  apply (hbudget (spatialPart ξ) (z.1 0, z.1 0 - r, spatialPart z.1)
    (by simpa only [elapsedPoint_eq] using hz) k hk).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (norm_spatialPart_le ξ) (hB k)) (pow_nonneg hL k)

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization.PrimitiveGrades
