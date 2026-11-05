module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.FullNormalKernel.Adjoint

/-!
# Absolute convergence of compact cross kernels

The Fubini prerequisite for `app:ch_osc:eq:osc-exact-normal-kernel` and
`app:ch_osc:prop:osc-normal`. The two kernels may differ, as required for
parameter derivatives of the normal operator.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace JanetCartan.NormalComparison

variable {d m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "U" => EuclideanSpace ℝ (Fin m)

/-- Absolute integrability of the full cross-kernel weight in
`app:ch_osc:eq:osc-exact-normal-kernel`. Compact projections localize both
inputs; the parameter domain can have infinite measure. -/
theorem integrable_compactCrossKernel_weight
    (D : Set U) {s t : E → U → ℂ}
    (hcS : Continuous (Function.uncurry s))
    (hsS : HasCompactSupport (Function.uncurry s))
    (hcT : Continuous (Function.uncurry t))
    (hsT : HasCompactSupport (Function.uncurry t))
    (g : Lp ℂ ∞ (volume.restrict D)) (f : Lp (α := E) ℂ 2) (x : E) :
    Integrable (fun p : E × U ↦ s x p.2 * star (t p.1 p.2) * g p.2 * f p.1)
      (volume.prod (volume.restrict D)) := by
  let X := Prod.fst '' tsupport (Function.uncurry t)
  let V := Prod.snd '' tsupport (Function.uncurry t)
  have hX : IsCompact X := hsT.image continuous_fst
  have hV : IsCompact V := hsT.image continuous_snd
  have hfi := ((Lp.memLp f).locallyIntegrable (by norm_num)).integrableOn_isCompact hX
    |>.integrable_indicator hX.measurableSet
  have hgi := ((Lp.memLp g).locallyIntegrable (by simp)).integrableOn_isCompact hV
    |>.integrable_indicator hV.measurableSet
  obtain ⟨A, hA⟩ := hsS.exists_bound_of_continuous hcS
  obtain ⟨B, hB⟩ := hsT.exists_bound_of_continuous hcT
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA (0, 0))
  have hm : Continuous (fun p : E × U ↦ s x p.2 * star (t p.1 p.2)) :=
    (hcS.comp (continuous_const.prodMk continuous_snd)).mul hcT.star
  have hb : ∀ p : E × U, ‖s x p.2 * star (t p.1 p.2)‖ ≤ A * B := by
    intro p
    rw [norm_mul, norm_star]
    exact mul_le_mul (hA (x, p.2)) (hB p) (norm_nonneg _) hA0
  apply ((hfi.mul_prod hgi).bdd_mul hm.aestronglyMeasurable
    (Eventually.of_forall hb)).congr
  apply Eventually.of_forall
  intro p
  by_cases hp : t p.1 p.2 = 0
  · simp [hp]
  · have hpK := subset_tsupport (Function.uncurry t) hp
    have hpX : p.1 ∈ X := ⟨p, hpK, rfl⟩
    have hpV : p.2 ∈ V := ⟨p, hpK, rfl⟩
    simp only [Set.indicator_of_mem hpX, Set.indicator_of_mem hpV]
    ring

/-- Every parameter section of the cross kernel is absolutely convergent,
with both physical positions independent (`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem integrable_compactCrossKernel_section
    (D : Set U) {s t : E → U → ℂ}
    (hcS : Continuous (Function.uncurry s))
    (hsS : HasCompactSupport (Function.uncurry s))
    (hcT : Continuous (Function.uncurry t))
    (hsT : HasCompactSupport (Function.uncurry t))
    (g : Lp ℂ ∞ (volume.restrict D)) (x y : E) :
    Integrable (fun u ↦ s x u * star (t y u) * g u) (volume.restrict D) := by
  let V := Prod.snd '' tsupport (Function.uncurry t)
  have hV : IsCompact V := hsT.image continuous_snd
  have hgi := ((Lp.memLp g).locallyIntegrable (by simp)).integrableOn_isCompact hV
    |>.integrable_indicator hV.measurableSet
  obtain ⟨A, hA⟩ := hsS.exists_bound_of_continuous hcS
  obtain ⟨B, hB⟩ := hsT.exists_bound_of_continuous hcT
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA (0, 0))
  have hm : Continuous (fun u ↦ s x u * star (t y u)) :=
    (hcS.comp (continuous_const.prodMk continuous_id)).mul
      (hcT.comp (continuous_const.prodMk continuous_id)).star
  have hb : ∀ u, ‖s x u * star (t y u)‖ ≤ A * B := by
    intro u
    rw [norm_mul, norm_star]
    exact mul_le_mul (hA (x, u)) (hB (y, u)) (norm_nonneg _) hA0
  apply (hgi.bdd_mul hm.aestronglyMeasurable (Eventually.of_forall hb)).congr
  apply Eventually.of_forall
  intro u
  by_cases hu : t y u = 0
  · simp [hu]
  · have huV : u ∈ V := ⟨(y, u), subset_tsupport (Function.uncurry t) hu, rfl⟩
    simp only [Set.indicator_of_mem huV]

/-- Integrability in the original composition order, needed to distribute the
finite vector sum in `app:ch_osc:prop:osc-normal`. -/
theorem integrable_compactCrossKernel_adjoint_integral
    (D : Set U) {s t : E → U → ℂ}
    (hcS : Continuous (Function.uncurry s))
    (hsS : HasCompactSupport (Function.uncurry s))
    (hcT : Continuous (Function.uncurry t))
    (hsT : HasCompactSupport (Function.uncurry t))
    (g : Lp ℂ ∞ (volume.restrict D)) (f : Lp (α := E) ℂ 2) (x : E) :
    Integrable (fun u ↦ s x u * (g u * ∫ y, star (t y u) * f y))
      (volume.restrict D) := by
  convert (integrable_compactCrossKernel_weight D hcS hsS hcT hsT g f x).integral_prod_right
    using 1
  funext u
  rw [← integral_const_mul, ← integral_const_mul]
  congr 1
  funext y
  ring

/-- The outer physical integral is absolutely convergent for every output
position in `app:ch_osc:eq:osc-exact-normal-kernel`. -/
theorem integrable_compactCrossKernel_action
    (D : Set U) {s t : E → U → ℂ}
    (hcS : Continuous (Function.uncurry s))
    (hsS : HasCompactSupport (Function.uncurry s))
    (hcT : Continuous (Function.uncurry t))
    (hsT : HasCompactSupport (Function.uncurry t))
    (g : Lp ℂ ∞ (volume.restrict D)) (f : Lp (α := E) ℂ 2) (x : E) :
    Integrable (fun y ↦ (∫ u in D, s x u * star (t y u) * g u) * f y) := by
  simpa only [integral_mul_const] using
    (integrable_compactCrossKernel_weight D hcS hsS hcT hsT g f x).integral_prod_left

/-- Fubini changes the actual composition order to the literal full kernel
order in `app:ch_osc:eq:osc-exact-normal-kernel`. -/
theorem integral_compactCrossKernel_swap
    (D : Set U) {s t : E → U → ℂ}
    (hcS : Continuous (Function.uncurry s))
    (hsS : HasCompactSupport (Function.uncurry s))
    (hcT : Continuous (Function.uncurry t))
    (hsT : HasCompactSupport (Function.uncurry t))
    (g : Lp ℂ ∞ (volume.restrict D)) (f : Lp (α := E) ℂ 2) (x : E) :
    (∫ u in D, s x u * (g u * ∫ y, star (t y u) * f y)) =
      ∫ y, (∫ u in D, s x u * star (t y u) * g u) * f y := by
  calc
    _ = ∫ u in D, ∫ y, s x u * star (t y u) * g u * f y := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro u
      dsimp only
      rw [← integral_const_mul, ← integral_const_mul]
      congr 1
      funext y
      ring
    _ = ∫ y, ∫ u in D, s x u * star (t y u) * g u * f y :=
      (integral_integral_swap
        (integrable_compactCrossKernel_weight D hcS hsS hcT hsT g f x)).symm
    _ = _ := by simp only [integral_mul_const]

end JanetCartan.NormalComparison
