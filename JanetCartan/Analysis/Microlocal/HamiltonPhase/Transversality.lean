module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.LocalChart

/-!
# Transversality of the Hamilton projection

The initial derivative in `app:lem:common-hamilton-phase` is invertible
because the Hamilton velocity is transverse to the initial hyperplane.
The section is an isometry onto the normal vector’s orthogonal hyperplane.
-/

open Set Filter
open scoped Topology InnerProductSpace
@[expose] public noncomputable section
namespace JanetCartan.HamiltonPhase
variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- The columns `h_ξ, j` are bijective when the velocity has nonzero normal
component and `j` parametrizes the whole section (`app:lem:common-hamilton-phase`). -/
theorem flowDifferential_bijective_of_transverse
    (j : U →ₗᵢ[ℝ] E) (ν : E)
    (horth : ∀ u : U, ⟪ν, j u⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    {v : E} (hv : ⟪ν, v⟫_ℝ ≠ 0) :
    Function.Bijective (flowDifferential v j.toContinuousLinearMap) := by
  constructor
  · intro a b hab
    have ht : a.1 = b.1 := by
      have he := congrArg (fun x : E ↦ ⟪ν, x⟫_ℝ) hab
      simp only [flowDifferential_apply, LinearIsometry.coe_toContinuousLinearMap,
        inner_add_right, inner_smul_right, horth, add_zero] at he
      exact mul_right_cancel₀ hv he
    have hu : a.2 = b.2 := by
      apply j.injective
      simpa only [flowDifferential_apply, LinearIsometry.coe_toContinuousLinearMap, ht, add_right_inj] using hab
    exact Prod.ext ht hu
  · intro x
    let t := ⟪ν, x⟫_ℝ / ⟪ν, v⟫_ℝ
    obtain ⟨u, hu⟩ := hspan (x - t • v) (by
      simp [inner_sub_right, inner_smul_right, t, hv])
    exact ⟨(t, u), by simp [flowDifferential_apply, hu]⟩

variable [CompleteSpace E] [CompleteSpace U] {H : HomogeneousSymbol E} (Φ : HamiltonFlow H U)

/-- The augmented projection has an invertible derivative at the initial
section, derived from the transverse velocity (`app:lem:common-hamilton-phase`). -/
theorem HamiltonFlow.exists_initialAugmentedProjectionEquiv
    (j : U →ₗᵢ[ℝ] E) (hj : Φ.sectionMap = j.toContinuousLinearMap)
    (ν : E) (horth : ∀ u : U, ⟪ν, j u⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    {s : InitialData U} (hs : s ∈ Φ.parameters)
    (hv : ⟪ν, H.hp (j s.1, Φ.momentum (0, s))⟫_ℝ ≠ 0) :
    ∃ A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U)),
      HasFDerivAt Φ.augmentedProjection (A : _ →L[ℝ] _) (0, s) := by
  let v := H.hp (j s.1, Φ.momentum (0, s))
  let L : (ℝ × InitialData U) →L[ℝ] (E × (ℝ × U)) :=
    (flowDifferential v (j.toContinuousLinearMap.comp
      (ContinuousLinearMap.fst ℝ U (ℝ × U)))).prod
      ((ContinuousLinearMap.snd ℝ U (ℝ × U)).comp
        (ContinuousLinearMap.snd ℝ ℝ (InitialData U)))
  have hbij := flowDifferential_bijective_of_transverse j ν horth hspan hv
  have hL : Function.Bijective L := by
    constructor
    · intro a b hab
      have hbase := hbij.1 (a₁ := (a.1, a.2.1)) (a₂ := (b.1, b.2.1))
        (congrArg Prod.fst hab)
      have hη := congrArg Prod.snd hab
      exact Prod.ext (congrArg (fun z : ℝ × U ↦ z.1) hbase)
        (Prod.ext (congrArg (fun z : ℝ × U ↦ z.2) hbase) hη)
    · intro z
      obtain ⟨⟨t, u⟩, hu⟩ := hbij.2 z.1
      exact ⟨(t, (u, z.2)), Prod.ext hu rfl⟩
  let A := ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hL.1) (LinearMap.range_eq_top.mpr hL.2)
  refine ⟨A, ?_⟩
  have hd := Φ.hasFDerivAt_augmentedProjection (q := (0, s)) ⟨Φ.zero_mem_time, hs⟩
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro q
  simp [A, L, ContinuousLinearEquiv.coe_ofBijective, flowDifferential,
    Φ.initial_variation s hs, Φ.initial_position s hs, hj, v]

end JanetCartan.HamiltonPhase
