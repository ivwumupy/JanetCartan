module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.BufferedProjection
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Smooth Hamilton charts on buffered targets

For `app:lem:common-hamilton-phase`, turn the quantitative projection gap into
an actual smooth inverse on the entire convex source and any open target
contained in its image. These lemmas retain their explicit derivative-gap
inputs; the transverse construction discharges them for the reference flow.
-/

open Set Filter
open scoped Topology ContDiff NNReal
@[expose] public noncomputable section

namespace JanetCartan.HamiltonPhase

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]

/-- The normalized half gap makes a finite-dimensional derivative invertible
(`app:lem:buffered-inverse-stability`). -/
theorem exists_linearEquiv_of_normalized_half_gap (A : X ≃L[ℝ] Y) (B : X →L[ℝ] Y)
    (h : ‖(A.symm : Y →L[ℝ] X).comp B - ContinuousLinearMap.id ℝ X‖ ≤ 1 / 2) :
    ∃ B' : X ≃L[ℝ] Y, (B' : X →L[ℝ] Y) = B := by
  have hi : Function.Injective B := by
    apply (injective_iff_map_eq_zero B).mpr
    intro x hx
    have hb := ((A.symm : Y →L[ℝ] X).comp B - ContinuousLinearMap.id ℝ X).le_opNorm x
    simp only [sub_apply, ContinuousLinearMap.comp_apply, hx,
      map_zero, ContinuousLinearMap.id_apply, zero_sub, norm_neg] at hb
    have hm := mul_le_mul_of_nonneg_right h (norm_nonneg x)
    exact norm_eq_zero.mp (by linarith [norm_nonneg x])
  have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    A.toLinearEquiv.finrank_eq (f := B.toLinearMap)).mp hi
  exact ⟨(LinearEquiv.ofBijective B.toLinearMap ⟨hi, hs⟩).toContinuousLinearEquiv, rfl⟩

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] in
/-- The normalized segment estimate gives an inverse on the entire convex
source (`app:lem:buffered-inverse-stability`). -/
theorem exists_openPartialHomeomorph_of_normalized_half_gap [CompleteSpace X]
    {D : Set X} (hD : IsOpen D) (hconv : Convex ℝ D)
    (A : X ≃L[ℝ] Y) (f : X → Y) (hf : ∀ x ∈ D, DifferentiableAt ℝ f x)
    (hgap : ∀ x ∈ D,
      ‖(A.symm : Y →L[ℝ] X).comp (fderiv ℝ f x) - ContinuousLinearMap.id ℝ X‖ ≤ 1 / 2) :
    ∃ e : OpenPartialHomeomorph X Y, (e : X → Y) = f ∧ e.source = D ∧ e.target = f '' D := by
  have ha := approximatesLinearOn_normalized_of_derivative_gap hconv A hf
    (c := (1 / 2 : ℝ≥0)) (by simpa using hgap)
  have hc : Subsingleton X ∨ (1 / 2 : ℝ≥0) <
      ‖((ContinuousLinearEquiv.refl ℝ X).symm : X →L[ℝ] X)‖₊⁻¹ := by
    rcases subsingleton_or_nontrivial X with h | h
    · exact Or.inl h
    · right; simp; norm_num
  let e₀ := ha.toOpenPartialHomeomorph _ D hc hD
  let e := e₀.transHomeomorph A.toHomeomorph
  have he : (e : X → Y) = f := by funext x; exact A.apply_symm_apply (f x)
  refine ⟨e, he, rfl, ?_⟩
  ext y
  change A.symm y ∈ (fun x ↦ A.symm (f x)) '' D ↔ y ∈ f '' D
  constructor
  · rintro ⟨x, hx, hxy⟩; exact ⟨x, hx, A.symm.injective hxy⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

/-- Smoothness of the forward map upgrades the inverse on the whole convex
source to a smooth inverse (`app:lem:buffered-inverse-stability`). -/
theorem exists_smoothInverse_of_normalized_half_gap [CompleteSpace X]
    {D : Set X} (hD : IsOpen D) (hconv : Convex ℝ D)
    (A : X ≃L[ℝ] Y) (f : X → Y) (hf : ContDiffOn ℝ ∞ f D)
    (hgap : ∀ x ∈ D,
      ‖(A.symm : Y →L[ℝ] X).comp (fderiv ℝ f x) - ContinuousLinearMap.id ℝ X‖ ≤ 1 / 2) :
    ∃ e : OpenPartialHomeomorph X Y, (e : X → Y) = f ∧ e.source = D ∧
      e.target = f '' D ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have hd : ∀ x ∈ D, DifferentiableAt ℝ f x :=
    fun x hx ↦ (hf.contDiffAt (hD.mem_nhds hx)).differentiableAt (by simp)
  obtain ⟨e, he, hs, ht⟩ :=
    exists_openPartialHomeomorph_of_normalized_half_gap hD hconv A f hd hgap
  refine ⟨e, he, hs, ht, ?_⟩
  intro y hy
  have hx : e.symm y ∈ D := hs ▸ e.map_target hy
  obtain ⟨B, hB⟩ := exists_linearEquiv_of_normalized_half_gap A _ (hgap _ hx)
  have hc := hf.contDiffAt (hD.mem_nhds hx)
  apply ContDiffAt.contDiffWithinAt
  apply e.contDiffAt_symm hy (f₀' := B)
  · rw [he, hB]
    exact (hd _ hx).hasFDerivAt
  · rw [he]
    exact hc

section HamiltonChart

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ U]
  {H : HomogeneousSymbol E} (Φ : HamiltonFlow H U)

omit [CompleteSpace E] in
/-- Construct a smooth projection chart with exactly the prescribed open
target and the entire preimage in the convex source. The inverse and its
smoothness follow from the half gap, not from supplied inverse data
(`app:lem:common-hamilton-phase`). -/
theorem HamiltonFlow.exists_smoothBufferedProjectionChart
    {D : Set (ℝ × InitialData U)} {V : Set (E × (ℝ × U))}
    (hD : IsOpen D) (hconv : Convex ℝ D) (hV : IsOpen V)
    (hadm : D ⊆ Φ.time ×ˢ Φ.parameters)
    (himage : V ⊆ Φ.augmentedProjection '' D)
    (hc : ContDiffOn ℝ ∞ Φ.position (Φ.time ×ˢ Φ.parameters))
    (A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U)))
    (hgap : ∀ q ∈ D,
      ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
        (fderiv ℝ Φ.augmentedProjection q) - ContinuousLinearMap.id ℝ (ℝ × InitialData U)‖
          ≤ 1 / 2) :
    ∃ C : ProjectionChart Φ,
      C.target = V ∧ C.source = D ∩ Φ.augmentedProjection ⁻¹' V ∧
      ContDiffOn ℝ ∞ C.coordinates V := by
  have hf : ContDiffOn ℝ ∞ Φ.augmentedProjection D :=
    (hc.prodMk contDiff_snd.snd.contDiffOn).mono hadm
  obtain ⟨e, he, hs, ht, hi⟩ :=
    exists_smoothInverse_of_normalized_half_gap hD hconv A Φ.augmentedProjection hf hgap
  let e₁ := (e.symm.restrOpen V hV).symm
  have he₁ : (e₁ : (ℝ × InitialData U) → E × (ℝ × U)) = Φ.augmentedProjection := he
  have hs₁ : e₁.source = D ∩ Φ.augmentedProjection ⁻¹' V := by
    change e.source ∩ e ⁻¹' V = _
    rw [he, hs]
  have ht₁ : e₁.target = V := by
    change e.target ∩ V = V
    exact inter_eq_right.mpr (ht ▸ himage)
  have hadm₁ : e₁.source ⊆ Φ.time ×ˢ Φ.parameters := by
    rw [hs₁]
    exact inter_subset_left.trans hadm
  have hi₁ : ∀ z ∈ e₁.target, ContDiffAt ℝ ∞ e₁.symm z := by
    intro z hz
    exact hi.contDiffAt (e.open_target.mem_nhds hz.1)
  let C := ProjectionChart.ofOpenPartialHomeomorph Φ e₁ he₁ hadm₁
    (fun z hz ↦ (hi₁ z hz).differentiableAt (by simp))
  refine ⟨C, ht₁, hs₁, ?_⟩
  intro z hz
  exact ((hi₁ z (ht₁.symm ▸ hz)).fst.prodMk
    (hi₁ z (ht₁.symm ▸ hz)).snd.fst).contDiffWithinAt

end HamiltonChart
end JanetCartan.HamiltonPhase
