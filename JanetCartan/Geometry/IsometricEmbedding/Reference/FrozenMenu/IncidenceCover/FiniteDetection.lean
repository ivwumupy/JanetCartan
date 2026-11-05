module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.AllSeeds
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.LocalPatches
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.Cover

/-!
# Finite detecting carriers at a fixed covector

Compactness of the unit sphere of the pencil kernel selects actual constructed
carriers in Step 4 of `app:ch_seed:prop:seed-frozen-menu`. The image channel is
retained when passing from kernel detection to a positive Gram gap.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace Matrix Matrix.Norms.Frobenius
open Set Metric

namespace JanetCartan.FrozenMenu

private theorem pencil_transpose {n : ℕ} (k : Euclidean n) :
    (cubePencil k).transpose = cubePencil k := by
  ext i j
  by_cases h : i = j
  · subst j; rfl
  · simp [cubePencil, Matrix.transpose_apply, h, Ne.symm h]

/-- For the symmetric cube pencil, the image-channel kernel is precisely the
pencil kernel (`app:ch_seed:prop:seed-frozen-menu`, Step 4). -/
theorem imageChannel_cubePencil_eq_zero_iff {n : ℕ} (k s : Euclidean n) :
    ActualCarriers.imageChannel (cubePencil k) s = 0 ↔
      (cubePencil k).mulVec (fun i ↦ s i) = 0 := by
  simp only [ActualCarriers.imageChannel, pencil_transpose]
  constructor
  · intro h
    exact congrArg (WithLp.ofLp) h
  · intro h
    simp [h]

/-- Finitely many of the constructed seeds detect the entire pencil kernel.
The list may be empty, including when the pencil is invertible
(`app:ch_seed:prop:seed-frozen-menu`, Step 4). -/
theorem exists_finite_detecting_seeds {n : ℕ} (hn : 5 ≤ n)
    {k : Euclidean n} (hk : k ≠ 0) :
    ∃ (m : ℕ) (ξ : Fin m → Euclidean n),
      (∀ a, ∃ s, CarrierSeed k s (ξ a)) ∧
      ∀ s, ActualCarriers.imageChannel (cubePencil k) s = 0 →
        (∀ a, ⟪CubeCarrier.quadratic (ξ a), s⟫_ℝ = 0) → s = 0 := by
  classical
  let I := {ξ : Euclidean n // ∃ s, CarrierSeed k s ξ}
  let K := sphere (0 : Euclidean n) 1 ∩
    {s | ActualCarriers.imageChannel (cubePencil k) s = 0}
  have hcont : Continuous (ActualCarriers.imageChannel (cubePencil k)) := by
    unfold ActualCarriers.imageChannel
    apply (PiLp.continuous_toLp 2 _).comp
    unfold Matrix.mulVec dotProduct
    fun_prop
  have hK : IsCompact K := (isCompact_sphere 0 1).inter_right
    (isClosed_eq hcont continuous_const)
  let U : I → Set (Euclidean n) := fun ξ ↦ {s | ⟪CubeCarrier.quadratic ξ.val, s⟫_ℝ ≠ 0}
  have hopen : ∀ ξ, IsOpen (U ξ) := fun ξ ↦
    (isClosed_eq (continuous_const.inner continuous_id) continuous_const).isOpen_compl
  have hcover : K ⊆ ⋃ ξ, U ξ := by
    intro s hs
    have hs0 : s ≠ 0 := by
      intro h
      have hnorm : ‖s‖ = 1 := by simpa using hs.1
      simp [h] at hnorm
    obtain ⟨ξ, hξ⟩ := exists_carrierSeed hn hk hs0
      ((imageChannel_cubePencil_eq_zero_iff k s).mp hs.2)
    refine mem_iUnion.mpr ⟨⟨ξ, s, hξ⟩, ?_⟩
    simpa [U, PiLp.inner_apply, mul_comm] using hξ.detects
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hopen hcover
  let e := (Fintype.equivFin t).symm
  refine ⟨Fintype.card t, fun a ↦ (e a).val.val, fun a ↦ (e a).val.property, ?_⟩
  intro s hs hzero
  by_contra hs0
  let v := ‖s‖⁻¹ • s
  have hv : v ∈ K := by
    refine ⟨?_, ?_⟩
    · simp [v, norm_smul, norm_ne_zero_iff.mpr hs0]
    · apply (imageChannel_cubePencil_eq_zero_iff k v).mpr
      have hker := (imageChannel_cubePencil_eq_zero_iff k s).mp hs
      change (cubePencil k).mulVec (‖s‖⁻¹ • (fun i ↦ s i)) = 0
      rw [Matrix.mulVec_smul, hker, smul_zero]
  obtain ⟨ξ, hξt, hξ⟩ := mem_iUnion₂.mp (ht hv)
  let a := e.symm ⟨ξ, hξt⟩
  have hq : ⟪CubeCarrier.quadratic ξ.val, s⟫_ℝ = 0 := by
    simpa [a] using hzero a
  exact hξ (by simp [v, real_inner_smul_right, hq])

/-- The finite detecting seeds give actual quantitative patches, each centered
at an incident carrier and transverse on its whole parameter cube
(`app:ch_seed:prop:seed-frozen-menu`, Steps 3–4). -/
theorem exists_finite_detecting_patches {n : ℕ} (hn : 5 ≤ n)
    {k : Euclidean n} (hk : k ≠ 0) :
    ∃ (m : ℕ) (P : Fin m → Patch n) (c C : Fin m → ℝ),
      (∀ a, (P a).IsValid (c a) (C a) ∧ incidence k ((P a).toFun 0) = 0 ∧
        ∀ z ∈ parameterCube (P a).radius,
          c a ≤ |fderiv ℝ (fun w ↦ incidence k ((P a).toFun w)) z
            (EuclideanSpace.single 0 1)|) ∧
      ∀ s, ActualCarriers.imageChannel (cubePencil k) s = 0 →
        (∀ a, ⟪CubeCarrier.quadratic ((P a).toFun 0), s⟫_ℝ = 0) → s = 0 := by
  classical
  obtain ⟨m, ξ, hseed, hdet⟩ := exists_finite_detecting_seeds hn hk
  choose s hs using hseed
  choose P c C hP hcenter hderiv using fun a ↦ (hs a).exists_valid_patch hn
  refine ⟨m, P, c, C, ?_, ?_⟩
  · intro a
    exact ⟨hP a, by rw [hcenter a]; exact (hs a).incident, hderiv a⟩
  · simpa only [hcenter] using hdet

/-- The selected patches have a stable positive full detector gap, including
the image term, at every nonzero covector. No finite menu is assumed
(`app:ch_seed:eq:seed-frozen-detection`, Step 4 of its proof). -/
theorem exists_finite_patch_detection_radius {n : ℕ} (hn : 5 ≤ n)
    {k : Euclidean n} (hk : k ≠ 0) :
    ∃ (m : ℕ) (P : Fin m → Patch n) (c C : Fin m → ℝ) (γ δ : ℝ),
      (∀ a, (P a).IsValid (c a) (C a) ∧ incidence k ((P a).toFun 0) = 0 ∧
        ∀ z ∈ parameterCube (P a).radius,
          c a ≤ |fderiv ℝ (fun w ↦ incidence k ((P a).toFun w)) z
            (EuclideanSpace.single 0 1)|) ∧
      0 < γ ∧ 0 < δ ∧
      ∀ (M : MetricTensor n) (q : Fin m → Euclidean n),
        ‖M - cubePencil k‖ < δ →
        ‖q - (fun a ↦ CubeCarrier.quadratic ((P a).toFun 0))‖ < δ →
        ∀ s : Euclidean n,
          γ * ‖s‖ ^ 2 ≤ ‖ActualCarriers.imageChannel M s‖ ^ 2 +
            ∑ a, ⟪q a, s⟫_ℝ ^ 2 := by
  obtain ⟨m, P, c, C, hP, hdet⟩ := exists_finite_detecting_patches hn hk
  obtain ⟨γ, δ, hγ, hδ, hgap⟩ := ActualCarriers.exists_detection_perturbation_radius
    (cubePencil k) (fun a ↦ CubeCarrier.quadratic ((P a).toFun 0)) hdet
  exact ⟨m, P, c, C, γ, δ, hP, hγ, hδ, hgap⟩

end JanetCartan.FrozenMenu
