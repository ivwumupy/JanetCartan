module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.IncidenceCover.FiniteDetection
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.IncidenceCover.LocalData
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.IncidenceCover.Roots

/-!
# Decorated detecting incidence covers

Steps 3–4 of `app:ch_seed:prop:seed-frozen-menu`, with additional data attached
to the literal selected patches. A local seed-to-patch producer supplies the
final patches and their decorations before any incidence sections are built.
The full image-channel detector inequality survives local continuation and
finite-cover selection, including charts with empty patch lists.

The consuming parent construction uses `Decoration := FrozenPatchData` and
`exists_frozenPatchData_of_localReference`. Constructing those local Hamilton
references and instantiating this conditional theorem remain with that parent.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace Matrix Matrix.Norms.Frobenius Topology
open Set Filter

namespace JanetCartan.ActualCarriers.FrozenPhaseReference

open FrozenMenu

/-- The local step of `exists_decorated_coverData_of_local_patches`: restrict
only the covector neighborhood, retaining each decorated patch literally
(`app:ch_seed:prop:seed-frozen-menu`, Step 4). -/
private theorem exists_decorated_chartData_of_patch_sections {n m : ℕ} {k : Euclidean n}
    (Decoration : Patch n → Type)
    (P : Fin m → Patch n) (c C d : Fin m → ℝ)
    (U : Fin m → Set (Euclidean n)) (root : Fin m → Euclidean n → Euclidean 3)
    (hdec : ∀ a, Nonempty (Decoration (P a)))
    (hP : ∀ a, (P a).IsValid (c a) (C a))
    (hU : ∀ a, IsOpen (U a)) (hkU : ∀ a, k ∈ U a)
    (hd : ∀ a, 0 < d a) (hroot : ∀ a, root a k = 0)
    (hsec : ∀ a, (P a).IsIncidenceSection (U a) (root a) (d a))
    {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ)
    (hgap : ∀ (M : MetricTensor n) (q : Fin m → Euclidean n),
      ‖M - cubePencil k‖ < δ →
      ‖q - (fun a ↦ CubeCarrier.quadratic ((P a).toFun 0))‖ < δ →
      ∀ s : Euclidean n, γ * ‖s‖ ^ 2 ≤ ‖ActualCarriers.imageChannel M s‖ ^ 2 +
        ∑ a, ⟪q a, s⟫_ℝ ^ 2) :
    ∃ (D : ChartData n) (c₀ C₀ : ℝ), D.IsValid c₀ C₀ ∧ k ∈ D.domain ∧
      ∀ a, Nonempty (Decoration (D.patches a)) := by
  classical
  let q := fun l a ↦ CubeCarrier.quadratic ((P a).toFun (root a l))
  have hquadratic : Continuous (@CubeCarrier.quadratic n) := by
    unfold CubeCarrier.quadratic
    apply (PiLp.continuous_toLp 2 _).comp
    fun_prop
  have hq : ContinuousAt q k := by
    apply continuousAt_pi.mpr
    intro a
    have hp : ContinuousAt (P a).toFun 0 :=
      (hP a).2.2.2.1.continuousOn.continuousAt
        (parameterInterior_mem_nhds (mul_pos (by norm_num) (hP a).1))
    have hr := (hsec a).1.continuousOn.continuousAt ((hU a).mem_nhds (hkU a))
    apply hquadratic.continuousAt.comp
    apply ContinuousAt.comp _ hr
    simpa only [hroot a] using hp
  have hqzero : q k = fun a ↦ CubeCarrier.quadratic ((P a).toFun 0) := by
    funext a
    simp [q, hroot]
  have hqnear : ∀ᶠ l in 𝓝 k,
      ‖q l - (fun a ↦ CubeCarrier.quadratic ((P a).toFun 0))‖ < δ := by
    have hh : ContinuousAt (fun l ↦
        ‖q l - (fun a ↦ CubeCarrier.quadratic ((P a).toFun 0))‖) k :=
      (hq.sub continuousAt_const).norm
    apply hh.eventually (gt_mem_nhds ?_)
    simpa [hqzero] using hδ
  have hMnear : ∀ᶠ l in 𝓝 k, ‖cubePencil l - cubePencil k‖ < δ := by
    have hh : ContinuousAt (fun l ↦ ‖cubePencil l - cubePencil k‖) k :=
      ((cubePencilContinuousLinearMap n).continuous.continuousAt.sub
        continuousAt_const).norm
    apply hh.eventually (gt_mem_nhds ?_)
    simpa using hδ
  have hallU : ∀ᶠ l in 𝓝 k, ∀ a, l ∈ U a :=
    eventually_all.mpr fun a ↦ (hU a).mem_nhds (hkU a)
  obtain ⟨V, hVsub, hV, hkV⟩ := mem_nhds_iff.mp (hallU.and (hMnear.and hqnear))
  obtain ⟨ε, hε, hεbound⟩ := Pi.exists_forall_pos_add_lt
    (fun a ↦ lt_min (hP a).2.1 (hd a))
  let c₀ := min γ ε
  let C₀ := 1 + ∑ a, C a
  have hc₀ : 0 < c₀ := lt_min hγ hε
  have hsum : 0 ≤ ∑ a, C a := Finset.sum_nonneg fun a _ ↦ (hP a).2.2.1.le
  have hC₀ : 0 < C₀ := by dsimp [C₀]; linarith
  have hupper : ∀ a, C a ≤ C₀ := by
    intro a
    have hh := Finset.single_le_sum (fun b _ ↦ (hP b).2.2.1.le) (Finset.mem_univ a)
    dsimp [C₀]
    linarith
  refine ⟨⟨m, P, V, root⟩, c₀, C₀, ⟨hc₀, hC₀, hV, ?_, ?_⟩, hkV, hdec⟩
  · intro a
    have he : ε ≤ min (c a) (d a) := by simpa using (hεbound a).le
    refine ⟨(hP a).mono hc₀ ((min_le_right γ ε).trans (he.trans (min_le_left _ _)))
      (hupper a), ?_⟩
    exact (hsec a).mono (fun l hl ↦ (hVsub hl).1 a)
      ((min_le_right γ ε).trans (he.trans (min_le_right _ _)))
  · intro l hl s
    exact (mul_le_mul_of_nonneg_right (min_le_left γ ε) (sq_nonneg ‖s‖)).trans
      (hgap (cubePencil l) (q l) (hVsub hl).2.1 (hVsub hl).2.2 s)

/-- The compactness step of `exists_decorated_coverData_of_local_patches`:
select charts without changing their patch lists or decorations, allowing empty
lists and retaining the image channel (`app:ch_seed:prop:seed-frozen-menu`, Step 4). -/
private theorem exists_decorated_coverData_of_local_charts {n : ℕ}
    (Decoration : Patch n → Type)
    (hlocal : ∀ k ∈ Metric.sphere (0 : Euclidean n) 1,
      ∃ (D : ChartData n) (c C : ℝ), D.IsValid c C ∧ k ∈ D.domain ∧
        ∀ a, Nonempty (Decoration (D.patches a))) :
    ∃ (D : CoverData n) (c C : ℝ), D.IsValid c C ∧
      ∀ b a, Nonempty (Decoration (D.patches b a)) := by
  classical
  let S := Metric.sphere (0 : Euclidean n) 1
  choose D c C hD hmem hdec using fun k : S ↦ hlocal k.val k.property
  have hcover : S ⊆ ⋃ k : S, (D k).domain := by
    intro k hk
    exact mem_iUnion.mpr ⟨⟨k, hk⟩, hmem ⟨k, hk⟩⟩
  obtain ⟨t, ht⟩ := (isCompact_sphere (0 : Euclidean n) 1).elim_finite_subcover
    (fun k : S ↦ (D k).domain) (fun k ↦ (hD k).2.2.1) hcover
  let e := t.equivFin.symm
  let E : Fin t.card → ChartData n := fun b ↦ D (e b).val
  -- These finite bounds also provide positive margins when there are no charts.
  obtain ⟨c₀, hc₀, hlower⟩ := Pi.exists_forall_pos_add_lt
    (fun b : Fin t.card ↦ (hD (e b).val).1)
  let C₀ : ℝ := 1 + ∑ b : Fin t.card, C (e b).val
  have hsum : 0 ≤ ∑ b : Fin t.card, C (e b).val :=
    Finset.sum_nonneg fun b _ ↦ (hD (e b).val).2.1.le
  have hC₀ : 0 < C₀ := by dsimp [C₀]; linarith
  have hupper : ∀ b : Fin t.card, C (e b).val ≤ C₀ := by
    intro b
    have hb := Finset.single_le_sum
      (fun a _ ↦ (hD (e a).val).2.1.le) (Finset.mem_univ b)
    dsimp [C₀]
    linarith
  have hE : ∀ b, (E b).IsValid c₀ C₀ := by
    intro b
    exact (hD (e b).val).mono hc₀ (by simpa using (hlower b).le) (hupper b)
  let F : CoverData n :=
    { chartCount := t.card
      patchCount := fun b ↦ (E b).patchCount
      patches := fun b ↦ (E b).patches
      domain := fun b ↦ (E b).domain
      roots := fun b ↦ (E b).roots }
  refine ⟨F, c₀, C₀,
    ⟨hc₀, hC₀, fun b ↦ (hE b).2.2.1, ?_,
      fun b ↦ (hE b).2.2.2.1, fun b ↦ (hE b).2.2.2.2⟩,
    fun b a ↦ hdec (e b).val a⟩
  intro k hk
  obtain ⟨j, hj, hkj⟩ := mem_iUnion₂.mp (ht hk)
  refine mem_iUnion.mpr ⟨e.symm ⟨j, hj⟩, ?_⟩
  simpa [F, E] using hkj


/-- Assemble a finite detecting cover while retaining decorations on its literal
patch indices (`app:ch_seed:prop:seed-frozen-menu`, Steps 3–4).

The sole extra hypothesis is a local producer from each `CarrierSeed` to a valid
centered transverse patch with its decoration. Incidence sections are constructed
on these final patches, after any shrinking performed by the producer. Neither
patches nor their indices are merged, and the full image-channel inequality in
`CoverData.IsValid` permits empty detector lists.

The parent reference-menu construction supplies this hypothesis using
`exists_frozenPatchData_of_localReference` with `Decoration := FrozenPatchData`;
this theorem does not assert unconditional existence of those references. -/
theorem exists_decorated_coverData_of_local_patches {n : ℕ} (hn : 5 ≤ n)
    (Decoration : Patch n → Type)
    (hlocal : ∀ (k s ξ : Euclidean n), CarrierSeed k s ξ →
      ∃ (P : Patch n) (c C : ℝ), P.IsValid c C ∧ P.toFun 0 = ξ ∧
        (∀ z ∈ parameterCube P.radius,
          c ≤ |fderiv ℝ (fun w ↦ incidence k (P.toFun w)) z
            (EuclideanSpace.single 0 1)|) ∧ Nonempty (Decoration P)) :
    ∃ (D : CoverData n) (c C : ℝ), D.IsValid c C ∧
      ∀ b a, Nonempty (Decoration (D.patches b a)) := by
  classical
  apply exists_decorated_coverData_of_local_charts Decoration
  intro k hk
  have hk0 : k ≠ 0 := by
    intro hzero
    simp [hzero] at hk
  obtain ⟨m, ξ, hseed, hdet⟩ := exists_finite_detecting_seeds hn hk0
  choose s hs using hseed
  choose P c C hP hcenter hderiv hdec using fun a ↦ hlocal k (s a) (ξ a) (hs a)
  have hinc : ∀ a, incidence k ((P a).toFun 0) = 0 := by
    intro a
    rw [hcenter a]
    exact (hs a).incident
  have hdetP : ∀ s, imageChannel (cubePencil k) s = 0 →
      (∀ a, ⟪CubeCarrier.quadratic ((P a).toFun 0), s⟫_ℝ = 0) → s = 0 := by
    simpa only [hcenter] using hdet
  obtain ⟨γ, δ, hγ, hδ, hgap⟩ := exists_detection_perturbation_radius
    (cubePencil k) (fun a ↦ CubeCarrier.quadratic ((P a).toFun 0)) hdetP
  choose U root d hU hkU hroot hd hsec using fun a ↦
    (P a).exists_centered_incidenceSection k (c a) (C a) (hP a) (hinc a) (hderiv a)
  exact exists_decorated_chartData_of_patch_sections Decoration P c C d U root
    hdec hP hU hkU hd hroot hsec hγ hδ hgap

end JanetCartan.ActualCarriers.FrozenPhaseReference
