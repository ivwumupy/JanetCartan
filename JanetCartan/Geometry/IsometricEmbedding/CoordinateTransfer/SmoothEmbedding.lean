module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Normed.Module.ContinuousInverse

/-!
# The finite-dimensional smooth embedding criterion

For the embedding conclusion of `main:thm:main` and the final paragraph of
`main:sec:convergence` in `paper.tex`, a smooth topological embedding with injective
manifold differential is a smooth embedding in Mathlib's chart-based sense.

We extend the map in complementary directions and apply the inverse function
theorem to obtain charts in which the original map is `u ↦ (u, 0)`. Finite
dimensionality identifies the pointwise complements with one fixed vector space.
-/

public noncomputable section

open scoped ContDiff Manifold
open Set Topology

namespace JanetCartan

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The inverse-function step in `main:sec:convergence`: a smooth map with
identity derivative admits a local inverse smooth at every order on one open set. -/
lemma exists_smooth_inverse_chart [CompleteSpace F]
    {g : F → F} {s : Set F} {a : F} (hs : IsOpen s) (ha : a ∈ s)
    (hg : ContDiffOn ℝ ∞ g s)
    (hd : HasFDerivAt g (ContinuousLinearEquiv.refl ℝ F : F →L[ℝ] F) a) :
    ∃ e : OpenPartialHomeomorph F F, a ∈ e.source ∧ (e : F → F) = g ∧
      e.source ⊆ s ∧ ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have hga := hg.contDiffAt (hs.mem_nhds ha)
  let e₀ := hga.toOpenPartialHomeomorph g hd (by simp)
  have ha₀ : a ∈ e₀.source := hga.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hdcont : ContinuousAt (fderiv ℝ g) a :=
    (hg.continuousOn_fderiv_of_isOpen hs (by simp)).continuousAt (hs.mem_nhds ha)
  have hdinv : (fderiv ℝ g a).IsInvertible := by
    rw [hd.fderiv]
    exact ⟨ContinuousLinearEquiv.refl ℝ F, rfl⟩
  obtain ⟨u, huinv, hau, hu⟩ :=
    mem_nhds_iff.mp (hdcont hdinv.eventually_nhds)
  let e := e₀.restr (s ∩ u)
  have hes : e.source ⊆ s := by
    simpa [e, (hs.inter hau).interior_eq] using
      (show e₀.source ∩ (s ∩ u) ⊆ s from fun _ h ↦ h.2.1)
  have heinv : ∀ y ∈ e.source, (fderiv ℝ g y).IsInvertible := by
    intro y hy
    apply huinv
    have : y ∈ e₀.source ∩ (s ∩ u) := by simpa [e, (hs.inter hau).interior_eq] using hy
    exact this.2.2
  have hecoe : (e : F → F) = g := rfl
  refine ⟨e, ?_, hecoe, hes, ?_, ?_⟩
  · simpa [e, (hs.inter hau).interior_eq] using And.intro ha₀ (And.intro ha hu)
  · rw [hecoe]
    exact hg.mono hes
  · intro y hy
    have hx := e.map_target hy
    obtain ⟨d, hd'⟩ := heinv _ hx
    apply ContDiffAt.contDiffWithinAt
    apply e.contDiffAt_symm hy (f₀' := d)
    · rw [hecoe, hd']
      exact ((hg.contDiffAt (hs.mem_nhds (hes hx))).differentiableAt (by simp)).hasFDerivAt
    · rw [hecoe]
      exact hg.contDiffAt (hs.mem_nhds (hes hx))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The chart construction behind the final paragraph of `main:sec:convergence`:
a differential which is the inclusion of a complemented factor gives an immersion.
The inverse of the map extended in complementary directions is the ambient chart. -/
lemma isImmersionAtOfComplement_of_split_chart [CompleteSpace F]
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    {f : M → F} {x : M} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (c : OpenPartialHomeomorph M E) (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hx : x ∈ c.source) (q : (E × K) ≃L[ℝ] F)
    (hd : HasFDerivAt (f ∘ c.symm)
      (q.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ E K)) (c x)) :
    Manifold.IsImmersionAtOfComplement K 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x := by
  let p : F →L[ℝ] E := (ContinuousLinearMap.fst ℝ E K).comp q.symm.toContinuousLinearMap
  let v : F →L[ℝ] F := q.toContinuousLinearMap.comp
    ((ContinuousLinearMap.inr ℝ E K).comp
      ((ContinuousLinearMap.snd ℝ E K).comp q.symm.toContinuousLinearMap))
  let g : F → F := fun y ↦ f (c.symm (p y)) + v y
  let a := q (c x, 0)
  let s := p ⁻¹' c.target
  have hs : IsOpen s := c.open_target.preimage p.continuous
  have ha : a ∈ s := by simpa [s, p, a] using c.map_source hx
  have hk : ContDiffOn ℝ ∞ (f ∘ c.symm) c.target :=
    (hf.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas hc)).contDiffOn
  have hg : ContDiffOn ℝ ∞ g s :=
    (hk.comp p.contDiff.contDiffOn (fun _ hy ↦ hy)).add v.contDiff.contDiffOn
  have hda : HasFDerivAt g (ContinuousLinearEquiv.refl ℝ F : F →L[ℝ] F) a := by
    have hdpa : HasFDerivAt (f ∘ c.symm) (q.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl ℝ E K)) (p a) := by simpa [p, a] using hd
    convert (hdpa.comp a p.hasFDerivAt).add v.hasFDerivAt using 1
    · rfl
    · ext y
      change y = q ((q.symm y).1, 0) + q (0, (q.symm y).2)
      rw [← map_add]
      simp
  obtain ⟨e, hae, he, _, hreg, hinv⟩ := exists_smooth_inverse_chart hs ha hg hda
  have hea : e a = f x := by simp [he, g, a, p, v, c.left_inv hx]
  let t := (fun u : E ↦ q (u, 0)) ⁻¹' e.source
  have ht : IsOpen t :=
    e.open_source.preimage (q.continuous.comp (continuous_id.prodMk continuous_const))
  have hct : IsOpen (c.source ∩ c ⁻¹' t) := c.continuousOn.isOpen_inter_preimage c.open_source ht
  -- Restricting through the chart keeps the source open.
  let b := c.restr (c.source ∩ c ⁻¹' t)
  have hb : b ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M :=
    restr_mem_maximalAtlas _ hc hct
  have hxb : x ∈ b.source := by
    change x ∈ c.source ∩ interior (c.source ∩ c ⁻¹' t)
    rw [hct.interior_eq]
    exact ⟨hx, hx, hae⟩
  have hechart : e.symm ∈ IsManifold.maximalAtlas 𝓘(ℝ, F) ∞ F :=
    e.symm.mem_maximalAtlas_of_contMDiffOn hinv.contMDiffOn hreg.contMDiffOn
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    hf.continuous.continuousAt q b e.symm hxb (hea ▸ e.map_source hae) hb hechart
  intro u hu
  have hub : u ∈ b.target := by simpa [OpenPartialHomeomorph.extend_target] using hu
  have hbu := b.map_target hub
  have huq : q (u, 0) ∈ e.source := by
    change c.symm u ∈ c.source ∩ interior (c.source ∩ c ⁻¹' t) at hbu
    rw [hct.interior_eq] at hbu
    have heq : c (c.symm u) = u := b.right_inv hub
    have htmem : q (c (c.symm u), 0) ∈ e.source := hbu.2.2
    exact heq ▸ htmem
  have hgu : e (q (u, 0)) = f (c.symm u) := by simp [he, g, p, v]
  change e.symm (f (c.symm u)) = q (u, 0)
  rw [← hgu]
  exact e.left_inv huq

/-- The local immersion step for `main:thm:main`: an injective differential into
a finite-dimensional space gives genuine immersion charts, with complement the
kernel of a continuous linear left inverse. -/
lemma exists_isImmersionAtOfComplement_ker_of_injective_mfderiv [FiniteDimensional ℝ F]
    {f : M → F} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (x : M)
    (hinj : Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)) :
    ∃ (L : F →L[ℝ] E),
      Manifold.IsImmersionAtOfComplement L.ker 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x ∧
      Nonempty ((E × L.ker) ≃L[ℝ] F) := by
  let c := chartAt E x
  let d : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x
  have hinjd : Function.Injective d := hinj
  obtain ⟨L, hL⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hinjd
  let q := (ContinuousLinearEquiv.equivOfRightInverse L d hL).symm
  have hq : q.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ E L.ker) = d := by
    ext u
    change d u + 0 = d u
    exact add_zero _
  refine ⟨L, ?_, ⟨q⟩⟩
  apply isImmersionAtOfComplement_of_split_chart hf c (IsManifold.chart_mem_maximalAtlas x)
    (mem_chart_source E x) q
  rw [hq]
  have hmd := hf.mdifferentiable (by simp) x
  have hfd : d = fderiv ℝ (f ∘ c.symm) (c x) := by
    simpa [d, c, writtenInExtChartAt, extChartAt, mfld_simps] using! hmd.mfderiv_abuse
  rw [hfd]
  have hcont : ContDiffAt ℝ ∞ (f ∘ c.symm) (c x) := by
    apply ContMDiffAt.contDiffAt
    apply (hf (c.symm (c x))).comp
    exact contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x)
      (c.map_source (mem_chart_source E x))
  exact (hcont.differentiableAt (by simp)).hasFDerivAt

/-- The immersion criterion used for `main:thm:main` and `main:sec:convergence`:
a smooth map between finite-dimensional real manifolds, with vector-space target
and injective manifold differentials, is a chart-based immersion. -/
theorem isImmersion_of_injective_mfderiv [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : M → F} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)) :
    Manifold.IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f := by
  let K := Fin (Module.finrank ℝ F - Module.finrank ℝ E) → ℝ
  have himm : Manifold.IsImmersionOfComplement K 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f := by
    intro x
    obtain ⟨L, hL, ⟨q⟩⟩ := exists_isImmersionAtOfComplement_ker_of_injective_mfderiv hf x (hinj x)
    have hdim : Module.finrank ℝ L.ker = Module.finrank ℝ K := by
      have hq := q.toLinearEquiv.finrank_eq
      rw [Module.finrank_prod] at hq
      simp only [K, Module.finrank_fin_fun]
      omega
    exact hL.trans_F (ContinuousLinearEquiv.ofFinrankEq hdim)
  exact himm.isImmersion

/-- The smooth embedding criterion for `main:thm:main`, as used in the final
paragraph of `main:sec:convergence`: smoothness, a topological embedding, and
injectivity of every manifold differential imply `Manifold.IsSmoothEmbedding`. -/
theorem isSmoothEmbedding_of_injective_mfderiv [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : M → F} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hemb : Topology.IsEmbedding f)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)) :
    Manifold.IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f :=
  ⟨isImmersion_of_injective_mfderiv hf hinj, hemb⟩

end JanetCartan
