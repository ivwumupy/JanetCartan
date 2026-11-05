module

public import JanetCartan.Geometry.IsometricEmbedding.MetricPreservation
public import JanetCartan.Geometry.IsometricEmbedding.CoordinateTransfer.Dilation
public import JanetCartan.Geometry.IsometricEmbedding.CoordinateTransfer.SmoothEmbedding

/-!
# Transferring a Euclidean metric realization to a manifold

The coordinate step in Theorem `main:thm:main`, and the final paragraph of
Section 9 of paper.tex. The input is an actual local solution for the metric
pulled back by the inverse coordinates. No existence theorem is used here.
The final transfer theorems give `Manifold.IsSmoothEmbedding` on one open
neighborhood, using positive definiteness to establish immersion.
-/

@[expose] public noncomputable section

open scoped ContDiff Manifold
open Bundle TopologicalSpace Set

namespace JanetCartan

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- The coordinate metric in `main:thm:main`: pull back the manifold metric by
an inverse coordinate map and evaluate on the standard Euclidean basis. -/
def inverseCoordinateMetric {n : ℕ}
    (g : RiemannianMetric (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (ψ : Euclidean n → M) : MetricField n := fun y i j ↦
  g.inner (ψ y)
    (mfderiv 𝓘(ℝ, Euclidean n) 𝓘(ℝ, E) ψ y (EuclideanSpace.single i 1))
    (mfderiv 𝓘(ℝ, Euclidean n) 𝓘(ℝ, E) ψ y (EuclideanSpace.single j 1))

/-- `main:thm:main`: equality of the coordinate matrices gives equality on all
vectors, by bilinearity. This requires no regularity assumption. -/
theorem inner_fderiv_eq_inverseCoordinateMetric {n N : ℕ}
    (g : RiemannianMetric (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (ψ : Euclidean n → M) {F : Euclidean n → Euclidean N} {y : Euclidean n}
    (hmetric : inducedMetric F y = inverseCoordinateMetric g ψ y)
    (v w : Euclidean n) :
    inner ℝ (fderiv ℝ F y v) (fderiv ℝ F y w) =
      g.inner (ψ y) (mfderiv 𝓘(ℝ, Euclidean n) 𝓘(ℝ, E) ψ y v)
        (mfderiv 𝓘(ℝ, Euclidean n) 𝓘(ℝ, E) ψ y w) := by
  let D : Euclidean n →L[ℝ] TangentSpace 𝓘(ℝ, E) (ψ y) :=
    (mfderiv 𝓘(ℝ, Euclidean n) 𝓘(ℝ, E) ψ y).comp
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm.toContinuousLinearMap
  have hb (i j : Fin n) :
      inner ℝ (fderiv ℝ F y (EuclideanSpace.single i 1))
        (fderiv ℝ F y (EuclideanSpace.single j 1)) =
      g.inner (ψ y) (D (EuclideanSpace.single i 1)) (D (EuclideanSpace.single j 1)) :=
    congrFun (congrFun hmetric i) j
  change inner ℝ (fderiv ℝ F y v) (fderiv ℝ F y w) = g.inner (ψ y) (D v) (D w)
  rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v,
    ← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr w]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, starRingEnd_apply, star_trivial, sum_apply, smul_apply,
    Finset.mul_sum, smul_eq_mul]
  simp only [EuclideanSpace.basisFun_apply]
  simp_rw [hb]

/-- `main:thm:main`: transfer a local Euclidean metric solution through smooth
coordinates. The inverse-coordinate identity is an identity of maps, so the
chain rule supplies the required identity of differentials. -/
theorem preservesRiemannianMetric_comp_coordinates {n N : ℕ}
    (g : RiemannianMetric (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    {U : Opens M} {c : U → Euclidean n} {ψ : Euclidean n → M}
    {s : Set (Euclidean n)} {F : Euclidean n → Euclidean N}
    (hs : IsOpen s) (hc : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Euclidean n) ∞ c)
    (hcs : ∀ x, c x ∈ s)
    (hψ : ContMDiffOn 𝓘(ℝ, Euclidean n) 𝓘(ℝ, E) ∞ ψ s)
    (hψc : ∀ x, ψ (c x) = x.val) (hF : ContDiffOn ℝ ∞ F s)
    (hmetric : IsIsometricOn (inverseCoordinateMetric g ψ) F s) :
    PreservesRiemannianMetric g U (F ∘ c) := by
  intro x v w
  have hcd := hc.mdifferentiable (by simp) x
  have hFd := (hF.contDiffAt (hs.mem_nhds (hcs x))).differentiableAt (by simp)
  have hψd := (hψ.contMDiffAt (hs.mem_nhds (hcs x))).mdifferentiableAt (by simp)
  have hid : ψ ∘ c = (Subtype.val : U → M) := funext hψc
  have hderiv := mfderiv_comp x hψd hcd
  rw [hid] at hderiv
  rw [mfderiv_comp x hFd.mdifferentiableAt hcd, mfderiv_eq_fderiv]
  change inner ℝ (fderiv ℝ F (c x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Euclidean n) c x v))
    (fderiv ℝ F (c x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Euclidean n) c x w)) = _
  erw [inner_fderiv_eq_inverseCoordinateMetric g ψ (hmetric (hcs x))]
  rw [hderiv]
  congr 3
  exact hψc x

/-- Section 9: smoothness of the transferred map holds at every order on one
fixed neighborhood. -/
theorem contMDiff_comp_coordinates {n N : ℕ} {U : Opens M}
    {c : U → Euclidean n} {s : Set (Euclidean n)} {F : Euclidean n → Euclidean N}
    (hc : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Euclidean n) ∞ c)
    (hcs : ∀ x, c x ∈ s) (hF : ContDiffOn ℝ ∞ F s) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Euclidean N) ∞ (F ∘ c) :=
  hF.contMDiffOn.comp_contMDiff hc hcs

/-- Section 9: composing the coordinate embedding with a Euclidean embedding
on the coordinate domain preserves the topological embedding property. -/
theorem isEmbedding_comp_coordinates {n N : ℕ} {U : Opens M}
    {c : U → Euclidean n} {s : Set (Euclidean n)} {F : Euclidean n → Euclidean N}
    (hc : Topology.IsEmbedding c) (hcs : ∀ x, c x ∈ s)
    (hF : Topology.IsEmbedding (fun y : s ↦ F y.val)) :
    Topology.IsEmbedding (F ∘ c) :=
  hF.comp (hc.codRestrict s hcs)

/-- Section 9: restricting a smooth metric realization to a smaller open
neighborhood preserves the metric equation, with the inclusion differentials. -/
theorem PreservesRiemannianMetric.restrict {N : ℕ}
    {g : RiemannianMetric (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)}
    {U V : Opens M} {F : U → Euclidean N} (hVU : V ≤ U)
    (hF : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Euclidean N) ∞ F)
    (hmetric : PreservesRiemannianMetric g U F) :
    PreservesRiemannianMetric g V (F ∘ Opens.inclusion hVU) := by
  intro x v w
  have hi := (contMDiff_inclusion (I := 𝓘(ℝ, E)) hVU).mdifferentiable
    (show (∞ : ℕ∞ω) ≠ 0 by simp) x
  rw [mfderiv_comp x (hF.mdifferentiable (by simp) _) hi]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hmetric]
  have hval := mfderiv_comp x
    ((contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U)).mdifferentiable
      (show (∞ : ℕ∞ω) ≠ 0 by simp) _) hi
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : V → M) x = _ at hval
  rw [hval]
  rfl

/-- Section 9: positive definiteness of the manifold metric makes a coordinate
solution immersive whenever the inverse coordinate differential is injective. -/
theorem fderiv_injective_of_inverseCoordinateMetric {n N : ℕ}
    (g : RiemannianMetric (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    {ψ : Euclidean n → M} {F : Euclidean n → Euclidean N} {y : Euclidean n}
    (hψ : Function.Injective (mfderiv 𝓘(ℝ, Euclidean n) 𝓘(ℝ, E) ψ y))
    (hmetric : inducedMetric F y = inverseCoordinateMetric g ψ y) :
    Function.Injective (fderiv ℝ F y) := by
  intro v w hvw
  have hz : fderiv ℝ F y (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have hm := inner_fderiv_eq_inverseCoordinateMetric g ψ hmetric (v - w) (v - w)
  rw [hz, inner_zero_left] at hm
  have hzero : mfderiv 𝓘(ℝ, Euclidean n) 𝓘(ℝ, E) ψ y (v - w) = 0 := by
    by_contra hne
    exact (g.pos (ψ y) _ hne).ne' hm.symm
  have : (v - w : Euclidean n) = 0 := hψ (hzero.trans (map_zero _).symm)
  exact sub_eq_zero.mp this

/-- `main:thm:main`, final paragraph of Section 9: an actual smooth Euclidean
solution for the inverse-chart metric gives a smooth metric-preserving
topological embedding on a smaller manifold neighborhood. -/
theorem exists_local_metric_embedding_of_coordinate_solution {n N : ℕ}
    (g : RiemannianMetric (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (e : OpenPartialHomeomorph M (Euclidean n)) {p : M} (hp : p ∈ e.source)
    (he : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, Euclidean n) ∞ e e.source)
    (he' : ContMDiffOn 𝓘(ℝ, Euclidean n) 𝓘(ℝ, E) ∞ e.symm e.target)
    {s : Set (Euclidean n)} (hs : IsOpen s) (hst : s ⊆ e.target) (hps : e p ∈ s)
    {F : Euclidean n → Euclidean N} (hF : ContDiffOn ℝ ∞ F s)
    (hmetric : IsIsometricOn (inverseCoordinateMetric g e.symm) F s) :
    ∃ U : Opens M, p ∈ U ∧ (U : Set M) ⊆ e.source ∧
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Euclidean N) ∞ (fun x : U ↦ F (e x.val)) ∧
      Topology.IsEmbedding (fun x : U ↦ F (e x.val)) ∧
      PreservesRiemannianMetric g U (fun x : U ↦ F (e x.val)) := by
  have hed : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, Euclidean n) :=
    ⟨he.mdifferentiableOn (by simp), he'.mdifferentiableOn (by simp)⟩
  have hcomp := hed.comp_symm_deriv (e.map_source hp)
  have hinv : Function.Injective
      (mfderiv 𝓘(ℝ, Euclidean n) 𝓘(ℝ, E) e.symm (e p)) := by
    intro v w hvw
    have hv := congrArg (fun L ↦ L v) hcomp
    have hw := congrArg (fun L ↦ L w) hcomp
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Euclidean n) e (e.symm (e p))
      (mfderiv 𝓘(ℝ, Euclidean n) 𝓘(ℝ, E) e.symm (e p) v) = v at hv
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Euclidean n) e (e.symm (e p))
      (mfderiv 𝓘(ℝ, Euclidean n) 𝓘(ℝ, E) e.symm (e p) w) = w at hw
    rw [← hv, ← hw, hvw]
  obtain ⟨V, hpV, hVs, hFV⟩ := exists_isEmbedding_restrict_of_injective_fderiv
    hs hps (hF.of_le (by simp))
    (fderiv_injective_of_inverseCoordinateMetric g hinv (hmetric hps))
  let U : Opens M := ⟨e.source ∩ e ⁻¹' V, e.isOpen_inter_preimage V.isOpen⟩
  let c : U → Euclidean n := fun x ↦ e x.val
  have hUs : (U : Set M) ⊆ e.source := fun _ hx ↦ hx.1
  have hc : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Euclidean n) ∞ c :=
    he.comp_contMDiff contMDiff_subtype_val (fun x ↦ hUs x.property)
  have hcV : ∀ x, c x ∈ (V : Set (Euclidean n)) := fun x ↦ x.property.2
  have hce : Topology.IsEmbedding c :=
    e.isEmbedding_restrict.comp (Topology.IsEmbedding.inclusion hUs)
  refine ⟨U, ⟨hp, hpV⟩, hUs, contMDiff_comp_coordinates hc hcV (hF.mono hVs),
    isEmbedding_comp_coordinates hce hcV hFV, ?_⟩
  exact preservesRiemannianMetric_comp_coordinates g V.isOpen hc hcV (he'.mono (hVs.trans hst))
    (fun x ↦ e.left_inv (hUs x.property)) (hF.mono hVs)
    (fun _ hx ↦ hmetric (hVs hx))

/-- Section 9, final paragraph: undo the fixed dilation, transfer the resulting
Euclidean solution through the chart, and restrict once to obtain an embedding.
The Euclidean solution is an explicit input, not an existence assumption. -/
theorem exists_local_metric_embedding_of_dilated_coordinate_solution {n N : ℕ}
    (g : RiemannianMetric (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (e : OpenPartialHomeomorph M (Euclidean n)) {p : M} (hp : p ∈ e.source)
    (he : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, Euclidean n) ∞ e e.source)
    (he' : ContMDiffOn 𝓘(ℝ, Euclidean n) 𝓘(ℝ, E) ∞ e.symm e.target)
    {r : ℝ} (hr : r ≠ 0) {s : Set (Euclidean n)} (hs : IsOpen s)
    (hst : (fun x ↦ r⁻¹ • x) ⁻¹' s ⊆ e.target) (hps : r⁻¹ • e p ∈ s)
    {F : Euclidean n → Euclidean N} (hF : ContDiffOn ℝ ∞ F s)
    (hmetric : IsIsometricOn (fun y ↦ inverseCoordinateMetric g e.symm (r • y)) F s) :
    ∃ U : Opens M, p ∈ U ∧ (U : Set M) ⊆ e.source ∧
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Euclidean N) ∞
        (fun x : U ↦ undoDilation r F (e x.val)) ∧
      Topology.IsEmbedding (fun x : U ↦ undoDilation r F (e x.val)) ∧
      PreservesRiemannianMetric g U (fun x : U ↦ undoDilation r F (e x.val)) :=
  exists_local_metric_embedding_of_coordinate_solution g e hp he he'
    (hs.preimage (continuous_const_smul r⁻¹)) hst hps (contDiffOn_undoDilation hF)
    (isIsometricOn_undoDilation hr hs hF hmetric)

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- `main:thm:main`, final paragraph of `main:sec:convergence`: a smooth
topological embedding preserving a positive definite metric is a smooth
embedding, since metric preservation forces injectivity of its differential. -/
theorem PreservesRiemannianMetric.isSmoothEmbedding
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    {g : RiemannianMetric (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)}
    {U : Opens M} {f : U → F} (hmetric : PreservesRiemannianMetric g U f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (hemb : Topology.IsEmbedding f) :
    Manifold.IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f :=
  isSmoothEmbedding_of_injective_mfderiv hf hemb hmetric.mfderiv_injective

/-- `main:thm:main`, final paragraph of `main:sec:convergence`: an actual
smooth solution of the inverse-coordinate metric equation yields a smooth
isometric embedding on one smaller manifold neighborhood. The Euclidean
solution and the smooth coordinate maps remain explicit inputs. -/
theorem exists_local_isometric_embedding_of_coordinate_solution {n N : ℕ}
    (g : RiemannianMetric (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (e : OpenPartialHomeomorph M (Euclidean n)) {p : M} (hp : p ∈ e.source)
    (he : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, Euclidean n) ∞ e e.source)
    (he' : ContMDiffOn 𝓘(ℝ, Euclidean n) 𝓘(ℝ, E) ∞ e.symm e.target)
    {s : Set (Euclidean n)} (hs : IsOpen s) (hst : s ⊆ e.target) (hps : e p ∈ s)
    {F : Euclidean n → Euclidean N} (hF : ContDiffOn ℝ ∞ F s)
    (hmetric : IsIsometricOn (inverseCoordinateMetric g e.symm) F s) :
    ∃ U : Opens M, p ∈ U ∧ (U : Set M) ⊆ e.source ∧
      Manifold.IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, Euclidean N) ∞
        (fun x : U ↦ F (e x.val)) ∧
      PreservesRiemannianMetric g U (fun x : U ↦ F (e x.val)) := by
  obtain ⟨U, hpU, hUs, hf, hemb, hmetricU⟩ :=
    exists_local_metric_embedding_of_coordinate_solution g e hp he he' hs hst hps hF hmetric
  exact ⟨U, hpU, hUs, hmetricU.isSmoothEmbedding hf hemb, hmetricU⟩

/-- `main:thm:main`, final paragraph of `main:sec:convergence`: undo the fixed
nonzero dilation and transfer an actual Euclidean solution to a smooth isometric
embedding of a manifold neighborhood. No existence of a Euclidean solution is
asserted; the conclusion has the smooth embedding and metric preservation
properties required by the manifold theorem. -/
theorem exists_local_isometric_embedding_of_dilated_coordinate_solution {n N : ℕ}
    (g : RiemannianMetric (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (e : OpenPartialHomeomorph M (Euclidean n)) {p : M} (hp : p ∈ e.source)
    (he : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, Euclidean n) ∞ e e.source)
    (he' : ContMDiffOn 𝓘(ℝ, Euclidean n) 𝓘(ℝ, E) ∞ e.symm e.target)
    {r : ℝ} (hr : r ≠ 0) {s : Set (Euclidean n)} (hs : IsOpen s)
    (hst : (fun x ↦ r⁻¹ • x) ⁻¹' s ⊆ e.target) (hps : r⁻¹ • e p ∈ s)
    {F : Euclidean n → Euclidean N} (hF : ContDiffOn ℝ ∞ F s)
    (hmetric : IsIsometricOn (fun y ↦ inverseCoordinateMetric g e.symm (r • y)) F s) :
    ∃ U : Opens M, p ∈ U ∧ (U : Set M) ⊆ e.source ∧
      Manifold.IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, Euclidean N) ∞
        (fun x : U ↦ undoDilation r F (e x.val)) ∧
      PreservesRiemannianMetric g U (fun x : U ↦ undoDilation r F (e x.val)) := by
  obtain ⟨U, hpU, hUs, hf, hemb, hmetricU⟩ :=
    exists_local_metric_embedding_of_dilated_coordinate_solution
      g e hp he he' hr hs hst hps hF hmetric
  exact ⟨U, hpU, hUs, hmetricU.isSmoothEmbedding hf hemb, hmetricU⟩

end JanetCartan
