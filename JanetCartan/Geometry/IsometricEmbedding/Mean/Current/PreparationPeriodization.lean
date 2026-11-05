module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationSmooth
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Periodization.Basic

/-!
# Actual periodic extensions of the preparation amplitudes

For `app:ch_mean_pairs:eq:mean-density-lipschitz`, the current and transported
matrix fields are originally smooth on a physical neighborhood. A single
fixed cutoff supported inside the centered cell gives jointly smooth torus
and carrier extensions. They agree with the original fields on its plateau,
which contains the measurement chart. Thus no global smoothness of the
centered chart representative is required by `PreparationSmooth`.
-/

open Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
namespace JanetCartan.CurrentMean
open ContinuumRow AmplitudeBound
variable {n N : ℕ}

/-- The centered-representative extension of the preparation matrix fields,
retaining the literal carrier variables (`app:ch_mean_pairs:prop:mean-coarse`). -/
def preparationMatrixPeriodization
    (f : Euclidean n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    (p : Torus n × CarrierParameter) : Matrix (Fin N) (Fin n) ℂ :=
  f (centeredTorusRepresentative p.1, p.2)

/-- A uniform physical support gap gives exact agreement on a larger box,
for every carrier parameter (`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem preparationMatrixPeriodization_eq_of_lt
    (f : Euclidean n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    {b : ℝ} (hb : b < 1 / 2)
    (hs : ∀ x z, f (x,z) ≠ 0 → ∀ i, |x i| ≤ b)
    (x : Euclidean n) (z : CarrierParameter) (hx : ∀ i, |x i| < 1 - b) :
    preparationMatrixPeriodization f (torusQuotient x,z) = f (x,z) := by
  ext i j
  apply periodicLift_amplitudePeriodization_eq_of_lt hb (f := fun y ↦ f (y,z) i j) _ hx
  intro y hy
  apply hs y z
  intro h
  exact hy (by simp [h])

/-- The periodized matrix agrees jointly near each point of the closed cell,
including its faces (`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem preparationMatrixPeriodization_lift_eventuallyEq
    (f : Euclidean n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    {b : ℝ} (hb : b < 1 / 2)
    (hs : ∀ x z, f (x,z) ≠ 0 → ∀ i, |x i| ≤ b)
    {x : Euclidean n} (hx : x ∈ fundamentalCell n) (z : CarrierParameter) :
    (fun p : Euclidean n × CarrierParameter ↦
      preparationMatrixPeriodization f (torusQuotient p.1,p.2)) =ᶠ[𝓝 (x,z)] f := by
  have hmem : ∀ᶠ p : Euclidean n × CarrierParameter in 𝓝 (x,z),
      ∀ i, |p.1 i| < 1 - b := by
    apply eventually_all.mpr
    intro i
    apply (isOpen_lt (((EuclideanSpace.proj i).continuous.comp continuous_fst).abs)
      continuous_const).mem_nhds
    exact (abs_le.mpr (hx i)).trans_lt (by linarith)
  exact hmem.mono fun p hp ↦ preparationMatrixPeriodization_eq_of_lt f hb hs p.1 p.2 hp

/-- Construct joint torus/carrier regularity from the actual physical field
and a uniform support gap (`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem preparationMatrixPeriodization_regular
    (f : Euclidean n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    {b : ℝ} (hb : b < 1 / 2)
    (hs : ∀ x z, f (x,z) ≠ 0 → ∀ i, |x i| ≤ b)
    (hf : ContDiff ℝ ∞ f) :
    Continuous (preparationMatrixPeriodization f) ∧
    ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      preparationMatrixPeriodization f (torusQuotient p.1,p.2)) := by
  have hd : ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      preparationMatrixPeriodization f (torusQuotient p.1,p.2)) := by
    rw [contDiff_iff_contDiffAt]
    rintro ⟨x,z⟩
    obtain ⟨y, hy, k, rfl⟩ := exists_mem_fundamentalCell_add_integerTranslation x
    have hl := hf.contDiffAt.congr_of_eventuallyEq
      (preparationMatrixPeriodization_lift_eventuallyEq f hb hs hy z)
    have he : ((y + integerTranslation k) - integerTranslation k,z) = (y,z) := by simp
    have hl' := he.symm ▸ hl
    have hcomp := hl'.comp (y + integerTranslation k,z)
      ((contDiffAt_fst.sub (contDiffAt_const (c := integerTranslation k))).prodMk contDiffAt_snd)
    convert hcomp using 1
    funext p
    have hp := (periodicLift_periodic
      (fun x ↦ preparationMatrixPeriodization f (x,p.2)) k).sub_eq p.1
    exact hp.symm
  have hq : IsOpenQuotientMap (@torusQuotient n) :=
    (IsOpenQuotientMap.piMap (fun _ : Fin n ↦
      QuotientAddGroup.isOpenQuotientMap_mk)).comp
        (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap
  exact ⟨(hq.prodMap IsOpenQuotientMap.id).isQuotientMap.continuous_iff.mpr hd.continuous, hd⟩



/-- The fixed cutoff extends a locally smooth physical matrix field jointly
in its carrier variables (`app:ch_mean_pairs:prop:mean-coarse`). -/
theorem contDiff_preparationCutMatrix
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    {V : Set (Euclidean n)} (hV : IsOpen V) (hs : tsupport χ ⊆ V)
    (f : Euclidean n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    (hf : ContDiffOn ℝ ∞ f (V ×ˢ Set.univ)) :
    ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦ χ p.1 • f p) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.1 ∈ tsupport χ
  · exact ((hχ.comp contDiff_fst).contDiffAt).smul
      (hf.contDiffAt ((hV.prod isOpen_univ).mem_nhds ⟨hs hp, mem_univ _⟩))
  · have hzero : ∀ᶠ q : Euclidean n × CarrierParameter in 𝓝 p, χ q.1 = 0 := by
      have hn := ((isClosed_tsupport χ).isOpen_compl.preimage continuous_fst).mem_nhds hp
      exact Filter.Eventually.mono hn fun q hq ↦ image_eq_zero_of_notMem_tsupport hq
    apply (contDiffAt_const (c := (0 : Matrix (Fin N) (Fin n) ℂ))).congr_of_eventuallyEq
    exact hzero.mono fun q hq ↦ by simp [hq]

/-- One literal fixed-cutoff extension used to realize the current and
transport discrepancy. The cutoff only constructs an extension; it is one on
the original measurement region (`app:ch_mean_pairs:prop:mean-coarse`). -/
def preparationMatrixExtension (χ : Euclidean n → ℝ)
    (f : Euclidean n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ) :
    Torus n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ :=
  preparationMatrixPeriodization (fun p ↦ χ p.1 • f p)

/-- Local smoothness and the fixed support gap produce the actual common
smooth extensions required by the discrepancy constructor
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem preparationMatrixExtension_regular
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    {V : Set (Euclidean n)} (hV : IsOpen V) (hs : tsupport χ ⊆ V)
    {b : ℝ} (hb : b < 1 / 2) (hbox : ∀ x ∈ tsupport χ, ∀ i, |x i| ≤ b)
    (f : Euclidean n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    (hf : ContDiffOn ℝ ∞ f (V ×ˢ Set.univ)) :
    Continuous (preparationMatrixExtension χ f) ∧
    ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      preparationMatrixExtension χ f (torusQuotient p.1,p.2)) := by
  apply preparationMatrixPeriodization_regular _ hb _
    (contDiff_preparationCutMatrix χ hχ hV hs f hf)
  intro x z hx
  apply hbox x (subset_tsupport χ ?_)
  intro h
  exact hx (by simp [h])

/-- On the fixed plateau the extended matrix is exactly the original field,
so its measured Hermitian square is unchanged
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem preparationMatrixExtension_eq_on_plateau (χ : Euclidean n → ℝ)
    (f : Euclidean n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    (x : Torus n) (z : CarrierParameter)
    (hx : χ (centeredTorusRepresentative x) = 1) :
    preparationMatrixExtension χ f (x,z) = f (centeredTorusRepresentative x,z) := by
  simp [preparationMatrixExtension, preparationMatrixPeriodization, hx]



section PhysicalDiscrepancy

open MeasureTheory

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Construct the supported smooth preparation source from the original
locally smooth physical current and transport matrices. One fixed cutoff
produces both extensions and all their joint regularity; the resulting source
is the literal measured integral at every torus point and in the original L²
space (`app:ch_mean_pairs:eq:mean-density-lipschitz`,
`app:ch_mean_pairs:eq:mean-density-recursion`).

The actual current-atom producer must supply these SAME physical fields and
their formula on the chart. Quantitative discrepancy, inverse, and density
bounds are not assumptions or conclusions of this regularity construction. -/
theorem exists_preparationDiscrepancyRepresentative_of_physical
    (d : ι → CarrierData n N) (hC : ∀ a, IsSmoothPeriodic (preparationMeasurement (d a)))
    (χ : ι → CarrierParameter → ℝ) (hχ : ∀ a, ContDiff ℝ ∞ (χ a))
    (hχc : ∀ a, HasCompactSupport (χ a))
    (mask : ι → κ → CarrierParameter → ℝ)
    (hm : ∀ a c, Measurable (mask a c)) (hm₀ : ∀ a c z, 0 ≤ mask a c z)
    (hmask : ∀ a z, ∑ c, mask a c z = 1)
    (current : ι → κ → CarrierParameter → (CarrierVariable n → ℝ) →ₗ[ℝ]
      (Torus n → Matrix (Fin N) (Fin n) ℂ))
    (r v : ι → CarrierVariable n → ℝ)
    (ϑ : Euclidean n → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    {V : Set (Euclidean n)} (hV : IsOpen V) (hs : tsupport ϑ ⊆ V)
    {b : ℝ} (hb : b < 1 / 2) (hbox : ∀ x ∈ tsupport ϑ, ∀ i, |x i| ≤ b)
    (hplateau : ∀ a x, x ∈ (d a).outputChart → ϑ (centeredTorusRepresentative x) = 1)
    (U : ι → κ → Euclidean n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    (T : ι → Euclidean n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    (hU : ∀ a c, ContDiffOn ℝ ∞ (U a c) (V ×ˢ Set.univ))
    (hT : ∀ a, ContDiffOn ℝ ∞ (T a) (V ×ˢ Set.univ))
    (hcurrent : ∀ a c x, x ∈ (d a).outputChart → ∀ z, χ a z ≠ 0 →
      U a c (centeredTorusRepresentative x,z) =
        current a c z (fun q ↦ positiveDensityAmplitude (r a q) (v a q)) x)
    (htransport : ∀ a x, x ∈ (d a).outputChart → ∀ z, χ a z ≠ 0 →
      T a (centeredTorusRepresentative x,z) = densityTransportMatrix (d a) (v a) x z) :
    ∃ e : SmoothResidual n,
      e ∈ supportedSmoothResidual n (⋃ a, (d a).outputChart) ∧
      (∀ x, e.val x () = finitePreparationDiscrepancy d χ mask current r v x) ∧
      (smoothResidualToL2 n e =ᵐ[volume] finitePreparationDiscrepancy d χ mask current r v) ∧
      ∀ s : ℕ, smoothResidualToL2 n e ∈ (periodicSobolevScale n (Euclidean n)).level s := by
  let U' := fun a c ↦ preparationMatrixExtension ϑ (U a c)
  let T' := fun a ↦ preparationMatrixExtension ϑ (T a)
  have hU' (a : ι) (c : κ) :=
    preparationMatrixExtension_regular ϑ hϑ hV hs hb hbox (U a c) (hU a c)
  have hT' (a : ι) :=
    preparationMatrixExtension_regular ϑ hϑ hV hs hb hbox (T a) (hT a)
  have hc' (a : ι) (c : κ) (x : Torus n) (hx : x ∈ (d a).outputChart)
      (z : CarrierParameter) (hz : χ a z ≠ 0) :
      U' a c (x,z) = current a c z (fun q ↦ positiveDensityAmplitude (r a q) (v a q)) x := by
    rw [show U' a c (x,z) = U a c (centeredTorusRepresentative x,z) from
      preparationMatrixExtension_eq_on_plateau ϑ _ x z (hplateau a x hx)]
    exact hcurrent a c x hx z hz
  have ht' (a : ι) (x : Torus n) (hx : x ∈ (d a).outputChart)
      (z : CarrierParameter) (hz : χ a z ≠ 0) :
      T' a (x,z) = densityTransportMatrix (d a) (v a) x z := by
    rw [show T' a (x,z) = T a (centeredTorusRepresentative x,z) from
      preparationMatrixExtension_eq_on_plateau ϑ _ x z (hplateau a x hx)]
    exact htransport a x hx z hz
  let e := preparationDiscrepancyRepresentative d hC χ hχ hχc mask hm hm₀ hmask current r v
    U' T' (fun a c ↦ (hU' a c).1) (fun a ↦ (hT' a).1)
    (fun a c ↦ (hU' a c).2) (fun a ↦ (hT' a).2) hc' ht'
  exact ⟨e, preparationDiscrepancyRepresentative_supported d hC χ hχ hχc mask hm hm₀ hmask
      current r v U' T' _ _ _ _ hc' ht', fun _ ↦ rfl,
    preparationDiscrepancyRepresentative_toL2 d hC χ hχ hχc mask hm hm₀ hmask
      current r v U' T' _ _ _ _ hc' ht', smoothResidualToL2_mem e⟩

end PhysicalDiscrepancy

end JanetCartan.CurrentMean
