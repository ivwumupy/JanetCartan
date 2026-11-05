module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.ConjugationIdentity.GraphDifferentiation
public import JanetCartan.Analysis.Microlocal.FourierIntegral.ConjugationIdentity.SourceTime

/-! # Integral algebra for the direct graph identity

Integrability needed to subtract the two literal graph operators in
`app:ch_regular_base:eq:direct-graph-identity`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}

/-- Subtract literal graph amplitudes using integrability on the Euclidean
frequency/source product. Consumer: the two-term direct graph identity. -/
theorem graphOperator_sub_of_integrable
    (S : Euclidean n → Euclidean n → ℝ) (a b : FullAmplitude n r)
    (v : Euclidean n → Fin r → ℂ) (x : Euclidean n)
    (ha : Integrable (fun p : Euclidean n × Euclidean n ↦
      graphOscillation S x p.2 p.1 • (a x p.2 p.1).mulVec (v p.2)) (volume.prod volume))
    (hb : Integrable (fun p : Euclidean n × Euclidean n ↦
      graphOscillation S x p.2 p.1 • (b x p.2 p.1).mulVec (v p.2)) (volume.prod volume)) :
    graphOperator S (fun z y η ↦ a z y η - b z y η) v x =
      graphOperator S a v x - graphOperator S b v x := by
  simp only [graphOperator, Matrix.sub_mulVec, smul_sub]
  have hab := integral_prod _ (ha.sub hb)
  dsimp only [Pi.sub_apply] at hab
  rw [← hab, ← integral_prod _ ha, ← integral_prod _ hb,
    integral_sub ha hb, smul_sub]

/-- Smooth compact frequency amplitudes and compact source data give product
integrability for `app:ch_regular_base:eq:direct-graph-identity`. -/
theorem integrable_graph_integrand_of_compact
    {S : Euclidean n → Euclidean n → ℝ}
    {b : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    {v : Euclidean n → Fin r → ℂ} {O K : Set (Euclidean n)}
    (hK : IsCompact K)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (O ×ˢ univ))
    (hb : ContDiffOn ℝ ∞ (Function.uncurry b) (O ×ˢ univ))
    (hbK : ∀ x ∈ O, ∀ η ∉ K, b x η = 0)
    (hv : ContDiff ℝ ∞ v) (hvK : HasCompactSupport v)
    {x : Euclidean n} (hx : x ∈ O) :
    Integrable (fun p : Euclidean n × Euclidean n ↦
      graphOscillation S x p.2 p.1 • (b x p.1).mulVec (v p.2)) (volume.prod volume) := by
  apply GraphDifferentiation.integrable_section (hK.prod hvK)
    (GraphDifferentiation.contDiffOn_integrand hS hb hv).continuousOn _ hx
  intro z hz p hp
  by_cases hη : p.1 ∈ K
  · have hy : p.2 ∉ tsupport v := fun hy ↦ hp ⟨hη, hy⟩
    simp [image_eq_zero_of_notMem_tsupport hy]
  · simp [hbK z hz p.1 hη]

/-- The differentiated graph amplitude is integrable by compact support, as
needed to subtract `T_0 D_t` in `app:ch_regular_base:eq:direct-graph-identity`. -/
theorem integrable_differentiated_graph_integrand
    (A : Euclidean n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (B : Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    {S : Euclidean n → Euclidean n → ℝ}
    {b : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    {v : Euclidean n → Fin r → ℂ} {O K : Set (Euclidean n)}
    (hO : IsOpen O) (hK : IsCompact K)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (O ×ˢ univ))
    (hb : ContDiffOn ℝ ∞ (Function.uncurry b) (O ×ˢ univ))
    (hbK : ∀ x ∈ O, ∀ η ∉ K, b x η = 0)
    (hv : ContDiff ℝ ∞ v) (hvK : HasCompactSupport v)
    {x : Euclidean n} (hx : x ∈ O) :
    Integrable (fun p : Euclidean n × Euclidean n ↦
      graphOscillation S x p.2 p.1 •
        (((∑ j, ((partialDeriv (fun z ↦ S z p.1) x j : ℝ) : ℂ) • A x j) * b x p.1 +
          transportRemainder (A x) (fun j ↦ partialDeriv (fun z ↦ b z p.1) x j)
            (B x) (b x p.1)).mulVec (v p.2))) (volume.prod volume) := by
  let f : Euclidean n × (Euclidean n × Euclidean n) → Fin r → ℂ :=
    fun p ↦ graphOscillation S p.1 p.2.2 p.2.1 • (b p.1 p.2.1).mulVec (v p.2.2)
  have hf : ContDiffOn ℝ ∞ f (O ×ˢ univ) :=
    GraphDifferentiation.contDiffOn_integrand hS hb hv
  have hs : ∀ z ∈ O, ∀ p ∉ K ×ˢ tsupport v, f (z, p) = 0 := by
    intro z hz p hp
    by_cases hη : p.1 ∈ K
    · have hy : p.2 ∉ tsupport v := fun hy ↦ hp ⟨hη, hy⟩
      simp [f, image_eq_zero_of_notMem_tsupport hy]
    · simp [f, hbK z hz p.1 hη]
  have hi := GraphDifferentiation.integrable_physicalOperator (μ := volume.prod volume)
    hO (hK.prod hvK) hf hs A B hx
  apply hi.congr
  filter_upwards with p
  have hSx : DifferentiableAt ℝ (fun z ↦ S z p.1) x :=
    ((hS.contDiffAt ((hO.prod isOpen_univ).mem_nhds ⟨hx, mem_univ _⟩)).comp x
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hbx : DifferentiableAt ℝ (fun z ↦ b z p.1) x :=
    ((hb.contDiffAt ((hO.prod isOpen_univ).mem_nhds ⟨hx, mem_univ _⟩)).comp x
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  exact GraphDifferentiation.physicalOperator_integrand A B S b v x p.2 p.1 hSx hbx

/-- Joint smoothness and fixed compact frequency support give a smooth actual
graph output on the output chart. This supplies the weak output integration by
parts needed for the distributional form of
`app:ch_regular_base:eq:direct-graph-identity`. -/
theorem contDiffOn_graphOperator_of_compact
    {S : Euclidean n → Euclidean n → ℝ}
    {b : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    {v : Euclidean n → Fin r → ℂ} {O K : Set (Euclidean n)}
    (hO : IsOpen O) (hK : IsCompact K)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (O ×ˢ univ))
    (hb : ContDiffOn ℝ ∞ (Function.uncurry b) (O ×ˢ univ))
    (hbK : ∀ x ∈ O, ∀ η ∉ K, b x η = 0)
    (hv : ContDiff ℝ ∞ v) (hvK : HasCompactSupport v) :
    ContDiffOn ℝ ∞ (graphOperator S (fun x _ η ↦ b x η) v) O := by
  let f : Euclidean n × (Euclidean n × Euclidean n) → Fin r → ℂ :=
    fun p ↦ graphOscillation S p.1 p.2.2 p.2.1 • (b p.1 p.2.1).mulVec (v p.2.2)
  let μ : Measure (Euclidean n × Euclidean n) := volume.prod volume
  have hf : ContDiffOn ℝ ∞ f (O ×ˢ univ) :=
    GraphDifferentiation.contDiffOn_integrand hS hb hv
  have hs : ∀ z ∈ O, ∀ p ∉ K ×ˢ tsupport v, f (z, p) = 0 := by
    intro z hz p hp
    by_cases hη : p.1 ∈ K
    · have hy : p.2 ∉ tsupport v := fun hy ↦ hp ⟨hη, hy⟩
      simp [f, image_eq_zero_of_notMem_tsupport hy]
    · simp [f, hbK z hz p.1 hη]
  have hcarrier := hK.prod hvK
  let : IsFiniteMeasure (μ.restrict (K ×ˢ tsupport v)) :=
    isFiniteMeasure_restrict.mpr hcarrier.measure_lt_top.ne
  have hsm := (contDiffOn_compactParameterIntegral (μ := μ) hO isOpen_univ
    hcarrier (subset_univ _) hf).const_smul (((2 * Real.pi) ^ n : ℂ)⁻¹)
  apply hsm.congr
  intro x hx
  unfold graphOperator
  congr 1
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hs x hx)]
  exact (integral_prod _ (GraphDifferentiation.integrable_section (μ := μ)
    hcarrier hf.continuousOn hs hx)).symm

end JanetCartan.FourierIntegral
