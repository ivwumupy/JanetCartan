module

public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Cutoff

/-!
# Bounded channels from compact input integrals

The channel existence and integral distribution step of
`app:ch_osc:prop:osc-normal`. No quantitative amplitude bounds are needed here.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff ENNReal
set_option maxHeartbeats 800000
namespace JanetCartan.NormalComparison
open AmplitudeBound
variable {n r : ℕ}
local notation "E" => Euclidean n

/-- Integrating a smooth interior-supported channel gives a continuous compact
physical kernel (`app:ch_osc:prop:osc-normal`). The input domain may have
infinite measure. This supplies the actual bounded channel construction. -/
theorem compactIntegratedKernel_regular
    {D X V : Set E} (hD : IsOpen D) (hX : IsCompact X) (hV : IsCompact V)
    (hVD : V ⊆ D) {F : (E × E) × E → ℂ}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ D))
    (hs : ∀ p, p ∉ (X ×ˢ X) ×ˢ V → F p = 0) :
    Continuous (fun z : E × E ↦ ∫ u in D, F (z, u)) ∧
      HasCompactSupport (fun z : E × E ↦ ∫ u in D, F (z, u)) := by
  let : IsFiniteMeasure (volume.restrict V) := ⟨by simpa using hV.measure_lt_top (μ := volume)⟩
  have he (z : E × E) : (∫ u in D, F (z, u)) = ∫ u in V, F (z, u) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu ↦
      hs (z, u) (fun hp ↦ hu (hVD hp.2))),
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu ↦
        hs (z, u) (fun hp ↦ hu hp.2))]
  have hc : Continuous (fun z : E × E ↦ ∫ u in D, F (z, u)) := by
    simp_rw [he]
    exact (contDiffOn_univ.mp (contDiffOn_compactParameterIntegral
      isOpen_univ hD hV hVD hF)).continuous
  refine ⟨hc, (hX.prod hX).of_isClosed_subset (isClosed_tsupport _) ?_⟩
  apply closure_minimal _ (hX.prod hX).isClosed
  intro z hz
  by_contra hn
  exact hz (integral_eq_zero_of_ae (Eventually.of_forall fun u ↦
    hs (z, u) (fun hp ↦ hn hp.1)))

/-- Each input section of the compact channel is integrable; this is the
premise needed to distribute the transport sum (`app:ch_osc:prop:osc-normal`). -/
theorem compactIntegratedKernel_integrable
    {D V : Set E} (_hD : IsOpen D) (hV : IsCompact V) (hVD : V ⊆ D)
    {F : (E × E) × E → ℂ} (hF : ContDiffOn ℝ ∞ F (univ ×ˢ D))
    (hs : ∀ z u, u ∉ V → F (z, u) = 0) (z : E × E) :
    IntegrableOn (fun u ↦ F (z, u)) D := by
  let : IsFiniteMeasure (volume.restrict V) := ⟨by simpa using hV.measure_lt_top (μ := volume)⟩
  have hi := integrableOn_compactParameter hV hVD hF.continuousOn (mem_univ z)
    (μ := volume)
  have hg : Integrable (fun u ↦ F (z, u)) :=
    (integrable_indicator_iff hV.measurableSet).2 hi |>.congr
      (Eventually.of_forall fun u ↦ by
        by_cases hu : u ∈ V
        · simp [hu]
        · simp [hu, hs z u hu])
  exact hg.integrableOn

/-- Actual bounded matrix channels for a finite collection of smooth compact
integrands. Their full physical kernels and both integrability assertions are
consequences of smoothness/support (`app:ch_osc:prop:osc-normal`). -/
theorem exists_compactIntegratedChannels {ι : Type*} [Fintype ι]
    {D X V : Set E} (hD : IsOpen D) (hX : IsCompact X) (hV : IsCompact V)
    (hVD : V ⊆ D) (F : ι → Fin r → Fin r → (E × E) × E → ℂ)
    (hF : ∀ k i j, ContDiffOn ℝ ∞ (F k i j) (univ ×ˢ D))
    (hs : ∀ k i j p, p ∉ (X ×ˢ X) ×ˢ V → F k i j p = 0) :
    ∃ N : ι → NormalOutputL2 n r →L[ℂ] NormalOutputL2 n r,
      (∀ k f i, (N k f) i =ᵐ[volume] fun x ↦
        ∑ j, ∫ y, (∫ u in D, F k i j ((x, y), u)) * f j y) ∧
      (∀ k i j x y, IntegrableOn (fun u ↦ F k i j ((x, y), u)) D) ∧
      (∀ k i j (f : Lp (α := E) ℂ 2) x,
        Integrable (fun y ↦ (∫ u in D, F k i j ((x, y), u)) * f y)) := by
  have hreg k i j := compactIntegratedKernel_regular hD hX hV hVD (hF k i j) (hs k i j)
  let B := fun k i j ↦ compactKernelOperator (μ := volume) (ν := volume)
    (t := fun x y ↦ ∫ u in D, F k i j ((x, y), u)) (hreg k i j).1 (hreg k i j).2
  refine ⟨fun k ↦ matrixOperator (B k), ?_, ?_, ?_⟩
  · intro k f i
    exact matrixOperator_ae_kernel (B k) _
      (fun i j f ↦ compactKernelOperator_ae_integral (hreg k i j).1 (hreg k i j).2 f) f i
  · intro k i j x y
    exact compactIntegratedKernel_integrable hD hV hVD (hF k i j)
      (fun z u hu ↦ hs k i j (z, u) (fun hp ↦ hu hp.2)) (x, y)
  · intro k i j f x
    exact integrable_compactKernel_mul_L2
      (t := fun x y ↦ ∫ u in D, F k i j ((x, y), u)) (hreg k i j).1 (hreg k i j).2 f x

/-- Finite channel sums distribute through the two integrals, with every
integrability premise supplied by compact support (`app:ch_osc:prop:osc-normal`). -/
theorem integral_sum_compactChannels {ι : Type*} [Fintype ι]
    {D X V : Set E} (hD : IsOpen D) (hX : IsCompact X) (hV : IsCompact V)
    (hVD : V ⊆ D) (F : ι → (E × E) × E → ℂ)
    (hF : ∀ k, ContDiffOn ℝ ∞ (F k) (univ ×ˢ D))
    (hs : ∀ k p, p ∉ (X ×ˢ X) ×ˢ V → F k p = 0)
    (f : Lp (α := E) ℂ 2) (x : E) :
    (∫ y, (∫ u in D, ∑ k, F k ((x, y), u)) * f y) =
      ∑ k, ∫ y, (∫ u in D, F k ((x, y), u)) * f y := by
  have hi k y := compactIntegratedKernel_integrable hD hV hVD (hF k)
    (fun z u hu ↦ hs k (z, u) (fun hp ↦ hu hp.2)) (x, y)
  have ho k := compactIntegratedKernel_regular hD hX hV hVD (hF k) (hs k)
  simp_rw [integral_finsetSum _ (fun k _ ↦ hi k _), Finset.sum_mul]
  exact integral_finsetSum _ (fun k _ ↦ integrable_compactKernel_mul_L2
    (t := fun x y ↦ ∫ u in D, F k ((x, y), u)) (ho k).1 (ho k).2 f x)
end JanetCartan.NormalComparison
