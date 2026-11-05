module

public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.DifferentiatedKernel
public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Transport

/-!
# Transported kernels of actual normal derivatives

The operator norm derivative and compact-support transport calculation in
`app:ch_osc:prop:osc-normal` are connected before the channel estimates.
-/

@[expose] public noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal Topology ContDiff

namespace JanetCartan.NormalComparison

open CompactTransport AmplitudeBound

variable {n r : ℕ}
local notation "E" => Euclidean n

/-- The derivative under the integral equals the transported expression in
`app:ch_osc:prop:osc-normal`. All analytic premises follow from smoothness
and compact support inside the domain; the phase velocity identity is the
geometric input. -/
theorem integral_deriv_oscillatory_eq_transport
    {D S : Set E} (hD : IsOpen D) (hS : IsCompact S) (hSD : S ⊆ D)
    {Φ : ℝ × E → ℝ} {A : ℝ × E → ℂ} {w : E → E} {m : E → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (hA : ContDiff ℝ ∞ A)
    (hw : ContDiffOn ℝ ∞ w D) (hm : ContDiffOn ℝ ∞ m D)
    (hs : ∀ t, tsupport (fun u ↦ A (t, u)) ⊆ S) (s K : ℝ)
    (hv : ∀ u ∈ D, A (s, u) ≠ 0 → deriv (fun t ↦ Φ (t, u)) s =
      fderiv ℝ (fun v ↦ Φ (s, v)) u (w u)) :
    (∫ u in D, deriv (fun t ↦ oscillatoryFactor K (Φ (t, u)) * A (t, u)) s * (m u : ℂ)) =
      ∫ u in D, oscillatoryFactor K (Φ (s, u)) *
        (transportCoefficient (fun v ↦ deriv (fun t ↦ A (t, v)) s)
          (fun j v ↦ (w v j : ℂ) * A (s, v)) u * (m u : ℂ) +
          ∑ j, (-((w u j : ℂ) * A (s, u))) * ((partialDeriv m u j : ℝ) : ℂ)) := by
  have hE := contDiff_oscillatoryFactor hΦ K
  have hf : ContDiffOn ℝ ∞
      (fun p : ℝ × E ↦ oscillatoryFactor K (Φ p) * A p * (m p.2 : ℂ)) (univ ×ˢ D) :=
    (hE.mul hA).contDiffOn.mul
      (Complex.ofRealCLM.contDiff.comp_contDiffOn
        (hm.comp contDiffOn_snd (fun _ hp ↦ hp.2)))
  have hd := hasDerivAt_integral_carrier isOpen_univ hD hS hSD hf
    (fun t _ u hu ↦ by
      have hz := image_eq_zero_of_notMem_tsupport (f := fun v ↦ A (t, v))
        (fun h ↦ hu (hs t h))
      simp only [hz, mul_zero, zero_mul]) (s := s) (mem_univ s)
  have hi := hasDerivAt_compact_transport_on_support isOpen_univ hD hS hSD hΦ hA hw hm
    (fun t _ ↦ hs t) (s := s) (mem_univ s) K hv
  have hi' : HasDerivAt
      (fun t ↦ ∫ u in D, oscillatoryFactor K (Φ (t, u)) * A (t, u) * (m u : ℂ))
      (∫ u in D, oscillatoryFactor K (Φ (s, u)) *
        (transportCoefficient (fun v ↦ deriv (fun t ↦ A (t, v)) s)
          (fun j v ↦ (w v j : ℂ) * A (s, v)) u * (m u : ℂ) +
          ∑ j, (-((w u j : ℂ) * A (s, u))) * ((partialDeriv m u j : ℝ) : ℂ))) s := by
    simpa only [Complex.real_smul, mul_assoc, mul_comm, mul_left_comm] using hi
  have he := hd.unique hi'
  rw [← he]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro u
  exact (deriv_mul_const
    (((hE.mul hA).comp (contDiff_id.prodMk contDiff_const)).differentiable
      (by simp) s) (m u : ℂ)).symm

/-- Smoothness of a normalized kernel family at fixed frequency, as needed
for operator norm differentiation in `app:ch_osc:prop:osc-normal`. -/
theorem contDiff_normalizedOscillatoryKernel_family
    (scale K : ℝ) {φ : ℝ → E → E → ℝ} {a : ℝ → E → E → ℂ}
    (hφ : ContDiff ℝ ∞ (fun p : ℝ × (E × E) ↦ φ p.1 p.2.1 p.2.2))
    (ha : ContDiff ℝ ∞ (fun p : ℝ × (E × E) ↦ a p.1 p.2.1 p.2.2)) :
    ContDiff ℝ ∞ (fun p : ℝ × (E × E) ↦
      normalizedOscillatoryKernel scale K (φ p.1) (a p.1) p.2.1 p.2.2) :=
  (contDiff_const.mul (contDiff_oscillatoryFactor hφ K)).mul ha

/-- The actual normal operator has an operator norm derivative whose full
kernel is the transported kernel in `app:ch_osc:prop:osc-normal`. The scalar
normalization is retained as `scale²`, both physical positions are independent,
and the only mask derivatives in the answer are its first derivatives.
`Channels` identifies this integral with the constructed bounded operators
associated to a fixed scalar cutoff equal to one on the amplitude support.
The velocity identity is required only where both amplitude factors are supported. -/
theorem exists_compactOscillatoryNormal_transportDerivative
    {D : Set E} (hD : IsOpen D) (scale K : ℝ)
    {φ : ℝ → E → E → ℝ} {a : ℝ → E → E → Fin r → ℂ}
    (hφ : ContDiff ℝ ∞ (fun p : ℝ × (E × E) ↦ φ p.1 p.2.1 p.2.2))
    (ha : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × (E × E) ↦ a p.1 p.2.1 p.2.2 i))
    {S : Set (E × E)} (hS : IsCompact S) (hSD : Prod.snd '' S ⊆ D)
    (hs : ∀ i s z, z ∉ S → a s z.1 z.2 i = 0)
    {m : E → ℝ} (hm : ContDiffOn ℝ ∞ m D)
    (g : Lp ℂ ∞ (volume.restrict D))
    (hg : g =ᵐ[volume.restrict D] fun u ↦ (m u : ℂ))
    (s₀ : ℝ) (w : E → E → E → E)
    (hw : ∀ x y, ContDiffOn ℝ ∞ (w x y) D)
    (hv : ∀ x y u, u ∈ D → (x, u) ∈ S → (y, u) ∈ S → deriv (fun s ↦ φ s x u - φ s y u) s₀ =
      fderiv ℝ (fun v ↦ φ s₀ x v - φ s₀ y v) u (w x y u)) :
    let A := fun s x y u i j ↦ a s x u i * star (a s y u j)
    let c₀ := fun x y u i j ↦ transportCoefficient
      (fun v ↦ deriv (fun s ↦ A s x y v i j) s₀)
      (fun k v ↦ (w x y v k : ℂ) * A s₀ x y v i j) u
    let c := fun k x y u i j ↦ -((w x y u k : ℂ) * A s₀ x y u i j)
    ∃ E' : NormalOutputL2 n r →L[ℂ] NormalOutputL2 n r,
      HasDerivAt
        (fun s ↦ compactOscillatoryNormalOperator D scale K
          (φ := φ s) (a := a s)
          (hφ.continuous.comp (continuous_const.prodMk continuous_id))
          (fun i ↦ (ha i).continuous.comp (continuous_const.prodMk continuous_id))
          (fun i ↦ hasCompactSupport_kernelSlice hS (hs i) s) g) E' s₀ ∧
      ∀ f i, (E' f) i =ᵐ[volume] fun x ↦ ∑ j, ∫ y,
        (((scale ^ 2 : ℝ) : ℂ) * ∫ u in D, oscillatoryFactor K (φ s₀ x u - φ s₀ y u) *
          (c₀ x y u i j * (m u : ℂ) +
            ∑ k, c k x y u i j * ((partialDeriv m u k : ℝ) : ℂ))) * f j y := by
  let t : Fin r → ℝ → E × E → ℂ := fun i s z ↦
    normalizedOscillatoryKernel scale K (φ s) (fun x u ↦ a s x u i) z.1 z.2
  have ht (i) : ContDiff ℝ 1 (Function.uncurry (t i)) := by
    exact (contDiff_normalizedOscillatoryKernel_family scale K
      (φ := φ) (a := fun s x u ↦ a s x u i) hφ (ha i)).of_le (by norm_num)
  have hts (i) (s : ℝ) (z : E × E) (hz : z ∉ S) : t i s z = 0 := by
    simp only [t, normalizedOscillatoryKernel, hs i s z hz, mul_zero]
  obtain ⟨E', hd, hrep⟩ := exists_compactVectorKernel_normalDerivative D ht hS hts g s₀
  refine ⟨E', hd, ?_⟩
  intro f i
  refine (hrep f i).trans (Eventually.of_forall fun x ↦ ?_)
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  congr 1
  let Φ : ℝ × E → ℝ := fun p ↦ φ p.1 x p.2 - φ p.1 y p.2
  let A : ℝ × E → ℂ := fun p ↦ a p.1 x p.2 i * star (a p.1 y p.2 j)
  have hΦ : ContDiff ℝ ∞ Φ :=
    (hφ.comp (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd))).sub
      (hφ.comp (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)))
  have hA : ContDiff ℝ ∞ A :=
    ((ha i).comp (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd))).mul
      (Complex.conjCLE.contDiff.comp
        ((ha j).comp (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd))))
  have hAS (s : ℝ) : tsupport (fun u ↦ A (s, u)) ⊆ Prod.snd '' S := by
    apply closure_minimal _ (hS.image continuous_snd).isClosed
    intro u hu
    by_contra hn
    have hz : a s x u i = 0 := hs i s (x, u) (fun h ↦ hn ⟨(x, u), h, rfl⟩)
    exact hu (by simp [A, hz])
  have hEA := (contDiff_oscillatoryFactor hΦ K).mul hA
  have hprod (u : E) :
      (fun s ↦ t i s (x, u) * star (t j s (y, u))) =
      fun s ↦ ((scale ^ 2 : ℝ) : ℂ) * (oscillatoryFactor K (Φ (s, u)) * A (s, u)) := by
    funext s
    simpa only [t, Φ, A, mul_assoc] using normalizedOscillatoryKernel_mul_star scale K
      (φ s) (fun x u ↦ a s x u i) (fun y u ↦ a s y u j) x y u
  calc
    _ = ∫ u in D, deriv (fun s ↦ t i s (x, u) * star (t j s (y, u))) s₀ * (m u : ℂ) := by
      apply integral_congr_ae
      filter_upwards [hg] with u hu
      rw [hu]
    _ = ((scale ^ 2 : ℝ) : ℂ) *
        ∫ u in D, deriv (fun s ↦ oscillatoryFactor K (Φ (s, u)) * A (s, u)) s₀ * (m u : ℂ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro u
      dsimp only
      have hdu : DifferentiableAt ℝ
          (fun s ↦ oscillatoryFactor K (Φ (s, u)) * A (s, u)) s₀ :=
        (hEA.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) s₀
      rw [hprod u, deriv_const_mul _ hdu]
      exact mul_assoc _ _ _
    _ = _ := by
      rw [integral_deriv_oscillatory_eq_transport hD (hS.image continuous_snd) hSD
        hΦ hA (hw x y) hm hAS s₀ K (fun u hu hne ↦ hv x y u hu
          (by by_contra hn; exact hne (by simp [A, hs i s₀ (x, u) hn]))
          (by by_contra hn; exact hne (by simp [A, hs j s₀ (y, u) hn])))]

end JanetCartan.NormalComparison
