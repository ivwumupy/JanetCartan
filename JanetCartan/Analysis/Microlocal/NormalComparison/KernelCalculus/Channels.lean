module

public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.ChannelRegularity
public import JanetCartan.Analysis.Microlocal.NormalComparison.MaskSymbols

/-!
# The actual derivative as a sum of full normal channels

Final compact-kernel calculus for `app:ch_osc:prop:osc-normal`. The channels
are constructed from their smooth compact kernels, and therefore can be used
in the independent uniform amplitude estimates of `ChannelBounds`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff ENNReal
namespace JanetCartan.NormalComparison
open AmplitudeBound CompactTransport
variable {n r : ℕ}
local notation "E" => Euclidean n

/-- Recover the two independent physical positions from the concatenated
coordinates used by `fullNormalAmplitudeKernel` (`app:ch_osc:prop:osc-normal`). -/
def splitPhysicalPositions (z : Euclidean (2 * n)) : E × E :=
  (WithLp.toLp 2 (fun i ↦ z ⟨i.val, by omega⟩),
   WithLp.toLp 2 (fun i ↦ z ⟨n + i.val, by omega⟩))

/-- The full-kernel concatenation preserves both physical positions
(`app:ch_osc:prop:osc-normal`). -/
@[simp] theorem splitPhysicalPositions_pairedPosition (x y : E) :
    splitPhysicalPositions (pairedPosition x y) = (x, y) := by
  apply Prod.ext <;> ext i
  · simp [splitPhysicalPositions, pairedPosition]
  · simp [splitPhysicalPositions, pairedPosition]

/-- The exact channel decomposition of the actual operator norm derivative
in `app:ch_osc:prop:osc-normal`. The input symbols are L∞ representatives of
only `m` and its first derivatives (constructed by
`exists_mask_derivative_symbols` from the manuscript assumptions).
The channels themselves are constructed here: no boundedness, integral identity,
or differentiability is assumed. Their normalization is exactly `scale²`.
The sole geometric identity is needed only on the original amplitude carrier. -/
theorem exists_compactOscillatoryNormal_transportChannels
    {D : Set E} (hD : IsOpen D) (scale K : ℝ)
    {φ : ℝ → E → E → ℝ} {a : ℝ → E → E → Fin r → ℂ}
    (hφ : ContDiff ℝ ∞ (fun p : ℝ × (E × E) ↦ φ p.1 p.2.1 p.2.2))
    (ha : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × (E × E) ↦ a p.1 p.2.1 p.2.2 i))
    {S : Set (E × E)} (hS : IsCompact S) (hSD : Prod.snd '' S ⊆ D)
    (hs : ∀ i s z, z ∉ S → a s z.1 z.2 i = 0)
    {m : E → ℝ} (hm : ContDiffOn ℝ ∞ m D)
    (g : Option (Fin n) → Lp ℂ ∞ (volume.restrict D))
    (hg : ∀ k, g k =ᵐ[volume.restrict D] compactTransportMask m k)
    (χ : E → E → ℂ) (hχ : ∀ z ∈ S, χ z.1 z.2 = 1)
    (s₀ : ℝ) (w : (E × E) → E → E)
    (hw : ContDiff ℝ ∞ (Function.uncurry w))
    (hv : ∀ x y u, u ∈ D → (x, u) ∈ S → (y, u) ∈ S →
      deriv (fun s ↦ φ s x u - φ s y u) s₀ =
        fderiv ℝ (fun v ↦ φ s₀ x v - φ s₀ y v) u (w (x, y) u)) :
    let A := fun i j s (z : E × E) u ↦ a s z.1 u i * star (a s z.2 u j)
    let c := fun k u z i j ↦ compactTransportEntry (A i j) w s₀ k
      (splitPhysicalPositions z) u
    ∃ N : Option (Fin n) → NormalOutputL2 n r →L[ℂ] NormalOutputL2 n r,
      (∀ k f i, (N k f) i =ᵐ[volume] fun x ↦ ∑ j,
        fullNormalAmplitudeKernel (μ := volume.restrict D)
          (normalizedOscillatoryKernel scale K (φ s₀) χ)
          (fun u z ↦ c k u z i j) (g k) (f j) x) ∧
      HasDerivAt
        (fun s ↦ compactOscillatoryNormalOperator D scale K
          (φ := φ s) (a := a s)
          (hφ.continuous.comp (continuous_const.prodMk continuous_id))
          (fun i ↦ (ha i).continuous.comp (continuous_const.prodMk continuous_id))
          (fun i ↦ hasCompactSupport_kernelSlice hS (hs i) s) (g none))
        (N none + ∑ k, N (some k)) s₀ := by
  dsimp only
  let A := fun i j s (z : E × E) u ↦ a s z.1 u i * star (a s z.2 u j)
  let C := fun k i j ↦ compactTransportEntry (A i j) w s₀ k
  let X := Prod.fst '' S
  let V := Prod.snd '' S
  have hX : IsCompact X := hS.image continuous_fst
  have hV : IsCompact V := hS.image continuous_snd
  have hA i j : ContDiff ℝ ∞
      (fun p : ℝ × ((E × E) × E) ↦ A i j p.1 p.2.1 p.2.2) :=
    ((ha i).comp (contDiff_fst.prodMk (contDiff_snd.fst.fst.prodMk contDiff_snd.snd))).mul
      (Complex.conjCLE.contDiff.comp
        ((ha j).comp (contDiff_fst.prodMk (contDiff_snd.fst.snd.prodMk contDiff_snd.snd))))
  have hAs i j t p (hp : p ∉ (X ×ˢ X) ×ˢ V) : A i j t p.1 p.2 = 0 := by
    by_cases hx : (p.1.1, p.2) ∈ S
    · by_cases hy : (p.1.2, p.2) ∈ S
      · exact (hp ⟨⟨⟨_, hx, rfl⟩, ⟨_, hy, rfl⟩⟩, ⟨_, hx, rfl⟩⟩).elim
      · simp [A, hs j t (p.1.2, p.2) hy]
    · simp [A, hs i t (p.1.1, p.2) hx]
  have hC k i j : ContDiff ℝ ∞ (Function.uncurry (C k i j)) :=
    contDiff_compactTransportEntry (hA i j) hw s₀ k
  have hCs k i j p (hp : p ∉ (X ×ˢ X) ×ˢ V) : C k i j p.1 p.2 = 0 :=
    compactTransportEntry_eq_zero_off_product hV.isClosed (hAs i j) w s₀ k p hp
  let F := fun k i j (p : (E × E) × E) ↦
    ((scale ^ 2 : ℝ) : ℂ) * oscillatoryFactor K (φ s₀ p.1.1 p.2 - φ s₀ p.1.2 p.2) *
      C k i j p.1 p.2 * compactTransportMask m k p.2
  have hphase : ContDiff ℝ ∞
      (fun p : (E × E) × E ↦ φ s₀ p.1.1 p.2 - φ s₀ p.1.2 p.2) :=
    (hφ.comp (contDiff_const.prodMk (contDiff_fst.fst.prodMk contDiff_snd))).sub
      (hφ.comp (contDiff_const.prodMk (contDiff_fst.snd.prodMk contDiff_snd)))
  have hF k i j : ContDiffOn ℝ ∞ (F k i j) (univ ×ˢ D) :=
    ((contDiff_const.mul (contDiff_oscillatoryFactor hphase K)).mul (hC k i j)).contDiffOn.mul
      ((contDiffOn_compactTransportMask hD hm k).comp contDiffOn_snd (fun _ hp ↦ hp.2))
  have hFs k i j p (hp : p ∉ (X ×ˢ X) ×ˢ V) : F k i j p = 0 := by
    simp only [F, hCs k i j p hp, mul_zero, zero_mul]
  obtain ⟨N, hN, _, _⟩ := exists_compactIntegratedChannels hD hX hV hSD F hF hFs
  refine ⟨N, ?_, ?_⟩
  · intro k f i
    refine (hN k f i).trans (Eventually.of_forall fun x ↦ ?_)
    apply Finset.sum_congr rfl
    intro j _
    have hc x y u : χ x u * C k i j (x, y) u * star (χ y u) = C k i j (x, y) u := by
      cases k with
      | none =>
          exact cutoff_mul_transportCoefficient hS.isClosed
            (a := fun s x u ↦ a s x u i) (b := fun s x u ↦ a s x u j)
            (fun s z hz ↦ hs i s z hz) (fun s z hz ↦ hs j s z hz) χ hχ s₀ x y (w (x, y)) u
      | some l =>
          exact cutoff_mul_transportVectorEntry
            (a := fun x u ↦ a s₀ x u i) (b := fun x u ↦ a s₀ x u j)
            (fun z hz ↦ hs i s₀ z hz) (fun z hz ↦ hs j s₀ z hz) χ hχ x y (w (x, y)) u l
    rw [fullNormalAmplitudeKernel_normalized_cutoff D scale K (φ s₀) χ
      (fun u z ↦ C k i j (splitPhysicalPositions z) u)
      (by simpa only [splitPhysicalPositions_pairedPosition] using hc)]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    dsimp only
    rw [splitPhysicalPositions_pairedPosition]
    congr 1
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hg k] with u hu
    simp only [F, hu]
    ring
  · obtain ⟨E', hd, he⟩ := exists_compactOscillatoryNormal_transportDerivative hD scale K
      hφ ha hS hSD hs hm (g none) (hg none) s₀ (fun x y ↦ w (x, y))
      (fun x y ↦ (hw.comp (contDiff_const.prodMk contDiff_id)).contDiffOn) hv
    apply hd.congr_deriv
    rw [← Fintype.sum_option]
    ext f i
    have hsum : ((∑ k, N k) f) i = ∑ k, (N k f) i := by
      rw [sum_apply]
      exact map_sum (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ Lp ℂ 2 (volume : Measure E)) i) (fun k ↦ N k f) Finset.univ
    rw [hsum]
    have hall : ∀ᵐ x ∂volume, ∀ k, (N k f) i x =
        ∑ j, ∫ y, (∫ u in D, F k i j ((x, y), u)) * f j y :=
      ae_all_iff.mpr (fun k ↦ hN k f i)
    filter_upwards [he f i, Lp.coeFn_fun_finsetSum Finset.univ (fun k ↦ (N k f) i), hall]
      with x hx hsum hxN
    rw [hx, hsum]
    simp_rw [hxN]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← integral_sum_compactChannels hD hX hV hSD (fun k ↦ F k i j)
      (fun k ↦ hF k i j) (fun k ↦ hFs k i j) (f j) x]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    dsimp only
    congr 1
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro u
    simp only [Fintype.sum_option, F, C, compactTransportEntry, compactTransportMask, A,
      Finset.mul_sum, mul_add]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro k _
      ring
end JanetCartan.NormalComparison
