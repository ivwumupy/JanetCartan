module

public import JanetCartan.Analysis.Fourier.SeparatedSampling
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundQuadrature.Exactness

/-!
# Window support and finite quadrature

The actual convolved-box product window and its finite sampled mass in
`app:ch_waves:eq:background-quadrature`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff

namespace JanetCartan.Sampling.BackgroundQuadrature
open SeparatedSampling LatticeQuadrature

/-- The actual mollified box window satisfies the deterministic sampling bounds,
with upper bound one, by its translated partition of unity
(`app:ch_waves:thm:sampling`). -/
theorem convolvedBoxWindow_bounds {κ : ℝ → ℝ} (hi : Integrable κ)
    (hm : ∫ x, κ x = 1) (hn : ∀ x, 0 ≤ κ x)
    (hs : Function.support κ ⊆ Set.Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) : WindowBounds p (convolvedBoxWindow κ p) 1 where
  nonneg := convolvedBoxWindow_nonneg hn p
  le_bound x := by
    simpa using le_hasSum (hasSum_convolvedBoxWindow hi hm hp x) 0
      (fun j _ ↦ convolvedBoxWindow_nonneg hn p (x + j))
  support x hx := by
    have ht := support_convolvedBoxWindow_subset hs p hx
    rw [abs_le]
    dsimp [windowRadius]
    constructor <;> linarith [ht.1, ht.2]

/-- Support of the tensor window lies in the fixed carrier cube
(`app:ch_waves:eq:background-quadrature`). -/
theorem productWindow_support_norm {p : ℕ} {w : ℝ → ℝ} {M : ℝ}
    (hw : WindowBounds p w M) {x : Point} (hx : productWindow w x ≠ 0) :
    ‖x‖ ≤ windowRadius p := by
  apply (pi_norm_le_iff_of_nonneg (by dsimp [windowRadius]; positivity)).mpr
  intro i
  exact (Real.norm_eq_abs _).symm ▸ hw.support _
    ((Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i))

/-- Compact support of the product window, in the coordinate cube of
`app:ch_waves:thm:sampling`. -/
theorem hasCompactSupport_productWindow {p : ℕ} {w : ℝ → ℝ} {M : ℝ}
    (hw : WindowBounds p w M) : HasCompactSupport (productWindow (n := 3) w) := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin 3 ↦ -windowRadius p)
      (fun _ ↦ windowRadius p)))
  intro x hx
  by_contra hn
  apply hx
  have hb (i) := hw.support (x i) ((Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ i))
  exact ⟨fun i ↦ (abs_le.mp (hb i)).1, fun i ↦ (abs_le.mp (hb i)).2⟩

/-- Integrability of windowed continuous Banach-valued carrier functions
(`app:ch_waves:eq:background-quadrature`). -/
theorem integrable_productWindow_smul {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {p : ℕ} {w : ℝ → ℝ} {M : ℝ}
    (hw : WindowBounds p w M) (hwc : Continuous w) {f : Point → V} (hf : Continuous f) :
    Integrable (fun x ↦ productWindow w x • f x) := by
  apply (Continuous.smul (continuous_finsetProd _ fun i _ ↦
    hwc.comp (continuous_apply i)) hf).integrable_of_hasCompactSupport
  exact (hasCompactSupport_productWindow hw).smul_right

/-- Outside the existing offset enumeration the translated product window is
zero. This proves finiteness without discarding nonzero samples
(`app:ch_waves:thm:sampling`). -/
theorem productWindow_eq_zero_outside_offsets {p : ℕ} {w : ℝ → ℝ} {M : ℝ}
    (hw : WindowBounds p w M) {u : Point} (hu : ∀ i, 0 ≤ u i ∧ u i < 1)
    {m : Lattice} (hm : m ∉ integerCube (p + 2)) :
    productWindow w (fun i ↦ u i + m i) = 0 := by
  by_contra hn
  apply hm
  apply mem_integerCube.mpr
  intro i
  have hs := hw.support _ ((Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ i))
  have hu' := hu i
  have hpn : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hb : |(m i : ℝ)| ≤ ((p + 2 : ℕ) : ℝ) := by
    rw [abs_le] at hs ⊢
    dsimp [windowRadius] at hs
    push_cast
    constructor <;> linarith [hs.1, hs.2]
  exact_mod_cast hb

/-- The finite offset enumeration has exactly mass one at every admissible
normalized shift (`app:ch_waves:eq:background-quadrature`). -/
theorem sum_productWindow_offsets {κ : ℝ → ℝ} (hi : Integrable κ)
    (hm : ∫ x, κ x = 1) {p : ℕ} (hp : 0 < p) {M : ℝ}
    (hw : WindowBounds p (convolvedBoxWindow κ p) M)
    {u : Point} (hu : ∀ i, 0 ≤ u i ∧ u i < 1) :
    ∑ m ∈ integerCube (p + 2),
      productWindow (convolvedBoxWindow κ p) (fun i ↦ u i + m i) = 1 :=
  (hasSum_sum_of_ne_finset_zero (fun _ hm ↦
    productWindow_eq_zero_outside_offsets hw hu hm)).unique
      (hasSum_productWindow hi hm hp u)

/-- Exact cancellation on the literal finite offset cube of the Banach-valued
Taylor polynomial (`app:ch_waves:eq:background-quadrature`). -/
theorem sum_carrierTaylor_offsets {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] {κ : ℝ → ℝ}
    (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ) {p : ℕ} {M : ℝ}
    (hw : WindowBounds p (convolvedBoxWindow κ p) M)
    (f : Point → V) (x : Point) (h : ℝ) {u : Point}
    (hu : ∀ i, 0 ≤ u i ∧ u i < 1) :
    (∑ m ∈ integerCube (p + 2),
      productWindow (convolvedBoxWindow κ p) (fun i ↦ u i + m i) •
        carrierTaylor f p x (h • (fun i ↦ u i + m i))) =
      ∫ y : Point, productWindow (convolvedBoxWindow κ p) y •
        carrierTaylor f p x (h • y) := by
  apply (hasSum_sum_of_ne_finset_zero ?_).unique
    (hasSum_carrierTaylor_productWindow hc hs f p x h u)
  intro m hm
  rw [productWindow_eq_zero_outside_offsets hw hu hm, zero_smul]

end JanetCartan.Sampling.BackgroundQuadrature
