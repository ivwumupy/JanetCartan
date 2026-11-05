module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.DensityDiscrepancy.Bounds
public import JanetCartan.Analysis.Iteration.BackgroundPreparation

/-!
# Discrepancy inputs for finite positive-density preparation

The finite-order adapter for `app:ch_mean_pairs:prop:mean-coarse` derives the
exact `hE` and `hinit` premises of `finite_positive_density_preparation`.
Only bounds on the linear current and transport amplitudes are inputs.
The output seminorms are realized in normed spaces, e.g. the shared Fourier
Sobolev spaces. The realization identity specifies the actual measured integral;
it is not a bound on that integral. Parent constructions must supply it, together
with the current-atom bounds and the transport-density identity.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.DensityDiscrepancy
open BackgroundPreparation

variable {X P A V D W α ι a b : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [AddCommGroup A] [Module ℝ A] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup D] [Module ℝ D] [AddCommGroup W] [Module ℝ W]
  [MeasurableSpace α] [Fintype ι] [Fintype a] [Fintype b]

set_option backward.isDefEq.respectTransparency false in
/-- `app:ch_mean_pairs:eq:mean-density-lipschitz` and
`app:ch_mean_pairs:prop:mean-coarse`: one positive constant supplies precisely
`hE` and `hinit` at the finite backward reserves. It is chosen before the
frequency, masks, current/transport maps, and accuracy of any later mean solve.

`m s` is the explicit finite initial/carrier jet shift. Evaluation and jet
comparisons concern arbitrary density corrections. On the radius-`ρ` ball they
prove the positive class needed by the square-root estimate. The actual atom
bounds are the remaining responsibility of `jc-corrected-atoms` and
`jc-raw-primary-fields`; the measurement and integral identities belong to
`jc-positive-background` and `jc-current-mean`. -/
theorem exists_preparation_discrepancy_inputs
    (Y : ℕ → Type*) [∀ s, NormedAddCommGroup (Y s)] [∀ s, NormedSpace ℝ (Y s)]
    (μ : Measure α) [IsFiniteMeasure μ]
    (I : A →ₗ[ℝ] (X → ℝ)) (F : V →ₗ[ℝ] (P → Matrix a b ℂ))
    (L : ∀ s, (P → Matrix b b ℝ) →ₗ[ℝ] Y s)
    (realize : ∀ s, W →ₗ[ℝ] Y s)
    (p : ℕ → Seminorm ℝ D) (q : ℕ → Seminorm ℝ W)
    (hq : ∀ s e, q s e = ‖realize s e‖)
    (eval : D →ₗ[ℝ] (X → ℝ)) (m d k : ℕ → ℕ) (R S J : ℕ)
    {initial : Set X} (hi : IsCompact initial) {physical : Set P} (ht : IsCompact physical)
    (heval : ∀ s v x, |eval v x| ≤ p (m s) v)
    (hjets : ∀ s v, cNorm initial (m s) (eval v) ≤ p (m s) v)
    (hsmooth : ∀ s v, ContDiff ℝ (m s) (eval v))
    (hF : ∀ s v, ContDiff ℝ (k s) (F v))
    (r : X → ℝ) (hr : ∀ s, ContDiff ℝ (m s) r)
    (N C K : ℕ → ℝ) (hN : ∀ s, 0 ≤ N s) (hC : ∀ s, 0 ≤ C s) (hK : ∀ s, 0 ≤ K s)
    (hrN : ∀ s, cNorm initial (m s) r ≤ N s)
    (hL : ∀ s f, ContDiff ℝ (k s) f → ‖L s f‖ ≤ K s * cNorm physical (k s) f)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρhalf : ρ ≤ 1 / 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ (mask : ι → α → ℝ),
      (∀ i z, 0 ≤ mask i z) → (∀ z, ∑ i, mask i z = 1) →
      ∀ (Λ : ℝ), 0 < Λ → ∀ U T : ι → α → A →ₗ[ℝ] V,
      (∀ s i z u, cNorm physical (k s) (F (U i z u)) ≤
        C s * cNorm initial (m s) (I u)) →
      (∀ s i z u, cNorm physical (k s) (F (T i z u)) ≤
        C s * cNorm initial (m s) (I u)) →
      (∀ s i z u, cNorm physical (k s) (F ((U i z - T i z) u)) ≤
        Λ⁻¹ * C s * cNorm initial (m s) (I u)) →
      ∀ (amplitude : D → A) (E : D → W),
      (∀ s v, p (m s) v ≤ ρ → I (amplitude v) =
        (fun x ↦ positiveDensityAmplitude (r x) (eval v x))) →
      (∀ s v, p (m s) v ≤ ρ → realize s (E v) =
        integratedHermitianDiscrepancy μ mask F (L s) U T (amplitude v)) →
      (∀ s v, p (m s) v ≤ ρ → Integrable (fun z ↦ ∑ i, mask i z •
        squareDiscrepancy (measuredHermitianBilinear F (L s))
          (U i z) (T i z) (amplitude v)) μ) →
      (∀ l < J, ∀ v w,
        p (m (reserves m d R S l).2) v ≤ ρ →
        p (m (reserves m d R S l).2) w ≤ ρ →
        q (reserves m d R S l).2 (E v - E w) ≤
          B * Λ⁻¹ * p (m (reserves m d R S l).2) (v - w)) ∧
      q (reserves m d R S J).2 (E 0) ≤ B * Λ⁻¹ := by
  choose B hB hbounds using fun s ↦ exists_density_discrepancy_bounds (ι := ι) μ I F (L s)
    hi ht (m s) (k s) (hF s) r (hr s) hρ (hN s) (hC s) (hK s) (hrN s) (hL s)
  let cap := ∑ l ∈ Finset.range (J + 1), B (reserves m d R S l).2
  have hcap : 0 ≤ cap := Finset.sum_nonneg (fun _ _ ↦ (hB _).le)
  have hle (l : ℕ) (hl : l ≤ J) : B (reserves m d R S l).2 ≤ 1 + cap := by
    have hh : B (reserves m d R S l).2 ≤ cap :=
      Finset.single_le_sum (f := fun l ↦ B (reserves m d R S l).2)
        (fun _ _ ↦ (hB _).le)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))
    linarith
  refine ⟨1 + cap, by positivity, ?_⟩
  intro mask hm hpartition Λ hΛ U T hU hT hdiff amplitude E hamp hreal hint
  have hpositive (s : ℕ) (v : D) (hv : p (m s) v ≤ ρ) (x : X) :
      1 + eval v x ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) := by
    have hh := abs_le.mp ((heval s v x).trans (hv.trans hρhalf))
    constructor <;> linarith
  constructor
  · intro l hl v w hv hw
    let s := (reserves m d R S l).2
    have hb := (hbounds s mask hm hpartition Λ hΛ U T (hU s) (hT s) (hdiff s)).1
      (eval v) (eval w) (amplitude v) (amplitude w) (hsmooth s v) (hsmooth s w)
      ((hjets s v).trans hv) ((hjets s w).trans hw)
      (fun x ↦ by have hh := (hpositive s v hv x).1; linarith)
      (fun x ↦ by have hh := (hpositive s w hw x).1; linarith)
      (fun x _ ↦ hpositive s v hv x) (fun x _ ↦ hpositive s w hw x)
      (hamp s v hv) (hamp s w hw) (hint s v hv) (hint s w hw)
    rw [hq, map_sub, hreal s v hv, hreal s w hw]
    apply hb.trans
    have hj := hjets s (v - w)
    rw [map_sub] at hj
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right (hle l hl.le) (inv_nonneg.mpr hΛ.le)) hj
      (cNorm_nonneg _ _ _) (by positivity)
  · let s := (reserves m d R S J).2
    have hz : p (m s) 0 ≤ ρ := by simpa using hρ
    have ha₀ : I (amplitude 0) = r := by
      simpa only [map_zero, Pi.zero_apply, positiveDensityAmplitude_zero] using hamp s 0 hz
    rw [hq, hreal s 0 hz]
    exact ((hbounds s mask hm hpartition Λ hΛ U T (hU s) (hT s) (hdiff s)).2
      (amplitude 0) ha₀).trans
      (mul_le_mul_of_nonneg_right (hle J le_rfl) (inv_nonneg.mpr hΛ.le))

end JanetCartan.DensityDiscrepancy
