module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalChange.IndividualBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.SmoothMap
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.SampledMetric

/-!
# The amplitude of the same physical canonical sum

For `app:ch_pairs:lem:pairs-ledger`, differentiate the actual finite sum of
prepared and raw corrected waves. Its demodulated derivative is exactly the
prepared base plus the canonical accumulation, using the same component
adjoints, inverse and residuals. Equality holds on the full supplied open
validity domain. Periodicity transfers the individual cell seminorm to every
point there; no inverse sample weights or assumed final amplitude estimate
enter this identification.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Finset
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CurrentMean
open ContinuumRow CanonicalChange SmoothPeriodicFamily UniformStep

variable {n N : ℕ} {ι : Type*}

/-- Demodulation distributes over the SAME finite physical wave sum on its
original phase (`app:ch_pairs:lem:pairs-ledger`). This uses ordinary
derivatives on the validity domain, so no boundary derivative is substituted. -/
theorem sampledDerivativeAmplitude_add_sum
    (Zc : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (W : ℕ → ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (θ : ι → Euclidean n → ℝ) (I : ℕ) (i : ι) (x : Euclidean n)
    (hZc : DifferentiableAt ℝ (Zc i) x)
    (hW : ∀ l < I, DifferentiableAt ℝ (W l i) x) :
    sampledDerivativeAmplitude (fun i ↦ Zc i + ∑ l ∈ range I, W l i) θ i x =
      sampledDerivativeAmplitude Zc θ i x +
        ∑ l ∈ range I, sampledDerivativeAmplitude (W l) θ i x := by
  classical
  have hsum : DifferentiableAt ℝ (∑ l ∈ range I, W l i) x :=
    DifferentiableAt.sum (fun l hl ↦ hW l (mem_range.mp hl))
  have hd : sampledDerivative (fun i ↦ Zc i + ∑ l ∈ range I, W l i) i x =
      sampledDerivative Zc i x + ∑ l ∈ range I, sampledDerivative (W l) i x := by
    change RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N
      (fderiv ℝ (Zc i + ∑ l ∈ range I, W l i) x) = _
    rw [fderiv_add hZc hsum, fderiv_sum (fun l hl ↦ hW l (mem_range.mp hl)), map_add, map_sum]
    rfl
  simp only [sampledDerivativeAmplitude, hd, smul_add, Finset.smul_sum]

variable {Raw : ι → Type*} [∀ i, NormedAddCommGroup (Raw i)]
    [∀ i, InnerProductSpace ℝ (Raw i)] [∀ i, CompleteSpace (Raw i)]

/-- The actual physical waves evaluated at the original component adjoints
have exactly the smooth amplitude used by the canonical recurrence
(`main:eq:old-canonical`, `app:ch_pairs:lem:pairs-ledger`). Only the original
prepared and raw-atom realization identities are inputs; the final identity
is proved by differentiating the literal finite sum. -/
theorem sampledDerivativeAmplitude_add_canonicalSum_eqOn
    (Zc : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (W : ℕ → ∀ i, Raw i → Euclidean n → EuclideanSpace ℂ (Fin N))
    (θ : ι → Euclidean n → ℝ)
    (base : SmoothPeriodicFamily n ι (Matrix (Fin N) (Fin n) ℂ))
    (G : ℕ → ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (A : ℕ → ∀ i, Raw i →L[ℝ] OutputL2 n)
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (e : ℕ → OutputL2 n) (I : ℕ)
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hZc : ∀ i, ContDiffOn ℝ ∞ (Zc i) U)
    (hW : ∀ l < I, ∀ i v, ContDiffOn ℝ ∞ (W l i v) U)
    (hbase : ∀ i, EqOn (sampledDerivativeAmplitude Zc θ i)
      (periodicLift (fun x ↦ base.val x i)) U)
    (hraw : ∀ l < I, ∀ i v, EqOn
      (sampledDerivativeAmplitude (fun _ : Unit ↦ W l i v) (fun _ ↦ θ i) ())
      (periodicLift (fun x ↦ (G l i v).val x ())) U) :
    ∀ i, EqOn
      (sampledDerivativeAmplitude
        (fun i ↦ Zc i + ∑ l ∈ range I, W l i ((A l i).adjoint (Q₀ (e l)))) θ i)
      (periodicLift (fun x ↦
        (base + ∑ l ∈ range I, smoothCanonicalDerivative (A l) (G l) Q₀ (e l)).val x i)) U := by
  classical
  intro i x hx
  rw [sampledDerivativeAmplitude_add_sum Zc
    (fun l i ↦ W l i ((A l i).adjoint (Q₀ (e l)))) θ I i x
    ((hZc i).differentiableOn (by simp) x hx |>.differentiableAt (hU.mem_nhds hx))
    (fun l hl ↦ (hW l hl i _).differentiableOn (by simp) x hx |>.differentiableAt (hU.mem_nhds hx)),
    hbase i hx]
  change base.val (torusQuotient x) i + _ = _
  simp only [periodicLift, Function.comp_apply, Submodule.coe_add, Submodule.coe_sum,
    Pi.add_apply, Finset.sum_apply]
  congr 1
  apply sum_congr rfl
  intro l hl
  exact hraw l (mem_range.mp hl) i _ hx

/-- All physical jets of the SAME final sampled amplitude are controlled
by the individual canonical seminorm (`app:ch_pairs:lem:pairs-ledger`).
The entire open validity domain is retained. Its seminorm is bounded by
`exists_admissible_history_originalScale_canonicalRun_individual_profiles`;
this theorem adds no analytic final-amplitude premise. -/
theorem norm_iteratedFDeriv_sampledDerivativeAmplitude_add_canonicalSum_le
    (Zc : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (W : ℕ → ∀ i, Raw i → Euclidean n → EuclideanSpace ℂ (Fin N))
    (θ : ι → Euclidean n → ℝ)
    (base : SmoothPeriodicFamily n ι (Matrix (Fin N) (Fin n) ℂ))
    (G : ℕ → ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (A : ℕ → ∀ i, Raw i →L[ℝ] OutputL2 n)
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (e : ℕ → OutputL2 n) (I : ℕ)
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hZc : ∀ i, ContDiffOn ℝ ∞ (Zc i) U)
    (hW : ∀ l < I, ∀ i v, ContDiffOn ℝ ∞ (W l i v) U)
    (hbase : ∀ i, EqOn (sampledDerivativeAmplitude Zc θ i)
      (periodicLift (fun x ↦ base.val x i)) U)
    (hraw : ∀ l < I, ∀ i v, EqOn
      (sampledDerivativeAmplitude (fun _ : Unit ↦ W l i v) (fun _ ↦ θ i) ())
      (periodicLift (fun x ↦ (G l i v).val x ())) U)
    (s : ℕ) (i : ι) {x : Euclidean n} (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ s
      (sampledDerivativeAmplitude
        (fun i ↦ Zc i + ∑ l ∈ range I, W l i ((A l i).adjoint (Q₀ (e l)))) θ i) x‖ ≤
      componentCSeminorm s i
        (base + ∑ l ∈ range I, smoothCanonicalDerivative (A l) (G l) Q₀ (e l)) := by
  let family := base + ∑ l ∈ range I, smoothCanonicalDerivative (A l) (G l) Q₀ (e l)
  have heq := sampledDerivativeAmplitude_add_canonicalSum_eqOn Zc W θ base G A Q₀ e I hU hZc hW hbase hraw i
  have hlocal := hU.mem_nhds hx
  have hev : sampledDerivativeAmplitude
      (fun i ↦ Zc i + ∑ l ∈ range I, W l i ((A l i).adjoint (Q₀ (e l)))) θ i =ᶠ[nhds x]
        periodicLift (fun y ↦ family.val y i) := Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hlocal, heq⟩
  rw [(hev.iteratedFDeriv ℝ s).eq_of_nhds]
  apply norm_iteratedFDeriv_periodicLift_le
  intro y hy
  exact norm_iteratedFDeriv_le_cNorm (isCompact_fundamentalCell n)
    ((smooth family i).2.of_le (by simp)) hy le_rfl

end JanetCartan.CurrentMean
