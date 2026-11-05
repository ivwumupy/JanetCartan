module
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.PhysicalBounds
/-! # Slow jets on the original uncut angular integral

Use the actual L¹ mass, not the `K^(n/2)` Hilbert norm estimate. The
parameter window is the inverse image of the original open window for the
Fourier datum. No change of variables in the integral or Fourier normalization
is made. Consumer: the nonzero, whole-source node contribution to
`main:eq:pair-error` and `app:ch_waves:eq:raw-physical-bound`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option warningAsError true
open Set Metric MeasureTheory Filter
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPairs.AngularMassJets
open RawPrimary RawInputPartition
variable {n N J : ℕ}
local notation "E" => Euclidean n
local notation "P" => Euclidean (n-1)
local notation "H" => Matrix (Fin N) (Fin n) ℂ
/-- Express the same open Fourier window in the unscaled angular variable. -/
def window (ζ : P) (τ : ℝ) (V : Set P) : Set P := (fun ξ ↦ τ⁻¹ • (ξ-ζ)) ⁻¹' V
private theorem window_open {ζ : P} {τ : ℝ} {V : Set P} (hV : IsOpen V) : IsOpen (window ζ τ V) := hV.preimage (by fun_prop)
/-- Restrict smoothness on the native physical/angular cell to the unchanged
fixed spatial patch and the original shifted Fourier window. -/
theorem slice_smooth {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Set (E × (Euclidean 3 × P))} {X : Set E} {V : Set P}
    {z : Euclidean 3} {ζ : P} {τ : ℝ} (hτ : τ ≠ 0)
    (hshift : ∀ p ∈ X ×ˢ V, (p.1,(z,ζ + τ • p.2)) ∈ Ω)
    {A : E × (Euclidean 3 × P) → F} (hA : ContDiffOn ℝ ∞ A Ω) :
    ContDiffOn ℝ ∞ (Function.uncurry (fun x ξ ↦ A (x,(z,ξ)))) (X ×ˢ window ζ τ V) := by
  apply hA.comp (contDiffOn_fst.prodMk (contDiffOn_const.prodMk contDiffOn_snd))
  rintro ⟨x,ξ⟩ ⟨hx,hξ⟩
  have ht := hshift (x,τ⁻¹ • (ξ-ζ)) ⟨hx,hξ⟩
  simpa only [smul_smul, mul_inv_cancel₀ hτ, one_smul, add_sub_cancel] using ht
/-- From the literal whole-wave integral identity to sharp pointwise
spatial jets. The only derivative inputs are for a single angular atom and the
mixed phase, never the complete modulated wave. No loss from band cardinality
or Hilbert-to-mass conversion. -/
theorem point_grade {X : Set E} {V : Set P} {ζ : P} {τ : ℝ}
    {S : E → P → ℝ} {A : E → P → H} (hX : IsOpen X) (hV : IsOpen V)
    (hceil : closedBall 0 ((2:ℝ)^J) ⊆ V) (hτ : τ ≠ 0)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ window ζ τ V))
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (X ×ˢ window ζ τ V))
    {d : P → ℂ} {M : ℝ} (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)
    (v : WideInput n J) {g : E → H}
    (hg : EqOn g (rawPrimaryDemodulatedIntegral S A ζ τ volume (weightedWideDensity d v)) X)
    (a p : ℕ → ℝ) {L : ℝ} (hL : 1 ≤ L) (k : ℕ)
    (ha : ∀ j ≤ k, 0 ≤ a j) (hp : ∀ j, 1 ≤ j → j ≤ k → 0 ≤ p j)
    (hAj : ∀ j ≤ k, ∀ x ∈ X, ∀ ξ ∈ window ζ τ V, ‖iteratedFDeriv ℝ j (fun y ↦ A y ξ) x‖ ≤ a j * L^j)
    (hPj : ∀ j, 1 ≤ j → j ≤ k → ∀ x ∈ X, ∀ ξ ∈ window ζ τ V, ‖iteratedFDeriv ℝ j (fun y ↦ fderiv ℝ (S y) ξ) x‖ ≤ p j * L^(j-1))
    (x : E) (hx : x ∈ X) : ‖iteratedFDeriv ℝ k g x‖ ≤ rawPhysicalConstant 1 a p k * ((2:ℝ)^J+L)^k * ∫ η, ‖weightedWideDensity d v η‖ := by
  let K : ℝ := 2^J
  have hK : 1 ≤ K := one_le_pow₀ (by norm_num)
  have hW := window_open (ζ := ζ) (τ := τ) hV
  have hz : ζ ∈ window ζ τ V := by simpa [window] using hceil (mem_closedBall_self (zero_le_one.trans hK))
  have seg : ∀ η ∈ closedBall (0:P) (1*K), ∀ t ∈ Icc (0:ℝ) 1, ζ+(t*τ) • η ∈ window ζ τ V := by
    intro η hη t ht
    change τ⁻¹ • (ζ+(t*τ) • η - ζ) ∈ V
    rw [add_sub_cancel_left,smul_smul,← mul_left_comm,inv_mul_cancel₀ hτ,mul_one]
    apply hceil
    simp only [mem_closedBall_zero_iff,one_mul] at hη ⊢
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans hη
  have hf : ∀ᵐ η ∂volume, η ∉ closedBall (0:P) (1*K) → weightedWideDensity d v η = 0 := by
    filter_upwards [] with η hη
    apply wideDensity_eq_zero_of_ceiling_le
    simpa [K] using le_of_lt (lt_of_not_ge (by simpa only [one_mul,mem_closedBall_zero_iff] using hη))
  let : IsFiniteMeasure (volume.restrict (closedBall (0:P) (1*K))) := isFiniteMeasure_restrict.mpr (isCompact_closedBall _ _).measure_lt_top.ne
  have est := cNorm_rawPrimaryDemodulatedIntegral_le hX hW (singleton_subset_iff.mpr hx) hS hA hτ hz (by norm_num : (0:ℝ) ≤ 1) hK hL seg (integrable_wideDensity hd hM hb v) hf ha hp hAj hPj
  have germ := (eventuallyEq_of_mem (hX.mem_nhds hx) hg).iteratedFDeriv ℝ k
  rw [germ.eq_of_nhds]
  exact (norm_iteratedFDeriv_le_cNorm_of_bddAbove ((Set.finite_singleton x).image _).bddAbove (mem_singleton x) le_rfl).trans est
end JanetCartan.PhysicalPairs.AngularMassJets
end
