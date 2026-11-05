module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.InactiveDerivatives.UniformPhase.Directions

/-!
# Uniform Sobolev profile for the original carrier derivative

The common constants precede phase, frequency, scale, original source,
parameter and unit direction tuples. This is the source-facing input to
inactive arbitrary precision in `app:ch_response:thm:response-literal-transfer`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.UniformPhase
open Pseudodifferential
variable {p d r : ℕ}
local notation "P" => Euclidean p
local notation "E" => Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- The common actual Sobolev profile, using only fixed dimensions, support
volume and primitive joint phase/original source constants. Source:
`app:ch_response:thm:response-literal-transfer`. -/
def unitSobolevBudget (d r : ℕ) (S : Set E) (H : ℕ → ℝ)
    (C : ℕ → ℕ → ℝ) (k j : ℕ) : ℝ :=
  ((r : ℝ) * (1 + (d : ℝ)) ^ j * Real.sqrt (volume.real S)) *
    ∑ i ∈ Finset.range (j + 1), unitSpatialBudget d H C k i

/-- Nonnegativity of the common Sobolev profile. Source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem unitSobolevBudget_nonneg (S : Set E) {H : ℕ → ℝ}
    (hH : ∀ j, 0 ≤ H j) (C : ℕ → ℕ → ℝ) (k j : ℕ) :
    0 ≤ unitSobolevBudget d r S H C k j := by
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun i _ ↦ unitSpatialBudget_nonneg hH C k i)

/-- Actual Sobolev estimate for the normalized `k`th derivative of the SAME
original carrier source, uniform over phase and unit directions. It consumes
primitive joint phase orders through `j+k` and original source Sobolev orders
through `j+d+1`, at parameter orders through `k`. The only fixed extra scale
cost is `ρ^k K^(k+d+1)`, independent of accuracy and spatial order.

The phase producer is FullPhaseCharts/SharpPhaseBounds and the original source
producer is CoefficientScale; their concrete history instantiation belongs to
the correction-step consumers. Source: `app:ch_response:thm:response-literal-transfer`.
-/
theorem norm_parameterCarrierJet_sobolev_le_unit
    {V B : Set P} {U S : Set E} (hV : IsOpen V) (hU : IsOpen U)
    (hBV : B ⊆ V) (hS : IsCompact S) (hSU : S ⊆ U)
    (H : ℕ → ℝ) (hH : ∀ m, 0 ≤ H m) (C : ℕ → ℕ → ℝ)
    (k : ℕ) (ρ A K : ℝ) (hρ : 1 ≤ ρ) (hA : 0 ≤ A) (hK : 1 ≤ K)
    {φ : P → E → ℝ} (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ U))
    {f : P → E → F} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (V ×ˢ univ))
    (hs : ∀ a ∈ V, tsupport (f a) ⊆ S) {c : P} (hc : c ∈ B)
    (hm : ∀ vs : List P, MemLp (fun x ↦ parameterListJet (fun a ↦ f a x) vs c) 2 volume)
    (hmem : ∀ vs (j : ℕ), MemVectorFourierSobolev (j : ℝ) ((hm vs).toLp _))
    (hprofile : ∀ vs, vs.length ≤ k → (∀ w ∈ vs, ‖w‖ ≤ 1) → ∀ j : ℕ,
      vectorFourierSobolevNorm (j : ℝ) ((hm vs).toLp _) ≤
        C vs.length j * (A * K ^ vs.length) * K ^ j)
    (v : Fin k → P) (hv : ∀ i, ‖v i‖ ≤ 1) (j : ℕ)
    (hphase : ∀ x ∈ S, ∀ m ≤ j + k,
      ‖iteratedFDeriv ℝ m (Function.uncurry φ) (c, x)‖ ≤ H m * K ^ m) :
    vectorFourierSobolevNorm (j : ℝ)
      ((memLp_parameterCarrierJet_of_original hV hU hS hSU ρ hφ hf hs k v (hBV hc)).toLp
        (parameterCarrierJet ρ φ f k v c)) ≤
      unitSobolevBudget d r S H C k j * (A * ρ ^ k * K ^ (k + d + 1)) * K ^ j := by
  let J := unitSpatialBudget d H C k
  have hJ : ∀ i, 0 ≤ J i := unitSpatialBudget_nonneg hH C k
  have hsum : 0 ≤ ∑ i ∈ Finset.range (j + 1), J i :=
    Finset.sum_nonneg fun i _ ↦ hJ i
  have hAmp : 0 ≤ A * ρ ^ k * K ^ (k + d + 1) := by positivity
  apply (vectorSobolev_le_compactJets hS j _
    (contDiff_parameterCarrierJet_of_original hV hU hS hSU ρ hφ hf hs k v (hBV hc))
    (tsupport_parameterCarrierJet_subset_original hV hS ρ φ f hs k v (hBV hc))
    _ (mul_nonneg (mul_nonneg hsum hAmp) (pow_nonneg (zero_le_one.trans hK) j))
    ?_).trans_eq (by dsimp [unitSobolevBudget, J]; ring)
  intro i hi x
  apply (norm_parameterCarrierJet_spatial_le_unit hV hU hBV hS hSU H hH C k ρ A K
    hρ hA hK hφ hf hs hc hm hmem hprofile v hv i
    (fun x hx m hm ↦ hphase x hx m (by omega)) x).trans
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun l _ ↦ hJ l) (Finset.mem_range_succ_iff.mpr hi)) hAmp)
    (pow_le_pow_right₀ hK hi) (pow_nonneg (zero_le_one.trans hK) i)
    (mul_nonneg hsum hAmp)

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.UniformPhase
