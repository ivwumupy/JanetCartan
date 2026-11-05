module
public import JanetCartan.Iteration.PhysicalPairs.Secondary

/-! # No rounding loss at fractional physical Sobolev orders

For the Euclidean-radian weight, split at the *actual* coarse carrier λ. Below
it the L² estimate suffices; above it use the next integer derivative multiplied
by λ^(r-⌈r⌉). Thus the true exponent remains r+1 for every real r≥0,
not ⌈r⌉+1. Consumer: `main:eq:pair-high-size`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
open MeasureTheory FourierTransform
open scoped SchwartzMap
namespace JanetCartan.PhysicalPairs.FractionalSize
open Pseudodifferential PhysicalCutoff LocalSobolev
variable {n N : ℕ}
local notation "E" => Euclidean n
local notation "V" => Euclidean N
local notation "Z" => EuclideanSpace ℂ (Fin N)

private theorem weight_power (s : ℝ) (ξ : E) : euclideanSobolevWeight s ξ = (euclideanSobolevWeight 1 ξ)^s := by
  unfold euclideanSobolevWeight
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  ring

private theorem weight_split {lam r k : ℝ} (hl : 0 < lam) (h : 0 ≤ r) (hh : r ≤ k) (ξ : E) :
    euclideanSobolevWeight r ξ ≤ lam^r + lam^(r-k)*euclideanSobolevWeight k ξ := by
  let b := euclideanSobolevWeight 1 ξ
  have hb : 0 < b := euclideanSobolevWeight_pos _ _
  rw [weight_power r,weight_power k]
  change b^r ≤ lam^r + lam^(r-k)*b^k
  by_cases he : b ≤ lam
  · exact (Real.rpow_le_rpow hb.le he h).trans (le_add_of_nonneg_right (by positivity))
  · have e : b^r = b^(r-k)*b^k := by rw [←Real.rpow_add hb]; congr 1; ring
    exact (e.le.trans (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hl (le_of_not_ge he) (sub_nonpos.mpr hh)) (Real.rpow_nonneg hb.le _))).trans (le_add_of_nonneg_left (by positivity))

def normAt (s : ℝ) (u : 𝓢(E,V)) := (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ((2*Real.pi) • ξ) • 𝓕 (complexify u) ξ) 2 volume).toReal

theorem split {lam r k : ℝ} (hl : 0 < lam) (h : 0 ≤ r) (hh : r ≤ k) (u : 𝓢(E,V)) :
    normAt r u ≤ lam^r*normAt 0 u + lam^(r-k)*normAt k u := by
  let v := fun (s : ℝ) (ξ : E) ↦ euclideanSobolevWeight s ((2*Real.pi) • ξ) • 𝓕 (complexify u) ξ
  let a := lam^r
  let b := lam^(r-k)
  have ha : 0 ≤ a := Real.rpow_nonneg hl.le _
  have hb : 0 ≤ b := Real.rpow_nonneg hl.le _
  have h0 : MemLp (a • v 0) 2 volume := (memLp_physicalWeightedFourier 0 u).const_smul a
  have hk : MemLp (b • v k) 2 volume := (memLp_physicalWeightedFourier k u).const_smul b
  have hp : eLpNorm (v r) 2 volume ≤ eLpNorm (a • v 0 + b • v k) 2 volume := by
    apply eLpNorm_mono (memLp_physicalWeightedFourier r u).aestronglyMeasurable
    intro ξ
    simp only [Pi.add_apply, Pi.smul_apply,v,euclideanSobolevWeight_zero,one_smul,smul_smul,←add_smul,norm_smul,
      Real.norm_of_nonneg (euclideanSobolevWeight_pos _ _).le,Real.norm_of_nonneg (add_nonneg ha (mul_nonneg hb (euclideanSobolevWeight_pos _ _).le))]
    exact mul_le_mul_of_nonneg_right (weight_split hl h hh _) (norm_nonneg _)
  have ht := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨h0.eLpNorm_ne_top,hk.eLpNorm_ne_top⟩)
    (hp.trans (eLpNorm_add_le (μ := volume) (f := a • v 0) (g := b • v k) (by norm_num)))
  rw [ENNReal.toReal_add h0.eLpNorm_ne_top hk.eLpNorm_ne_top] at ht
  simpa only [normAt,eLpNorm_const_smul,ENNReal.toReal_mul,toReal_enorm,Real.norm_of_nonneg ha,Real.norm_of_nonneg hb,v,a,b] using ht

def cost (D : ℕ → ℝ) (r : ℝ) := D 0 + D ⌈r⌉₊
theorem cost_nonneg {D : ℕ → ℝ} (hD : ∀ i, 0 ≤ D i) (r : ℝ) : 0 ≤ cost D r := add_nonneg (hD _) (hD _)

theorem all_real (u : 𝓢(E,V)) (D : ℕ → ℝ) (δ R A : ℝ) (hR : 1 ≤ R)
    (h : ∀ k : ℕ, normAt k u ≤ D k*δ^2*R^(2*A+1+samplingSlack)*(R^carrierExponent)^(k+1))
    (r : ℝ) (hr : 0 ≤ r) : normAt r u ≤ cost D r*δ^2*R^(2*A+1+samplingSlack)*(R^carrierExponent)^(r+1) := by
  let k := ⌈r⌉₊
  let lam := R^carrierExponent
  have hl : 0 < lam := Real.rpow_pos_of_pos (zero_lt_one.trans_le hR) _
  have hlr : lam^r*lam = lam^(r+1) := by rw [Real.rpow_add hl,Real.rpow_one]
  have hlk : lam^(r-(k:ℝ))*lam^(k+1) = lam^(r+1) := by
    rw [←Real.rpow_natCast,←Real.rpow_add hl]; congr 1; push_cast; ring
  have h₀ := h 0
  simp only [Nat.cast_zero,Nat.zero_add,pow_one] at h₀
  calc
    _ ≤ lam^r*normAt 0 u + lam^(r-k)*normAt k u := split hl hr (Nat.le_ceil r) u
    _ ≤ lam^r*(D 0*δ^2*R^(2*A+1+samplingSlack)*lam) + lam^(r-k)*(D k*δ^2*R^(2*A+1+samplingSlack)*lam^(k+1)) :=
      add_le_add (mul_le_mul_of_nonneg_left h₀ (Real.rpow_nonneg hl.le _)) (mul_le_mul_of_nonneg_left (h k) (Real.rpow_nonneg hl.le _))
    _ = D 0*δ^2*R^(2*A+1+samplingSlack)*(lam^r*lam) + D k*δ^2*R^(2*A+1+samplingSlack)*(lam^(r-k)*lam^(k+1)) := by ring
    _ = _ := by rw [hlr,hlk]; unfold cost; change _ = (D 0+D k)*δ^2*R^_ *lam^(r+1); ring
end JanetCartan.PhysicalPairs.FractionalSize
end
