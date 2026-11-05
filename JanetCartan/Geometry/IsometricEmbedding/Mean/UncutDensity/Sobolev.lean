module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.UncutDensity.RawLimit
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.WeightedInput

/-!
# Uncut density on the full mixed initial Sobolev domain

For `app:ch_background:eq:bg-density-four`, `app:ch_background:eq:bg-density-twice`
and `app:ch_mean_pairs:eq:mean-density-recursion`, the full mixed raw regularity
now supplies the transverse weighted membership used in the literal integral
passage. This uses the proved comparison for the existing `MemRawSobolev`,
which retains every physical `z,y` derivative and the actual partial unitary
radian transform. No additional initial scale or weighted-membership premise
is introduced.

The initial-adjoint and inverse producers must establish this full membership
for their actual raw inputs. The continuum-row and positive-background owners
must supply the primitive geometric hypotheses below. Neither obligation is
asserted by these conditional density identities.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace JanetCartan.UncutDensity
open ContinuumRow CarrierSobolev RawCutoffBounds ContinuumAdjoint.DensityMultiplier

variable {n N : ℕ}

/-- The existing full mixed raw membership supplies the density multiplier's
transverse weight (`app:ch_background:eq:bg-density-four`). The two published
weights have exactly the same formula; the nontrivial comparison is the shared
full physical Sobolev theorem. -/
theorem carrierWeightedMem_of_memRawSobolev {s : ℕ} {f : CarrierL2 n}
    (hf : MemRawSobolev s f) : CarrierWeightedMem (etaBesselWeight s) f :=
  hf.carrierWeightedMem_transverseBesselWeight

/-- Literal synthesis agrees with the partial unitary inverse, including its
exact `synthesisFactor`, on the full mixed raw domain supplied by the initial
adjoint (`app:ch_background:eq:bg-density-four`). Multiplier L² membership and
frequency-slice integrability are consequences, not additional hypotheses. -/
theorem realSynthesisL2_sobolev_coeFn (d : CarrierData n N) (s : ℕ)
    (hs : n - 1 < 2 * s)
    (hρm : Measurable (fun p : CarrierVariable n ↦ (d.angularCutoff p.1 p.2 : ℂ)))
    (hhm : Measurable d.highCutoff) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hρ : ∀ z θ, |d.angularCutoff z θ| ≤ A)
    (hhi : ∀ r, |d.highCutoff r| ≤ B)
    (c : ℝ) (f : CarrierL2 n) (hf : MemRawSobolev (s + 1) f) :
    ∃ hg : MemLp (fun p ↦ carrierDensitySymbol d p * f p) 2 (carrierMeasure n),
      realSynthesisL2 c (hg.toLp _) =ᵐ[carrierMeasure n] initialDensity d c f :=
  realSynthesisL2_raw_coeFn d s hs hρm hhm hA hB hρ hhi c f
    (carrierWeightedMem_of_memRawSobolev hf)

section Geometry

variable (d : CarrierData n N) (s : ℕ) (hs : n - 1 < 2 * s)
    (χ : CarrierParameter → ℝ)
    (hχ : ∀ z θ, d.angularCutoff z θ ≠ 0 → χ z = 1)
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ u : carrierInitialTestSpace n,
      U (carrierInitialTestToLp u) =ᵐ[volume] carrierTestIntegral d u.val)
    (hk : ∀ x, AEStronglyMeasurable (carrierKernel d x) (carrierMeasure n))
    {K : Set CarrierParameter} (hK : IsCompact K)
    (hsupp : ∀ z ∉ K, ∀ θ, d.angularCutoff z θ = 0)
    (hst : ∀ x, ContinuousOn (measuredStress d x) K)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hρ : ∀ z θ, |d.angularCutoff z θ| ≤ A)
    (hhi : ∀ r, |d.highCutoff r| ≤ B)

include hs hχ hU hk hK hsupp hst hA hB hρ hhi

/-- Full mixed regularity suffices for the literal measured identity. The
coefficient is `c/2`, so this includes both paper coefficients without any
cutoff in the initial spatial variables (`app:ch_background:eq:bg-density-twice`,
`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem measuredIncrement_sobolev_coeFn (c : ℝ) (f : CarrierL2 n)
    (hf : MemRawSobolev (s + 1) f) :
    measuredIncrement d (fun z ↦ χ z ^ 2) (initialDensity d c f) =ᵐ[volume]
      ((c / 2) • carrierChannel U f : OutputL2 n) :=
  measuredIncrement_raw_coeFn d s hs χ hχ U hU hk hK hsupp hst hA hB hρ hhi c f
    (carrierWeightedMem_of_memRawSobolev hf)

/-- The transported density is an actual output L² function on the full
mixed raw domain (`app:ch_background:eq:bg-density-twice`). -/
theorem measuredIncrement_sobolev_memLp (c : ℝ) (f : CarrierL2 n)
    (hf : MemRawSobolev (s + 1) f) :
    MemLp (measuredIncrement d (fun z ↦ χ z ^ 2) (initialDensity d c f)) 2 volume :=
  measuredIncrement_raw_memLp d s hs χ hχ U hU hk hK hsupp hst hA hB hρ hhi c f
    (carrierWeightedMem_of_memRawSobolev hf)

/-- Strong domain passage for literal transported densities on the existing
full mixed raw domain. L² convergence suffices; uniform higher bounds are not
required (`app:ch_background:eq:bg-density-twice`). In particular this applies
to any regular approximation of the carrier slots of `A* Q₀ e`. -/
theorem measuredIncrement_sobolev_tendsto (c : ℝ) (f : ℕ → CarrierL2 n) (g : CarrierL2 n)
    (hf : ∀ k, MemRawSobolev (s + 1) (f k)) (hg : MemRawSobolev (s + 1) g)
    (hlim : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun k ↦ (measuredIncrement_sobolev_memLp d s hs χ hχ U hU hk hK hsupp hst
      hA hB hρ hhi c (f k) (hf k)).toLp _) atTop
      (𝓝 ((measuredIncrement_sobolev_memLp d s hs χ hχ U hU hk hK hsupp hst
        hA hB hρ hhi c g hg).toLp _)) :=
  measuredIncrement_raw_tendsto d s hs χ hχ U hU hk hK hsupp hst hA hB hρ hhi c f g
    (fun k ↦ carrierWeightedMem_of_memRawSobolev (hf k))
    (carrierWeightedMem_of_memRawSobolev hg) hlim

end Geometry
end JanetCartan.UncutDensity
