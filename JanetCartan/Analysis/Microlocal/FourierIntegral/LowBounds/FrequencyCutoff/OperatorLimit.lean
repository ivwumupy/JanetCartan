module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.FrequencyCutoff.GraphConvergence
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.FrequencyCutoff.Multipliers

/-!
# Frequency regularization of a realized bounded graph

For `app:ch_regular_base:thm:actual-calculus`, Step 1, the actual compact
graphs satisfy `T_j = T.comp P_j` whenever a bounded `T` realizes the uncut
source-first integral on Schwartz inputs. Density extends the literal Schwartz
factorization to the same vector Lebesgue L² used by `LowBounds.VectorGraph`.
Self-adjointness of `P_j` then gives strong convergence of both graphs and
their actual Hilbert adjoints. The latter are the literal reverse integrals
by `compactVectorGraph_adjoint_ae_reverseIntegral`.

These are conditional consequences, not an existence theorem for `T`.
The consuming source-independent low-bound construction must produce `T`
and its Schwartz realization from the uniform normal bound and density.
Neither a polynomial bound nor a new analytic premise is needed for the
factorization once that realization is supplied.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.LowBounds.FrequencyCutoff

variable {n r : ℕ}
local notation "ℋ" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (Euclidean n))
attribute [local instance] sourceSymbolContinuousENorm sourceSymbolPseudoMetrizableSpace

/-- The two constructed Schwartz inclusions agree in the actual vector L².
This connects graph convergence to the multiplier realization in
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem schwartzVectorToLp_eq_toEuclideanSchwartz_toLp
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ)) :
    schwartzVectorToLp u = (toEuclideanSchwartz u).toLp 2 := by
  apply Lp.ext
  exact (schwartzVectorToLp_ae u).trans ((toEuclideanSchwartz u).coeFn_toLp 2).symm

/-- Exact Schwartz preservation in the inclusion used by graph convergence,
for the density argument in `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem multiplier_schwartzVectorToLp (j : ℕ)
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ)) :
    multiplier j (schwartzVectorToLp u) =
      schwartzVectorToLp (schwartzMultiplier (Fin r → ℂ) j u) := by
  simp only [schwartzVectorToLp_eq_toEuclideanSchwartz_toLp,
    multiplier_toEuclideanSchwartz_toLp]

/-- If `T` realizes the uncut graph on Schwartz data, the actual compact
frequency graphs equal `T.comp P_j` on all vector Lebesgue L². The producer
of `T` and `hT` is the parent low-bound extension, which must establish both
from primitive data (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem compactVectorGraph_cut_eq_comp
    {S : Euclidean n → Euclidean n → ℝ}
    {A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    (hS : Continuous (Function.uncurry S)) (hA : Continuous (Function.uncurry A))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hsA : ∀ x η, x ∉ K → A x η = 0)
    (T : ℋ →L[ℂ] ℋ)
    (hT : ∀ u : SchwartzMap (Euclidean n) (Fin r → ℂ),
      T (schwartzVectorToLp u) =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η) u x)) (j : ℕ) :
    compactVectorGraph hS (cutAmplitude_entry_continuous hA j)
      (cutAmplitude_entry_hasCompactSupport hK hsA j) = T.comp (multiplier j) := by
  apply DFunLike.coe_injective
  apply denseRange_graphTestToLp.equalizer (map_continuous _) (map_continuous _)
  funext u
  change compactVectorGraph hS (cutAmplitude_entry_continuous hA j)
    (cutAmplitude_entry_hasCompactSupport hK hsA j) (graphTestToLp u) =
      T (multiplier j (graphTestToLp u))
  rw [← schwartzVectorToLp_graphTestToSchwartz u, multiplier_schwartzVectorToLp]
  apply Lp.ext
  refine (compactVectorGraph_schwartz_ae hS (cutAmplitude_entry_continuous hA j)
    (cutAmplitude_entry_hasCompactSupport hK hsA j) (graphTestToSchwartz u)).trans ?_
  rw [show (fun z _ η ↦ cutAmplitude A j z η) =
    (fun z _ η ↦ complexPhysicalCutoff j η • A z η) from rfl,
    graphOperator_eq_graphOperator_schwartzMultiplier]
  exact (hT _).symm

/-- The actual Hilbert adjoints factor as `P_j.comp T.adjoint`, using the
reality of the constructed cutoff. These are the literal reverse-integral
operators of `VectorGraph`, for `app:ch_regular_base:thm:actual-calculus`, Step 1.
The bounded uncut realization remains an explicit conditional input. -/
theorem compactVectorGraph_cut_adjoint_eq_comp
    {S : Euclidean n → Euclidean n → ℝ}
    {A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    (hS : Continuous (Function.uncurry S)) (hA : Continuous (Function.uncurry A))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hsA : ∀ x η, x ∉ K → A x η = 0)
    (T : ℋ →L[ℂ] ℋ)
    (hT : ∀ u : SchwartzMap (Euclidean n) (Fin r → ℂ),
      T (schwartzVectorToLp u) =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η) u x)) (j : ℕ) :
    (compactVectorGraph hS (cutAmplitude_entry_continuous hA j)
      (cutAmplitude_entry_hasCompactSupport hK hsA j)).adjoint =
        (multiplier j).comp T.adjoint := by
  rw [compactVectorGraph_cut_eq_comp hS hA hK hsA T hT,
    ContinuousLinearMap.adjoint_comp, multiplier_adjoint]

/-- Strong convergence of the actual compact graphs on every L² input,
conditional on the parent construction's bounded Schwartz realization.
Source: `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem compactVectorGraph_cut_tendsto_of_realizes
    {S : Euclidean n → Euclidean n → ℝ}
    {A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    (hS : Continuous (Function.uncurry S)) (hA : Continuous (Function.uncurry A))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hsA : ∀ x η, x ∉ K → A x η = 0)
    (T : ℋ →L[ℂ] ℋ)
    (hT : ∀ u : SchwartzMap (Euclidean n) (Fin r → ℂ),
      T (schwartzVectorToLp u) =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η) u x)) (f : ℋ) :
    Tendsto (fun j ↦ compactVectorGraph hS (cutAmplitude_entry_continuous hA j)
      (cutAmplitude_entry_hasCompactSupport hK hsA j) f) atTop (𝓝 (T f)) := by
  simp_rw [compactVectorGraph_cut_eq_comp hS hA hK hsA T hT,
    ContinuousLinearMap.comp_apply]
  exact (T.continuous.tendsto f).comp (multiplier_tendsto f)

/-- Strong convergence of the literal Hilbert adjoints on every L² input.
This follows from the exact factorization, not from strong convergence of
arbitrary operators. The parent must construct the bounded uncut `T` and
prove `hT` (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem compactVectorGraph_cut_adjoint_tendsto_of_realizes
    {S : Euclidean n → Euclidean n → ℝ}
    {A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    (hS : Continuous (Function.uncurry S)) (hA : Continuous (Function.uncurry A))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hsA : ∀ x η, x ∉ K → A x η = 0)
    (T : ℋ →L[ℂ] ℋ)
    (hT : ∀ u : SchwartzMap (Euclidean n) (Fin r → ℂ),
      T (schwartzVectorToLp u) =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η) u x)) (f : ℋ) :
    Tendsto (fun j ↦ (compactVectorGraph hS (cutAmplitude_entry_continuous hA j)
      (cutAmplitude_entry_hasCompactSupport hK hsA j)).adjoint f)
        atTop (𝓝 (T.adjoint f)) := by
  simp_rw [compactVectorGraph_cut_adjoint_eq_comp hS hA hK hsA T hT,
    ContinuousLinearMap.comp_apply]
  exact multiplier_tendsto (T.adjoint f)

end JanetCartan.FourierIntegral.LowBounds.FrequencyCutoff
