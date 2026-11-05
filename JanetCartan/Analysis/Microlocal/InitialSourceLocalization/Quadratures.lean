module

public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.Sobolev
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.LocalizerReality
public import JanetCartan.Analysis.Microlocal.RegularSector.Realization.Compression
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.QuadratureNorm

/-!
# Both real quadratures of the same even initial proof mask

Frequency reflection for the literal right quantization proves that its
bounded real compression commutes with taking any rotated real part. Hence
both original quadratures inherit the same initial-source estimate and its
same constants. No independently chosen reflected mask is identified.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped ContDiff

namespace JanetCartan.InitialSourceLocalization

open FiniteChain.Graph JanetCartan.Localization Pseudodifferential
open RegularSector RegularSector.Realization ArbitraryAccuracy.ResidualLocalization
open ResponseTransfer.SourceNegative
open scoped RegularSector.Realization

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "RV" => EuclideanSpace ℝ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)
local notation "RH" => Lp RV 2 (volume : Measure E)

private theorem initial_realPart_imaginary_inclusion (v : RH) :
    l2RealPart volume (Complex.I • l2ComplexInclusion volume v) = 0 := by
  apply Lp.ext
  filter_upwards [euclideanRealPart.coeFn_compLpL (Complex.I • l2ComplexInclusion volume v),
    Lp.coeFn_smul Complex.I (l2ComplexInclusion volume v),
    euclideanComplexInclusion.coeFn_compLpL v, Lp.coeFn_zero RV 2 volume] with y hr hi hv hz
  change (l2RealPart volume (Complex.I • l2ComplexInclusion volume v)) y = _ at hr
  change (l2ComplexInclusion volume v) y = euclideanComplexInclusion (v y) at hv
  rw [hr, hi, Pi.smul_apply, hv, hz]
  ext i
  simp [euclideanRealPart_apply, euclideanComplexInclusion_apply]

/-- Both real quadratures have exactly the same initial defect under the
original even mask. Reality follows from reflection of the literal right
quantization, and the identity is subtracted once
(`app:ch_regular:eq:source-tail`, `app:ch_osc:cor:osc-real`). -/
theorem initialSource_real_quadrature_defect
    (ρ : ℝ) (m : LocalizerSymbol n) (heven : ∀ y ξ, m (y, -ξ) = m (y, ξ))
    (M : H →L[ℂ] H)
    (hM : ∀ v : H, M v =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (rightLocalizer ρ m (fun y ↦ (v y).ofLp) x))
    (u : H) (c : ℂ) :
    l2RealPart volume (c • u) - realCompression M (l2RealPart volume (c • u)) =
      l2RealPart volume (c • (u - M u)) := by
  have hconj : conjugateOperator M.toLinearMap = M.toLinearMap := by
    ext1 v
    change star (M (star v)) = M v
    rw [boundedRightLocalizer_star_of_even ρ m heven M hM, star_star]
  have hr (v : H) : l2RealPart volume (M v) = realCompression M (l2RealPart volume v) := by
    rw [realCompression_complex_extension M hconj v, map_add,
      realPart_inclusion, initial_realPart_imaginary_inclusion, add_zero]
  rw [smul_sub, map_sub, ← M.map_smul, hr]

/-- The SAME initial-source bound controls every unit rotated real quadrature
of the original even right localizer. In particular real and imaginary
sources use one mask and one constant (`app:ch_regular:eq:source-tail`). -/
theorem bounded_initialSource_real_quadrature_sobolev_bound
    (m : LocalizerSymbol n) (hm : ContDiff ℝ ∞ m) (hmc : HasCompactSupport m)
    (heven : ∀ y ξ, m (y, -ξ) = m (y, ξ))
    (φ : E → ℝ) (a : E → V)
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hφ : ContDiffOn ℝ ∞ φ U) (ha : ContDiffOn ℝ ∞ a U) (hs : tsupport a ⊆ K)
    {S : Set (E × E)} {δ G A L ρ : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A)
    (hL : 1 ≤ L) (hρ : 1 ≤ ρ) (b : ℕ)
    (hgraph : ∀ y ∈ tsupport a, (y, gradient φ y) ∈ S)
    (hplateau : cthickening δ S ⊆ interior {p | m p = 1})
    (hupper : ∀ y ∈ U, ‖fderiv ℝ φ y‖ ≤ G)
    (P D C : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j) (hD : ∀ j, 0 ≤ D j)
    (hC : ∀ j, 0 ≤ C j)
    (hmjet : ∀ j p, ‖iteratedFDeriv ℝ j m p‖ ≤ D j)
    (hp : ∀ y ∈ tsupport a, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) φ y‖ ≤ P j * L ^ j)
    (hajet : ∀ y ∈ tsupport a, ∀ j,
      ‖iteratedFDeriv ℝ j a y‖ ≤ C j * ((A * L ^ b) * L ^ j))
    (M : H →L[ℂ] H)
    (hM : ∀ v : H, M v =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (rightLocalizer ρ m (fun y ↦ (v y).ofLp) x))
    (u : H) (hu : u =ᵐ[volume] fun y ↦ phaseOscillation (fun z ↦ ρ * φ z) y • a y)
    {s : ℝ} (hszero : 0 ≤ s) (q : ℕ) (hq : s + (n : ℝ) / 2 < q)
    (c : ℂ) (hc : ‖c‖ = 1) :
    let v := l2RealPart volume (c • u) - realCompression M (l2RealPart volume (c • u))
    ArbitraryAccuracy.MemComponentFourierSobolev (EuclideanSpace.basisFun (Fin r) ℝ) s v ∧
      ArbitraryAccuracy.componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin r) ℝ) s v ≤
        ((r : ℝ) * sourceLocalizationKernelConstant K δ G P D C q *
          Real.sqrt (∫ ξ : E, (1 + ‖ξ‖) ^ (-(2 * (q : ℝ) - 2 * s)))) *
            (A * L ^ b) * (ρ ^ (s + (n : ℝ) / 2) * (L / ρ) ^ q) := by
  dsimp only
  rw [initialSource_real_quadrature_defect ρ m heven M hM u c]
  obtain ⟨hmemb, hbound⟩ := bounded_initialSource_defect_sobolev_bound m hm hmc φ a
    hU hK hKU hφ ha hs hδ hA hL hρ b hgraph hplateau hupper P D C
    hP hD hC hmjet hp hajet M hM u hu hszero q hq
  obtain ⟨hreal, hnorm⟩ := real_quadrature_fourierSobolev_bound hmemb c hc
  exact ⟨hreal, hnorm.trans hbound⟩

end JanetCartan.InitialSourceLocalization

