module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Admission.Linearity.Calculus

/-!
# Full complex strain of a corrected atom

The algebra in `app:ch_response:cor:current-atoms` uses one real response and
its existing complexification. The cutoff is applied after taking the complete
primary strain. These definitions have no accuracy parameter; all observation
orders refer to this same field. Bounds for the actual response are separate
obligations of `Response.Transfer` and `FixedDomainInverse`.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology Matrix.Norms.Frobenius

namespace JanetCartan.CorrectedAtoms
open ResponseSourceExtension PrimarySourceAdmission.InitialScalarCalculus

variable {n N : ℕ}

/-- The complete complex cutoff strain from
`app:ch_response:cor:current-atoms`, retaining both real quadratures. -/
def complexAtomicSource (F : Euclidean n → Euclidean N) (χ : Euclidean n → ℝ)
    (W : Euclidean n → EuclideanSpace ℂ (Fin N)) :
    Euclidean n → Matrix (Fin n) (Fin n) ℂ :=
  fun x ↦ χ x • WKB.complexLinearizedMetric F W x

/-- The literal corrected atom of `app:ch_response:cor:current-atoms` for one
fixed real response. Neither the response nor its extension is reselected. -/
def complexCorrectedAtom (F : Euclidean n → Euclidean N) (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (W : Euclidean n → EuclideanSpace ℂ (Fin N)) :
    Euclidean n → EuclideanSpace ℂ (Fin N) :=
  W - complexifyResponse B (complexAtomicSource F χ W)

/-- The full residual of the same complexified response, with the sign in
`app:ch_response:eq:response-full-identity`. It includes every strain term. -/
def complexAtomicResidual (F : Euclidean n → Euclidean N)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (H : Euclidean n → Matrix (Fin n) (Fin n) ℂ) :
    Euclidean n → Matrix (Fin n) (Fin n) ℂ :=
  WKB.complexLinearizedMetric F (complexifyResponse B H) - H

/-- Subtracting two differentiable complex variations subtracts their complete
strain (`app:ch_response:cor:current-atoms`). -/
theorem complexLinearizedMetric_sub (F : Euclidean n → Euclidean N)
    {W Y : Euclidean n → EuclideanSpace ℂ (Fin N)} {x : Euclidean n}
    (hW : DifferentiableAt ℝ W x) (hY : DifferentiableAt ℝ Y x) :
    WKB.complexLinearizedMetric F (W - Y) x =
      WKB.complexLinearizedMetric F W x - WKB.complexLinearizedMetric F Y x := by
  simpa only [neg_one_smul, sub_eq_add_neg] using
    (complexLinearizedMetric_add F hW (hY.const_smul (-1 : ℝ))).trans
      (congrArg (WKB.complexLinearizedMetric F W x + ·)
        (complexLinearizedMetric_real_smul F hY (-1)))

/-- Exact cancellation of the full complex primary strain on the ORIGINAL
source plateau (`app:ch_response:cor:current-atoms`). -/
theorem complexCorrectedAtom_strain (F : Euclidean n → Euclidean N)
    (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (W : Euclidean n → EuclideanSpace ℂ (Fin N)) {x : Euclidean n}
    (hχ : χ x = 1) (hW : DifferentiableAt ℝ W x)
    (hB : DifferentiableAt ℝ (complexifyResponse B (complexAtomicSource F χ W)) x) :
    WKB.complexLinearizedMetric F (complexCorrectedAtom F χ B W) x =
      -complexAtomicResidual F B (complexAtomicSource F χ W) x := by
  rw [complexCorrectedAtom, complexLinearizedMetric_sub F hW hB]
  simp only [complexAtomicResidual, Pi.sub_apply, complexAtomicSource, hχ, one_smul,
    neg_sub]

/-- Every strain jet of the same atom is the negative residual jet wherever
the cutoff is locally one. This lets arbitrary-accuracy estimates vary their
order without changing the atom (`app:ch_response:cor:current-atoms`). -/
theorem complexCorrectedAtom_iteratedStrain (F : Euclidean n → Euclidean N)
    (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (W : Euclidean n → EuclideanSpace ℂ (Fin N)) {O : Set (Euclidean n)}
    (hO : IsOpen O) (hχ : ∀ x ∈ O, χ x = 1)
    (hW : ∀ x ∈ O, DifferentiableAt ℝ W x)
    (hB : ∀ x ∈ O,
      DifferentiableAt ℝ (complexifyResponse B (complexAtomicSource F χ W)) x)
    (k : ℕ) {x : Euclidean n} (hx : x ∈ O) :
    iteratedFDeriv ℝ k (WKB.complexLinearizedMetric F (complexCorrectedAtom F χ B W)) x =
      iteratedFDeriv ℝ k (-complexAtomicResidual F B (complexAtomicSource F χ W)) x := by
  have he : WKB.complexLinearizedMetric F (complexCorrectedAtom F χ B W) =ᶠ[𝓝 x]
      -complexAtomicResidual F B (complexAtomicSource F χ W) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact complexCorrectedAtom_strain F χ B W (hχ y hy) (hW y hy) (hB y hy)
  exact (he.iteratedFDeriv ℝ k).self_of_nhds

/-- All finite strain seminorms are EXACTLY the residual seminorms on a fixed
inner plateau. Thus every precision bound for the fixed response transfers to
the same atom (`app:ch_response:cor:current-atoms`); no accuracy-dependent
choice of response or field occurs. -/
theorem cNorm_complexCorrectedAtom_strain_eq (F : Euclidean n → Euclidean N)
    (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (W : Euclidean n → EuclideanSpace ℂ (Fin N)) {O s : Set (Euclidean n)}
    (hO : IsOpen O) (hs : s ⊆ O) (hχ : ∀ x ∈ O, χ x = 1)
    (hW : ∀ x ∈ O, DifferentiableAt ℝ W x)
    (hB : ∀ x ∈ O,
      DifferentiableAt ℝ (complexifyResponse B (complexAtomicSource F χ W)) x)
    (q : ℕ) :
    cNorm s q (WKB.complexLinearizedMetric F (complexCorrectedAtom F χ B W)) =
      cNorm s q (complexAtomicResidual F B (complexAtomicSource F χ W)) := by
  calc
    _ = cNorm s q (-complexAtomicResidual F B (complexAtomicSource F χ W)) := by
      unfold cNorm
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      apply Set.image_congr
      intro x hx
      exact congrArg norm (complexCorrectedAtom_iteratedStrain F χ B W
        hO hχ hW hB j (hs hx))
    _ = _ := cNorm_neg _ _ _

end JanetCartan.CorrectedAtoms
