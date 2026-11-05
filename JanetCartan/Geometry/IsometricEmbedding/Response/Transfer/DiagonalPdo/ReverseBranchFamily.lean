module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.NormalGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.ReverseAssembly.UniformBranches

/-!
# Diagonal full-amplitude branches with the actual identity normal chart

Apply the existing carrier branch constructor on the original physical and
frequency supports. The phase, inverse, determinant, shell geometry and low
normal constants are all instantiated explicitly. Primitive primary and
symbol profiles retain the original reserve and derivative count.
Sources: `app:ch_response:eq:direct-envelope-profile`, `new:eq:carrier-ibp`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DiagonalPdo
open FourierIntegral FourierIntegral.LowBounds NormalComparison WeightedPrincipalLocalization


open DirectEvolution DirectEvolution.AnnularSobolev DirectEvolution.CompactTransfer
open DirectEvolution.BranchAmplitudes DirectEvolution.ModifiedLow
open FourierIntegral.FullLowBounds RegularSector.Characteristic.EvolutionIntegral
variable {d r : ℕ} {ι : Type} [Fintype ι]
local notation "E" => Euclidean (d+1)
local notation "Param" => Euclidean 3 × Euclidean d
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- The literal-adjoint diagonal branch family has the same fixed unit
normal jets and constant-two shell comparison, with the original exchanged
physical supports and full-frequency amplitude (`new:eq:carrier-ibp`). -/
theorem exists_diagonalReverseBranchFamily_of_primitive_jets
    (R ℓ : ℝ) (hℓ : 0 < ℓ) (hRcell : R / ℓ < 1 / 2)
    (basis : OrthonormalBasis ι ℝ (CarrierVariables (d + 1)))
    (s : ℕ) (suffix : List (E × Param))
    (Aphase Aamp : ℕ → ℝ) (hphase : ∀ j, 0 ≤ Aphase j) (hamp : ∀ j, 0 ≤ Aamp j)
    {B radius : ℝ} (hB : 0 ≤ B) (hradius : 0 ≤ radius) :
    ∃ C ≥ 0, ∀ (X₀ Y₀ F₀ : Set E), IsCompact X₀ → IsCompact Y₀ →
      (∀ y ∈ Y₀, ∀ i : Fin (d + 1), |y i| ≤ R) → IsClosed F₀ → (0 : E) ∉ F₀ →
    X₀ ⊆ ball 0 R →
    ∀ (Rstar : ℕ), fullLowReserve (d + 1) + 2 < Rstar →
    ∀ (L lam : ℝ), 1 ≤ L → 1 ≤ lam → ∀ (p : ℤ)
    (φ : E → Param → ℝ) (w₀ : E × Param → CarrierVariables (d + 1))
    (α : (E × Param) → CarrierVariables (d + 1) → Mat)
    (U : Set (E × Param)) (Dcrit : Set (CarrierVariables (d + 1))),
    IsOpen U → IsOpen Dcrit → Convex ℝ Dcrit →
    ContDiffOn ℝ ∞ (Function.uncurry (carrierPhase (fun x ξ : E ↦ inner ℝ x ξ) φ)) (U ×ˢ Dcrit) →
    ContDiffOn ℝ ∞ w₀ U → MapsTo w₀ U Dcrit →
    (∀ q ∈ U, gradient (carrierPhase (fun x ξ : E ↦ inner ℝ x ξ) φ q) (w₀ q) = 0) →
    (∀ q ∈ U, ∀ w ∈ Dcrit, IsUnit (averagedPhaseHessian (carrierPhase (fun x ξ : E ↦ inner ℝ x ξ) φ) w₀ q w)) →
    (∀ q ∈ U, ∀ w ∈ Dcrit,
      ‖Ring.inverse (averagedPhaseHessian (carrierPhase (fun x ξ : E ↦ inner ℝ x ξ) φ) w₀ q w)‖ ≤ B) →
    (∀ j ≤ fullLowReserve (d + 1) + (s + suffix.length) + 2,
      ∀ q ∈ U ×ˢ Dcrit,
        ‖iteratedFDeriv ℝ j (Function.uncurry (carrierPhase (fun x ξ : E ↦ inner ℝ x ξ) φ)) q‖ ≤
          Aphase j * L ^ (j - Rstar)) →
    ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ Dcrit) →
    (∀ j ≤ fullLowReserve (d + 1) + (s + suffix.length),
      ∀ q ∈ U ×ˢ Dcrit,
        ‖iteratedFDeriv ℝ j (Function.uncurry α) q‖ ≤ Aamp j * L ^ (j + 2 - Rstar)) →
    ∀ param : Param,
    (∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry α) →
      normalizedSlice param q ∈ U ×ˢ Dcrit) →
    (∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry α) → ‖q.2‖ ≤ radius) →
    (∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry α) →
      q.1.2 ∈ X₀ ∧ q.1.1 ∈ Y₀ ∧ lam • q.2 ∈ F₀) →
    (∀ is : List (Fin (d + 1)), is.length ≤ s →
      ∀ branch ∈ jointTransferTerms basis
        ((is.map fun i => (EuclideanSpace.single i (1 : ℝ), (0 : Param))) ++ suffix),
      ∀ hφ : Continuous (fun x => φ x param),
        ‖reverseAnnularBranchOperator basis (fun _ _ x ξ ↦ inner ℝ x ξ) 0 lam p φ w₀ α branch param hφ‖ ≤
          C * lam ^ p * L ^ (is.length + suffix.length - branch.datumWord.length)) ∧
    (∀ es : List (E × Param), es.length ≤ s + suffix.length →
      ∀ branch ∈ jointTransferTerms basis es,
      ∀ u : graphTestSpace (d + 1) r,
        (fullGraphOperator ((fun x ξ : E ↦ inner ℝ x ξ)) (fun x z ξ =>
          (modifiedAmplitude lam p (normalizedTermAmplitude basis
            (carrierPhase (fun x ξ : E ↦ inner ℝ x ξ) φ) w₀ α branch param) z x ξ).conjTranspose)).adjoint
          (graphTestToLp u) =ᵐ[volume] fun x => WithLp.toLp 2
        (reverseGraphOperator ((fun x ξ : E ↦ inner ℝ x ξ)) (fun y z ξ =>
          modifiedAmplitude lam p (normalizedTermAmplitude basis
            (carrierPhase (fun x ξ : E ↦ inner ℝ x ξ) φ) w₀ α branch param) z y ξ)
          (fun y => (u.val y).ofLp) x)) := by
  obtain ⟨C, hC, hbuild⟩ := exists_reverseAnnularBranchFamily_of_primitive_jets
    (d := d) (r := r) (P := Param) R ℓ 1 1 2 hℓ hRcell
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (1 : ℝ) ≤ 2) basis s suffix Aphase Aamp hphase hamp hB hradius
  refine ⟨C, hC, ?_⟩
  intro X₀ Y₀ F₀ hXcompact hYcompact hYbox hFclosed hFzero hX₀
  let Ψ : TwoTimePhase d := fun _ _ x ξ ↦ inner ℝ x ξ
  let X : Set E := ball 0 R
  let Ω : Set (NormalVariables (d+1)) := X ×ˢ X ×ˢ univ
  let K : Set (NormalVariables (d+1)) := X₀ ×ˢ X₀ ×ˢ F₀
  let V := normalDyadicShell Ω
  have hp : elapsedPhase Ψ 0 = (fun x ξ : E ↦ inner ℝ x ξ) := by
    funext x ξ
    exact elapsedPhase_zero Ψ (fun _ _ _ ↦ rfl) x ξ
  have hdomain : bufferedNormalDomain X univ (elapsedPhase Ψ 0) = Ω := by
    rw [hp, diagonal_bufferedNormalDomain]
  have hopen : IsOpen Ω := isOpen_ball.prod (isOpen_ball.prod isOpen_univ)
  have hforward : normalForwardCoordinates (elapsedPhase Ψ 0) = id := by
    rw [hp, diagonal_normalForwardCoordinates]
  have hη : normalInverseCoordinates (fun _ _ ξ : E ↦ ξ) = id := rfl
  have hJ : ∀ l, (fun q : NormalVariables (d+1) ↦
      normalizedNormalJacobian ((2 : ℝ)^l)
        (fun _ _ _ : E ↦ ContinuousLinearMap.id ℝ E) q.1 q.2.1 q.2.2) =
      (fun _ ↦ ContinuousLinearMap.id ℝ E) := fun _ ↦ rfl
  have hmap : ∀ l, MapsTo (normalInverseCoordinates
      (normalizedNormalInverse ((2 : ℝ)^l) (fun _ _ ξ : E ↦ ξ)))
        (normalDyadicShell (bufferedNormalDomain X univ (elapsedPhase Ψ 0)) l) (V l) := by
    intro l
    rw [diagonal_normalizedInverse (by positivity : (2 : ℝ)^l ≠ 0), hdomain]
    exact mapsTo_id _
  have hh := hbuild X₀ Y₀ F₀ hXcompact hYcompact hYbox hFclosed hFzero Ψ 0
    (by rw [hp]; exact contDiff_fst.inner ℝ contDiff_snd)
    (X := X) (D := univ) (η := fun _ _ ξ ↦ ξ)
    (J := fun _ _ _ ↦ ContinuousLinearMap.id ℝ E) (W := univ) (K := K)
    (by rw [hp]; exact principal_linearPhase_chart X)
    (hdomain.symm ▸ hopen)
    (by rw [hη]; exact contDiffOn_id)
    (fun _ _ ↦ mem_univ _) contDiffOn_const
    (by intro q _; simp [ContinuousLinearMap.det])
    (by intro q _; rw [hforward, hη]; rfl)
    (fun _ _ hx hy hξ ↦ ⟨hx, hy, hξ⟩)
    (by rw [hforward, image_id]; exact hXcompact.isClosed.prod (hXcompact.isClosed.prod hFclosed))
    (by rw [hforward, image_id, hdomain]; exact prod_mono hX₀ (prod_mono hX₀ (subset_univ _)))
    (fun _ hx ↦ (mem_ball_zero_iff.mp hx).le)
    (by intro x _ y _ u _; rw [hp, averagedGradient_principal_linearPhase]; simp)
    V (fun l ↦ hdomain.symm ▸ WholeImageGeometry.isOpen_normalDyadicShell hopen l)
    (fun l ↦ WholeImageGeometry.isOpen_normalDyadicShell hopen l)
    (by intro l; rw [diagonal_normalizedInverse (by positivity : (2 : ℝ)^l ≠ 0)]; exact contDiffOn_id)
    hmap
    (by intro l; rw [hJ]; exact contDiffOn_const)
    (by intro l z _; simp [normalizedNormalJacobian, ContinuousLinearMap.det])
    (fun l z _ i _ ↦ (diagonal_normalShell_jets l z).1 i)
    (fun l z _ i hi _ ↦ (diagonal_normalShell_jets l z).2 i hi)
    (fun l z hz ↦ diagonal_normalShell_scale X l z hz)
    hX₀ (subset_univ _)
  simpa only [hp, diagonal_adjointCarrierPhase_eq] using hh

end JanetCartan.ResponseTransfer.DiagonalPdo
