module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.Frequency
public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.Jets
public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.Support
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.PrimitiveBounds.Shells
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.Amplitude

/-!
# Primitive low inputs from the original phase

This closes the geometric assumptions of `LowBounds.exists_graphL2_of_primitive_inputs`
and `FourierIntegral.exists_graphL2_of_local_phase` in actual-calculus Step 1.
The source annulus and all geometric constants precede the phase and amplitudes.
The original amplitude assumptions are local smoothness, finite normalized jets,
and a closed supported set strictly inside the original chart. Both physical
positions are retained on every shell of the whole normal image.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.WholeImageGeometry
open NormalComparison LowBounds
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- Original matrix smoothness survives the order-zero normalization used in
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem normalizedMatrix_contDiffOn_sourceBand {A : E → E → Mat} {X D : Set E}
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (X ×ˢ D)) (ρ a b : ℝ) :
    ContDiffOn ℝ ∞ (Function.uncurry (normalizedNormalMatrix ρ 0 A))
      (X ×ˢ normalizedSourceBand D ρ a b) := by
  simpa only [normalizedNormalMatrix, neg_zero, Real.rpow_zero, one_smul,
    Function.uncurry_def, Function.comp_def] using
    hA.comp (contDiffOn_fst.prodMk (contDiffOn_snd.const_smul ρ))
      (s := X ×ˢ normalizedSourceBand D ρ a b) (fun _ hq ↦ ⟨hq.1, hq.2.1⟩)

/-- Each physical position inherits the normalized original matrix jets with
no derivative loss. These are the two amplitude slots of the primitive shell
input in `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem normalizedMatrix_position_jets_le {A : E → E → Mat} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (X ×ˢ D))
    (ρ a b : ℝ) {N : ℕ} {B : ℝ}
    (hb : ∀ z ∈ X ×ˢ normalizedSourceBand D ρ a b, ∀ k ≤ N,
      ‖iteratedFDeriv ℝ k (Function.uncurry (normalizedNormalMatrix ρ 0 A)) z‖ ≤ B)
    {q : NormalVariables n} (hq : q ∈ X ×ˢ (X ×ˢ normalizedSourceBand D ρ a b))
    {k : ℕ} (hk : k ≤ N) :
    ‖iteratedFDeriv ℝ k (fun z : NormalVariables n ↦
      normalizedNormalMatrix ρ 0 A z.1 z.2.2) q‖ ≤ B ∧
    ‖iteratedFDeriv ℝ k (fun z : NormalVariables n ↦
      normalizedNormalMatrix ρ 0 A z.2.1 z.2.2) q‖ ≤ B := by
  have hf := normalizedMatrix_contDiffOn_sourceBand hA ρ a b
  have hU := hX.prod (isOpen_normalizedSourceBand hD ρ a b)
  have hproj (P : NormalVariables n →L[ℝ] E × E) (hP : ‖P‖ ≤ 1)
      (hp : P q ∈ X ×ˢ normalizedSourceBand D ρ a b) :
      ‖iteratedFDeriv ℝ k (Function.uncurry (normalizedNormalMatrix ρ 0 A) ∘ P) q‖ ≤ B := by
    apply (norm_iteratedFDeriv_comp_linear_on_open_le P hU hf hp k).trans
    exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hP)).trans
      (hb _ hp k hk)
  exact ⟨hproj (normalLeftInput n) (norm_normalLeftInput_le n) ⟨hq.1, hq.2.2⟩,
    hproj (normalRightInput n) (norm_normalRightInput_le n) hq.2⟩

/-- All primitive low normal inputs from finite original phase and amplitude
jets. The frequency and inverse estimates are outputs, on the entire image.
The phase reserve is `wholeImagePhaseReserve n = 2 * (n + 1) + 2`, fixed before
any output Sobolev order. Original amplitude jets through `primitiveNormalReserve n`
are the only amplitude bounds; their two physical-position versions are derived.
This is the geometric input producer for the low graph theorem in
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem exists_wholeImage_primitive_inputs (B₀ Bφ : ℝ)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ F > 0, ∃ C > 0, ∃ a > 0, ∃ b > a, ∃ M > 0, ∃ L > 0,
      ∀ (S : E → E → ℝ) (X D : Set E),
      IsOpen X → IsOpen D → Convex ℝ X →
      ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D) →
      (∀ x ∈ X, ∀ u ∈ D, ∀ t : ℝ, 0 < t → t • u ∈ D →
        S x (t • u) = t * S x u) →
      (∀ x ∈ X, ∀ u ∈ D,
        ‖fderiv ℝ (fun v ↦ fderiv ℝ (fun z ↦ S z v) x) u‖ ≤ B₀) →
      (∀ x ∈ X, ∀ y ∈ X, InjOn (averagedGradient S x y) D) →
      (∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D, δ ≤ |(averagedJacobian S x y u).det|) →
      (∀ u ∈ D, ε < ‖u‖) →
      (∀ j : ℕ, ∀ z ∈ X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b,
        ∀ k ≤ wholeImagePhaseReserve n, ‖iteratedFDeriv ℝ k
          (Function.uncurry (normalizedPhase ((2 : ℝ)^j) S)) z‖ ≤ Bφ) →
      AveragedGradientChart S X D (wholeImageInverse S D) (averagedJacobian S) δ ∧
      (∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D,
        ‖averagedGradient S x y u‖ ≤ F * ‖u‖ ∧
        ‖u‖ ≤ C * ‖averagedGradient S x y u‖) ∧
      ∀ (A B : E → E → Mat) (K : Set (NormalVariables n)) (α β : ℝ),
      IsClosed K → K ⊆ X ×ˢ (X ×ˢ D) →
      ContDiffOn ℝ ∞ (Function.uncurry A) (X ×ˢ D) →
      ContDiffOn ℝ ∞ (Function.uncurry B) (X ×ˢ D) →
      (∀ q ∈ X ×ˢ (X ×ˢ D), A q.1 q.2.2 ≠ 0 → B q.2.1 q.2.2 ≠ 0 → q ∈ K) →
      (∀ x u, x ∉ X → A x u = 0) → (∀ y u, y ∉ X → B y u = 0) →
      (∀ j : ℕ, ∀ z ∈ X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b,
        ∀ k ≤ primitiveNormalReserve n, ‖iteratedFDeriv ℝ k
          (Function.uncurry (normalizedNormalMatrix ((2 : ℝ)^j) 0 A)) z‖ ≤ α) →
      (∀ j : ℕ, ∀ z ∈ X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b,
        ∀ k ≤ primitiveNormalReserve n, ‖iteratedFDeriv ℝ k
          (Function.uncurry (normalizedNormalMatrix ((2 : ℝ)^j) 0 B)) z‖ ≤ β) →
      PrimitiveNormalGeometry X D S A B (wholeImageInverse S D) (averagedJacobian S)
        (X ×ˢ (X ×ˢ D)) K ∧
      ∀ j, PrimitiveNormalShellInputs A B (wholeImageInverse S D) (averagedJacobian S)
        ((2 : ℝ)^j) (primitiveNormalReserve n) M L δ α β
        (normalDyadicShell (bufferedNormalDomain X D S) j)
        (X ×ˢ (X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b)) := by
  obtain ⟨F, hF, C, hC, a, ha, b, hab, hfrequency⟩ :=
    exists_wholeImage_frequency_comparison_and_shell_range (n := n) B₀ hδ hε
  obtain ⟨M, hM, L, hL, hjets⟩ :=
    exists_normalizedWholeImage_jet_bounds (n := n) (primitiveNormalReserve n) Bφ b hδ
  refine ⟨F, hF, C, hC, a, ha, b, hab, M, hM, L, hL, ?_⟩
  intro S X D hX hD hcX hS hhom hmix hinj hgap hcollar hphase
  obtain ⟨hcompare, hmap⟩ := hfrequency S X D hX hD hcX hS hhom hmix hgap hcollar
  have hj := hjets S X D hX hD hcX hS hinj hgap a ha hab hphase hmap
  refine ⟨averagedGradientChart hX hD hcX hS hinj hδ hgap, hcompare, ?_⟩
  intro A B K α β hK hKsub hA hB hsupp hleft hright hjA hjB
  refine ⟨primitiveNormalGeometry_of_frequency_bound hX hD hcX hS hinj hδ hgap hC.le
    (fun x hx y hy u hu ↦ (hcompare x hx y hy u hu).2)
    hK hKsub hA hB hsupp hleft hright, ?_⟩
  intro j
  have hl := normalizedMatrix_contDiffOn_sourceBand hA ((2 : ℝ)^j) a b
  have hr := normalizedMatrix_contDiffOn_sourceBand hB ((2 : ℝ)^j) a b
  exact
    { open_domain := isOpen_normalDyadicShell
        (isOpen_bufferedNormalDomain hX hD hcX hS hinj hδ hgap) j
      open_range := hX.prod (hX.prod (isOpen_normalizedSourceBand hD _ a b))
      inverse_smooth := normalizedWholeImageInverse_contDiffOn_shell hX hD hcX hS hinj hδ hgap j
      mapsTo := hmap j
      input_smooth := (normalizedAveragedJacobian_contDiffOn_band hX hD hcX hS _ a b).prodMk
        ((hl.comp (normalLeftInput n).contDiff.contDiffOn (fun _ hq ↦ ⟨hq.1, hq.2.2⟩)).prodMk
          (hr.comp (normalRightInput n).contDiff.contDiffOn (fun _ hq ↦ hq.2)))
      gap := fun z hz ↦ hgap _ hz.1 _ hz.2.1 _ hz.2.2.1
      jacobianJets := (hj j).1
      leftJets := fun z hz k hk ↦
        (normalizedMatrix_position_jets_le hX hD hA _ a b (hjA j) hz hk).1
      rightJets := fun z hz k hk ↦
        (normalizedMatrix_position_jets_le hX hD hB _ a b (hjB j) hz hk).2
      inverseJets := (hj j).2 }

end JanetCartan.FourierIntegral.WholeImageGeometry
