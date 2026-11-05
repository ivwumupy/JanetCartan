module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.PrimitiveInputs
public import JanetCartan.Analysis.Microlocal.FourierIntegral.PhaseExtension

/-!
# Low graph realization from finite original phase jets

Apply `exists_graphL2_of_local_phase` with the actual inverse on the entire
normal image. All inverse, Jacobian, transported support and shell geometry
inputs are discharged. The original phase and amplitude hypotheses remain
explicit; instantiating the Hamilton family belongs to the finite-calculus
construction. The globally smooth auxiliary phase is supplied by PhaseExtension.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.WholeImageGeometry
open NormalComparison LowBounds FrequencyCutoff
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The low pure graph theorem with every whole-image geometric premise
proved from the original phase. Only the original local smoothness, degree-one
law, mixed second-jet bound, injectivity, determinant gap, positive source
collar and finite normalized phase jets are required. The phase reserve is
fixed before every Sobolev order. Original amplitude assumptions are local
smoothness, global continuity, buffered support, compact physical support,
polynomial growth and normalized jets through `primitiveNormalReserve n`.

The actual closed carrier is constructed from the original topological
support. No inverse, shell-range or transported-support bound is assumed.
The smooth auxiliary phase and all exact original-kernel realizations come
from PhaseExtension. Source: `app:ch_regular_base:thm:actual-calculus`, Step 1,
and `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem exists_graphL2_of_wholeImage_phase (hn : 0 < n) (R B₀ Bφ : ℝ)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ a > 0, ∃ b > a, ∃ C > 0,
      ∀ (X D : Set E) (O : Set (E × E)) (S : E → E → ℝ) (A : E → E → Mat)
        (α : ℝ), 0 ≤ α → IsOpen X → IsOpen D → Convex ℝ X → IsOpen O →
      closure (X ×ˢ D) ⊆ O → ContDiffOn ℝ ∞ (Function.uncurry S) O →
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
      (∀ x ∈ X, ‖x‖ ≤ R) →
      ContDiffOn ℝ ∞ (Function.uncurry A) (X ×ˢ D) →
      (∀ j : ℕ, ∀ z ∈ X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b,
        ∀ k ≤ primitiveNormalReserve n, ‖iteratedFDeriv ℝ k
          (Function.uncurry (normalizedNormalMatrix ((2 : ℝ)^j) 0 A)) z‖ ≤ α) →
      ∀ (hA : Continuous (Function.uncurry A)) (Kout : Set E) (hKout : IsCompact Kout)
        (hsA : ∀ x u, x ∉ Kout → A x u = 0),
      tsupport (Function.uncurry A) ⊆ X ×ˢ D →
      ∀ (P : ℝ) (k : ℕ), (∀ x u, ‖A x u‖ ≤ P * (1 + ‖u‖ ^ k)) →
      ∃ (S' : E → E → ℝ) (hS' : ContDiff ℝ ∞ (Function.uncurry S')),
        (∀ q ∈ closure (X ×ˢ D),
          Function.uncurry S' =ᶠ[𝓝 q] Function.uncurry S) ∧
        let Tj : ℕ → H →L[ℂ] H := fun j ↦ compactVectorGraph hS'.continuous
          (cutAmplitude_entry_continuous hA j)
          (cutAmplitude_entry_hasCompactSupport hKout hsA j)
        ∃ T : H →L[ℂ] H, ‖T‖ ≤ C * α ∧ ‖T.adjoint‖ ≤ C * α ∧
          (∀ u : graphTestSpace n r, T (graphTestToLp u) =ᵐ[volume]
            fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ u ↦ A z u)
              (graphTestToSchwartz u) x)) ∧
          (∀ u : SchwartzMap E (Fin r → ℂ), T (schwartzVectorToLp u) =ᵐ[volume]
            fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ u ↦ A z u) u x)) ∧
          (∀ f : H, Tendsto (fun j ↦ Tj j f) atTop (𝓝 (T f))) ∧
          (∀ f : H, Tendsto (fun j ↦ (Tj j).adjoint f) atTop (𝓝 (T.adjoint f))) ∧
          (∀ j, Tj j = T.comp (multiplier j)) ∧
          (∀ j, (Tj j).adjoint = (multiplier j).comp T.adjoint) ∧
          (∀ j (v : E → Fin r → ℂ),
            graphOperator S' (fun x _ u ↦ cutAmplitude A j x u) v =
              graphOperator S (fun x _ u ↦ cutAmplitude A j x u) v) ∧
          ∀ U : H →L[ℂ] H, (∀ u : graphTestSpace n r, U (graphTestToLp u) =ᵐ[volume]
            fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ u ↦ A z u)
              (graphTestToSchwartz u) x)) → U = T := by
  obtain ⟨F, hF, C₀, _hC₀, a, ha, b, hab, M, _hM, L, _hL, hinputs⟩ :=
    exists_wholeImage_primitive_inputs (n := n) (r := r) B₀ Bφ hδ hε
  obtain ⟨C, hC, hlow⟩ := FourierIntegral.exists_graphL2_of_local_phase
    (r := r) hn R M L hδ hF.le
  refine ⟨a, ha, b, hab, C, hC, ?_⟩
  intro X D O S A α hα hX hD hcX hO hbuffer hS hhom hmix hinj hgap hcollar
    hphase hR hAsmooth hjA hA Kout hKout hsA hsupp P k hpoly
  have hSlocal := hS.mono (subset_trans subset_closure hbuffer)
  obtain ⟨chart, hcompare, hgeometry⟩ :=
    hinputs S X D hX hD hcX hSlocal hhom hmix hinj hgap hcollar hphase
  have hK : IsClosed (jointNormalCarrier A A) :=
    ((isClosed_tsupport (Function.uncurry A)).preimage
      (continuous_fst.prodMk continuous_snd.snd)).inter
      ((isClosed_tsupport (Function.uncurry A)).preimage
        (continuous_snd.fst.prodMk continuous_snd.snd))
  have hKsub : jointNormalCarrier A A ⊆ X ×ˢ (X ×ˢ D) :=
    fun _ hq ↦ ⟨(hsupp hq.1).1, (hsupp hq.2).1, (hsupp hq.1).2⟩
  have hcarrier : ∀ q ∈ X ×ˢ (X ×ˢ D),
      A q.1 q.2.2 ≠ 0 → A q.2.1 q.2.2 ≠ 0 → q ∈ jointNormalCarrier A A :=
    fun _ _ hl hr ↦ ⟨subset_tsupport (Function.uncurry A) hl,
      subset_tsupport (Function.uncurry A) hr⟩
  have hleft : ∀ x u, x ∉ X → A x u = 0 := by
    intro x u hx
    by_contra hne
    exact hx (hsupp (subset_tsupport (Function.uncurry A)
      (show (x, u) ∈ Function.support (Function.uncurry A) from hne))).1
  obtain ⟨geometry, shells⟩ := hgeometry A A (jointNormalCarrier A A) α α hK hKsub
    hAsmooth hAsmooth hcarrier hleft hleft hjA hjA
  have hforward : ContinuousOn (normalForwardCoordinates S) (jointNormalCarrier A A) :=
    (continuousOn_fst.prodMk (continuousOn_snd.fst.prodMk
      (averagedGradient_contDiffOn hX hD hcX hSlocal).continuousOn)).mono hKsub
  exact hlow X D O S A (wholeImageInverse S D) (averagedJacobian S)
    (X ×ˢ (X ×ˢ D)) (jointNormalCarrier A A)
    (fun j ↦ X ×ˢ (X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b)) α hα
    hX hcX hO hbuffer hS chart geometry hKsub hR
    (fun x hx y hy u hu ↦ (hcompare x hx y hy u hu).1.trans
      (mul_le_mul_of_nonneg_left (by linarith) hF.le)) shells
    hA Kout hKout hsA hsupp hforward P k hpoly

end JanetCartan.FourierIntegral.WholeImageGeometry
