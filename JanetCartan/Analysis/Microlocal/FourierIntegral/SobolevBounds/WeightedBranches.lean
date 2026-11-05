module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeightedBranches.Bounds

/-!
# Weighted branch jets on the actual carrier

The fixed low L² reserve in `app:ch_regular_base:eq:fio-input` uses weighted
covector derivatives, not just bounded unweighted derivatives. The finite
primitive expansion conserves their exact total number. These theorems retain
both physical positions and the entire masked amplitude, and require regularity
only away from zero with invertibility on the compact physical carrier.

Individual weighted primitive majorants and their interpolation remain explicit
inputs. The parent strong Sobolev construction must produce them from the
normalized amplitude and phase seminorms, including the inverse gap, and apply
the supplied low L² reserve. No branch operator bound is assumed here.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget.Local.Weighted
open Local FirstOutputJets
variable {n r : ℕ} {S : Euclidean n → Euclidean n → ℝ} {A : FullAmplitude n r}

/-- Uniform graph bounds at every point from regularity away from zero and
an inverse gap only on the physical carrier. Nonvanishing branch jets are
proved to lie in the regular neighborhood. For the reverse graph `A` is already
conjugate-transposed, as in `WeakTransfer`.
Source: Step 3, `app:ch_regular_base:eq:fio-input`. -/
theorem graph_branch_jet_norm_le_of_carrier
    {K₀ : Set (Euclidean n × Euclidean n)} {F₀ : Set (Euclidean n)}
    (hK₀ : IsCompact K₀) (hF₀ : IsClosed F₀) (hF₀0 : (0 : Euclidean n) ∉ F₀)
    (hphase : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hinv : ∀ p ∈ K₀, ∀ η, η ≠ 0 → IsUnit (mixedPhaseMatrix S p.1 η).det)
    (hsmooth : ∀ p : Point n, p.2 ≠ 0 → ContDiffAt ℝ ∞ (uncurry A) p)
    (hsupport : ∀ p : Point n, p ∉ K₀ ×ˢ F₀ → uncurry A p = 0)
    (ρ : Euclidean n → ℝ) (hρ : ∀ η, 0 ≤ ρ η)
    (q : Option (ScalarIndex n) → ℕ → ℝ) (hq : ∀ a j, 0 ≤ q a j)
    (hmono : ∀ a, Monotone (q a)) (μ s : ℕ)
    (L K H : ℝ) (hL : 1 ≤ L) (hK : 1 ≤ K) (hH : 1 ≤ H)
    (hlow : ∀ a, q a μ ≤ L) (hhigh : ∀ a, q a (μ + s) ≤ H)
    (hinterp : ∀ a j, μ < j → j < μ + s →
      q a j ≤ K * q a μ ^ (1 - ((j - μ : ℕ) : ℝ) / s) *
        q a (μ + s) ^ (((j - μ : ℕ) : ℝ) / s))
    (hA : ∀ p ∈ K₀ ×ˢ F₀, ∀ w, (ρ p.2) ^ frequencyOrder w * ‖uncurry (jet w A) p‖ ≤ q none w.length)
    (hS : ∀ p ∈ K₀ ×ˢ F₀, ∀ a w,
      (ρ p.2) ^ frequencyOrder w * ‖uncurry (jet w (scalarPrimitive S a)) p‖ ≤ q (some a) w.length)
    (is : List (Fin n)) (his : is.length ≤ s)
    (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S)
      (graphTransferDatum S) A is)
    (w : List (Coordinate n)) (hw : w.length ≤ μ) (x y η : Euclidean n) :
    (ρ η) ^ frequencyOrder w * ‖jet w p.1 x y η‖ ≤ branchJetConstant n s μ L K *
      H ^ (((s - p.2.length : ℕ) : ℝ) / s) := by
  by_cases hz : jet w p.1 x y η = 0
  · rw [hz, norm_zero, mul_zero]
    exact mul_nonneg (branchJetConstant_nonneg n s μ (zero_le_one.trans hL) (zero_le_one.trans hK))
      (Real.rpow_nonneg (zero_le_one.trans hH) _)
  have hsupp : tsupport (uncurry A) ⊆ K₀ ×ˢ F₀ :=
    tsupport_subset_carrier hK₀ hF₀ hsupport
  have hj := graph_branch_jet_support (S := S) (A := A) is p hp w
  have hc : ((x, y), η) ∈ K₀ ×ˢ F₀ :=
    hsupp (hj (subset_tsupport (uncurry (jet w p.1)) hz))
  have hopen : IsOpen (regularRegion S) := isOpen_regularRegion (S := S) hphase
  have hreg : SmoothPrimitivesOn S A (regularRegion S) :=
    smoothPrimitivesOn_regularRegion (S := S) (A := A) hphase hsmooth
  have hmem : ((x, y), η) ∈ regularRegion S :=
    mem_regularRegion_of_carrier (S := S) hF₀0 hinv hc
  have hAmp : ∀ v, (ρ η) ^ frequencyOrder v * ‖jet v A x y η‖ ≤ q none v.length := hA ((x, y), η) hc
  have hScalar : ∀ a v, (ρ η) ^ frequencyOrder v * ‖jet v (scalarPrimitive S a) x y η‖ ≤ q (some a) v.length :=
    hS ((x, y), η) hc
  exact graph_branch_jet_norm_le (S := S) (A := A) (U := regularRegion S) hopen
    hreg q hq hmono μ s is his p hp L K H hL hK hH hlow hhigh hinterp
    (ρ η) (hρ η) x y η hmem hAmp hScalar w hw

/-- Uniform adjoint bounds at every point from regularity away from zero and
an inverse gap only on the physical carrier. Nonvanishing branch jets are
proved to lie in the regular neighborhood. For the reverse graph `A` is already
conjugate-transposed, as in `WeakTransfer`.
Source: Step 3, `app:ch_regular_base:eq:fio-input`. -/
theorem adjoint_branch_jet_norm_le_of_carrier
    {K₀ : Set (Euclidean n × Euclidean n)} {F₀ : Set (Euclidean n)}
    (hK₀ : IsCompact K₀) (hF₀ : IsClosed F₀) (hF₀0 : (0 : Euclidean n) ∉ F₀)
    (hphase : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hinv : ∀ p ∈ K₀, ∀ η, η ≠ 0 → IsUnit (mixedPhaseMatrix S p.1 η).det)
    (hsmooth : ∀ p : Point n, p.2 ≠ 0 → ContDiffAt ℝ ∞ (uncurry A) p)
    (hsupport : ∀ p : Point n, p ∉ K₀ ×ˢ F₀ → uncurry A p = 0)
    (ρ : Euclidean n → ℝ) (hρ : ∀ η, 0 ≤ ρ η)
    (q : Option (ScalarIndex n) → ℕ → ℝ) (hq : ∀ a j, 0 ≤ q a j)
    (hmono : ∀ a, Monotone (q a)) (μ s : ℕ)
    (L K H : ℝ) (hL : 1 ≤ L) (hK : 1 ≤ K) (hH : 1 ≤ H)
    (hlow : ∀ a, q a μ ≤ L) (hhigh : ∀ a, q a (μ + s) ≤ H)
    (hinterp : ∀ a j, μ < j → j < μ + s →
      q a j ≤ K * q a μ ^ (1 - ((j - μ : ℕ) : ℝ) / s) *
        q a (μ + s) ^ (((j - μ : ℕ) : ℝ) / s))
    (hA : ∀ p ∈ K₀ ×ˢ F₀, ∀ w, (ρ p.2) ^ frequencyOrder w * ‖uncurry (jet w A) p‖ ≤ q none w.length)
    (hS : ∀ p ∈ K₀ ×ˢ F₀, ∀ a w,
      (ρ p.2) ^ frequencyOrder w * ‖uncurry (jet w (scalarPrimitive S a)) p‖ ≤ q (some a) w.length)
    (is : List (Fin n)) (his : is.length ≤ s)
    (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S)
      (adjointTransferDatum S) A is)
    (w : List (Coordinate n)) (hw : w.length ≤ μ) (x y η : Euclidean n) :
    (ρ η) ^ frequencyOrder w * ‖jet w p.1 x y η‖ ≤ branchJetConstant n s μ L K *
      H ^ (((s - p.2.length : ℕ) : ℝ) / s) := by
  by_cases hz : jet w p.1 x y η = 0
  · rw [hz, norm_zero, mul_zero]
    exact mul_nonneg (branchJetConstant_nonneg n s μ (zero_le_one.trans hL) (zero_le_one.trans hK))
      (Real.rpow_nonneg (zero_le_one.trans hH) _)
  have hsupp : tsupport (uncurry A) ⊆ K₀ ×ˢ F₀ :=
    tsupport_subset_carrier hK₀ hF₀ hsupport
  have hj := adjoint_branch_jet_support (S := S) (A := A) is p hp w
  have hc : ((x, y), η) ∈ K₀ ×ˢ F₀ :=
    hsupp (hj (subset_tsupport (uncurry (jet w p.1)) hz))
  have hopen : IsOpen (regularRegion S) := isOpen_regularRegion (S := S) hphase
  have hreg : SmoothPrimitivesOn S A (regularRegion S) :=
    smoothPrimitivesOn_regularRegion (S := S) (A := A) hphase hsmooth
  have hmem : ((x, y), η) ∈ regularRegion S :=
    mem_regularRegion_of_carrier (S := S) hF₀0 hinv hc
  have hAmp : ∀ v, (ρ η) ^ frequencyOrder v * ‖jet v A x y η‖ ≤ q none v.length := hA ((x, y), η) hc
  have hScalar : ∀ a v, (ρ η) ^ frequencyOrder v * ‖jet v (scalarPrimitive S a) x y η‖ ≤ q (some a) v.length :=
    hS ((x, y), η) hc
  exact adjoint_branch_jet_norm_le (S := S) (A := A) (U := regularRegion S) hopen
    hreg q hq hmono μ s is his p hp L K H hL hK hH hlow hhigh hinterp
    (ρ η) (hρ η) x y η hmem hAmp hScalar w hw

end JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget.Local.Weighted
