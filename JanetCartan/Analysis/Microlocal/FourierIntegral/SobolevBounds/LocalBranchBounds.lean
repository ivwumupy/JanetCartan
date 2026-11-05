module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.LocalBranchBounds.Carrier

/-!
# Local quantitative graph branch bounds on the actual carrier

For Step 3 of `app:ch_regular_base:thm:actual-calculus`, this module proves
forward and literal reverse primitive expansions and their uniform low-jet
bounds without globally smooth homogeneous primitives. The open neighborhood
`Local.regularRegion` consists of nonzero physical covectors where the actual
mixed matrix is invertible. Phase regularity and the actual determinant gap
produce primitive regularity on this neighborhood.

Every joint jet of every branch is supported in the original complete amplitude.
Compact physical support and a closed frequency carrier excluding zero therefore
place every nonvanishing jet in that neighborhood. Outside the carrier the jet
vanishes, with no smoothness or inverse gap required there. Both physical masks,
both positions, physical covectors and derivatives of the actual inverse remain
in `Term.value` and `jet` throughout.

The same `branchJetConstant n s μ L K` works simultaneously for output words of
length at most `s` and joint low words of length at most `μ`. It depends on neither
the phase, the amplitude nor the high majorant. Individual primitive majorants,
low/high bounds and interpolation are explicit inputs. Their production from
normalized amplitude/phase seminorms and the inverse gap, and application of the
low L² reserve in `app:ch_regular_base:eq:fio-input`, remain obligations of
`jc-deduce-fio-strong-sobolev`; no branch/operator bound is assumed here.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget.Local
variable {n r : ℕ} {S : Euclidean n → Euclidean n → ℝ} {A : FullAmplitude n r}

/-- Local graph primitive budget, including multiplicities, factor counts and
joint excess order. Consumed by the low L² reserve in Step 3 of the actual
calculus. Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem graph_branch_primitive_budget {U : Set (Point n)}
    (hU : IsOpen U) (h : SmoothPrimitivesOn S A U)
    (is : List (Fin n)) (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S)
      (graphTransferDatum S) A is)
    (w : List (Coordinate n)) (μ : ℕ) (hw : w.length ≤ μ) :
    ∃ ts : List (Term n),
      Set.EqOn (uncurry (jet w p.1)) (uncurry (ts.map (Term.value S A)).sum) U ∧
      ts.length ≤ branchTermCount n is.length * (is.length + 1) ^ μ ∧
      ∀ t ∈ ts, t.order ≤ is.length - p.2.length + μ ∧
        t.orders.length ≤ is.length + 1 ∧
        OrderedProducts.excessOrder (fun _ => μ) t.orders ≤ is.length - p.2.length := by
  obtain ⟨ts, he, hn, ht⟩ := (graph_branch_bounded_expansion hU h is p hp).jet hU h w
  refine ⟨ts, he, hn.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by omega) hw)), fun t hm => ?_⟩
  have hb := (ht t hm).1.trans (Nat.add_le_add_left hw _)
  exact ⟨hb, (ht t hm).2, t.excess_le_of_order_le μ _ hb⟩

/-- Local adjoint primitive budget, including multiplicities, factor counts and
joint excess order. Consumed by the low L² reserve in Step 3 of the actual
calculus. Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem adjoint_branch_primitive_budget {U : Set (Point n)}
    (hU : IsOpen U) (h : SmoothPrimitivesOn S A U)
    (is : List (Fin n)) (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S)
      (adjointTransferDatum S) A is)
    (w : List (Coordinate n)) (μ : ℕ) (hw : w.length ≤ μ) :
    ∃ ts : List (Term n),
      Set.EqOn (uncurry (jet w p.1)) (uncurry (ts.map (Term.value S A)).sum) U ∧
      ts.length ≤ branchTermCount n is.length * (is.length + 1) ^ μ ∧
      ∀ t ∈ ts, t.order ≤ is.length - p.2.length + μ ∧
        t.orders.length ≤ is.length + 1 ∧
        OrderedProducts.excessOrder (fun _ => μ) t.orders ≤ is.length - p.2.length := by
  obtain ⟨ts, he, hn, ht⟩ := (adjoint_branch_bounded_expansion hU h is p hp).jet hU h w
  refine ⟨ts, he, hn.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by omega) hw)), fun t hm => ?_⟩
  have hb := (ht t hm).1.trans (Nat.add_le_add_left hw _)
  exact ⟨hb, (ht t hm).2, t.excess_le_of_order_le μ _ hb⟩

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
    (q : Option (ScalarIndex n) → ℕ → ℝ) (hq : ∀ a j, 0 ≤ q a j)
    (hmono : ∀ a, Monotone (q a)) (μ s : ℕ)
    (L K H : ℝ) (hL : 1 ≤ L) (hK : 1 ≤ K) (hH : 1 ≤ H)
    (hlow : ∀ a, q a μ ≤ L) (hhigh : ∀ a, q a (μ + s) ≤ H)
    (hinterp : ∀ a j, μ < j → j < μ + s →
      q a j ≤ K * q a μ ^ (1 - ((j - μ : ℕ) : ℝ) / s) *
        q a (μ + s) ^ (((j - μ : ℕ) : ℝ) / s))
    (hA : ∀ p ∈ K₀ ×ˢ F₀, ∀ w, ‖uncurry (jet w A) p‖ ≤ q none w.length)
    (hS : ∀ p ∈ K₀ ×ˢ F₀, ∀ a w,
      ‖uncurry (jet w (scalarPrimitive S a)) p‖ ≤ q (some a) w.length)
    (is : List (Fin n)) (his : is.length ≤ s)
    (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S)
      (graphTransferDatum S) A is)
    (w : List (Coordinate n)) (hw : w.length ≤ μ) (x y η : Euclidean n) :
    ‖jet w p.1 x y η‖ ≤ branchJetConstant n s μ L K *
      H ^ (((s - p.2.length : ℕ) : ℝ) / s) := by
  by_cases hz : jet w p.1 x y η = 0
  · rw [hz, norm_zero]
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
  have hAmp : ∀ v, ‖jet v A x y η‖ ≤ q none v.length := hA ((x, y), η) hc
  have hScalar : ∀ a v, ‖jet v (scalarPrimitive S a) x y η‖ ≤ q (some a) v.length :=
    hS ((x, y), η) hc
  exact graph_branch_jet_norm_le (S := S) (A := A) (U := regularRegion S) hopen
    hreg q hq hmono μ s is his p hp L K H hL hK hH hlow hhigh hinterp
    x y η hmem hAmp hScalar w hw

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
    (q : Option (ScalarIndex n) → ℕ → ℝ) (hq : ∀ a j, 0 ≤ q a j)
    (hmono : ∀ a, Monotone (q a)) (μ s : ℕ)
    (L K H : ℝ) (hL : 1 ≤ L) (hK : 1 ≤ K) (hH : 1 ≤ H)
    (hlow : ∀ a, q a μ ≤ L) (hhigh : ∀ a, q a (μ + s) ≤ H)
    (hinterp : ∀ a j, μ < j → j < μ + s →
      q a j ≤ K * q a μ ^ (1 - ((j - μ : ℕ) : ℝ) / s) *
        q a (μ + s) ^ (((j - μ : ℕ) : ℝ) / s))
    (hA : ∀ p ∈ K₀ ×ˢ F₀, ∀ w, ‖uncurry (jet w A) p‖ ≤ q none w.length)
    (hS : ∀ p ∈ K₀ ×ˢ F₀, ∀ a w,
      ‖uncurry (jet w (scalarPrimitive S a)) p‖ ≤ q (some a) w.length)
    (is : List (Fin n)) (his : is.length ≤ s)
    (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S)
      (adjointTransferDatum S) A is)
    (w : List (Coordinate n)) (hw : w.length ≤ μ) (x y η : Euclidean n) :
    ‖jet w p.1 x y η‖ ≤ branchJetConstant n s μ L K *
      H ^ (((s - p.2.length : ℕ) : ℝ) / s) := by
  by_cases hz : jet w p.1 x y η = 0
  · rw [hz, norm_zero]
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
  have hAmp : ∀ v, ‖jet v A x y η‖ ≤ q none v.length := hA ((x, y), η) hc
  have hScalar : ∀ a v, ‖jet v (scalarPrimitive S a) x y η‖ ≤ q (some a) v.length :=
    hS ((x, y), η) hc
  exact adjoint_branch_jet_norm_le (S := S) (A := A) (U := regularRegion S) hopen
    hreg q hq hmono μ s is his p hp L K H hL hK hH hlow hhigh hinterp
    x y η hmem hAmp hScalar w hw

end JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget.Local
