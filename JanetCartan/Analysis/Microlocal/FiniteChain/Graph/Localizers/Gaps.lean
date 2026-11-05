module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Localizers.Masks
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Localizers.Differential

/-!
# Actual joint derivative gaps on complementary supports

The compactness argument of `app:ch_regular:lem:finite-chain` is applied to the
actual packed derivative. A single compact parameter set must contain the entire
family for a uniform conclusion; separate compactness for each phase is not such
an input. Quantitative bounds in terms of mixed inverse geometry are separate.
-/

@[expose] public noncomputable section
open Set
namespace JanetCartan.FiniteChain.Graph
open FourierIntegral

variable {n : ℕ}

/-- A zero of the actual joint derivative lies on the full canonical relation,
for either literal orientation (`app:ch_regular:eq:joint-stationary`). -/
theorem orientedRelation_of_fderiv_jointPhase_eq_zero
    (backward : Bool) (φ : Euclidean n → Euclidean n → ℝ)
    (x y : Euclidean n) (p : JointVariables (Euclidean n))
    (hφ : DifferentiableAt ℝ (Function.uncurry φ) (p.1.1, p.2.1))
    (hzero : fderiv ℝ (jointPhase backward φ x y) p = 0) :
    orientedRelation backward φ (y, p.2.2.1) (x, p.2.2.2) := by
  rcases p with ⟨⟨u,z⟩, ξ, η, ζ⟩
  have hu := (hφ.hasFDerivAt.comp u
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) u ξ)).differentiableAt
  have hξ := (hφ.hasFDerivAt.comp ξ
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) u ξ)).differentiableAt
  cases backward
  · have hs := (fderiv_jointPhase_forward_eq_zero_iff φ x y _ hφ).mp hzero
    obtain ⟨h1, h2, h3, h4, h5⟩ := (forwardStationary_iff φ x y u z ξ η ζ hu hξ).mp hs
    subst η; subst z; subst x
    exact ⟨h1, h3⟩
  · have hs := (fderiv_jointPhase_reverse_eq_zero_iff φ x y _ hφ).mp hzero
    obtain ⟨h1, h2, h3, h4, h5⟩ := (reverseStationary_iff φ x y u z ξ η ζ hu hξ).mp hs
    subst ζ; subst u; subst x
    exact ⟨h1, h3⟩

/-- The complementary amplitude support has no actual stationary point,
including both base equations and the closed support of `1-mo`
(`app:ch_regular:lem:finite-chain`). -/
theorem fderiv_jointPhase_ne_zero_of_buffer
    (backward : Bool) (φ : Euclidean n → Euclidean n → ℝ)
    {mi mo : LocalizerSymbol n} {R : Set (Euclidean n × Euclidean n)}
    (κ : (Euclidean n × Euclidean n) → Euclidean n × Euclidean n)
    (hbuffer : ∀ p ∈ tsupport mi, κ p ∈ interior {q | mo q = 1})
    (hchart : ∀ p ∈ tsupport mi, ∀ q ∈ R,
      orientedRelation backward φ p q → κ p = q)
    (x y : Euclidean n) (p : JointVariables (Euclidean n))
    (hφ : DifferentiableAt ℝ (Function.uncurry φ) (p.1.1, p.2.1))
    (hi : (y, p.2.2.1) ∈ tsupport mi) (hoR : (x, p.2.2.2) ∈ R)
    (ho : (x, p.2.2.2) ∈ tsupport (fun q => 1 - mo q)) :
    fderiv ℝ (jointPhase backward φ x y) p ≠ 0 := by
  intro hzero
  exact not_orientedRelation_of_buffer backward φ κ hbuffer hchart hi hoR ho
    (orientedRelation_of_fderiv_jointPhase_eq_zero backward φ x y p hφ hzero)

/-- One positive actual derivative gap for a whole compact family of phases
and integration points (`app:ch_regular:lem:finite-chain`). `S` must include the
phase parameter as well as the integration variables. The parent supplies this
compact family and continuity of its first derivatives on the actual conic
charts; this theorem does not infer uniformity from pointwise compactness. -/
theorem exists_compact_family_joint_gap
    {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsCompact S)
    (backward : Bool) (φ : X → Euclidean n → Euclidean n → ℝ)
    (x y : X → Euclidean n) (p : X → JointVariables (Euclidean n))
    {mi mo : LocalizerSymbol n} {R : Set (Euclidean n × Euclidean n)}
    (κ : X → (Euclidean n × Euclidean n) → Euclidean n × Euclidean n)
    (hbuffer : ∀ t ∈ S, ∀ q ∈ tsupport mi, κ t q ∈ interior {q | mo q = 1})
    (hchart : ∀ t ∈ S, ∀ q ∈ tsupport mi, ∀ r ∈ R,
      orientedRelation backward (φ t) q r → κ t q = r)
    (hφ : ∀ t ∈ S, DifferentiableAt ℝ (Function.uncurry (φ t)) ((p t).1.1, (p t).2.1))
    (hcont : ContinuousOn (fun t => fderiv ℝ (jointPhase backward (φ t) (x t) (y t))
      (p t)) S)
    (hi : ∀ t ∈ S, (y t, (p t).2.2.1) ∈ tsupport mi)
    (hoR : ∀ t ∈ S, (x t, (p t).2.2.2) ∈ R)
    (ho : ∀ t ∈ S, (x t, (p t).2.2.2) ∈ tsupport (fun q => 1 - mo q)) :
    ∃ δ > 0, ∀ t ∈ S, δ ≤ ‖fderiv ℝ (jointPhase backward (φ t) (x t) (y t)) (p t)‖ := by
  apply CompatibleResponse.exists_uniform_positive_bound hS hcont.norm
  intro t ht
  exact norm_pos_iff.mpr (fderiv_jointPhase_ne_zero_of_buffer backward (φ t) (κ t)
    (hbuffer t ht) (hchart t ht) (x t) (y t) (p t) (hφ t ht)
    (hi t ht) (hoR t ht) (ho t ht))

/-- The closed support of the actual joint amplitude retains the entire input
support and the closed complement of the output plateau. No regularity or
compact frequency support of the amplitude is required for this inclusion
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem jointAmplitude_tsupport_subset {r : ℕ} (ρ : ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ) (x y : Euclidean n)
    {p : JointVariables (Euclidean n)}
    (hp : p ∈ tsupport (jointAmplitude ρ A mi mo χA χo x y)) :
    (y, p.2.2.1) ∈ tsupport mi ∧
      (x, p.2.2.2) ∈ tsupport (fun q => 1 - mo q) := by
  constructor
  · apply closure_minimal (s := Function.support (jointAmplitude ρ A mi mo χA χo x y))
      (t := (fun p : JointVariables (Euclidean n) => (y, p.2.2.1)) ⁻¹' tsupport mi)
      _ ((isClosed_tsupport mi).preimage (by fun_prop)) hp
    intro q hq
    apply subset_tsupport mi
    intro hz
    exact hq (by simp [jointAmplitude, hz])
  · apply closure_minimal (s := Function.support (jointAmplitude ρ A mi mo χA χo x y))
      (t := (fun p : JointVariables (Euclidean n) => (x, p.2.2.2)) ⁻¹'
        tsupport (fun q => 1 - mo q))
      _ ((isClosed_tsupport _).preimage (by fun_prop)) hp
    intro q hq
    apply subset_tsupport (fun q => 1 - mo q)
    intro hz
    exact hq (by simp [jointAmplitude, hz])

end JanetCartan.FiniteChain.Graph
