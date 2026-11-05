module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.TransportSymbolBounds.PhysicalJets
public import JanetCartan.Analysis.Microlocal.FourierIntegral.TransportSymbolBounds.FiniteInterpolation

/-!
# Physical transport symbol seminorms

For `app:ch_regular_base:eq:actual-one-high`, the high-frequency seminorm sums
suprema of the actual mixed derivatives, with a radius factor for each covector
slot and the negative symbol order. The normalized set is a buffered annular
chart; its radial dilation is measured in the original physical frequency units.
The definition is a real supremum, so applications must first establish the
bounds below. This does not assert a low-frequency extension.
-/

@[expose] public noncomputable section
open scoped BigOperators ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {X Ξ F G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Sum of physical mixed derivative suprema for symbol order `-d` on the radial
extension of a normalized chart `K`. Positions may include both kernel positions.
Consumed by the finite-calculus estimate `app:ch_regular_base:eq:actual-one-high`.
As for `cNorm`, boundedness is supplied by the subsequent estimates. -/
def transportPhysicalSeminorm (K : Set (X × Ξ)) (N d : ℕ) (f : X × Ξ → F) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), sSup {a : ℝ | ∃ (r : ℝ), 1 ≤ r ∧
    ∃ p ∈ K, ∃ (q : Finset (Fin n)) (v : Fin n → X × Ξ),
      (∀ i, if i ∈ q then (v i).1 = 0 else (v i).2 = 0) ∧
      (∀ i, ‖v i‖ ≤ 1) ∧ a = r ^ (d + q.card) *
        ‖iteratedFDeriv ℝ n f (p.1, r • p.2) v‖}

/-- The finite physical seminorm is controlled by the sum of normalized joint
bounds. The radial identity remains explicit so concrete amplitude assembly
must supply it from the primitive homogeneities, not assume a symbol estimate.
Source: `app:ch_regular_base:eq:actual-one-high`. -/
theorem transportPhysicalSeminorm_le_of_radial_identity (N d : ℕ)
    {K U V : Set (X × Ξ)} (hU : IsOpen U) (hV : IsOpen V) (hKU : K ⊆ U)
    {f b : X × Ξ → F} (hf : ContDiffOn ℝ N f V) (hb : ContDiffOn ℝ N b U)
    (hVrad : ∀ r : ℝ, 1 ≤ r → ∀ p ∈ K, (p.1, r • p.2) ∈ V)
    (hscale : ∀ r : ℝ, 1 ≤ r → Set.EqOn (fun z : X × Ξ ↦ f (z.1, r • z.2))
      (fun z ↦ (r⁻¹ ^ d) • b z) U)
    {C : ℕ → ℝ} (hC : ∀ n ≤ N, 0 ≤ C n)
    (hbound : ∀ n ≤ N, ∀ p ∈ K, ‖iteratedFDeriv ℝ n b p‖ ≤ C n) :
    transportPhysicalSeminorm K N d f ≤ ∑ n ∈ Finset.range (N + 1), C n := by
  apply Finset.sum_le_sum
  intro n hn
  have hnN : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  apply Real.sSup_le _ (hC n hnN)
  rintro _ ⟨r, hr, p, hp, q, v, hv, hvnorm, rfl⟩
  exact (norm_transportMixedJet_of_radial_identity n d (lt_of_lt_of_le zero_lt_one hr)
    hV hU (hf.of_le (by exact_mod_cast hnN)) (hb.of_le (by exact_mod_cast hnN))
    (hscale r hr) p (hVrad r hr p hp) (hKU hp) q v hv hvnorm).trans (hbound n hnN p hp)

/-- A uniform normalized one-high bound remains linear in the high coefficient
quantity after summing all physical mixed derivative suprema. This is the final
scalar aggregation for `app:ch_regular_base:eq:actual-one-high`. -/
theorem transportPhysicalSeminorm_oneHigh_of_radial_identity (N d : ℕ)
    {K U V : Set (X × Ξ)} (hU : IsOpen U) (hV : IsOpen V) (hKU : K ⊆ U)
    {f b : X × Ξ → F} (hf : ContDiffOn ℝ N f V) (hb : ContDiffOn ℝ N b U)
    (hVrad : ∀ r : ℝ, 1 ≤ r → ∀ p ∈ K, (p.1, r • p.2) ∈ V)
    (hscale : ∀ r : ℝ, 1 ≤ r → Set.EqOn (fun z : X × Ξ ↦ f (z.1, r • z.2))
      (fun z ↦ (r⁻¹ ^ d) • b z) U)
    {C : ℕ → ℝ} (hC : ∀ n ≤ N, 0 ≤ C n) {H : ℝ} (hH : 0 ≤ H)
    (hbound : ∀ n ≤ N, ∀ p ∈ K, ‖iteratedFDeriv ℝ n b p‖ ≤ C n * H) :
    transportPhysicalSeminorm K N d f ≤ (∑ n ∈ Finset.range (N + 1), C n) * H := by
  simpa only [Finset.sum_mul] using transportPhysicalSeminorm_le_of_radial_identity
    N d hU hV hKU hf hb hVrad hscale (fun n hn ↦ mul_nonneg (hC n hn) hH) hbound

/-- Literal isometries in the matrix value preserve the physical mixed seminorm,
including all masks and radius weights (`app:ch_regular_base:eq:actual-one-high`). -/
theorem transportPhysicalSeminorm_isometry (L : F ≃ₗᵢ[ℝ] G)
    (K : Set (X × Ξ)) (N d : ℕ) (f : X × Ξ → F) :
    transportPhysicalSeminorm K N d (L ∘ f) = transportPhysicalSeminorm K N d f := by
  have he (n : ℕ) (p : X × Ξ) (v : Fin n → X × Ξ) :
      ‖iteratedFDeriv ℝ n (L ∘ f) p v‖ = ‖iteratedFDeriv ℝ n f p v‖ := by
    rw [show (L ∘ f) = (L.toContinuousLinearEquiv ∘ f) from rfl,
      L.toContinuousLinearEquiv.iteratedFDeriv_comp_left]
    exact L.norm_map _
  simp only [transportPhysicalSeminorm, he]

variable {m : Type*} [Fintype m]

/-- The literal conjugate-transpose amplitude has the identical physical mixed
Frobenius seminorm, hence the same finite one-high bound. This concerns amplitudes,
not a graph operator adjoint identity (`app:ch_regular_base:eq:actual-one-high`). -/
theorem transportPhysicalSeminorm_conjTranspose (K : Set (X × Ξ)) (N d : ℕ)
    (f : X × Ξ → Matrix m m ℂ) :
    transportPhysicalSeminorm K N d (fun p ↦ (f p).conjTranspose) =
      transportPhysicalSeminorm K N d f := by
  let L : Matrix m m ℂ ≃ₗᵢ[ℝ] Matrix m m ℂ :=
    { Matrix.conjTransposeLinearEquiv m m ℝ ℂ with
      norm_map' := Matrix.frobenius_norm_conjTranspose }
  exact transportPhysicalSeminorm_isometry L K N d f

/-- Entrywise conjugation preserves the same physical mixed Frobenius seminorm,
with the literal differentiated masks (`app:ch_regular_base:eq:actual-one-high`). -/
theorem transportPhysicalSeminorm_conjugate (K : Set (X × Ξ)) (N d : ℕ)
    (f : X × Ξ → Matrix m m ℂ) :
    transportPhysicalSeminorm K N d (fun p ↦ (f p).map star) =
      transportPhysicalSeminorm K N d f := by
  let L : Matrix m m ℂ ≃ₗᵢ[ℝ] Matrix m m ℂ :=
    { Matrix.transposeLinearEquiv m m ℝ ℂ with
      norm_map' := Matrix.frobenius_norm_transpose }
  exact (transportPhysicalSeminorm_isometry L K N d (fun p ↦ (f p).conjTranspose)).trans
    (transportPhysicalSeminorm_conjTranspose K N d f)

end JanetCartan.FourierIntegral
