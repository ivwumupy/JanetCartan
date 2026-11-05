module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.BranchAmplitudes

/-!
# Primitive symbol budgets after exchanging the physical positions

The reverse branch is restored in its own output/source order. To use the
original graph calculus one exchanges those positions and conjugate-transposes.
The exchange is an isometry of the normalized variables, so the primitive
joint-jet proof uses exactly the same reserve. Consumer: the literal reversed
L² construction for `new:eq:carrier-ibp` and
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
open FourierIntegral FullAmplitudePrimitiveBudget.Local PrimitiveProfiles
open SourceExpansion FullLowBounds BranchAmplitudes CompactTransfer ModifiedLow NearCarrierSymbol
variable {n r : ℕ}
local notation "En" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- Exchange only the two physical positions. The normalized covector, and
therefore the physical frequency weight, stay fixed (`new:eq:carrier-ibp`). -/
def exchangeAnnularPositions : Point n ≃ₗᵢ[ℝ] Point n :=
  { (LinearEquiv.prodComm ℝ En En).prodCongr (LinearEquiv.refl ℝ En) with
    norm_map' := by intro q; simp [Prod.norm_def, max_comm] }

/-- The position exchange preserves every joint derivative norm, without
increasing its order. Consumer: `hasFullSourceSymbolBound_exchanged_modifiedAmplitude`.
Source: the literal reversed case of `new:eq:carrier-coefficient`. -/
theorem norm_iteratedFDeriv_exchangeAnnularPositions (f : Point n → Mat)
    (q : Point n) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun q => f ((q.1.2, q.1.1), q.2)) q‖ =
      ‖iteratedFDeriv ℝ j f ((q.1.2, q.1.1), q.2)‖ :=
  exchangeAnnularPositions.norm_iteratedFDeriv_comp_right f q j

/-- The support rectangle exchanges its two sides, and the frequency carrier
is unchanged. Conjugate transpose costs no support or regularity assumption.
The original graph chart still uses `X`, not a chart for a substituted phase.
Source: the literal adjoint case of `app:ch_response:eq:direct-envelope-profile`. -/
theorem forwardAmplitudeAdmissible_exchange_conjTranspose
    {X Y F : Set En} {A : FullAmplitude n r}
    (hA : ForwardAmplitudeAdmissible Y X F A) :
    ForwardAmplitudeAdmissible X Y F (fun x y ξ => (A y x ξ).conjTranspose) := by
  apply forwardAmplitudeAdmissible_conjTranspose
  refine ⟨hA.smooth.comp
    (contDiff_snd.fst.prodMk (contDiff_fst.prodMk contDiff_snd.snd)), ?_⟩
  intro x y ξ h
  apply hA.support y x ξ
  rcases h with hx | hy | hξ
  · exact Or.inr (Or.inl hx)
  · exact Or.inl hy
  · exact Or.inr (Or.inr hξ)

/-- Joint normalized jets of the actual branch give the SAME source-symbol
budget after exchange and conjugate transpose. The order and annular weights
are retained, and the low derivative reserve is still `N`.
Consumer: `exists_reverseJointTransferTerm_symbol_constant`, for
`app:ch_response:eq:direct-envelope-profile`. -/
theorem hasFullSourceSymbolBound_exchanged_modifiedAmplitude
    {f : Point n → Mat} (hf : ContDiff ℝ ∞ f)
    {lam radius B : ℝ} (hlam : 1 ≤ lam) (hradius : 0 ≤ radius) (hB : 0 ≤ B)
    (p : ℤ) (N : ℕ)
    (hs : ∀ q ∈ tsupport f, ‖q.2‖ ≤ radius)
    (hj : ∀ j ≤ N, ∀ q, ‖iteratedFDeriv ℝ j f q‖ ≤ B) :
    HasFullSourceSymbolBound (fun x y ξ => (modifiedAmplitude lam p f y x ξ).conjTranspose)
      N ((1 + radius) ^ N * (lam ^ p * B)) := by
  have hlampos : 0 < lam := zero_lt_one.trans_le hlam
  have hp : 0 ≤ lam ^ p := (zpow_pos hlampos p).le
  let g : Point n → Mat := fun q => f ((q.1.2, q.1.1), q.2)
  have hg : ContDiff ℝ ∞ g := hf.comp exchangeAnnularPositions.contDiff
  have hgs : ∀ q ∈ tsupport ((lam ^ p) • g), ‖q.2‖ ≤ radius := by
    intro q hq
    have hq' := tsupport_smul_subset_right (fun _ : Point n => lam ^ p) g hq
    have hpre := tsupport_comp_subset_preimage f exchangeAnnularPositions.continuous hq'
    exact hs (exchangeAnnularPositions q) hpre
  apply hasFullSourceSymbolBound_conjTranspose
  change HasFullSourceSymbolBound (modifiedAmplitude lam p g) N _
  apply hasFullSourceSymbolBound_of_normalized_jets
    (contDiff_modifiedAmplitude lam p hg) hlam hradius (mul_nonneg hp hB) N
    (support_physicalAmplitudeOfNormalized hlampos hgs)
  intro j hjN q
  rw [normalizedField_modifiedAmplitude hlampos.ne' p,
    iteratedFDeriv_const_smul_apply (hg.of_le (by simp)).contDiffAt,
    norm_smul, Real.norm_of_nonneg hp]
  apply mul_le_mul_of_nonneg_left _ hp
  rw [show g = fun q => f ((q.1.2, q.1.1), q.2) from rfl,
    norm_iteratedFDeriv_exchangeAnnularPositions]
  exact hj j hjN _

variable {P ι : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [Fintype ι]

/-- Primitive reversed critical geometry and original phase/amplitude jets
produce the exchanged conjugate-transposed symbol needed by the original
forward graph constructor. The constant precedes all varying fields and
scales, and the reserve is unchanged from
`exists_jointTransferTerm_symbol_constant`. No branch bound is assumed.
Source: `new:eq:carrier-coefficient`, `app:ch_response:eq:direct-envelope-profile`.
-/
theorem exists_reverseJointTransferTerm_symbol_constant
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (es : List (En × P)) (t : JointTransferTerm n P Mat ι)
    (ht : t ∈ jointTransferTerms b es) (N : ℕ)
    (Aphase Aamp : ℕ → ℝ) (hphase : ∀ j, 0 ≤ Aphase j) (hamp : ∀ j, 0 ≤ Aamp j)
    {B radius : ℝ} (hB : 0 ≤ B) (hradius : 0 ≤ radius) :
    ∃ C ≥ 0, ∀ (R : ℕ), N + 2 < R → ∀ (L lam : ℝ), 1 ≤ L → 1 ≤ lam →
      ∀ (p : ℤ) (f : (En × P) → CarrierVariables n → ℝ)
        (w₀ : (En × P) → CarrierVariables n)
        (α : (En × P) → CarrierVariables n → Mat)
        (U : Set (En × P)) (D : Set (CarrierVariables n)),
      IsOpen U → IsOpen D → Convex ℝ D →
      ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D) →
      ContDiffOn ℝ ∞ w₀ U → MapsTo w₀ U D →
      (∀ q ∈ U, gradient (f q) (w₀ q) = 0) →
      (∀ q ∈ U, ∀ w ∈ D, IsUnit (averagedPhaseHessian f w₀ q w)) →
      (∀ q ∈ U, ∀ w ∈ D, ‖Ring.inverse (averagedPhaseHessian f w₀ q w)‖ ≤ B) →
      (∀ j ≤ N + (es.length - t.datumWord.length) + 2, ∀ q ∈ U ×ˢ D,
        ‖iteratedFDeriv ℝ j (Function.uncurry f) q‖ ≤ Aphase j * L ^ (j - R)) →
      ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D) →
      (∀ j ≤ N + (es.length - t.datumWord.length), ∀ q ∈ U ×ˢ D,
        ‖iteratedFDeriv ℝ j (Function.uncurry α) q‖ ≤ Aamp j * L ^ (j + 2 - R)) →
      ∀ c : P,
      (∀ q, normalizedSlice c q ∈ tsupport (Function.uncurry α) →
        normalizedSlice c q ∈ U ×ˢ D) →
      (∀ q, normalizedSlice c q ∈ tsupport (Function.uncurry α) → ‖q.2‖ ≤ radius) →
      ContDiff ℝ ∞ (normalizedTermAmplitude b f w₀ α t c) ∧
        HasFullSourceSymbolBound (fun x y ξ =>
          (modifiedAmplitude lam p (normalizedTermAmplitude b f w₀ α t c) y x ξ).conjTranspose)
          N (C * lam ^ p * L ^ (es.length - t.datumWord.length)) := by
  obtain ⟨Pj, hPj, hfields⟩ := exists_jointAmplitudeFields_jet_profile
    (n := n) (E := En × P) (M := Mat) (ι := ι) Aphase Aamp hphase hamp hB
  refine ⟨(1 + radius) ^ N * termLowConstant t Pj N,
    mul_nonneg (pow_nonneg (by linarith) _) (termLowConstant_nonneg t Pj hPj N), ?_⟩
  intro R hR L lam hL hlam p f w₀ α U D hU hD hcD hf hw₀ h₀ hcrit hu hi hp hα hαjet c hs hsfreq
  have hA := contDiffOn_transferCoefficient hU hD hcD hf hw₀ h₀ hu
  have hsm := contDiff_normalizedTermAmplitude b hU hD hα hA es t ht c hs
  refine ⟨hsm, ?_⟩
  have hsymbol := hasFullSourceSymbolBound_exchanged_modifiedAmplitude hsm hlam hradius
    (mul_nonneg (termLowConstant_nonneg t Pj hPj N)
      (pow_nonneg (zero_le_one.trans hL) _)) p N
    (fun q hq => hsfreq q (tsupport_normalizedTermAmplitude_subset b f w₀ α es t ht c hq))
    (fun j hj q => norm_lowJet_normalizedTermAmplitude_le b hU hD hα hA es t ht c hs
      Pj hPj N R hR hL
      (hfields R (by omega) L hL (N + (es.length - t.datumWord.length)) b f w₀ α U D
        hU hD hcD hf hw₀ h₀ hcrit hu hi hp hα hαjet) hj q)
  convert hsymbol using 1
  ring

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
