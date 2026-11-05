module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionProtection
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.GradientGaps

/-!
# Actual supported relations for protected proof masks

The relations in `app:ch_regular:lem:finite-chain` retain the two physical
factor masks, the original source in the reverse orientation, and every
point of the root and physical segments. Only zero-energy flow is included.
The diagonal is supplied by `PositiveConicChain`, without an energy condition.

The primitive flow inputs below are the initial condition and ODE on the
common initial-state/time buffer of `UniformGeometry`; `K` is a closed
whole-segment buffer inside its open root domain. No invariant-set or mask
conclusion is an input. The current-family instantiation remains with the
sector construction and the arbitrary-accuracy parent.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic EvolutionIntegratedLocalization ProtectedFlow

variable {d : ℕ}

/-- The original forward source, also in a literal adjoint factor
(`app:ch_regular:eq:joint-stationary`). -/
def originalSource (backward : Bool)
    (a b : Euclidean (d + 1) × Euclidean (d + 1)) := if backward then b else a

/-- The original forward output; physical factors keep both positions
(`app:ch_regular:lem:finite-chain`). -/
def originalTarget (backward : Bool)
    (a b : Euclidean (d + 1) × Euclidean (d + 1)) := if backward then a else b

/-- The full supported segment, including both endpoints. `U` is the initial
state buffer, `K` the whole root-state buffer, and `W` the physical buffer.
Consumer: `maskedZeroEnergyRelation` and its compactness construction
(`app:ch_regular:lem:finite-chain`). -/
def elapsedSegmentCarrier
    (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d))
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (U K : Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1))) :
    Set ((Euclidean (d + 1) × Euclidean (d + 1)) × ℝ) :=
  {ar | spacetimeRootState ar.1 ∈ U ∧ ∀ t ∈ Icc 0 ar.2,
    Φ (spacetimeRootState ar.1, t) ∈ K ∧
      (physicalPencilRootState e h (Φ (spacetimeRootState ar.1, t))).1 ∈ W}

/-- The actual zero-energy relation with both physical masks and the entire
segment restriction. `Δ` is the original elapsed support bound and is never
multiplied by proof depth. Both orientations use the SAME forward flow
(`app:ch_regular:lem:finite-chain`). -/
def maskedZeroEnergyRelation
    (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d))
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (U K : Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
    (χsource χout : Euclidean (d + 1) → ℂ) (Δ : ℝ) (backward : Bool)
    (a b : Euclidean (d + 1) × Euclidean (d + 1)) : Prop :=
  ∃ r ∈ Icc 0 Δ,
    (originalSource backward a b, r) ∈ elapsedSegmentCarrier e h Φ U K W ∧
    (originalSource backward a b).1 ∈ tsupport χsource ∧
    (originalTarget backward a b).1 ∈ tsupport χout ∧
    zeroEnergyFlowRelation backward h Φ r a b

/-- A zero-energy flow segment is a complete pencil-root segment. The
original source, ODE, and whole domains are retained for either orientation;
there is no fixed-elapsed arbitrary-energy graph substitution
(`app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`). -/
theorem maskedZeroEnergyRelation_completePencilRootSegment
    {e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d)}
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {U K D : Set (RootState (Euclidean d))} {W : Set (Euclidean (d + 1))}
    {χsource χout : Euclidean (d + 1) → ℂ} {Δ : ℝ}
    (hKD : K ⊆ D) (hi : ∀ v ∈ U, Φ (v, 0) = v)
    (hode : ∀ v ∈ U, ∀ t ∈ Icc 0 Δ,
      HasDerivAt (fun s ↦ Φ (v, s)) (rootHamiltonField h (Φ (v, t))) t)
    {backward : Bool} {a b : Euclidean (d + 1) × Euclidean (d + 1)}
    (hab : maskedZeroEnergyRelation e h Φ U K W χsource χout Δ backward a b) :
    CompletePencilRootSegment e h D W
      (adaptedPhysicalPhaseState e a) (adaptedPhysicalPhaseState e b) := by
  have forward {a b : Euclidean (d + 1) × Euclidean (d + 1)} {r : ℝ}
      (hr : r ∈ Icc 0 Δ)
      (hc : (a, r) ∈ elapsedSegmentCarrier e h Φ U K W)
      (he : rootSuspension h a = 0)
      (hf : b = rootSuspensionState h 0 (Φ (spacetimeRootState a, r))) :
      CompletePencilRootSegment e h D W
        (adaptedPhysicalPhaseState e a) (adaptedPhysicalPhaseState e b) := by
    refine ⟨fun t ↦ Φ (spacetimeRootState a, t), 0, r, 0, r,
      ⟨le_rfl, hr.1⟩, ⟨hr.1, le_rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      exact hode _ hc.1 t ⟨ht.1, ht.2.trans hr.2⟩
    · exact fun t ht ↦ hKD (hc.2 t ht).1
    · exact fun t ht ↦ (hc.2 t ht).2
    · dsimp only
      rw [hi _ hc.1]
      exact adaptedPhysicalPhaseState_eq_root_of_zero_energy e h a he
    · rw [hf, adaptedPhysicalPhaseState_rootSuspensionState]
  obtain ⟨r, hr, hc, _, _, hrel⟩ := hab
  cases backward
  · exact forward hr hc hrel.1 hrel.2
  · exact (forward hr hc hrel.1 hrel.2).symm

/-- A root patch is transported back from its own canonical coordinates.
The finite family may include both source signs as distinct indices; the
orientation is separately quantified and is not identified with a sign
(`app:ch_regular:lem:finite-chain`). -/
def physicalDirectRelation {J : Type*}
    (i : J → Fin (d + 1)) (h : J → RootState (Euclidean d) → ℝ)
    (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (U K : J → Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
    (χsource χout : J → Euclidean (d + 1) → ℂ) (Δ : ℝ)
    (p q : Euclidean (d + 1) × Euclidean (d + 1)) : Prop :=
  ∃ j backward a b,
    maskedZeroEnergyRelation (coordinateSplit (i j)) (h j) (Φ j) (U j) (K j) W
      (χsource j) (χout j) Δ backward a b ∧
    p = adaptedPhysicalPhaseState (coordinateSplit (i j)) a ∧
    q = adaptedPhysicalPhaseState (coordinateSplit (i j)) b

/-- Source recutting uses the literal physical support `X = tsupport χ₂`.
The full diagonal of an elliptic factor is retained. The producer of the
plateau `χ₃ = 1` on this support is the original nested cutoff construction
(`app:ch_regular:lem:finite-chain`, protected finite-chain paragraph). -/
def sourceRecutRelation
    (χ₂ : Euclidean (d + 1) → ℝ)
    (R : (Euclidean (d + 1) × Euclidean (d + 1)) →
      (Euclidean (d + 1) × Euclidean (d + 1)) → Prop)
    (p q : Euclidean (d + 1) × Euclidean (d + 1)) : Prop :=
  p.1 ∈ tsupport χ₂ ∧ (p = q ∨ R p q)

/-- Every actual recut source sees the original outer plateau; recutting
does not introduce a new source domain (`app:ch_regular:lem:finite-chain`). -/
theorem sourceRecutRelation_outer_eq_one
    {χ₂ χ₃ : Euclidean (d + 1) → ℝ}
    (hcut : EqOn χ₃ 1 (tsupport χ₂))
    {R : (Euclidean (d + 1) × Euclidean (d + 1)) →
      (Euclidean (d + 1) × Euclidean (d + 1)) → Prop}
    {p q : Euclidean (d + 1) × Euclidean (d + 1)}
    (hrecut : sourceRecutRelation χ₂ R p q) : χ₃ p.1 = 1 :=
  hcut hrecut.1

/-- Recutting preserves the original full chain, including its identity
branches and its length (`app:ch_regular:lem:finite-chain`). -/
theorem sourceRecutRelation_chain
    {χ₂ : Euclidean (d + 1) → ℝ}
    {R : (Euclidean (d + 1) × Euclidean (d + 1)) →
      (Euclidean (d + 1) × Euclidean (d + 1)) → Prop}
    {p q : Euclidean (d + 1) × Euclidean (d + 1)} {k : ℕ}
    (hc : PositiveConicChain (sourceRecutRelation χ₂ R) p q k) :
    PositiveConicChain R p q k := by
  induction hc with
  | refl p => exact .refl p
  | tail hs _ ih =>
    exact .tail (hs.elim Or.inl (fun h ↦ h.2)) ih

/-- Reachability at the fixed proof depth, with the full diagonal included.
This is an actual relational image, not a hypothesized protected set.
Consumer: construction of nested masks for `finiteChain_observation_rapidDecayAt`
(`app:ch_regular:lem:finite-chain`). -/
def reachableAt
    (R : (Euclidean (d + 1) × Euclidean (d + 1)) →
      (Euclidean (d + 1) × Euclidean (d + 1)) → Prop)
    (S : Set (Euclidean (d + 1) × Euclidean (d + 1))) (k : ℕ) :
    Set (Euclidean (d + 1) × Euclidean (d + 1)) :=
  {q | ∃ p ∈ S, PositiveConicChain R p q k}

/-- Chains of the actual relations, including diagonal branches, are chains
of whole root segments in the common physical domain. This is the input of
the retained comparison-family theorem (`app:ch_regular:thm:no-return`). -/
theorem physicalDirectRelation_chain {J : Type*}
    (i : J → Fin (d + 1)) (h : J → RootState (Euclidean d) → ℝ)
    (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (U K D : J → Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
    (χsource χout : J → Euclidean (d + 1) → ℂ) (Δ : ℝ)
    (hKD : ∀ j, K j ⊆ D j) (hi : ∀ j v, v ∈ U j → Φ j (v, 0) = v)
    (hode : ∀ j v, v ∈ U j → ∀ t ∈ Icc 0 Δ,
      HasDerivAt (fun s ↦ Φ j (v, s)) (rootHamiltonField (h j) (Φ j (v, t))) t)
    {p q : Euclidean (d + 1) × Euclidean (d + 1)} {k : ℕ}
    (hc : PositiveConicChain (physicalDirectRelation i h Φ U K W χsource χout Δ) p q k) :
    PositiveConicChain (fun a b ↦ ∃ j,
      CompletePencilRootSegment (coordinateSplit (i j)) (h j) (D j) W a b) p q k := by
  induction hc with
  | refl p => exact .refl p
  | @tail p a q k hs _ ih =>
    apply PositiveConicChain.tail (n := k) ?_ ih
    rcases hs with hd | ⟨j, backward, a, b, hab, rfl, rfl⟩
    · exact Or.inl hd
    · exact Or.inr ⟨j, maskedZeroEnergyRelation_completePencilRootSegment
        (hKD j) (hi j) (hode j) hab⟩

/-- Enlarging only the whole physical segment buffer preserves the actual
relation, its masks, orientation and elapsed time. This connects the closed
compactness buffer to the open comparison ball without changing any factor
(`app:ch_regular:lem:finite-chain`). -/
theorem physicalDirectRelation_mono_physical_buffer {J : Type*}
    {i : J → Fin (d + 1)} {h : J → RootState (Euclidean d) → ℝ}
    {Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {U K : J → Set (RootState (Euclidean d))}
    {W W' : Set (Euclidean (d + 1))}
    {χsource χout : J → Euclidean (d + 1) → ℂ} {Δ : ℝ}
    (hW : W ⊆ W') {p q : Euclidean (d + 1) × Euclidean (d + 1)}
    (hpq : physicalDirectRelation i h Φ U K W χsource χout Δ p q) :
    physicalDirectRelation i h Φ U K W' χsource χout Δ p q := by
  obtain ⟨j, backward, a, b, ⟨r, hr, hc, hs, ho, hf⟩, hp, hq⟩ := hpq
  exact ⟨j, backward, a, b,
    ⟨r, hr, ⟨hc.1, fun t ht ↦ ⟨(hc.2 t ht).1, hW (hc.2 t ht).2⟩⟩,
      hs, ho, hf⟩, hp, hq⟩

/-- The closed physical carrier embeds into the retained open comparison
ball at every step, with the same chain length and elapsed bound
(`app:ch_regular:thm:no-return`). -/
theorem physicalDirectRelation_chain_mono_physical_buffer {J : Type*}
    {i : J → Fin (d + 1)} {h : J → RootState (Euclidean d) → ℝ}
    {Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {U K : J → Set (RootState (Euclidean d))}
    {W W' : Set (Euclidean (d + 1))}
    {χsource χout : J → Euclidean (d + 1) → ℂ} {Δ : ℝ}
    (hW : W ⊆ W') {p q : Euclidean (d + 1) × Euclidean (d + 1)} {n : ℕ}
    (hc : PositiveConicChain (physicalDirectRelation i h Φ U K W χsource χout Δ) p q n) :
    PositiveConicChain (physicalDirectRelation i h Φ U K W' χsource χout Δ) p q n := by
  induction hc with
  | refl p => exact .refl p
  | tail hs _ ih =>
    exact .tail (hs.imp_right (physicalDirectRelation_mono_physical_buffer hW)) ih

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
