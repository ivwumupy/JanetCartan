module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.FrequencyBounds.ConicJets
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.FrequencyBounds.RadialCutoff
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.FrequencyBounds.Completion

/-!
# Frequency calculus for the actual transport amplitude

For `app:ch_background:eq:bg-symbol` and Step 1 of
`app:ch_background:prop:bg-frame`, these leaves prove:

* positive dilation of mixed jets divides the homogeneity weight by one factor
  per frequency derivative, retaining both physical-position variables;
* the actual homogeneous spectator amplitude satisfies that identity from the
  primitive conic inverse and Jacobian identities, with arbitrary angular masks;
* fixed smooth compact radial cutoffs, constant near zero, have uniform weighted
  symbol jets for every `R ≥ 1`, including the square required by the normal;
* a fixed smooth completion, with smooth bounded-frequency discrepancy from
  the actual high-cutoff amplitude, follows from primitive chart regularity,
  inverse identities, original support buffers and frequency comparison.

The consumer is `TransportSymbol`. Its geometric owners must instantiate the
primitive inputs. Quantitative normalized-shell amplitude estimates, their
application through the inverse substitution, and the final numerical symbol
bounds remain the parent's obligations. No normal-amplitude symbol estimate is
assumed in this calculus.
-/
