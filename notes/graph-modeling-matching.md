# Graph Modeling for CRN Coefficient Matching

*Zinan Huang, 2026-04-16*

This note records my understanding of the bipartite graph / flow network framework
used in the BD project (DNA30_BD) and the LPP pipeline for converting polynomial
ODEs into population protocol reactions. The framework is used in at least two places:
(1) PP → NAP via cubing, and (2) TPP → PLPP via coefficient matching.

---

## 1. The Core Asymmetry: Demand vs. Supply

The fundamental observation is that **negative and positive polynomial terms play
asymmetric roles** when converting ODE systems into reaction networks.

**Negative terms = Demand.** A negative term in x'_i must arise from a reaction
that *consumes* x_i. The CRN-implementability constraint (C3: negative terms in
x'_i must contain x_i as a factor) and the NAP condition (no species in its own
positive production) impose hard constraints on how these terms can be decomposed
into bimolecular reactions. The decomposition is often forced or has very few options.

**Positive terms = Supply.** Positive terms can be produced by any reaction whose
products include the target species. The decomposition into bimolecular reactions
is flexible — there are usually multiple valid factorizations.

This asymmetry is the reason the matching problem has the structure of a bipartite
graph: demand nodes (constrained) on one side, supply options (flexible) on the other.

---

## 2. Per-Monomial Bipartite Graphs

For each distinct monomial M that appears across all ODEs in the system:

- **Left nodes (supply):** All positive occurrences of M, with their coefficients.
  Each can be decomposed in multiple ways.

- **Right nodes (demand):** All negative occurrences of M, where the decomposition
  is constrained (must contain the variable being consumed, or must avoid
  autocatalysis, etc.).

- **Edges:** A supply node connects to a demand node if there exists a valid
  bimolecular factorization satisfying all constraints (C1–C4 for CRN, or
  non-autocatalytic for NAP).

**Feasibility = Hall's condition:** For every subset S of demand nodes,
|N(S)| ≥ |S| (the neighborhood has enough total supply capacity).

---

## 3. The PP → NAP Algorithm (BD Project)

**Goal:** Transform any PP (Population Protocol) into a NAP (Non-Autocatalytic
Protocol) where no species appears in its own positive production.

### Pipeline

1. **λ-trick:** Introduce slack variable r, rescale non-readout variables by λ.
   Still degree 2.

2. **r²-trick:** Multiply all derivatives by r². Degree rises from 2 to 4.
   This is a time reparametrization (dt_new = r^{-2} dt_old) that preserves
   equilibria and convergence.

3. **Cubing (degree-3 lifting):** Define lifted variables
   v_α = C(3,α) ∏ x_j^{α_j}, |α| = 3.
   By multinomial theorem, Σ v_α = (Σ x_j)³ = 1 (conservation).

### Why cubing works but squaring fails

The chain rule produces degree-6 monomials in the lifted system. Each must split
as m_β · m_γ with |β| = |γ| = 3, and β ≠ α, γ ≠ α (non-autocatalytic).

The **bucket size argument:**
- Squaring: buckets have 2 slots. A monomial r³x₁ splits as r²·rx₁ = z₀₀·z₀₁.
  The second factor z₀₁ IS the variable we're computing. No alternative exists.
  Failure: the single remaining slot after overflow is filled by exactly the
  foreign atom that reconstructs v_α.

- Cubing: buckets have 3 slots. Even with r appearing 4 times (max concentration),
  the split 4 = 2+2 leaves room for foreign atoms in both buckets. Neither bucket
  matches v_α = r³ because each has only 2 r-atoms plus a foreign atom.

### The only obstruction (and why it's impossible)

The unique failure mode would be x_j^6 — every degree-3 divisor is x_j³ = v_α.
But x_j^6 in v̇_{x_j³} requires x_j⁴ in the positive part of f_j. The 4-PP
condition forbids this, and the 4-PP condition is **automatic** from the original PP:

```
PP (x_j² ∤ p_j, degree 2)
  →[r²-trick] 4-PP (x_j⁴ ∤ positive, self-power ≤ 2 < 4, automatic)
  →[cubing]   NAP (x_j⁶ impossible → all monomials have valid splits)
```

### The CF'24 running example ("first matched graph")

Starting from x' = x² - x + 1/9, the pipeline produces:
- 4 base variables: (r, u, z₀₁, z₁₁) after λ-trick + r²-trick
- 20 cubed variables after lifting

Each of the 20 variables' positive terms was verified to have non-autocatalytic
splits. Three representative cases from Note 14:

| Variable | Positive monomial | Dangerous split | Valid split |
|----------|-------------------|-----------------|-------------|
| v₁ = r³ | r⁴uz₀₁ | r³·ruz₀₁ (autocatalytic) | r²u · r²z₀₁ = v₂·v₃ |
| v₁₁ = u³ | r²u³z₀₁ | u³·r²z₀₁ (autocatalytic) | u²z₀₁ · r²u = v₁₂·v₂ |
| v₂₀ = z₁₁³ | r²z₀₁z₁₁³ | z₁₁³·r²z₀₁ (autocatalytic) | z₀₁z₁₁² · r²z₁₁ = v₁₉·v₄ |

In each case, the key move is **redistributing** the concentrated exponent across
both factors: 4=2+2 for r, 3=2+1 for z₁₁, etc.

---

## 4. Connection to LPP Stage 4 (TPP → PLPP)

The same demand/supply framework applies to Stage 4 of the LPP pipeline
(Theorem 16 / Construction 1 in [LPP]):

**Setting:** Given a PP-implementable field with balance equation
x'_r = f_r(x) - 2x_r(Σx_k), where f_r is a quadratic form with
non-negative coefficients c_{r,i,j}.

**Matching:** Pair positive coefficient terms across different equations.
For each monomial x_i·x_j, match the positive contributions (from f_r)
with negative contributions (from -2x_r·Σx_k), forming 2-in-2-out reactions.

The CF'24 paper (Huang-Migunov) formalizes this as a product distribution:
α_{i,j,k,l} = c_{k,i,j} · c_{l,i,j} / 4, automatically satisfying marginal
constraints. Conservation is guaranteed by Σ_r c_{r,i,j} = 2.

---

## 5. Connection to Note 12 Flow Network and Note 25 Cross-Square

### Note 12: General flow network feasibility

Generalizes the per-monomial bipartite graph to arbitrary variable systems:
- For the BD (Balancing Dilation) construction, variables are lifted to
  v_i = x_i, β = r², γ_i = r²x_i, δ_{i,j} = rx_ix_j
- Each monomial's decomposition into z-products is tabulated
- C1 (bimolecular) and C3 (negative must contain variable) constrain demand
- Multiple supply options exist for most monomials; some are "forced"

### Note 25: Cross-square theorem (necessity)

The cross-square condition is a necessary condition for flow-network feasibility:
- For each species x_i, every monomial in f_i that does NOT involve x_i
  must have non-negative coefficient
- Proved via degree argument: b_{x_i,x_i} = ½x_i² has x_i-degree ≥ 2,
  so any product b_{x_i,x_i}·z_α has x_i-degree ≥ 2, but a monomial with
  x_i-degree 1 can't be matched via C3

---

## 6. The Bournez Gap and the Balancing Dilation

Bournez-Fraigniaud-Koegler (MFCS 2012) proved the same algebraic↔LPP
characterization, but via a **direct construction**: given P(X) ∈ ℚ[X] with
P(ν) = 0, construct transition rules whose balance equation has ν as an
equilibrium. Their construction has a **structural gap** identified by Xiang:

**The gap:** They set dx_δ = -∑ dx_i for conservation. This breaks
CRN-implementability. The negative constant term -εa₀ (from dx₁) appears
in dx_δ and cannot be decomposed as p_δ(x) - q_δ(x)·x_δ with p_δ ≥ 0
on the non-negative orthant. Without CRN-implementability, the system
cannot be realized as a population protocol.

**Why the balancing dilation fixes this:** Instead of the "lazy" conservation
dx₀ = -∑ f_j, the balancing dilation multiplies by x₀:

```
dx₀ = -(∑ f_j) · x₀
dx_{j+1} = f_j · x₀
```

If the inner field is CRN-implementable (f_j = p_j - q_j·x_j), then:
- prod₀ = (∑ q_j·x_{j+1}) · x₀ ≥ 0
- degr₀ = ∑ p_j ≥ 0
- dx₀ = prod₀ - degr₀ · x₀ ✓ (CRN form preserved!)

The multiplication by x₀ is not merely a time rescaling — it transforms the
conservation equation into a form compatible with CRN algebra. This is the
core insight of the [LPP] Stage 2 construction.

The CF'24 example (x' = x² - x + 1/9) was specifically constructed as a
counterexample to Bournez's method. Running their algorithm on this example
demonstrates the CRN-implementability failure.

---

## 7. Key Takeaways for Lean Formalization

1. **The matching framework is algebraic, not analytic.** It operates on polynomial
   coefficients, not on ODE solutions. This means it can be formalized without
   heavy analysis — it's combinatorics on monomials.

2. **Per-monomial decomposition is local, feasibility is global.** Each monomial's
   bipartite graph can be analyzed independently, but the GLOBAL assignment must be
   consistent (choosing a split for one monomial may constrain options elsewhere).

3. **For the cubing construction, local feasibility implies global feasibility.**
   The NAP Splitting Feasibility theorem (Note 14, Theorem 1) shows every monomial
   always has at least one valid split — so the global matching trivially exists.

4. **For general constructions (BD, LPP), Hall's condition or LP is needed.**
   Note 12's flow network framework + Note 25's cross-square theorem provide
   necessary conditions. Sufficiency may require computational verification
   (the nap_feasibility LP scripts in DNA30_BD/working_notes/scripts/).

5. **The SynPPBalance structure in Ripple already captures the right abstraction.**
   It represents the syntactic coefficients c_{r,i,j} needed for matching.
   The product distribution (Stage 4) is the specific matching algorithm used
   in [LPP], producing exact PLPP transition probabilities.
