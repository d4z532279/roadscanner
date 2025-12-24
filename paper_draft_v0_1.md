# Locality Audits, Witness Hashing, and a LocalNOT-to-Monotone Extraction Program for NP Circuit Lower Bounds
*(Draft v0.1 — 2025-12-23 — working notes; not a completed proof)*

## Abstract
We outline a program aiming to separate nonuniform circuit classes for an NP language by combining:
(i) *audit-style* functional identities (existential self-reduction, witness checking, and renaming invariance) to force a **locality** property of any circuit that succeeds on the audited distribution; (ii) a **LocalNOT-to-monotone extraction** step under random vertex restrictions; (iii) a compositional **substitution construction** that reduces a “SAT-filtered clique” language to a monotone threshold on the clique number; and (iv) a **Valiant–Vazirani–style witness hashing** lemma to induce unique-witness instances with noticeable probability.
Several central components remain conjectural, notably the audit soundness theorem converting approximate identities into LocalNOT implementability. We present the scaffold, the proved sub-lemmas, and the remaining keystone statements.

## 1. Preliminaries

### 1.1 Graphs and clique number
For a graph \(G\), let \(\omega(G)\) denote its clique number. The predicate \([\omega(G)\ge T]\) is monotone in the edge set.

### 1.2 Block locality and LocalNOT
Inputs are partitioned into \(B\) blocks. A **LocalNOT** circuit is one in which every NOT gate’s input depends on at most \(r\) blocks (in the block-index metric). (Precise formalization depends on the chosen circuit model.)

### 1.3 Monotone lower bounds
We assume availability of monotone lower bounds for CLIQUE in the relevant regime (e.g., the classical exponential-size monotone circuit lower bounds for CLIQUE). These bounds provide the contradiction target after monotone extraction.

## 2. The NP Language \(L_{mix}\)

### 2.1 Definition
Input:
- A graph \(H\) on vertex set \([B]\) (edge bits \(h_{ij}\)).
- CNF formulas \(\Phi=(\phi_1,\dots,\phi_B)\) over disjoint variable sets.

Fix parameter \(t\). Define:
\[
L_{mix}(H;\Phi)=1 \iff \exists C\subseteq[B], |C|=t: C 	ext{ is a clique in } H \ \wedge\ orall i\in C,\ SAT(\phi_i)=1.
\]
This language is in NP with witness \(C\) plus satisfying assignments for \(\{\phi_i:i\in C\}\).

### 2.2 Hard core embedding
If we fix every \(\phi_i\) to a trivial satisfiable CNF, then \(L_{mix}(H;\Phi)\) reduces to \(\mathrm{CLIQUE}_{B,t}(H)\). Thus CLIQUE is a monotone projection of \(L_{mix}\).

## 3. Substitution Construction and Clique Threshold Encoding

### 3.1 SAT-to-CLIQUE gadget per block
For each block CNF \(\phi_i\), construct a graph gadget \(G_i(\phi_i)\) such that:
- If \(SAT(\phi_i)=1\), then \(\omega(G_i)=k\).
- If \(SAT(\phi_i)=0\), then \(\omega(G_i)\le k-1\).
This is the standard SAT→CLIQUE reduction with uniform clause padding to fix \(k\).

### 3.2 Substitution graph
Define the substitution (lexicographic product) graph:
\[
G = H[G_1,\dots,G_B],
\]
where vertices are the disjoint union of gadget vertices and cross-edges are complete bipartite between gadgets \(G_i,G_j\) iff \((i,j)\in E(H)\).

### 3.3 Threshold equivalence
Let \(T=t\cdot k\). Under the 1-gap promise:
\[
L_{mix}(H;\Phi)=1 \iff \omega(G)\ge T.
\]
Thus \(L_{mix}\) reduces to the monotone predicate \([\omega(G)\ge T]\) on the substitution graph.

## 4. Audits and Locality: What Must Be Proved

### 4.1 Audit family
We consider audits consisting of:
- **Existential self-reduction (SR)** checks: for random input bit \(z\), enforce \(f(I)=f(I[z=0])ee f(I[z=1])\).
- **Witness checking**: if \(f(I)=1\), the circuit must output a verifiable witness.
- **Renaming invariance**: random permutations of block indices do not change the output.

Additionally, we introduce two locality-identities:
- **Star test \(T_{star}\)**: choose a graph \(H_i(S_0)\) whose only \(t\)-clique necessarily includes vertex \(i\).
- **Pair test \(T_{pair}\)**: choose a graph \(H_{i,j}(S_0)\) whose only \(t\)-clique requires both vertices \(i\) and \(j\).

These tests are exact identities for the true language \(L_{mix}\) (perfect completeness).

### 4.2 Keystone conjecture (audit soundness ⇒ LocalNOT)
**Conjecture (K_locality_mix).**  
If a function \(f\) passes the audit family with small error on the audit distribution, then \(f\) is close to a composed form
\[
\widehat F(H,\Phi)=igvee_{C\in\mathcal{K}_t(H)} \ igwedge_{i\in C} y_i(\phi_i),
\]
for some block-local predicates \(y_i\), and hence admits a LocalNOT implementation (negations confined within blocks).

## 5. Proved Module: Local Bits from Star/Pair Tests (Sketch)

### 5.1 Resampling/influence formulation
Formalize \(T_{star}\) as a resampling test: resample a random non-\(i\) block and require invariance of \(f(H_i(S_0),\Phi)\).

### 5.2 Extracting local bits
Define:
\[
y_i(\phi_i)=\mathrm{Maj}_{\Phi_{-i}} f(H_i(S_0),(\phi_i,\Phi_{-i})).
\]
Passing the resampling test implies \(f(H_i(S_0),\Phi)\) is close to \(y_i(\phi_i)\) (a junta-style locality bound).

### 5.3 AND-consistency from \(T_{pair}\)
Passing \(T_{pair}\) implies:
\[
f(H_{i,j}(S_0),\Phi)pprox y_i(\phi_i)\wedge y_j(\phi_j).
\]
This yields a robust “local bit extraction” module.

(See: thoughts_chaos_15.txt.)

## 6. Unique Witness via Valiant–Vazirani Hashing (Explicit)

### 6.1 Hash-filtered language
Augment input by a seed \((m,A,b)\) defining a pairwise-independent hash
\[
h(C)=A\chi(C)\oplus b.
\]
Define:
\[
L_{mix}^{hash}(H,\Phi;m,A,b)=1 \iff \exists C\in W(H,\Phi): h(C)=0^m,
\]
where \(W(H,\Phi)\) is the witness set of size-\(t\) cliques among “good” vertices.

### 6.2 Explicit uniqueness bound
Let \(K=|W|\) and let \(X\) be the number of surviving witnesses under the filter \(h(C)=0^m\).
Using pairwise independence and a second-moment bound, if \(m\) is chosen so that \(2^m\in[K,2K]\), then:
\[
\Pr[X=1]\ge 1/8.
\]
Randomizing \(m\) over a logarithmic range yields unique-survivor probability \(\Omega(1/\log K)\).

(See: thoughts_chaos_18.txt.)

### 6.3 Why this helps
On unique-filter instances, witness checking forces the circuit to “focus” on the unique witness \(C^*\), so acceptance reduces to an AND over the block-local bits of \(C^*\), making LocalNOT implementability substantially easier.

## 7. LocalNOT-to-Monotone Extraction (High-Level)

Given a LocalNOT circuit over block indices, restrict to a random subset \(U\subseteq[B]\).
With high probability, NOT gates whose supports intersect the complement simplify or become constants,
yielding a monotone circuit for the restricted instance.
Fix all block formulas to trivial satisfiable so \(y_i=1\); the restricted function then contains CLIQUE
as a monotone projection. Known monotone lower bounds for CLIQUE yield the contradiction.

## 8. What Remains Open

### 8.1 Main missing theorem
A rigorous **audit soundness** theorem proving that passing SR+renaming+witness+\(T_{star}\)+\(T_{pair}\)
implies LocalNOT implementability for circuits deciding \(L_{mix}^{hash}\).

### 8.2 Quantitative parameter regime
A full parameterization is needed to ensure:
- extraction kills negations with sufficiently high probability,
- the restricted instance still lies in a regime where monotone CLIQUE lower bounds apply,
- overheads remain polynomial.

### 8.3 Scope
This draft is a **program sketch** and does **not** constitute a proof of \(P
e NP\) or any established separation.

## Appendix A. File Map
- thoughts_chaos_15.txt: local-bit extraction via resampling + pair consistency.
- thoughts_chaos_17.txt: VV-style witness hashing concept for unique witnesses.
- thoughts_chaos_18.txt: explicit second-moment uniqueness bounds for pairwise-independent hashing.
