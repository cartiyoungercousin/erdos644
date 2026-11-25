# Literature check for Lemma A0 (notes/PROGRAMME2_A.md)

**Lemma A0.** If every ≤ 3 members (repeats allowed) of a family of sets of size ≤ k share a point, then τ ≤ (k+1)/2.

Status: **[proved in Lean]** as `lemma_A0` in `Lean644/RichFamilies.lean`. No source states it in this form, but it is elementary and sits one step from two published lemmas. It is tight: K_n^(k) with n = ⌈3k/2⌉ − 1 is 3-wise intersecting with τ = n − k + 1 = ⌊(k+1)/2⌋.

## Searched
Web searches on the following, all without an exact hit:
- 3-wise intersecting, transversal or covering number, (k+1)/2;
- r-wise intersecting, covering number, (k−1)/(r−1);
- Frankl, Füredi, Tuza.

## Read (full text extracted from the arXiv PDFs)
1. **D. T. Nagy, B. Patkós, "Triangles in intersecting families", arXiv:2201.02452.**
   - Proposition 2.2: an r-wise intersecting family with τ = t is [(r−2)(t−1)+1]-intersecting.
   - The proof partitions F ∩ F′ into r−2 non-covers.
   - For r = 3 this is exactly the first step of A0: τ = t gives |B₁ ∩ B₂| ≥ t.
   - The paper does not take the second step (every (|B₁| − t + 1)-subset of B₁ is a cover). With only |B₁ ∩ B₂| ≤ k it gets τ ≤ k for r = 3, which is weaker than A0.
   - For the size question, the paper cites Frankl, JCTA 20 (1976), on the maximum size of r-wise intersecting k-uniform families. I did not read that paper.
2. **A. Bishnoi, S. Das, P. Morris, T. Szabó, "Ryser's Conjecture for t-intersecting hypergraphs", arXiv:2001.04132.**
   - §1.2 and Theorem 1.7 give tight cover bounds for k-wise t-intersecting r-uniform hypergraphs, but only **r-partite** ones.
   - The proof of Theorem 1.7 (§2.3) uses the same mechanism as A0. Let U be the intersection of k−1 edges. Every edge meets U in ≥ t points, so U minus any t−1 points is a cover.
   - That is A0's argument with k−1 = 2, t = 1, applied after the first step.
   - §1.2 attributes the study of k-wise intersecting families to Frankl, and later work to Füredi and others.

## Not read
- Frankl–Tokushige survey "Invitation to intersection problems for finite sets": found in the search, but not opened.
- Frankl 1976.
- Tuza's and Gyárfás's papers: no hit specific to covers of 3-wise intersecting families.

## Conclusion
- A0 is folklore-level: Nagy–Patkós Prop. 2.2 (r = 3) plus the "U minus points is a cover" step from Bishnoi–Das–Morris–Szabó.
- No citation states the bound τ ≤ (k+1)/2 for general (non-partite) 3-wise intersecting families. Cite those two papers and keep the self-contained proof.
- Open: is τ ≤ (k−1)/(r−1) + 1 true for r-wise intersecting families, and is it stated anywhere?
  - Not checked, and not found in the literature.
  - The two steps alone give only τ ≤ (k+1)/2 for every r ≥ 3.
