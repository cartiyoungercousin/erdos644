# Glossary

- **Property (7,2).** Every at most seven members of the family can be pierced by two points ("at most" convention, see `Lean644/Statements.lean`).
- **τ (transversal number).** The fewest points meeting every member.
- **Request game.** A requester names sets of $T$ points. An adversary answers each with a member avoiding that set, which exists whenever $\tau>T$. The requester wins if seven answers have no 2-point cover.
- **Confinement.** Three answers with empty common intersection confine all later play to their union $V$, with $|V|\le 3k$.
- **Units.** Sizes are measured in units of $k$: $t=T/k=\tfrac34+\varepsilon$ and $N=|V|/k$. A co-edge has mass $c=N-1$. The free mass is $\omega=N-1-t$, and $\delta=N-\tfrac74$.
- **Co-edge.** The complement $K=V\setminus B$ of a member $B$ inside $V$.
- **T-covering.** Every $T$-subset of $V$ lies in some co-edge. This is equivalent to $\tau>T$.
- **Good seven.** Seven co-edges covering every pair of $V$. Equivalently, seven members with no 2-point transversal.
- **Co-type.** For a point $x$ and chosen co-edges $K_1,\dots,K_7$, the set $I_x=\{i : x\in K_i\}$. A good seven means the co-types are nonempty and pairwise intersecting.
- **Dump.** The part of an answer not forced by the request; it has mass $\omega$ for a full request.
- **Pencil.** Three Fano lines through a common point. A *pencil triple* is three co-edges with union $V$ and large triple intersection.
- **(Σ).** The three sufficient configurations: a Q′ quadruple, a pencil triple, or a Theorem-T triangle.
- **Core window.** $5t-2<N<3-t$, roughly $1.75k$ to $2.25k$ points. This is the open region.
- **Bottom strip.** $3t-\tfrac12<N\le 5t-2$. Closed by a density argument.
- **Petal side.** $N\ge 3-t$: four or more answers ("petals") with empty common intersection.
- **Pool family.** A family whose co-edges all contain a common set $Y$, its "pool". This is the near-extremal model.
- **Selector, class, head.** In greedy adversary models, a rule picks one of several priority orders (a class) from the request. The head of an order is its first points.
