# Structural results related to the Fair Traversal Conjecture

## Status and scope

This note gives complete ordinary mathematical proofs of several partial results related to the Fair Traversal Conjecture. It does **not** prove or disprove the conjecture for all finite connected vertex-transitive graphs. No novelty claim is made, and these arguments have not been formalized in Lean in this note.

The main positive results proved here are:

1. An exact reduction to the convex hull of Hamilton-path edge-orbit counts, together with an exact separating-weight criterion.
2. An equivalence with equality in the elementary density lower bound for fractional linear arboricity.
3. Closure of the fair traversal property under Cartesian products of regular graphs.
4. The fair traversal property for every connected Cayley graph of a finite abelian group, and more generally for the normal-subgroup Cayley graphs specified in Section 7. In particular, the result applies to every finite Dedekind group, meaning a group in which every subgroup is normal.

The unresolved steps in possible approaches to the full conjecture are kept separate in Section 8.

## 1. Definitions and a rationality lemma

All graphs in this note are finite, simple, and undirected. A Hamilton path visits every vertex exactly once; it has exactly one fewer edge than the graph has vertices. We identify a path with its edge set when discussing incidence vectors. Choosing an orientation for a path does not change its incidence vector.

Let a graph have vertex set \(V\), edge set \(E\), \(N=|V|\ge 2\), and \(M=|E|>0\). Write \(\mathcal H(G)\) for its finite set of Hamilton paths.

We say that \(G\) is **fair** if there are positive integers \(r,k\) and a list of Hamilton paths \(P_1,\ldots,P_r\), with repetition allowed, such that every edge belongs to exactly \(k\) paths in the list. Necessarily

\[
r(N-1)=kM.
\]

Consequently, fairness is equivalent to a finitely supported rational probability distribution on Hamilton paths for which every edge has inclusion probability

\[
\lambda_G=\frac{N-1}{M}.
\tag{1}
\]

In one direction, choose uniformly from a fair list. Conversely, clear the denominators of the rational probabilities and of \(\lambda_G\). The resulting list has a positive number of paths, and each edge occurs the same positive integer number of times.

Thus fairness is equivalent to

\[
\lambda_G\mathbf 1_E\in
\operatorname{conv}\{\mathbf 1_{E(P)}:P\in\mathcal H(G)\}.
\tag{2}
\]

The use of a real convex hull in (2) causes no rationality gap, by the following elementary lemma.

### Lemma 1.1: rational convex combinations

If \(v_1,\ldots,v_s\in\mathbb Q^a\), \(q\in\mathbb Q^a\), and \(q\) is a real convex combination of the \(v_i\), then it is a rational convex combination of them.

**Proof.** Among all representations of \(q\) as a convex combination, choose one with the fewest positive coefficients. The vectors in its support are affinely independent: otherwise there is a nonzero affine dependence, and moving the coefficient vector in one direction along that dependence until a coefficient first reaches zero produces a smaller support while retaining nonnegativity, total mass one, and the same represented vector.

For an affinely independent support, the equations

\[
\sum_i p_i v_i=q,\qquad \sum_i p_i=1
\]

have a unique solution for the supported coefficients. Their matrix and right-hand side are rational, so Gaussian elimination shows that the solution is rational. These coefficients are the original nonnegative ones. \(\square\)

This lemma will be used repeatedly to pass from finite-dimensional convex geometry to actual finite multisets of paths.

## 2. Exact reduction to edge-orbit counts

Let \(G\) be connected and vertex-transitive, with \(N\ge2\). Choose **any** vertex-transitive subgroup \(\mathcal A\le\operatorname{Aut}(G)\); it need not be the full automorphism group. The graph is regular; write its degree as \(d\ge1\), so that \(M=Nd/2\). Let

\[
E=E_1\sqcup\cdots\sqcup E_s
\]

be the orbits of \(\mathcal A\) on unordered edges. For each \(j\), the number \(d_j\) of edges of \(E_j\) incident to a vertex is independent of the vertex. Indeed, an element of \(\mathcal A\) taking one vertex to another preserves each \(\mathcal A\)-edge orbit. Counting incidences gives

\[
|E_j|=\frac{Nd_j}{2},\qquad \sum_{j=1}^s d_j=d.
\]

For a Hamilton path \(P\), define its orbit-count vector by

\[
t(P)=(t_1(P),\ldots,t_s(P)),\qquad
t_j(P)=|E(P)\cap E_j|.
\]

Every such vector has total coordinate sum \(N-1\). Define the rational target vector

\[
q_j=\frac{(N-1)|E_j|}{M}
=\frac{(N-1)d_j}{d}.
\tag{3}
\]

### Theorem 2.1: edge-orbit criterion

The graph \(G\) is fair if and only if

\[
q\in\operatorname{conv}\{t(P):P\in\mathcal H(G)\}.
\tag{4}
\]

**Proof.** A fair path distribution has expected count \(\lambda_G|E_j|=q_j\) in each orbit, proving the forward implication.

Conversely, suppose (4) holds. Lemma 1.1 supplies a rational probability distribution on Hamilton paths with expected orbit counts \(q_j\). Independently choose a uniformly random element \(\sigma\) of the finite group \(\mathcal A\), and replace the chosen path \(P\) by \(\sigma(P)\).

The resulting probability distribution is invariant under \(\mathcal A\). Therefore all edges in \(E_j\) have the same inclusion probability. Their expected total count remains \(q_j\), so that common probability is

\[
\frac{q_j}{|E_j|}=\frac{N-1}{M}=\lambda_G.
\]

All probabilities remain rational because this is averaging over a finite group. Clearing denominators gives a fair finite multiset. \(\square\)

Thus a certificate may use an explicitly supplied transitive group of graph automorphisms and its edge orbits. It need not identify or prove completeness of the full automorphism group. The supplied transformations must actually preserve adjacency, and their generated action must be vertex-transitive.

**Consequence.** An edge-transitive graph that has a Hamilton path is fair: there is only one orbit, and every path has the required count \(N-1\). For a graph with several edge orbits, averaging one path only balances edges within their own orbits; it does not automatically produce (3) across the different orbits.

## 3. Exact separating-weight criterion

The convex-hull criterion has a useful dual form. Here an edge weight is simply a real number assigned to each unordered edge; negative weights are allowed. In this section, invariance means invariance under the chosen vertex-transitive group \(\mathcal A\). One may in particular choose \(\mathcal A=\operatorname{Aut}(G)\) to obtain the full-automorphism version.

### Theorem 3.1: separating weights

For the graph in Section 2, the following are equivalent:

1. \(G\) is not fair.
2. There is an \(\mathcal A\)-invariant rational edge weighting \(w:E\to\mathbb Q\) such that
   \[
   \sum_{e\in E}w(e)=0
   \tag{5}
   \]
   and
   \[
   \sum_{e\in E(P)}w(e)>0
   \quad\text{for every Hamilton path }P.
   \tag{6}
   \]
3. There is an \(\mathcal A\)-invariant integer edge weighting with total weight zero and with every Hamilton path having weight at least one.

Equivalently, \(G\) is fair if and only if every \(\mathcal A\)-invariant rational edge weighting of total weight zero admits a Hamilton path of weight at most zero.

**Proof.** First assume that Hamilton paths exist. If the uniform incidence vector in (2) is outside their convex hull, strict separation from that finite, hence compact, convex hull gives real weights \(a(e)\) such that

\[
\sum_{e\in E(P)}a(e)>
\lambda_G\sum_{e\in E}a(e)
\quad\text{for every }P.
\]

Subtract the constant

\[
\bar a=\frac1M\sum_{e\in E}a(e)
\]

from every edge weight. Since every Hamilton path has \(N-1\) edges and \(\lambda_G M=N-1\), the new weights have total zero and give every Hamilton path strictly positive weight.

Average those weights over \(\mathcal A\). Total weight zero is preserved. For any fixed Hamilton path, its weight under the averaged weighting is an average of the positive weights of its images under \(\mathcal A\), and is therefore positive. This yields an invariant real weighting satisfying (5)–(6).

Such invariant weights are specified by one value \(c_j\) on each orbit, and the total-zero condition is the rational linear equation

\[
\sum_j |E_j|c_j=0.
\tag{7}
\]

Rational points are dense in the real solution space of this equation: solve for one coordinate using the others. There are only finitely many Hamilton paths, and all their strict inequalities have a positive margin. Consequently an adequately close rational point still satisfies all of them. Clearing denominators gives integer weights; a strictly positive integer path weight is at least one.

Conversely, a fair path distribution would give expected path weight

\[
\sum_{e\in E}\lambda_Gw(e)=0,
\]

which is impossible if every path has strictly positive weight.

If the graph has no Hamilton path, it is not fair, and the zero weighting satisfies the universally quantified conditions (6), or their integer version, vacuously. Thus the equivalences remain true in this case as well. \(\square\)

In orbit coordinates, a certificate has the particularly small description

\[
\sum_j |E_j|c_j=0,
\qquad
\sum_j c_jt_j(P)\ge1\quad\text{for every Hamilton path }P.
\tag{8}
\]

For an invariant weighting satisfying (5), the incident weight sum at each vertex is also zero. The incident sum is constant by vertex-transitivity, and summing it over vertices gives twice the total edge weight. Equivalently,

\[
\sum_j d_jc_j=0.
\]

This is a necessary feature of an invariant separating certificate. It does not, on its own, rule such a certificate out.

## 4. Fractional linear arboricity

This section requires only \(N\ge2\) and \(M>0\), not regularity or vertex-transitivity.

A **linear forest** is a spanning subgraph whose components are paths, allowing isolated vertices. Equivalently, its edge set is acyclic and its maximum degree is at most two. Let \(\mathcal L(G)\) be the finite family of all such edge sets.

Define the fractional linear arboricity by the finite linear program

\[
\operatorname{fla}(G)=
\min\left\{
\sum_{F\in\mathcal L(G)}x_F:
x_F\ge0,\quad
\sum_{F\ni e}x_F\ge1\text{ for every }e\in E
\right\}.
\tag{9}
\]

The program is feasible because single edges are linear forests. Its minimum is attained; for example, intersect its feasible region with the objective sublevel set given by that finite single-edge cover.

Every linear forest has at most \(N-1\) edges. Summing the covering inequalities therefore gives

\[
M\le\sum_F x_F|F|\le(N-1)\sum_Fx_F,
\]

and hence

\[
\operatorname{fla}(G)\ge\frac{M}{N-1}.
\tag{10}
\]

### Theorem 4.1: equality characterizes fairness

For \(N\ge2\) and \(M>0\),

\[
G\text{ is fair}
\quad\Longleftrightarrow\quad
\operatorname{fla}(G)=\frac{M}{N-1}.
\tag{11}
\]

**Proof.** Given a fair multiset with \(r\) paths and edge multiplicity \(k\), assign each Hamilton path its multiset multiplicity divided by \(k\). This is an exact fractional edge cover by linear forests, of total weight

\[
\frac rk=\frac{M}{N-1}.
\]

Together with (10), this proves equality.

Conversely, let an optimal solution in (9) attain the lower bound. Both inequalities in

\[
M\le\sum_Fx_F|F|\le(N-1)\sum_Fx_F=M
\]

must be equalities. Since the coverage excess at each edge is nonnegative and their sum is zero, every edge is covered with total weight exactly one. Since every term \(x_F((N-1)-|F|)\) is nonnegative and their sum is zero, every positive-weight forest has \(N-1\) edges.

A forest on \(N\) vertices with \(N-1\) edges is connected. If it also has maximum degree at most two, it is a Hamilton path. Thus the optimal weights are supported entirely on Hamilton paths. Normalize these weights by their total \(M/(N-1)\). The resulting probability distribution has edge marginal \((N-1)/M\), so its uniform incidence vector lies in the finite rational convex hull (2). Lemma 1.1 and denominator clearing give a fair multiset. \(\square\)

The assumption \(M>0\) avoids an irrelevant degeneracy: for an edgeless graph on at least two vertices, the numerical lower bound and optimum are both zero although no Hamilton path exists.

## 5. Endpoint probabilities in regular fair graphs

Let \(G\) be \(d\)-regular on \(n\ge2\) vertices and fair. Necessarily \(d\ge1\). Choose a path from a rational fair probability distribution.

Every vertex has degree one in the selected path if it is an endpoint, and degree two otherwise. Therefore

\[
\mathbb E[\deg_P(v)]
=2-\mathbb P(v\text{ is an endpoint}).
\]

On the other hand, the common edge marginal is

\[
\lambda_G=\frac{2(n-1)}{nd},
\]

so the expected degree at each vertex is \(d\lambda_G=2(n-1)/n\). Hence

\[
\mathbb P(v\text{ is an endpoint})=\frac2n.
\tag{12}
\]

Now orient every chosen path by an independent fair coin. Each of its two orientations has half the original probability. Then

\[
\mathbb P(v\text{ is the start})
=\mathbb P(v\text{ is the end})
=\frac1n.
\tag{13}
\]

This argument uses regularity and fairness, but no automorphisms. It is the endpoint fact needed in the Cartesian product theorem.

## 6. Cartesian product closure, with explicit mixing weights

Let \(G,H\) be regular fair graphs with

\[
|V(G)|=n\ge2,\quad |V(H)|=m\ge2,
\]

and respective degrees \(a,b\). Thus

\[
1\le a\le n-1,\qquad 1\le b\le m-1.
\]

The Cartesian product \(G\square H\) has vertex set \(V(G)\times V(H)\). Its horizontal edges change only the \(G\)-coordinate along a \(G\)-edge; its vertical edges change only the \(H\)-coordinate along an \(H\)-edge. It is \((a+b)\)-regular on \(nm\) vertices.

Set

\[
A=\frac{2(n-1)}{na},\qquad
B=\frac{2(m-1)}{mb}.
\tag{14}
\]

Choose independently from rational fair path distributions in the two factors and randomize orientations as in Section 5.

### First family of snakes

Let the selected oriented paths have vertex lists

\[
g_0,\ldots,g_{n-1},\qquad h_0,\ldots,h_{m-1}.
\]

Traverse the entire \(G\)-path in the layer at \(h_0\), traverse it in reverse in the layer at \(h_1\), and continue alternating. Join consecutive layers by the \(H\)-edge \(h_jh_{j+1}\) at the current \(G\)-endpoint.

This is a Hamilton path of the product: it visits each layer once, visits every vertex of that layer once, and uses a legitimate product edge between successive layers. For any fixed horizontal edge, its probability of inclusion is \(A\), because the selected \(G\)-path is used in every layer.

For a fixed vertical edge \(((g,h),(g,h'))\), the selected \(H\)-path must contain \(hh'\), an event of probability \(B\). Conditional on that path and on the position of \(hh'\), the crossing uses either the start or the end of the independently selected oriented \(G\)-path. Either endpoint is uniform by (13). Thus the vertical marginal is \(B/n\).

The marginals of this first family are therefore

\[
(\text{horizontal},\text{vertical})=(A,B/n).
\tag{15}
\]

### Second family of snakes

Exchange the roles of the factors: traverse an entire \(H\)-path in each successive \(G\)-layer, reversing alternate copies. The marginals are

\[
(\text{horizontal},\text{vertical})=(A/m,B).
\tag{16}
\]

### Mixing the two families

Choose the first family with probability

\[
\begin{aligned}
\alpha
&=\frac{B-A/m}{A(1-1/m)+B(1-1/n)}\\
&=\frac{na(m-1)-b(n-1)}{(n-1)(m-1)(a+b)},
\end{aligned}
\tag{17}
\]

and choose the second family with probability \(1-\alpha\).

This is a rational number strictly between zero and one. The denominator is positive, and the numerator satisfies

\[
na(m-1)-b(n-1)
\ge(m-1)\bigl(na-(n-1)\bigr)>0.
\]

The denominator minus the numerator is

\[
mb(n-1)-a(m-1)
\ge(n-1)\bigl(mb-(m-1)\bigr)>0.
\]

By the first formula in (17), the mixed horizontal and vertical marginals agree:

\[
\alpha A+(1-\alpha)\frac Am
=\alpha\frac Bn+(1-\alpha)B.
\]

Every sampled object is a Hamilton path with \(nm-1\) edges. The common edge marginal must consequently be

\[
\frac{nm-1}{|E(G\square H)|}
=\frac{2(nm-1)}{nm(a+b)}.
\tag{18}
\]

All factor probabilities, orientation probabilities, and the mixing probability are rational. Clearing their denominators produces an actual finite fair multiset.

### Theorem 6.1: Cartesian product closure

The Cartesian product of two regular fair graphs, each having at least two vertices, is fair. In particular, a Cartesian product of two connected vertex-transitive graphs already known to be fair is fair.

A singleton factor merely gives an isomorphic copy of the other graph and can be treated separately; no formula involving its zero degree is required.

## 7. Cayley graphs with normal generated subgroups

The next theorem proves fairness for an infinite class. Its proof uses ordered subgroup constructions and elementary separation of finite convex hulls; it does not require a general theorem about polymatroids.

Let \(\Gamma\) be a finite group of order \(n\ge2\). Let \(T\subseteq\Gamma\setminus\{1\}\) be inverse-closed and generate \(\Gamma\). We use the right-generator convention for its undirected Cayley graph:

\[
x\sim xs\quad(s\in T).
\]

Partition \(T\) into inverse pairs, treating an involution as a pair of size one. Let the index set of those parts be \(I\), choose a representative \(g_i\) for each part, and put

\[
d_i=|\{g_i,g_i^{-1}\}|\in\{1,2\},\qquad
d=|T|=\sum_{i\in I}d_i.
\]

The edges of type \(i\) are the unordered edges \(\{x,xg_i\}\). There are exactly \(nd_i/2\) such edges. Left translations act transitively on each type, and preserve every type.

For \(S\subseteq I\), write

\[
H(S)=\langle g_i:i\in S\rangle,
\qquad h(S)=|H(S)|.
\]

Assume the following condition:

> For every \(S\subseteq I\), the subgroup \(H(S)\) is normal in \(\Gamma\).

This holds for every abelian group, and for every Dedekind group. More generally it is only a condition on the subgroups generated by the chosen inverse-pair connection set.

### Lemma 7.1: extension across a cyclic quotient

Suppose \(H\trianglelefteq K=\langle H,g\rangle\), and suppose a Hamilton path \(P\) in the Cayley graph on \(H\), using some previously allowed generators, starts at \(1\) and ends at \(u\in H\). Let \(k=[K:H]\). Then the Cayley graph on \(K\) has a Hamilton path starting at \(1\) that uses:

- \(k\) times the number of edges of each previously used generator type;
- exactly \(k-1\) edges of the new generator type \(\{g,g^{-1}\}\).

Here the new type is distinct from the previously indexed types, although \(g\) may already belong to their generated subgroup. If \(k=1\), the construction simply retains \(P\) and adds zero new edges.

**Proof.** The quotient \(K/H\) is cyclic, generated by \(gH\), of order \(k\). For \(0\le j<k\), set

\[
z_j=(ug)^j.
\]

The left-translated path \(z_jP\) starts at \(z_j\), ends at \(z_ju\), and covers exactly the left coset \(z_jH\). In the quotient,

\[
z_jH=(gH)^j,
\]

so these \(k\) cosets are pairwise disjoint and exhaust \(K\).

Concatenate the paths \(z_0P,z_1P,\ldots,z_{k-1}P\). Between successive paths use the edge

\[
z_ju\longrightarrow z_jug=z_{j+1}.
\]

It is an allowed edge of type \(\{g,g^{-1}\}\). Left translation preserves all previously allowed generator types. The concatenation is therefore a Hamilton path with exactly the asserted counts. \(\square\)

### Lemma 7.2: count vectors from all generator orderings

Take any ordering \(\pi_1,\ldots,\pi_s\) of \(I\), with prefix sets

\[
S_j=\{\pi_1,\ldots,\pi_j\},\quad S_0=\varnothing,
\qquad h_j=h(S_j).
\]

There is a Hamilton path of the Cayley graph whose number of edges of type \(\pi_j\) is

\[
c^{\pi}_{\pi_j}=\frac{n}{h_{j-1}}-\frac{n}{h_j}.
\tag{19}
\]

In particular, its count in the first \(j\) types is

\[
c^{\pi}(S_j)=n-\frac{n}{h_j}.
\tag{20}
\]

**Proof.** Start with the one-vertex path in \(H(S_0)=\{1\}\). Apply Lemma 7.1 successively to

\[
H(S_{j-1})\trianglelefteq H(S_j)
=\langle H(S_{j-1}),g_{\pi_j}\rangle.
\]

At stage \(j\), the index is \(k_j=h_j/h_{j-1}\). The new type occurs \(k_j-1\) times. Every subsequent stage multiplies that count by its own index, whose product is \(n/h_j\). The final count is

\[
(k_j-1)\frac{n}{h_j}
=\frac{n}{h_{j-1}}-\frac{n}{h_j}.
\]

The prefix formula telescopes. \(\square\)

The desired fair expected count of type \(i\) is

\[
q_i=\frac{(n-1)d_i}{d}.
\tag{21}
\]

Its total is \(q(I)=n-1\). Define also

\[
f(S)=n-\frac{n}{h(S)}.
\]

### Lemma 7.3: the target satisfies every subgroup bound

For every \(S\subseteq I\),

\[
q(S)\le f(S).
\tag{22}
\]

**Proof.** Put \(d_S=\sum_{i\in S}d_i\) and \(h=h(S)\). All the \(d_S\) distinct connection elements indexed by \(S\) belong to \(H(S)\setminus\{1\}\), so

\[
d_S\le h-1.
\]

If \(h=n\), then \(q(S)\le q(I)=n-1=f(S)\).

If \(h<n\), some connection element lies outside \(H(S)\), since all the connection elements together generate \(\Gamma\). Thus \(d\ge d_S+1\). Consequently

\[
\begin{aligned}
q(S)
&=\frac{(n-1)d_S}{d}\\
&\le\frac{(n-1)d_S}{d_S+1}\\
&\le\frac{(n-1)(h-1)}{h}\\
&\le n\left(1-\frac1h\right)=f(S).
\end{aligned}
\]

This includes \(S=\varnothing\), where \(d_S=0\), \(h=1\), and both sides are zero. \(\square\)

### Theorem 7.4: fair traversal for normal-subgroup Cayley graphs

Under the stated normality condition, the Cayley graph is fair. In particular, every connected Cayley graph of a finite abelian group is fair, and so is every connected Cayley graph of a finite Dedekind group.

**Proof.** We first show that the rational target vector \(q\) lies in the convex hull of the finitely many integer count vectors \(c^{\pi}\) from (19).

Take arbitrary real weights \(w_i\) on the generator types. Choose an ordering \(\pi\) such that

\[
w_{\pi_1}\ge\cdots\ge w_{\pi_s}.
\]

Both \(c^{\pi}\) and \(q\) have total sum \(n-1\). By summation by parts,

\[
\begin{aligned}
w\cdot(c^{\pi}-q)
&=\sum_{j=1}^{s-1}
\bigl(w_{\pi_j}-w_{\pi_{j+1}}\bigr)
\bigl(c^{\pi}(S_j)-q(S_j)\bigr)\\
&=\sum_{j=1}^{s-1}
\bigl(w_{\pi_j}-w_{\pi_{j+1}}\bigr)
\bigl(f(S_j)-q(S_j)\bigr)\\
&\ge0,
\end{aligned}
\tag{23}
\]

where the last inequality follows from the ordering and Lemma 7.3. For a singleton index set, the sum is empty and the same equality holds.

Thus, for every linear functional \(w\), at least one constructed Hamilton-path count vector satisfies

\[
w\cdot c^{\pi}\ge w\cdot q.
\]

If \(q\) were outside their finite convex hull, strict separation would give a functional with \(w\cdot q>w\cdot c^{\pi}\) for every \(\pi\), a contradiction. Hence \(q\) lies in that convex hull.

Lemma 1.1 supplies a rational probability distribution on the constructed paths with expected type counts \(q_i\). Independently choose a uniformly random left translation by an element of \(\Gamma\). Translation is an automorphism of the right-generator Cayley graph, and it acts transitively on the \(nd_i/2\) edges of type \(i\). Each such edge therefore has inclusion probability

\[
\frac{q_i}{nd_i/2}
=\frac{2(n-1)}{nd},
\]

which is independent of \(i\). This is precisely the common marginal required by (1). All probabilities are rational, so denominator clearing completes the proof. \(\square\)

**Why this does not cover all Cayley graphs.** The coset extension lemma depends on normality: it uses the cyclic group quotient \(\langle H,g\rangle/H\), and the equalities \((ug)^jH=(gH)^j\). For an arbitrary nonnormal prefix subgroup, those quotient expressions and the resulting distinct-coset enumeration are unavailable. The proof above supplies no replacement for that step.

**Optional structural observation.** Under the normality condition, \(f(S)=n-n/h(S)\) is also submodular. Indeed, let \(A=H(S)\), \(B=H(T)\), put \(a=|A|\), \(b=|B|\), \(c=|A\cap B|\), and \(s=|H(S\cap T)|\le c\). Normality makes \(AB=H(S\cup T)\) a subgroup of order \(ab/c\). The elementary inequality

\[
\frac1a+\frac1b\le\frac1c+\frac{c}{ab}
\]

is equivalent to \((a-c)(b-c)\ge0\). Replacing \(1/c\) by the larger \(1/s\) proves the submodular inequality for \(f\). This observation is not used in the proof of Theorem 7.4; (23) gives the required convex-hull inclusion directly.

### 7.5. General invariant edge partitions and the rank bound

There is a useful exact comparison with an arbitrary connected vertex-transitive graph. Let a vertex-transitive automorphism group have edge orbits \(E_i\), so that \(E=\bigsqcup_{i\in I}E_i\), and let \(d_i\) be the common degree contributed by class \(i\). For \(S\subseteq I\), form the spanning subgraph \(G_S\) with edge set \(\bigcup_{i\in S}E_i\).

The acting group remains vertex-transitive on \(G_S\), so its connected components all have the same size \(h(S)\). Its number of components is \(N/h(S)\), and the maximum number of edges in a forest contained in \(G_S\) is

\[
f(S)=N-\frac{N}{h(S)}.
\tag{25}
\]

This is the graphic matroid rank of the selected union of edge classes. If \(d_S=\sum_{i\in S}d_i\), then \(d_S\le h(S)-1\). If \(h(S)<N\), connectedness of the full graph implies that at least one incident edge type is omitted, so \(d\ge d_S+1\). Exactly the inequalities in Lemma 7.3 therefore show that the fair target

\[
q_i=\frac{(N-1)d_i}{d}
\]

satisfies \(q(S)\le f(S)\) for every \(S\), and \(q(I)=f(I)=N-1\).

For any ordering of the classes, there is a **spanning tree** whose class-count vector attains equality in all the corresponding prefix bounds. Construct a forest greedily: at each stage add as many edges from the next class as possible without creating a cycle. After processing a prefix, the current forest connects each component of the prefix subgraph, since otherwise an edge joining two of its forest components could still be added. Its size is therefore the rank (25). At the final stage the forest is a spanning tree.

The sorted-weight argument (23) now proves that \(q\) lies in the convex hull of these spanning-tree count vectors. Averaging over the acting group then gives a distribution on spanning trees with uniform edge marginals \((N-1)/M\). This establishes the relevant spanning-tree relaxation directly, without a separate edge-connectivity theorem.

The normal-subgroup Cayley construction proves more: its class-count vectors attaining all prefix ranks are realized by **Hamilton paths**. That additional realization is exactly what allows the same sorted-weight proof to reach the Hamilton-path convex hull in Theorem 7.4. Requiring every ordering to admit such a prefix-saturating path is a strictly stronger condition than fairness: fairness alone only asks for one target vector to belong to the path-count convex hull. The next example shows that the stronger condition actually fails for a connected vertex-transitive graph that is fair.

### 7.6. A vertex-transitive obstruction to extending the greedy construction

Define the Petersen graph \(B\) on the ten two-element subsets of \(\{1,2,3,4,5\}\), with two vertices adjacent when the subsets are disjoint. Each vertex has three neighbors. The graph is connected: two distinct intersecting two-element subsets have the two-element complement of their union as a common neighbor, while disjoint subsets are adjacent.

Expand each vertex into a triangle. Precisely, the expanded graph \(X\) has vertices the thirty ordered adjacent pairs \((u,v)\) of \(B\). For each fixed \(u\), join its three darts \((u,v)\) into a triangle. Also join \((u,v)\) to \((v,u)\). These latter edges form a perfect matching \(M\) of size fifteen. The expanded graph is connected and cubic.

Every permutation of \(\{1,2,3,4,5\}\) induces an automorphism of \(X\). These permutations act transitively on ordered pairs of disjoint two-element subsets, hence transitively on the vertices of \(X\). Thus \(X\) is vertex-transitive, established directly from its definition.

The graphic rank of the matching is

\[
r(M)=15,
\]

since its fifteen edges form a forest. Nevertheless, **every Hamilton path of \(X\) uses at most eleven edges of \(M\)**. For a triangle containing neither endpoint of the path, the sum of the three path-degrees is six. If \(a\) internal triangle edges and \(b\) matching edges are used there, then \(2a+b=6\), with \(0\le b\le3\). Hence \(b\) is either zero or two. Zero would require all three internal triangle edges, creating a cycle in the path, so \(b=2\).

At most two triangles contain path endpoints, and each has at most three matching incidences. Thus the total matching incidence count is at most

\[
8\cdot2+2\cdot3=22.
\]

This upper bound also holds if both endpoints are in the same triangle. Every used matching edge contributes two incidences, proving the bound of eleven. Consequently no Hamilton path attains the rank bound for the prefix consisting only of \(M\). The sufficient greedy-prefix condition fails in this vertex-transitive graph.

For completeness, \(X\) is nevertheless fair. Abbreviate the subset \(\{i,j\}\) by \(ij\). The base graph has the Hamilton path

\[
12,34,15,23,45,13,24,35,14,25.
\tag{26}
\]

Replacing each base vertex by a traversal of its entire triangle gives a Hamilton path of \(X\) using nine matching edges. At an intermediate triangle, enter through the incoming base-edge dart, visit the third dart, and leave through the outgoing base-edge dart. At the two end triangles, traverse their three vertices in an order compatible with the one incident base-path edge.

There is also a Hamilton path using ten matching edges. Add the edge \(12\text{--}45\) to (26), obtaining a five-cycle with a tail attached at \(45\). In the expanded graph, start at one of the two cycle darts of the triangle at \(45\); traverse the expanded cycle, returning through its other cycle dart; join that dart to the tail dart by one internal triangle edge; and then follow the expanded tail to its end. Every other triangle is traversed through all three of its vertices. This visits all thirty darts once and uses precisely the ten matching edges corresponding to the cycle and tail.

Under the induced permutation action, the matching edges form one edge orbit and the thirty internal edges form the other. For the internal edges, this follows because the stabilizer of a base vertex permutes its three neighbors arbitrarily. Average each of the two constructed paths over that action, and mix the nine-matching-edge family with probability \(1/3\) and the ten-matching-edge family with probability \(2/3\). The expected matching count is

\[
\frac13\cdot9+\frac23\cdot10=\frac{29}{3},
\]

which is the required target \((30-1)\cdot1/3\). The expected internal count is \(29-29/3=58/3\). The two orbit marginals therefore both equal \(29/45\). Clearing denominators gives a fair finite multiset.

This example distinguishes the failure of the stronger greedy construction from failure of fairness itself. It rules out extending that particular prefix-saturation argument to all vertex-transitive graphs, even if one already knows that the graphs involved have Hamilton paths.

## 8. Separate caveats and unresolved general steps

The results above leave the full vertex-transitive conjecture unresolved. The following distinctions prevent several tempting arguments from being mistaken for a complete proof.

### 8.1 Traceability and endpoint balance do not establish edge balance

Vertex-transitivity allows one to average any Hamilton path over automorphisms. This makes each vertex an endpoint with probability \(2/N\), but only equalizes edge marginals within automorphism edge orbits.

For example, in the triangular prism \(C_3\square K_2\), consider a path that traverses two edges of one triangle, crosses one matching edge, and traverses two edges of the other triangle. Its automorphism average has endpoint probability \(1/3\) at every vertex. Nevertheless, its six triangle edges have marginal \(4/6=2/3\), whereas its three matching edges have marginal \(1/3\). The fair marginal would be \(5/9\).

The prism itself is fair, as Theorem 6.1 also shows. This example concerns only the insufficiency of endpoint balance in a particular distribution, not a counterexample to the conjecture.

### 8.2 Having every edge in some Hamilton path is insufficient

If a vertex-transitive graph is traceable, every edge belongs to some Hamilton path. To see this, move a Hamilton path by an automorphism so that one endpoint is a chosen endpoint \(u\) of the desired edge \(uv\). If the edge is absent from the path, write its oriented vertex order as \(u=x_0,x_1,\ldots,x_{N-1}\), with \(v=x_j\). Then

\[
x_{j-1},x_{j-2},\ldots,x_0,x_j,x_{j+1},\ldots,x_{N-1}
\]

is a Hamilton path containing \(uv\): the operation adds \(x_0x_j\), deletes \(x_{j-1}x_j\), and reverses the first segment. The case \(j=N-1\) is included.

This guarantees positive coverage is possible edge by edge. It does not prove that the uniform target vector belongs to the convex hull of path incidence vectors, which is the simultaneous requirement in (2).

### 8.3 Fractional relaxations need an integer-hull argument

For a \(d\)-regular, \(d\)-edge-connected graph on \(N\) vertices, the uniform vector

\[
x_e=\frac{2(N-1)}{Nd}
\]

satisfies the usual spanning-tree inequalities. In fact, for every nonempty proper vertex subset \(S\),

\[
2|E(S)|=d|S|-|\delta(S)|\le d(|S|-1),
\]

so

\[
x(E(S))\le\frac{N-1}{N}(|S|-1)\le |S|-1,
\]

and \(x(E)=N-1\).

It also satisfies the standard inequalities for twice the matching polytope: its incident sum at a vertex is \(2(N-1)/N\le2\), and its odd-subset inequalities are bounded by the same spanning-tree inequalities (including the total-set equality when \(N\) is odd).

This feasibility in the intersection of two familiar fractional polytopes is not a Hamilton-path decomposition. Integer points in the intersection of the spanning-tree polytope and twice the matching polytope are precisely Hamilton-path incidence vectors: an integer spanning tree with all degrees at most two is a Hamilton path. What is missing is a proof that the specific uniform point lies in the convex hull of these integer points. Intersecting two integral polytopes does not generally preserve integrality.

The distinction between this relaxation and its integer hull is also relevant to the tree-double-matching polytope studied by Karel Devriendt in *Graphs with Nonnegative Resistance Curvature*, Annals of Combinatorics 30 (2026), 415–438; see [the author's arXiv version](https://arxiv.org/html/2410.07756v3), especially Proposition 4.6 and the subsequent polyhedral questions. That paper is background for this caveat, not a proof of the Fair Traversal Conjecture.

### 8.4 Hamiltonian covers do not directly supply base Hamilton paths

A Hamilton cycle in a \(t\)-sheet graph cover projects to a closed walk in which each base vertex is visited \(t\) times. It need not project to a Hamilton cycle, and even extracting a consecutive Hamilton-path segment can fail.

Here is an explicit finite illustration. Label the Petersen graph by outer-cycle vertices \(0,1,2,3,4\), inner vertices \(5,6,7,8,9\), outer edges \(i\sim i+1\pmod5\), spokes \(i\sim i+5\), and inner edges \(i+5\sim(i+2\pmod5)+5\). In its bipartite double cover, the cyclic list

\[
0,1,2,3,4,0,5,7,9,4,3,8,6,9,7,2,1,6,8,5
\tag{24}
\]

lifts to a Hamilton cycle by attaching the coordinate \(j\bmod2\) to the entry in position \(j\), indexed from zero. Every step, including the closing step, projects to an edge. Each base label appears exactly once in each parity, so all twenty lifted vertices are distinct.

Yet every cyclic window of ten entries in (24) repeats a base label. For windows beginning at positions \(0,1,\ldots,19\), respectively, one repeated label is

\[
0,3,3,3,4,7,7,7,6,6,6,6,1,1,1,1,0,0,0,0.
\]

Thus this Hamilton cycle offers no base Hamilton path as a consecutive projected segment. This does not disprove a more sophisticated extraction or rearrangement theorem. Such a theorem would need its own proof; it is not furnished by the covering map.

### 8.5 What remains open in this note

None of the preceding arguments establishes that every connected vertex-transitive graph has a Hamilton path, or that every traceable vertex-transitive graph has the uniform incidence vector in its Hamilton-path convex hull. The positive classes covered in this note may narrow a search for counterexamples or supply components for further constructions, but they do not settle the full problem.

The original problem and its formal statement can be reviewed at [LeftToSolve: Gillibert Fair Traversal](https://lefttosolve.com/p/gillibert-fair-traversal). The source manuscript is [*The Fair Traversal Conjecture*](https://github.com/Gillibert/ConjecturesGillibert/blob/main/fair_traversal_conjecture.tex).
