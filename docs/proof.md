# The anchored gadget $[M,2M+6]$ is infeasible (Erdős #197, partial result)

*Partial progress on [Erdős Problem #197](https://www.erdosproblems.com/197). The problem itself remains open, and this note does not solve it.*

## Background

**Problem (Erdős–Graham).** Can $\mathbb N$ be partitioned into two sets, each of which admits an enumeration (a listing of order type $\omega$) with no monotone 3-term arithmetic progression? Call $S\subseteq\mathbb N$ *permutable* if it has such an enumeration.

Davis, Entringer, Graham and Simmons (1977) showed that $\mathbb N$ itself is not permutable. W. Kasel (arXiv:2609.02939, 2026) proved that the dyadic partition fails. His tools are a finite *order gadget* $\mathrm{OG}(M)$ on the block $(M,2M]$ and a toolkit of ladder lemmas (zigzag and flood, his Lemmas 23–26). He conjectured (his Remark 30) that $\mathrm{OG}(M)$ is infeasible for every $M\ge16$. This was proved in Lean in [the-omega-institute/trureturing PR #9626](https://github.com/the-omega-institute/trureturing/pull/9626). In the language of this note (Section 7), $\mathrm{OG}(M)$ is the anchored gadget on the window $[M',2M'+13]$ with $M'=M-14$. The PR's theorem yields: a permutable set containing $v,v+1$ contains only finitely many intervals $[P,2P-v+13]$.

This note proves the same for the shorter window $[M,2M+6]$ (Theorem I). The window in the consequence for permutable sets improves from $2P-v+13$ to $2P-v+6$ (Corollary I). The constant $6$ is optimal for Theorem I as stated, that is, for all $M\ge8$ (Section 6). Both statements are formalized in Lean 4 in this repository.

## 0. Statement and conventions

Fix $M\ge 8$ and $I=[M,2M+6]=\{M,M+1,\dots,2M+6\}$. A linear order $\prec$ on $I$ is *AP-free* if no 3-term arithmetic progression $x<y<z$ of $I$ is monotone in $\prec$: neither $x\prec y\prec z$ nor $z\prec y\prec x$. The eight *anchor constraints* are
$$U(j,a):\qquad 2(M+j)-a\ \prec\ M+j\qquad (j\in\{0,1,2,3\},\ a\in\{0,1\}).$$
They are what an enumeration of a permutable set forces on $I$ when $0$ and $1$ are listed before every element of $I$: if $p\in\{0,1\}$ comes before $w$ and $2w-p$ is also listed, then $2w-p$ must come before $w$ (otherwise $p,w,2w-p$ is monotone). For $w\in I$ and $p\in\{0,1\}$, the point $2w-p$ lies in $I\setminus\{w\}$ exactly when $w\in\{M,\dots,M+3\}$.

**Theorem I.** For every $M\ge 8$ there is no AP-free linear order of $[M,2M+6]$ satisfying $U(j,a)$ for all $j\in\{0,1,2,3\}$ and $a\in\{0,1\}$.

**Corollary I.** Let $S\subseteq\mathbb N$ be permutable and let $v,v+1\in S$. Then there is $P_0$ such that no interval $[P,\,2P-v+6]$ with $P\ge P_0$ is contained in $S$.

*Notation.* "$u\prec w$" means $u$ comes before $w$. We write $b_j=M+j$ ($0\le j\le 3$, the *bottoms*) and $u(j,a)=2b_j-a$ (the *tops*), so $U(j,a)$ reads $u(j,a)\prec b_j$. In Sections 1–4, $\prec$ is a fixed AP-free order of $I$ satisfying all $U(j,a)$, and we derive a contradiction.

**Midpoint rule.** For every 3-AP $x<y<z$ in $I$: $y\prec x\iff y\prec z$. The midpoint comes before both endpoints or after both. This is a restatement of AP-freeness.

## 1. Ladder lemmas

The lemmas of this section hold for any AP-free linear order of any integer interval $I=[L,R]$. They are the zigzag/flood toolkit of Kasel (arXiv:2609.02939, Lemmas 23–26). We give self-contained proofs, in the form used in the Lean formalization.

For $g\ge1$, the *$g$-ladder* through $w$ is $(w+g\mathbb Z)\cap I$. Its *orientation* at $w$ is $o_g(w)=[\,w\prec w+g\,]$, defined when $w,w+g\in I$. Say $x$ *$g$-leads* if $x$ precedes its $g$-neighbours $x\pm g$ in $I$, and *$g$-trails* if it follows them.

**Lemma 1 (zigzag).** If $w,w+2g\in I$ then $o_g(w+g)=\neg\,o_g(w)$. Consequently $o_g(w+2mg)=o_g(w)$ whenever $w,\ w+(2m+1)g\in I$. Every $x$ with $x\pm g\in I$ either $g$-leads or $g$-trails, and of two $g$-neighbours exactly one $g$-leads.

*Proof.* The midpoint rule for $(w,w+g,w+2g)$ gives $w+g\prec w+2g\iff w+g\prec w$, i.e. $o_g(w+g)\iff\neg o_g(w)$. Iterate twice per step. For the last sentence: $x$ $g$-leads iff $o_g(x)$ and $\neg o_g(x-g)$, and these agree by the first sentence. $\square$

**Lemma 2 (flood).** Let $h\ge1$, $c\in I$, and $e=h(2k+1)$ with $c-e,\ c+e\in I$. Then $c\prec c+e\iff c\prec c+h$. By the midpoint rule also $c\prec c-e\iff c\prec c+e$.

*Proof.* Induction on $k$; $k=0$ is trivial. For the step let $e=h(2k+1)$, $e'=e+2h$ with $c\pm e'\in I$. Put $g=2h$ and
$$y_-=c-e',\quad x_-=c-e,\quad x_+=c+e,\quad y_+=c+e'.$$
Then $x_+-y_-=2e+g=2(k+1)g$, so Lemma 1 on the $g$-ladder gives $o_g(y_-)=o_g(x_+)$, i.e. $y_-\prec x_-\iff x_+\prec y_+$. We show $c\prec x_+\iff c\prec y_+$; with the induction hypothesis this proves the claim.

* If $x_+\prec y_+$ (so $y_-\prec x_-$): from $c\prec x_+$ we get $c\prec y_+$ by transitivity. Conversely, suppose $c\prec y_+$ but $x_+\prec c$. The midpoint rule for $(x_-,c,x_+)$ gives $x_-\prec c$, so $y_-\prec x_-\prec c$. The midpoint rule for $(y_-,c,y_+)$ then gives $y_+\prec c$, a contradiction.
* If $y_+\prec x_+$ (so $x_-\prec y_-$): from $c\prec x_+$ the midpoint rule gives $c\prec x_-\prec y_-$, and then $c\prec y_+$. Conversely $c\prec y_+\prec x_+$. $\square$

## 2. The rules used in the proof

**Leading parity.** By Lemma 1 for $g=1$ on $I$ itself, there is a parity class $\pi\in\{0,1\}$ such that every $x$ with $x\pm1\in I$ and $x\equiv\pi\pmod 2$ $1$-leads, and every such $x\not\equiv\pi$ $1$-trails. Precisely: $x\prec x+1\iff(M\prec M+1\iff x\equiv M\pmod 2)$. We call $\pi$ the *leading parity*.

**Rule A** (Lemma 2 with $h=1$). Let $x,w\in I$ with $w-x$ odd and $2x-w\in I$. Then $x\prec w\iff x\prec x+1$. So if $x\equiv\pi$ then $x\prec w$, and if $x\not\equiv\pi$ then $w\prec x$.

**Rule B** (Lemma 2 with $h=2$). Let $x,w\in I$ with $w-x\equiv2\pmod 4$ and $2x-w\in I$. Then $x\prec w\iff x\prec x+2$. In words: (i) if $x$ $2$-leads then $x\prec w$, and if $x$ $2$-trails then $w\prec x$; (ii) conversely, $x\prec w$ forces $x$ to $2$-lead, and $w\prec x$ forces it to $2$-trail.

(In both rules $x\pm1$, resp. $x\pm2$, lie in $I$ automatically, since $w$ and $2x-w$ do.)

**Rule Z** (Lemma 1 with $g=2$). If $x,x+2\in I$ both $2$-lead, or both $2$-trail, we have a contradiction.

## 3. Two mechanisms

**Lemma I (two adjacent centres).** Let $M\ge 8$, $j\in\{0,1\}$, $a\in\{0,1\}$ and let $s$ be an integer with
$$\frac{M-a-4}{8}\ \le\ s\ \le\ \frac{M-j}{8}. \tag{I.1}$$
Put $c=M+j+2+4s$ and suppose $c\equiv\pi$ and $a\not\equiv\pi\pmod 2$. Then $\prec$ does not exist.

*Proof.* From (I.1) and $M\ge8$: $s\ge1$, so $c\ge M+6$. Also $c\le (3M+j)/2+2$, so $c+4\le 2M+6$. Let $b=b_j=M+j$ and $u=u(j,a)=2b-a$. Let $b'=b+2=b_{j+2}$ (note $j+2\le3$), $u'=u(j+2,a)=u+4$ and $c'=c+2$.

1. $c\prec u$ by Rule A at $x=c$, $w=u$. Indeed $u\equiv a\not\equiv\pi\equiv c$. Also $2c-u=4+8s+a$, which lies in $I$: $4+8s+a\ge M$ is the left inequality of (I.1), and $4+8s+a\le M+5$.
2. $u\prec b$ is $U(j,a)$. So $c\prec b$.
3. $c$ $2$-leads, by Rule B(ii) at $x=c$, $w=b$. Indeed $b-c=-(2+4s)\equiv2\pmod4$. Also $2c-b=M+j+4+8s\in I$, because $8s\le M-j$.
4. $c'\prec u'$ by Rule A at $x=c'$, $w=u'$: $u'\equiv a\not\equiv\pi\equiv c'$, and $2c'-u'=2c-u\in I$.
5. $u'\prec b'$ is $U(j+2,a)$. So $c'\prec b'$.
6. $c'$ $2$-leads, by Rule B(ii) at $x=c'$, $w=b'$: $b'-c'=b-c\equiv2\pmod 4$, and $2c'-b'=M+j+6+8s\le 2M+6$.
7. $c$ and $c'=c+2$ both $2$-lead, contradicting Rule Z. $\square$

**Lemma II (one centre, one AP).** Let $c\in I$ with $c\pm2\in I$ and $c\not\equiv\pi\pmod 2$. Let $\delta\in\{1,-1\}$ and $c'=c+2\delta$ with $c'\pm2\in I$. Let $(j_i,a_i)$, $i=1,2,3$, be index pairs with $b_i=M+j_i$ and $u_i=u(j_i,a_i)=2b_i-a_i$, such that

1. $b_1\equiv\pi\pmod 2$ and $2c-b_1\in I$;
2. $u_1-c\equiv2\pmod4$ and $2c-u_1\in I$;
3. $u_2-c'\equiv2\pmod 4$ and $2c'-u_2\in I$;
4. $b_3\equiv\pi\pmod2$ and $2c'-b_3\in I$;
5. $b_2+u_3=2c'$.

Then $\prec$ does not exist.

*Proof.* Rule A at $x=c$ (which $1$-trails) and $w=b_1$ gives $b_1\prec c$ (hypothesis 1). With $U(j_1,a_1)$: $u_1\prec b_1\prec c$. By hypothesis 2 and Rule B(ii) at $x=c$, $w=u_1$, the point $c$ $2$-trails. By Lemma 1 its $2$-neighbour $c'=c+2\delta$ $2$-leads. By hypothesis 3 and Rule B(i) at $x=c'$, $w=u_2$: $c'\prec u_2$; with $U(j_2,a_2)$: $c'\prec b_2$. Next, $c'\equiv c\not\equiv\pi$, so $c'$ $1$-trails; hypothesis 4 and Rule A at $x=c'$, $w=b_3$ give $b_3\prec c'$, and with $U(j_3,a_3)$: $u_3\prec b_3\prec c'$. By hypothesis 5, $(b_2,c',u_3)$ is an AP with midpoint $c'$, and $b_2<c'<u_3$ because $b_2\le M+3<2M-1\le u_3$. The midpoint rule and $u_3\prec c'$ give $b_2\prec c'$, contradicting $c'\prec b_2$. $\square$

## 4. Proof of Theorem I

Let $\pi$ be the leading parity of $\prec$ and $C=\lfloor(3M+6)/2\rfloor$. We distinguish the branch $\pi\equiv M$ (the parity of $M$ leads) from the branch $\pi\not\equiv M$, and the residue $M\bmod 8$: sixteen cases.

**Cases handled by Lemma I.** Take $j=0$ if $\pi\equiv M$ and $j=1$ if $\pi\not\equiv M$, so that $c=M+j+2+4s\equiv\pi$. Take $a=1-\pi$, so that $a\not\equiv\pi$. An integer $s$ satisfying (I.1) exists iff $[M-a-4,\,M-j]$ contains a multiple of $8$, i.e. iff $M\bmod8\in\{j,j+1,\dots,a+4\}$; then $s=\lfloor M/8\rfloor$ works.

| branch | $M$ even ($\pi$, $a$) | $M$ odd ($\pi$, $a$) | residues $M\bmod 8$ covered |
|---|---|---|---|
| $\pi\equiv M$ ($j=0$) | $\pi=0,\ a=1$: $M\bmod8\in\{0,\dots,5\}$ | $\pi=1,\ a=0$: $M\bmod8\in\{0,\dots,4\}$ | $0,1,2,3,4$ |
| $\pi\not\equiv M$ ($j=1$) | $\pi=1,\ a=0$: $M\bmod8\in\{1,\dots,4\}$ | $\pi=0,\ a=1$: $M\bmod8\in\{1,\dots,5\}$ | $1,2,3,4,5$ |

For instance, take $M\equiv0\pmod 8$ and $\pi\equiv M$. Then $j=0$, $a=1$, $s=M/8$, $c=(3M+4)/2=C-1$, $c'=C+1$, $u=2M-1$, $u'=2M+3$. The chains are $C-1\prec 2M-1\prec M$ and $C+1\prec 2M+3\prec M+2$, so both centres $2$-lead.

**Cases handled by Lemma II.** These are the six remaining (branch, residue) pairs. In each row all hypotheses 1–5 of Lemma II hold; "$\equiv2$" abbreviates "$\equiv2\pmod 4$". Recall $u(j,a)=2M+2j-a$.

| branch, $M\bmod8$ | $c$; why $c\not\equiv\pi$ | $(u_1\to b_1)$; hyp. 1, 2 | $c'$ | $(u_2\to b_2)$; hyp. 3 | $(u_3\to b_3)$; hyp. 4, 5 |
|---|---|---|---|---|---|
| $\pi\equiv M$, $5$ | $c=C-2=\frac{3M+1}2$; $c-M=\frac{M+1}2\equiv3\ (4)$ odd | $2M\to M$; $2c-b_1=2M+1$; $u_1-c=\frac{M-1}2\equiv2$, $2c-u_1=M+1$ | $C=\frac{3M+5}2$ | $2M+2\to M+1$; $u_2-c'=\frac{M-1}2\equiv2$, $2c'-u_2=M+3$ | $2M+4\to M+2$; $2c'-b_3=2M+3$; $b_2+u_3=3M+5=2c'$ |
| $\pi\equiv M$, $6$ | $c=C-3=\frac{3M}2$; $c-M=\frac M2\equiv3\ (4)$ odd | $2M-1\to M$; $2c-b_1=2M$; $u_1-c=\frac{M-2}2\equiv2$, $2c-u_1=M+1$ | $C-1=\frac{3M+4}2$ | $2M+1\to M+1$; $u_2-c'=\frac{M-2}2\equiv2$, $2c'-u_2=M+3$ | $2M+3\to M+2$; $2c'-b_3=2M+2$; $b_2+u_3=3M+4=2c'$ |
| $\pi\equiv M$, $7$ | $c=C-1=\frac{3M+3}2$; $c-M=\frac{M+3}2\equiv1\ (4)$ odd | $2M\to M$; $2c-b_1=2M+3$; $u_1-c=\frac{M-3}2\equiv2$, $2c-u_1=M+3$ | $C+1=\frac{3M+7}2$ | $2M+6\to M+3$; $u_2-c'=\frac{M+5}2\equiv2$, $2c'-u_2=M+1$ | $2M+4\to M+2$; $2c'-b_3=2M+5$; $b_2+u_3=3M+7=2c'$ |
| $\pi\not\equiv M$, $0$ | $c=C+1=\frac{3M+8}2$; $c-M=\frac{M+8}2\equiv0\ (4)$ even | $2M+6\to M+3$; $2c-b_1=2M+5$; $u_1-c=\frac{M+4}2\equiv2$, $2c-u_1=M+2$ | $C-1=\frac{3M+4}2$ | $2M+4\to M+2$; $u_2-c'=\frac{M+4}2\equiv2$, $2c'-u_2=M$ | $2M+2\to M+1$; $2c'-b_3=2M+3$; $b_2+u_3=3M+4=2c'$ |
| $\pi\not\equiv M$, $6$ | $c=C=\frac{3M+6}2$; $c-M=\frac{M+6}2\equiv2\ (4)$ even | $2M+2\to M+1$; $2c-b_1=2M+5$; $u_1-c=\frac{M-2}2\equiv2$, $2c-u_1=M+4$ | $C-2=\frac{3M+2}2$ | $2M\to M$; $u_2-c'=\frac{M-2}2\equiv2$, $2c'-u_2=M+2$ | $2M+2\to M+1$; $2c'-b_3=2M+1$; $b_2+u_3=3M+2=2c'$ |
| $\pi\not\equiv M$, $7$ | $c=C=\frac{3M+5}2$; $c-M=\frac{M+5}2\equiv2\ (4)$ even | $2M+1\to M+1$; $2c-b_1=2M+4$; $u_1-c=\frac{M-3}2\equiv2$, $2c-u_1=M+4$ | $C-2=\frac{3M+1}2$ | $2M-1\to M$; $u_2-c'=\frac{M-3}2\equiv2$, $2c'-u_2=M+2$ | $2M+1\to M+1$; $2c'-b_3=2M$; $b_2+u_3=3M+1=2c'$ |

Checks common to all six rows:

* $b_1,b_3\equiv\pi$. In the rows with $\pi\equiv M$ the bottoms $b_1,b_3\in\{M,M+2\}$ have the parity of $M$; in the rows with $\pi\not\equiv M$ they lie in $\{M+1,M+3\}$.
* $c\not\equiv\pi$ is shown in the second column.
* All listed values $2c-b_1$, $2c-u_1$, $2c'-u_2$, $2c'-b_3$ lie in $[M,2M+6]$.
* The congruences $\equiv2\pmod 4$ follow from the residue of $M$ modulo $8$. For example, $M\equiv5\pmod8$ gives $M-1\equiv4\pmod8$, so $(M-1)/2\equiv2\pmod4$.
* $c\pm2$ and $c'\pm2$ lie in $[\frac{3M-4}2,\frac{3M+12}2]\subseteq I$, since $M\ge8$.

Together, the two tables cover both branches and all residues: branch $\pi\equiv M$ has residues $0$–$4$ by Lemma I and $5,6,7$ by Lemma II; branch $\pi\not\equiv M$ has residues $1$–$5$ by Lemma I and $0,6,7$ by Lemma II. Hence $\prec$ does not exist. $\blacksquare$

*Remark.* Each case uses at most three of the eight constraints. Lemma I uses $U(j,a)$ and $U(j+2,a)$. The first four Lemma II rows use three constraints each; the last two use only two, because there $(u_1\to b_1)=(u_3\to b_3)$. Different residues use different subsets.

## 5. Proof of Corollary I

Let $f:\mathbb N\to S$ be an enumeration with no monotone 3-AP. Write $x\prec y$ when $x$ is listed before $y$.

*Anchor rule.* If $p,w,t\in S$, $p<w$, $p+t=2w$ and $p\prec w$, then $t\prec w$. Otherwise $w\prec t$, and $p\prec w\prec t$ is a monotone progression $p<w<t$.

Only finitely many elements precede $v$ or $v+1$; let $B$ bound them, and put $P_0=B+v+9$. Suppose $P\ge P_0$ and $G=[P,\,2P-v+6]\subseteq S$. Put $M=P-v\ge 8$. Every $w\in G$ exceeds $B$, so $v\prec w$ and $v+1\prec w$. For $w=P+j$ ($0\le j\le3$) and $p=v+a$ ($a\in\{0,1\}$) the point $t=2w-p=2(M+j)-a+v$ lies in $G$, and $p<w$. So the anchor rule gives $t\prec w$. Now transport the order to $[M,2M+6]$ by $x\mapsto x+v$. This preserves 3-APs, so the transported order is AP-free, and it satisfies all eight constraints $U(j,a)$. This contradicts Theorem I. $\square$

*Remarks.* (1) The same argument with the affine map $k\mapsto v+kd$ gives the following. If $v,v+d\in S$, then only finitely many $K\ge8$ satisfy $\{v+kd:K\le k\le 2K+6\}\subseteq S$.

(2) Corollary I reproves Kasel's theorem that the dyadic partition fails. Its class $\bigcup_i(2^{2i-1},2^{2i}]$ contains $9,10$ and the intervals $[P,2P-2]\supseteq[P,2P-9+6]$ with $P=2^{2i-1}+1$. This consequence already follows from trureturing PR #9626, with $v=15$ and window $2P-v+13$.

## 6. Optimality of the constant 6

Theorem I fails with $2M+5$ in place of $2M+6$. For $M=8$ the order
$$15\prec19\prec21\prec11\prec13\prec17\prec16\prec20\prec18\prec9\prec8\prec12\prec10\prec14$$
of $[8,21]$ is AP-free and satisfies the seven anchor constraints whose tops lie in $[8,21]$ (all except $U(3,0)$, whose top is $22$). This was found by a short search and checked by the Lean kernel (`checks/nonvacuity.lean`). So the constant $6$ is optimal for Theorem I as stated, that is, for all $M\ge8$.

The following computations are evidence, not proof. Two independently written SAT encodings (CaDiCaL 2.1.2, every model decoded and re-checked) agree on the following. For $8\le M\le 90$, the window $[M,2M+5]$ with its seven constraints is feasible exactly for
$$M\in\{8,10,16,18,24,26,34,42,50,58,74,82,90\}.$$
Both encodings also find $[M,2M+6]$ infeasible for every $8\le M\le 90$, as Theorem I says. A third, separately written encoding (by an AI auditor of this repository) gives the same list for $8\le M\le 90$, and for $91\le M\le 160$ finds $[M,2M+5]$ feasible exactly for $M\in\{98,106,114,122,138,154\}$; that range was checked by this one program only. These computations were run by two of the referees of the proof and by the auditor. They are recorded in work notes (the scripts are not included in this repository) and are not part of the proof of Theorem I.

*Conjecture.* The window $[M,2M+5]$ with its seven constraints is feasible for infinitely many $M$. If this holds, $2P-v+6$ is the best window that the gadget argument of Corollary I can give from a single consecutive pair, since that argument uses only an AP-free order of the window with these anchor constraints. The data above support the conjecture; it is not proved.

## 7. Relation to earlier work

* *Kasel's order gadget.* $\mathrm{OG}(M)$ asks for an AP-free order of the block $(M,2M]$ with the "guards" $2M+2j-x\prec M+j$ for $x\in\{15,16\}$ and $1\le j\le x/2$. Translating by $-15$ and putting $M'=M-14$, this is exactly an AP-free order of $[M',2M'+13]$ satisfying every constraint $U(j,a)$ whose top lies in that window ($x=15\leftrightarrow a=0$, $x=16\leftrightarrow a=1$, $j'=j-1$). Theorem I implies that $\mathrm{OG}(M)$ is infeasible for every $M\ge22$: restrict to $[M',2M'+6]$, which carries all eight constraints $U(j,a)$.
* *trureturing PR #9626* proves $\mathrm{OG}(M)$ infeasible for all $M\ge16$, in Lean. Its mechanism is a "four-flood cycle" on two adjacent centres, which is Lemma I here; its four guards per parity are, after translation, exactly the anchor pairs that Lemma I uses in the two branches. On the longer window $[M',2M'+13]$ the PR's proof needs only this mechanism. On $[M,2M+6]$ Lemma I has no admissible centre pair in the six (branch, residue) cases of the second table, and those need Lemma II. The four guards alone do not suffice on $[M,2M+6]$: for $M=13$ and $M=14$ there are AP-free orders of $[M,2M+6]$ satisfying them (found by a referee's solver and re-checked by a separate script). So neither result is obtained from the other by specialization: Theorem I does not follow by restricting the four-guard lemma to the shorter window, and the four-guard lemma is not an instance of Theorem I.
* *What is new* is Lemma II and the window constant $6$, which is optimal for Theorem I as stated ($M\ge8$): $13\to6$ in the consequence for permutable sets.

## 8. Lean formalization

`Erdos197Interval/Basic.lean` follows Sections 1–5.

* A linear order of $[L,R]$ is an injective ranking $\sigma:\mathbb N\to\mathbb N$, with $x\prec y$ iff $\sigma(x)<\sigma(y)$. Every linear order of a finite set has such a ranking (its position function), and every injective ranking defines one. `Good L R σ` packages injectivity on $[L,R]$ and the midpoint rule.
* `Good.alt` is Lemma 1. `Good.flood` and `Good.rule` are Lemma 2 (one-sided and two-sided), and `Good.ruleA`/`Good.ruleB` are Rules A and B in the iff form above. `Good.lead_iff` is the leading parity.
* `Good.lemmaI` and `Good.lemmaII` are Lemmas I and II, stated for a general interval with the anchor constraints and the side conditions as hypotheses. `gadget_core` is Section 4: one call of Lemma I per branch with $s=\lfloor M/8\rfloor$, and the six Lemma II rows with the points written as $12q+\dots$, $16q+\dots$, $8q+\dots$ for $q=\lfloor M/8\rfloor$.
* `corollary` is Section 5; `no_ap` converts the formal-conjectures predicate into the statement that no positions $p<q<r$ carry a 3-AP.

The Lean statements use Lean's $\mathbb N=\{0,1,2,\dots\}$, as formal-conjectures does. Nothing above uses positivity. In Corollary I, `2 * P + 6 - v` is truncated subtraction, which equals $2P-v+6$ for all $P\ge v$, in particular for all $P\ge P_0$.
