# Simplifications visible after closure

This file records genuine post-closure compression opportunities.  A proposed
compression is not promoted to the review manuscript until every hypothesis
and endpoint has been checked against the active proof sources.

## 1. One six-circle signature lemma

Let `Gamma` be a maximal proper circle on six marked points and let `X` be its
`q`-point complement.  For an outside pair `e`, let `h_e` be the number of
circles through `e` and two points of `Gamma`, and put

```text
W = sum_e h_e.
```

Two distinct such circles use disjoint pairs of `Gamma`, hence `h_e <= 3`.
If equality holds, the three pairs form a perfect matching of the six marked
points and determine a fixed-point-free projective involution of `Gamma`.
Cyclic order permits at most four such involutions.  For a fixed involution,
the outside pairs carrying it form a matching in `K_q`; consequently the
number `F` of full outside pairs satisfies

```text
F <= 4 floor(q/2).
```

Every non-full pair contributes at most two, so one uniform estimate is

```text
W <= 2 binom(q,2) + 4 floor(q/2).                    (S)
```

For `q=7,8,9`, this gives `W<=54,72,88`.  Thus the former separate capacity
arguments at `n=13,14,15` should be presented as one lemma.  The smaller
values `q=5,6` need their already proved line-centre refinements; (S) alone is
not sharp enough there.

## 2. One added-centre row for six-circles

For `n=q+6`, the coefficientwise added-centre inequality used at `n=14,15`
has the common form

```text
4D >= 6P0 + 9P1 + 12P2 + 6P3
      + 3 M_Gamma + 6 M_X - 36C - 6W,
```

where

```text
P0=binom(q,3),  P1=6 binom(q,2),  P2=15q,  P3=20,
M_Gamma>=18,   M_X>=3q,            D<=n(n-4).
```

Under the counterexample cap `C<=F(n)-1`, it follows that

```text
6W >= 6 binom(q,3) + 54 binom(q,2) + 198q + 174
      -36(F(q+6)-1) -4(q+6)(q+2).                   (A)
```

The right side of (A) equals `276,454,720` for `q=7,8,9`.  Hence

```text
q=7: W>=46,
q=8: W>=76,
q=9: W>=120.
```

Combining with (S) immediately settles `q=8,9`, that is the six-circle
branches at `n=14,15`.  At `q=7`, the common row only narrows the range to
`46<=W<=54`; the sharper coefficientwise inequality already proved for
`n=13` gives `W>=48` and the remaining values need their short congruence and
incidence arguments.  It would be incorrect to claim that (A) alone closes
`n=13`.

The same row also applies to the sixteen-point six-circle branch.  Here
`q=10`, the critical-deletion reduction bounds every generalized block by
nine points, and the line factors remain nonnegative on the resulting ranges.
Formula (A) gives `W>=168`, whereas (S) gives `W<=110`.  This replaces the
former weak branch-specific dual `20041/204>98` by a large integral gap.

## 2a. The same row removes the four- and five-circle branches at n=16

For a selected circle of size `m=4,5,6`, keep `n=16`, put `q=16-m`, and use
the same coefficientwise row.  Its slack on the selected block is
respectively `12,11,0`, and the nonselected factors are nonnegative because
every generalized block has size at most nine.  The resulting lower bounds
are

```text
m=4: W>=90,
m=5: W>=132,
m=6: W>=168.
```

For `m=5`, two distinct circles over one outside pair consume disjoint pairs
of the five selected points, so `W<=2 binom(11,2)=110`.  For `m=6`, (S) gives
`W<=110`.  For `m=4`, a full outside pair uses one of the three perfect
matchings of the selected four-set.  The support of each fixed matching is a
matching on the twelve outside points, so at most eighteen outside pairs are
full and

```text
W <= binom(12,2)+3 floor(12/2)=84.
```

Thus one added-centre lemma plus one matching-support lemma replaces three of
the seven former sixteen-point duals.

## 3. The five-circle transfer is already parametric

The added-centre identities

```text
A <= 4C+n(n-4)-binom(n,3)+C5,
A >= (5/3)S,
24 binom(n,3)+27P <= 35(S+3C)
```

form one blockwise transfer, not separate computations for each `n`.  It
settles the five-circle branches at `n=13,14` and reduces `n=12` to the three
boundary values `C=48,49,50`.  The review manuscript should state and prove
this transfer once, then treat only the genuinely exceptional endpoints.

## 4. A small ordinary-pair graph lemma removes an external classification

The post-closure link argument proves internally that ten real points with no
four collinear cannot have thirteen triple lines.  Its ordinary-pair graph
would be `K_{1,3} disjoint union 3K_2`; deleting the degree-three vertex gives
the forbidden nine-point `C_6` link.  The corresponding eleven-point case
with seventeen triple lines reduces to it through its `C_4` ordinary graph.
This should replace the former external arrangement classification wherever
it occurs.

## 5. Simplifications not yet justified

- The seven selected-circle duals in the sixteen-point base case do not yet
  all follow from the parametric `n>=17` functional.  The post-closure
  added-centre argument above now removes `m=4,5,6`, the elementary `m=3`
  combination remains short, and the correct rich-circle estimate removes
  `m=9`.  The substantive cases still needing simplification are `m=7,8`.
  Notice that the rich-circle estimate is
  `1+q*(binom(m,2)-floor(m/2))-binom(q,2)floor(m/2)`; omitting its first
  collinearity loss would incorrectly claim that `m=8` is already closed.
- The three endpoint mechanisms at `n=12,C=48,49,50` currently express
  genuinely different obstructions (Gram, inversion/parity, and grid/Hall).
  They may be grouped expositionally, but no honest common lemma has yet been
  proved.
- Large rational multipliers may be moved to coefficient tables, but hiding
  them is not a mathematical simplification.  A real simplification must
  reduce the hypotheses or replace several certificates by one proved
  inequality.
