import Erdos506.Finite.IncidenceMoments
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Tetrahedral decomposition from two-triangle links

This file is purely finite.  A tetrahedral completion of a triple `e` is a
four-set `Q` containing `e` whose four three-faces all belong to the family.
Unique local completion is the label-free consequence of saying that every
edge in every link belongs to a unique link triangle.

For the ten-vertex application we also package the elementary local data for
a link of type `C3 ⊔ C3 ⊔ 3K1`: it has six edges, every active link vertex
has degree at most two, and every hyperedge has its unique tetrahedral
completion.  The decomposition itself only needs the uniformity, the twenty
edges, and unique local completion, so its main theorem is stated in that
slightly stronger, reusable form.
-/

namespace Erdos506.Finite

open scoped BigOperators

/-- `Q` is the tetrahedral boundary completing the triple `e` inside `H`. -/
def IsTetrahedralCompletion {Point : Type*} [DecidableEq Point]
    (H : Finset (Finset Point)) (e Q : Finset Point) : Prop :=
  Q.card = 4 ∧ e ⊆ Q ∧ Q.powersetCard 3 ⊆ H

/-- Every hyperedge has one and only one local tetrahedral completion. -/
def HasUniqueLocalTriangleCompletion {Point : Type*} [DecidableEq Point]
    (H : Finset (Finset Point)) : Prop :=
  ∀ e ∈ H, ∃! Q : Finset Point, IsTetrahedralCompletion H e Q

/-- Number of triples of `H` through a vertex.  This is the edge count of its
link graph. -/
def tripleDegree {Point : Type*} [DecidableEq Point]
    (H : Finset (Finset Point)) (p : Point) : ℕ :=
  (H.filter fun e => p ∈ e).card

/-- Degree of `q` in the link graph at `p`. -/
def linkVertexDegree {Point : Type*} [DecidableEq Point]
    (H : Finset (Finset Point)) (p q : Point) : ℕ :=
  (H.filter fun e => p ∈ e ∧ q ∈ e).card

/-- A label-free local certificate for links `C3 ⊔ C3 ⊔ 3K1`.

Uniformity makes the members triples.  There are six link edges at every
pivot.  The pair-degree cap prevents two link triangles from sharing a
vertex, while `completion` supplies and uniquely closes the triangle around
each link edge.  On ten vertices the remaining three link vertices are
isolated. -/
structure TwoTriangleLinks {Point : Type*} [DecidableEq Point]
    (H : Finset (Finset Point)) : Prop where
  uniform : ∀ e ∈ H, e.card = 3
  link_card : ∀ p, tripleDegree H p = 6
  link_vertex_degree_le_two : ∀ p q, p ≠ q → linkVertexDegree H p q ≤ 2
  completion : HasUniqueLocalTriangleCompletion H

/-- A ten-vertex three-uniform family with two-triangle links has twenty
triples. -/
theorem card_eq_twenty_of_twoTriangleLinks
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (H : Finset (Finset Point)) (hPoint : Fintype.card Point = 10)
    (hlinks : TwoTriangleLinks H) :
    H.card = 20 := by
  have hsum := sum_incidenceDegree H (fun e : Finset Point => e)
  have hdegree (p : Point) :
      incidenceDegree H (fun e : Finset Point => e) p = 6 := by
    simpa only [incidenceDegree, incidenceIndicator, tripleDegree,
      Finset.sum_boole] using hlinks.link_card p
  have hleft :
      (∑ p : Point, incidenceDegree H (fun e : Finset Point => e) p) = 60 := by
    simp only [hdegree, Finset.sum_const, Finset.card_univ, hPoint]
    norm_num
  have hright :
      (∑ e ∈ H, ((fun f : Finset Point => f) e).card) = 3 * H.card := by
    calc
      (∑ e ∈ H, ((fun f : Finset Point => f) e).card) =
          ∑ _e ∈ H, 3 := by
            apply Finset.sum_congr rfl
            intro e he
            exact hlinks.uniform e he
      _ = 3 * H.card := by simp [Nat.mul_comm]
  rw [hleft, hright] at hsum
  omega

/-- The candidate four-sets all of whose three-faces belong to `H`. -/
def tetrahedralBoundaries {Point : Type*} [Fintype Point]
    [DecidableEq Point] (H : Finset (Finset Point)) : Finset (Finset Point) :=
  (Finset.univ.powersetCard 4).filter fun Q => Q.powersetCard 3 ⊆ H

theorem mem_tetrahedralBoundaries
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {H : Finset (Finset Point)} {Q : Finset Point} :
    Q ∈ tetrahedralBoundaries H ↔
      Q.card = 4 ∧ Q.powersetCard 3 ⊆ H := by
  simp [tetrahedralBoundaries, Finset.mem_powersetCard]

/-- Twenty triples with unique local triangle completion are the disjoint
union of five tetrahedral boundaries. -/
theorem exists_five_tetrahedral_boundaries
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (H : Finset (Finset Point))
    (huniform : ∀ e ∈ H, e.card = 3)
    (hcard : H.card = 20)
    (hcompletion : HasUniqueLocalTriangleCompletion H) :
    ∃ K : Finset (Finset Point),
      K.card = 5 ∧
      (∀ Q ∈ K, Q.card = 4 ∧ Q.powersetCard 3 ⊆ H) ∧
      H = K.biUnion (fun Q => Q.powersetCard 3) ∧
      (K : Set (Finset Point)).PairwiseDisjoint
        (fun Q => Q.powersetCard 3) := by
  classical
  let K := tetrahedralBoundaries H
  have hK (Q : Finset Point) :
      Q ∈ K ↔ Q.card = 4 ∧ Q.powersetCard 3 ⊆ H := by
    simpa only [K] using
      (mem_tetrahedralBoundaries (H := H) (Q := Q))
  have hcover : H = K.biUnion (fun Q => Q.powersetCard 3) := by
    ext e
    constructor
    · intro he
      obtain ⟨Q, hQ, _hunique⟩ := hcompletion e he
      have hQK : Q ∈ K := hK Q |>.2 ⟨hQ.1, hQ.2.2⟩
      exact Finset.mem_biUnion.mpr ⟨Q, hQK,
        Finset.mem_powersetCard.mpr ⟨hQ.2.1, huniform e he⟩⟩
    · intro he
      rcases Finset.mem_biUnion.mp he with ⟨Q, hQK, heQ⟩
      exact (hK Q |>.1 hQK).2 heQ
  have hdisjoint :
      (K : Set (Finset Point)).PairwiseDisjoint
        (fun Q => Q.powersetCard 3) := by
    intro Q hQ R hR hQR
    change Disjoint (Q.powersetCard 3) (R.powersetCard 3)
    rw [Finset.disjoint_left]
    intro e heQ heR
    have hQdata := hK Q |>.1 hQ
    have hRdata := hK R |>.1 hR
    have heH : e ∈ H := hQdata.2 heQ
    obtain ⟨W, _hW, hWunique⟩ := hcompletion e heH
    have hQcompletion : IsTetrahedralCompletion H e Q :=
      ⟨hQdata.1, Finset.mem_powersetCard.mp heQ |>.1, hQdata.2⟩
    have hRcompletion : IsTetrahedralCompletion H e R :=
      ⟨hRdata.1, Finset.mem_powersetCard.mp heR |>.1, hRdata.2⟩
    have hQW : Q = W := hWunique Q hQcompletion
    have hRW : R = W := hWunique R hRcompletion
    exact hQR (hQW.trans hRW.symm)
  have hboundaryCard (Q : Finset Point) (hQ : Q ∈ K) :
      (Q.powersetCard 3).card = 4 := by
    rw [Finset.card_powersetCard, (hK Q |>.1 hQ).1]
    norm_num
  have hdecompositionCard : H.card = K.card * 4 := by
    rw [hcover, Finset.card_biUnion hdisjoint]
    calc
      (∑ Q ∈ K, (Q.powersetCard 3).card) = ∑ _Q ∈ K, 4 := by
        apply Finset.sum_congr rfl
        intro Q hQ
        exact hboundaryCard Q hQ
      _ = K.card * 4 := by simp
  have hKcard : K.card = 5 := by omega
  exact ⟨K, hKcard, fun Q hQ => hK Q |>.1 hQ, hcover, hdisjoint⟩

/-- Two distinct three-faces of one four-set share at least two vertices. -/
theorem two_le_card_inter_of_three_subsets_of_four
    {Point : Type*} [DecidableEq Point]
    {e f Q : Finset Point}
    (hecard : e.card = 3) (hfcard : f.card = 3) (hQcard : Q.card = 4)
    (heQ : e ⊆ Q) (hfQ : f ⊆ Q) :
    2 ≤ (e ∩ f).card := by
  have hunion : (e ∪ f).card ≤ Q.card :=
    Finset.card_le_card (Finset.union_subset heQ hfQ)
  have hcount := Finset.card_union_add_card_inter e f
  omega

/-- A two-overlap-free subfamily contains at most one face from each of the
five tetrahedral boundaries. -/
theorem card_le_five_of_pairwise_inter_lt_two
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (H P : Finset (Finset Point))
    (huniform : ∀ e ∈ H, e.card = 3)
    (hcard : H.card = 20)
    (hcompletion : HasUniqueLocalTriangleCompletion H)
    (hsub : P ⊆ H)
    (hinter : ∀ e ∈ P, ∀ f ∈ P, e ≠ f → (e ∩ f).card < 2) :
    P.card ≤ 5 := by
  classical
  obtain ⟨K, hKcard, hK, hcover, hdisjoint⟩ :=
    exists_five_tetrahedral_boundaries H huniform hcard hcompletion
  let selectedFaces : Finset Point → Finset (Finset Point) :=
    fun Q => P ∩ Q.powersetCard 3
  have hselectedCard (Q : Finset Point) (hQ : Q ∈ K) :
      (selectedFaces Q).card ≤ 1 := by
    refine Finset.card_le_one_iff.mpr ?_
    intro e f he hf
    have heP : e ∈ P := (Finset.mem_inter.mp he).1
    have hfP : f ∈ P := (Finset.mem_inter.mp hf).1
    by_contra hef
    have heface := Finset.mem_powersetCard.mp (Finset.mem_inter.mp he).2
    have hfface := Finset.mem_powersetCard.mp (Finset.mem_inter.mp hf).2
    have hlarge := two_le_card_inter_of_three_subsets_of_four
      heface.2 hfface.2 (hK Q hQ).1 heface.1 hfface.1
    exact (Nat.not_le_of_lt (hinter e heP f hfP hef)) hlarge
  have hselectedDisjoint :
      (K : Set (Finset Point)).PairwiseDisjoint selectedFaces := by
    intro Q hQ R hR hQR
    exact (hdisjoint hQ hR hQR).mono
      Finset.inter_subset_right Finset.inter_subset_right
  have hselectedCover : P = K.biUnion selectedFaces := by
    ext e
    constructor
    · intro heP
      have heH := hsub heP
      rw [hcover] at heH
      rcases Finset.mem_biUnion.mp heH with ⟨Q, hQ, heQ⟩
      exact Finset.mem_biUnion.mpr ⟨Q, hQ, Finset.mem_inter.mpr ⟨heP, heQ⟩⟩
    · intro he
      rcases Finset.mem_biUnion.mp he with ⟨Q, _hQ, heQ⟩
      exact (Finset.mem_inter.mp heQ).1
  rw [hselectedCover, Finset.card_biUnion hselectedDisjoint]
  calc
    (∑ Q ∈ K, (selectedFaces Q).card) ≤ ∑ _Q ∈ K, 1 := by
      apply Finset.sum_le_sum
      intro Q hQ
      exact hselectedCard Q hQ
    _ = K.card := by simp
    _ = 5 := hKcard

/-- The ten-vertex form: the exact local two-triangle-link certificate both
supplies the twenty triples and forces the five-boundary decomposition. -/
theorem exists_five_tetrahedral_boundaries_of_twoTriangleLinks
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (H : Finset (Finset Point)) (hPoint : Fintype.card Point = 10)
    (hlinks : TwoTriangleLinks H) :
    ∃ K : Finset (Finset Point),
      K.card = 5 ∧
      (∀ Q ∈ K, Q.card = 4 ∧ Q.powersetCard 3 ⊆ H) ∧
      H = K.biUnion (fun Q => Q.powersetCard 3) ∧
      (K : Set (Finset Point)).PairwiseDisjoint
        (fun Q => Q.powersetCard 3) := by
  exact exists_five_tetrahedral_boundaries H hlinks.uniform
    (card_eq_twenty_of_twoTriangleLinks H hPoint hlinks) hlinks.completion

/-- Consequently every subfamily whose distinct triples meet in fewer than
two vertices has at most five members. -/
theorem card_le_five_of_twoTriangleLinks
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (H P : Finset (Finset Point)) (hPoint : Fintype.card Point = 10)
    (hlinks : TwoTriangleLinks H)
    (hsub : P ⊆ H)
    (hinter : ∀ e ∈ P, ∀ f ∈ P, e ≠ f → (e ∩ f).card < 2) :
    P.card ≤ 5 := by
  exact card_le_five_of_pairwise_inter_lt_two H P hlinks.uniform
    (card_eq_twenty_of_twoTriangleLinks H hPoint hlinks)
    hlinks.completion hsub hinter

end Erdos506.Finite
