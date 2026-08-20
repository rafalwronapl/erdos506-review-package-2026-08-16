import Erdos506.Incidence.RealProjectiveArrangementFaceThreeMinimalFinish
import Erdos506.Incidence.RealProjectiveOrdinaryEdgeTriangle
import Erdos506.Incidence.RealProjectiveArrangementGlobalFinish
import Erdos506.Incidence.RealPlaneEvenArrangementDerivation
import Erdos506.V1.TwelveGalleryDerivation
import Erdos506.V1.TwelveDirectionFinish

/-!
# The simplicial entrance to the twelve-point Type-A gallery

The restored Type-A defect is the Melchior slack of the restored pivot
configuration.  When it vanishes, the dual face defect vanishes.  The
signed face-excess identity and the unconditional three-side theorem then
force every actual dual face to be triangular.
-/

namespace Erdos506.Incidence

open scoped BigOperators

universe u

namespace FiniteProjectiveLineArrangement

noncomputable local instance galleryArrangementFaceFintype
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) : Fintype A.ArrangementFace :=
  A.arrangementFaceFintype

/-- Vanishing of the actual signed face defect makes every face triangular.
The proof uses no abstract cellulation: the exact boundary handshake gives
the signed sum, while the facet theorem makes each summand nonnegative. -/
theorem all_arrangementFaceBoundary_card_eq_three_of_signedFaceDefect_eq_zero
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (base : Line)
    (hdefect :
      2 * (Fintype.card A.GeometricEdge : ℤ) -
          3 * (Fintype.card A.ArrangementFace : ℤ) = 0) :
    ∀ F : A.ArrangementFace,
      (A.arrangementFaceBoundary F).card = 3 := by
  classical
  have hsum :
      (∑ F : A.ArrangementFace,
          A.arrangementFaceBoundarySignedExcess F) = 0 := by
    rw [A.sum_arrangementFaceBoundarySignedExcess_eq hA, hdefect]
  have hnonneg (F : A.ArrangementFace) :
      0 ≤ A.arrangementFaceBoundarySignedExcess F := by
    have hthree : 3 ≤ (A.arrangementFaceBoundary F).card :=
      A.three_le_arrangementFaceBoundary_card hA base F
    unfold arrangementFaceBoundarySignedExcess
    omega
  intro F
  have hle :
      A.arrangementFaceBoundarySignedExcess F ≤
        ∑ G : A.ArrangementFace,
          A.arrangementFaceBoundarySignedExcess G :=
    Finset.single_le_sum
      (fun G _hG => hnonneg G) (Finset.mem_univ F)
  rw [hsum] at hle
  have hzero : A.arrangementFaceBoundarySignedExcess F = 0 := by
    exact le_antisymm hle (hnonneg F)
  have hthree : 3 ≤ (A.arrangementFaceBoundary F).card :=
    A.three_le_arrangementFaceBoundary_card hA base F
  unfold arrangementFaceBoundarySignedExcess at hzero
  omega

/-- The multiplicity word on one arrangement line, written in the canonical
positive cyclic labelling already supplied by the projective successor API. -/
noncomputable def cyclicLineVertexMultiplicity
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (i : Fin (Fintype.card (A.CircularGapSlot l))) : ℕ :=
  A.multiplicity (A.circularGapCyclicLabel l i).1

/-- One letter-step in the cyclic multiplicity word is literally the
geometric positive successor of the corresponding marked vertex.  This is
the lossless successor/word bridge needed before the finite `TTDTDTD`
classification; no arbitrary enumeration is introduced. -/
theorem cyclicLineVertexMultiplicity_finRotate_eq_successor
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (i : Fin (Fintype.card (A.CircularGapSlot l))) :
    A.cyclicLineVertexMultiplicity l
        (finRotate (Fintype.card (A.CircularGapSlot l)) i) =
      A.multiplicity
        (A.circularGapSuccessor l (A.circularGapCyclicLabel l i)).1 := by
  unfold cyclicLineVertexMultiplicity
  rw [A.circularGapSuccessor_apply_label l i]

/-- If every indexed line except `l` passes through `q`, then `q` has at
least `|Line| - 1` incident arrangement lines.  This is the finite incidence
part of the ordinary--ordinary edge obstruction; its remaining input is the
geometric fact that such an edge forces this near-pencil configuration. -/
theorem card_sub_one_le_multiplicity_of_incident_away
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (q : RealProjectivePoint)
    (haway : ∀ m : Line, m ≠ l → A.Incident q m) :
    Fintype.card Line - 1 ≤ A.multiplicity q := by
  classical
  unfold multiplicity
  have hsub : (Finset.univ.erase l : Finset Line) ⊆
      Finset.univ.filter fun m => A.Incident q m := by
    intro m hm
    have hm' := Finset.mem_erase.mp hm
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, haway m hm'.1⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ] at hcard
  exact hcard

/-- A twelve-line arrangement whose actual vertices all have multiplicity
at most five cannot be a near-pencil after deleting one distinguished line.
This is the exact numerical contradiction needed after the geometric `DD`
edge lemma: eleven concurrent lines would give multiplicity at least eleven. -/
theorem no_concurrent_away_of_card_twelve_of_vertex_multiplicity_le_five
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line)
    (hcard : Fintype.card Line = 12)
    (hcap : ∀ q ∈ A.vertexSet, A.multiplicity q ≤ 5)
    (l : Line) :
    ¬ ∃ q : RealProjectivePoint,
      ∀ m : Line, m ≠ l → A.Incident q m := by
  rintro ⟨q, haway⟩
  have hlow := A.card_sub_one_le_multiplicity_of_incident_away l q haway
  have htwo : 2 ≤ A.multiplicity q := by omega
  have hq : q ∈ A.vertexSet :=
    (A.mem_vertexSet_iff_two_le_multiplicity q).2 htwo
  have hupp := hcap q hq
  omega

/-- Once the geometric `DD`-edge lemma supplies concurrency away from the
supporting line, the actual cyclic successor word has no adjacent ordinary
vertices.  This deliberately isolates the sole geometric seam from the
finite near-pencil contradiction above. -/
theorem cyclicLineVertexMultiplicity_no_adjacent_of_dd_forces_concurrent_away
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line)
    (hcard : Fintype.card Line = 12)
    (hcap : ∀ q ∈ A.vertexSet, A.multiplicity q ≤ 5)
    (l : Line)
    (hDD : ∀ i : Fin (Fintype.card (A.CircularGapSlot l)),
      A.cyclicLineVertexMultiplicity l i = 2 →
      A.multiplicity
          (A.circularGapSuccessor l (A.circularGapCyclicLabel l i)).1 = 2 →
      ∃ q : RealProjectivePoint,
        ∀ m : Line, m ≠ l → A.Incident q m) :
    ∀ i, A.cyclicLineVertexMultiplicity l i = 2 →
      A.cyclicLineVertexMultiplicity l
          (finRotate (Fintype.card (A.CircularGapSlot l)) i) ≠ 2 := by
  intro i hi hnext
  have hsuccessor :
      A.multiplicity
          (A.circularGapSuccessor l (A.circularGapCyclicLabel l i)).1 = 2 := by
    rw [← A.cyclicLineVertexMultiplicity_finRotate_eq_successor l i]
    exact hnext
  exact (A.no_concurrent_away_of_card_twelve_of_vertex_multiplicity_le_five
    hcard hcap l) (hDD i hi hsuccessor)

/-- Actual no-`DD` theorem.  Simpliciality supplies the two triangular
incident faces, the ordinary-edge sector lemma forces a near-pencil, and
the twelve-line multiplicity cap excludes that near-pencil. -/
theorem cyclicLineVertexMultiplicity_no_adjacent_of_all_faces_triangular
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (hcard : Fintype.card Line = 12)
    (hcap : ∀ q ∈ A.vertexSet, A.multiplicity q ≤ 5)
    (l : Line)
    (htri : ∀ F : A.ArrangementFace,
      (A.arrangementFaceBoundary F).card = 3) :
    ∀ i, A.cyclicLineVertexMultiplicity l i = 2 →
      A.cyclicLineVertexMultiplicity l
          (finRotate (Fintype.card (A.CircularGapSlot l)) i) ≠ 2 := by
  apply A.cyclicLineVertexMultiplicity_no_adjacent_of_dd_forces_concurrent_away
    hcard hcap l
  intro i hi hnext
  apply A.exists_concurrent_away_of_circularGap_dd_of_all_faces_triangular
    hA l (A.circularGapCyclicLabel l i)
  · simpa only [cyclicLineVertexMultiplicity] using hi
  · exact hnext
  · exact htri

end FiniteProjectiveLineArrangement

end Erdos506.Incidence

namespace Erdos506.V1

open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.Incidence.FiniteProjectiveLineArrangement
open Erdos506.V4

/-- Rotation by `k` letters in a seven-letter cyclic word. -/
def gallerySevenShift (r : Fin 7) (k : ℕ) : Fin 7 :=
  (finRotate 7)^[k] r

/-- A numerical cyclic word is `TTDTDTD`, up to choice of its first
letter; `T` is represented by multiplicity three and `D` by multiplicity
two. -/
def IsTTDTDTD (word : Fin 7 → ℕ) : Prop :=
  ∃ r : Fin 7,
    word (gallerySevenShift r 0) = 3 ∧
    word (gallerySevenShift r 1) = 3 ∧
    word (gallerySevenShift r 2) = 2 ∧
    word (gallerySevenShift r 3) = 3 ∧
    word (gallerySevenShift r 4) = 2 ∧
    word (gallerySevenShift r 5) = 3 ∧
    word (gallerySevenShift r 6) = 2

/-- Positions of the four triple vertices when the unique `TT` gap is cut
open and the remaining gallery is read as a strip. -/
def fourStripRungPosition : Fin 4 → Fin 7 := ![1, 3, 5, 0]

/-- Positions of the three ordinary vertices between consecutive strip
rungs. -/
def fourStripSingletonPosition : Fin 3 → Fin 7 := ![2, 4, 6]

def fourStripLabelPosition : GalleryLineLabel → Fin 7
  | .inl (.inl i) => fourStripRungPosition i
  | .inl (.inr i) => fourStripRungPosition i
  | .inr i => fourStripSingletonPosition i

private theorem gallerySevenShift_fin_injective (r : Fin 7) :
    Function.Injective (fun i : Fin 7 => gallerySevenShift r i.1) := by
  intro i j hij
  fin_cases r <;> fin_cases i <;> fin_cases j <;>
    simp [gallerySevenShift, Function.iterate_succ_apply] at hij ⊢

private theorem gallerySevenShift_finRotate (r i : Fin 7) :
    finRotate 7 (gallerySevenShift r i.1) =
      gallerySevenShift r (finRotate 7 i).1 := by
  fin_cases r <;> fin_cases i <;>
    rfl

/-- The three geometrically extracted `T-D-T` steps, already oriented into
two coherent rails.  This is the lossless intermediate object between the
cyclic word and `LabelledFourStripGalleryEntrance`. -/
structure LabelledFourStripGallerySteps
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) (ell : Line) where
  vertexEquiv : Fin 7 ≃ A.CircularGapSlot ell
  successor_apply : ∀ i,
    A.circularGapSuccessor ell (vertexEquiv i) =
      vertexEquiv (finRotate 7 i)
  rungMultiplicity : ∀ i : Fin 4,
    A.multiplicity (vertexEquiv (fourStripRungPosition i)).1 = 3
  singletonMultiplicity : ∀ i : Fin 3,
    A.multiplicity (vertexEquiv (fourStripSingletonPosition i)).1 = 2
  step0 : A.OrdinaryTDTGalleryStep ell (vertexEquiv 2)
  step1 : A.OrdinaryTDTGalleryStep ell (vertexEquiv 4)
  step2 : A.OrdinaryTDTGalleryStep ell (vertexEquiv 6)
  align01Upper : step0.successorUpper = step1.predecessorUpper
  align01Lower : step0.successorLower = step1.predecessorLower
  align12Upper : step1.successorUpper = step2.predecessorUpper
  align12Lower : step1.successorLower = step2.predecessorLower

private theorem exists_labelledFourStripGallerySteps_of_indexed_word
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (ell : Line) (V : Fin 7 ≃ A.CircularGapSlot ell)
    (hVsuccessor : ∀ i : Fin 7,
      A.circularGapSuccessor ell (V i) = V (finRotate 7 i))
    (hrung : ∀ i : Fin 4,
      A.multiplicity (V (fourStripRungPosition i)).1 = 3)
    (hsingleton : ∀ i : Fin 3,
      A.multiplicity (V (fourStripSingletonPosition i)).1 = 2)
    (htri : ∀ F : A.ArrangementFace,
      (A.arrangementFaceBoundary F).card = 3)
    (hnoConcurrent : ∀ l : Line, ¬ ∃ q : RealProjectivePoint,
      ∀ m : Line, m ≠ l → A.Incident q m) :
    Nonempty (LabelledFourStripGallerySteps A ell) := by
  let S0 : A.OrdinaryTDTGalleryStep ell (V 2) :=
    Classical.choice (A.exists_ordinaryTDTGalleryStep
      hA ell (V 2) (by simpa [fourStripSingletonPosition] using hsingleton 0)
        htri hnoConcurrent)
  let S1 : A.OrdinaryTDTGalleryStep ell (V 4) :=
    Classical.choice (A.exists_ordinaryTDTGalleryStep
      hA ell (V 4) (by simpa [fourStripSingletonPosition] using hsingleton 1)
        htri hnoConcurrent)
  let S2 : A.OrdinaryTDTGalleryStep ell (V 6) :=
    Classical.choice (A.exists_ordinaryTDTGalleryStep
      hA ell (V 6) (by simpa [fourStripSingletonPosition] using hsingleton 2)
        htri hnoConcurrent)
  have hs23 : A.circularGapSuccessor ell (V 2) = V 3 := by
    simpa using hVsuccessor 2
  have hs34 : A.circularGapSuccessor ell (V 3) = V 4 := by
    simpa using hVsuccessor 3
  have hp4 : A.circularGapPredecessor ell (V 4) = V 3 := by
    rw [← hs34]
    exact A.circularGapPredecessor_successor ell (V 3)
  have hmatch01 := S0.shared_triple_matching A ell (V 2) (V 4) S1
    (congrArg Subtype.val (hs23.trans hp4.symm))
    (by rw [hs23]; simpa [fourStripRungPosition] using hrung 1)
  obtain ⟨T1, h01U, h01L⟩ :
      ∃ T : A.OrdinaryTDTGalleryStep ell (V 4),
        S0.successorUpper = T.predecessorUpper ∧
          S0.successorLower = T.predecessorLower := by
    rcases hmatch01 with hmatch01 | hmatch01
    · exact ⟨S1, hmatch01⟩
    · exact ⟨S1.swap, hmatch01⟩
  have hs45 : A.circularGapSuccessor ell (V 4) = V 5 := by
    simpa using hVsuccessor 4
  have hs56 : A.circularGapSuccessor ell (V 5) = V 6 := by
    simpa using hVsuccessor 5
  have hp6 : A.circularGapPredecessor ell (V 6) = V 5 := by
    rw [← hs56]
    exact A.circularGapPredecessor_successor ell (V 5)
  have hmatch12 := T1.shared_triple_matching A ell (V 4) (V 6) S2
    (congrArg Subtype.val (hs45.trans hp6.symm))
    (by rw [hs45]; simpa [fourStripRungPosition] using hrung 2)
  obtain ⟨T2, h12U, h12L⟩ :
      ∃ T : A.OrdinaryTDTGalleryStep ell (V 6),
        T1.successorUpper = T.predecessorUpper ∧
          T1.successorLower = T.predecessorLower := by
    rcases hmatch12 with hmatch12 | hmatch12
    · exact ⟨S2, hmatch12⟩
    · exact ⟨S2.swap, hmatch12⟩
  exact ⟨{
    vertexEquiv := V
    successor_apply := hVsuccessor
    rungMultiplicity := hrung
    singletonMultiplicity := hsingleton
    step0 := S0
    step1 := T1
    step2 := T2
    align01Upper := h01U
    align01Lower := h01L
    align12Upper := h12U
    align12Lower := h12L
  }⟩

/-- The actual `TTDTDTD` word and triangular-face geometry construct three
coherently oriented strip steps. -/
theorem exists_labelledFourStripGallerySteps_of_isTTDTDTD
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (ell : Line)
    (hgapCard : Fintype.card (A.CircularGapSlot ell) = 7)
    (hword : IsTTDTDTD (fun i : Fin 7 =>
      A.multiplicity (A.circularGapCyclicLabelSeven ell hgapCard i).1))
    (htri : ∀ F : A.ArrangementFace,
      (A.arrangementFaceBoundary F).card = 3)
    (hnoConcurrent : ∀ l : Line, ¬ ∃ q : RealProjectivePoint,
      ∀ m : Line, m ≠ l → A.Incident q m) :
    Nonempty (LabelledFourStripGallerySteps A ell) := by
  classical
  rcases hword with ⟨r, h0, h1, h2, h3, h4, h5, h6⟩
  let E := A.circularGapCyclicLabelSeven ell hgapCard
  let rotateFrom : Fin 7 → Fin 7 := fun i => gallerySevenShift r i.1
  have hrotateInj : Function.Injective rotateFrom := by
    exact gallerySevenShift_fin_injective r
  let R : Fin 7 ≃ Fin 7 := Equiv.ofBijective rotateFrom
    ⟨hrotateInj, Finite.injective_iff_surjective.mp hrotateInj⟩
  let V : Fin 7 ≃ A.CircularGapSlot ell := R.trans E
  have hV (i : Fin 7) : V i = E (gallerySevenShift r i.1) := by
    rfl
  have hVsuccessor : ∀ i : Fin 7,
      A.circularGapSuccessor ell (V i) = V (finRotate 7 i) := by
    intro i
    rw [hV i, hV (finRotate 7 i)]
    rw [A.circularGapSuccessor_apply_labelSeven]
    exact congrArg E (gallerySevenShift_finRotate r i)
  have hrung : ∀ i : Fin 4,
      A.multiplicity (V (fourStripRungPosition i)).1 = 3 := by
    intro i
    fin_cases i
    · simpa [fourStripRungPosition, hV] using h1
    · simpa [fourStripRungPosition, hV] using h3
    · simpa [fourStripRungPosition, hV] using h5
    · simpa [fourStripRungPosition, hV] using h0
  have hsingleton : ∀ i : Fin 3,
      A.multiplicity (V (fourStripSingletonPosition i)).1 = 2 := by
    intro i
    fin_cases i
    · simpa [fourStripSingletonPosition, hV] using h2
    · simpa [fourStripSingletonPosition, hV] using h4
    · simpa [fourStripSingletonPosition, hV] using h6
  exact exists_labelledFourStripGallerySteps_of_indexed_word
    A hA ell V hVsuccessor hrung hsingleton htri hnoConcurrent

def LabelledFourStripGallerySteps.a
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell) : Fin 4 → Line :=
  ![G.step0.predecessorUpper, G.step0.successorUpper,
    G.step1.successorUpper, G.step2.successorUpper]

def LabelledFourStripGallerySteps.b
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell) : Fin 4 → Line :=
  ![G.step0.predecessorLower, G.step0.successorLower,
    G.step1.successorLower, G.step2.successorLower]

def LabelledFourStripGallerySteps.c
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell) : Fin 3 → Line :=
  ![G.step0.c, G.step1.c, G.step2.c]

def LabelledFourStripGallerySteps.rungSlot
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell) (i : Fin 4) :
    A.CircularGapSlot ell :=
  G.vertexEquiv (fourStripRungPosition i)

def LabelledFourStripGallerySteps.singletonSlot
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell) (i : Fin 3) :
    A.CircularGapSlot ell :=
  G.vertexEquiv (fourStripSingletonPosition i)

@[simp]
theorem LabelledFourStripGallerySteps.predecessor_singletonSlot
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell) (i : Fin 3) :
    A.circularGapPredecessor ell (G.singletonSlot i) =
      G.rungSlot (galleryStripLeft i) := by
  fin_cases i
  · have h : A.circularGapSuccessor ell (G.vertexEquiv 1) =
        G.vertexEquiv 2 := by
      simpa [finRotate_apply] using G.successor_apply 1
    change A.circularGapPredecessor ell (G.vertexEquiv 2) =
      G.vertexEquiv 1
    rw [← h]
    exact A.circularGapPredecessor_successor ell _
  · have h : A.circularGapSuccessor ell (G.vertexEquiv 3) =
        G.vertexEquiv 4 := by
      simpa [finRotate_apply] using G.successor_apply 3
    change A.circularGapPredecessor ell (G.vertexEquiv 4) =
      G.vertexEquiv 3
    rw [← h]
    exact A.circularGapPredecessor_successor ell _
  · have h : A.circularGapSuccessor ell (G.vertexEquiv 5) =
        G.vertexEquiv 6 := by
      simpa [finRotate_apply] using G.successor_apply 5
    change A.circularGapPredecessor ell (G.vertexEquiv 6) =
      G.vertexEquiv 5
    rw [← h]
    exact A.circularGapPredecessor_successor ell _

@[simp]
theorem LabelledFourStripGallerySteps.successor_singletonSlot
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell) (i : Fin 3) :
    A.circularGapSuccessor ell (G.singletonSlot i) =
      G.rungSlot (galleryStripRight i) := by
  fin_cases i
  · simpa [LabelledFourStripGallerySteps.singletonSlot,
      LabelledFourStripGallerySteps.rungSlot, fourStripSingletonPosition,
      fourStripRungPosition, galleryStripRight] using G.successor_apply 2
  · simpa [LabelledFourStripGallerySteps.singletonSlot,
      LabelledFourStripGallerySteps.rungSlot, fourStripSingletonPosition,
      fourStripRungPosition, galleryStripRight] using G.successor_apply 4
  · simpa [LabelledFourStripGallerySteps.singletonSlot,
      LabelledFourStripGallerySteps.rungSlot, fourStripSingletonPosition,
      fourStripRungPosition, galleryStripRight] using G.successor_apply 6

theorem LabelledFourStripGallerySteps.intersection_a
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell) (i : Fin 4) :
    A.intersection ell (G.a i) = (G.rungSlot i).1 := by
  fin_cases i
  · exact G.step0.predecessorUpper_point.trans
      (congrArg Subtype.val (G.predecessor_singletonSlot 0))
  · exact G.step0.successorUpper_point.trans
      (congrArg Subtype.val (G.successor_singletonSlot 0))
  · exact G.step1.successorUpper_point.trans
      (congrArg Subtype.val (G.successor_singletonSlot 1))
  · exact G.step2.successorUpper_point.trans
      (congrArg Subtype.val (G.successor_singletonSlot 2))

theorem LabelledFourStripGallerySteps.intersection_b
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell) (i : Fin 4) :
    A.intersection ell (G.b i) = (G.rungSlot i).1 := by
  fin_cases i
  · exact G.step0.predecessorLower_point.trans
      (congrArg Subtype.val (G.predecessor_singletonSlot 0))
  · exact G.step0.successorLower_point.trans
      (congrArg Subtype.val (G.successor_singletonSlot 0))
  · exact G.step1.successorLower_point.trans
      (congrArg Subtype.val (G.successor_singletonSlot 1))
  · exact G.step2.successorLower_point.trans
      (congrArg Subtype.val (G.successor_singletonSlot 2))

theorem LabelledFourStripGallerySteps.intersection_c
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell) (i : Fin 3) :
    A.intersection ell (G.c i) = (G.singletonSlot i).1 := by
  fin_cases i
  · symm
    apply A.eq_intersection_of_incident G.step0.c_ne_ell.symm
    · exact (G.step0.singletonIncident_iff ell).2 (Or.inl rfl)
    · exact (G.step0.singletonIncident_iff G.step0.c).2 (Or.inr rfl)
  · symm
    apply A.eq_intersection_of_incident G.step1.c_ne_ell.symm
    · exact (G.step1.singletonIncident_iff ell).2 (Or.inl rfl)
    · exact (G.step1.singletonIncident_iff G.step1.c).2 (Or.inr rfl)
  · symm
    apply A.eq_intersection_of_incident G.step2.c_ne_ell.symm
    · exact (G.step2.singletonIncident_iff ell).2 (Or.inl rfl)
    · exact (G.step2.singletonIncident_iff G.step2.c).2 (Or.inr rfl)

@[simp]
theorem LabelledFourStripGallerySteps.a_ne_ell
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell) (i : Fin 4) :
    G.a i ≠ ell := by
  fin_cases i
  · exact G.step0.predecessorUpper_ne_ell
  · exact G.step0.successorUpper_ne_ell
  · exact G.step1.successorUpper_ne_ell
  · exact G.step2.successorUpper_ne_ell

@[simp]
theorem LabelledFourStripGallerySteps.b_ne_ell
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell) (i : Fin 4) :
    G.b i ≠ ell := by
  fin_cases i
  · exact G.step0.predecessorLower_ne_ell
  · exact G.step0.successorLower_ne_ell
  · exact G.step1.successorLower_ne_ell
  · exact G.step2.successorLower_ne_ell

@[simp]
theorem LabelledFourStripGallerySteps.c_ne_ell
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell) (i : Fin 3) :
    G.c i ≠ ell := by
  fin_cases i
  · exact G.step0.c_ne_ell
  · exact G.step1.c_ne_ell
  · exact G.step2.c_ne_ell

theorem LabelledFourStripGallerySteps.a_ne_b
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell) (i : Fin 4) :
    G.a i ≠ G.b i := by
  fin_cases i
  · exact G.step0.predecessor_ne
  · exact G.step0.successor_ne
  · exact G.step1.successor_ne
  · exact G.step2.successor_ne

theorem LabelledFourStripGallerySteps.rungIncident_iff
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell) (i : Fin 4) (m : Line) :
    A.Incident (G.rungSlot i).1 m ↔
      m = ell ∨ m = G.a i ∨ m = G.b i := by
  have hrell : A.Incident (G.rungSlot i).1 ell :=
    ((A.mem_lineVertexSet ell).1 (G.rungSlot i).2).2
  have hra : A.Incident (G.rungSlot i).1 (G.a i) := by
    rw [← G.intersection_a i]
    exact A.intersection_incident_right (G.a_ne_ell i).symm
  have hrb : A.Incident (G.rungSlot i).1 (G.b i) := by
    rw [← G.intersection_b i]
    exact A.intersection_incident_right (G.b_ne_ell i).symm
  exact A.incident_iff_eq_or_eq_or_eq_of_multiplicity_eq_three
    (G.rungSlot i).1 ell (G.a i) (G.b i) hrell hra hrb
      (G.a_ne_ell i).symm (G.b_ne_ell i).symm (G.a_ne_b i)
        (G.rungMultiplicity i) m

theorem LabelledFourStripGallerySteps.singletonIncident_iff
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell) (i : Fin 3) (m : Line) :
    A.Incident (G.singletonSlot i).1 m ↔ m = ell ∨ m = G.c i := by
  fin_cases i
  · exact G.step0.singletonIncident_iff m
  · exact G.step1.singletonIncident_iff m
  · exact G.step2.singletonIncident_iff m

def LabelledFourStripGallerySteps.upperVertex
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell) :
    Fin 3 → RealProjectivePoint :=
  ![G.step0.upperVertex, G.step1.upperVertex, G.step2.upperVertex]

def LabelledFourStripGallerySteps.lowerVertex
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell) :
    Fin 3 → RealProjectivePoint :=
  ![G.step0.lowerVertex, G.step1.lowerVertex, G.step2.lowerVertex]

theorem LabelledFourStripGallerySteps.upperIncidence
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell) (i : Fin 3) :
    A.Incident (G.upperVertex i) (G.a (galleryStripLeft i)) ∧
    A.Incident (G.upperVertex i) (G.a (galleryStripRight i)) ∧
    A.Incident (G.upperVertex i) (G.c i) := by
  fin_cases i
  · exact ⟨G.step0.upperIncidence.2.1,
      G.step0.upperIncidence.2.2, G.step0.upperIncidence.1⟩
  · change A.Incident G.step1.upperVertex G.step0.successorUpper ∧
      A.Incident G.step1.upperVertex G.step1.successorUpper ∧
      A.Incident G.step1.upperVertex G.step1.c
    rw [G.align01Upper]
    exact ⟨G.step1.upperIncidence.2.1,
      G.step1.upperIncidence.2.2, G.step1.upperIncidence.1⟩
  · change A.Incident G.step2.upperVertex G.step1.successorUpper ∧
      A.Incident G.step2.upperVertex G.step2.successorUpper ∧
      A.Incident G.step2.upperVertex G.step2.c
    rw [G.align12Upper]
    exact ⟨G.step2.upperIncidence.2.1,
      G.step2.upperIncidence.2.2, G.step2.upperIncidence.1⟩

theorem LabelledFourStripGallerySteps.lowerIncidence
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell) (i : Fin 3) :
    A.Incident (G.lowerVertex i) (G.b (galleryStripLeft i)) ∧
    A.Incident (G.lowerVertex i) (G.b (galleryStripRight i)) ∧
    A.Incident (G.lowerVertex i) (G.c i) := by
  fin_cases i
  · exact ⟨G.step0.lowerIncidence.2.1,
      G.step0.lowerIncidence.2.2, G.step0.lowerIncidence.1⟩
  · change A.Incident G.step1.lowerVertex G.step0.successorLower ∧
      A.Incident G.step1.lowerVertex G.step1.successorLower ∧
      A.Incident G.step1.lowerVertex G.step1.c
    rw [G.align01Lower]
    exact ⟨G.step1.lowerIncidence.2.1,
      G.step1.lowerIncidence.2.2, G.step1.lowerIncidence.1⟩
  · change A.Incident G.step2.lowerVertex G.step1.successorLower ∧
      A.Incident G.step2.lowerVertex G.step2.successorLower ∧
      A.Incident G.step2.lowerVertex G.step2.c
    rw [G.align12Lower]
    exact ⟨G.step2.lowerIncidence.2.1,
      G.step2.lowerIncidence.2.2, G.step2.lowerIncidence.1⟩

def LabelledFourStripGallerySteps.line
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell) : GalleryLineLabel → Line
  | .inl (.inl i) => G.a i
  | .inl (.inr i) => G.b i
  | .inr i => G.c i

def LabelledFourStripGallerySteps.slot
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell) (s : GalleryLineLabel) :
    A.CircularGapSlot ell :=
  G.vertexEquiv (fourStripLabelPosition s)

theorem LabelledFourStripGallerySteps.intersection_line
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell) (s : GalleryLineLabel) :
    A.intersection ell (G.line s) = (G.slot s).1 := by
  rcases s with (i | i) | i
  · exact G.intersection_a i
  · exact G.intersection_b i
  · exact G.intersection_c i

@[simp]
theorem LabelledFourStripGallerySteps.line_ne_ell
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell) (s : GalleryLineLabel) :
    G.line s ≠ ell := by
  rcases s with (i | i) | i
  · exact G.a_ne_ell i
  · exact G.b_ne_ell i
  · exact G.c_ne_ell i

theorem LabelledFourStripGallerySteps.line_injective
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell) :
    Function.Injective G.line := by
  intro s t hst
  have hslotVal : (G.slot s).1 = (G.slot t).1 := by
    calc
      (G.slot s).1 = A.intersection ell (G.line s) :=
        (G.intersection_line s).symm
      _ = A.intersection ell (G.line t) := congrArg _ hst
      _ = (G.slot t).1 := G.intersection_line t
  have hpos : fourStripLabelPosition s = fourStripLabelPosition t :=
    G.vertexEquiv.injective (Subtype.ext hslotVal)
  have hne0 := G.a_ne_b 0
  have hne1 := G.a_ne_b 1
  have hne2 := G.a_ne_b 2
  have hne3 := G.a_ne_b 3
  rcases s with (si | si) | si <;> rcases t with (ti | ti) | ti
  all_goals
    fin_cases si <;> fin_cases ti <;>
      simp_all [fourStripLabelPosition, fourStripRungPosition,
        fourStripSingletonPosition, LabelledFourStripGallerySteps.line,
        LabelledFourStripGallerySteps.a, LabelledFourStripGallerySteps.b,
        LabelledFourStripGallerySteps.c]

noncomputable def LabelledFourStripGallerySteps.lineEquiv
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell)
    (hcard : Fintype.card Line = 12) :
    GalleryLineLabel ≃ {m : Line // m ≠ ell} := by
  let f : GalleryLineLabel → {m : Line // m ≠ ell} :=
    fun s => ⟨G.line s, G.line_ne_ell s⟩
  have hinj : Function.Injective f := by
    intro s t hst
    apply G.line_injective
    exact congrArg Subtype.val hst
  have hcards : Fintype.card GalleryLineLabel =
      Fintype.card {m : Line // m ≠ ell} := by
    simp [GalleryLineLabel, Fintype.card_subtype_compl, hcard]
  exact Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcards⟩)

@[simp]
theorem LabelledFourStripGallerySteps.lineEquiv_apply_val
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell)
    (hcard : Fintype.card Line = 12) (s : GalleryLineLabel) :
    (G.lineEquiv hcard s).1 = G.line s :=
  rfl

/-- Forgetting the temporary cyclic-step coordinates gives precisely the
finite entrance consumed by the cut-saturation module. -/
noncomputable def LabelledFourStripGallerySteps.toEntrance
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : LabelledFourStripGallerySteps A ell)
    (hcard : Fintype.card Line = 12) :
    A.LabelledFourStripGalleryEntrance ell where
  lineEquiv := G.lineEquiv hcard
  rungVertex := fun i => (G.rungSlot i).1
  singletonVertex := fun i => (G.singletonSlot i).1
  upperVertex := G.upperVertex
  lowerVertex := G.lowerVertex
  rungIncident_iff := by
    intro i m
    simpa [LabelledFourStripGallerySteps.line] using G.rungIncident_iff i m
  singletonIncident_iff := by
    intro i m
    simpa [LabelledFourStripGallerySteps.line] using
      G.singletonIncident_iff i m
  upperIncidence := by
    intro i
    simpa [LabelledFourStripGallerySteps.line] using G.upperIncidence i
  lowerIncidence := by
    intro i
    simpa [LabelledFourStripGallerySteps.line] using G.lowerIncidence i

/-- Full arrangement-level entrance extractor from the actual seven-letter
word.  No finite cut certificate is assumed here. -/
theorem exists_labelledFourStripGalleryEntrance_of_isTTDTDTD
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (hcard : Fintype.card Line = 12) (ell : Line)
    (hgapCard : Fintype.card (A.CircularGapSlot ell) = 7)
    (hword : IsTTDTDTD (fun i : Fin 7 =>
      A.multiplicity (A.circularGapCyclicLabelSeven ell hgapCard i).1))
    (htri : ∀ F : A.ArrangementFace,
      (A.arrangementFaceBoundary F).card = 3)
    (hnoConcurrent : ∀ l : Line, ¬ ∃ q : RealProjectivePoint,
      ∀ m : Line, m ≠ l → A.Incident q m) :
    Nonempty (A.LabelledFourStripGalleryEntrance ell) := by
  obtain ⟨G⟩ := exists_labelledFourStripGallerySteps_of_isTTDTDTD
    A hA ell hgapCard hword htri hnoConcurrent
  exact ⟨G.toEntrance hcard⟩

private theorem cycleSeven_independent_three_bits
    (a0 a1 a2 a3 a4 a5 a6 : ℕ)
    (h0 : a0 ≤ 1) (h1 : a1 ≤ 1) (h2 : a2 ≤ 1)
    (h3 : a3 ≤ 1) (h4 : a4 ≤ 1) (h5 : a5 ≤ 1)
    (h6 : a6 ≤ 1)
    (hsum : a0 + a1 + a2 + a3 + a4 + a5 + a6 = 3)
    (h01 : a0 + a1 ≤ 1) (h12 : a1 + a2 ≤ 1)
    (h23 : a2 + a3 ≤ 1) (h34 : a3 + a4 ≤ 1)
    (h45 : a4 + a5 ≤ 1) (h56 : a5 + a6 ≤ 1)
    (h60 : a6 + a0 ≤ 1) :
    (a0 = 0 ∧ a1 = 0 ∧ a2 = 1 ∧ a3 = 0 ∧
      a4 = 1 ∧ a5 = 0 ∧ a6 = 1) ∨
    (a0 = 1 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 1 ∧
      a4 = 0 ∧ a5 = 1 ∧ a6 = 0) ∨
    (a0 = 0 ∧ a1 = 1 ∧ a2 = 0 ∧ a3 = 0 ∧
      a4 = 1 ∧ a5 = 0 ∧ a6 = 1) ∨
    (a0 = 1 ∧ a1 = 0 ∧ a2 = 1 ∧ a3 = 0 ∧
      a4 = 0 ∧ a5 = 1 ∧ a6 = 0) ∨
    (a0 = 0 ∧ a1 = 1 ∧ a2 = 0 ∧ a3 = 1 ∧
      a4 = 0 ∧ a5 = 0 ∧ a6 = 1) ∨
    (a0 = 1 ∧ a1 = 0 ∧ a2 = 1 ∧ a3 = 0 ∧
      a4 = 1 ∧ a5 = 0 ∧ a6 = 0) ∨
    (a0 = 0 ∧ a1 = 1 ∧ a2 = 0 ∧ a3 = 1 ∧
      a4 = 0 ∧ a5 = 1 ∧ a6 = 0) := by
  by_cases ha0 : a0 = 0
  · by_cases ha1 : a1 = 0
    · apply Or.inl
      omega
    · by_cases ha3 : a3 = 0
      · apply Or.inr
        apply Or.inr
        apply Or.inl
        omega
      · by_cases ha5 : a5 = 0
        · apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inl
          omega
        · apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          omega
  · by_cases ha2 : a2 = 0
    · apply Or.inr
      apply Or.inl
      omega
    · by_cases ha4 : a4 = 0
      · apply Or.inr
        apply Or.inr
        apply Or.inr
        apply Or.inl
        omega
      · apply Or.inr
        apply Or.inr
        apply Or.inr
        apply Or.inr
        apply Or.inr
        apply Or.inl
        omega

/-- The finite cyclic-word step in the gallery entrance.  A complete word
with three ordinary and four triple letters, and no adjacent ordinary
letters, is the unique cyclic pattern `TTDTDTD`. -/
theorem isTTDTDTD_of_three_ordinary_of_no_adjacent
    (word : Fin 7 → ℕ)
    (hcomplete : ∀ i, word i = 2 ∨ word i = 3)
    (hthree :
      ((Finset.univ : Finset (Fin 7)).filter fun i => word i = 2).card = 3)
    (hnoAdjacent : ∀ i, word i = 2 → word (finRotate 7 i) ≠ 2) :
    IsTTDTDTD word := by
  classical
  let d : Fin 7 → ℕ := fun i => if word i = 2 then 1 else 0
  have hcount : ∑ i : Fin 7, d i = 3 := by
    rw [← hthree, Finset.card_eq_sum_ones, Finset.sum_filter]
  have hcount' : d 0 + d 1 + d 2 + d 3 + d 4 + d 5 + d 6 = 3 := by
    simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, add_assoc]
      using hcount
  have hbit (i : Fin 7) : d i ≤ 1 := by
    simp only [d]
    split <;> omega
  have hadj (i : Fin 7) : d i + d (finRotate 7 i) ≤ 1 := by
    by_cases hi : word i = 2
    · have hn := hnoAdjacent i hi
      simp only [d, if_pos hi, if_neg hn]
      omega
    · simp only [d, if_neg hi]
      split <;> omega
  have hpatterns := cycleSeven_independent_three_bits
    (d 0) (d 1) (d 2) (d 3) (d 4) (d 5) (d 6)
    (hbit 0) (hbit 1) (hbit 2) (hbit 3) (hbit 4) (hbit 5) (hbit 6)
    hcount'
    (by simpa [finRotate_apply] using hadj 0)
    (by simpa [finRotate_apply] using hadj 1)
    (by simpa [finRotate_apply] using hadj 2)
    (by simpa [finRotate_apply] using hadj 3)
    (by simpa [finRotate_apply] using hadj 4)
    (by simpa [finRotate_apply] using hadj 5)
    (by simpa [finRotate_apply] using hadj 6)
  have hd0 (i : Fin 7) : d i = 0 ↔ word i ≠ 2 := by simp [d]
  have hd1 (i : Fin 7) : d i = 1 ↔ word i = 2 := by simp [d]
  simp only [hd0, hd1] at hpatterns
  have hc0 := hcomplete 0
  have hc1 := hcomplete 1
  have hc2 := hcomplete 2
  have hc3 := hcomplete 3
  have hc4 := hcomplete 4
  have hc5 := hcomplete 5
  have hc6 := hcomplete 6
  rcases hpatterns with hpat | hpat | hpat | hpat | hpat | hpat | hpat
  · refine ⟨0, ?_⟩
    simp_all [gallerySevenShift, Function.iterate_succ_apply, finRotate_apply]
  · refine ⟨1, ?_⟩
    simp_all [gallerySevenShift, Function.iterate_succ_apply, finRotate_apply]
  · refine ⟨2, ?_⟩
    simp_all [gallerySevenShift, Function.iterate_succ_apply, finRotate_apply]
  · refine ⟨3, ?_⟩
    simp_all [gallerySevenShift, Function.iterate_succ_apply, finRotate_apply]
  · refine ⟨4, ?_⟩
    simp_all [gallerySevenShift, Function.iterate_succ_apply, finRotate_apply]
  · refine ⟨5, ?_⟩
    simp_all [gallerySevenShift, Function.iterate_succ_apply, finRotate_apply]
  · refine ⟨6, ?_⟩
    simp_all [gallerySevenShift, Function.iterate_succ_apply, finRotate_apply]

/-- The restored twelve-line arrangement in the Type-A row cannot be a
near-pencil after removal of any one supporting line.  The block-size cap
and the absence of a size-six original line through the pivot give the
uniform dual multiplicity cap five; eleven concurrent lines contradict it. -/
theorem twelveGallery_typeA_restored_no_concurrent_away
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha)
    (hcard : Fintype.card alpha = 12)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (p : alpha)
    (hline6 : (blockSystem cfg).lineDegree 6 p = 0)
    (l : Option (Erdos506.V3.AwayFrom p)) :
    ¬ ∃ q : RealProjectivePoint,
      ∀ m : Option (Erdos506.V3.AwayFrom p), m ≠ l →
        (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident q m := by
  let A := labelDualArrangement (restoredPivotConfiguration cfg p)
  have hAcard : Fintype.card (Option (Erdos506.V3.AwayFrom p)) = 12 := by
    rw [Fintype.card_option, Erdos506.V3.card_awayFrom, hcard]
  apply A.no_concurrent_away_of_card_twelve_of_vertex_multiplicity_le_five
    hAcard
  intro q hq
  apply labelDualMultiplicity_restored_le_five_of_blockSizeCap_of_lineDegree_six_eq_zero
    cfg p hcap hline6
  simpa only [A, labelDualVertexSet] using hq

/-- A zero restored-pivot defect forces the actual labelled-dual arrangement
of the restored configuration to be simplicial.  The global input is used
only to identify Melchior slack with the actual face defect (through Euler);
the lower bound on face size is the unconditional facet theorem. -/
theorem restoredPivot_all_dual_faces_triangular_of_restoredKappa_eq_zero
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (H : RealProjectiveArrangementGlobalInput.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : 3 ≤ Fintype.card alpha) (p : alpha)
    (hkappa : (blockSystem cfg).restoredKappa p = 0) :
    ∀ F : (labelDualArrangement
        (restoredPivotConfiguration cfg p)).ArrangementFace,
      ((labelDualArrangement (restoredPivotConfiguration cfg p)).arrangementFaceBoundary F).card = 3 := by
  classical
  let restored := restoredPivotConfiguration cfg p
  let A := labelDualArrangement restored
  have hnon : Noncollinear restored := by
    simpa only [restored] using
      restoredPivotConfiguration_noncollinear cfg hadm hcard p
  have hA : A.NonPencil := by
    simpa only [A] using
      labelDualArrangement_nonPencil_of_noncollinear restored hnon
  letI : Fintype A.ArrangementFace := A.arrangementFaceFintype
  letI : DecidableEq A.GeometricEdge :=
    geometricEdgeDecidableEqForMelchiorDerivation A
  let C := labelDualProjectiveArrangementCellulation H restored hnon
  have hslack : lineMelchiorSlack restored = 0 := by
    rw [← restoredKappa_eq_lineMelchiorSlack cfg p]
    exact hkappa
  have hslackDefect :=
    lineMelchiorSlack_eq_dualFaceDefect restored C (fun _L => rfl)
  change lineMelchiorSlack restored =
      2 * (Fintype.card A.GeometricEdge : ℤ) -
        3 * (Fintype.card A.ArrangementFace : ℤ) at hslackDefect
  have hdefect :
      2 * (Fintype.card A.GeometricEdge : ℤ) -
          3 * (Fintype.card A.ArrangementFace : ℤ) = 0 :=
    hslackDefect.symm.trans hslack
  change ∀ F : A.ArrangementFace,
    (A.arrangementFaceBoundary F).card = 3
  exact A.all_arrangementFaceBoundary_card_eq_three_of_signedFaceDefect_eq_zero
    hA none hdefect

/-- The numerical Type-A gallery row has zero restored defect, hence its
restored pivot arrangement is an actual simplicial projective arrangement. -/
theorem twelveGallery_typeA_all_restoredPivot_dual_faces_triangular
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (H : RealProjectiveArrangementGlobalInput.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (Gram : RealPlaneTwelveGramPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : Fintype.card alpha = 12)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (p : alpha)
    (hd3 : (blockSystem cfg).blockDegree 3 p = 7)
    (hd4 : (blockSystem cfg).blockDegree 4 p = 10)
    (hd5 : (blockSystem cfg).blockDegree 5 p = 3)
    (hd6 : (blockSystem cfg).blockDegree 6 p = 0)
    (hl3 : (blockSystem cfg).lineDegree 3 p = 4)
    (hl4 : (blockSystem cfg).lineDegree 4 p = 0)
    (hl5 : (blockSystem cfg).lineDegree 5 p = 0)
    (hl6 : (blockSystem cfg).lineDegree 6 p = 0) :
    ∀ F : (labelDualArrangement
        (restoredPivotConfiguration cfg p)).ArrangementFace,
      ((labelDualArrangement (restoredPivotConfiguration cfg p)).arrangementFaceBoundary F).card = 3 := by
  let Mel : RealPlaneMelchiorPrinciple.{u} :=
    realPlaneMelchiorPrincipleOfGlobalInput H
  let EvenArr : RealPlaneEvenArrangementPrinciple.{u} :=
    realPlaneEvenArrangementPrincipleOfGlobalInput H
  have hkappa : (blockSystem cfg).restoredKappa p = 0 :=
    (twelveGallery_typeA_forces_local_defect
      Mel EvenArr Kelly Gram cfg hadm hcard hcap p
      hd3 hd4 hd5 hd6 hl3 hl4 hl5 hl6).2
  apply restoredPivot_all_dual_faces_triangular_of_restoredKappa_eq_zero
    H cfg hadm (by omega) p hkappa

/-- The actual distinguished dual line of a Type-A pivot has no cyclic
ordinary--ordinary gap.  This is the unconditional geometric endpoint of
the simplicial DD argument; the later labelled-gallery/Hall completion is
logically separate. -/
theorem twelveGallery_typeA_restoredPivot_no_adjacent_ordinary
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (H : RealProjectiveArrangementGlobalInput.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (Gram : RealPlaneTwelveGramPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : Fintype.card alpha = 12)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (p : alpha)
    (hd3 : (blockSystem cfg).blockDegree 3 p = 7)
    (hd4 : (blockSystem cfg).blockDegree 4 p = 10)
    (hd5 : (blockSystem cfg).blockDegree 5 p = 3)
    (hd6 : (blockSystem cfg).blockDegree 6 p = 0)
    (hl3 : (blockSystem cfg).lineDegree 3 p = 4)
    (hl4 : (blockSystem cfg).lineDegree 4 p = 0)
    (hl5 : (blockSystem cfg).lineDegree 5 p = 0)
    (hl6 : (blockSystem cfg).lineDegree 6 p = 0) :
    let A := labelDualArrangement (restoredPivotConfiguration cfg p)
    ∀ i : Fin (Fintype.card (A.CircularGapSlot none)),
      A.cyclicLineVertexMultiplicity none i = 2 →
      A.cyclicLineVertexMultiplicity none
          (finRotate (Fintype.card (A.CircularGapSlot none)) i) ≠ 2 := by
  classical
  let restored := restoredPivotConfiguration cfg p
  let A := labelDualArrangement restored
  have hnon : Noncollinear restored := by
    simpa only [restored] using
      restoredPivotConfiguration_noncollinear cfg hadm (by omega) p
  have hA : A.NonPencil := by
    simpa only [A] using
      labelDualArrangement_nonPencil_of_noncollinear restored hnon
  have hAcard : Fintype.card (Option (Erdos506.V3.AwayFrom p)) = 12 := by
    rw [Fintype.card_option, Erdos506.V3.card_awayFrom, hcard]
  have hAcap : ∀ q ∈ A.vertexSet, A.multiplicity q ≤ 5 := by
    intro q hq
    apply labelDualMultiplicity_restored_le_five_of_blockSizeCap_of_lineDegree_six_eq_zero
      cfg p hcap hl6
    simpa only [A, restored, labelDualVertexSet] using hq
  have htri : ∀ F : A.ArrangementFace,
      (A.arrangementFaceBoundary F).card = 3 := by
    simpa only [A, restored] using
      twelveGallery_typeA_all_restoredPivot_dual_faces_triangular
        H Kelly Gram cfg hadm hcard hcap p
          hd3 hd4 hd5 hd6 hl3 hl4 hl5 hl6
  change ∀ i : Fin (Fintype.card (A.CircularGapSlot none)),
    A.cyclicLineVertexMultiplicity none i = 2 →
    A.cyclicLineVertexMultiplicity none
      (finRotate (Fintype.card (A.CircularGapSlot none)) i) ≠ 2
  exact A.cyclicLineVertexMultiplicity_no_adjacent_of_all_faces_triangular
    hA hAcard hAcap none htri

end Erdos506.V1
