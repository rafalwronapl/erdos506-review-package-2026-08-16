import Erdos506.V1.TenFiveTwoPentagonGoldenAxis
import Erdos506.Finite.TwoPFourThreeMatching
import Erdos506.V1.PivotThreeLines

/-!
# The ordinary matching on the inverted two-pentagon link

This file is the finite transport layer between the labelled two-pentagon
endpoint and the nine vertices of the pivot inversion.  The configuration
cardinality is deliberately explicit: saturation itself only supplies the
two disjoint five-supports, while the fact that they exhaust the carrier is
the ten-point endpoint hypothesis.
-/

namespace Erdos506.V1

open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

namespace TenTwoPentagonSaturationData

variable {α : Type u} [Fintype α] [DecidableEq α]
  {cfg : Configuration α}

/-- The nine ordinary vertices, as actual labels away from the chosen first
pentagon pivot. -/
noncomputable def goldenAwayLabel
    (d : TenTwoPentagonSaturationData cfg) :
    GoldenOrdinaryVertex → AwayFrom d.pivot.1
  | .inl i =>
      ⟨(d.qLabel i).1.1, by
        intro h
        apply (d.qLabel i).2
        apply Subtype.ext
        exact h⟩
  | .inr i =>
      ⟨(d.secondLabel i).1, by
        intro h
        apply Finset.disjoint_left.mp d.base.supports_disjoint
          (by simpa only [d.base.exclusiveTrace_Γ_Ω] using d.pivot.2)
          (by
            rw [← h]
            simpa only [d.base.exclusiveTrace_Ω_Γ] using (d.secondLabel i).2)⟩

@[simp] theorem goldenAwayLabel_q
    (d : TenTwoPentagonSaturationData cfg) (i : Fin 4) :
    d.goldenAwayLabel (goldenQ i) =
      ⟨(d.qLabel i).1.1, by
        intro h
        apply (d.qLabel i).2
        apply Subtype.ext
        exact h⟩ := rfl

@[simp] theorem goldenAwayLabel_b
    (d : TenTwoPentagonSaturationData cfg) (i : Fin 5) :
    d.goldenAwayLabel (goldenB i) =
      ⟨(d.secondLabel i).1, by
        intro h
        apply d.pivot_not_mem_secondSupport
        rw [← h]
        exact d.secondLabel_mem_secondSupport i⟩ := rfl

theorem goldenB_ne (a b : Fin 5) (hab : a ≠ b) : goldenB a ≠ goldenB b := by
  intro h
  exact hab (Sum.inr.inj h)

theorem goldenQ_ne_goldenB (i : Fin 4) (k : Fin 5) :
    goldenQ i ≠ goldenB k := by simp [goldenQ, goldenB]

private theorem goldenAwayLabel_injective
    (d : TenTwoPentagonSaturationData cfg) :
    Function.Injective d.goldenAwayLabel := by
  intro x y hxy
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          have hAway := hxy
          change (⟨(d.qLabel i).1.1, by
              intro h
              apply (d.qLabel i).2
              exact Subtype.ext h⟩ : AwayFrom d.pivot.1) =
            ⟨(d.qLabel j).1.1, by
              intro h
              apply (d.qLabel j).2
              exact Subtype.ext h⟩ at hAway
          have hval : (d.qLabel i).1.1 = (d.qLabel j).1.1 :=
            congrArg (fun z : AwayFrom d.pivot.1 => z.1) hAway
          have hinner : (d.qLabel i).1 = (d.qLabel j).1 :=
            Subtype.ext hval
          have hij : i = j := d.qLabel.injective (Subtype.ext hinner)
          subst j
          rfl
      | inr j =>
          exfalso
          have hval := congrArg Subtype.val hxy
          change (d.qLabel i).1.1 = (d.secondLabel j).1 at hval
          have hq := d.qLabel_mem_firstSupport i
          have hb := d.secondLabel_mem_secondSupport j
          exact Finset.disjoint_left.mp d.base.supports_disjoint hq
            (hval.symm ▸ hb)
  | inr i =>
      cases y with
      | inl j =>
          exfalso
          have hval := congrArg Subtype.val hxy
          change (d.secondLabel i).1 = (d.qLabel j).1.1 at hval
          have hq := d.qLabel_mem_firstSupport j
          have hb := d.secondLabel_mem_secondSupport i
          exact Finset.disjoint_left.mp d.base.supports_disjoint
            (hval ▸ hq) hb
      | inr j =>
          have hAway := hxy
          change (⟨(d.secondLabel i).1, by
              intro h
              apply d.pivot_not_mem_secondSupport
              rw [← h]
              exact d.secondLabel_mem_secondSupport i⟩ : AwayFrom d.pivot.1) =
            ⟨(d.secondLabel j).1, by
              intro h
              apply d.pivot_not_mem_secondSupport
              rw [← h]
              exact d.secondLabel_mem_secondSupport j⟩ at hAway
          have hval : (d.secondLabel i).1 = (d.secondLabel j).1 :=
            congrArg (fun z : AwayFrom d.pivot.1 => z.1) hAway
          have hij : i = j := d.secondLabel.injective (Subtype.ext hval)
          subst j
          rfl

/-- The labelled ordinary graph exhausts the nine labels away from the
pivot whenever the ambient selected configuration has ten points. -/
noncomputable def awayEquiv
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10) :
    GoldenOrdinaryVertex ≃ AwayFrom d.pivot.1 := by
  apply Equiv.ofBijective d.goldenAwayLabel
  refine ⟨d.goldenAwayLabel_injective, ?_⟩
  intro x
  have hcover := d.base.supports_union_eq_univ hcard
  have hxcover : x.1 ∈ geometricBlockSupport cfg d.base.first ∪
      geometricBlockSupport cfg d.base.second := by
    rw [hcover]
    simp
  by_cases hfirst : x.1 ∈ geometricBlockSupport cfg d.base.first
  · let q : {y : TenTwoPentagonFirstTrace d // y ≠ d.pivot} :=
      ⟨⟨x.1, by
        simpa only [d.base.exclusiveTrace_Γ_Ω] using hfirst⟩, by
        intro h
        apply x.2
        exact congrArg Subtype.val h⟩
    obtain ⟨i, hi⟩ := d.qLabel.surjective q
    refine ⟨.inl i, ?_⟩
    apply Subtype.ext
    change (d.qLabel i).1.1 = x.1
    exact congrArg (fun z : {y : TenTwoPentagonFirstTrace d // y ≠ d.pivot} =>
      z.1.1) hi
  · have hsecond : x.1 ∈ geometricBlockSupport cfg d.base.second := by
      rcases Finset.mem_union.mp hxcover with h | h
      · exact (hfirst h).elim
      · exact h
    let b : TenTwoPentagonSecondTrace d := ⟨x.1, by
      simpa only [d.base.exclusiveTrace_Ω_Γ] using hsecond⟩
    obtain ⟨i, hi⟩ := d.secondLabel.surjective b
    refine ⟨.inr i, ?_⟩
    apply Subtype.ext
    change (d.secondLabel i).1 = x.1
    exact congrArg Subtype.val hi

@[simp] theorem awayEquiv_apply_q
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10) (i : Fin 4) :
    d.awayEquiv hcard (goldenQ i) =
      ⟨(d.qLabel i).1.1, by
        intro h
        apply (d.qLabel i).2
        apply Subtype.ext
        exact h⟩ := rfl

@[simp] theorem awayEquiv_apply_b
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10) (i : Fin 5) :
    (d.awayEquiv hcard (goldenB i)).1 = (d.secondLabel i).1 := rfl

/-- Transport a finite support of the abstract nine-vertex graph into the
actual away-from-pivot carrier. -/
noncomputable def encodeOrdinarySupport
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (S : Finset GoldenOrdinaryVertex) : Finset (AwayFrom d.pivot.1) :=
  S.map (d.awayEquiv hcard).toEmbedding

@[simp] theorem mem_encodeOrdinarySupport
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (S : Finset GoldenOrdinaryVertex) (x : GoldenOrdinaryVertex) :
    d.awayEquiv hcard x ∈ d.encodeOrdinarySupport hcard S ↔ x ∈ S := by
  simp [encodeOrdinarySupport]

/-- Encode one ordinary edge by its two actual inverted labels. -/
noncomputable def encodeOrdinaryEdge
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10) (e : GoldenOrdinaryEdge) :
    Finset (AwayFrom d.pivot.1) :=
  d.encodeOrdinarySupport hcard e.1

@[simp] theorem mem_encodeOrdinaryEdge
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10) (e : GoldenOrdinaryEdge)
    (x : GoldenOrdinaryVertex) :
    d.awayEquiv hcard x ∈ d.encodeOrdinaryEdge hcard e ↔ x ∈ e.1 := by
  exact d.mem_encodeOrdinarySupport hcard e.1 x

/-- The six encoded ordinary supports of the two `P4` components. -/
noncomputable def encodedOrdinaryEdges
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10) :
    Finset (Finset (AwayFrom d.pivot.1)) :=
  goldenOrdinaryEdges.image (d.encodeOrdinaryEdge hcard)

@[simp] theorem encode_goldenQEdge_mem_encodedOrdinaryEdges
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10) (i : Fin 4) :
    d.encodeOrdinaryEdge hcard (goldenQEdge i) ∈
      d.encodedOrdinaryEdges hcard := by
  apply Finset.mem_image.mpr
  refine ⟨goldenQEdge i, ?_, rfl⟩
  fin_cases i <;> simp [goldenOrdinaryEdges]

@[simp] theorem encode_goldenBEdge13_mem_encodedOrdinaryEdges
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10) :
    d.encodeOrdinaryEdge hcard goldenBEdge13 ∈
      d.encodedOrdinaryEdges hcard := by
  apply Finset.mem_image.mpr
  exact ⟨goldenBEdge13, by simp [goldenOrdinaryEdges], rfl⟩

@[simp] theorem encode_goldenBEdge24_mem_encodedOrdinaryEdges
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10) :
    d.encodeOrdinaryEdge hcard goldenBEdge24 ∈
      d.encodedOrdinaryEdges hcard := by
  apply Finset.mem_image.mpr
  exact ⟨goldenBEdge24, by simp [goldenOrdinaryEdges], rfl⟩

/-- The two row endpoints of the second pentagon lie on a common pivot line
coming from their saturated cross-block. -/
theorem encoded_second_row_endpoint_on_pivotLine
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (i : Fin 4) (j k : Fin 2) :
    ∃ L : DeterminedLine (pivotInversion cfg d.pivot.1),
      d.awayEquiv hcard
        (goldenB (goldenCenterChordEndpoint i j k)) ∈
        lineSupport (pivotInversion cfg d.pivot.1) L := by
  refine ⟨d.goldenRowPivotLine i j, ?_⟩
  simpa only [awayEquiv_apply_b] using
    d.golden_row_endpoint_mem_pivotLine i j k

/-- The first-pentagon partner lies on both row pivot lines.  This is the
concurrency lane used together with the ordinary three-line transport. -/
theorem encoded_qLabel_on_pivotLine
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (i : Fin 4) (j : Fin 2) :
    ∃ L : DeterminedLine (pivotInversion cfg d.pivot.1),
      d.awayEquiv hcard (goldenQ i) ∈
        lineSupport (pivotInversion cfg d.pivot.1) L := by
  refine ⟨d.goldenRowPivotLine i j, ?_⟩
  simpa only [awayEquiv_apply_q] using
    d.qLabel_mem_goldenPivotLine i j

/-! ## Closed finite row helpers -/

/-- Every canonical chord has one finite row owner. -/
theorem goldenCanonicalChord_owner
    (e : FinFiveChord) :
    ∃! c : Fin 5, e ∈ kFiveCanonicalFactorFamily c := by
  exact kFiveCanonicalNearOneFactorizationCode.valid e

/-- A finite five-label is zero or a unique successor label. -/
theorem finFive_zero_or_succ (c : Fin 5) :
    c = 0 ∨ ∃ i : Fin 4, c = i.succ := by
  fin_cases c <;> decide +kernel

/-- Among four labels, two distinct labels leave a third one available. -/
theorem exists_finFour_ne_ne (i j : Fin 4) (hij : i ≠ j) :
    ∃ m : Fin 4, m ≠ i ∧ m ≠ j := by
  fin_cases i <;> fin_cases j <;> simp_all <;> decide +kernel

/-- The other endpoint position of a two-element row chord. -/
def otherFinTwo (t : Fin 2) : Fin 2 :=
  if t = 0 then 1 else 0

@[simp] theorem otherFinTwo_ne (t : Fin 2) : otherFinTwo t ≠ t := by
  fin_cases t <;> simp [otherFinTwo]

/-- The zero row of the canonical table consists precisely of the two middle
edges in the two `P4` components. -/
theorem goldenCanonicalChord_zero_row :
    kFiveCanonicalFactorFamily 0 =
      {kFiveChord13, kFiveChord24} := by
  decide +kernel

/-- Package a distinct pair of finite labels as a canonical K5 chord. -/
def finFiveChordOfNe (a b : Fin 5) (hab : a ≠ b) : FinFiveChord :=
  ⟨{a, b}, by simp [hab]⟩

@[simp] theorem finFiveChordOfNe_val
    (a b : Fin 5) (hab : a ≠ b) :
    (finFiveChordOfNe a b hab).1 = {a, b} := rfl

/-- The explicit row chord through a non-omitted finite vertex. -/
theorem goldenCanonicalChord_covers_succ
    (i : Fin 4) (k : Fin 5) (hk : k ≠ i.succ) :
    ∃ j : Fin 2, k ∈ (goldenCanonicalChord i j).1 := by
  fin_cases i <;> fin_cases k <;> simp_all [goldenCanonicalChord] <;>
    decide +kernel

/-- Membership in a displayed chord supplies an endpoint position. -/
theorem mem_goldenCanonicalChord_endpoint
    (i : Fin 4) (j : Fin 2) (k : Fin 5)
    (hk : k ∈ (goldenCanonicalChord i j).1) :
    ∃ t : Fin 2, k = goldenCenterChordEndpoint i j t := by
  rcases (by
    simpa only [goldenCanonicalChord_val, Finset.mem_insert,
      Finset.mem_singleton] using hk :
      k = goldenCenterChordEndpoint i j 0 ∨
        k = goldenCenterChordEndpoint i j 1) with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩

/-- The two endpoint positions of every displayed golden chord are distinct. -/
theorem goldenCenterChordEndpoint_ne
    (i : Fin 4) (j t u : Fin 2) (htu : t ≠ u) :
    goldenCenterChordEndpoint i j t ≠ goldenCenterChordEndpoint i j u := by
  fin_cases i <;> fin_cases j <;> fin_cases t <;> fin_cases u <;>
    simp_all [goldenCenterChordEndpoint]

/-- A chord in a nonzero canonical row is one of its two displayed chords. -/
theorem goldenCanonicalChord_eq_of_mem_succ
    (i : Fin 4) (e : FinFiveChord)
    (he : e ∈ kFiveCanonicalFactorFamily i.succ) :
    ∃ j : Fin 2, e = goldenCanonicalChord i j := by
  rw [kFiveCanonicalFactorFamily_succ] at he
  rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using he :
    e = goldenCanonicalChord i 0 ∨ e = goldenCanonicalChord i 1) with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩

/-- A finite pair in the zero canonical row is one of the two middle edges
of the `2P4` graph. -/
theorem goldenBEdge_of_finFiveChord_zero_owner
    (a b : Fin 5) (hab : a ≠ b)
    (howner : finFiveChordOfNe a b hab ∈ kFiveCanonicalFactorFamily 0) :
    goldenOrdinaryEdgeOfNe (goldenB a) (goldenB b) (goldenB_ne a b hab) =
      goldenBEdge13 ∨
    goldenOrdinaryEdgeOfNe (goldenB a) (goldenB b) (goldenB_ne a b hab) =
      goldenBEdge24 := by
  have hzero : finFiveChordOfNe a b hab = kFiveChord13 ∨
      finFiveChordOfNe a b hab = kFiveChord24 := by
    rw [goldenCanonicalChord_zero_row] at howner
    simpa only [Finset.mem_insert, Finset.mem_singleton] using howner
  rcases hzero with h | h
  · left
    apply Subtype.ext
    have hm := congrArg
      (Finset.map ⟨goldenB, fun x y hxy => Sum.inr.inj hxy⟩) (congrArg Subtype.val h)
    simpa only [goldenOrdinaryEdgeOfNe, goldenBEdge13, goldenB,
      finFiveChordOfNe_val, Finset.map_insert, Finset.map_singleton] using hm
  · right
    apply Subtype.ext
    have hm := congrArg
      (Finset.map ⟨goldenB, fun x y hxy => Sum.inr.inj hxy⟩) (congrArg Subtype.val h)
    simpa only [goldenOrdinaryEdgeOfNe, goldenBEdge24, goldenB,
      finFiveChordOfNe_val, Finset.map_insert, Finset.map_singleton] using hm

/-- Every pair of distinct `b` labels is either one of the two middle
ordinary edges or a displayed chord of a nonzero canonical row. -/
theorem goldenBPair_middle_or_row
    (a b : Fin 5) (hab : a ≠ b) :
    goldenOrdinaryEdgeOfNe (goldenB a) (goldenB b) (goldenB_ne a b hab) ∈
        goldenOrdinaryEdges ∨
      ∃ i : Fin 4, ∃ j : Fin 2,
        finFiveChordOfNe a b hab = goldenCanonicalChord i j := by
  obtain ⟨c, hc, _⟩ := goldenCanonicalChord_owner (finFiveChordOfNe a b hab)
  rcases finFive_zero_or_succ c with rfl | ⟨i, rfl⟩
  · rcases goldenBEdge_of_finFiveChord_zero_owner a b hab hc with h | h
    · rw [h]
      simp [goldenOrdinaryEdges]
    · rw [h]
      simp [goldenOrdinaryEdges]
  · obtain ⟨j, hj⟩ := goldenCanonicalChord_eq_of_mem_succ i _ hc
    exact Or.inr ⟨i, j, hj⟩

/-- Equality with a displayed canonical chord identifies both endpoints. -/
theorem finFiveChordOfNe_eq_goldenCanonicalChord_endpoints
    (a b : Fin 5) (hab : a ≠ b) (i : Fin 4) (j : Fin 2)
    (h : finFiveChordOfNe a b hab = goldenCanonicalChord i j) :
    ∃ t u : Fin 2, t ≠ u ∧
      a = goldenCenterChordEndpoint i j t ∧
      b = goldenCenterChordEndpoint i j u := by
  have ha : a ∈ (goldenCanonicalChord i j).1 := by
    rw [← h]
    simp [finFiveChordOfNe]
  obtain ⟨t, hat⟩ := mem_goldenCanonicalChord_endpoint i j a ha
  let u := otherFinTwo t
  have htu : t ≠ u := (otherFinTwo_ne t).symm
  have hb : b ∈ (goldenCanonicalChord i j).1 := by
    rw [← h]
    simp [finFiveChordOfNe]
  obtain ⟨r, hbr⟩ := mem_goldenCanonicalChord_endpoint i j b hb
  have hrt : r ≠ t := by
    intro hrt
    apply hab
    rw [hat, hbr, hrt]
  have hru : r = u := by
    dsimp only [u]
    fin_cases t <;> fin_cases r <;> simp_all [otherFinTwo]
  exact ⟨t, u, htu, hat,
    hbr.trans (congrArg (goldenCenterChordEndpoint i j) hru)⟩

/-! ## Universal ordinary-line classification -/

/-- The desired six-edge classification for an ordinary inverted line.
The subsequent geometric proof discharges this predicate by splitting the
two support labels into `q-q`, `q-b`, and `b-b` cases. -/
def IsGoldenEncodedOrdinaryLine
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (L : DeterminedLineOfSize (pivotInversion cfg d.pivot.1) 2) :
    Prop := ∃ e : GoldenOrdinaryEdge, e ∈ goldenOrdinaryEdges ∧
      lineSupport (pivotInversion cfg d.pivot.1) L.1 =
        d.encodeOrdinaryEdge hcard e

/-- Extract the two distinct away-labels supporting an ordinary inverted
line.  The equality is deliberately oriented for later rewriting of line
membership in the `q-q`, `q-b`, and `b-b` cases. -/
theorem ordinaryLine_support_pair
    (d : TenTwoPentagonSaturationData cfg)
    (L : DeterminedLineOfSize (pivotInversion cfg d.pivot.1) 2) :
    ∃ x y : AwayFrom d.pivot.1, x ≠ y ∧
      lineSupport (pivotInversion cfg d.pivot.1) L.1 = {x, y} := by
  exact Finset.card_eq_two.mp L.2

/-- Pull an actual away-from-pivot label back to the abstract nine-vertex
labeling. -/
noncomputable def decodeOrdinaryVertex
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10) :
    AwayFrom d.pivot.1 → GoldenOrdinaryVertex :=
  (d.awayEquiv hcard).symm

@[simp] theorem awayEquiv_decodeOrdinaryVertex
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10) (x : AwayFrom d.pivot.1) :
    d.awayEquiv hcard (d.decodeOrdinaryVertex hcard x) = x :=
  (d.awayEquiv hcard).apply_symm_apply x

@[simp] theorem decodeOrdinaryVertex_awayEquiv
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10) (x : GoldenOrdinaryVertex) :
    d.decodeOrdinaryVertex hcard (d.awayEquiv hcard x) = x :=
  (d.awayEquiv hcard).symm_apply_apply x

/-- Three distinct support labels cannot lie on an ordinary line whose
support cardinality is two. -/
theorem card_two_contradiction_of_three_mem
    {β : Type*} [DecidableEq β] (S : Finset β)
    (hcard : S.card = 2) (x y z : β)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) : False := by
  have hsub : ({x, y, z} : Finset β) ⊆ S := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz
  have hle := Finset.card_le_card hsub
  have hthree : ({x, y, z} : Finset β).card = 3 := by
    simp [hxy, hxz, hyz]
  rw [hthree, hcard] at hle
  omega

/-- Encoding an abstract pair is exactly the pair of its away labels. -/
theorem encodeOrdinaryEdge_pair
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (x y : GoldenOrdinaryVertex) (hxy : x ≠ y) :
    d.encodeOrdinaryEdge hcard (goldenOrdinaryEdgeOfNe x y hxy) =
      {d.awayEquiv hcard x, d.awayEquiv hcard y} := by
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw⟩ := (d.awayEquiv hcard).surjective z
    rw [← hw] at hz ⊢
    rw [mem_encodeOrdinaryEdge] at hz
    simp only [goldenOrdinaryEdgeOfNe, Finset.mem_insert,
      Finset.mem_singleton] at hz
    rcases hz with h | h
    · simp [congrArg (d.awayEquiv hcard) h]
    · simp [congrArg (d.awayEquiv hcard) h]
  · intro hz
    obtain ⟨w, hw⟩ := (d.awayEquiv hcard).surjective z
    rw [← hw] at hz ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rw [mem_encodeOrdinaryEdge]
    simp only [goldenOrdinaryEdgeOfNe, Finset.mem_insert,
      Finset.mem_singleton]
    rcases hz with h | h
    · exact Or.inl ((d.awayEquiv hcard).injective h)
    · exact Or.inr ((d.awayEquiv hcard).injective h)

@[simp] theorem awayEquiv_ne_iff
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (x y : GoldenOrdinaryVertex) :
    d.awayEquiv hcard x ≠ d.awayEquiv hcard y ↔ x ≠ y := by
  constructor
  · intro h hxy
    exact h (congrArg (d.awayEquiv hcard) hxy)
  · exact (d.awayEquiv hcard).injective.ne

/-- Reversing the presentation of a two-element golden edge does not change
the packaged edge. -/
theorem goldenOrdinaryEdgeOfNe_swap
    (x y : GoldenOrdinaryVertex) (hxy : x ≠ y) :
    goldenOrdinaryEdgeOfNe y x hxy.symm = goldenOrdinaryEdgeOfNe x y hxy := by
  apply Subtype.ext
  simp only [goldenOrdinaryEdgeOfNe]
  exact Finset.pair_comm y x

/-- Once the two abstract support labels form one of the six displayed
edges, the corresponding ordinary line has the required encoding. -/
theorem isGoldenEncodedOrdinaryLine_of_support_pair
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (L : DeterminedLineOfSize (pivotInversion cfg d.pivot.1) 2)
    (x y : GoldenOrdinaryVertex) (hxy : x ≠ y)
    (hedge : goldenOrdinaryEdgeOfNe x y hxy ∈ goldenOrdinaryEdges)
    (hsupport : lineSupport (pivotInversion cfg d.pivot.1) L.1 =
      {d.awayEquiv hcard x, d.awayEquiv hcard y}) :
    d.IsGoldenEncodedOrdinaryLine hcard L := by
  refine ⟨goldenOrdinaryEdgeOfNe x y hxy, hedge, ?_⟩
  exact hsupport.trans (d.encodeOrdinaryEdge_pair hcard x y hxy).symm

/-- Two distinct `q` labels cannot be the complete support of an ordinary
inverted line: their line is the inversion line of the first base circle and
contains a third `q` label. -/
theorem q_q_impossible
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (L : DeterminedLineOfSize (pivotInversion cfg d.pivot.1) 2)
    (i j : Fin 4) (hij : i ≠ j)
    (hsupport : lineSupport (pivotInversion cfg d.pivot.1) L.1 =
      {d.awayEquiv hcard (goldenQ i), d.awayEquiv hcard (goldenQ j)}) :
    False := by
  classical
  obtain ⟨m, hmi, hmj⟩ := exists_finFour_ne_ne i j hij
  let qi : AwayFrom d.pivot.1 := d.awayEquiv hcard (goldenQ i)
  let qj : AwayFrom d.pivot.1 := d.awayEquiv hcard (goldenQ j)
  let qm : AwayFrom d.pivot.1 := d.awayEquiv hcard (goldenQ m)
  have hijAway : qi ≠ qj := by
    dsimp only [qi, qj]
    exact (d.awayEquiv hcard).injective.ne (by simpa [goldenQ] using hij)
  let A : KSubset (AwayFrom d.pivot.1) 2 := ⟨{qi, qj}, by simp [hijAway]⟩
  have hAonL : ∀ x ∈ A.1, (pivotInversion cfg d.pivot.1) x ∈ (L.1 : Set Point2) := by
    intro x hx
    apply (mem_lineSupport (cfg := pivotInversion cfg d.pivot.1) (L := L.1)
      (x := x)).mp
    rw [hsupport]
    simpa only [A, qi, qj, Finset.mem_insert, Finset.mem_singleton] using hx
  have hlineL : lineOfPair (pivotInversion cfg d.pivot.1) A = L.1 :=
    lineOfPair_eq_of_mem_of_direction_finrank_one
      (pivotInversion cfg d.pivot.1) A L.1 hAonL L.1.direction_finrank
  have hpivot : d.pivot.1 ∈ circleTrace cfg d.base.Γ.1 := by
    rw [d.base.circleTrace_Γ]
    simpa only [d.base.exclusiveTrace_Γ_Ω] using d.pivot.2
  have hqCircle (r : Fin 4) :
      (d.awayEquiv hcard (goldenQ r)).1 ∈ circleTrace cfg d.base.Γ.1 := by
    rw [d.awayEquiv_apply_q]
    rw [d.base.circleTrace_Γ]
    exact d.qLabel_mem_firstSupport r
  have hAonCircle : ∀ x ∈ A.1,
      (pivotInversion cfg d.pivot.1) x ∈
        circlePivotLine cfg d.pivot.1 d.base.Γ.1 := by
    intro x hx
    apply (pivotInversion_mem_circlePivotLine_iff cfg d.pivot.1 d.base.Γ.1
      hpivot x).2
    rcases (by
      simpa only [A, qi, qj, Finset.mem_insert, Finset.mem_singleton] using hx :
        x = qi ∨ x = qj) with rfl | rfl
    · exact hqCircle i
    · exact hqCircle j
  have hlineCircle : lineOfPair (pivotInversion cfg d.pivot.1) A =
      circlePivotLine cfg d.pivot.1 d.base.Γ.1 :=
    lineOfPair_eq_of_mem_of_direction_finrank_one
      (pivotInversion cfg d.pivot.1) A
      (circlePivotLine cfg d.pivot.1 d.base.Γ.1) hAonCircle
      (circlePivotLine_direction_finrank cfg d.pivot.1 d.base.Γ.1 hpivot)
  have hqmL : qm ∈ lineSupport (pivotInversion cfg d.pivot.1) L.1 := by
    apply mem_lineSupport.mpr
    rw [← hlineL, hlineCircle]
    exact (pivotInversion_mem_circlePivotLine_iff cfg d.pivot.1 d.base.Γ.1
      hpivot qm).2 (hqCircle m)
  have hqiL : qi ∈ lineSupport (pivotInversion cfg d.pivot.1) L.1 := by
    rw [hsupport]
    simp [qi]
  have hqjL : qj ∈ lineSupport (pivotInversion cfg d.pivot.1) L.1 := by
    rw [hsupport]
    simp [qj]
  have hqiQm : qi ≠ qm := by
    dsimp only [qi, qm]
    apply (d.awayEquiv hcard).injective.ne
    simpa [goldenQ] using hmi.symm
  have hqjQm : qj ≠ qm := by
    dsimp only [qj, qm]
    apply (d.awayEquiv hcard).injective.ne
    simpa [goldenQ] using hmj.symm
  exact card_two_contradiction_of_three_mem _ L.2 qi qj qm
    hijAway hqiQm hqjQm hqiL hqjL hqmL

/-- A saturated row pivot line contains its `q` label and both endpoints of
the associated second-pentagon chord.  They are pairwise distinct, hence it
cannot itself be ordinary. -/
theorem row_line_support_ge_three
    (d : TenTwoPentagonSaturationData cfg)
    (i : Fin 4) (j : Fin 2) :
    ∃ L : DeterminedLine (pivotInversion cfg d.pivot.1),
      ∃ q b₀ b₁ : AwayFrom d.pivot.1,
        q ∈ lineSupport (pivotInversion cfg d.pivot.1) L ∧
        b₀ ∈ lineSupport (pivotInversion cfg d.pivot.1) L ∧
        b₁ ∈ lineSupport (pivotInversion cfg d.pivot.1) L ∧
        q ≠ b₀ ∧ q ≠ b₁ ∧ b₀ ≠ b₁ := by
  classical
  let L := d.goldenRowPivotLine i j
  have second_ne_pivot (k : Fin 5) : (d.secondLabel k).1 ≠ d.pivot.1 := by
    intro h
    apply d.pivot_not_mem_secondSupport
    rw [← h]
    exact d.secondLabel_mem_secondSupport k
  let q : AwayFrom d.pivot.1 := ⟨(d.qLabel i).1.1, by
    intro h
    apply (d.qLabel i).2
    exact Subtype.ext h⟩
  let b₀ : AwayFrom d.pivot.1 :=
    ⟨(d.secondLabel (goldenCenterChordEndpoint i j 0)).1,
      second_ne_pivot _⟩
  let b₁ : AwayFrom d.pivot.1 :=
    ⟨(d.secondLabel (goldenCenterChordEndpoint i j 1)).1,
      second_ne_pivot _⟩
  refine ⟨L, q, b₀, b₁, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact d.qLabel_mem_goldenRowPivotLine i j
  · exact d.golden_row_endpoint_mem_goldenRowPivotLine i j 0
  · exact d.golden_row_endpoint_mem_goldenRowPivotLine i j 1
  · intro h
    have hval : (d.qLabel i).1.1 =
        (d.secondLabel (goldenCenterChordEndpoint i j 0)).1 :=
      congrArg (fun z : AwayFrom d.pivot.1 => z.1) h
    exact Finset.disjoint_left.mp d.base.supports_disjoint
      (d.qLabel_mem_firstSupport i)
      (hval.symm ▸ d.secondLabel_mem_secondSupport _)
  · intro h
    have hval : (d.qLabel i).1.1 =
        (d.secondLabel (goldenCenterChordEndpoint i j 1)).1 :=
      congrArg (fun z : AwayFrom d.pivot.1 => z.1) h
    exact Finset.disjoint_left.mp d.base.supports_disjoint
      (d.qLabel_mem_firstSupport i)
      (hval.symm ▸ d.secondLabel_mem_secondSupport _)
  · intro h
    have hval : (d.secondLabel (goldenCenterChordEndpoint i j 0)).1 =
        (d.secondLabel (goldenCenterChordEndpoint i j 1)).1 :=
      congrArg (fun z : AwayFrom d.pivot.1 => z.1) h
    have hend : goldenCenterChordEndpoint i j 0 =
        goldenCenterChordEndpoint i j 1 :=
      d.secondLabel.injective (Subtype.ext hval)
    exact goldenCenterChordEndpoint_ne i j 0 1 (by decide) hend

/-- A named row line cannot have ordinary support, once its three displayed
points are placed in that support. -/
theorem row_line_not_ordinary_of_three_points
    (d : TenTwoPentagonSaturationData cfg)
    (R : DeterminedLine (pivotInversion cfg d.pivot.1))
    (q b₀ b₁ : AwayFrom d.pivot.1)
    (hq : q ∈ lineSupport (pivotInversion cfg d.pivot.1) R)
    (hb₀ : b₀ ∈ lineSupport (pivotInversion cfg d.pivot.1) R)
    (hb₁ : b₁ ∈ lineSupport (pivotInversion cfg d.pivot.1) R)
    (hqb₀ : q ≠ b₀) (hqb₁ : q ≠ b₁) (hb₀b₁ : b₀ ≠ b₁) :
    (lineSupport (pivotInversion cfg d.pivot.1) R).card ≠ 2 := by
  intro hcard
  exact card_two_contradiction_of_three_mem _ hcard q b₀ b₁
    hqb₀ hqb₁ hb₀b₁ hq hb₀ hb₁

/-- Two distinct common support points determine a unique affine line. -/
theorem determinedLine_eq_of_two_mem
    {β : Type*} [Fintype β] [DecidableEq β]
    (C : Configuration β) (L R : DeterminedLine C)
    (x y : β) (hxy : x ≠ y)
    (hxL : x ∈ lineSupport C L) (hyL : y ∈ lineSupport C L)
    (hxR : x ∈ lineSupport C R) (hyR : y ∈ lineSupport C R) :
    L = R := by
  let A : KSubset β 2 := ⟨{x, y}, by simp [hxy]⟩
  have hAonL : ∀ z ∈ A.1, C z ∈ L.1 := by
    intro z hz
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact mem_lineSupport.mp hxL
    · exact mem_lineSupport.mp hyL
  have hAonR : ∀ z ∈ A.1, C z ∈ R.1 := by
    intro z hz
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact mem_lineSupport.mp hxR
    · exact mem_lineSupport.mp hyR
  apply Subtype.ext
  exact (lineOfPair_eq_of_mem_of_direction_finrank_one C A L.1
    hAonL L.direction_finrank).symm.trans
    (lineOfPair_eq_of_mem_of_direction_finrank_one C A R.1
      hAonR R.direction_finrank)

/-- A non-end `q_i-b_k` pair is not ordinary: the canonical row through
`k` supplies a golden row line containing `q_i` and both of that row's
second endpoints. -/
theorem q_b_nonedge_impossible
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (L : DeterminedLineOfSize (pivotInversion cfg d.pivot.1) 2)
    (i : Fin 4) (k : Fin 5) (hk : k ≠ i.succ)
    (hsupport : lineSupport (pivotInversion cfg d.pivot.1) L.1 =
      {d.awayEquiv hcard (goldenQ i), d.awayEquiv hcard (goldenB k)}) :
    False := by
  classical
  obtain ⟨j, hj⟩ := goldenCanonicalChord_covers_succ i k hk
  have hrow : ∃ j t : Fin 2, k = goldenCenterChordEndpoint i j t :=
    ⟨j, mem_goldenCanonicalChord_endpoint i j k hj⟩
  obtain ⟨j, t, hkt⟩ := hrow
  let x := d.awayEquiv hcard (goldenQ i)
  let y := d.awayEquiv hcard (goldenB k)
  let z := d.awayEquiv hcard
    (goldenB (goldenCenterChordEndpoint i j (otherFinTwo t)))
  let R := d.goldenRowPivotLine i j
  have hxy : x ≠ y := by
    dsimp only [x, y]
    exact (d.awayEquiv hcard).injective.ne (by simp [goldenQ, goldenB])
  have hxL : x ∈ lineSupport (pivotInversion cfg d.pivot.1) L.1 := by
    rw [hsupport]
    simp [x]
  have hyL : y ∈ lineSupport (pivotInversion cfg d.pivot.1) L.1 := by
    rw [hsupport]
    simp [y]
  have hxR : x ∈ lineSupport (pivotInversion cfg d.pivot.1) R := by
    dsimp only [x, R]
    simpa only [awayEquiv_apply_q] using d.qLabel_mem_goldenRowPivotLine i j
  have hyR : y ∈ lineSupport (pivotInversion cfg d.pivot.1) R := by
    dsimp only [y, R]
    rw [hkt]
    simpa only [awayEquiv_apply_b] using
      d.golden_row_endpoint_mem_goldenRowPivotLine i j t
  have hLR : L.1 = R := by
    have h := determinedLine_eq_of_two_mem
      (pivotInversion cfg d.pivot.1) L.1 R x y hxy hxL hyL hxR hyR
    exact h
  have hzR : z ∈ lineSupport (pivotInversion cfg d.pivot.1) R := by
    dsimp only [z, R]
    simpa only [awayEquiv_apply_b] using
      d.golden_row_endpoint_mem_goldenRowPivotLine i j (otherFinTwo t)
  have hzL : z ∈ lineSupport (pivotInversion cfg d.pivot.1) L.1 := by
    rw [hLR]
    exact hzR
  have hxz : x ≠ z := by
    dsimp only [x, z]
    exact (d.awayEquiv hcard).injective.ne (by simp [goldenQ, goldenB])
  have hyz : y ≠ z := by
    dsimp only [y, z]
    rw [hkt]
    apply (d.awayEquiv hcard).injective.ne
    exact goldenB_ne _ _ (goldenCenterChordEndpoint_ne i j t (otherFinTwo t)
      (otherFinTwo_ne t).symm)
  exact card_two_contradiction_of_three_mem _ L.2 x y z
    hxy hxz hyz hxL hyL hzL

/-- A non-middle `b_a-b_b` pair is not ordinary: its unique nonzero
canonical row contributes the associated `q` label as a third point of the
same golden row line. -/
theorem b_b_nonedge_impossible
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (L : DeterminedLineOfSize (pivotInversion cfg d.pivot.1) 2)
    (a b : Fin 5) (hab : a ≠ b)
    (hnonedge : goldenOrdinaryEdgeOfNe (goldenB a) (goldenB b) (goldenB_ne a b hab) ∉
      goldenOrdinaryEdges)
    (hsupport : lineSupport (pivotInversion cfg d.pivot.1) L.1 =
      {d.awayEquiv hcard (goldenB a), d.awayEquiv hcard (goldenB b)}) :
    False := by
  classical
  have hrow : ∃ i : Fin 4, ∃ j : Fin 2,
      finFiveChordOfNe a b hab = goldenCanonicalChord i j :=
    (goldenBPair_middle_or_row a b hab).resolve_left hnonedge
  obtain ⟨i, j, hchord⟩ := hrow
  obtain ⟨t, u, htu, hat, hbu⟩ :=
    finFiveChordOfNe_eq_goldenCanonicalChord_endpoints a b hab i j hchord
  let x := d.awayEquiv hcard (goldenB a)
  let y := d.awayEquiv hcard (goldenB b)
  let z := d.awayEquiv hcard (goldenQ i)
  let R := d.goldenRowPivotLine i j
  have hxy : x ≠ y := by
    dsimp only [x, y]
    exact (d.awayEquiv hcard).injective.ne (by simpa [goldenB] using hab)
  have hxL : x ∈ lineSupport (pivotInversion cfg d.pivot.1) L.1 := by
    rw [hsupport]
    simp [x]
  have hyL : y ∈ lineSupport (pivotInversion cfg d.pivot.1) L.1 := by
    rw [hsupport]
    simp [y]
  have hxR : x ∈ lineSupport (pivotInversion cfg d.pivot.1) R := by
    dsimp only [x, R]
    rw [hat]
    simpa only [awayEquiv_apply_b] using
      d.golden_row_endpoint_mem_goldenRowPivotLine i j t
  have hyR : y ∈ lineSupport (pivotInversion cfg d.pivot.1) R := by
    dsimp only [y, R]
    rw [hbu]
    simpa only [awayEquiv_apply_b] using
      d.golden_row_endpoint_mem_goldenRowPivotLine i j u
  have hLR : L.1 = R := by
    have h := determinedLine_eq_of_two_mem
      (pivotInversion cfg d.pivot.1) L.1 R x y hxy hxL hyL hxR hyR
    exact h
  have hzR : z ∈ lineSupport (pivotInversion cfg d.pivot.1) R := by
    dsimp only [z, R]
    simpa only [awayEquiv_apply_q] using d.qLabel_mem_goldenRowPivotLine i j
  have hzL : z ∈ lineSupport (pivotInversion cfg d.pivot.1) L.1 := by
    rw [hLR]
    exact hzR
  have hxz : x ≠ z := by
    dsimp only [x, z]
    exact (d.awayEquiv hcard).injective.ne (by simp [goldenQ, goldenB])
  have hyz : y ≠ z := by
    dsimp only [y, z]
    exact (d.awayEquiv hcard).injective.ne (by simp [goldenQ, goldenB])
  exact card_two_contradiction_of_three_mem _ L.2 x y z
    hxy hxz hyz hxL hyL hzL

/-- Every ordinary line after pivot inversion is the encoding of one of the
six edges of the golden `2P4` graph.  The four cases are the two types of
abstract labels; nonedges are excluded by the three-point row and circle
arguments above. -/
theorem goldenOrdinaryLine_classified
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (L : DeterminedLineOfSize (pivotInversion cfg d.pivot.1) 2) :
    d.IsGoldenEncodedOrdinaryLine hcard L := by
  classical
  obtain ⟨x, y, hxy, hsupport⟩ := d.ordinaryLine_support_pair L
  let u := d.decodeOrdinaryVertex hcard x
  let v := d.decodeOrdinaryVertex hcard y
  have huv : u ≠ v := by
    intro huv
    apply hxy
    simpa only [u, v, awayEquiv_decodeOrdinaryVertex] using
      congrArg (d.awayEquiv hcard) huv
  have hs : lineSupport (pivotInversion cfg d.pivot.1) L.1 =
      {d.awayEquiv hcard u, d.awayEquiv hcard v} := by
    simpa only [u, v, awayEquiv_decodeOrdinaryVertex] using hsupport
  rcases u with i | a
  · rcases v with j | k
    · have hij : i ≠ j := fun h => huv (congrArg Sum.inl h)
      exact (d.q_q_impossible hcard L i j hij (by
        simpa only [goldenQ] using hs)).elim
    · have hqbk : goldenQ i ≠ goldenB k := by simp [goldenQ, goldenB]
      by_cases hk : k = i.succ
      · subst k
        apply d.isGoldenEncodedOrdinaryLine_of_support_pair hcard L
          (goldenQ i) (goldenB i.succ) hqbk
        · fin_cases i <;> simp [goldenOrdinaryEdges, goldenQEdge]
        · simpa only [goldenQ, goldenB] using hs
      · exact (d.q_b_nonedge_impossible hcard L i k hk (by
          simpa only [goldenQ, goldenB] using hs)).elim
  · rcases v with i | b
    · have hqba : goldenQ i ≠ goldenB a := by simp [goldenQ, goldenB]
      by_cases ha : a = i.succ
      · subst a
        apply d.isGoldenEncodedOrdinaryLine_of_support_pair hcard L
          (goldenB i.succ) (goldenQ i) hqba.symm
        · rw [goldenOrdinaryEdgeOfNe_swap (goldenQ i) (goldenB i.succ) hqba]
          fin_cases i <;> simp [goldenOrdinaryEdges, goldenQEdge]
        · simpa only [goldenQ, goldenB] using hs
      · exact (d.q_b_nonedge_impossible hcard L i a ha (by
          simpa only [goldenQ, goldenB, Finset.pair_comm] using hs)).elim
    · have hab : a ≠ b := fun h => huv (congrArg Sum.inr h)
      let e := goldenOrdinaryEdgeOfNe (goldenB a) (goldenB b) (by
        simp [goldenB, hab])
      by_cases he : e ∈ goldenOrdinaryEdges
      · apply d.isGoldenEncodedOrdinaryLine_of_support_pair hcard L
          (goldenB a) (goldenB b) (by simp [goldenB, hab])
        · exact he
        · simpa only [e, goldenB] using hs
      · exact (d.b_b_nonedge_impossible hcard L a b hab (by
          simpa only [e] using he) (by simpa only [goldenB] using hs)).elim

/-- The data-valued golden edge classified by an ordinary inverted line. -/
noncomputable def classifiedGoldenEdge
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (L : DeterminedLineOfSize (pivotInversion cfg d.pivot.1) 2) :
    GoldenOrdinaryEdge :=
  Classical.choose (d.goldenOrdinaryLine_classified hcard L)

@[simp] theorem classifiedGoldenEdge_mem
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (L : DeterminedLineOfSize (pivotInversion cfg d.pivot.1) 2) :
    d.classifiedGoldenEdge hcard L ∈ goldenOrdinaryEdges :=
  (Classical.choose_spec (d.goldenOrdinaryLine_classified hcard L)).1

@[simp] theorem classifiedGoldenEdge_support
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (L : DeterminedLineOfSize (pivotInversion cfg d.pivot.1) 2) :
    lineSupport (pivotInversion cfg d.pivot.1) L.1 =
      d.encodeOrdinaryEdge hcard (d.classifiedGoldenEdge hcard L) :=
  (Classical.choose_spec (d.goldenOrdinaryLine_classified hcard L)).2

/-- Disjoint encoded supports reflect disjointness of their abstract golden
edges, because `awayEquiv` is a bijection. -/
theorem disjoint_goldenEdges_of_disjoint_encoded
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (e f : GoldenOrdinaryEdge)
    (hdisj : Disjoint (d.encodeOrdinaryEdge hcard e)
      (d.encodeOrdinaryEdge hcard f)) :
    Disjoint e.1 f.1 := by
  rw [Finset.disjoint_left] at hdisj ⊢
  intro x hxe hxf
  exact hdisj
    ((d.mem_encodeOrdinaryEdge hcard e x).mpr hxe)
    ((d.mem_encodeOrdinaryEdge hcard f x).mpr hxf)

/-- Three distinct original three-lines through the pivot are concurrent at
the pivot before inversion.  This deliberately records the source-side
concurrency separately from the finite matching classification. -/
theorem taggedThreeLines_concurrent_at_pivot
    (d : TenTwoPentagonSaturationData cfg)
    (b : Fin 3 → TaggedLineAtSize cfg d.pivot.1 3) :
    ∀ i : Fin 3, d.pivot.1 ∈ geometricBlockSupport cfg (b i).1 := by
  intro i
  exact (b i).2.2.2

/-- The three selected inverted ordinary lines are pairwise disjoint when
their source three-lines are distinct. -/
theorem taggedThreeLines_inverted_pairwiseDisjoint
    (d : TenTwoPentagonSaturationData cfg)
    (b : Fin 3 → TaggedLineAtSize cfg d.pivot.1 3)
    (hinj : Function.Injective b) :
    ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint
      (fun i => lineSupport (pivotInversion cfg d.pivot.1)
        (taggedThreeLineInvertedOrdinaryLine (b i)).1) := by
  intro i _hi j _hj hij
  exact taggedThreeLineInvertedOrdinaryLines_disjoint (hinj.ne hij)

/-- A data-valued label of exactly three original three-lines through the
pivot. -/
noncomputable def taggedThreeLineLabel
    (d : TenTwoPentagonSaturationData cfg)
    (hthree : (blockSystem cfg).lineDegree 3 d.pivot.1 = 3) :
    Fin 3 ≃ TaggedLineAtSize cfg d.pivot.1 3 := by
  apply (Fintype.equivFinOfCardEq ?_).symm
  rw [← lineDegree_eq_card_taggedLineAtSize]
  exact hthree

@[simp] theorem taggedThreeLineLabel_surjective
    (d : TenTwoPentagonSaturationData cfg)
    (hthree : (blockSystem cfg).lineDegree 3 d.pivot.1 = 3) :
    Function.Surjective (d.taggedThreeLineLabel hthree) :=
  (d.taggedThreeLineLabel hthree).surjective

/-- The three labelled source lines remain concurrent at the selected pivot. -/
theorem taggedThreeLineLabel_concurrent
    (d : TenTwoPentagonSaturationData cfg)
    (hthree : (blockSystem cfg).lineDegree 3 d.pivot.1 = 3) :
    ∀ i : Fin 3, d.pivot.1 ∈ geometricBlockSupport cfg
      (d.taggedThreeLineLabel hthree i).1 :=
  d.taggedThreeLines_concurrent_at_pivot (d.taggedThreeLineLabel hthree)

/-- The golden edge selected by a labelled original three-line after pivot
inversion. -/
noncomputable def taggedThreeLineGoldenEdge
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (hthree : (blockSystem cfg).lineDegree 3 d.pivot.1 = 3)
    (i : Fin 3) : GoldenOrdinaryEdge :=
  d.classifiedGoldenEdge hcard
    (taggedThreeLineInvertedOrdinaryLine (d.taggedThreeLineLabel hthree i))

@[simp] theorem taggedThreeLineGoldenEdge_mem
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (hthree : (blockSystem cfg).lineDegree 3 d.pivot.1 = 3)
    (i : Fin 3) :
    d.taggedThreeLineGoldenEdge hcard hthree i ∈ goldenOrdinaryEdges :=
  d.classifiedGoldenEdge_mem hcard
    (taggedThreeLineInvertedOrdinaryLine (d.taggedThreeLineLabel hthree i))

@[simp] theorem taggedThreeLineGoldenEdge_support
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (hthree : (blockSystem cfg).lineDegree 3 d.pivot.1 = 3)
    (i : Fin 3) :
    lineSupport (pivotInversion cfg d.pivot.1)
        (taggedThreeLineInvertedOrdinaryLine
          (d.taggedThreeLineLabel hthree i)).1 =
      d.encodeOrdinaryEdge hcard
        (d.taggedThreeLineGoldenEdge hcard hthree i) :=
  d.classifiedGoldenEdge_support hcard
    (taggedThreeLineInvertedOrdinaryLine (d.taggedThreeLineLabel hthree i))

/-- Distinct labelled three-lines yield distinct classified golden edges.
Indeed, equal encodings would make two disjoint ordinary supports equal,
whereas each has cardinality two. -/
theorem taggedThreeLineGoldenEdge_injective
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (hthree : (blockSystem cfg).lineDegree 3 d.pivot.1 = 3) :
    Function.Injective (d.taggedThreeLineGoldenEdge hcard hthree) := by
  intro i j hij
  by_contra hne
  have hpairwise := d.taggedThreeLines_inverted_pairwiseDisjoint
    (d.taggedThreeLineLabel hthree)
    (d.taggedThreeLineLabel hthree).injective
  have hsourceDisjoint : Disjoint
      (lineSupport (pivotInversion cfg d.pivot.1)
        (taggedThreeLineInvertedOrdinaryLine
          (d.taggedThreeLineLabel hthree i)).1)
      (lineSupport (pivotInversion cfg d.pivot.1)
        (taggedThreeLineInvertedOrdinaryLine
          (d.taggedThreeLineLabel hthree j)).1) :=
    hpairwise (by simp) (by simp) hne
  have hsupportEq :
      lineSupport (pivotInversion cfg d.pivot.1)
          (taggedThreeLineInvertedOrdinaryLine
            (d.taggedThreeLineLabel hthree i)).1 =
        lineSupport (pivotInversion cfg d.pivot.1)
          (taggedThreeLineInvertedOrdinaryLine
            (d.taggedThreeLineLabel hthree j)).1 := by
    rw [d.taggedThreeLineGoldenEdge_support hcard hthree i,
      d.taggedThreeLineGoldenEdge_support hcard hthree j, hij]
  have hself : Disjoint
      (lineSupport (pivotInversion cfg d.pivot.1)
        (taggedThreeLineInvertedOrdinaryLine
          (d.taggedThreeLineLabel hthree i)).1)
      (lineSupport (pivotInversion cfg d.pivot.1)
        (taggedThreeLineInvertedOrdinaryLine
          (d.taggedThreeLineLabel hthree i)).1) := by
    rw [← hsupportEq] at hsourceDisjoint
    exact hsourceDisjoint
  have hempty : lineSupport (pivotInversion cfg d.pivot.1)
      (taggedThreeLineInvertedOrdinaryLine
        (d.taggedThreeLineLabel hthree i)).1 = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro z hz
    exact (Finset.disjoint_left.mp hself) hz hz
  have htwo :=
    (taggedThreeLineInvertedOrdinaryLine
      (d.taggedThreeLineLabel hthree i)).2
  rw [hempty] at htwo
  simp at htwo

/-- The three classified golden edges have pairwise disjoint abstract
supports. -/
theorem taggedThreeLineGoldenEdge_pairwiseDisjoint
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (hthree : (blockSystem cfg).lineDegree 3 d.pivot.1 = 3)
    (i j : Fin 3) (hij : i ≠ j) :
    Disjoint (d.taggedThreeLineGoldenEdge hcard hthree i).1
      (d.taggedThreeLineGoldenEdge hcard hthree j).1 := by
  apply d.disjoint_goldenEdges_of_disjoint_encoded hcard
  have hpairwise := d.taggedThreeLines_inverted_pairwiseDisjoint
    (d.taggedThreeLineLabel hthree)
    (d.taggedThreeLineLabel hthree).injective
  have hsourceDisjoint : Disjoint
      (lineSupport (pivotInversion cfg d.pivot.1)
        (taggedThreeLineInvertedOrdinaryLine
          (d.taggedThreeLineLabel hthree i)).1)
      (lineSupport (pivotInversion cfg d.pivot.1)
        (taggedThreeLineInvertedOrdinaryLine
          (d.taggedThreeLineLabel hthree j)).1) :=
    hpairwise (by simp) (by simp) hij
  simpa only [d.taggedThreeLineGoldenEdge_support hcard hthree i,
    d.taggedThreeLineGoldenEdge_support hcard hthree j] using hsourceDisjoint

/-! ## Finite normalization of a classified three-line selection -/

/-- The finite edge family selected by three labelled source lines. -/
def goldenThreeEdgeImage (edge : Fin 3 → GoldenOrdinaryEdge) :
    Finset GoldenOrdinaryEdge :=
  Finset.univ.image edge

/-- Any injective choice of three pairwise disjoint displayed golden edges
is normalized by the checked `2P4` matching theorem.  The geometric
classifier supplies the hypotheses of this purely finite bridge. -/
theorem goldenThreeEdgeImage_end_or_middle
    (edge : Fin 3 → GoldenOrdinaryEdge)
    (hmem : ∀ i, edge i ∈ goldenOrdinaryEdges)
    (hinj : Function.Injective edge)
    (hdisj : ∀ i j, i ≠ j → Disjoint (edge i).1 (edge j).1) :
    ∃ k : Fin 4,
      goldenPermuteMatching (goldenCycleVertex ^ k.val)
          (goldenThreeEdgeImage edge) = goldenCanonicalEndMatching ∨
        goldenPermuteMatching (goldenCycleVertex ^ k.val)
          (goldenThreeEdgeImage edge) = goldenCanonicalMiddleMatching := by
  have hsubset : goldenThreeEdgeImage edge ⊆ goldenOrdinaryEdges := by
    intro e he
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp he
    exact hmem i
  have hcard : (goldenThreeEdgeImage edge).card = 3 := by
    unfold goldenThreeEdgeImage
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hM : goldenThreeEdgeImage edge ∈
      goldenOrdinaryEdges.powersetCard 3 :=
    Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩
  have hmatching : GoldenOrdinaryIsMatching (goldenThreeEdgeImage edge) := by
    intro e he f hf hef
    obtain ⟨i, _hi, hie⟩ := Finset.mem_image.mp he
    obtain ⟨j, _hj, hjf⟩ := Finset.mem_image.mp hf
    subst e
    subst f
    apply hdisj i j
    intro hij
    apply hef
    simp only [hij]
  exact goldenThreeMatching_end_or_middle
    (goldenThreeEdgeImage edge) hM hmatching

/-- The three original three-lines through the pivot classify as one of the
two finite golden three-edge matching normal forms.  The source lines remain
concurrent at the pivot by `taggedThreeLineLabel_concurrent`; inversion is
used only to obtain this finite matching. -/
theorem taggedThreeLineGoldenEdge_end_or_middle
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (hthree : (blockSystem cfg).lineDegree 3 d.pivot.1 = 3) :
    ∃ k : Fin 4,
      goldenPermuteMatching (goldenCycleVertex ^ k.val)
          (goldenThreeEdgeImage (d.taggedThreeLineGoldenEdge hcard hthree)) =
        goldenCanonicalEndMatching ∨
      goldenPermuteMatching (goldenCycleVertex ^ k.val)
          (goldenThreeEdgeImage (d.taggedThreeLineGoldenEdge hcard hthree)) =
        goldenCanonicalMiddleMatching := by
  exact goldenThreeEdgeImage_end_or_middle
    (d.taggedThreeLineGoldenEdge hcard hthree)
    (d.taggedThreeLineGoldenEdge_mem hcard hthree)
    (d.taggedThreeLineGoldenEdge_injective hcard hthree)
    (d.taggedThreeLineGoldenEdge_pairwiseDisjoint hcard hthree)

/-- Orbit-oriented version of the three-line classification.  This is the
form used by downstream concurrency code, which relabels its raw arrays
forward by the returned cycle power. -/
theorem taggedThreeLineGoldenEdge_in_end_or_middle_orbit
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (hthree : (blockSystem cfg).lineDegree 3 d.pivot.1 = 3) :
    ∃ k : Fin 4,
      goldenThreeEdgeImage (d.taggedThreeLineGoldenEdge hcard hthree) =
          goldenPermuteMatching (goldenCycleVertex ^ k.val)
            goldenCanonicalEndMatching ∨
        goldenThreeEdgeImage (d.taggedThreeLineGoldenEdge hcard hthree) =
          goldenPermuteMatching (goldenCycleVertex ^ k.val)
            goldenCanonicalMiddleMatching := by
  apply goldenThreeMatching_in_end_or_middle_orbit
  · have hsubset : goldenThreeEdgeImage
        (d.taggedThreeLineGoldenEdge hcard hthree) ⊆ goldenOrdinaryEdges := by
      intro e he
      obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp he
      exact d.taggedThreeLineGoldenEdge_mem hcard hthree i
    have himageCard : (goldenThreeEdgeImage
        (d.taggedThreeLineGoldenEdge hcard hthree)).card = 3 := by
      unfold goldenThreeEdgeImage
      rw [Finset.card_image_of_injective _
        (d.taggedThreeLineGoldenEdge_injective hcard hthree)]
      simp
    exact Finset.mem_powersetCard.mpr ⟨hsubset, himageCard⟩
  · intro e he f hf hef
    obtain ⟨i, _hi, hie⟩ := Finset.mem_image.mp he
    obtain ⟨j, _hj, hjf⟩ := Finset.mem_image.mp hf
    subst e
    subst f
    apply d.taggedThreeLineGoldenEdge_pairwiseDisjoint hcard hthree i j
    intro hij
    apply hef
    simp only [hij]

end TenTwoPentagonSaturationData

end Erdos506.V1
