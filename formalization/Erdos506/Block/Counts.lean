import Erdos506.Block.System
import Erdos506.Finite.RelativeOwner

/-!
# Size counts and incidence rows for tagged block systems

All counts in this file are finite.  Blocks are grouped by their full support
cardinality, and the basic rows are obtained by finite double counting rather
than by enumerating configurations.
-/

namespace Erdos506.Block

open scoped BigOperators

namespace BlockSystem

variable {Point Block : Type*} [Fintype Point] [Fintype Block]
  [DecidableEq Point]

/-- All blocks with a specified support cardinality. -/
def blocksOfSize (S : BlockSystem Point Block) (s : ℕ) : Finset Block :=
  Finset.univ.filter fun b => (S.support b).card = s

/-- All blocks of a specified kind. -/
def blocksOfKind (S : BlockSystem Point Block) (k : BlockKind) : Finset Block :=
  Finset.univ.filter fun b => S.kind b = k

/-- Blocks of a specified kind and support cardinality. -/
def blocksOfKindSize (S : BlockSystem Point Block) (k : BlockKind)
    (s : ℕ) : Finset Block :=
  (S.blocksOfKind k).filter fun b => (S.support b).card = s

abbrev lineBlocksOfSize (S : BlockSystem Point Block) (s : ℕ) :=
  S.blocksOfKindSize .line s

abbrev circleBlocksOfSize (S : BlockSystem Point Block) (s : ℕ) :=
  S.blocksOfKindSize .circle s

def blockCount (S : BlockSystem Point Block) (s : ℕ) : ℕ :=
  (S.blocksOfSize s).card

def lineCount (S : BlockSystem Point Block) (s : ℕ) : ℕ :=
  (S.lineBlocksOfSize s).card

def circleCount (S : BlockSystem Point Block) (s : ℕ) : ℕ :=
  (S.circleBlocksOfSize s).card

/-- Number of blocks in a finite family that contain a point. -/
def degreeIn (S : BlockSystem Point Block) (F : Finset Block)
    (p : Point) : ℕ :=
  (F.filter fun b => p ∈ S.support b).card

def blockDegree (S : BlockSystem Point Block) (s : ℕ) (p : Point) : ℕ :=
  S.degreeIn (S.blocksOfSize s) p

def lineDegree (S : BlockSystem Point Block) (s : ℕ) (p : Point) : ℕ :=
  S.degreeIn (S.lineBlocksOfSize s) p

def circleDegree (S : BlockSystem Point Block) (s : ℕ) (p : Point) : ℕ :=
  S.degreeIn (S.circleBlocksOfSize s) p

@[simp] theorem mem_blocksOfSize (S : BlockSystem Point Block)
    {s : ℕ} {b : Block} :
    b ∈ S.blocksOfSize s ↔ (S.support b).card = s := by
  simp [blocksOfSize]

@[simp] theorem mem_blocksOfKind (S : BlockSystem Point Block)
    {k : BlockKind} {b : Block} :
    b ∈ S.blocksOfKind k ↔ S.kind b = k := by
  simp [blocksOfKind]

@[simp] theorem mem_blocksOfKindSize (S : BlockSystem Point Block)
    {k : BlockKind} {s : ℕ} {b : Block} :
    b ∈ S.blocksOfKindSize k s ↔ S.kind b = k ∧ (S.support b).card = s := by
  simp [blocksOfKindSize]

/-- Every size layer is the disjoint union of its line and circle layers. -/
theorem blockCount_eq_lineCount_add_circleCount
    (S : BlockSystem Point Block) (s : ℕ) :
    S.blockCount s = S.lineCount s + S.circleCount s := by
  classical
  let F := S.blocksOfSize s
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := F) (fun b => S.kind b = .line)
  have hline :
      F.filter (fun b => S.kind b = .line) = S.lineBlocksOfSize s := by
    ext b
    simp [F, blocksOfSize, blocksOfKindSize, blocksOfKind, and_comm]
  have hcircle :
      F.filter (fun b => ¬S.kind b = .line) = S.circleBlocksOfSize s := by
    ext b
    cases hkind : S.kind b <;>
      simp [F, blocksOfSize, blocksOfKindSize, blocksOfKind, hkind, and_comm]
  rw [hline, hcircle] at hsplit
  exact hsplit.symm

/-- A support size larger than the point set has no blocks. -/
theorem blockCount_eq_zero_of_card_lt (S : BlockSystem Point Block)
    {s : ℕ} (hs : Fintype.card Point < s) :
    S.blockCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hcard : (S.support b).card = s := (S.mem_blocksOfSize).mp hb
  have hle := S.support_card_le_point_card b
  omega

theorem lineCount_eq_zero_of_card_lt (S : BlockSystem Point Block)
    {s : ℕ} (hs : Fintype.card Point < s) :
    S.lineCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hcard : (S.support b).card = s := (S.mem_blocksOfKindSize).mp hb |>.2
  have hle := S.support_card_le_point_card b
  omega

theorem circleCount_eq_zero_of_card_lt (S : BlockSystem Point Block)
    {s : ℕ} (hs : Fintype.card Point < s) :
    S.circleCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hcard : (S.support b).card = s := (S.mem_blocksOfKindSize).mp hb |>.2
  have hle := S.support_card_le_point_card b
  omega

theorem lineCount_eq_zero_of_lt_two (S : BlockSystem Point Block)
    {s : ℕ} (hs : s < 2) : S.lineCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hspec := S.mem_blocksOfKindSize.mp hb
  have hmin := S.line_min b hspec.1
  omega

theorem circleCount_eq_zero_of_lt_three (S : BlockSystem Point Block)
    {s : ℕ} (hs : s < 3) : S.circleCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hspec := S.mem_blocksOfKindSize.mp hb
  have hmin := S.circle_min b hspec.1
  omega

/-- Point--block incidence double count for an arbitrary finite block family. -/
theorem sum_degreeIn (S : BlockSystem Point Block) (F : Finset Block) :
    (∑ p : Point, S.degreeIn F p) =
      ∑ b ∈ F, (S.support b).card := by
  classical
  simp only [degreeIn, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/-- Incidence Fubini restricted to an arbitrary finite set of points. -/
theorem sum_degreeIn_over (S : BlockSystem Point Block)
    (F : Finset Block) (D : Finset Point) :
    (∑ x ∈ D, S.degreeIn F x) =
      ∑ b ∈ F, (D ∩ S.support b).card := by
  classical
  simp only [degreeIn, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  simp

/-- The global point--block incidence row at a fixed support size. -/
theorem block_incidence (S : BlockSystem Point Block) (s : ℕ) :
    (∑ p : Point, S.blockDegree s p) = s * S.blockCount s := by
  change (∑ p : Point, S.degreeIn (S.blocksOfSize s) p) = _
  rw [S.sum_degreeIn]
  calc
    (∑ b ∈ S.blocksOfSize s, (S.support b).card) =
        (S.blocksOfSize s).card * s := by
      apply Finset.sum_const_nat
      intro b hb
      exact S.mem_blocksOfSize.mp hb
    _ = s * S.blockCount s := by simp [blockCount, Nat.mul_comm]

theorem line_incidence (S : BlockSystem Point Block) (s : ℕ) :
    (∑ p : Point, S.lineDegree s p) = s * S.lineCount s := by
  change (∑ p : Point, S.degreeIn (S.lineBlocksOfSize s) p) = _
  rw [S.sum_degreeIn]
  calc
    (∑ b ∈ S.lineBlocksOfSize s, (S.support b).card) =
        (S.lineBlocksOfSize s).card * s := by
      apply Finset.sum_const_nat
      intro b hb
      exact (S.mem_blocksOfKindSize.mp hb).2
    _ = s * S.lineCount s := by simp [lineCount, Nat.mul_comm]

theorem circle_incidence (S : BlockSystem Point Block) (s : ℕ) :
    (∑ p : Point, S.circleDegree s p) = s * S.circleCount s := by
  change (∑ p : Point, S.degreeIn (S.circleBlocksOfSize s) p) = _
  rw [S.sum_degreeIn]
  calc
    (∑ b ∈ S.circleBlocksOfSize s, (S.support b).card) =
        (S.circleBlocksOfSize s).card * s := by
      apply Finset.sum_const_nat
      intro b hb
      exact (S.mem_blocksOfKindSize.mp hb).2
    _ = s * S.circleCount s := by simp [circleCount, Nat.mul_comm]

/-- Group a weighted finite subfamily by support size. -/
theorem sum_familyCount_weight (S : BlockSystem Point Block)
    (F : Finset Block) (w : ℕ → ℕ) :
    (∑ s ∈ Finset.range (Fintype.card Point + 1),
        w s * (F.filter fun b => (S.support b).card = s).card) =
      ∑ b ∈ F, w (S.support b).card := by
  classical
  have hmaps : ∀ b ∈ F,
      (S.support b).card ∈ Finset.range (Fintype.card Point + 1) := by
    intro b _hb
    simp only [Finset.mem_range]
    exact Nat.lt_succ_of_le (S.support_card_le_point_card b)
  have hgroup := Finset.sum_fiberwise_of_maps_to hmaps
    (fun b : Block => w (S.support b).card)
  calc
    (∑ s ∈ Finset.range (Fintype.card Point + 1),
        w s * (F.filter fun b => (S.support b).card = s).card) =
        ∑ s ∈ Finset.range (Fintype.card Point + 1),
          ∑ b ∈ F with (S.support b).card = s,
            w (S.support b).card := by
      apply Finset.sum_congr rfl
      intro s hs
      symm
      calc
        (∑ b ∈ F with (S.support b).card = s,
            w (S.support b).card) =
            (F.filter fun b => (S.support b).card = s).card * w s := by
          apply Finset.sum_const_nat
          intro b hb
          exact congrArg w (Finset.mem_filter.mp hb).2
        _ = w s * (F.filter fun b => (S.support b).card = s).card := by
          rw [Nat.mul_comm]
    _ = ∑ b ∈ F, w (S.support b).card := hgroup

/-- Group an arbitrary natural-valued block weight by full support size. -/
theorem sum_blockCount_weight (S : BlockSystem Point Block) (w : ℕ → ℕ) :
    (∑ s ∈ Finset.range (Fintype.card Point + 1), w s * S.blockCount s) =
      ∑ b : Block, w (S.support b).card := by
  classical
  have hmaps : ∀ b ∈ (Finset.univ : Finset Block),
      (S.support b).card ∈ Finset.range (Fintype.card Point + 1) := by
    intro b _hb
    simp only [Finset.mem_range]
    exact Nat.lt_succ_of_le (S.support_card_le_point_card b)
  have hgroup := Finset.sum_fiberwise_of_maps_to hmaps
    (fun b : Block => w (S.support b).card)
  calc
    (∑ s ∈ Finset.range (Fintype.card Point + 1),
        w s * S.blockCount s) =
        ∑ s ∈ Finset.range (Fintype.card Point + 1),
          ∑ b ∈ (Finset.univ : Finset Block) with (S.support b).card = s,
            w (S.support b).card := by
      apply Finset.sum_congr rfl
      intro s hs
      symm
      calc
        (∑ b ∈ (Finset.univ : Finset Block) with (S.support b).card = s,
            w (S.support b).card) =
            ∑ b ∈ S.blocksOfSize s, w (S.support b).card := by
          simp [blocksOfSize]
        _ = (S.blocksOfSize s).card * w s := by
          apply Finset.sum_const_nat
          intro b hb
          exact congrArg w (S.mem_blocksOfSize.mp hb)
        _ = w s * S.blockCount s := by simp [blockCount, Nat.mul_comm]
    _ = ∑ b ∈ (Finset.univ : Finset Block), w (S.support b).card := hgroup
    _ = ∑ b : Block, w (S.support b).card := by simp

/-- The same grouping restricted to one block tag. -/
theorem sum_kindCount_weight (S : BlockSystem Point Block)
    (k : BlockKind) (w : ℕ → ℕ) :
    (∑ s ∈ Finset.range (Fintype.card Point + 1),
        w s * (S.blocksOfKindSize k s).card) =
      ∑ b ∈ S.blocksOfKind k, w (S.support b).card := by
  classical
  have hmaps : ∀ b ∈ S.blocksOfKind k,
      (S.support b).card ∈ Finset.range (Fintype.card Point + 1) := by
    intro b _hb
    simp only [Finset.mem_range]
    exact Nat.lt_succ_of_le (S.support_card_le_point_card b)
  have hgroup := Finset.sum_fiberwise_of_maps_to hmaps
    (fun b : Block => w (S.support b).card)
  calc
    (∑ s ∈ Finset.range (Fintype.card Point + 1),
        w s * (S.blocksOfKindSize k s).card) =
        ∑ s ∈ Finset.range (Fintype.card Point + 1),
          ∑ b ∈ S.blocksOfKind k with (S.support b).card = s,
            w (S.support b).card := by
      apply Finset.sum_congr rfl
      intro s hs
      symm
      calc
        (∑ b ∈ S.blocksOfKind k with (S.support b).card = s,
            w (S.support b).card) =
            ∑ b ∈ S.blocksOfKindSize k s, w (S.support b).card := by
          simp [blocksOfKindSize]
        _ = (S.blocksOfKindSize k s).card * w s := by
          apply Finset.sum_const_nat
          intro b hb
          exact congrArg w (S.mem_blocksOfKindSize.mp hb).2
        _ = w s * (S.blocksOfKindSize k s).card := by
          rw [Nat.mul_comm]
    _ = ∑ b ∈ S.blocksOfKind k, w (S.support b).card := hgroup

/-- Triple ownership, now grouped into the manuscript's size rows. -/
theorem triple_partition_by_size (S : BlockSystem Point Block) :
    (∑ s ∈ Finset.range (Fintype.card Point + 1),
        Nat.choose s 3 * S.blockCount s) =
      Nat.choose (Fintype.card Point) 3 := by
  rw [S.sum_blockCount_weight (fun s => Nat.choose s 3)]
  exact S.triple_partition

/-- Pair ownership by line blocks, grouped by line support size. -/
theorem line_pair_partition_by_size (S : BlockSystem Point Block) :
    (∑ s ∈ Finset.range (Fintype.card Point + 1),
        Nat.choose s 2 * S.lineCount s) =
      Nat.choose (Fintype.card Point) 2 := by
  change (∑ s ∈ Finset.range (Fintype.card Point + 1),
      Nat.choose s 2 * (S.blocksOfKindSize .line s).card) = _
  rw [S.sum_kindCount_weight .line (fun s => Nat.choose s 2)]
  calc
    (∑ b ∈ S.blocksOfKind .line, Nat.choose (S.support b).card 2) =
        ∑ b : LineBlock S, Nat.choose (S.support b.1).card 2 := by
      simpa [blocksOfKind] using
        (Finset.sum_subtype (S.blocksOfKind .line)
          (fun b => by simp [blocksOfKind])
          (fun b => Nat.choose (S.support b).card 2))
    _ = Nat.choose (Fintype.card Point) 2 := S.line_pair_partition

/-- Total number of circle-tagged blocks. -/
def totalCircleCount (S : BlockSystem Point Block) : ℕ :=
  (S.blocksOfKind .circle).card

theorem totalCircleCount_eq_sum_circleCount (S : BlockSystem Point Block) :
    S.totalCircleCount =
      ∑ s ∈ Finset.range (Fintype.card Point + 1), S.circleCount s := by
  have h := S.sum_kindCount_weight .circle (fun _ => 1)
  calc
    S.totalCircleCount = ∑ b ∈ S.blocksOfKind .circle, 1 :=
      Finset.card_eq_sum_ones (S.blocksOfKind .circle)
    _ = ∑ s ∈ Finset.range (Fintype.card Point + 1),
        1 * (S.blocksOfKindSize .circle s).card := h.symm
    _ = ∑ s ∈ Finset.range (Fintype.card Point + 1), S.circleCount s := by
      simp [circleCount]

/-- Triple ownership refined by the number of labels in a fixed set `D`. -/
theorem relative_triple_partition (S : BlockSystem Point Block)
    (D : Finset Point) (j : ℕ) (hj : j ≤ 3) :
    (∑ b : Block,
        Nat.choose (S.support b ∩ D).card j *
          Nat.choose (S.support b \ D).card (3 - j)) =
      Nat.choose D.card j *
        Nat.choose (Fintype.card Point - D.card) (3 - j) :=
  (S.tripleOwnership.relative_owner_partition D j hj)

/-- Pair ownership by lines, refined relative to a fixed set `D`. -/
theorem relative_line_pair_partition (S : BlockSystem Point Block)
    (D : Finset Point) (j : ℕ) (hj : j ≤ 2) :
    (∑ b : LineBlock S,
        Nat.choose (S.support b.1 ∩ D).card j *
          Nat.choose (S.support b.1 \ D).card (2 - j)) =
      Nat.choose D.card j *
        Nat.choose (Fintype.card Point - D.card) (2 - j) :=
  (S.lineOwnership.relative_owner_partition D j hj)

/-- Triples containing a fixed point, counted through their owning blocks. -/
theorem pivot_pair_partition_blocks (S : BlockSystem Point Block) (p : Point) :
    (∑ b ∈ (Finset.univ.filter fun b : Block => p ∈ S.support b),
        Nat.choose ((S.support b).card - 1) 2) =
      Nat.choose (Fintype.card Point - 1) 2 := by
  classical
  have hrel := S.relative_triple_partition ({p} : Finset Point) 1 (by omega)
  have hterms :
      (∑ b : Block, if p ∈ S.support b then
          Nat.choose ((S.support b).card - 1) 2 else 0) =
        Nat.choose (Fintype.card Point - 1) 2 := by
    calc
      (∑ b : Block, if p ∈ S.support b then
          Nat.choose ((S.support b).card - 1) 2 else 0) =
          ∑ b : Block,
            Nat.choose (S.support b ∩ {p}).card 1 *
              Nat.choose (S.support b \ {p}).card 2 := by
        apply Fintype.sum_congr
        intro b
        by_cases hp : p ∈ S.support b
        · have hsub : ({p} : Finset Point) ⊆ S.support b := by simpa
          simp [hp, Finset.card_sdiff_of_subset hsub]
        · simp [hp]
      _ = Nat.choose (Fintype.card Point - 1) 2 := by
        simpa using hrel
  rw [Finset.sum_filter]
  simpa using hterms

/-- Pivot triple ownership in the manuscript's size/degree notation. -/
theorem pivot_pair_partition (S : BlockSystem Point Block) (p : Point) :
    (∑ s ∈ Finset.range (Fintype.card Point + 1),
        Nat.choose (s - 1) 2 * S.blockDegree s p) =
      Nat.choose (Fintype.card Point - 1) 2 := by
  classical
  let F : Finset Block := Finset.univ.filter fun b => p ∈ S.support b
  have hgroup := S.sum_familyCount_weight F
    (fun s => Nat.choose (s - 1) 2)
  calc
    (∑ s ∈ Finset.range (Fintype.card Point + 1),
        Nat.choose (s - 1) 2 * S.blockDegree s p) =
        ∑ s ∈ Finset.range (Fintype.card Point + 1),
          Nat.choose (s - 1) 2 *
            (F.filter fun b => (S.support b).card = s).card := by
      apply Finset.sum_congr rfl
      intro s hs
      congr 1
      apply congrArg Finset.card
      ext b
      simp [F, blocksOfSize, and_comm]
    _ = ∑ b ∈ F, Nat.choose ((S.support b).card - 1) 2 := hgroup
    _ = Nat.choose (Fintype.card Point - 1) 2 := by
      simpa [F] using S.pivot_pair_partition_blocks p

/-- The line traces through a fixed point partition all other labels. -/
theorem line_arms_blocks (S : BlockSystem Point Block) (p : Point) :
    (∑ b ∈ ((S.blocksOfKind .line).filter fun b => p ∈ S.support b),
        ((S.support b).card - 1)) = Fintype.card Point - 1 := by
  classical
  have hrel := S.relative_line_pair_partition ({p} : Finset Point) 1 (by omega)
  have hsubtype :
      (∑ b : LineBlock S, if p ∈ S.support b.1 then
          (S.support b.1).card - 1 else 0) =
        Fintype.card Point - 1 := by
    calc
      (∑ b : LineBlock S, if p ∈ S.support b.1 then
          (S.support b.1).card - 1 else 0) =
          ∑ b : LineBlock S,
            Nat.choose (S.support b.1 ∩ {p}).card 1 *
              Nat.choose (S.support b.1 \ {p}).card 1 := by
        apply Fintype.sum_congr
        intro b
        by_cases hp : p ∈ S.support b.1
        · have hsub : ({p} : Finset Point) ⊆ S.support b.1 := by simpa
          simp [hp, Finset.card_sdiff_of_subset hsub]
        · simp [hp]
      _ = Fintype.card Point - 1 := by simpa using hrel
  rw [Finset.sum_filter]
  calc
    (∑ b ∈ S.blocksOfKind .line,
        if p ∈ S.support b then (S.support b).card - 1 else 0) =
        ∑ b : LineBlock S,
          if p ∈ S.support b.1 then (S.support b.1).card - 1 else 0 := by
      simpa [blocksOfKind] using
        (Finset.sum_subtype (S.blocksOfKind .line)
          (fun b => by simp [blocksOfKind])
          (fun b => if p ∈ S.support b then (S.support b).card - 1 else 0))
    _ = Fintype.card Point - 1 := hsubtype

/-- The line-arm partition grouped by support size. -/
theorem line_arms (S : BlockSystem Point Block) (p : Point) :
    (∑ s ∈ Finset.range (Fintype.card Point + 1),
        (s - 1) * S.lineDegree s p) = Fintype.card Point - 1 := by
  classical
  let F : Finset Block :=
    (S.blocksOfKind .line).filter fun b => p ∈ S.support b
  have hgroup := S.sum_familyCount_weight F (fun s => s - 1)
  calc
    (∑ s ∈ Finset.range (Fintype.card Point + 1),
        (s - 1) * S.lineDegree s p) =
        ∑ s ∈ Finset.range (Fintype.card Point + 1),
          (s - 1) * (F.filter fun b => (S.support b).card = s).card := by
      apply Finset.sum_congr rfl
      intro s hs
      congr 1
      apply congrArg Finset.card
      ext b
      simp [F, blocksOfKindSize, blocksOfKind,
        and_comm, and_left_comm, and_assoc]
    _ = ∑ b ∈ F, ((S.support b).card - 1) := hgroup
    _ = Fintype.card Point - 1 := by
      simpa [F] using S.line_arms_blocks p

end BlockSystem
end Erdos506.Block
