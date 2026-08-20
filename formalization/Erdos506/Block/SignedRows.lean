import Erdos506.Block.Moments
import Mathlib.Tactic

/-!
# Exact signed block rows

The manuscript's universal scalar rows are identities in `Int`.  Keeping all
subtractions signed prevents truncated natural subtraction from concealing a
false equality.  No nonnegativity or incidence theorem is assumed here.
-/

namespace Erdos506.Block

open scoped BigOperators

namespace BlockSystem

variable {Point Block : Type*} [Fintype Point] [Fintype Block]
  [DecidableEq Point]

/-- Support sizes from three through the size of the point set. -/
def nontrivialSizes (_S : BlockSystem Point Block) : Finset ℕ :=
  Finset.Icc 3 (Fintype.card Point)

/-- The signed local pivot expression before geometric nonnegativity. -/
def pivotSigma (S : BlockSystem Point Block) (p : Point) : ℤ :=
  (∑ s ∈ S.nontrivialSizes,
      (4 - (s : ℤ)) * (S.blockDegree s p : ℤ)) - 3

/-- The global signed row `P`. -/
def pivotRow (S : BlockSystem Point Block) : ℤ :=
  ∑ s ∈ S.nontrivialSizes,
    (s : ℤ) * (4 - (s : ℤ)) * (S.blockCount s : ℤ)

/-- Blocks of support size at least three through a fixed point. -/
abbrev NontrivialBlockAt (S : BlockSystem Point Block) (p : Point) :=
  {b : Block // p ∈ S.support b ∧ 3 ≤ (S.support b).card}

/-- All blocks through a fixed point. -/
abbrev BlockAt (S : BlockSystem Point Block) (p : Point) :=
  {b : Block // p ∈ S.support b}

/-- Line blocks of support size at least three through a fixed point. -/
abbrev NontrivialLineAt (S : BlockSystem Point Block) (p : Point) :=
  {b : Block //
    p ∈ S.support b ∧ S.kind b = .line ∧ 3 ≤ (S.support b).card}

/-- Group an integer-valued weight over blocks through one point by support
size. -/
theorem sum_nontrivialBlockAt_weight (S : BlockSystem Point Block)
    (p : Point) (w : ℕ → ℤ) :
    (∑ s ∈ S.nontrivialSizes,
        w s * (S.blockDegree s p : ℤ)) =
      ∑ b : NontrivialBlockAt S p, w (S.support b.1).card := by
  classical
  let F : Finset Block := Finset.univ.filter fun b =>
    p ∈ S.support b ∧ 3 ≤ (S.support b).card
  have hmaps : ∀ b ∈ F, (S.support b).card ∈ S.nontrivialSizes := by
    intro b hb
    have hspec := Finset.mem_filter.mp hb |>.2
    exact Finset.mem_Icc.mpr
      ⟨hspec.2, S.support_card_le_point_card b⟩
  have hgroup := Finset.sum_fiberwise_of_maps_to hmaps
    (fun b : Block => w (S.support b).card)
  calc
    (∑ s ∈ S.nontrivialSizes,
        w s * (S.blockDegree s p : ℤ)) =
        ∑ s ∈ S.nontrivialSizes,
          ∑ b ∈ F with (S.support b).card = s,
            w (S.support b).card := by
      apply Finset.sum_congr rfl
      intro s hs
      have hs3 : 3 ≤ s := (Finset.mem_Icc.mp hs).1
      let G := F.filter fun b => (S.support b).card = s
      have hGcard : G.card = S.blockDegree s p := by
        apply congrArg Finset.card
        ext b
        constructor
        · intro hb
          have hb' := Finset.mem_filter.mp hb
          have hbF := Finset.mem_filter.mp hb'.1
          apply Finset.mem_filter.mpr
          exact ⟨S.mem_blocksOfSize.mpr hb'.2, hbF.2.1⟩
        · intro hb
          have hb' := Finset.mem_filter.mp hb
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ b,
            hb'.2, ?_⟩, ?_⟩
          · rw [S.mem_blocksOfSize.mp hb'.1]
            exact hs3
          · exact S.mem_blocksOfSize.mp hb'.1
      symm
      calc
        (∑ b ∈ F with (S.support b).card = s,
            w (S.support b).card) = ∑ _b ∈ G, w s := by
          apply Finset.sum_congr rfl
          intro b hb
          exact congrArg w (Finset.mem_filter.mp hb).2
        _ = (G.card : ℤ) * w s := by simp
        _ = w s * (S.blockDegree s p : ℤ) := by
          rw [hGcard]
          ring
    _ = ∑ b ∈ F, w (S.support b).card := hgroup
    _ = ∑ b : NontrivialBlockAt S p, w (S.support b.1).card := by
      simpa [F] using
        (Finset.sum_subtype F
          (fun b => by simp [F])
          (fun b => w (S.support b).card))

/-- The line-tagged analogue of `sum_nontrivialBlockAt_weight`. -/
theorem sum_nontrivialLineAt_weight (S : BlockSystem Point Block)
    (p : Point) (w : ℕ → ℤ) :
    (∑ s ∈ S.nontrivialSizes,
        w s * (S.lineDegree s p : ℤ)) =
      ∑ b : NontrivialLineAt S p, w (S.support b.1).card := by
  classical
  let F : Finset Block := Finset.univ.filter fun b =>
    p ∈ S.support b ∧ S.kind b = .line ∧ 3 ≤ (S.support b).card
  have hmaps : ∀ b ∈ F, (S.support b).card ∈ S.nontrivialSizes := by
    intro b hb
    have hspec := Finset.mem_filter.mp hb |>.2
    exact Finset.mem_Icc.mpr
      ⟨hspec.2.2, S.support_card_le_point_card b⟩
  have hgroup := Finset.sum_fiberwise_of_maps_to hmaps
    (fun b : Block => w (S.support b).card)
  calc
    (∑ s ∈ S.nontrivialSizes,
        w s * (S.lineDegree s p : ℤ)) =
        ∑ s ∈ S.nontrivialSizes,
          ∑ b ∈ F with (S.support b).card = s,
            w (S.support b).card := by
      apply Finset.sum_congr rfl
      intro s hs
      have hs3 : 3 ≤ s := (Finset.mem_Icc.mp hs).1
      let G := F.filter fun b => (S.support b).card = s
      have hGcard : G.card = S.lineDegree s p := by
        apply congrArg Finset.card
        ext b
        simp [G, F, blocksOfKindSize, blocksOfKind,
          and_comm, and_left_comm, and_assoc]
        omega
      symm
      calc
        (∑ b ∈ F with (S.support b).card = s,
            w (S.support b).card) = ∑ _b ∈ G, w s := by
          apply Finset.sum_congr rfl
          intro b hb
          exact congrArg w (Finset.mem_filter.mp hb).2
        _ = (G.card : ℤ) * w s := by simp
        _ = w s * (S.lineDegree s p : ℤ) := by
          rw [hGcard]
          ring
    _ = ∑ b ∈ F, w (S.support b).card := hgroup
    _ = ∑ b : NontrivialLineAt S p, w (S.support b.1).card := by
      simpa [F] using
        (Finset.sum_subtype F
          (fun b => by simp [F])
          (fun b => w (S.support b).card))

/-- Rewrite a sum over blocks through a point as an unrestricted sum with an
incidence indicator. -/
theorem sum_blockAt_weight (S : BlockSystem Point Block)
    (p : Point) (w : Block → ℤ) :
    (∑ b : BlockAt S p, w b.1) =
      ∑ b : Block, if p ∈ S.support b then w b else 0 := by
  classical
  let F : Finset Block := Finset.univ.filter fun b => p ∈ S.support b
  calc
    (∑ b : BlockAt S p, w b.1) = ∑ b ∈ F, w b := by
      symm
      simpa [F] using
        (Finset.sum_subtype F
          (fun b => by simp [F]) w)
    _ = ∑ b : Block, if p ∈ S.support b then w b else 0 := by
      simp [F, Finset.sum_filter]

/-- Indicator form of a sum over nontrivial blocks through a point. -/
theorem sum_nontrivialBlockAt_weight_indicator
    (S : BlockSystem Point Block) (p : Point) (w : Block → ℤ) :
    (∑ b : NontrivialBlockAt S p, w b.1) =
      ∑ b : Block,
        if p ∈ S.support b ∧ 3 ≤ (S.support b).card then w b else 0 := by
  classical
  let F : Finset Block := Finset.univ.filter fun b =>
    p ∈ S.support b ∧ 3 ≤ (S.support b).card
  calc
    (∑ b : NontrivialBlockAt S p, w b.1) = ∑ b ∈ F, w b := by
      symm
      simpa [F] using
        (Finset.sum_subtype F
          (fun b => by simp [F]) w)
    _ = ∑ b : Block,
        if p ∈ S.support b ∧ 3 ≤ (S.support b).card then w b else 0 := by
      simp [F, Finset.sum_filter]

/-- Indicator form of a sum over nontrivial line blocks through a point. -/
theorem sum_nontrivialLineAt_weight_indicator
    (S : BlockSystem Point Block) (p : Point) (w : Block → ℤ) :
    (∑ b : NontrivialLineAt S p, w b.1) =
      ∑ b : Block,
        if p ∈ S.support b ∧ S.kind b = .line ∧
            3 ≤ (S.support b).card then w b else 0 := by
  classical
  let F : Finset Block := Finset.univ.filter fun b =>
    p ∈ S.support b ∧ S.kind b = .line ∧ 3 ≤ (S.support b).card
  calc
    (∑ b : NontrivialLineAt S p, w b.1) = ∑ b ∈ F, w b := by
      symm
      simpa [F] using
        (Finset.sum_subtype F
          (fun b => by simp [F]) w)
    _ = ∑ b : Block,
        if p ∈ S.support b ∧ S.kind b = .line ∧
            3 ≤ (S.support b).card then w b else 0 := by
      simp [F, Finset.sum_filter]

/-- The local signed pivot expression is exactly the sum of Melchior
coefficients over nontrivial blocks through the point, minus three. -/
theorem pivotSigma_eq_sum_nontrivialBlockAt_sub_three
    (S : BlockSystem Point Block) (p : Point) :
    S.pivotSigma p =
      (∑ b : NontrivialBlockAt S p,
        (4 - ((S.support b.1).card : ℤ))) - 3 := by
  unfold pivotSigma
  rw [S.sum_nontrivialBlockAt_weight p
    (fun s => 4 - (s : ℤ))]

/-- Cast of the fixed-size incidence row to `Int`. -/
theorem block_incidence_int (S : BlockSystem Point Block) (s : ℕ) :
    (∑ p : Point, (S.blockDegree s p : ℤ)) =
      (s : ℤ) * (S.blockCount s : ℤ) := by
  exact_mod_cast S.block_incidence s

theorem line_incidence_int (S : BlockSystem Point Block) (s : ℕ) :
    (∑ p : Point, (S.lineDegree s p : ℤ)) =
      (s : ℤ) * (S.lineCount s : ℤ) := by
  exact_mod_cast S.line_incidence s

theorem circle_incidence_int (S : BlockSystem Point Block) (s : ℕ) :
    (∑ p : Point, (S.circleDegree s p : ℤ)) =
      (s : ℤ) * (S.circleCount s : ℤ) := by
  exact_mod_cast S.circle_incidence s

/-- Summing the local pivot expressions gives the exact global `P` row. -/
theorem sum_pivotSigma_eq_pivotRow_sub_three_n
    (S : BlockSystem Point Block) :
    (∑ p : Point, S.pivotSigma p) =
      S.pivotRow - 3 * (Fintype.card Point : ℤ) := by
  classical
  simp only [pivotSigma, Finset.sum_sub_distrib]
  calc
    (∑ p : Point,
        ∑ s ∈ S.nontrivialSizes,
          (4 - (s : ℤ)) * (S.blockDegree s p : ℤ)) -
        ∑ _p : Point, (3 : ℤ) =
      (∑ s ∈ S.nontrivialSizes,
        ∑ p : Point,
          (4 - (s : ℤ)) * (S.blockDegree s p : ℤ)) -
        ∑ _p : Point, (3 : ℤ) := by
      rw [Finset.sum_comm]
    _ = (∑ s ∈ S.nontrivialSizes,
          (4 - (s : ℤ)) *
            ((s : ℤ) * (S.blockCount s : ℤ))) -
        3 * (Fintype.card Point : ℤ) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro s hs
        rw [← Finset.mul_sum, S.block_incidence_int s]
      · simp
        ring
    _ = S.pivotRow - 3 * (Fintype.card Point : ℤ) := by
      unfold pivotRow
      congr 1
      apply Finset.sum_congr rfl
      intro s hs
      ring

/-- The signed local restored-centre expression before its geometric
nonnegativity input. -/
def restoredKappa (S : BlockSystem Point Block) (p : Point) : ℤ :=
  ((Fintype.card Point : ℤ) - 1) + S.pivotSigma p -
    ∑ s ∈ S.nontrivialSizes,
      (s : ℤ) * (S.lineDegree s p : ℤ)

/-- The Melchior coefficient of a block after restoring the pivot centre.
Line blocks retain their support size; circle blocks lose the pivot label. -/
def restoredBlockWeight (S : BlockSystem Point Block) (b : Block) : ℤ :=
  match S.kind b with
  | .line => 3 - ((S.support b).card : ℤ)
  | .circle => 4 - ((S.support b).card : ℤ)

/-- The algebraic restored-centre expression is exactly the sum of the
restored Melchior coefficients over all blocks through the pivot, minus
three. -/
theorem restoredKappa_eq_sum_blockAt_weight_sub_three
    (S : BlockSystem Point Block) (p : Point) :
    S.restoredKappa p =
      (∑ b : BlockAt S p, S.restoredBlockWeight b.1) - 3 := by
  classical
  let Fline : Finset Block :=
    (S.blocksOfKind .line).filter fun b => p ∈ S.support b
  have hnpos : 1 ≤ Fintype.card Point :=
    Fintype.card_pos_iff.mpr ⟨p⟩
  have harmsCast :
      (∑ b ∈ Fline, (((S.support b).card - 1 : ℕ) : ℤ)) =
        (((Fintype.card Point - 1 : ℕ)) : ℤ) := by
    exact_mod_cast (S.line_arms_blocks p)
  have harms :
      ((Fintype.card Point : ℤ) - 1) =
        ∑ b : Block,
          if p ∈ S.support b ∧ S.kind b = .line then
            ((S.support b).card : ℤ) - 1 else 0 := by
    calc
      ((Fintype.card Point : ℤ) - 1) =
          (((Fintype.card Point - 1 : ℕ)) : ℤ) := by omega
      _ = ∑ b ∈ Fline, (((S.support b).card - 1 : ℕ) : ℤ) :=
        harmsCast.symm
      _ = ∑ b ∈ Fline, (((S.support b).card : ℤ) - 1) := by
        apply Finset.sum_congr rfl
        intro b hb
        have hkind : S.kind b = .line := by
          exact S.mem_blocksOfKind.mp (Finset.mem_filter.mp hb).1
        have hmin := S.line_min b hkind
        omega
      _ = ∑ b : Block,
          if p ∈ S.support b ∧ S.kind b = .line then
            ((S.support b).card : ℤ) - 1 else 0 := by
        have hFline : Fline = Finset.univ.filter fun b =>
            p ∈ S.support b ∧ S.kind b = .line := by
          ext b
          simp [Fline, blocksOfKind, and_comm]
        rw [hFline, Finset.sum_filter]
  have hsigma :
      S.pivotSigma p =
        (∑ b : Block,
          if p ∈ S.support b ∧ 3 ≤ (S.support b).card then
            4 - ((S.support b).card : ℤ) else 0) - 3 := by
    calc
      S.pivotSigma p =
          (∑ b : NontrivialBlockAt S p,
            (4 - ((S.support b.1).card : ℤ))) - 3 :=
        S.pivotSigma_eq_sum_nontrivialBlockAt_sub_three p
      _ = (∑ b : Block,
          if p ∈ S.support b ∧ 3 ≤ (S.support b).card then
            4 - ((S.support b).card : ℤ) else 0) - 3 := by
        rw [S.sum_nontrivialBlockAt_weight_indicator p
          (fun b => 4 - ((S.support b).card : ℤ))]
  have hline :
      (∑ s ∈ S.nontrivialSizes,
          (s : ℤ) * (S.lineDegree s p : ℤ)) =
        ∑ b : Block,
          if p ∈ S.support b ∧ S.kind b = .line ∧
              3 ≤ (S.support b).card then
            ((S.support b).card : ℤ) else 0 := by
    calc
      (∑ s ∈ S.nontrivialSizes,
          (s : ℤ) * (S.lineDegree s p : ℤ)) =
          ∑ b : NontrivialLineAt S p,
            ((S.support b.1).card : ℤ) :=
        S.sum_nontrivialLineAt_weight p (fun s => (s : ℤ))
      _ = ∑ b : Block,
          if p ∈ S.support b ∧ S.kind b = .line ∧
              3 ≤ (S.support b).card then
            ((S.support b).card : ℤ) else 0 :=
        S.sum_nontrivialLineAt_weight_indicator p
          (fun b => ((S.support b).card : ℤ))
  have hpoint (b : Block) :
      (if p ∈ S.support b ∧ S.kind b = .line then
          ((S.support b).card : ℤ) - 1 else 0) +
        (if p ∈ S.support b ∧ 3 ≤ (S.support b).card then
          4 - ((S.support b).card : ℤ) else 0) -
        (if p ∈ S.support b ∧ S.kind b = .line ∧
            3 ≤ (S.support b).card then
          ((S.support b).card : ℤ) else 0) =
        if p ∈ S.support b then S.restoredBlockWeight b else 0 := by
    by_cases hp : p ∈ S.support b
    · cases hkind : S.kind b with
      | line =>
          have hmin := S.line_min b hkind
          by_cases hthree : 3 ≤ (S.support b).card
          · simp [hp, hkind, hthree, restoredBlockWeight]
          · simp [hp, hkind, hthree, restoredBlockWeight]
            omega
      | circle =>
          have hmin := S.circle_min b hkind
          simp [hp, hkind, hmin, restoredBlockWeight]
    · simp [hp]
  have hcombine :
      (∑ b : Block,
          if p ∈ S.support b ∧ S.kind b = .line then
            ((S.support b).card : ℤ) - 1 else 0) +
        (∑ b : Block,
          if p ∈ S.support b ∧ 3 ≤ (S.support b).card then
            4 - ((S.support b).card : ℤ) else 0) -
        (∑ b : Block,
          if p ∈ S.support b ∧ S.kind b = .line ∧
              3 ≤ (S.support b).card then
            ((S.support b).card : ℤ) else 0) =
        ∑ b : Block,
          if p ∈ S.support b then S.restoredBlockWeight b else 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _hb
    exact hpoint b
  have hblocks := S.sum_blockAt_weight p S.restoredBlockWeight
  unfold restoredKappa
  rw [harms, hsigma, hline]
  calc
    (∑ b : Block,
          if p ∈ S.support b ∧ S.kind b = .line then
            ((S.support b).card : ℤ) - 1 else 0) +
        ((∑ b : Block,
          if p ∈ S.support b ∧ 3 ≤ (S.support b).card then
            4 - ((S.support b).card : ℤ) else 0) - 3) -
        (∑ b : Block,
          if p ∈ S.support b ∧ S.kind b = .line ∧
              3 ≤ (S.support b).card then
            ((S.support b).card : ℤ) else 0) =
        ((∑ b : Block,
          if p ∈ S.support b then S.restoredBlockWeight b else 0) - 3) := by
      rw [← hcombine]
      ring
    _ = (∑ b : BlockAt S p, S.restoredBlockWeight b.1) - 3 := by
      rw [hblocks]

/-- The global signed row `D`. -/
def defectRow (S : BlockSystem Point Block) : ℤ :=
  (∑ s ∈ S.nontrivialSizes,
      (s : ℤ) * ((s : ℤ) - 4) * (S.circleCount s : ℤ)) +
    ∑ s ∈ S.nontrivialSizes,
      2 * (s : ℤ) * ((s : ℤ) - 2) * (S.lineCount s : ℤ)

theorem sum_line_size_degree (S : BlockSystem Point Block) :
    (∑ p : Point, ∑ s ∈ S.nontrivialSizes,
        (s : ℤ) * (S.lineDegree s p : ℤ)) =
      ∑ s ∈ S.nontrivialSizes,
        (s : ℤ) * (s : ℤ) * (S.lineCount s : ℤ) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [← Finset.mul_sum, S.line_incidence_int s]
  ring

/-- Exact algebraic conversion from the `P` row and line second moment to
the global defect row `D`. -/
theorem pivotRow_sub_line_square_eq_neg_defectRow
    (S : BlockSystem Point Block) :
    S.pivotRow -
        (∑ s ∈ S.nontrivialSizes,
          (s : ℤ) * (s : ℤ) * (S.lineCount s : ℤ)) =
      -S.defectRow := by
  classical
  have hsplit (s : ℕ) :
      (S.blockCount s : ℤ) =
        (S.lineCount s : ℤ) + (S.circleCount s : ℤ) := by
    exact_mod_cast S.blockCount_eq_lineCount_add_circleCount s
  unfold pivotRow defectRow
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ s ∈ S.nontrivialSizes,
        ((s : ℤ) * (4 - (s : ℤ)) * (S.blockCount s : ℤ) -
          (s : ℤ) * (s : ℤ) * (S.lineCount s : ℤ))) =
      ∑ s ∈ S.nontrivialSizes,
        -((s : ℤ) * ((s : ℤ) - 4) * (S.circleCount s : ℤ) +
          2 * (s : ℤ) * ((s : ℤ) - 2) * (S.lineCount s : ℤ)) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [hsplit s]
      ring
    _ = -((∑ s ∈ S.nontrivialSizes,
          (s : ℤ) * ((s : ℤ) - 4) * (S.circleCount s : ℤ)) +
        ∑ s ∈ S.nontrivialSizes,
          2 * (s : ℤ) * ((s : ℤ) - 2) * (S.lineCount s : ℤ)) := by
      rw [Finset.sum_neg_distrib, Finset.sum_add_distrib]

/-- Summing the restored-centre expressions gives the exact global `D`
identity.  Geometric inversion/Melchior is needed only later to prove each
local expression nonnegative. -/
theorem sum_restoredKappa_eq_n_mul_n_sub_four_sub_defectRow
    (S : BlockSystem Point Block) :
    (∑ p : Point, S.restoredKappa p) =
      (Fintype.card Point : ℤ) * ((Fintype.card Point : ℤ) - 4) -
        S.defectRow := by
  classical
  have hexpand :
      (∑ p : Point, S.restoredKappa p) =
        (Fintype.card Point : ℤ) * ((Fintype.card Point : ℤ) - 1) +
          (∑ p : Point, S.pivotSigma p) -
          ∑ p : Point, ∑ s ∈ S.nontrivialSizes,
            (s : ℤ) * (S.lineDegree s p : ℤ) := by
    unfold restoredKappa
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    congr 2
    simp
    ring
  rw [hexpand, S.sum_pivotSigma_eq_pivotRow_sub_three_n,
    S.sum_line_size_degree]
  have hdef := S.pivotRow_sub_line_square_eq_neg_defectRow
  calc
    (Fintype.card Point : ℤ) * ((Fintype.card Point : ℤ) - 1) +
          (S.pivotRow - 3 * (Fintype.card Point : ℤ)) -
          ∑ s ∈ S.nontrivialSizes,
            (s : ℤ) * (s : ℤ) * (S.lineCount s : ℤ) =
        (Fintype.card Point : ℤ) * ((Fintype.card Point : ℤ) - 4) +
          (S.pivotRow -
            ∑ s ∈ S.nontrivialSizes,
              (s : ℤ) * (s : ℤ) * (S.lineCount s : ℤ)) := by ring
    _ = (Fintype.card Point : ℤ) * ((Fintype.card Point : ℤ) - 4) -
        S.defectRow := by rw [hdef]; ring

/-- The global row `L` used by the conditional Langer input. -/
def langerRow (S : BlockSystem Point Block) : ℤ :=
  ∑ s ∈ S.nontrivialSizes,
    (s : ℤ) * ((s : ℤ) - 1) * (S.blockCount s : ℤ)

theorem langerRow_eq_sum_local_weighted_degree
    (S : BlockSystem Point Block) :
    S.langerRow =
      ∑ p : Point, ∑ s ∈ S.nontrivialSizes,
        ((s : ℤ) - 1) * (S.blockDegree s p : ℤ) := by
  classical
  unfold langerRow
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [← Finset.mul_sum, S.block_incidence_int s]
  ring

/-- Melchior slack of the line-tagged part of a block system, written
directly over its line blocks. -/
def globalLineSlack (S : BlockSystem Point Block) : ℤ :=
  (∑ b : LineBlock S,
    (3 - ((S.support b.1).card : ℤ))) - 3

/-- The direct global line row in block form.  Two-point lines contribute
zero; every line of size at least three has coefficient
`choose(s,2) + s - 3`. -/
def globalLineRow (S : BlockSystem Point Block) : ℤ :=
  ∑ b : LineBlock S,
    if 3 ≤ (S.support b.1).card then
      (Nat.choose (S.support b.1).card 2 : ℤ) +
        ((S.support b.1).card : ℤ) - 3
    else 0

/-- Exact conversion of the line-pair partition into the manuscript's
direct global line row.  Melchior is used only later to give the slack a
sign. -/
theorem choose_two_sub_three_sub_globalLineRow_eq_globalLineSlack
    (S : BlockSystem Point Block) :
    (Nat.choose (Fintype.card Point) 2 : ℤ) - 3 - S.globalLineRow =
      S.globalLineSlack := by
  classical
  have hpair :
      (∑ b : LineBlock S,
        (Nat.choose (S.support b.1).card 2 : ℤ)) =
        (Nat.choose (Fintype.card Point) 2 : ℤ) := by
    exact_mod_cast S.line_pair_partition
  have hpoint (b : LineBlock S) :
      (Nat.choose (S.support b.1).card 2 : ℤ) -
          (if 3 ≤ (S.support b.1).card then
            (Nat.choose (S.support b.1).card 2 : ℤ) +
              ((S.support b.1).card : ℤ) - 3
          else 0) =
        3 - ((S.support b.1).card : ℤ) := by
    by_cases hthree : 3 ≤ (S.support b.1).card
    · simp [hthree]
      ring
    · have hmin := S.line_min b.1 b.2
      have hcard : (S.support b.1).card = 2 := by omega
      simp [hcard]
  unfold globalLineRow globalLineSlack
  rw [← hpair]
  calc
    (∑ b : LineBlock S,
          (Nat.choose (S.support b.1).card 2 : ℤ)) - 3 -
        (∑ b : LineBlock S,
          if 3 ≤ (S.support b.1).card then
            (Nat.choose (S.support b.1).card 2 : ℤ) +
              ((S.support b.1).card : ℤ) - 3
          else 0) =
        (∑ b : LineBlock S,
          ((Nat.choose (S.support b.1).card 2 : ℤ) -
            (if 3 ≤ (S.support b.1).card then
              (Nat.choose (S.support b.1).card 2 : ℤ) +
                ((S.support b.1).card : ℤ) - 3
            else 0))) - 3 := by
      rw [Finset.sum_sub_distrib]
      ring
    _ = (∑ b : LineBlock S,
        (3 - ((S.support b.1).card : ℤ))) - 3 := by
      congr 1
      apply Fintype.sum_congr
      exact hpoint

end BlockSystem
end Erdos506.Block
