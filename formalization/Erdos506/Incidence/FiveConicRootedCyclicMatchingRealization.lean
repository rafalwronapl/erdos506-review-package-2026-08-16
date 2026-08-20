import Erdos506.Incidence.FiveConicRootedCyclicDiagonalRealization
import Erdos506.Incidence.FiveConicRootedCyclicMatching

/-!
# Realizing a finite rooted matching as its normal diagonal point

The finite matching code of a saturated two-host fibre is a row of
`kFiveRowOptions 4`.  Here that row is connected to the literal projective
intersection of its two selected chords.  This is the small bridge consumed
by the actual one-single page law.
-/

namespace Erdos506.Incidence

open Erdos506.Finite
open Erdos506.V3
open Erdos506.V4
open scoped LinearAlgebra.Projectivization

universe u

/-- The projective line of a finite chord after applying the rooted trace
labelling. -/
noncomputable def fiveConicRootedCyclicProjectiveChord
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) (r : Fin 5)
    (e : FinFiveChord) : RealProjectiveLine :=
  projectiveChordLine cfg
    (circleChordPair
      (kFiveChordEquivOfVertexLabel
        (fiveConicRootedCyclicLabel cfg Gamma hGamma r) e))

/-- A rooted finite chord can be written using its displayed two rooted
labels. -/
theorem fiveConicRootedCyclicProjectiveChord_eq_projectiveLine
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5)
    (r i j : Fin 5) (hij : i ≠ j) :
    fiveConicRootedCyclicProjectiveChord cfg Gamma hGamma r
      ⟨{i, j}, by simp [hij]⟩ =
        projectiveLine
          (cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r i).1)
          (cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r j).1)
          (cfg.injective.ne
            (fiveConicRootedCyclicLabel_ne cfg Gamma hGamma r i j hij)) := by
  unfold fiveConicRootedCyclicProjectiveChord
  apply projectiveChordLine_eq_projectiveLine_of_mem cfg
  · exact (mem_kFiveChordEquivOfVertexLabel
      (fiveConicRootedCyclicLabel cfg Gamma hGamma r)
      ⟨{i, j}, by simp [hij]⟩ i).mpr (by simp)
  · exact (mem_kFiveChordEquivOfVertexLabel
      (fiveConicRootedCyclicLabel cfg Gamma hGamma r)
      ⟨{i, j}, by simp [hij]⟩ j).mpr (by simp)
  · exact fiveConicRootedCyclicLabel_ne cfg Gamma hGamma r i j hij

private theorem pair_eq_of_mem_two_chord_row
    (e f a b : FinFiveChord) (hab : a ≠ b)
    (hrow : ({e, f} : Finset FinFiveChord) = {a, b}) :
    (e = a ∧ f = b) ∨ (e = b ∧ f = a) := by
  have hcard : ({e, f} : Finset FinFiveChord).card = 2 := by
    rw [hrow]
    simp [hab]
  have hef : e ≠ f := by
    intro heq
    subst f
    simp at hcard
  have he : e = a ∨ e = b := by
    have : e ∈ ({a, b} : Finset FinFiveChord) := by
      rw [← hrow]
      simp
    simpa using this
  have hf : f = a ∨ f = b := by
    have : f ∈ ({a, b} : Finset FinFiveChord) := by
      rw [← hrow]
      simp
    simpa using this
  rcases he with hea | heb <;> rcases hf with hfa | hfb
  · exact False.elim (hef (hea.trans hfa.symm))
  · exact Or.inl ⟨hea, hfb⟩
  · exact Or.inr ⟨heb, hfa⟩
  · exact False.elim (hef (heb.trans hfb.symm))

/-- A two-chord rooted matching row realizes the corresponding transported
normal diagonal.  The returned frame is constructed from the actual cyclic
five-trace, so callers do not choose a projective chart. -/
theorem exists_fiveConicRootedCyclic_normalDiagonal_eq_cross_chords_of_row
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) (r : Fin 5)
    (i : Fin 3) (e f : FinFiveChord)
    (hrow : ({e, f} : Finset FinFiveChord) = kFiveRowOptions 4 i) :
    ∃ (g : GL (Fin 2) ℝ) (lam t : ℝ) (hlam : 1 < lam), lam < t ∧
      fiveConicTransportedNormalDiagonal Gamma.1 g⁻¹ lam hlam i =
        Projectivization.cross
          (fiveConicRootedCyclicProjectiveChord cfg Gamma hGamma r e)
          (fiveConicRootedCyclicProjectiveChord cfg Gamma hGamma r f) := by
  obtain ⟨g, lam, t, hlam, hlt, _hmark, hdiag0, hdiag1, hdiag2⟩ :=
    exists_fiveConicTraceRootedCyclic_diagonal_realization
      cfg Gamma hGamma r
  have h01 : (kFiveChord01 : FinFiveChord) ≠ kFiveChord23 := by decide
  have h02 : (kFiveChord02 : FinFiveChord) ≠ kFiveChord13 := by decide
  have h03 : (kFiveChord03 : FinFiveChord) ≠ kFiveChord12 := by decide
  refine ⟨g, lam, t, hlam, hlt, ?_⟩
  fin_cases i
  · have hpair : ({e, f} : Finset FinFiveChord) =
        {kFiveChord01, kFiveChord23} := by
      simpa [kFiveRowOptions] using hrow
    rcases pair_eq_of_mem_two_chord_row e f kFiveChord01 kFiveChord23 h01
        hpair with h | h
    · rcases h with ⟨rfl, rfl⟩
      simp only [kFiveChord01, kFiveChord23,
        fiveConicRootedCyclicProjectiveChord_eq_projectiveLine
        cfg Gamma hGamma r 0 1 (by decide),
        fiveConicRootedCyclicProjectiveChord_eq_projectiveLine
          cfg Gamma hGamma r 2 3 (by decide)]
      exact hdiag0
    · rcases h with ⟨rfl, rfl⟩
      simp only [kFiveChord23, kFiveChord01,
        fiveConicRootedCyclicProjectiveChord_eq_projectiveLine
        cfg Gamma hGamma r 2 3 (by decide),
        fiveConicRootedCyclicProjectiveChord_eq_projectiveLine
          cfg Gamma hGamma r 0 1 (by decide)]
      rw [Projectivization.cross_comm]
      exact hdiag0
  · have hpair : ({e, f} : Finset FinFiveChord) =
        {kFiveChord02, kFiveChord13} := by
      simpa [kFiveRowOptions] using hrow
    rcases pair_eq_of_mem_two_chord_row e f kFiveChord02 kFiveChord13 h02
        hpair with h | h
    · rcases h with ⟨rfl, rfl⟩
      simp only [kFiveChord02, kFiveChord13,
        fiveConicRootedCyclicProjectiveChord_eq_projectiveLine
        cfg Gamma hGamma r 0 2 (by decide),
        fiveConicRootedCyclicProjectiveChord_eq_projectiveLine
          cfg Gamma hGamma r 1 3 (by decide)]
      exact hdiag1
    · rcases h with ⟨rfl, rfl⟩
      simp only [kFiveChord13, kFiveChord02,
        fiveConicRootedCyclicProjectiveChord_eq_projectiveLine
        cfg Gamma hGamma r 1 3 (by decide),
        fiveConicRootedCyclicProjectiveChord_eq_projectiveLine
          cfg Gamma hGamma r 0 2 (by decide)]
      rw [Projectivization.cross_comm]
      exact hdiag1
  · have hpair : ({e, f} : Finset FinFiveChord) =
        {kFiveChord03, kFiveChord12} := by
      simpa [kFiveRowOptions] using hrow
    rcases pair_eq_of_mem_two_chord_row e f kFiveChord03 kFiveChord12 h03
        hpair with h | h
    · rcases h with ⟨rfl, rfl⟩
      simp only [kFiveChord03, kFiveChord12,
        fiveConicRootedCyclicProjectiveChord_eq_projectiveLine
        cfg Gamma hGamma r 0 3 (by decide),
        fiveConicRootedCyclicProjectiveChord_eq_projectiveLine
          cfg Gamma hGamma r 1 2 (by decide)]
      exact hdiag2
    · rcases h with ⟨rfl, rfl⟩
      simp only [kFiveChord12, kFiveChord03,
        fiveConicRootedCyclicProjectiveChord_eq_projectiveLine
        cfg Gamma hGamma r 1 2 (by decide),
        fiveConicRootedCyclicProjectiveChord_eq_projectiveLine
          cfg Gamma hGamma r 0 3 (by decide)]
      rw [Projectivization.cross_comm]
      exact hdiag2

/-- One constructed rooted frame realizes every one of the three finite
matching rows simultaneously.  This shared-frame form is the one used when
the two double fibres of a one-single page are fed to the normal separator.
-/
theorem exists_fiveConicRootedCyclic_normalDiagonal_cross_chords_all_rows
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) (r : Fin 5) :
    ∃ (g : GL (Fin 2) ℝ) (lam t : ℝ) (hlam : 1 < lam), lam < t ∧
      fiveConicTransportedNormalPoint Gamma.1 g⁻¹ t =
        projectivePoint
          (cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 4).1) ∧
      ∀ (i : Fin 3) (e f : FinFiveChord),
        ({e, f} : Finset FinFiveChord) = kFiveRowOptions 4 i →
          fiveConicTransportedNormalDiagonal Gamma.1 g⁻¹ lam hlam i =
            Projectivization.cross
              (fiveConicRootedCyclicProjectiveChord cfg Gamma hGamma r e)
              (fiveConicRootedCyclicProjectiveChord cfg Gamma hGamma r f) := by
  obtain ⟨g, lam, t, hlam, hlt, _hmark, hdiag0, hdiag1, hdiag2⟩ :=
    exists_fiveConicTraceRootedCyclic_diagonal_realization
      cfg Gamma hGamma r
  have h01 : (kFiveChord01 : FinFiveChord) ≠ kFiveChord23 := by decide
  have h02 : (kFiveChord02 : FinFiveChord) ≠ kFiveChord13 := by decide
  have h03 : (kFiveChord03 : FinFiveChord) ≠ kFiveChord12 := by decide
  refine ⟨g, lam, t, hlam, hlt, _hmark, ?_⟩
  intro i e f hrow
  fin_cases i
  · have hpair : ({e, f} : Finset FinFiveChord) =
        {kFiveChord01, kFiveChord23} := by
      simpa [kFiveRowOptions] using hrow
    rcases pair_eq_of_mem_two_chord_row e f kFiveChord01 kFiveChord23 h01
        hpair with h | h
    · rcases h with ⟨rfl, rfl⟩
      simp only [kFiveChord01, kFiveChord23,
        fiveConicRootedCyclicProjectiveChord_eq_projectiveLine
        cfg Gamma hGamma r 0 1 (by decide),
        fiveConicRootedCyclicProjectiveChord_eq_projectiveLine
          cfg Gamma hGamma r 2 3 (by decide)]
      exact hdiag0
    · rcases h with ⟨rfl, rfl⟩
      simp only [kFiveChord23, kFiveChord01,
        fiveConicRootedCyclicProjectiveChord_eq_projectiveLine
        cfg Gamma hGamma r 2 3 (by decide),
        fiveConicRootedCyclicProjectiveChord_eq_projectiveLine
          cfg Gamma hGamma r 0 1 (by decide)]
      rw [Projectivization.cross_comm]
      exact hdiag0
  · have hpair : ({e, f} : Finset FinFiveChord) =
        {kFiveChord02, kFiveChord13} := by
      simpa [kFiveRowOptions] using hrow
    rcases pair_eq_of_mem_two_chord_row e f kFiveChord02 kFiveChord13 h02
        hpair with h | h
    · rcases h with ⟨rfl, rfl⟩
      simp only [kFiveChord02, kFiveChord13,
        fiveConicRootedCyclicProjectiveChord_eq_projectiveLine
        cfg Gamma hGamma r 0 2 (by decide),
        fiveConicRootedCyclicProjectiveChord_eq_projectiveLine
          cfg Gamma hGamma r 1 3 (by decide)]
      exact hdiag1
    · rcases h with ⟨rfl, rfl⟩
      simp only [kFiveChord13, kFiveChord02,
        fiveConicRootedCyclicProjectiveChord_eq_projectiveLine
        cfg Gamma hGamma r 1 3 (by decide),
        fiveConicRootedCyclicProjectiveChord_eq_projectiveLine
          cfg Gamma hGamma r 0 2 (by decide)]
      rw [Projectivization.cross_comm]
      exact hdiag1
  · have hpair : ({e, f} : Finset FinFiveChord) =
        {kFiveChord03, kFiveChord12} := by
      simpa [kFiveRowOptions] using hrow
    rcases pair_eq_of_mem_two_chord_row e f kFiveChord03 kFiveChord12 h03
        hpair with h | h
    · rcases h with ⟨rfl, rfl⟩
      simp only [kFiveChord03, kFiveChord12,
        fiveConicRootedCyclicProjectiveChord_eq_projectiveLine
        cfg Gamma hGamma r 0 3 (by decide),
        fiveConicRootedCyclicProjectiveChord_eq_projectiveLine
          cfg Gamma hGamma r 1 2 (by decide)]
      exact hdiag2
    · rcases h with ⟨rfl, rfl⟩
      simp only [kFiveChord12, kFiveChord03,
        fiveConicRootedCyclicProjectiveChord_eq_projectiveLine
        cfg Gamma hGamma r 1 2 (by decide),
        fiveConicRootedCyclicProjectiveChord_eq_projectiveLine
          cfg Gamma hGamma r 0 3 (by decide)]
      rw [Projectivization.cross_comm]
      exact hdiag2

/-- Two distinct rooted matching rows whose chord-intersection points lie on
one actual page trace are necessarily the first and second normal rows. -/
theorem fiveConicRootedCyclic_two_double_row_indices_eq_zero_one
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) (r : Fin 5)
    (ell : RealProjectivePlane)
    (hmark : Projectivization.orthogonal
      (projectivePoint
        (cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 4).1)) ell)
    (i j : Fin 3) (hij : i ≠ j)
    (ei fi ej fj : FinFiveChord)
    (hirow : ({ei, fi} : Finset FinFiveChord) = kFiveRowOptions 4 i)
    (hjrow : ({ej, fj} : Finset FinFiveChord) = kFiveRowOptions 4 j)
    (hi : Projectivization.orthogonal
      (Projectivization.cross
        (fiveConicRootedCyclicProjectiveChord cfg Gamma hGamma r ei)
        (fiveConicRootedCyclicProjectiveChord cfg Gamma hGamma r fi)) ell)
    (hj : Projectivization.orthogonal
      (Projectivization.cross
        (fiveConicRootedCyclicProjectiveChord cfg Gamma hGamma r ej)
        (fiveConicRootedCyclicProjectiveChord cfg Gamma hGamma r fj)) ell) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
  obtain ⟨g, lam, t, hlam, hlt, hmarkEq, hrows⟩ :=
    exists_fiveConicRootedCyclic_normalDiagonal_cross_chords_all_rows
      cfg Gamma hGamma r
  apply fiveConicTransportedNormal_collinear_diagonal_pair_eq_zero_one
    Gamma.1 g⁻¹ hlam hlt i j hij ell
  · rw [hmarkEq]
    exact hmark
  · rw [hrows i ei fi hirow]
    exact hi
  · rw [hrows j ej fj hjrow]
    exact hj

end Erdos506.Incidence
