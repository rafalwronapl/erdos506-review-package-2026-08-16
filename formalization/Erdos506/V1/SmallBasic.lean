import Erdos506.V1.RichBlockPencil
import Erdos506.V4.Main

/-!
# The first two small V1 cases

For four labels, V1 admissibility already rules out a four-point circle, so
the public V4 lower bound applies directly.  For five labels, either V4 still
applies or a four-point circle supplies a rich circle block; its pencil gives
the required five determined circles.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.V4

theorem circleCount_ge_target_of_card_four
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hα : Fintype.card α = 4) :
    Erdos506.v1Target (Fintype.card α) ≤
      Erdos506.V4.circleCount cfg := by
  have hfour : NoFourConcyclic cfg := by
    intro c
    have hc := hadm.2 c
    rw [hα] at hc
    omega
  have hv4 := Erdos506.V4.circleCount_ge_target cfg (by omega)
    (show Erdos506.V4.Admissible cfg from ⟨hadm.1, hfour⟩)
  rw [hα] at hv4 ⊢
  norm_num [Erdos506.v1Target, Erdos506.v4Target, Nat.choose] at hv4 ⊢
  exact hv4

theorem circleCount_ge_target_of_card_five
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hα : Fintype.card α = 5) :
    Erdos506.v1Target (Fintype.card α) ≤
      Erdos506.V4.circleCount cfg := by
  classical
  by_cases hfour : NoFourConcyclic cfg
  · have hv4 := Erdos506.V4.circleCount_ge_target cfg (by omega)
      (show Erdos506.V4.Admissible cfg from ⟨hadm.1, hfour⟩)
    rw [hα] at hv4 ⊢
    norm_num [Erdos506.v1Target, Erdos506.v1UniformTarget,
      Erdos506.v4Target, Nat.choose] at hv4 ⊢
    omega
  · have hfour' : ∃ c : ProperCircle,
        ¬(circleTrace cfg c).card ≤ 3 := by
      simpa only [NoFourConcyclic, not_forall] using hfour
    obtain ⟨c, hcnot⟩ := hfour'
    have hcgt : 4 ≤ (circleTrace cfg c).card := by omega
    have hclt : (circleTrace cfg c).card < Fintype.card α := hadm.2 c
    have hccard : (circleTrace cfg c).card = 4 := by omega
    have hthree : 3 ≤ (circleTrace cfg c).card := by omega
    obtain ⟨t, htsub, htcard⟩ := Finset.exists_subset_card_eq hthree
    let A : Erdos506.Finite.KSubset α 3 := ⟨t, htcard⟩
    have htNoncollinear : IsNoncollinear cfg t := by
      by_contra htcol
      exact not_triple_subset_circle_of_collinear cfg A htcol c htsub
    let nt : NoncollinearTriple cfg :=
      ⟨t, mem_noncollinearTriples.mpr ⟨htcard, htNoncollinear⟩⟩
    have hcDetermined : c ∈ determinedCircles cfg := by
      rw [mem_determinedCircles_iff]
      refine ⟨nt, ?_⟩
      intro x hx
      exact mem_circleTrace.mp (htsub hx)
    let g : DeterminedCircle cfg := ⟨c, hcDetermined⟩
    let b : GeometricBlock cfg := Sum.inr g
    have hbcard : (geometricBlockSupport cfg b).card = 4 := by
      simpa [b, g] using hccard
    have hbproper : ((blockSystem cfg).support b).card < Fintype.card α := by
      change (geometricBlockSupport cfg b).card < Fintype.card α
      simpa [b, g] using hclt
    have hbsize : 3 ≤ ((blockSystem cfg).support b).card := by
      change 3 ≤ (geometricBlockSupport cfg b).card
      omega
    have hpencil := richBlockPencilBound_le_totalCircleCount
      (blockSystem cfg) b hbproper hbsize
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hpencil
    change richBlockPencilBound (Fintype.card α)
      (geometricBlockSupport cfg b).card ≤
        Erdos506.V4.circleCount cfg at hpencil
    rw [hα, hbcard] at hpencil
    rw [hα] at ⊢
    norm_num [richBlockPencilBound, Erdos506.v1Target, Nat.choose] at hpencil ⊢
    exact hpencil

end Erdos506.V1
