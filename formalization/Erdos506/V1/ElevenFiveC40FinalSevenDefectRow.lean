import Erdos506.V1.ElevenFiveC40FinalSevenDefectProfile

/-!
# The terminal row defect of the C40 seven-five face

Once the `4^3 3^7 2` profile has produced its unique disjoint pair, the
two support rows force the two endpoints to contain too few four-degree
points.  This is a purely finite contradiction; the configuration wrapper
only supplies the already-established exclusion of singleton intersections.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u

/-- The `4^3 3^7 2` seven-block profile is incompatible with the absence of
singleton intersections.  Its moment-`40` disjoint pair is unique, each
endpoint has row mass `15`, and those two row equalities contradict the
three high-degree points. -/
theorem fiveBlock_four_three_two_profile_impossible_of_no_singleton
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hfive : S.blockCount 5 = 7)
    (hfour : ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 5 p = 4).card = 3)
    (htwo : ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 5 p = 2).card = 1)
    (hprofile : ∀ p : Point, S.blockDegree 5 p = 2 ∨
      S.blockDegree 5 p = 3 ∨ S.blockDegree 5 p = 4)
    (hnosingleton : ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card ≠ 1) : False := by
  classical
  let H := (Finset.univ : Finset Point).filter
    fun p => S.blockDegree 5 p = 4
  let U := (Finset.univ : Finset Point).filter
    fun p => S.blockDegree 5 p = 2
  have hHcard : H.card = 3 := by simpa [H] using hfour
  have hUcard : U.card = 1 := by simpa [U] using htwo
  have hmoment := fiveBlock_secondMoment_eq_forty_of_four_three_two_profile
    S hcard hfour htwo hprofile
  obtain ⟨f, hf, g, hg, hfg, hdisjoint⟩ :=
    fiveBlock_exists_disjoint_pair_of_secondMoment_eq_forty
      S hfive hmoment hnosingleton
  obtain ⟨hrowF, hrowG⟩ :=
    fiveBlock_support_degree_sum_eq_fifteen_of_secondMoment_forty_of_disjoint_pair
      S hfive hmoment hf hg hfg hdisjoint
  have hpoint (p : Point) : S.blockDegree 5 p +
      (if p ∈ U then 1 else 0) =
        3 + (if p ∈ H then 1 else 0) := by
    rcases hprofile p with htwo' | hthree | hfour'
    · norm_num [H, U, htwo']
    · norm_num [H, U, hthree]
    · norm_num [H, U, hfour']
  have hindicator (D T : Finset Point) :
      (∑ p ∈ D, if p ∈ T then 1 else 0) = (D ∩ T).card := by
    rw [← Finset.sum_filter]
    have hfilter : D.filter (fun p => p ∈ T) = D ∩ T := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_inter]
    rw [hfilter]
    simp
  have hsupportBalance (b : Block) (hb : b ∈ S.blocksOfSize 5) :
      (∑ p ∈ S.support b, S.blockDegree 5 p) +
          (S.support b ∩ U).card =
        15 + (S.support b ∩ H).card := by
    calc
      (∑ p ∈ S.support b, S.blockDegree 5 p) +
          (S.support b ∩ U).card =
          (∑ p ∈ S.support b, S.blockDegree 5 p) +
            ∑ p ∈ S.support b, if p ∈ U then 1 else 0 := by
              rw [hindicator]
      _ = ∑ p ∈ S.support b,
          (S.blockDegree 5 p + (if p ∈ U then 1 else 0)) :=
            Finset.sum_add_distrib.symm
      _ = ∑ p ∈ S.support b,
          (3 + (if p ∈ H then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro p _hp
            exact hpoint p
      _ = (∑ _p ∈ S.support b, 3) +
          ∑ p ∈ S.support b, if p ∈ H then 1 else 0 := by
            rw [Finset.sum_add_distrib]
      _ = 15 + (S.support b ∩ H).card := by
            rw [hindicator]
            simp [S.mem_blocksOfSize.mp hb]
  have hFbalance : (S.support f ∩ U).card =
      (S.support f ∩ H).card := by
    have hbalance := hsupportBalance f hf
    rw [hrowF] at hbalance
    omega
  have hGbalance : (S.support g ∩ U).card =
      (S.support g ∩ H).card := by
    have hbalance := hsupportBalance g hg
    rw [hrowG] at hbalance
    omega
  have hFGdisjoint : Disjoint (S.support f) (S.support g) := by
    rw [Finset.disjoint_left]
    intro p hpf hpg
    have hp : p ∈ S.support f ∩ S.support g :=
      Finset.mem_inter.mpr ⟨hpf, hpg⟩
    have hempty : S.support f ∩ S.support g = ∅ :=
      Finset.card_eq_zero.mp hdisjoint
    simpa [hempty] using hp
  have hUdisjoint : Disjoint (S.support f ∩ U) (S.support g ∩ U) := by
    rw [Finset.disjoint_left]
    intro p hpf hpg
    exact Finset.disjoint_left.mp hFGdisjoint
      (Finset.mem_inter.mp hpf).1 (Finset.mem_inter.mp hpg).1
  have hUsub : (S.support f ∩ U) ∪ (S.support g ∩ U) ⊆ U := by
    intro p hp
    rcases Finset.mem_union.mp hp with hpf | hpg
    · exact (Finset.mem_inter.mp hpf).2
    · exact (Finset.mem_inter.mp hpg).2
  have hUsum : (S.support f ∩ U).card +
      (S.support g ∩ U).card ≤ 1 := by
    have hle := Finset.card_le_card hUsub
    rw [Finset.card_union_of_disjoint hUdisjoint, hUcard] at hle
    exact hle
  have hHsum : (S.support f ∩ H).card +
      (S.support g ∩ H).card ≤ 1 := by
    rw [← hFbalance, ← hGbalance]
    exact hUsum
  let V := S.support f ∪ S.support g
  have hVcard : V.card = 10 := by
    dsimp [V]
    rw [Finset.card_union_of_disjoint hFGdisjoint,
      S.mem_blocksOfSize.mp hf, S.mem_blocksOfSize.mp hg]
  have hcomplCard : ((Finset.univ : Finset Point) \ V).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ V),
      Finset.card_univ, hcard, hVcard]
  have hHoutsideSub : H \ V ⊆ (Finset.univ : Finset Point) \ V := by
    intro p hp
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ p,
      (Finset.mem_sdiff.mp hp).2⟩
  have hHoutside : (H \ V).card ≤ 1 := by
    have hle := Finset.card_le_card hHoutsideSub
    rwa [hcomplCard] at hle
  have hHsplit := Finset.card_inter_add_card_sdiff H V
  have hHinside : 2 ≤ (H ∩ V).card := by
    rw [hHcard] at hHsplit
    omega
  have hHdisjoint : Disjoint (S.support f ∩ H) (S.support g ∩ H) := by
    rw [Finset.disjoint_left]
    intro p hpf hpg
    exact Finset.disjoint_left.mp hFGdisjoint
      (Finset.mem_inter.mp hpf).1 (Finset.mem_inter.mp hpg).1
  have hHunion : H ∩ V =
      (S.support f ∩ H) ∪ (S.support g ∩ H) := by
    dsimp [V]
    ext p
    constructor
    · intro hp
      rcases Finset.mem_inter.mp hp with ⟨hpH, hpFG⟩
      rcases Finset.mem_union.mp hpFG with hpf | hpg
      · exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_inter.mpr ⟨hpf, hpH⟩))
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_inter.mpr ⟨hpg, hpH⟩))
    · intro hp
      rcases Finset.mem_union.mp hp with hpf | hpg
      · rcases Finset.mem_inter.mp hpf with ⟨hpf, hpH⟩
        exact Finset.mem_inter.mpr ⟨hpH,
          Finset.mem_union.mpr (Or.inl hpf)⟩
      · rcases Finset.mem_inter.mp hpg with ⟨hpg, hpH⟩
        exact Finset.mem_inter.mpr ⟨hpH,
          Finset.mem_union.mpr (Or.inr hpg)⟩
  have hHinsideEq : (H ∩ V).card =
      (S.support f ∩ H).card + (S.support g ∩ H).card := by
    rw [hHunion, Finset.card_union_of_disjoint hHdisjoint]
  rw [hHinsideEq] at hHinside
  omega

/-- In the actual C40 `L=11, B₅=7` row, the cardinal-three harmonic face
is therefore impossible under the same beta cap used by the completed
singleton dispatcher. -/
theorem elevenFive_c40_l11_sevenDefect_harmonic_three_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
          (blockSystem cfg).blockDegree 4 p +
            (blockSystem cfg).blockDegree 5 p ≤ 18)
    (hH : (elevenFiveHarmonicPivots (blockSystem cfg)).card = 3) : False := by
  have hbound : ∀ p : Point, (blockSystem cfg).blockDegree 5 p ≤
      3 + (if p ∈ elevenFiveHarmonicPivots (blockSystem cfg) then 1 else 0) := by
    intro p
    exact elevenFive_c40_l11_fiveDegree_le_three_add_harmonic
      (blockSystem cfg) p (hlocal p) hC (hbeta p)
  obtain ⟨hfour, htwo, hprofile⟩ :=
    elevenFive_c40_l11_harmonic_three_fiveDegree_profile
      (blockSystem cfg) hcard hglobal hfive hbound hH
  apply fiveBlock_four_three_two_profile_impossible_of_no_singleton
    (blockSystem cfg) hcard hfive hfour htwo hprofile
  intro b hb c hc hbc hsingle
  obtain ⟨p, hpinter⟩ := Finset.card_eq_one.mp hsingle
  have hp : p ∈ (blockSystem cfg).support b ∩
      (blockSystem cfg).support c := by
    rw [hpinter]
    simp
  have hpcommon : p ∈ geometricBlockSupport cfg b ∩
      geometricBlockSupport cfg c := by
    simpa [blockSystem, geometricBlockSystem,
      geometricBlockSupport] using hp
  have hsingleGeo : (geometricBlockSupport cfg b ∩
      geometricBlockSupport cfg c).card = 1 := by
    simpa [blockSystem, geometricBlockSystem,
      geometricBlockSupport] using hsingle
  exact elevenFive_c40_l11_fiveBlock_singleton_impossible
    cfg hcard p (hlocal p) hC (hbeta p) hb hc
      (Finset.mem_inter.mp hpcommon).1
      (Finset.mem_inter.mp hpcommon).2 hbc hsingleGeo

/-- The whole actual C40 `L=11, B₅=7` face reduces to the preceding row
contradiction: harmonic cardinality two was already parity-impossible, and
the remaining cardinality three case is the finite disjoint-pair defect. -/
theorem elevenFive_c40_l11_sevenDefect_impossible_of_beta_cap
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
          (blockSystem cfg).blockDegree 4 p +
            (blockSystem cfg).blockDegree 5 p ≤ 18) : False := by
  have hH := elevenFive_c40_l11_sevenDefect_harmonic_card_eq_three_of_configuration
    cfg hcard hlocal hglobal hC hfive hbeta
  exact elevenFive_c40_l11_sevenDefect_harmonic_three_impossible
    cfg hcard hlocal hglobal hC hfive hbeta hH

end Erdos506.V1
