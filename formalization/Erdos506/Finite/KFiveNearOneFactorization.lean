import Mathlib.Tactic

/-!
# Near-one-factorizations of the complete graph on five vertices

This file is deliberately independent of incidence and projective geometry.
Its abstract interface uses the chord type `A.powersetCard 2`.  The finite
part then labels the vertices and the omitted colours by `Fin 5`; after that
each colour has only three possible two-edge matchings.

There are exactly six labelled tables.  The classification is split into
three small certificates according to the first row, so a consumer never has
to unfold one large search theorem.
-/

namespace Erdos506.Finite

/-- The chords of a finite vertex set. -/
abbrev KFiveChord {α : Type*} [DecidableEq α] (A : Finset α) :=
  ↥(A.powersetCard 2)

/--
An abstract partition of the ten chords of a five-set into five matchings.

The colours are already identified with the vertices they omit.  Keeping
this equivalence as part of the interface makes the boundary with geometric
applications explicit: geometry supplies the five fibres and the omitted
colour bijection, while this module handles only the finite graph.
-/
structure KFiveNearOneFactorization
    {α : Type*} [DecidableEq α]
    (A : Finset α) (Colour : Type*)
    [Fintype Colour] [DecidableEq Colour] where
  vertex_card : A.card = 5
  factor : Colour → Finset (KFiveChord A)
  factor_card_two : ∀ c, (factor c).card = 2
  factor_matching : ∀ c e, e ∈ factor c → ∀ f, f ∈ factor c →
    e ≠ f → Disjoint e.1 f.1
  omittedColourEquiv : Colour ≃ ↥A
  factor_avoids_omitted : ∀ c e, e ∈ factor c →
    (omittedColourEquiv c).1 ∉ e.1
  factor_covers_other : ∀ c v, v ≠ omittedColourEquiv c →
    ∃ e ∈ factor c, v.1 ∈ e.1
  chord_unique : ∀ e : KFiveChord A, ∃! c, e ∈ factor c

namespace KFiveNearOneFactorization

variable {α Colour : Type*} [DecidableEq α]
  [Fintype Colour] [DecidableEq Colour]
  {A : Finset α}

/-- Reindex the factors directly by their omitted vertices. -/
def factorAtVertex (F : KFiveNearOneFactorization A Colour) (v : ↥A) :
    Finset (KFiveChord A) :=
  F.factor (F.omittedColourEquiv.symm v)

@[simp] theorem factorAtVertex_card
    (F : KFiveNearOneFactorization A Colour) (v : ↥A) :
    (F.factorAtVertex v).card = 2 := by
  exact F.factor_card_two _

theorem factorAtVertex_avoids
    (F : KFiveNearOneFactorization A Colour) (v : ↥A)
    (e : KFiveChord A) (he : e ∈ F.factorAtVertex v) :
    v.1 ∉ e.1 := by
  simpa [factorAtVertex] using
    F.factor_avoids_omitted (F.omittedColourEquiv.symm v) e he

end KFiveNearOneFactorization

/-! ## The fifteen local rows on `Fin 5` -/

/-- The ten labelled chords of `Fin 5`. -/
abbrev FinFiveChord :=
  KFiveChord (Finset.univ : Finset (Fin 5))

def kFiveChord01 : FinFiveChord := ⟨{0, 1}, by decide⟩
def kFiveChord02 : FinFiveChord := ⟨{0, 2}, by decide⟩
def kFiveChord03 : FinFiveChord := ⟨{0, 3}, by decide⟩
def kFiveChord04 : FinFiveChord := ⟨{0, 4}, by decide⟩
def kFiveChord12 : FinFiveChord := ⟨{1, 2}, by decide⟩
def kFiveChord13 : FinFiveChord := ⟨{1, 3}, by decide⟩
def kFiveChord14 : FinFiveChord := ⟨{1, 4}, by decide⟩
def kFiveChord23 : FinFiveChord := ⟨{2, 3}, by decide⟩
def kFiveChord24 : FinFiveChord := ⟨{2, 4}, by decide⟩
def kFiveChord34 : FinFiveChord := ⟨{3, 4}, by decide⟩

/--
For an omitted colour `c`, the three entries are the three perfect matchings
on the other four vertices.  This is the only local choice in a labelled
near-one-factorization of `K5`.
-/
def kFiveRowOptions : Fin 5 → Fin 3 → Finset FinFiveChord := ![
  ![
    {kFiveChord12, kFiveChord34},
    {kFiveChord13, kFiveChord24},
    {kFiveChord14, kFiveChord23}
  ],
  ![
    {kFiveChord23, kFiveChord04},
    {kFiveChord24, kFiveChord03},
    {kFiveChord02, kFiveChord34}
  ],
  ![
    {kFiveChord34, kFiveChord01},
    {kFiveChord03, kFiveChord14},
    {kFiveChord04, kFiveChord13}
  ],
  ![
    {kFiveChord04, kFiveChord12},
    {kFiveChord14, kFiveChord02},
    {kFiveChord24, kFiveChord01}
  ],
  ![
    {kFiveChord01, kFiveChord23},
    {kFiveChord02, kFiveChord13},
    {kFiveChord03, kFiveChord12}
  ]
]

theorem kFiveRowOptions_card_two :
    ∀ c r, (kFiveRowOptions c r).card = 2 := by
  decide +kernel

theorem kFiveRowOptions_matching :
    ∀ c r e, e ∈ kFiveRowOptions c r →
      ∀ f, f ∈ kFiveRowOptions c r → e ≠ f → Disjoint e.1 f.1 := by
  decide +kernel

theorem kFiveRowOptions_avoids_colour :
    ∀ c r e, e ∈ kFiveRowOptions c r → c ∉ e.1 := by
  decide +kernel

theorem kFiveRowOptions_covers_other :
    ∀ c r v, v ≠ c →
      ∃ e ∈ kFiveRowOptions c r, v ∈ e.1 := by
  decide +kernel

/-! ## Codes and the six tables -/

/-- The factor belonging to colour `c` in a row-choice code. -/
def kFiveCodedFactor (code : Fin 5 → Fin 3) (c : Fin 5) :
    Finset FinFiveChord :=
  kFiveRowOptions c (code c)

/-- Every chord has exactly one colour.  Local matching properties are
automatic from `kFiveRowOptions`. -/
def IsKFiveNearOneFactorizationCode (code : Fin 5 → Fin 3) : Prop :=
  ∀ e : FinFiveChord, ∃! c : Fin 5, e ∈ kFiveCodedFactor code c

private instance (code : Fin 5 → Fin 3) :
    Decidable (IsKFiveNearOneFactorizationCode code) := by
  unfold IsKFiveNearOneFactorizationCode ExistsUnique
  infer_instance

/-- A checked labelled near-one-factorization code. -/
@[ext] structure KFiveNearOneFactorizationCode where
  rowChoice : Fin 5 → Fin 3
  valid : IsKFiveNearOneFactorizationCode rowChoice

instance : CoeFun KFiveNearOneFactorizationCode
    (fun _ => Fin 5 → Fin 3) where
  coe C := C.rowChoice

/--
The complete list of labelled tables.  In decimal row notation these are
`00121`, `01210`, `10012`, `12100`, `21001`, and `22222`.
-/
def kFiveNearOneFactorizationTable : Fin 6 → Fin 5 → Fin 3 := ![
  ![0, 0, 1, 2, 1],
  ![0, 1, 2, 1, 0],
  ![1, 0, 0, 1, 2],
  ![1, 2, 1, 0, 0],
  ![2, 1, 0, 0, 1],
  ![2, 2, 2, 2, 2]
]

theorem kFiveNearOneFactorizationTable_valid :
    ∀ i, IsKFiveNearOneFactorizationCode
      (kFiveNearOneFactorizationTable i) := by
  decide +kernel

theorem kFiveNearOneFactorizationTable_injective :
    Function.Injective kFiveNearOneFactorizationTable := by
  decide +kernel

/-- The two valid continuations of a code whose first row is choice zero. -/
theorem kFiveNearOneFactorizationCode_first_zero :
    ∀ code : Fin 5 → Fin 3, code 0 = 0 →
      (IsKFiveNearOneFactorizationCode code ↔
        code = kFiveNearOneFactorizationTable 0 ∨
        code = kFiveNearOneFactorizationTable 1) := by
  decide +kernel

/-- The two valid continuations of a code whose first row is choice one. -/
theorem kFiveNearOneFactorizationCode_first_one :
    ∀ code : Fin 5 → Fin 3, code 0 = 1 →
      (IsKFiveNearOneFactorizationCode code ↔
        code = kFiveNearOneFactorizationTable 2 ∨
        code = kFiveNearOneFactorizationTable 3) := by
  decide +kernel

/-- The two valid continuations of a code whose first row is choice two. -/
theorem kFiveNearOneFactorizationCode_first_two :
    ∀ code : Fin 5 → Fin 3, code 0 = 2 →
      (IsKFiveNearOneFactorizationCode code ↔
        code = kFiveNearOneFactorizationTable 4 ∨
        code = kFiveNearOneFactorizationTable 5) := by
  decide +kernel

private theorem finThree_eq_zero_or_one_or_two :
    ∀ r : Fin 3, r = 0 ∨ r = 1 ∨ r = 2 := by
  decide +kernel

/-- Completeness of the six explicit labelled tables. -/
theorem kFiveNearOneFactorizationCode_complete
    (code : Fin 5 → Fin 3) :
    IsKFiveNearOneFactorizationCode code ↔
      ∃ i : Fin 6, code = kFiveNearOneFactorizationTable i := by
  constructor
  · intro hvalid
    rcases finThree_eq_zero_or_one_or_two (code 0) with hzero | hone | htwo
    · rcases (kFiveNearOneFactorizationCode_first_zero code hzero).mp hvalid with
        h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    · rcases (kFiveNearOneFactorizationCode_first_one code hone).mp hvalid with
        h | h
      · exact ⟨2, h⟩
      · exact ⟨3, h⟩
    · rcases (kFiveNearOneFactorizationCode_first_two code htwo).mp hvalid with
        h | h
      · exact ⟨4, h⟩
      · exact ⟨5, h⟩
  · rintro ⟨i, rfl⟩
    exact kFiveNearOneFactorizationTable_valid i

/-- The six table indices are equivalent to the checked code type. -/
noncomputable def kFiveNearOneFactorizationCodeEquiv :
    Fin 6 ≃ KFiveNearOneFactorizationCode :=
  Equiv.ofBijective
    (fun i =>
      { rowChoice := kFiveNearOneFactorizationTable i
        valid := kFiveNearOneFactorizationTable_valid i })
    ⟨by
      intro i j hij
      apply kFiveNearOneFactorizationTable_injective
      exact congrArg KFiveNearOneFactorizationCode.rowChoice hij,
     by
      rintro ⟨code, hcode⟩
      obtain ⟨i, hi⟩ :=
        (kFiveNearOneFactorizationCode_complete code).mp hcode
      refine ⟨i, ?_⟩
      apply KFiveNearOneFactorizationCode.ext
      exact hi.symm⟩

/-- The manuscript normal form `13|24, 02|34, 03|14, 04|12, 01|23`. -/
def kFiveCanonicalNearOneFactorizationCode :
    KFiveNearOneFactorizationCode :=
  { rowChoice := kFiveNearOneFactorizationTable 3
    valid := kFiveNearOneFactorizationTable_valid 3 }

/-- The cyclic all-double normal form `14|23, 02|34, 04|13, 01|24, 03|12`. -/
def kFiveCyclicNearOneFactorizationCode :
    KFiveNearOneFactorizationCode :=
  { rowChoice := kFiveNearOneFactorizationTable 5
    valid := kFiveNearOneFactorizationTable_valid 5 }

/-! ## Conversion of a checked code to the abstract interface -/

/-- The tautological identification of `Fin 5` with the subtype of `univ`. -/
def finFiveVertexEquiv :
    Fin 5 ≃ ↥(Finset.univ : Finset (Fin 5)) where
  toFun v := ⟨v, Finset.mem_univ v⟩
  invFun v := v.1
  left_inv _ := rfl
  right_inv _ := rfl

/-- A checked row-choice code supplies an abstract near-one-factorization. -/
def KFiveNearOneFactorizationCode.toFactorization
    (C : KFiveNearOneFactorizationCode) :
    KFiveNearOneFactorization
      (Finset.univ : Finset (Fin 5)) (Fin 5) where
  vertex_card := by decide
  factor := kFiveCodedFactor C.rowChoice
  factor_card_two := by
    intro c
    simpa [kFiveCodedFactor] using
      kFiveRowOptions_card_two c (C.rowChoice c)
  factor_matching := by
    intro c e he f hf hne
    exact kFiveRowOptions_matching c (C.rowChoice c) e he f hf hne
  omittedColourEquiv := finFiveVertexEquiv
  factor_avoids_omitted := by
    intro c e he
    simpa [finFiveVertexEquiv] using
      kFiveRowOptions_avoids_colour c (C.rowChoice c) e he
  factor_covers_other := by
    intro c v hv
    have hv' : v.1 ≠ c := by
      intro hvc
      apply hv
      apply Subtype.ext
      simpa [finFiveVertexEquiv] using hvc
    obtain ⟨e, he, hve⟩ :=
      kFiveRowOptions_covers_other c (C.rowChoice c) v.1 hv'
    exact ⟨e, he, hve⟩
  chord_unique := C.valid

@[simp] theorem KFiveNearOneFactorizationCode.toFactorization_factor
    (C : KFiveNearOneFactorizationCode) (c : Fin 5) :
    C.toFactorization.factor c = kFiveCodedFactor C.rowChoice c := rfl

end Erdos506.Finite
