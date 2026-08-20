import Mathlib.Tactic

/-!
# The six unordered pairs of `Fin 4`

This file isolates the only sixteen-case enumeration used by the
four-pentagon profile normalizer.  Each branch is closed independently;
downstream proofs use only the opaque theorem statement.
-/

namespace Erdos506.Finite

namespace FourPentagonFinFourPairLedger

/-- Two distinct elements of `Fin 4` form one of its six unordered pairs. -/
theorem pair_cases {j k : Fin 4} (hjk : j ≠ k) :
    ({j, k} : Finset (Fin 4)) = ({0, 1} : Finset (Fin 4)) ∨
    {j, k} = ({0, 2} : Finset (Fin 4)) ∨
    {j, k} = ({0, 3} : Finset (Fin 4)) ∨
    {j, k} = ({1, 2} : Finset (Fin 4)) ∨
    {j, k} = ({1, 3} : Finset (Fin 4)) ∨
    {j, k} = ({2, 3} : Finset (Fin 4)) := by
  fin_cases j <;> fin_cases k
  · exact (hjk rfl).elim
  · exact Or.inl (by decide)
  · exact Or.inr (Or.inl (by decide))
  · exact Or.inr (Or.inr (Or.inl (by decide)))
  · exact Or.inl (by decide)
  · exact (hjk rfl).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · exact Or.inr (Or.inl (by decide))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · exact (hjk rfl).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))
  · exact Or.inr (Or.inr (Or.inl (by decide)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))
  · exact (hjk rfl).elim

/-- A four-entry vector is injective when its six unordered pairs are
distinct.  Keeping this enumeration here prevents the labeling constructor
from reopening sixteen `Fin 4` branches. -/
theorem vector_injective
    {α : Type*} {b₀ b₁ b₂ b₃ : α}
    (h₀₁ : b₀ ≠ b₁) (h₀₂ : b₀ ≠ b₂) (h₀₃ : b₀ ≠ b₃)
    (h₁₂ : b₁ ≠ b₂) (h₁₃ : b₁ ≠ b₃) (h₂₃ : b₂ ≠ b₃) :
    Function.Injective (![b₀, b₁, b₂, b₃] : Fin 4 → α) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · change b₀ = b₁ at hij
    exact (h₀₁ hij).elim
  · change b₀ = b₂ at hij
    exact (h₀₂ hij).elim
  · change b₀ = b₃ at hij
    exact (h₀₃ hij).elim
  · change b₁ = b₀ at hij
    exact (h₀₁ hij.symm).elim
  · rfl
  · change b₁ = b₂ at hij
    exact (h₁₂ hij).elim
  · change b₁ = b₃ at hij
    exact (h₁₃ hij).elim
  · change b₂ = b₀ at hij
    exact (h₀₂ hij.symm).elim
  · change b₂ = b₁ at hij
    exact (h₁₂ hij.symm).elim
  · rfl
  · change b₂ = b₃ at hij
    exact (h₂₃ hij).elim
  · change b₃ = b₀ at hij
    exact (h₀₃ hij.symm).elim
  · change b₃ = b₁ at hij
    exact (h₁₃ hij.symm).elim
  · change b₃ = b₂ at hij
    exact (h₂₃ hij.symm).elim
  · rfl

end FourPentagonFinFourPairLedger

end Erdos506.Finite
