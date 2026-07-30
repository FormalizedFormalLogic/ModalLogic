module

public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Semantics.AxiomK
public import Neighborhood.Semantics.AxiomGeach
import Mathlib.Tactic.FinCases

@[expose] public section

variable {α : Type u}

abbrev Frame.trivial_containsUnit : Frame (Fin 2) := ⟨fun x => {{x}ᶜ, Set.univ}⟩

lemma Frame.trivial_containsUnit.not_isTransitive :
    ¬Frame.trivial_containsUnit.IsTransitive := by
  intro hC
  have hbox0 : Frame.trivial_containsUnit.box ({0} : Set (Fin 2)) = {1} := by
    ext y; fin_cases y <;> simp [Frame.box, Frame.trivial_containsUnit, Set.ext_iff]
  have hbox1 : Frame.trivial_containsUnit.box ({1} : Set (Fin 2)) = {0} := by
    ext y; fin_cases y <;> simp [Frame.box, Frame.trivial_containsUnit, Set.ext_iff]
  have hiter : Frame.trivial_containsUnit.box^[2] ({0} : Set (Fin 2)) = {0} := by
    show Frame.trivial_containsUnit.box (Frame.trivial_containsUnit.box {0}) = {0}
    rw [hbox0, hbox1]
  have h1 : (1 : Fin 2) ∈ Frame.trivial_containsUnit.box ({0} : Set (Fin 2)) := by
    rw [hbox0]; rfl
  have h2 := hC.trans ({0} : Set (Fin 2)) h1
  rw [hiter] at h2
  simp at h2

lemma Frame.trivial_containsUnit.not_valid_axiomFour :
    ¬Frame.trivial_containsUnit ⊧ (Axioms.Four (.atom 0) : Formula ℕ) :=
  fun h => Frame.trivial_containsUnit.not_isTransitive (isTransitive_of_valid_axiomFour h)

instance : Frame.trivial_containsUnit.ContainsUnit := ⟨by
  ext x; fin_cases x <;> simp [Frame.box, Frame.trivial_containsUnit]⟩

instance : Frame.trivial_containsUnit.IsSerial where
  serial X x hx := by
    simp only [Frame.trivial_containsUnit, Frame.box, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> fin_cases x <;>
      simp [Frame.box, Frame.dia, Frame.trivial_containsUnit, Set.ext_iff]

end
