module

public import Neighborhood.Axioms
public import Neighborhood.Semantics.Basic

/-!
# Axiom `N` on neighborhood frames

The frame condition corresponding to the axiom `N := □⊤`: the whole carrier is a neighborhood of
every world. This is exactly the requirement that `N` be valid on the frame.
-/

@[expose] public section

variable {κ : Type u} [Nonempty κ] {α : Type v} {F : Frame κ}

/-- A frame contains its unit: the whole carrier is a neighborhood of every world. -/
class Frame.ContainsUnit (F : Frame κ) : Prop where
  contains_unit : F.box Set.univ = Set.univ

lemma Frame.contains_unit [F.ContainsUnit] : F.box Set.univ = Set.univ :=
  Frame.ContainsUnit.contains_unit

@[simp]
lemma Frame.univ_mem [F.ContainsUnit] (x : F.World) : Set.univ ∈ F.𝒩 x := by
  have : x ∈ F.box Set.univ := by rw [F.contains_unit]; trivial
  simpa [Frame.box] using this

instance : (Frame.simple_blackhole).ContainsUnit := ⟨by
  ext x
  simp [Frame.box]⟩

@[simp, grind]
theorem valid_axiomN_of_containsUnit [F.ContainsUnit] : F ⊧ (Axioms.N : Formula α) := by
  intro V x
  simp [Forces, F.contains_unit]

theorem containsUnit_of_valid_axiomN (h : F ⊧ (Axioms.N : Formula ℕ)) : F.ContainsUnit := by
  constructor
  ext x
  simpa [Forces] using h (fun _ => Set.univ) x

end
