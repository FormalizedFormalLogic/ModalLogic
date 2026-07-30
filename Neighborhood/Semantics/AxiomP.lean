module

public import Neighborhood.Axioms
public import Neighborhood.Semantics.Basic

/-!
# Axiom `P`

Validity of the axiom scheme `P` (`∼□⊥`) on neighborhood frames, and its correspondence with
frames in which no world has the empty set as one of its neighborhoods.
-/

@[expose] public section

variable {κ : Type u} [Nonempty κ] {α : Type v} {F : Frame κ}

namespace Frame

/-- A frame in which no world has the empty set as one of its neighborhoods. -/
class NotContainsEmpty (F : Frame κ) : Prop where
  not_contains_empty : ∀ x, ∅ ∉ F.𝒩 x

@[simp, grind =>]
lemma not_contains_empty [F.NotContainsEmpty] {x : F.World} : ∅ ∉ F.𝒩 x :=
  NotContainsEmpty.not_contains_empty x

@[simp]
lemma mem_dia_univ [F.NotContainsEmpty] {x : F.World} : x ∈ F.dia Set.univ := by
  simp [Frame.dia, Frame.box]

instance : Frame.simple_blackhole.NotContainsEmpty :=
  ⟨fun _ => by simp [Set.empty_ne_univ]⟩

end Frame

/-- `P` is valid on any frame in which no world has the empty set as one of its neighborhoods. -/
@[simp]
theorem valid_axiomP_of_notContainsEmpty [F.NotContainsEmpty] : F ⊧ (Axioms.P : Formula α) := by
  intro V x
  simp [Forces, Frame.box]

/-- A frame validating `P` has no world with the empty set as one of its neighborhoods. -/
theorem notContainsEmpty_of_valid_axiomP (h : F ⊧ (Axioms.P : Formula α)) : F.NotContainsEmpty :=
  ⟨fun x => by simpa [Forces, Frame.box] using h (fun _ => ∅) x⟩

end
