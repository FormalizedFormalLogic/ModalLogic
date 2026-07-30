module

public import Neighborhood.Semantics.Basic

@[expose] public section

namespace LO.Modal.Neighborhood

open Formula.Neighborhood

variable {F : Frame} {a b}


namespace Frame

class HasPropertyK (F : Frame) : Prop where
  K : ∀ X Y : Set F, F.box (Xᶜ ∪ Y) ∩ F.box X ⊆ F.box Y

export HasPropertyK (K)

end Frame

@[simp]
lemma valid_axiomK_of_hasPropertyK [F.HasPropertyK] : F ⊧ Axioms.K (.atom a) (.atom b) := by
  intro V x;
  suffices (V a)ᶜ ∪ V b ∈ F.𝒩 x → V a ∈ F.𝒩 x → V b ∈ F.𝒩 x by simpa [Satisfies, imp_iff_not_or];
  rintro _ _;
  apply F.K;
  tauto;

lemma hasPropertyK_of_valid_axiomK (h : F ⊧ Axioms.K (.atom 0) (.atom 1)) : F.HasPropertyK := by
  constructor;
  rintro X Y w ⟨hx, hy⟩;
  have : Xᶜ ∪ Y ∈ F.𝒩 w → X ∈ F.𝒩 w → Y ∈ F.𝒩 w := by simpa [Satisfies, ←imp_iff_not_or] using @h (λ a => match a with | 0 => X | 1 => Y | _ => ∅) w;
  apply this <;> assumption;

end LO.Modal.Neighborhood
end
