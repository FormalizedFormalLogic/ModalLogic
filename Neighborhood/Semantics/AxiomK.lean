module

public import Neighborhood.Axioms
public import Neighborhood.Semantics.Basic

/-!
# Axiom `K`

The neighborhood-frame correlate of the axiom `K`, `□(A 🡒 B) 🡒 □A 🡒 □B`.
-/

@[expose] public section

namespace Frame

variable {κ : Type u} [Nonempty κ]

/-- A frame satisfies the `K`-property when, for all subsets `X Y` of the carrier, `Xᶜ ∪ Y` and
`X` both being neighborhoods of a world forces `Y` to be one as well. -/
class HasPropertyK (F : Frame κ) : Prop where
  K : ∀ X Y : Set κ, F.box (Xᶜ ∪ Y) ∩ F.box X ⊆ F.box Y

export HasPropertyK (K)

instance : Frame.simple_blackhole.HasPropertyK where
  K X Y w hw := by
    simp only [Frame.box, Set.mem_setOf_eq, Set.mem_singleton_iff] at hw ⊢
    obtain ⟨h₁, h₂⟩ := hw
    subst h₂
    simpa using h₁

end Frame

section

variable {κ : Type u} [Nonempty κ] {α : Type v} {F : Frame κ} {A B : Formula α}

theorem valid_axiomK_of_hasPropertyK [F.HasPropertyK] : F ⊧ Axioms.K A B := by
  intro V x
  simp only [forces_imp, forces_box]
  intro h₁ h₂
  exact F.K _ _ ⟨h₁, h₂⟩

theorem hasPropertyK_of_valid_axiomK (h : ∀ A B : Formula ℕ, F ⊧ Axioms.K A B) : F.HasPropertyK where
  K X Y w := by
    have := (h (.atom 0) (.atom 1)) (fun n => match n with | 0 => X | 1 => Y | _ => ∅) w
    simpa [forces_imp, forces_box] using this

end
