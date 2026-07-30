module

public import Neighborhood.Axioms
public import Neighborhood.Semantics.Basic
public import Mathlib.Tactic.TautoSet

/-!
# The monotonicity frame condition and axiom `M`

`Frame.IsMonotonic` is the neighborhood-frame condition (the neighborhood function is monotone
under intersection) that corresponds to the modal axiom `M : □(A ⋏ B) 🡒 (□A ⋏ □B)`.
-/

@[expose] public section

variable {κ : Type u} [Nonempty κ] {F : Frame κ}

/-- A frame is monotonic when its neighborhood function sends an intersection of two sets into
the intersection of their boxes. -/
class Frame.IsMonotonic (F : Frame κ) : Prop where
  mono : ∀ X Y : Set κ, F.box (X ∩ Y) ⊆ F.box X ∩ F.box Y

lemma Frame.mono [F.IsMonotonic] {X Y : Set κ} : F.box (X ∩ Y) ⊆ F.box X ∩ F.box Y :=
  IsMonotonic.mono X Y

lemma Frame.mono' [F.IsMonotonic] {X Y : Set κ} (h : X ⊆ Y) : F.box X ⊆ F.box Y := by
  have := F.mono (X := X) (Y := Y)
  rw [show X ∩ Y = X by tauto_set] at this
  exact this.trans Set.inter_subset_right

instance : Frame.simple_blackhole.IsMonotonic where
  mono X Y e he := by
    simp only [Frame.box, Set.mem_setOf_eq, Set.mem_singleton_iff] at he ⊢
    exact ⟨Set.Subset.antisymm (Set.subset_univ X) (he ▸ Set.inter_subset_left),
      Set.Subset.antisymm (Set.subset_univ Y) (he ▸ Set.inter_subset_right)⟩

section

variable {α : Type v} {A B : Formula α}

theorem valid_axiomM_of_isMonotonic [F.IsMonotonic] : F ⊧ Axioms.M A B := by
  intro V x
  apply forces_imp.mpr
  intro hx
  apply forces_and.mpr
  have hx' := forces_box.mp hx
  rw [Model.truthset.eq_and] at hx'
  exact ⟨forces_box.mpr (F.mono hx').1, forces_box.mpr (F.mono hx').2⟩

end
end
