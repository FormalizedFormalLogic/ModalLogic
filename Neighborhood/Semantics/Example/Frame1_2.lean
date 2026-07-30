module

public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Semantics.AxiomK
public import Neighborhood.Semantics.AxiomGeach

@[expose] public section

variable {α : Type u}


/-- The one-world frame whose only neighborhood is the whole carrier. -/
abbrev frame_1_2 : Frame (Fin 1) := ⟨fun _ => { Set.univ }⟩

instance : frame_1_2.IsMonotonic where
  mono X Y e he := by
    simp only [Frame.box, Set.mem_setOf_eq, Set.mem_singleton_iff] at he ⊢
    exact ⟨Set.Subset.antisymm (Set.subset_univ X) (he ▸ Set.inter_subset_left),
      Set.Subset.antisymm (Set.subset_univ Y) (he ▸ Set.inter_subset_right)⟩

instance : frame_1_2.IsRegular := ⟨by
  intro X Y e ⟨hX, hY⟩
  simp_all [Frame.box]⟩

instance : frame_1_2.NotContainsEmpty := by
  constructor;
  simp [Set.empty_ne_univ];

instance : frame_1_2.HasPropertyK where
  K X Y w hw := by
    simp only [Frame.box, Set.mem_setOf_eq, Set.mem_singleton_iff] at hw ⊢
    obtain ⟨h₁, h₂⟩ := hw
    subst h₂
    simpa using h₁

instance : frame_1_2.IsTransitive where
  trans X := by
    intro x hx
    simp only [Frame.box, Set.mem_singleton_iff, Set.mem_setOf_eq] at hx
    subst hx
    simp [Frame.box]

instance : frame_1_2.IsEuclidean where
  eucl X x hx := by simp_all [Frame.box, Frame.dia]

instance : frame_1_2.IsSymmetric := by
  constructor
  intro X x hx
  have hne : Xᶜ ≠ Set.univ := by
    simp only [ne_eq, Set.compl_univ_iff]
    rintro rfl
    simp at hx
  simp [Frame.box, Frame.dia, hne]

instance : frame_1_2.IsSerial where
  serial X x hx := by
    simp only [Frame.box, Set.mem_singleton_iff, Set.mem_setOf_eq] at hx
    subst hx
    simp [Frame.dia, Frame.box, Set.ext_iff]

instance : frame_1_2.IsReflexive where
  refl X x hx := by
    simp only [Frame.box, frame_1_2, Set.mem_singleton_iff, Set.mem_setOf_eq] at hx
    subst hx
    trivial

instance : frame_1_2.ContainsUnit := ⟨by
  ext x
  simp [Frame.box]⟩

end
