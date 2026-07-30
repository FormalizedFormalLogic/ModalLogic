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
abbrev Frame.simple_blackhole : Frame Unit := ⟨fun _ => { Set.univ }⟩

instance : Frame.simple_blackhole.IsMonotonic where
  mono X Y e he := by
    simp only [Frame.box, Set.mem_setOf_eq, Set.mem_singleton_iff] at he ⊢
    exact ⟨Set.Subset.antisymm (Set.subset_univ X) (he ▸ Set.inter_subset_left),
      Set.Subset.antisymm (Set.subset_univ Y) (he ▸ Set.inter_subset_right)⟩

instance : Frame.simple_blackhole.IsRegular := ⟨by
  intro X Y e ⟨hX, hY⟩
  simp_all [Frame.box]⟩

instance : Frame.simple_blackhole.NotContainsEmpty := by
  constructor;
  simp [Set.empty_ne_univ];

instance : Frame.simple_blackhole.HasPropertyK where
  K X Y w hw := by
    simp only [Frame.box, Set.mem_setOf_eq, Set.mem_singleton_iff] at hw ⊢
    obtain ⟨h₁, h₂⟩ := hw
    subst h₂
    simpa using h₁

instance : Frame.simple_blackhole.IsTransitive where
  trans X := by
    intro x hx
    simp only [Frame.box, Set.mem_singleton_iff, Set.mem_setOf_eq] at hx
    subst hx
    simp [Frame.box]

instance : Frame.simple_blackhole.IsEuclidean where
  eucl X x hx := by simp_all [Frame.box, Frame.dia]

instance : Frame.simple_blackhole.IsSymmetric := by
  constructor
  intro X x hx
  have hne : Xᶜ ≠ Set.univ := by
    simp only [ne_eq, Set.compl_univ_iff]
    rintro rfl
    simp at hx
  simp [Frame.box, Frame.dia, hne]

instance : Frame.simple_blackhole.IsSerial where
  serial X x hx := by
    simp only [Frame.box, Set.mem_singleton_iff, Set.mem_setOf_eq] at hx
    subst hx
    simp [Frame.dia, Frame.box, Set.ext_iff]

instance : Frame.simple_blackhole.IsReflexive where
  refl X x hx := by
    simp only [Frame.box, Frame.simple_blackhole, Set.mem_singleton_iff, Set.mem_setOf_eq] at hx
    subst hx
    trivial

instance : Frame.simple_blackhole.ContainsUnit := ⟨by
  ext x
  simp [Frame.box]⟩

end
