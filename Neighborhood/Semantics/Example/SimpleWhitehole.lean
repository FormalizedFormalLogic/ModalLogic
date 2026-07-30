module

public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Semantics.AxiomK
public import Neighborhood.Semantics.AxiomGeach

@[expose] public section

variable {α : Type u}

abbrev Frame.simple_whitehole : Frame Unit := ⟨fun _ => ∅⟩

@[simp]
lemma Frame.simple_whitehole.not_valid_axiomN :
    ¬Frame.simple_whitehole ⊧ (Axioms.N : Formula α) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun _ => ∅, (), by simp [NotForces, Forces, Frame.box]⟩

instance : Frame.simple_whitehole.IsRegular := ⟨by simp [Frame.box, Frame.simple_whitehole]⟩

instance : Frame.simple_whitehole.IsMonotonic where
  mono := by simp_all [Frame.simple_whitehole, Frame.box]

instance : Frame.simple_whitehole.IsTransitive where
  trans X := by simp [Frame.box]

instance : Frame.simple_whitehole.IsSerial where
  serial X x hx := by simp [Frame.box, Frame.simple_whitehole] at hx

instance : Frame.simple_whitehole.IsReflexive :=
  ⟨fun X => by simp [Frame.box, Frame.simple_whitehole]⟩

end
