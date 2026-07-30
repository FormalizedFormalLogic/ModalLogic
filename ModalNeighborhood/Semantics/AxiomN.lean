module

public import ModalNeighborhood.Semantics.Completeness
public import Foundation.Modal.Entailment.EN

@[expose] public section

namespace LO.Modal.Neighborhood

open Formula.Neighborhood

variable {F : Frame}

class Frame.ContainsUnit (F : Frame) : Prop where
  contains_unit : F.box Set.univ = Set.univ

lemma Frame.contains_unit [Frame.ContainsUnit F] : F.box Set.univ = Set.univ := Frame.ContainsUnit.contains_unit

@[simp]
lemma Frame.univ_mem [Frame.ContainsUnit F] (x) : Set.univ ∈ F.𝒩 x := by
  have : x ∈ F.box Set.univ := by rw [F.contains_unit]; trivial;
  simpa [Frame.box] using this;

instance : Frame.simple_blackhole.ContainsUnit := ⟨by ext x; simp⟩

@[simp]
lemma valid_axiomN_of_ContainsUnit [F.ContainsUnit] : F ⊧ Axioms.N := by
  intro V x;
  simp [Satisfies, F.contains_unit];

lemma containsUnit_of_valid_axiomN (h : F ⊧ Axioms.N) : F.ContainsUnit := by
  constructor;
  ext x;
  simpa [Satisfies] using @h (λ _ => Set.univ) x;

section

variable [Entailment S (Formula ℕ)]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.E 𝓢]

open Entailment
open MaximalConsistentSet
open proofset

instance [Entailment.HasAxiomN 𝓢] : (basicCanonicity 𝓢).toModel.ContainsUnit := by
  constructor;
  ext x;
  constructor;
  . intro _; trivial;
  . intro _;
    show ∃ φ, □φ ∈ x.1 ∧ Set.univ = proofset 𝓢 φ;
    exact ⟨⊤, MaximalConsistentSet.mem_of_prove (by simp), by simp [proofset.eq_top]⟩;

instance [Entailment.HasAxiomN 𝓢] : (relativeBasicCanonicity 𝓢 P).toModel.ContainsUnit := by
  constructor;
  ext x;
  suffices Set.univ ∈ (relativeBasicCanonicity 𝓢 P).toModel.𝒩 x by simpa;
  left;
  use ⊤;
  refine ⟨MaximalConsistentSet.mem_of_prove (by simp), ?_⟩;
  simp only [proofset.eq_top]; rfl;

end


end LO.Modal.Neighborhood
end
