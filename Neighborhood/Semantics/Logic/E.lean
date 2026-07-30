module

public import Neighborhood.Semantics.Hilbert
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomGeach
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Hilbert.Logics
import Mathlib.Tactic.FinCases

/-!
# The neighborhood logic `LogicE`

Soundness, consistency and completeness of `LogicE`, the weakest classical modal logic, with
respect to all neighborhood frames. Its strict inclusions in the stronger logics live in the
stronger logics' modules.

Also defines two auxiliary countermodels, `Frame.simple_whitehole` and
`Frame.trivial_nontransitive`, reused by several other neighborhood logics.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

@[simp]
lemma Set.inter_eq_univ {s t : Set α} : s ∩ t = Set.univ ↔ s = Set.univ ∧ t = Set.univ := by
  simpa using Set.sInter_eq_univ (S := ({s, t} : Set (Set α)))


abbrev Frame.simple_whitehole : Frame Unit := ⟨fun _ => ∅⟩

@[simp]
lemma Frame.simple_whitehole.not_valid_axiomN :
    ¬Frame.simple_whitehole ⊧ (Axioms.N : Formula α) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun _ => ∅, (), by simp [NotForces, Forces, Frame.box]⟩

abbrev Frame.trivial_nontransitive : Frame (Fin 2) :=
  ⟨fun w => match w with | 0 => ∅ | 1 => {Set.univ}⟩

instance : Frame.trivial_nontransitive.IsRegular where
  regular X Y x hx := by fin_cases x <;> simp_all [Frame.box, Frame.trivial_nontransitive]

instance : Frame.trivial_nontransitive.IsMonotonic where
  mono X Y x := by fin_cases x <;> simp [Frame.box, Frame.trivial_nontransitive]

instance : Frame.trivial_nontransitive.IsReflexive where
  refl X x := by fin_cases x <;> simp_all [Frame.box, Frame.trivial_nontransitive]

lemma Frame.trivial_nontransitive.not_isTransitive :
    ¬Frame.trivial_nontransitive.IsTransitive := by
  intro hC
  have h := hC.trans Set.univ
    (show (1 : Fin 2) ∈ Frame.trivial_nontransitive.box Set.univ by simp [Frame.box])
  simp [Frame.box, Set.eq_univ_iff_forall] at h

lemma Frame.trivial_nontransitive.not_valid_axiomFour :
    ¬Frame.trivial_nontransitive ⊧ (Axioms.Four (.atom 0) : Formula ℕ) :=
  fun h => Frame.trivial_nontransitive.not_isTransitive (isTransitive_of_valid_axiomFour h)


theorem LogicE.sound {κ} [Nonempty κ] (F : Frame κ) :
    A ∈ LogicE → F ⊧ A :=
  Hilbert.sound (fun B hB => by simp at hB)

theorem LogicE.consistent : (@LogicE α).IsConsistent :=
  Hilbert.consistent_of (F := Frame.simple_blackhole) (fun B hB => by simp at hB)

instance : Nonempty (MaximalConsistentSet (@LogicE α)) :=
  MaximalConsistentSet.nonempty LogicE.consistent

variable [DecidableEq α]

theorem LogicE.complete (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), F ⊧ A) :
    A ∈ @LogicE α :=
  (basicCanonicity LogicE).mem_of_valid
    (h (basicCanonicity LogicE).toModel.toFrame (basicCanonicity LogicE).toModel.Val)

end
