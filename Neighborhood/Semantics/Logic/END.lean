module

public import Neighborhood.Semantics.Hilbert
public import Neighborhood.Semantics.Completeness
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.AxiomGeach
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Hilbert.Logics
public import Neighborhood.Semantics.Logic.ED
public import Neighborhood.Semantics.Logic.EP

/-!
# The neighborhood logic `LogicEND`

Soundness, consistency and completeness of `LogicEND`, the classical modal logic axiomatised by
both `N := □⊤` and the seriality axiom `D` over `LogicE`, with respect to the serial neighborhood
frames containing their unit. Also its strict inclusions of `LogicED` and `LogicEP`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

/-! ### Soundness, consistency and completeness -/

/-- `LogicEND` is sound with respect to every serial neighborhood frame containing its unit. -/
theorem LogicEND.sound (h : A ∈ LogicEND) {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit]
    [F.IsSerial] : F ⊧ A :=
  Hilbert.sound
    (fun _ hB => by
      rcases hB with rfl | ⟨_, rfl⟩
      · exact valid_axiomN_of_containsUnit
      · exact valid_axiomD_of_isSerial) h

instance : (@LogicEND α).Consistent :=
  Hilbert.consistent_of (F := Frame.simple_blackhole)
    (fun _ hB => by
      rcases hB with rfl | ⟨_, rfl⟩
      · exact valid_axiomN_of_containsUnit
      · exact valid_axiomD_of_isSerial)

variable [DecidableEq α]

/-- `LogicEND` is complete with respect to all serial frames containing their unit. -/
theorem LogicEND.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), F.ContainsUnit → F.IsSerial → F ⊧ A) :
    A ∈ @LogicEND α :=
  (basicCanonicity LogicEND).mem_of_valid
    (h (basicCanonicity LogicEND).toModel.toFrame inferInstance inferInstance
      (basicCanonicity LogicEND).toModel.Val)

/-! ### Strict inclusions of `LogicED` and `LogicEP` -/

/-- `Frame.simple_whitehole` is (vacuously) serial, since it has no neighborhoods at all. -/
instance : Frame.simple_whitehole.IsSerial where
  serial X x hx := by simp [Frame.box, Frame.simple_whitehole] at hx

theorem LogicED_ssubset_LogicEND : @LogicED ℕ ⊂ LogicEND := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicED ℕ := h (ProvableHilbert.axm (Or.inl rfl))
    exact Frame.simple_whitehole.not_valid_axiomN (LogicED.sound hN Frame.simple_whitehole)

/-- A serial frame containing its unit has no world with the empty set as a neighborhood. -/
instance {κ} [Nonempty κ] {F : Frame κ} [F.ContainsUnit] [F.IsSerial] : F.NotContainsEmpty := by
  sorry

theorem LogicEP_ssubset_LogicEND : @LogicEP ℕ ⊂ LogicEND := by
  sorry

end
