module

public import Neighborhood.Semantics.Logic.ECN
public import Neighborhood.Semantics.Logic.EMC
public import Neighborhood.Semantics.Logic.EMN
import Mathlib.Tactic.FinCases

/-!
# The neighborhood logic `LogicEMCN`

Soundness, consistency and completeness of `LogicEMCN`, the classical modal logic axiomatised by
the monotonicity axiom `M`, the regularity axiom `C` and `N := □⊤`, with respect to the
neighborhood frames that are monotonic, regular, and contain their unit.

Also proves the strict inclusions of `LogicECN`, `LogicEMC` and `LogicEMN` in `LogicEMCN` (a
comparison of two logics lives in the stronger logic's module).
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEMCN.sound (h : A ∈ LogicEMCN) {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsRegular] [F.ContainsUnit] : F ⊧ A :=
  Hilbert.sound (by
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl)
    · exact valid_axiomM_of_isMonotonic
    · exact valid_axiomC_of_isRegular
    · exact valid_axiomN_of_containsUnit) h

instance : (@LogicEMCN α).Consistent :=
  Hilbert.consistent_of (F := Frame.simple_blackhole) (by
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl)
    · exact valid_axiomM_of_isMonotonic
    · exact valid_axiomC_of_isRegular
    · exact valid_axiomN_of_containsUnit)

variable [DecidableEq α]

theorem LogicEMCN.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), F.IsMonotonic → F.IsRegular →
      F.ContainsUnit → F ⊧ A) :
    A ∈ @LogicEMCN α :=
  (supplementedBasicCanonicity LogicEMCN).mem_of_valid
    (h (supplementedBasicCanonicity LogicEMCN).toModel.toFrame inferInstance inferInstance
      inferInstance (supplementedBasicCanonicity LogicEMCN).toModel.Val)


abbrev Frame.ECN_counterframe_for_M : Frame (Fin 2) := ⟨fun _ => {∅, Set.univ}⟩

instance : Frame.ECN_counterframe_for_M.IsRegular where
  regular X Y w hw := by
    simp only [Frame.box, Frame.ECN_counterframe_for_M, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw ⊢
    obtain ⟨hX, hY⟩ := hw
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;> simp

instance : Frame.ECN_counterframe_for_M.ContainsUnit := ⟨by
  ext w
  simp [Frame.box, Frame.ECN_counterframe_for_M]⟩

@[simp]
lemma Frame.ECN_counterframe_for_M.not_valid_axiomM :
    ¬Frame.ECN_counterframe_for_M ⊧ (Axioms.M (.atom 0) (.atom 1) : Formula ℕ) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun a => match a with | 0 => {0} | 1 => {1} | _ => Set.univ, 0, by
      unfold NotForces Forces
      simp [Frame.box, Frame.ECN_counterframe_for_M, Set.ext_iff]⟩

theorem LogicECN_ssubset_LogicEMCN : @LogicECN ℕ ⊂ LogicEMCN := by
  constructor
  · apply Hilbert.subset_of_subset_axioms
    rintro A (hC | hN)
    · exact Or.inl (Or.inr hC)
    · exact Or.inr hN
  · intro h
    have hM : Axioms.M (.atom 0) (.atom 1) ∈ @LogicECN ℕ :=
      h (ProvableHilbert.axm (Or.inl (Or.inl ⟨_, _, rfl⟩)))
    exact Frame.ECN_counterframe_for_M.not_valid_axiomM
      (LogicECN.sound hM Frame.ECN_counterframe_for_M)


theorem LogicEMC_ssubset_LogicEMCN : @LogicEMC ℕ ⊂ LogicEMCN := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicEMC ℕ := h (ProvableHilbert.axm (Or.inr rfl))
    exact Frame.simple_whitehole.not_valid_axiomN (LogicEMC.sound hN Frame.simple_whitehole)


instance : Frame.counterframe_axiomC₁.ContainsUnit := ⟨by
  rw [Set.Fin2.eq_univ]
  ext w
  fin_cases w <;> simp [Frame.box, Frame.counterframe_axiomC₁]⟩

theorem LogicEMN_ssubset_LogicEMCN : @LogicEMN ℕ ⊂ LogicEMCN := by
  constructor
  · apply Hilbert.subset_of_subset_axioms
    rintro A (hM | hN)
    · exact Or.inl (Or.inl hM)
    · exact Or.inr hN
  · intro h
    have hC : Axioms.C (.atom 0) (.atom 1) ∈ @LogicEMN ℕ :=
      h (ProvableHilbert.axm (Or.inl (Or.inr ⟨_, _, rfl⟩)))
    exact Frame.counterframe_axiomC₁.not_valid_axiomC
      (LogicEMN.sound hC Frame.counterframe_axiomC₁)

end
