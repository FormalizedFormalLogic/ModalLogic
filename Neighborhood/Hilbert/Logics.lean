module

public import Neighborhood.Hilbert.Basic

/-!
# The classical non-normal modal logics between `E` and `ET5`

Definitions of the logics `E`, `EM`, ..., `ET5` by their Hilbert axiomatisations, and the two
coincidences of logics with different axiom sets.
-/

@[expose] public section

abbrev E : Logic := Hilbert ∅

abbrev EM.axioms : Axiom := {Axioms.M (.atom 0) (.atom 1)}
instance : EM.axioms.HasM where p := 0; q := 1
abbrev EM : Logic := Hilbert EM.axioms

abbrev EC.axioms : Axiom := {Axioms.C (.atom 0) (.atom 1)}
instance : EC.axioms.HasC where p := 0; q := 1
abbrev EC : Logic := Hilbert EC.axioms

abbrev EN.axioms : Axiom := {Axioms.N}
instance : EN.axioms.HasN where
abbrev EN : Logic := Hilbert EN.axioms

abbrev EMC.axioms : Axiom := {Axioms.M (.atom 0) (.atom 1), Axioms.C (.atom 0) (.atom 1)}
instance : EMC.axioms.HasM where p := 0; q := 1
instance : EMC.axioms.HasC where p := 0; q := 1
abbrev EMC : Logic := Hilbert EMC.axioms

abbrev EMN.axioms : Axiom := {Axioms.M (.atom 0) (.atom 1), Axioms.N}
instance : EMN.axioms.HasM where p := 0; q := 1
instance : EMN.axioms.HasN where
abbrev EMN : Logic := Hilbert EMN.axioms

abbrev ECN.axioms : Axiom := {Axioms.C (.atom 0) (.atom 1), Axioms.N}
instance : ECN.axioms.HasC where p := 0; q := 1
instance : ECN.axioms.HasN where
abbrev ECN : Logic := Hilbert ECN.axioms

abbrev EMCN.axioms : Axiom := {
  Axioms.M (.atom 0) (.atom 1),
  Axioms.C (.atom 0) (.atom 1),
  Axioms.N
}
instance : EMCN.axioms.HasM where p := 0; q := 1
instance : EMCN.axioms.HasC where p := 0; q := 1
instance : EMCN.axioms.HasN where
abbrev EMCN : Logic := Hilbert EMCN.axioms

abbrev EK.axioms : Axiom := {Axioms.K (.atom 0) (.atom 1)}
instance : EK.axioms.HasK where p := 0; q := 1
abbrev EK : Logic := Hilbert EK.axioms

abbrev EMK.axioms : Axiom := {Axioms.M (.atom 0) (.atom 1), Axioms.K (.atom 0) (.atom 1)}
instance : EMK.axioms.HasM where p := 0; q := 1
instance : EMK.axioms.HasK where p := 0; q := 1
abbrev EMK : Logic := Hilbert EMK.axioms

abbrev EMCK.axioms : Axiom := {
  Axioms.M (.atom 0) (.atom 1),
  Axioms.C (.atom 0) (.atom 1),
  Axioms.K (.atom 0) (.atom 1)
}
instance : EMCK.axioms.HasM where p := 0; q := 1
instance : EMCK.axioms.HasC where p := 0; q := 1
instance : EMCK.axioms.HasK where p := 0; q := 1
abbrev EMCK : Logic := Hilbert EMCK.axioms

abbrev ET.axioms : Axiom := {Axioms.T (.atom 0)}
instance : ET.axioms.HasT where p := 0
abbrev ET : Logic := Hilbert ET.axioms

abbrev EMT.axioms : Axiom := {Axioms.M (.atom 0) (.atom 1), Axioms.T (.atom 0)}
instance : EMT.axioms.HasM where p := 0; q := 1
instance : EMT.axioms.HasT where p := 0
abbrev EMT : Logic := Hilbert EMT.axioms

abbrev ED.axioms : Axiom := {Axioms.D (.atom 0)}
instance : ED.axioms.HasD where p := 0
abbrev ED : Logic := Hilbert ED.axioms

abbrev END.axioms : Axiom := {Axioms.N, Axioms.D (.atom 0)}
instance : END.axioms.HasN where
instance : END.axioms.HasD where p := 0
abbrev END : Logic := Hilbert END.axioms

abbrev EP.axioms : Axiom := {Axioms.P}
instance : EP.axioms.HasP where
abbrev EP : Logic := Hilbert EP.axioms

abbrev EB.axioms : Axiom := {Axioms.B (.atom 0)}
instance : EB.axioms.HasB where p := 0
abbrev EB : Logic := Hilbert EB.axioms

abbrev ETB.axioms : Axiom := {Axioms.B (.atom 0), Axioms.T (.atom 0)}
instance : ETB.axioms.HasB where p := 0
instance : ETB.axioms.HasT where p := 0
abbrev ETB : Logic := Hilbert ETB.axioms

abbrev ENTB.axioms : Axiom := {Axioms.N, Axioms.B (.atom 0), Axioms.T (.atom 0)}
instance : ENTB.axioms.HasN where
instance : ENTB.axioms.HasB where p := 0
instance : ENTB.axioms.HasT where p := 0
abbrev ENTB : Logic := Hilbert ENTB.axioms

abbrev E4.axioms : Axiom := {Axioms.Four (.atom 0)}
instance : E4.axioms.HasFour where p := 0
abbrev E4 : Logic := Hilbert E4.axioms

abbrev EN4.axioms : Axiom := {Axioms.N, Axioms.Four (.atom 0)}
instance : EN4.axioms.HasN where
instance : EN4.axioms.HasFour where p := 0
abbrev EN4 : Logic := Hilbert EN4.axioms

abbrev ET4.axioms : Axiom := {Axioms.Four (.atom 0), Axioms.T (.atom 0)}
instance : ET4.axioms.HasFour where p := 0
instance : ET4.axioms.HasT where p := 0
abbrev ET4 : Logic := Hilbert ET4.axioms

abbrev ENT4.axioms : Axiom := {Axioms.N, Axioms.T (.atom 0), Axioms.Four (.atom 0)}
instance : ENT4.axioms.HasN where
instance : ENT4.axioms.HasT where p := 0
instance : ENT4.axioms.HasFour where p := 0
abbrev ENT4 : Logic := Hilbert ENT4.axioms

abbrev END4.axioms : Axiom := {Axioms.N, Axioms.D (.atom 0), Axioms.Four (.atom 0)}
instance : END4.axioms.HasN where
instance : END4.axioms.HasD where p := 0
instance : END4.axioms.HasFour where p := 0
abbrev END4 : Logic := Hilbert END4.axioms

abbrev EMT4.axioms : Axiom := {
  Axioms.M (.atom 0) (.atom 1),
  Axioms.T (.atom 0),
  Axioms.Four (.atom 0)
}
instance : EMT4.axioms.HasM where p := 0; q := 1
instance : EMT4.axioms.HasT where p := 0
instance : EMT4.axioms.HasFour where p := 0
abbrev EMT4 : Logic := Hilbert EMT4.axioms

abbrev EMNT4.axioms : Axiom := {
  Axioms.M (.atom 0) (.atom 1),
  Axioms.N,
  Axioms.T (.atom 0),
  Axioms.Four (.atom 0)
}
instance : EMNT4.axioms.HasM where p := 0; q := 1
instance : EMNT4.axioms.HasN where
instance : EMNT4.axioms.HasT where p := 0
instance : EMNT4.axioms.HasFour where p := 0
abbrev EMNT4 : Logic := Hilbert EMNT4.axioms

abbrev EMC4.axioms : Axiom := {
  Axioms.M (.atom 0) (.atom 1),
  Axioms.C (.atom 0) (.atom 1),
  Axioms.Four (.atom 0)
}
instance : EMC4.axioms.HasM where p := 0; q := 1
instance : EMC4.axioms.HasC where p := 0; q := 1
instance : EMC4.axioms.HasFour where p := 0
abbrev EMC4 : Logic := Hilbert EMC4.axioms

abbrev EMCN4.axioms : Axiom := {
  Axioms.M (.atom 0) (.atom 1),
  Axioms.C (.atom 0) (.atom 1),
  Axioms.N,
  Axioms.Four (.atom 0)
}
instance : EMCN4.axioms.HasM where p := 0; q := 1
instance : EMCN4.axioms.HasC where p := 0; q := 1
instance : EMCN4.axioms.HasN where
instance : EMCN4.axioms.HasFour where p := 0
abbrev EMCN4 : Logic := Hilbert EMCN4.axioms

abbrev E5.axioms : Axiom := {Axioms.Five (.atom 0)}
instance : E5.axioms.HasFive where p := 0
abbrev E5 : Logic := Hilbert E5.axioms

abbrev ET5.axioms : Axiom := {Axioms.T (.atom 0), Axioms.Five (.atom 0)}
instance : ET5.axioms.HasT where p := 0
instance : ET5.axioms.HasFive where p := 0
abbrev ET5 : Logic := Hilbert ET5.axioms

/-- The axiom scheme `C` is redundant over `M` and `K`. -/
theorem EMK_eq_EMCK : EMK = EMCK := by
  apply Set.Subset.antisymm;
  . apply Hilbert.subset_of_subset_axioms;
    intro φ hφ;
    rcases hφ with rfl | rfl <;> simp;
  . apply Hilbert.subset_of_provable_axioms;
    intro φ hφ;
    rcases hφ with rfl | rfl | rfl <;> simp;

/-- The axiom `N` is redundant over `T` and `B`. -/
theorem ETB_eq_ENTB : ETB = ENTB := by
  apply Set.Subset.antisymm;
  . apply Hilbert.subset_of_subset_axioms;
    intro φ hφ;
    rcases hφ with rfl | rfl <;> simp;
  . apply Hilbert.subset_of_provable_axioms;
    intro φ hφ;
    rcases hφ with rfl | rfl | rfl <;> simp;

end
