module

public import Neighborhood.Hilbert.Basic

@[expose] public section

variable {α : Type u}

abbrev LogicEMCNTDB45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCNTDB45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCNTDB45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCNTDB45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCNTDB45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCNTDB45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCNTDB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMCNTDB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMCNTDB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

end
