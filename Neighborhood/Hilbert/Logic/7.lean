module

public import Neighborhood.Hilbert.Basic

@[expose] public section

variable {α : Type u}

abbrev LogicEMCNTDB4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMCNTDB4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCNTDB4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCNTDB4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCNTDB4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCNTDB4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCNTDB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMCNTDB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMCNTDB5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCNTDB5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCNTDB5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCNTDB5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCNTDB5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCNTDB5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCNTDB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMCNTDB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMCNTD45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCNTD45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCNTD45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCNTD45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCNTD45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCNTD45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCNTD45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMCNTD45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMCNTB45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCNTB45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCNTB45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCNTB45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCNTB45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCNTB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMCNTB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMCNTB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMCNDB45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCNDB45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCNDB45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCNDB45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCNDB45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCNDB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMCNDB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMCNDB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMCTDB45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCTDB45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCTDB45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCTDB45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCTDB45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCTDB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMCTDB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMCTDB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMNTDB45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMNTDB45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNTDB45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNTDB45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMNTDB45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMNTDB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMNTDB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMNTDB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECNTDB45 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECNTDB45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNTDB45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNTDB45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECNTDB45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECNTDB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicECNTDB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicECNTDB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

end
