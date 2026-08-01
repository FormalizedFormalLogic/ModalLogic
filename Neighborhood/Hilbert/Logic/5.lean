module

public import Neighborhood.Hilbert.Basic

@[expose] public section

variable {α : Type u}

abbrev LogicEMCNTB : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicEMCNTB α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCNTB α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCNTB α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCNTB α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCNTB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicEMCNT4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMCNT4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCNT4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCNT4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCNT4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCNT4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMCNT5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCNT5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCNT5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCNT5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCNT5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCNT5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMCNDB : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicEMCNDB α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCNDB α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCNDB α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCNDB α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCNDB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicEMCND4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMCND4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCND4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCND4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCND4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCND4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMCND5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCND5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCND5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCND5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCND5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCND5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMCD45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCD45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCD45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCD45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCD45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMCD45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMND45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMND45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMND45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMND45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMND45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMND45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECND45 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECND45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECND45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECND45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECND45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicECND45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMCN45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCN45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCN45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCN45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCN45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMCN45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMCNB4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMCNB4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCNB4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCNB4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCNB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMCNB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMCNTD : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) }
instance : (@LogicEMCNTD α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCNTD α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCNTD α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCNTD α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCNTD α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;

abbrev LogicEMCNB5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCNB5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCNB5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCNB5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMCNB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMCNB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMCTDB : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicEMCTDB α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCTDB α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCTDB α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCTDB α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCTDB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicEMCTD4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMCTD4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCTD4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCTD4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCTD4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCTD4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMCTD5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCTD5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCTD5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCTD5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCTD5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCTD5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMCTB4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMCTB4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCTB4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCTB4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCTB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMCTB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMCTB5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCTB5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCTB5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCTB5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCTB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMCTB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMCT45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCT45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCT45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCT45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMCT45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMCT45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMCDB4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMCDB4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCDB4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCDB4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCDB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMCDB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMCDB5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCDB5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCDB5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCDB5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMCDB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMCDB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMCB45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMCB45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCB45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMCB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMCB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMNTDB : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicEMNTDB α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNTDB α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNTDB α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMNTDB α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMNTDB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicEMNTD4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMNTD4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNTD4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNTD4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMNTD4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMNTD4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMNTD5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMNTD5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNTD5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNTD5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMNTD5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMNTD5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMNTB4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMNTB4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNTB4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNTB4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMNTB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMNTB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMNTB5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMNTB5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNTB5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNTB5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMNTB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMNTB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMNT45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMNT45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNT45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNT45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMNT45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMNT45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMNDB4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMNDB4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNDB4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNDB4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMNDB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMNDB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMNDB5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMNDB5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNDB5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNDB5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMNDB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMNDB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMNB45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMNB45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNB45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMNB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMNB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMTDB4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMTDB4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMTDB4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMTDB4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMTDB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMTDB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMTDB5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMTDB5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMTDB5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMTDB5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMTDB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMTDB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMTD45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMTD45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMTD45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMTD45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMTD45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMTD45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMTB45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMTB45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMTB45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMTB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMTB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMTB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMDB45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMDB45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMDB45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMDB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMDB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEMDB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECNTDB : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicECNTDB α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNTDB α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNTDB α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECNTDB α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECNTDB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicECNTD4 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicECNTD4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNTD4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNTD4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECNTD4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECNTD4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicECNTD5 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECNTD5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNTD5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNTD5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECNTD5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECNTD5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECNTB4 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicECNTB4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNTB4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNTB4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECNTB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicECNTB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicECNTB5 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECNTB5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNTB5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNTB5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECNTB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicECNTB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECNT45 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECNT45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNT45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNT45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECNT45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicECNT45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECNDB4 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicECNDB4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNDB4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNDB4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECNDB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicECNDB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicECNDB5 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECNDB5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNDB5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNDB5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECNDB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicECNDB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECNB45 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECNB45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNB45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicECNB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicECNB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECTDB4 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicECTDB4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECTDB4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECTDB4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECTDB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicECTDB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicECTDB5 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECTDB5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECTDB5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECTDB5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECTDB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicECTDB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECTD45 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECTD45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECTD45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECTD45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECTD45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicECTD45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECTB45 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECTB45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECTB45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECTB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicECTB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicECTB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECDB45 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECDB45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECDB45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECDB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicECDB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicECDB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicENTDB4 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicENTDB4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENTDB4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicENTDB4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicENTDB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicENTDB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicENTDB5 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicENTDB5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENTDB5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicENTDB5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicENTDB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicENTDB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicENTD45 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicENTD45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENTD45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicENTD45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicENTD45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicENTD45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicENTB45 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicENTB45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENTB45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicENTB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicENTB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicENTB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicENDB45 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicENDB45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENDB45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicENDB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicENDB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicENDB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicETDB45 : Logic α := Hilbert $
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicETDB45 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicETDB45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicETDB45 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicETDB45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicETDB45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

end
