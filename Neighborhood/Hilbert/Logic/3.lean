module

public import Neighborhood.Hilbert.Basic

@[expose] public section

variable {α : Type u}

abbrev LogicEMCN : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N }
instance : (@LogicEMCN α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCN α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCN α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;

abbrev LogicEMCK : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.K A B | (A) (B) }
instance : (@LogicEMCK α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCK α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCK α).HasAxiomK := Hilbert.hasAxiomK_of $ by simp;

abbrev LogicEMNP : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.P }
instance : (@LogicEMNP α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNP α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNP α).HasAxiomP := Hilbert.hasAxiomP_of $ by simp;

abbrev LogicECNP : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.P }
instance : (@LogicECNP α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNP α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNP α).HasAxiomP := Hilbert.hasAxiomP_of $ by simp;

abbrev LogicEMCP : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.P }
instance : (@LogicEMCP α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCP α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCP α).HasAxiomP := Hilbert.hasAxiomP_of $ by simp;

abbrev LogicENTB : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicENTB α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENTB α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicENTB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicEMN4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMN4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMN4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMN4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicENT4 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicENT4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENT4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicENT4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEND4 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEND4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEND4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEND4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMT4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMT4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMT4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMT4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMC4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMC4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMC4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMC4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMCT : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) }
instance : (@LogicEMCT α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCT α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCT α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;

abbrev LogicEMNT : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) }
instance : (@LogicEMNT α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNT α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNT α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;

abbrev LogicECNT : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) }
instance : (@LogicECNT α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNT α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNT α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;

abbrev LogicEMCD : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.D A | (A) }
instance : (@LogicEMCD α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCD α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCD α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;

abbrev LogicEMND : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) }
instance : (@LogicEMND α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMND α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMND α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;

abbrev LogicECND : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) }
instance : (@LogicECND α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECND α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECND α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;

abbrev LogicEMCB : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.B A | (A) }
instance : (@LogicEMCB α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMCB α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMCB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicEMNB : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.B A | (A) }
instance : (@LogicEMNB α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNB α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicECNB : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.B A | (A) }
instance : (@LogicECNB α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNB α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicECN4 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.Four A | (A) }
instance : (@LogicECN4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECN4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECN4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMC5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMC5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMC5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEMC5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMN5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMN5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMN5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMN5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECN5 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECN5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECN5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECN5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMTB : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicEMTB α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMTB α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMTB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicECTB : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicECTB α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECTB α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECTB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicECT4 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicECT4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECT4 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECT4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMT5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMT5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMT5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMT5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECT5 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECT5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECT5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECT5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicENT5 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicENT5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENT5 α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicENT5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMDB : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicEMDB α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMDB α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMDB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicECDB : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicECDB α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECDB α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECDB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicENDB : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.B A | (A) }
instance : (@LogicENDB α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENDB α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicENDB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicEMD4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMD4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMD4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMD4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicECD4 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicECD4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECD4 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECD4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMD5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMD5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMD5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMD5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECD5 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECD5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECD5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECD5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEND5 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEND5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEND5 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEND5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicED45 : Logic α := Hilbert $
  { Axioms.D A | (A) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicED45 α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicED45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicED45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEM45 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEM45 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEM45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEM45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEC45 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEC45 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicEC45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEC45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEN45 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.Four A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEN45 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEN45 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;
instance : (@LogicEN45 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMB4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMB4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicECB4 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicECB4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicECB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicENB4 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicENB4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENB4 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicENB4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMNK : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.K A B | (A) (B) }
instance : (@LogicEMNK α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMNK α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicEMNK α).HasAxiomK := Hilbert.hasAxiomK_of $ by simp;

abbrev LogicEMKT : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.T A | (A) }
instance : (@LogicEMKT α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMKT α).HasAxiomK := Hilbert.hasAxiomK_of $ by simp;
instance : (@LogicEMKT α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;

abbrev LogicEMKB : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.B A | (A) }
instance : (@LogicEMKB α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMKB α).HasAxiomK := Hilbert.hasAxiomK_of $ by simp;
instance : (@LogicEMKB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicEMKD : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.D A | (A) }
instance : (@LogicEMKD α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMKD α).HasAxiomK := Hilbert.hasAxiomK_of $ by simp;
instance : (@LogicEMKD α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;

abbrev LogicEMKP : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.P }
instance : (@LogicEMKP α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMKP α).HasAxiomK := Hilbert.hasAxiomK_of $ by simp;
instance : (@LogicEMKP α).HasAxiomP := Hilbert.hasAxiomP_of $ by simp;

abbrev LogicEMK4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMK4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMK4 α).HasAxiomK := Hilbert.hasAxiomK_of $ by simp;
instance : (@LogicEMK4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMK5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMK5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMK5 α).HasAxiomK := Hilbert.hasAxiomK_of $ by simp;
instance : (@LogicEMK5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMTD : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) }
instance : (@LogicEMTD α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMTD α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMTD α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;

abbrev LogicEMTP : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.P }
instance : (@LogicEMTP α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMTP α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicEMTP α).HasAxiomP := Hilbert.hasAxiomP_of $ by simp;

abbrev LogicEMPB : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.P } ∪
  { Axioms.B A | (A) }
instance : (@LogicEMPB α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMPB α).HasAxiomP := Hilbert.hasAxiomP_of $ by simp;
instance : (@LogicEMPB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicEMB5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMB5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicEMB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicEMDP : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.P }
instance : (@LogicEMDP α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMDP α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicEMDP α).HasAxiomP := Hilbert.hasAxiomP_of $ by simp;

abbrev LogicEMP4 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.P } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEMP4 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMP4 α).HasAxiomP := Hilbert.hasAxiomP_of $ by simp;
instance : (@LogicEMP4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicEMP5 : Logic α := Hilbert $
  { Axioms.M A B | (A) (B) } ∪
  { Axioms.P } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEMP5 α).HasAxiomM := Hilbert.hasAxiomM_of $ by simp;
instance : (@LogicEMP5 α).HasAxiomP := Hilbert.hasAxiomP_of $ by simp;
instance : (@LogicEMP5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECNK : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.K A B | (A) (B) }
instance : (@LogicECNK α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECNK α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicECNK α).HasAxiomK := Hilbert.hasAxiomK_of $ by simp;

abbrev LogicECKT : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.T A | (A) }
instance : (@LogicECKT α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECKT α).HasAxiomK := Hilbert.hasAxiomK_of $ by simp;
instance : (@LogicECKT α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;

abbrev LogicECKD : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.D A | (A) }
instance : (@LogicECKD α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECKD α).HasAxiomK := Hilbert.hasAxiomK_of $ by simp;
instance : (@LogicECKD α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;

abbrev LogicECKP : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.P }
instance : (@LogicECKP α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECKP α).HasAxiomK := Hilbert.hasAxiomK_of $ by simp;
instance : (@LogicECKP α).HasAxiomP := Hilbert.hasAxiomP_of $ by simp;

abbrev LogicECKB : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.B A | (A) }
instance : (@LogicECKB α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECKB α).HasAxiomK := Hilbert.hasAxiomK_of $ by simp;
instance : (@LogicECKB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicECK4 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicECK4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECK4 α).HasAxiomK := Hilbert.hasAxiomK_of $ by simp;
instance : (@LogicECK4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicECK5 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECK5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECK5 α).HasAxiomK := Hilbert.hasAxiomK_of $ by simp;
instance : (@LogicECK5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicENKT : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.T A | (A) }
instance : (@LogicENKT α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENKT α).HasAxiomK := Hilbert.hasAxiomK_of $ by simp;
instance : (@LogicENKT α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;

abbrev LogicENKD : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.D A | (A) }
instance : (@LogicENKD α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENKD α).HasAxiomK := Hilbert.hasAxiomK_of $ by simp;
instance : (@LogicENKD α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;

abbrev LogicENKP : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.P }
instance : (@LogicENKP α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENKP α).HasAxiomK := Hilbert.hasAxiomK_of $ by simp;
instance : (@LogicENKP α).HasAxiomP := Hilbert.hasAxiomP_of $ by simp;

abbrev LogicENKB : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.B A | (A) }
instance : (@LogicENKB α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENKB α).HasAxiomK := Hilbert.hasAxiomK_of $ by simp;
instance : (@LogicENKB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicENK4 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicENK4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENK4 α).HasAxiomK := Hilbert.hasAxiomK_of $ by simp;
instance : (@LogicENK4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicENK5 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicENK5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENK5 α).HasAxiomK := Hilbert.hasAxiomK_of $ by simp;
instance : (@LogicENK5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECTD : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) }
instance : (@LogicECTD α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECTD α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECTD α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;

abbrev LogicECTP : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.P }
instance : (@LogicECTP α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECTP α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicECTP α).HasAxiomP := Hilbert.hasAxiomP_of $ by simp;

abbrev LogicECDP : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.P }
instance : (@LogicECDP α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECDP α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicECDP α).HasAxiomP := Hilbert.hasAxiomP_of $ by simp;

abbrev LogicECPB : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.P } ∪
  { Axioms.B A | (A) }
instance : (@LogicECPB α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECPB α).HasAxiomP := Hilbert.hasAxiomP_of $ by simp;
instance : (@LogicECPB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicECP4 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.P } ∪
  { Axioms.Four A | (A) }
instance : (@LogicECP4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECP4 α).HasAxiomP := Hilbert.hasAxiomP_of $ by simp;
instance : (@LogicECP4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicECP5 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.P } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECP5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECP5 α).HasAxiomP := Hilbert.hasAxiomP_of $ by simp;
instance : (@LogicECP5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicECB5 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECB5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by simp;
instance : (@LogicECB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicECB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicENTD : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) }
instance : (@LogicENTD α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENTD α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicENTD α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;

abbrev LogicENTP : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.P }
instance : (@LogicENTP α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENTP α).HasAxiomT := Hilbert.hasAxiomT_of $ by simp;
instance : (@LogicENTP α).HasAxiomP := Hilbert.hasAxiomP_of $ by simp;

abbrev LogicENDP : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.P }
instance : (@LogicENDP α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENDP α).HasAxiomD := Hilbert.hasAxiomD_of $ by simp;
instance : (@LogicENDP α).HasAxiomP := Hilbert.hasAxiomP_of $ by simp;

abbrev LogicENPB : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.P } ∪
  { Axioms.B A | (A) }
instance : (@LogicENPB α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENPB α).HasAxiomP := Hilbert.hasAxiomP_of $ by simp;
instance : (@LogicENPB α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;

abbrev LogicENP4 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.P } ∪
  { Axioms.Four A | (A) }
instance : (@LogicENP4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENP4 α).HasAxiomP := Hilbert.hasAxiomP_of $ by simp;
instance : (@LogicENP4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by simp;

abbrev LogicENP5 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.P } ∪
  { Axioms.Five A | (A) }
instance : (@LogicENP5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENP5 α).HasAxiomP := Hilbert.hasAxiomP_of $ by simp;
instance : (@LogicENP5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

abbrev LogicENB5 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicENB5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by simp;
instance : (@LogicENB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by simp;
instance : (@LogicENB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by simp;

end
