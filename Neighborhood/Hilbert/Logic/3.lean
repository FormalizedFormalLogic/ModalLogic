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

abbrev LogicECKN : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.N }
instance : (@LogicECKN α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECKN α).HasAxiomK := Hilbert.hasAxiomK_of $ by grind;
instance : (@LogicECKN α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;

abbrev LogicECKT : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.T A | (A) }
instance : (@LogicECKT α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECKT α).HasAxiomK := Hilbert.hasAxiomK_of $ by grind;
instance : (@LogicECKT α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;

abbrev LogicECKD : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.D A | (A) }
instance : (@LogicECKD α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECKD α).HasAxiomK := Hilbert.hasAxiomK_of $ by grind;
instance : (@LogicECKD α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;

abbrev LogicECKP : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.P }
instance : (@LogicECKP α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECKP α).HasAxiomK := Hilbert.hasAxiomK_of $ by grind;
instance : (@LogicECKP α).HasAxiomP := Hilbert.hasAxiomP_of $ by grind;

abbrev LogicECKB : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.B A | (A) }
instance : (@LogicECKB α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECKB α).HasAxiomK := Hilbert.hasAxiomK_of $ by grind;
instance : (@LogicECKB α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;

abbrev LogicECK4 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.Four A | (A) }
instance : (@LogicECK4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECK4 α).HasAxiomK := Hilbert.hasAxiomK_of $ by grind;
instance : (@LogicECK4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;

abbrev LogicECK5 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECK5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECK5 α).HasAxiomK := Hilbert.hasAxiomK_of $ by grind;
instance : (@LogicECK5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicEKNT : Logic α := Hilbert $
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.T A | (A) }
instance : (@LogicEKNT α).HasAxiomK := Hilbert.hasAxiomK_of $ by grind;
instance : (@LogicEKNT α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicEKNT α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;

abbrev LogicEKND : Logic α := Hilbert $
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.D A | (A) }
instance : (@LogicEKND α).HasAxiomK := Hilbert.hasAxiomK_of $ by grind;
instance : (@LogicEKND α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicEKND α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;

abbrev LogicEKNP : Logic α := Hilbert $
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.P }
instance : (@LogicEKNP α).HasAxiomK := Hilbert.hasAxiomK_of $ by grind;
instance : (@LogicEKNP α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicEKNP α).HasAxiomP := Hilbert.hasAxiomP_of $ by grind;

abbrev LogicEKNB : Logic α := Hilbert $
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.B A | (A) }
instance : (@LogicEKNB α).HasAxiomK := Hilbert.hasAxiomK_of $ by grind;
instance : (@LogicEKNB α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicEKNB α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;

abbrev LogicEKN4 : Logic α := Hilbert $
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.Four A | (A) }
instance : (@LogicEKN4 α).HasAxiomK := Hilbert.hasAxiomK_of $ by grind;
instance : (@LogicEKN4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicEKN4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;

abbrev LogicEKN5 : Logic α := Hilbert $
  { Axioms.K A B | (A) (B) } ∪
  { Axioms.N } ∪
  { Axioms.Five A | (A) }
instance : (@LogicEKN5 α).HasAxiomK := Hilbert.hasAxiomK_of $ by grind;
instance : (@LogicEKN5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicEKN5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicECTD : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) }
instance : (@LogicECTD α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECTD α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;
instance : (@LogicECTD α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;

abbrev LogicECTP : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.P }
instance : (@LogicECTP α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECTP α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;
instance : (@LogicECTP α).HasAxiomP := Hilbert.hasAxiomP_of $ by grind;

abbrev LogicECDP : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.P }
instance : (@LogicECDP α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECDP α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;
instance : (@LogicECDP α).HasAxiomP := Hilbert.hasAxiomP_of $ by grind;

abbrev LogicECPB : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.P } ∪
  { Axioms.B A | (A) }
instance : (@LogicECPB α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECPB α).HasAxiomP := Hilbert.hasAxiomP_of $ by grind;
instance : (@LogicECPB α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;

abbrev LogicECP4 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.P } ∪
  { Axioms.Four A | (A) }
instance : (@LogicECP4 α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECP4 α).HasAxiomP := Hilbert.hasAxiomP_of $ by grind;
instance : (@LogicECP4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;

abbrev LogicECP5 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.P } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECP5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECP5 α).HasAxiomP := Hilbert.hasAxiomP_of $ by grind;
instance : (@LogicECP5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicECB5 : Logic α := Hilbert $
  { Axioms.C A B | (A) (B) } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicECB5 α).HasAxiomC := Hilbert.hasAxiomC_of $ by grind;
instance : (@LogicECB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;
instance : (@LogicECB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicENTD : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.D A | (A) }
instance : (@LogicENTD α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicENTD α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;
instance : (@LogicENTD α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;

abbrev LogicENTP : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.T A | (A) } ∪
  { Axioms.P }
instance : (@LogicENTP α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicENTP α).HasAxiomT := Hilbert.hasAxiomT_of $ by grind;
instance : (@LogicENTP α).HasAxiomP := Hilbert.hasAxiomP_of $ by grind;

abbrev LogicENDP : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.D A | (A) } ∪
  { Axioms.P }
instance : (@LogicENDP α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicENDP α).HasAxiomD := Hilbert.hasAxiomD_of $ by grind;
instance : (@LogicENDP α).HasAxiomP := Hilbert.hasAxiomP_of $ by grind;

abbrev LogicENPB : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.P } ∪
  { Axioms.B A | (A) }
instance : (@LogicENPB α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicENPB α).HasAxiomP := Hilbert.hasAxiomP_of $ by grind;
instance : (@LogicENPB α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;

abbrev LogicENP4 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.P } ∪
  { Axioms.Four A | (A) }
instance : (@LogicENP4 α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicENP4 α).HasAxiomP := Hilbert.hasAxiomP_of $ by grind;
instance : (@LogicENP4 α).HasAxiomFour := Hilbert.hasAxiomFour_of $ by grind;

abbrev LogicENP5 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.P } ∪
  { Axioms.Five A | (A) }
instance : (@LogicENP5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicENP5 α).HasAxiomP := Hilbert.hasAxiomP_of $ by grind;
instance : (@LogicENP5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

abbrev LogicENB5 : Logic α := Hilbert $
  { Axioms.N } ∪
  { Axioms.B A | (A) } ∪
  { Axioms.Five A | (A) }
instance : (@LogicENB5 α).HasAxiomN := Hilbert.hasAxiomN_of $ by grind;
instance : (@LogicENB5 α).HasAxiomB := Hilbert.hasAxiomB_of $ by grind;
instance : (@LogicENB5 α).HasAxiomFive := Hilbert.hasAxiomFive_of $ by grind;

end
