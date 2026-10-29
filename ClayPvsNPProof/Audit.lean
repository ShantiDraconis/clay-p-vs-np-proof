import ClayPvsNPProof.SAT

/-!
# Auditoria de axiomas

Um `#guard_msgs` por declaração pública nova (teoremas, definições, tipos; os eliminadores gerados
automaticamente — `casesOn`, `recOn`, `noConfusion`, `ctorElim`, `elim`, `decEq` — ficam de fora), com a
saída REAL de `#print axioms`. Se aparecer qualquer outro axioma (inclusive `sorryAx`), a compilação falha.

Só aparecem `propext`, `Classical.choice` e `Quot.sound`. `Classical.choice` vem do Mathlib
(`Turing.TM2ComputableInPolyTime`, `Polynomial ℕ`, `Finset`) e das escolhas clássicas nas provas de tempo.
-/

/-! ## `ClayPvsNPProof.ClassP` (3 declarações) -/

/-- info: 'ClayPvsNPProof.polyTimeComputable_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.polyTimeComputable_iff

/-- info: 'ClayPvsNPProof.inP_iff_emP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.inP_iff_emP

/-- info: 'ClayPvsNPProof.P_eq_classeP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.P_eq_classeP

/-! ## `ClayPvsNPProof.ClassNP` (8 declarações) -/

/-- info: 'ClayPvsNPProof.verificador_ATK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.verificador_ATK

/-- info: 'ClayPvsNPProof.verificador_fixado' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.verificador_fixado

/-- info: 'ClayPvsNPProof.inNP_iff_emNP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.inNP_iff_emNP

/-- info: 'ClayPvsNPProof.NP_eq_classeNP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.NP_eq_classeNP

/-- info: 'ClayPvsNPProof.P_subset_NP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.P_subset_NP

/-- info: 'ClayPvsNPProof.P_eq_NP_iff_classes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.P_eq_NP_iff_classes

/-- info: 'ClayPvsNPProof.not_P_eq_NP_iff_PneNP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.not_P_eq_NP_iff_PneNP

/-- info: 'ClayPvsNPProof.P_eq_NP_iff_NP_subset_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.P_eq_NP_iff_NP_subset_P

/-! ## `ClayPvsNPProof.SAT` (14 declarações) -/

/-- info: 'ClayPvsNPProof.SAT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.SAT

/-- info: 'ClayPvsNPProof.SAT_eq_ATK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.SAT_eq_ATK

/-- info: 'ClayPvsNPProof.nil_mem_SAT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.nil_mem_SAT

/-- info: 'ClayPvsNPProof.x0_mem_SAT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.x0_mem_SAT

/-- info: 'ClayPvsNPProof.true_true_not_mem_SAT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.true_true_not_mem_SAT

/-- info: 'ClayPvsNPProof.KarpRed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.KarpRed

/-- info: 'ClayPvsNPProof.karpRed_iff_Red' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.karpRed_iff_Red

/-- info: 'ClayPvsNPProof.P_closed_KarpRed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.P_closed_KarpRed

/-- info: 'ClayPvsNPProof.SAT_mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.SAT_mem_NP

/-- info: 'ClayPvsNPProof.SAT_NP_hard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.SAT_NP_hard

/-- info: 'ClayPvsNPProof.P_eq_NP_iff_SAT_mem_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.P_eq_NP_iff_SAT_mem_P

/-- info: 'ClayPvsNPProof.Gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Gap

/-- info: 'ClayPvsNPProof.not_P_eq_NP_iff_Gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.not_P_eq_NP_iff_Gap

/-- info: 'ClayPvsNPProof.Target_iff_not_Gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Target_iff_not_Gap

/-! ## `ClayPvsNPProof.Transcoders` (38 declarações) -/

/-- info: 'ClayPvsNPProof.Transcoders.passoCopia' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.passoCopia

/-- info: 'ClayPvsNPProof.Transcoders.prog' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.prog

/-- info: 'ClayPvsNPProof.Transcoders.tm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.tm

/-- info: 'ClayPvsNPProof.Transcoders.stepT' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.stepT

/-- info: 'ClayPvsNPProof.Transcoders.one' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.one

/-- info: 'ClayPvsNPProof.Transcoders.copia_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.copia_cons

/-- info: 'ClayPvsNPProof.Transcoders.copia_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.copia_nil

/-- info: 'ClayPvsNPProof.Transcoders.saida_cons'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.saida_cons'

/-- info: 'ClayPvsNPProof.Transcoders.saida_nil'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.saida_nil'

/-- info: 'ClayPvsNPProof.Transcoders.run_copia' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.run_copia

/-- info: 'ClayPvsNPProof.Transcoders.run_saida'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.run_saida'

/-- info: 'ClayPvsNPProof.Transcoders.initList_tm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.initList_tm

/-- info: 'ClayPvsNPProof.Transcoders.haltList_tm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.haltList_tm

/-- info: 'ClayPvsNPProof.Transcoders.computavel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.computavel

/-- info: 'ClayPvsNPProof.Transcoders.passoA' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.passoA

/-- info: 'ClayPvsNPProof.Transcoders.tA' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.tA

/-- info: 'ClayPvsNPProof.Transcoders.kA' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.kA

/-- info: 'ClayPvsNPProof.Transcoders.tA_pair' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.tA_pair

/-- info: 'ClayPvsNPProof.Transcoders.kA_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.kA_le

/-- info: 'ClayPvsNPProof.Transcoders.tA_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.tA_length

/-- info: 'ClayPvsNPProof.Transcoders.stepA_tt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.stepA_tt

/-- info: 'ClayPvsNPProof.Transcoders.stepA_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.stepA_t

/-- info: 'ClayPvsNPProof.Transcoders.stepA_f' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.stepA_f

/-- info: 'ClayPvsNPProof.Transcoders.stepA_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.stepA_nil

/-- info: 'ClayPvsNPProof.Transcoders.runA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.runA

/-- info: 'ClayPvsNPProof.Transcoders.tAComputable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.tAComputable

/-- info: 'ClayPvsNPProof.Transcoders.passoP' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.passoP

/-- info: 'ClayPvsNPProof.Transcoders.tP' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.tP

/-- info: 'ClayPvsNPProof.Transcoders.kP' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.kP

/-- info: 'ClayPvsNPProof.Transcoders.tP_par' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.tP_par

/-- info: 'ClayPvsNPProof.Transcoders.kP_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.kP_le

/-- info: 'ClayPvsNPProof.Transcoders.tP_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.tP_length

/-- info: 'ClayPvsNPProof.Transcoders.stepP_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.stepP_eq

/-- info: 'ClayPvsNPProof.Transcoders.stepP_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.stepP_ne

/-- info: 'ClayPvsNPProof.Transcoders.stepP_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.stepP_one

/-- info: 'ClayPvsNPProof.Transcoders.stepP_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.stepP_nil

/-- info: 'ClayPvsNPProof.Transcoders.runP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.runP

/-- info: 'ClayPvsNPProof.Transcoders.tPComputable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.Transcoders.tPComputable

/-! ## `ClayPvsNPProof.ATK.Conditional.PvsNP` (12 declarações) -/

/-- info: 'ClayPvsNPProof.ATK.Conditional.PvsNP.ComplexityModel' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Conditional.PvsNP.ComplexityModel

/-- info: 'ClayPvsNPProof.ATK.Conditional.PvsNP.ComplexityModel.Lang' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Conditional.PvsNP.ComplexityModel.Lang

/-- info: 'ClayPvsNPProof.ATK.Conditional.PvsNP.ComplexityModel.P' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Conditional.PvsNP.ComplexityModel.P

/-- info: 'ClayPvsNPProof.ATK.Conditional.PvsNP.ComplexityModel.NP' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Conditional.PvsNP.ComplexityModel.NP

/-- info: 'ClayPvsNPProof.ATK.Conditional.PvsNP.ComplexityModel.Red' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Conditional.PvsNP.ComplexityModel.Red

/-- info: 'ClayPvsNPProof.ATK.Conditional.PvsNP.ComplexityModel.P_subset_NP' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Conditional.PvsNP.ComplexityModel.P_subset_NP

/-- info: 'ClayPvsNPProof.ATK.Conditional.PvsNP.ComplexityModel.P_closed_under_red' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Conditional.PvsNP.ComplexityModel.P_closed_under_red

/-- info: 'ClayPvsNPProof.ATK.Conditional.PvsNP.CookLevin' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Conditional.PvsNP.CookLevin

/-- info: 'ClayPvsNPProof.ATK.Conditional.PvsNP.SATNotInP' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Conditional.PvsNP.SATNotInP

/-- info: 'ClayPvsNPProof.ATK.Conditional.PvsNP.PneNP' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Conditional.PvsNP.PneNP

/-- info: 'ClayPvsNPProof.ATK.Conditional.PvsNP.pvsnp_conditional' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Conditional.PvsNP.pvsnp_conditional

/-- info: 'ClayPvsNPProof.ATK.Conditional.PvsNP.pneNP_iff_sat_not_in_P' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Conditional.PvsNP.pneNP_iff_sat_not_in_P

/-! ## `ClayPvsNPProof.ATK.LigacaoPNP` (24 declarações) -/

/-- info: 'ClayPvsNPProof.ATK.LigacaoPNP.Palavra' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.LigacaoPNP.Palavra

/-- info: 'ClayPvsNPProof.ATK.LigacaoPNP.Linguagem' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.LigacaoPNP.Linguagem

/-- info: 'ClayPvsNPProof.ATK.LigacaoPNP.cod' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.LigacaoPNP.cod

/-- info: 'ClayPvsNPProof.ATK.LigacaoPNP.EmP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.LigacaoPNP.EmP

/-- info: 'ClayPvsNPProof.ATK.LigacaoPNP.par' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.LigacaoPNP.par

/-- info: 'ClayPvsNPProof.ATK.LigacaoPNP.EmNP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.LigacaoPNP.EmNP

/-- info: 'ClayPvsNPProof.ATK.LigacaoPNP.classeP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.LigacaoPNP.classeP

/-- info: 'ClayPvsNPProof.ATK.LigacaoPNP.classeNP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.LigacaoPNP.classeNP

/-- info: 'ClayPvsNPProof.ATK.LigacaoPNP.PneNP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.LigacaoPNP.PneNP

/-- info: 'ClayPvsNPProof.ATK.LigacaoPNP.par_injective_aux' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.LigacaoPNP.par_injective_aux

/-- info: 'ClayPvsNPProof.ATK.LigacaoPNP.par_injective' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.LigacaoPNP.par_injective

/-- info: 'ClayPvsNPProof.ATK.LigacaoPNP.apagaEscreve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.LigacaoPNP.apagaEscreve

/-- info: 'ClayPvsNPProof.ATK.LigacaoPNP.cfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.LigacaoPNP.cfg

/-- info: 'ClayPvsNPProof.ATK.LigacaoPNP.update_unit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.LigacaoPNP.update_unit

/-- info: 'ClayPvsNPProof.ATK.LigacaoPNP.step_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.LigacaoPNP.step_cons

/-- info: 'ClayPvsNPProof.ATK.LigacaoPNP.step_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.LigacaoPNP.step_nil

/-- info: 'ClayPvsNPProof.ATK.LigacaoPNP.iterate_apaga' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.LigacaoPNP.iterate_apaga

/-- info: 'ClayPvsNPProof.ATK.LigacaoPNP.initList_apaga' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.LigacaoPNP.initList_apaga

/-- info: 'ClayPvsNPProof.ATK.LigacaoPNP.haltList_apaga' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.LigacaoPNP.haltList_apaga

/-- info: 'ClayPvsNPProof.ATK.LigacaoPNP.constComputavel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.LigacaoPNP.constComputavel

/-- info: 'ClayPvsNPProof.ATK.LigacaoPNP.vazio_em_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.LigacaoPNP.vazio_em_P

/-- info: 'ClayPvsNPProof.ATK.LigacaoPNP.univ_em_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.LigacaoPNP.univ_em_P

/-- info: 'ClayPvsNPProof.ATK.LigacaoPNP.vazio_em_NP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.LigacaoPNP.vazio_em_NP

/-- info: 'ClayPvsNPProof.ATK.LigacaoPNP.univ_em_NP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.LigacaoPNP.univ_em_NP

/-! ## `ClayPvsNPProof.ATK.ComposicaoTM2` (65 declarações) -/

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.iterate_none' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.iterate_none

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.iterate_sim' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.iterate_sim

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.Kc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.Kc

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.Γc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.Γc

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.Λc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.Λc

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.σc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.σc

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.Stc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.Stc

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.t₁' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.t₁

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.t₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.t₂

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.aux

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.liftA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.liftA

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.liftB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.liftB

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.transf₁' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.transf₁

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.transf₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.transf₂

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.progc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.progc

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.compTM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.compTM

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.Cfgc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.Cfgc

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.stkA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.stkA

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.labA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.labA

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.cfgA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.cfgA

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.update_stkA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.update_stkA

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.stepAux_liftA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.stepAux_liftA

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.step_cfgA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.step_cfgA

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.run_fase1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.run_fase1

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.stkT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.stkT

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.ne₁' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.ne₁

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.ne₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.ne₂

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.ne₃' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.ne₃

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.stkT_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.stkT_inl

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.stkT_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.stkT_aux

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.stkT_in₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.stkT_in₂

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.upd_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.upd_inl

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.upd_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.upd_aux

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.upd_in₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.upd_in₂

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.cfgT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.cfgT

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.transf₁_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.transf₁_cons

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.transf₁_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.transf₁_nil

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.run_transf₁' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.run_transf₁

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.transf₂_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.transf₂_cons

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.transf₂_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.transf₂_nil

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.run_transf₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.run_transf₂

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.stkB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.stkB

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.cfgB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.cfgB

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.update_stkB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.update_stkB

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.stepAux_liftB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.stepAux_liftB

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.step_cfgB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.step_cfgB

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.run_fase2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.run_fase2

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.initList_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.initList_comp

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.haltList_fase1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.haltList_fase1

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.initList_fase2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.initList_fase2

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.haltList_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.haltList_comp

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.run_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.run_comp

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.pushes' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.pushes

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.tam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.tam

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.tam_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.tam_update

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.tam_stepAux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.tam_stepAux

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.pushMax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.pushMax

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.tam_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.tam_step

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.tam_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.tam_iterate

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.tam_initList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.tam_initList

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.tam_haltList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.tam_haltList

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.saida_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.saida_le

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.eval_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.eval_mono

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.cotaSaida' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.cotaSaida

/-- info: 'ClayPvsNPProof.ATK.ComposicaoTM2.comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ComposicaoTM2.comp

/-! ## `ClayPvsNPProof.ATK.ModeloPNP` (54 declarações) -/

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.dec' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.dec

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.dec_par' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.dec_par

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.dec_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.dec_length_le

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.pil' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.pil

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.pil_false' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.pil_false

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.pil_true' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.pil_true

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.upd_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.upd_false

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.upd_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.upd_true

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.σD' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.σD

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.StD' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.StD

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.passoPar' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.passoPar

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.passoLimpa' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.passoLimpa

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.passoSaida' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.passoSaida

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.progD' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.progD

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.decTM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.decTM

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.CfgD' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.CfgD

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.cfgD' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.cfgD

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.stepD' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.stepD

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.par_igual' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.par_igual

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.par_dif' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.par_dif

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.par_um' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.par_um

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.par_vazio' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.par_vazio

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.limpa_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.limpa_cons

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.limpa_vazio' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.limpa_vazio

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.saida_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.saida_cons

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.saida_vazio' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.saida_vazio

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.iter_one_step' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.iter_one_step

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.run_limpa' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.run_limpa

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.run_saida' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.run_saida

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.kPar' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.kPar

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.kPar_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.kPar_le

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.run_par' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.run_par

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.initList_dec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.initList_dec

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.haltList_dec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.haltList_dec

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.decComputavel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.decComputavel

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.P_sub_NP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.P_sub_NP

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.Red' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.Red

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.P_fechada_red' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.P_fechada_red

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.red_refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.red_refl

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.red_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.red_trans

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.Literal' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.Literal

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.Clausula' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.Clausula

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.CNF' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.CNF

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.Satisfaz' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.Satisfaz

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.Satisfativel' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.Satisfativel

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.simb' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.simb

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.codLiteral' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.codLiteral

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.codClausula' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.codClausula

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.codCNF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.codCNF

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.SAT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.SAT

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.sat_vazia' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.sat_vazia

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.clausula_vazia_insat' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.clausula_vazia_insat

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.modeloPNP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.modeloPNP

/-- info: 'ClayPvsNPProof.ATK.ModeloPNP.fiel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.ModeloPNP.fiel

/-! ## `ClayPvsNPProof.ATK.SATemNP` (132 declarações) -/

/-- info: 'ClayPvsNPProof.ATK.SATemNP.deBits' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.deBits

/-- info: 'ClayPvsNPProof.ATK.SATemNP.Canonica' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.Canonica

/-- info: 'ClayPvsNPProof.ATK.SATemNP.deBits_bits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.deBits_bits

/-- info: 'ClayPvsNPProof.ATK.SATemNP.canonica_bits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.canonica_bits

/-- info: 'ClayPvsNPProof.ATK.SATemNP.deBits_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.deBits_ne_zero

/-- info: 'ClayPvsNPProof.ATK.SATemNP.bits_deBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.bits_deBits

/-- info: 'ClayPvsNPProof.ATK.SATemNP.Entrada' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.Entrada

/-- info: 'ClayPvsNPProof.ATK.SATemNP.codEntrada' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.codEntrada

/-- info: 'ClayPvsNPProof.ATK.SATemNP.codEntradas' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.codEntradas

/-- info: 'ClayPvsNPProof.ATK.SATemNP.MF' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.MF

/-- info: 'ClayPvsNPProof.ATK.SATemNP.ftr' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.ftr

/-- info: 'ClayPvsNPProof.ATK.SATemNP.filt' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.filt

/-- info: 'ClayPvsNPProof.ATK.SATemNP.filts' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.filts

/-- info: 'ClayPvsNPProof.ATK.SATemNP.filtE' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.filtE

/-- info: 'ClayPvsNPProof.ATK.SATemNP.filtsE' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.filtsE

/-- info: 'ClayPvsNPProof.ATK.SATemNP.ftr_ec' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.ftr_ec

/-- info: 'ClayPvsNPProof.ATK.SATemNP.ftr_es' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.ftr_es

/-- info: 'ClayPvsNPProof.ATK.SATemNP.ftr_cod' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.ftr_cod

/-- info: 'ClayPvsNPProof.ATK.SATemNP.filt_cod' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.filt_cod

/-- info: 'ClayPvsNPProof.ATK.SATemNP.filts_cod' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.filts_cod

/-- info: 'ClayPvsNPProof.ATK.SATemNP.mem_filtE' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.mem_filtE

/-- info: 'ClayPvsNPProof.ATK.SATemNP.mem_filtsE' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.mem_filtsE

/-- info: 'ClayPvsNPProof.ATK.SATemNP.ML' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.ML

/-- info: 'ClayPvsNPProof.ATK.SATemNP.lk' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.lk

/-- info: 'ClayPvsNPProof.ATK.SATemNP.lookupE' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.lookupE

/-- info: 'ClayPvsNPProof.ATK.SATemNP.lk_ls' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.lk_ls

/-- info: 'ClayPvsNPProof.ATK.SATemNP.lk_cod' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.lk_cod

/-- info: 'ClayPvsNPProof.ATK.SATemNP.lookupE_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.lookupE_eq

/-- info: 'ClayPvsNPProof.ATK.SATemNP.val' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.val

/-- info: 'ClayPvsNPProof.ATK.SATemNP.Md' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.Md

/-- info: 'ClayPvsNPProof.ATK.SATemNP.acc' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.acc

/-- info: 'ClayPvsNPProof.ATK.SATemNP.getLast?_cons_or' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.getLast?_cons_or

/-- info: 'ClayPvsNPProof.ATK.SATemNP.acc_lit' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.acc_lit

/-- info: 'ClayPvsNPProof.ATK.SATemNP.bom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.bom

/-- info: 'ClayPvsNPProof.ATK.SATemNP.passoFl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.passoFl

/-- info: 'ClayPvsNPProof.ATK.SATemNP.lb_canon' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.lb_canon

/-- info: 'ClayPvsNPProof.ATK.SATemNP.acc_cla' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.acc_cla

/-- info: 'ClayPvsNPProof.ATK.SATemNP.foldl_passo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.foldl_passo

/-- info: 'ClayPvsNPProof.ATK.SATemNP.dec_some' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.dec_some

/-- info: 'ClayPvsNPProof.ATK.SATemNP.acc_cnf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.acc_cnf

/-- info: 'ClayPvsNPProof.ATK.SATemNP.forma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.forma

/-- info: 'ClayPvsNPProof.ATK.SATemNP.resto' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.resto

/-- info: 'ClayPvsNPProof.ATK.SATemNP.resto_par' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.resto_par

/-- info: 'ClayPvsNPProof.ATK.SATemNP.resto_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.resto_length_le

/-- info: 'ClayPvsNPProof.ATK.SATemNP.verif' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.verif

/-- info: 'ClayPvsNPProof.ATK.SATemNP.verif_par' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.verif_par

/-- info: 'ClayPvsNPProof.ATK.SATemNP.bits_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.bits_inj

/-- info: 'ClayPvsNPProof.ATK.SATemNP.codEntradas_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.codEntradas_len

/-- info: 'ClayPvsNPProof.ATK.SATemNP.len_cert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.len_cert

/-- info: 'ClayPvsNPProof.ATK.SATemNP.sat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.sat_iff

/-- info: 'ClayPvsNPProof.ATK.SATemNP.Pk' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.Pk

/-- info: 'ClayPvsNPProof.ATK.SATemNP.instDecidableEqPk' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.instDecidableEqPk

/-- info: 'ClayPvsNPProof.ATK.SATemNP.instFintypePk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.instFintypePk

/-- info: 'ClayPvsNPProof.ATK.SATemNP.Lb' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.Lb

/-- info: 'ClayPvsNPProof.ATK.SATemNP.instDecidableEqLb' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.instDecidableEqLb

/-- info: 'ClayPvsNPProof.ATK.SATemNP.instFintypeLb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.instFintypeLb

/-- info: 'ClayPvsNPProof.ATK.SATemNP.St' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.St

/-- info: 'ClayPvsNPProof.ATK.SATemNP.St.v' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.St.v

/-- info: 'ClayPvsNPProof.ATK.SATemNP.St.b' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.St.b

/-- info: 'ClayPvsNPProof.ATK.SATemNP.St.ok' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.St.ok

/-- info: 'ClayPvsNPProof.ATK.SATemNP.St.fl' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.St.fl

/-- info: 'ClayPvsNPProof.ATK.SATemNP.St.lb' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.St.lb

/-- info: 'ClayPvsNPProof.ATK.SATemNP.instFintypeSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.instFintypeSt

/-- info: 'ClayPvsNPProof.ATK.SATemNP.instDecidableEqSt' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.instDecidableEqSt

/-- info: 'ClayPvsNPProof.ATK.SATemNP.Sg' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.Sg

/-- info: 'ClayPvsNPProof.ATK.SATemNP.Gm' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.Gm

/-- info: 'ClayPvsNPProof.ATK.SATemNP.Stm' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.Stm

/-- info: 'ClayPvsNPProof.ATK.SATemNP.st0' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.st0

/-- info: 'ClayPvsNPProof.ATK.SATemNP.ir' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.ir

/-- info: 'ClayPvsNPProof.ATK.SATemNP.irS' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.irS

/-- info: 'ClayPvsNPProof.ATK.SATemNP.rd2' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.rd2

/-- info: 'ClayPvsNPProof.ATK.SATemNP.falha' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.falha

/-- info: 'ClayPvsNPProof.ATK.SATemNP.nf' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.nf

/-- info: 'ClayPvsNPProof.ATK.SATemNP.prog' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.prog

/-- info: 'ClayPvsNPProof.ATK.SATemNP.satTM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.satTM

/-- info: 'ClayPvsNPProof.ATK.SATemNP.stks' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.stks

/-- info: 'ClayPvsNPProof.ATK.SATemNP.stks_s' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.stks_s

/-- info: 'ClayPvsNPProof.ATK.SATemNP.stks_g' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.stks_g

/-- info: 'ClayPvsNPProof.ATK.SATemNP.stks_w' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.stks_w

/-- info: 'ClayPvsNPProof.ATK.SATemNP.stks_t' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.stks_t

/-- info: 'ClayPvsNPProof.ATK.SATemNP.upd_s' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.upd_s

/-- info: 'ClayPvsNPProof.ATK.SATemNP.upd_g' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.upd_g

/-- info: 'ClayPvsNPProof.ATK.SATemNP.upd_w' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.upd_w

/-- info: 'ClayPvsNPProof.ATK.SATemNP.upd_t' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.upd_t

/-- info: 'ClayPvsNPProof.ATK.SATemNP.Cf' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.Cf

/-- info: 'ClayPvsNPProof.ATK.SATemNP.cf' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.cf

/-- info: 'ClayPvsNPProof.ATK.SATemNP.stp' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.stp

/-- info: 'ClayPvsNPProof.ATK.SATemNP.stp_cf' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.stp_cf

/-- info: 'ClayPvsNPProof.ATK.SATemNP.rd2_bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.rd2_bit

/-- info: 'ClayPvsNPProof.ATK.SATemNP.rd2_fim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.rd2_fim

/-- info: 'ClayPvsNPProof.ATK.SATemNP.rd2_fc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.rd2_fc

/-- info: 'ClayPvsNPProof.ATK.SATemNP.rd2_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.rd2_nil

/-- info: 'ClayPvsNPProof.ATK.SATemNP.rd2_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.rd2_one

/-- info: 'ClayPvsNPProof.ATK.SATemNP.Run' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.Run

/-- info: 'ClayPvsNPProof.ATK.SATemNP.Run.refl' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.Run.refl

/-- info: 'ClayPvsNPProof.ATK.SATemNP.Run.trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.Run.trans

/-- info: 'ClayPvsNPProof.ATK.SATemNP.Run.mono' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.Run.mono

/-- info: 'ClayPvsNPProof.ATK.SATemNP.Run.passo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.Run.passo

/-- info: 'ClayPvsNPProof.ATK.SATemNP.Run.um' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.Run.um

/-- info: 'ClayPvsNPProof.ATK.SATemNP.runU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.runU

/-- info: 'ClayPvsNPProof.ATK.SATemNP.runR' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.runR

/-- info: 'ClayPvsNPProof.ATK.SATemNP.runC1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.runC1

/-- info: 'ClayPvsNPProof.ATK.SATemNP.runC2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.runC2

/-- info: 'ClayPvsNPProof.ATK.SATemNP.runF2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.runF2

/-- info: 'ClayPvsNPProof.ATK.SATemNP.runX' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.runX

/-- info: 'ClayPvsNPProof.ATK.SATemNP.runZs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.runZs

/-- info: 'ClayPvsNPProof.ATK.SATemNP.runZg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.runZg

/-- info: 'ClayPvsNPProof.ATK.SATemNP.cfFim' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.cfFim

/-- info: 'ClayPvsNPProof.ATK.SATemNP.runZw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.runZw

/-- info: 'ClayPvsNPProof.ATK.SATemNP.lblF' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.lblF

/-- info: 'ClayPvsNPProof.ATK.SATemNP.runF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.runF

/-- info: 'ClayPvsNPProof.ATK.SATemNP.lblL' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.lblL

/-- info: 'ClayPvsNPProof.ATK.SATemNP.stL' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.stL

/-- info: 'ClayPvsNPProof.ATK.SATemNP.nf_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.nf_eq

/-- info: 'ClayPvsNPProof.ATK.SATemNP.runL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.runL

/-- info: 'ClayPvsNPProof.ATK.SATemNP.ftr_len' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.ftr_len

/-- info: 'ClayPvsNPProof.ATK.SATemNP.lk_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.lk_len

/-- info: 'ClayPvsNPProof.ATK.SATemNP.filt_len' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.filt_len

/-- info: 'ClayPvsNPProof.ATK.SATemNP.falha_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.falha_eq

/-- info: 'ClayPvsNPProof.ATK.SATemNP.cota' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.cota

/-- info: 'ClayPvsNPProof.ATK.SATemNP.runP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.runP

/-- info: 'ClayPvsNPProof.ATK.SATemNP.initList_sat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.initList_sat

/-- info: 'ClayPvsNPProof.ATK.SATemNP.haltList_sat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.haltList_sat

/-- info: 'ClayPvsNPProof.ATK.SATemNP.runTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.runTotal

/-- info: 'ClayPvsNPProof.ATK.SATemNP.verifComputavel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.verifComputavel

/-- info: 'ClayPvsNPProof.ATK.SATemNP.sat_em_NP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.sat_em_NP

/-- info: 'ClayPvsNPProof.ATK.SATemNP.sat_em_NP_modelo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.sat_em_NP_modelo

/-- info: 'ClayPvsNPProof.ATK.SATemNP.cookLevin_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.cookLevin_iff

/-- info: 'ClayPvsNPProof.ATK.SATemNP.teste_aceita' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.teste_aceita

/-- info: 'ClayPvsNPProof.ATK.SATemNP.teste_certificado_errado' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.teste_certificado_errado

/-- info: 'ClayPvsNPProof.ATK.SATemNP.teste_clausula_vazia' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.teste_clausula_vazia

/-- info: 'ClayPvsNPProof.ATK.SATemNP.teste_contradicao' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.SATemNP.teste_contradicao

/-! ## `ClayPvsNPProof.ATK.CookLevinBase` (20 declarações) -/

/-- info: 'ClayPvsNPProof.ATK.CookLevinBase.prof' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinBase.prof

/-- info: 'ClayPvsNPProof.ATK.CookLevinBase.head?_janela' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinBase.head?_janela

/-- info: 'ClayPvsNPProof.ATK.CookLevinBase.tail_janela' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinBase.tail_janela

/-- info: 'ClayPvsNPProof.ATK.CookLevinBase.stepAux_moldura' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinBase.stepAux_moldura

/-- info: 'ClayPvsNPProof.ATK.CookLevinBase.stepAux_topo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinBase.stepAux_topo

/-- info: 'ClayPvsNPProof.ATK.CookLevinBase.emp' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinBase.emp

/-- info: 'ClayPvsNPProof.ATK.CookLevinBase.length_stepAux_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinBase.length_stepAux_le

/-- info: 'ClayPvsNPProof.ATK.CookLevinBase.simbolos' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinBase.simbolos

/-- info: 'ClayPvsNPProof.ATK.CookLevinBase.simbolos_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinBase.simbolos_finite

/-- info: 'ClayPvsNPProof.ATK.CookLevinBase.mem_stepAux' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinBase.mem_stepAux

/-- info: 'ClayPvsNPProof.ATK.CookLevinBase.passoA' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinBase.passoA

/-- info: 'ClayPvsNPProof.ATK.CookLevinBase.passoA_parada' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinBase.passoA_parada

/-- info: 'ClayPvsNPProof.ATK.CookLevinBase.passoA_iter_parada' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinBase.passoA_iter_parada

/-- info: 'ClayPvsNPProof.ATK.CookLevinBase.iter_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinBase.iter_some

/-- info: 'ClayPvsNPProof.ATK.CookLevinBase.acolchoada_de_evals' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinBase.acolchoada_de_evals

/-- info: 'ClayPvsNPProof.ATK.CookLevinBase.eval_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinBase.eval_mono

/-- info: 'ClayPvsNPProof.ATK.CookLevinBase.cota' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinBase.cota

/-- info: 'ClayPvsNPProof.ATK.CookLevinBase.teste_prof_sat' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinBase.teste_prof_sat

/-- info: 'ClayPvsNPProof.ATK.CookLevinBase.teste_emp_sat' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinBase.teste_emp_sat

/-- info: 'ClayPvsNPProof.ATK.CookLevinBase.teste_topo_sat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinBase.teste_topo_sat

/-! ## `ClayPvsNPProof.ATK.Fragmentos` (24 declarações) -/

/-- info: 'ClayPvsNPProof.ATK.Fragmentos.rel' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Fragmentos.rel

/-- info: 'ClayPvsNPProof.ATK.Fragmentos.cmap' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Fragmentos.cmap

/-- info: 'ClayPvsNPProof.ATK.Fragmentos.stepAux_rel' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Fragmentos.stepAux_rel

/-- info: 'ClayPvsNPProof.ATK.Fragmentos.Frag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Fragmentos.Frag

/-- info: 'ClayPvsNPProof.ATK.Fragmentos.Frag.Λ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Fragmentos.Frag.Λ

/-- info: 'ClayPvsNPProof.ATK.Fragmentos.Frag.fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Fragmentos.Frag.fin

/-- info: 'ClayPvsNPProof.ATK.Fragmentos.Frag.entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Fragmentos.Frag.entry

/-- info: 'ClayPvsNPProof.ATK.Fragmentos.Frag.code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Fragmentos.Frag.code

/-- info: 'ClayPvsNPProof.ATK.Fragmentos.Frag.maq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Fragmentos.Frag.maq

/-- info: 'ClayPvsNPProof.ATK.Fragmentos.Faz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Fragmentos.Faz

/-- info: 'ClayPvsNPProof.ATK.Fragmentos.embute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Fragmentos.embute

/-- info: 'ClayPvsNPProof.ATK.Fragmentos.iter_none' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Fragmentos.iter_none

/-- info: 'ClayPvsNPProof.ATK.Fragmentos.seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Fragmentos.seq

/-- info: 'ClayPvsNPProof.ATK.Fragmentos.faz_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Fragmentos.faz_seq

/-- info: 'ClayPvsNPProof.ATK.Fragmentos.cond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Fragmentos.cond

/-- info: 'ClayPvsNPProof.ATK.Fragmentos.faz_cond_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Fragmentos.faz_cond_true

/-- info: 'ClayPvsNPProof.ATK.Fragmentos.faz_cond_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Fragmentos.faz_cond_false

/-- info: 'ClayPvsNPProof.ATK.Fragmentos.atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Fragmentos.atom

/-- info: 'ClayPvsNPProof.ATK.Fragmentos.faz_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Fragmentos.faz_atom

/-- info: 'ClayPvsNPProof.ATK.Fragmentos.laco' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Fragmentos.laco

/-- info: 'ClayPvsNPProof.ATK.Fragmentos.faz_laco' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Fragmentos.faz_laco

/-- info: 'ClayPvsNPProof.ATK.Fragmentos.laco_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Fragmentos.laco_cons

/-- info: 'ClayPvsNPProof.ATK.Fragmentos.laco_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Fragmentos.laco_nil

/-- info: 'ClayPvsNPProof.ATK.Fragmentos.empilha' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Fragmentos.empilha

/-! ## `ClayPvsNPProof.ATK.Compilador` (63 declarações) -/

/-- info: 'ClayPvsNPProof.ATK.Compilador.Pilha' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.Pilha

/-- info: 'ClayPvsNPProof.ATK.Compilador.instDecidableEqPilha' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.instDecidableEqPilha

/-- info: 'ClayPvsNPProof.ATK.Compilador.instFintypePilha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.instFintypePilha

/-- info: 'ClayPvsNPProof.ATK.Compilador.Fr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.Fr

/-- info: 'ClayPvsNPProof.ATK.Compilador.Stk' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.Stk

/-- info: 'ClayPvsNPProof.ATK.Compilador.pushesOut' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.pushesOut

/-- info: 'ClayPvsNPProof.ATK.Compilador.stepAux_pushesOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.stepAux_pushesOut

/-- info: 'ClayPvsNPProof.ATK.Compilador.emitF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.emitF

/-- info: 'ClayPvsNPProof.ATK.Compilador.faz_emit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.faz_emit

/-- info: 'ClayPvsNPProof.ATK.Compilador.pushesBit' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.pushesBit

/-- info: 'ClayPvsNPProof.ATK.Compilador.stepAux_pushesBit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.stepAux_pushesBit

/-- info: 'ClayPvsNPProof.ATK.Compilador.mover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.mover

/-- info: 'ClayPvsNPProof.ATK.Compilador.mv' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.mv

/-- info: 'ClayPvsNPProof.ATK.Compilador.faz_mover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.faz_mover

/-- info: 'ClayPvsNPProof.ATK.Compilador.Cmd.brecOn' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.Cmd.brecOn

/-- info: 'ClayPvsNPProof.ATK.Compilador.Cmd.below' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.Cmd.below

/-- info: 'ClayPvsNPProof.ATK.Compilador.Cmd' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.Cmd

/-- info: 'ClayPvsNPProof.ATK.Compilador.Env' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.Env

/-- info: 'ClayPvsNPProof.ATK.Compilador.semFor' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.semFor

/-- info: 'ClayPvsNPProof.ATK.Compilador.semBits' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.semBits

/-- info: 'ClayPvsNPProof.ATK.Compilador.sem' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.sem

/-- info: 'ClayPvsNPProof.ATK.Compilador.auxS' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.auxS

/-- info: 'ClayPvsNPProof.ATK.Compilador.rdO' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.rdO

/-- info: 'ClayPvsNPProof.ATK.Compilador.stmtInc' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.stmtInc

/-- info: 'ClayPvsNPProof.ATK.Compilador.stmtLen' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.stmtLen

/-- info: 'ClayPvsNPProof.ATK.Compilador.comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.comp

/-- info: 'ClayPvsNPProof.ATK.Compilador.WF' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.WF

/-- info: 'ClayPvsNPProof.ATK.Compilador.custoFor' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.custoFor

/-- info: 'ClayPvsNPProof.ATK.Compilador.custoBits' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.custoBits

/-- info: 'ClayPvsNPProof.ATK.Compilador.custo' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.custo

/-- info: 'ClayPvsNPProof.ATK.Compilador.res' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.res

/-- info: 'ClayPvsNPProof.ATK.Compilador.Pre' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.Pre

/-- info: 'ClayPvsNPProof.ATK.Compilador.Pre.reg' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.Pre.reg

/-- info: 'ClayPvsNPProof.ATK.Compilador.Pre.inp' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.Pre.inp

/-- info: 'ClayPvsNPProof.ATK.Compilador.Pre.tmp' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.Pre.tmp

/-- info: 'ClayPvsNPProof.ATK.Compilador.Pre.aux' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.Pre.aux

/-- info: 'ClayPvsNPProof.ATK.Compilador.Pre.bak' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.Pre.bak

/-- info: 'ClayPvsNPProof.ATK.Compilador.faz_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.faz_congr

/-- info: 'ClayPvsNPProof.ATK.Compilador.ok_emit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.ok_emit

/-- info: 'ClayPvsNPProof.ATK.Compilador.ok_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.ok_zero

/-- info: 'ClayPvsNPProof.ATK.Compilador.ok_inc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.ok_inc

/-- info: 'ClayPvsNPProof.ATK.Compilador.ok_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.ok_add

/-- info: 'ClayPvsNPProof.ATK.Compilador.laco_emitU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.laco_emitU

/-- info: 'ClayPvsNPProof.ATK.Compilador.ok_emitU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.ok_emitU

/-- info: 'ClayPvsNPProof.ATK.Compilador.laco_lenIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.laco_lenIn

/-- info: 'ClayPvsNPProof.ATK.Compilador.ok_lenIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.ok_lenIn

/-- info: 'ClayPvsNPProof.ATK.Compilador.res_res' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.res_res

/-- info: 'ClayPvsNPProof.ATK.Compilador.res_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.res_self

/-- info: 'ClayPvsNPProof.ATK.Compilador.res_update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.res_update

/-- info: 'ClayPvsNPProof.ATK.Compilador.pre_res' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.pre_res

/-- info: 'ClayPvsNPProof.ATK.Compilador.comp_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.comp_ok

/-- info: 'ClayPvsNPProof.ATK.Compilador.seqL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.seqL

/-- info: 'ClayPvsNPProof.ATK.Compilador.limpeza' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.limpeza

/-- info: 'ClayPvsNPProof.ATK.Compilador.Ftot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.Ftot

/-- info: 'ClayPvsNPProof.ATK.Compilador.maq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.maq

/-- info: 'ClayPvsNPProof.ATK.Compilador.faz_zeraRegs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.faz_zeraRegs

/-- info: 'ClayPvsNPProof.ATK.Compilador.custoLimpa' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.custoLimpa

/-- info: 'ClayPvsNPProof.ATK.Compilador.init_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.init_pre

/-- info: 'ClayPvsNPProof.ATK.Compilador.maq_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.maq_run

/-- info: 'ClayPvsNPProof.ATK.Compilador.computavel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.computavel

/-- info: 'ClayPvsNPProof.ATK.Compilador.progUnario' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.progUnario

/-- info: 'ClayPvsNPProof.ATK.Compilador.sem_unario' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.sem_unario

/-- info: 'ClayPvsNPProof.ATK.Compilador.unarioComputavel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.Compilador.unarioComputavel

/-! ## `ClayPvsNPProof.ATK.CookLevinLacos` (114 declarações) -/

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.seqC' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.seqC

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.Emite' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.Emite

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.emite_seqC_nil' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.emite_seqC_nil

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.emite_seqC_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.emite_seqC_cons

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.sem_seqC_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.sem_seqC_append

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.emite_seqC_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.emite_seqC_append

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.emite_seqC_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.emite_seqC_map

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.emite_emit' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.emite_emit

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.Igual' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.Igual

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.igual_refl' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.igual_refl

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.igual_trans' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.igual_trans

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.GeraU' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.GeraU

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.geraU_emite' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.geraU_emite

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.geraU_nil' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.geraU_nil

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.geraU_cons' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.geraU_cons

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.geraU_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.geraU_append

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.geraU_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.geraU_map

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.geraU_forU' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.geraU_forU

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.geraU_congr' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.geraU_congr

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.forall₂_map_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.forall₂_map_map

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.forall₂_append' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.forall₂_append

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.forall₂_flatMap' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.forall₂_flatMap

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.powLoop' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.powLoop

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.custoFor_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.custoFor_le

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.powLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.powLoop_spec

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.one_le_custo_seqC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.one_le_custo_seqC

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.custo_seqC_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.custo_seqC_append

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.seqC_acum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.seqC_acum

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.expoentes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.expoentes

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.sum_range_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.sum_range_list

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.sum_flatMap_sum' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.sum_flatMap_sum

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.sum_expoentes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.sum_expoentes

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.le_natDegree_of_mem_expoentes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.le_natDegree_of_mem_expoentes

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.polyZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.polyZ

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.sem_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.sem_zeros

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.polyZ_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.polyZ_spec

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.Passo' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.Passo

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.passo_nil' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.passo_nil

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.passo_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.passo_cons

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.passo_mono' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.passo_mono

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.passo_lenIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.passo_lenIn

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.lin' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.lin

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.passo_incs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.passo_incs

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.passo_lin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.passo_lin

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.Poli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.Poli

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.eval_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.eval_mono

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.poli_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.poli_eval

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.poli_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.poli_const

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.poli_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.poli_id

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.poli_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.poli_le

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.poli_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.poli_add

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.poli_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.poli_mul

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.poli_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.poli_pow

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.poli_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.poli_comp

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.poli_eval_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.poli_eval_comp

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.RA' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.RA

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.rn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.rn

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.rQ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.rQ

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.rip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.rip

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.rm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.rm

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.rT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.rT

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.rT1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.rT1

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.rHb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.rHb

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.rRr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.rRr

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.rH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.rH

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.rt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.rt

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.ri' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.ri

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.rn_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.rn_val

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.rQ_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.rQ_val

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.rip_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.rip_val

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.rm_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.rm_val

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.rT_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.rT_val

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.rT1_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.rT1_val

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.rHb_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.rHb_val

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.rRr_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.rRr_val

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.rH_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.rH_val

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.rt_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.rt_val

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.ri_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.ri_val

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.ctrs' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.ctrs

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.ctrs_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.ctrs_nodup

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.length_ctrs' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.length_ctrs

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.ge_of_mem_ctrs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.ge_of_mem_ctrs

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.nodup_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.nodup_poly

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.arit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.arit

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.custoZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.custoZ

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.passo_polyZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.passo_polyZ

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.passo_congr' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.passo_congr

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.custoA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.custoA

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.arit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.arit_spec

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.poli_custoZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.poli_custoZ

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.poli_custoA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.poli_custoA

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.escreve' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.escreve

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.Emis' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.Emis

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.tam' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.tam

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.profL' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.profL

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.semFor_nao_escreve' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.semFor_nao_escreve

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.sem_nao_escreve' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.sem_nao_escreve

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.Cota' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.Cota

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.cota_mono' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.cota_mono

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.cota_seq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.cota_seq

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.cota_seqC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.cota_seqC

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.cota_emis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.cota_emis

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.EmisW' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.EmisW

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.emisW_emit' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.emisW_emit

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.emisW_emitU' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.emisW_emitU

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.emisW_seqC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.emisW_seqC

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.emisW_forU' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.emisW_forU

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.emisW_mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.emisW_mono

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.wf_emis' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.wf_emis

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.wf_seqC' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.wf_seqC

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.wf_powLoop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.wf_powLoop

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.wf_polyZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.wf_polyZ

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.wf_lin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.wf_lin

/-- info: 'ClayPvsNPProof.ATK.CookLevinLacos.wf_arit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinLacos.wf_arit

/-! ## `ClayPvsNPProof.ATK.CookLevinTableau` (101 declarações) -/

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Var' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Var

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Lit' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Lit

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Cla' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Cla

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Sat' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Sat

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.sat_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.sat_append

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.sat_flatten' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.sat_flatten

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.sat_flatMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.sat_flatMap

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.sat_singleton' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.sat_singleton

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.tomaSome' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.tomaSome

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.tomaSome_celulas' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.tomaSome_celulas

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.peloMenos' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.peloMenos

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.noMaximo' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.noMaximo

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.umSo' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.umSo

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.sat_noMaximo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.sat_noMaximo

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.umSo_forca' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.umSo_forca

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.umSo_de_indicadora' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.umSo_de_indicadora

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.umSo_alguma' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.umSo_alguma

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.ix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.ix

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.ix_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.ix_lt

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.getElem_ix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.getElem_ix

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.getElem?_ix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.getElem?_ix

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.getElem?_eq_iff_ix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.getElem?_eq_iff_ix

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.ix_getElem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.ix_getElem

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.M' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.M

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.k₀' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.k₀

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.k₁' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.k₁

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.l₀' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.l₀

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.v₀' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.v₀

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.labs' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.labs

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.sts' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.sts

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.vals' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.vals

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.d' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.d

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.ks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.ks

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.mem_ks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.mem_ks

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.celulas' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.celulas

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.rotulos' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.rotulos

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.estados' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.estados

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.fE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.fE

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.fI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.fI

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.Pat' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.Pat

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.pats' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.pats

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.mem_pats' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.mem_pats

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.janela' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.janela

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.antes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.antes

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.conseq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.conseq

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.fR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.fR

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.fP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.fP

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.fA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.fA

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.formula

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.init' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.init

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.run' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.run

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.Cod' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.Cod

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.labs_nodup' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.labs_nodup

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.labs_all' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.labs_all

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.sts_nodup' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.sts_nodup

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.sts_all' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.sts_all

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.vals_nodup' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.vals_nodup

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.none_mem' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.none_mem

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.pre_mem' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.pre_mem

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.cands_mem' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.cands_mem

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.acc_mem' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.acc_mem

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.push_mem' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.push_mem

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.prof_le' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.prof_le

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.emp_le' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.emp_le

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.altura' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.Bom.altura

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.passoA_some' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.passoA_some

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.map_finRange_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.map_finRange_val

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Contigua' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Contigua

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.tomaSome_getElem?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.tomaSome_getElem?

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.length_tomaSome_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.length_tomaSome_le

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.mem_tomaSome' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.mem_tomaSome

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.forca_cod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.forca_cod

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.cod_umSo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.cod_umSo

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.run_zero' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.run_zero

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.run_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.run_succ

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.init_stk_k₀' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.init_stk_k₀

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.init_stk_ne' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.init_stk_ne

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.run_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.run_inv

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.τrun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.τrun

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.cod_τrun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.cod_τrun

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.celula_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.celula_mem

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.sat_par' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.sat_par

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.sat_unit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.sat_unit

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.conseq_sat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.conseq_sat

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.antes_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.antes_neg

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.completo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.completo

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.unit_true' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.unit_true

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.imp_true' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.imp_true

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.imp2_true' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.imp2_true

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.umSo_de_fE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.umSo_de_fE

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.mem_fR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.mem_fR

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.passo_correto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.passo_correto

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.base_correto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.base_correto

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Tab.tableau_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Tab.tableau_iff

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Teste.M₀' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Teste.M₀

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Teste.A₀' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Teste.A₀

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Teste.bom₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Teste.bom₀

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Teste.teste_aceita' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Teste.teste_aceita

/-- info: 'ClayPvsNPProof.ATK.CookLevinTableau.Teste.teste_recusa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinTableau.Teste.teste_recusa

/-! ## `ClayPvsNPProof.ATK.CookLevinReducao` (41 declarações) -/

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.codCNF_mem_SAT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.codCNF_mem_SAT

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.unario' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.unario

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.unario_append_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.unario_append_inj

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.κ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.κ

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.κ_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.κ_inj

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.cadeia' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.cadeia

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.cadeia_canonica' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.cadeia_canonica

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.cadeia_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.cadeia_inj

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.nome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.nome

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.bits_nome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.bits_nome

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.nome_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.nome_inj

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.renomeia' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.renomeia

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.satisfativel_renomeia' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.satisfativel_renomeia

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.simbolosTM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.simbolosTM

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.simbolosTM_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.simbolosTM_finite

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.fibra_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.fibra_finite

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.tabTM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.tabTM

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.empTM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.empTM

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.mem_vals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.mem_vals

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.bomTM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.bomTM

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.init_tabTM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.init_tabTM

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.DadosNP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.DadosNP

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.DadosNP.χ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.DadosNP.χ

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.DadosNP.M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.DadosNP.M

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.DadosNP.q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.DadosNP.q

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.DadosNP.hq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.DadosNP.hq

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.dadosNP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.dadosNP

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.preD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.preD

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.candsD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.candsD

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.accD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.accD

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.formulaD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.formulaD

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.reducao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.reducao

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.length_preD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.length_preD

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.entrada_par' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.entrada_par

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.length_par' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.length_par

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.haltList_k₁' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.haltList_k₁

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.run_par' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.run_par

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.reducao_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.reducao_iff

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.teste_cadeia_y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.teste_cadeia_y

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.teste_sat_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.teste_sat_unit

/-- info: 'ClayPvsNPProof.ATK.CookLevinReducao.teste_sat_vazia' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinReducao.teste_sat_vazia

/-! ## `ClayPvsNPProof.ATK.CookLevinGerador` (109 declarações) -/

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.sU' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.sU

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.unario_simb' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.unario_simb

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Termo' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Termo

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Termo.rs' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Termo.rs

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Termo.c' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Termo.c

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Termo.val' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Termo.val

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.pTermo' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.pTermo

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.emite_pTermo' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.emite_pTermo

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.ren' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.ren

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.codCNF_renomeia' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.codCNF_renomeia

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.pLit' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.pLit

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.emite_pLit' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.emite_pLit

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.codLiteral_nome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.codLiteral_nome

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.emite_litX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.emite_litX

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.emite_litY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.emite_litY

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.emite_litZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.emite_litZ

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.pCla' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.pCla

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.emite_pCla' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.emite_pCla

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Termo.em' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Termo.em

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Termo.val_igual' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Termo.val_igual

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.geraU_litX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.geraU_litX

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.geraU_litY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.geraU_litY

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.geraU_litZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.geraU_litZ

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.geraU_cla' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.geraU_cla

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.cc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.cc

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.codCNF_renomeia_cc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.codCNF_renomeia_cc

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.pNoMax' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.pNoMax

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.pUmSo' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.pUmSo

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.geraU_noMax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.geraU_noMax

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.geraU_umSo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.geraU_umSo

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.tc' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.tc

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.tr' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.tr

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.tr2' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.tr2

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.val_tc' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.val_tc

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.val_tr' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.val_tr

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.val_tr2' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.val_tr2

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.em_tc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.em_tc

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.em_tr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.em_tr

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.em_tr2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.em_tr2

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.lx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.lx

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.ly' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.ly

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.lz' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.lz

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.gx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.gx

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.gy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.gy

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.gz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.gz

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.gcla' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.gcla

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.progE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.progE

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.geraU_progE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.geraU_progE

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.progP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.progP

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.geraU_progP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.geraU_progP

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.progA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.progA

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.geraU_progA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.geraU_progA

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.corpoPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.corpoPre

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.progPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.progPre

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.gPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.gPre

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.ex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.ex

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.sem_corpoPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.sem_corpoPre

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.semBits_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.semBits_pre

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.geraU_progPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.geraU_progPre

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.flatMap_range_add' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.flatMap_range_add

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.flatMap_range_dobro' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.flatMap_range_dobro

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.getElem?_dup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.getElem?_dup

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.length_dup' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.length_dup

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.pre_par' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.pre_par

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.pre_fim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.pre_fim

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.length_pre' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.length_pre

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.livres' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.livres

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.saidaI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.saidaI

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.fI_saida' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.fI_saida

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.progI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.progI

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.geraU_progI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.geraU_progI

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.filter_range_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.filter_range_lt

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.antesC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.antesC

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.forall₂_antes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.forall₂_antes

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.progConseq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.progConseq

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.saidaC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.saidaC

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.conseq_saida' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.conseq_saida

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.geraU_progConseq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.geraU_progConseq

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.progRp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.progRp

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.progR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.progR

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.saidaR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.saidaR

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.length_janela' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.length_janela

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.fR_saida' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.fR_saida

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.geraU_progR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.geraU_progR

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Regs' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Regs

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Regs.rT' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Regs.rT

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Regs.rT1' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Regs.rT1

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Regs.rH' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Regs.rH

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Regs.rHb' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Regs.rHb

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Regs.rn' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Regs.rn

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Regs.rip' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Regs.rip

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Regs.rQ' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Regs.rQ

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Regs.rm' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Regs.rm

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Regs.rRr' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Regs.rRr

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Regs.t' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Regs.t

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Regs.i' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Regs.i

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Regs.params' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Regs.params

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.progTab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.progTab

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Vals' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Vals

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Vals.eT' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Vals.eT

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Vals.eT1' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Vals.eT1

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Vals.eH' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Vals.eH

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Vals.eHb' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Vals.eHb

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Vals.en' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Vals.en

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Vals.eip' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Vals.eip

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Vals.eQ' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Vals.eQ

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Vals.em' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Vals.em

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.Vals.eR' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.Vals.eR

/-- info: 'ClayPvsNPProof.ATK.CookLevinGerador.geraU_progTab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinGerador.geraU_progTab

/-! ## `ClayPvsNPProof.ATK.CookLevinNP` (80 declarações) -/

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.emisW_pTermo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.emisW_pTermo

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.emisW_pLit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.emisW_pLit

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.emisW_lx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.emisW_lx

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.emisW_ly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.emisW_ly

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.emisW_lz' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.emisW_lz

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.emisW_pCla' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.emisW_pCla

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.emisW_pNoMax' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.emisW_pNoMax

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.emisW_pUmSo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.emisW_pUmSo

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.emisW_progE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.emisW_progE

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.emisW_progP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.emisW_progP

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.emisW_progA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.emisW_progA

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.emisW_antesC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.emisW_antesC

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.emisW_progConseq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.emisW_progConseq

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.emisW_progR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.emisW_progR

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.listaI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.listaI

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.progI_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.progI_eq

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.nao_emis_progPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.nao_emis_progPre

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.emis_listaI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.emis_listaI

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.Cst' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.Cst

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.cota_seqC_gen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.cota_seqC_gen

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.cota_emisW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.cota_emisW

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.sem_puro' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.sem_puro

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.clPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.clPre

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.emisW_clPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.emisW_clPre

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.Bc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.Bc

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.custo_corpoPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.custo_corpoPre

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.cota_progPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.cota_progPre

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.emis_seqC_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.emis_seqC_mem

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.bfE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.bfE

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.bfE_emis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.bfE_emis

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.bfE_nao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.bfE_nao

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.bPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.bPre

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.oPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.oPre

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.bI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.bI

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.oI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.oI

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.cota_progI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.cota_progI

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.nao_emis_progI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.nao_emis_progI

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.listaTab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.listaTab

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.bTab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.bTab

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.oTab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.oTab

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.Distintos' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.Distintos

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.Distintos.t_i' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.Distintos.t_i

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.Distintos.T1_t' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.Distintos.T1_t

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.Distintos.T_t' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.Distintos.T_t

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.Distintos.H_i' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.Distintos.H_i

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.Distintos.H_t' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.Distintos.H_t

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.Distintos.Hb_i' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.Distintos.Hb_i

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.Distintos.Q_t' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.Distintos.Q_t

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.Distintos.R_t' does not depend on any axioms -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.Distintos.R_t

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.cota_progTab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.cota_progTab

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.wf_progTab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.wf_progTab

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.poli_sum_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.poli_sum_list

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.poli_Cst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.poli_Cst

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.poli_bfE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.poli_bfE

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.poli_Bc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.poli_Bc

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.poli_bPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.poli_bPre

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.poli_oPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.poli_oPre

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.poli_bI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.poli_bI

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.poli_oI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.poli_oI

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.poli_bTab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.poli_bTab

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.poli_oTab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.poli_oTab

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.LL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.LL

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.tabD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.tabD

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.regs

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.gerador' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.gerador

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.Tf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.Tf

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.Hf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.Hf

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.aritD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.aritD

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.saida_gerador' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.saida_gerador

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.distintos_regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.distintos_regs

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.wf_gerador' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.wf_gerador

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.Vf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.Vf

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.limitado' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.limitado

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.custoTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.custoTotal

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.custo_gerador' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.custo_gerador

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.poli_Vf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.poli_Vf

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.poli_custoTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.poli_custoTotal

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.maqRed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.maqRed

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.red_SAT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.red_SAT

/-- info: 'ClayPvsNPProof.ATK.CookLevinNP.cookLevin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayPvsNPProof.ATK.CookLevinNP.cookLevin
