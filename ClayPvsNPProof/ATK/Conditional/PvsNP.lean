-- Origem: kernel ATK, espelho público ShantiDraconis/atk-math-core-public @ ffc111a
-- (= ShantiDraconis/M-Core @ 390e378), arquivo imports/M-Core/atk-kernel/ATK/Conditional/PvsNP.lean
-- (sha256 do original: e1731d6b484651a6…).
-- Alterações comuns: namespace `ATK.*` → `ClayPvsNPProof.ATK.*`; linhas `#print axioms` removidas
-- (a auditoria está em `ClayPvsNPProof/Audit.lean`). Alterações específicas: nenhuma além das comuns.
import Mathlib.Data.Set.Basic

/-!
# Condicional — P vs NP

A Mathlib não define NP; por isso o enunciado é relativo a um `ComplexityModel`
(fidelidade: PARAMÉTRICA — vale para qualquer modelo que satisfaça os campos).

Forma condicional:

  `CookLevin M SAT → SATNotInP M SAT → M.P ≠ M.NP`

* `CookLevin` (PONTE; Cook 1971, Levin 1973): SAT ∈ NP e toda L ∈ NP reduz a SAT.
  No modelo do lane `m-core-p-vs-np`, a parte "SAT ∈ NP" foi FECHADA (P01, 09/10/2026;
  `PNPAfterP01.sat_in_np`, branch `atk/p01-closure-audit-20261013-pnp-reduction`). Lá, P ≠ NP
  fica reduzido a G2.1 = SAT ∉ P — a mesma hipótese aberta deste arquivo.
* `SATNotInP` (ABERTA; lane G21Pointwise do M-Core).

Também certificado: dada a ponte, `P ≠ NP ↔ SAT ∉ P` — a hipótese aberta é exatamente o
problema, não algo mais fraco.
-/

namespace ClayPvsNPProof.ATK.Conditional.PvsNP

universe u

/-- Modelo de complexidade: classes como conjuntos de linguagens + redução de Karp. -/
structure ComplexityModel where
  Lang : Type u
  P : Set Lang
  NP : Set Lang
  /-- `Red A B`: A reduz a B em tempo polinomial. -/
  Red : Lang → Lang → Prop
  P_subset_NP : P ⊆ NP
  P_closed_under_red : ∀ {A B : Lang}, Red A B → B ∈ P → A ∈ P

/-- PONTE (Cook–Levin): SAT é NP-completo. -/
def CookLevin (M : ComplexityModel.{u}) (SAT : M.Lang) : Prop :=
  SAT ∈ M.NP ∧ ∀ L ∈ M.NP, M.Red L SAT

/-- HIPÓTESE ABERTA: SAT ∉ P. -/
def SATNotInP (M : ComplexityModel.{u}) (SAT : M.Lang) : Prop :=
  SAT ∉ M.P

/-- Enunciado-alvo. -/
def PneNP (M : ComplexityModel.{u}) : Prop :=
  M.P ≠ M.NP

/-- **Condicional P ≠ NP.** -/
theorem pvsnp_conditional {M : ComplexityModel.{u}} {SAT : M.Lang}
    (hBridge : CookLevin M SAT) (hOpen : SATNotInP M SAT) : PneNP M := by
  unfold PneNP
  unfold SATNotInP at hOpen
  intro h
  apply hOpen
  rw [h]
  exact hBridge.1

/-- Dada a ponte, a hipótese aberta é equivalente ao enunciado. -/
theorem pneNP_iff_sat_not_in_P {M : ComplexityModel.{u}} {SAT : M.Lang}
    (hBridge : CookLevin M SAT) : PneNP M ↔ SATNotInP M SAT := by
  constructor
  · intro hne hSAT
    apply hne
    apply Set.Subset.antisymm M.P_subset_NP
    intro L hL
    exact M.P_closed_under_red (hBridge.2 L hL) hSAT
  · exact pvsnp_conditional hBridge

end ClayPvsNPProof.ATK.Conditional.PvsNP

