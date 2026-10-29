-- Origem: kernel ATK, espelho público ShantiDraconis/atk-math-core-public @ ffc111a
-- (= ShantiDraconis/M-Core @ 390e378), arquivo imports/M-Core/atk-kernel/ATK/LigacaoPNP.lean
-- (sha256 do original: a677ff4783b1f6a6…).
-- Alterações comuns: namespace `ATK.*` → `ClayPvsNPProof.ATK.*`; linhas `#print axioms` removidas
-- (a auditoria está em `ClayPvsNPProof/Audit.lean`). Alterações específicas: nenhuma além das comuns.
import ClayPvsNPProof.ATK.Conditional.PvsNP
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.Encoding

/-!
# ATK — Ligação L2 (parte 1): o enunciado fiel de P ≠ NP sobre as máquinas da Mathlib

`ClayPvsNPProof.ATK.Conditional.PvsNP.ComplexityModel` é uma interface. Aqui as classes **P** e **NP** são
definidas sobre o modelo de máquina da Mathlib (`Turing.FinTM2`, máquinas de Turing de pilhas
com tempo polinomial, `Turing.TM2ComputableInPolyTime`), na forma padrão (Arora–Barak, Def. 1.13
e 2.1):

* palavras binárias `List Bool`, linguagens `Set (List Bool)`;
* `L ∈ P` ⟺ a função característica de `L` é computável por uma `FinTM2` em tempo
  `p(|w|)` para algum polinômio `p`;
* `L ∈ NP` ⟺ existem `V ∈ P` e um polinômio `q` com
  `w ∈ L ⟺ ∃ c, |c| ≤ q(|w|) ∧ ⟨w, c⟩ ∈ V`, onde `⟨w, c⟩` duplica cada bit de `w`, põe o
  separador `01` e depois `c` (codificação de pares sem ambiguidade);
* `PneNP : classeP ≠ classeNP`.

Testes de sanidade com máquinas construídas e verificadas passo a passo (`apagaEscreve`):
`∅ ∈ P`, `todas as palavras ∈ P`, `∅ ∈ NP`, `todas ∈ NP`; a codificação de pares é injetiva
(`par_injective`).

**Parte 2** (`ClayPvsNPProof.ATK.ComposicaoTM2`, `ClayPvsNPProof.ATK.ModeloPNP`): composição de máquinas `FinTM2` em tempo
polinomial, `P ⊆ NP`, reduções de Karp com P fechada por elas, SAT e a instância
`ComplexityModel` (`ClayPvsNPProof.ATK.ModeloPNP.modeloPNP`), com `PneNP modeloPNP ↔ PneNP` por definição.

Nada aqui decide P vs NP. **CLOSED_MATH continua false.**
-/

namespace ClayPvsNPProof.ATK.LigacaoPNP

open Turing Computability StateTransition

/-- Palavras binárias. -/
abbrev Palavra := List Bool

/-- Linguagens. -/
abbrev Linguagem := Set Palavra

/-- Codificação das palavras na fita (alfabeto `Bool`, identidade). -/
def cod : Palavra → List Bool := id

/-- `L ∈ P`: a função característica é computável em tempo polinomial por uma `FinTM2`. -/
def EmP (L : Linguagem) : Prop :=
  ∃ χ : Palavra → Bool, (∀ w, w ∈ L ↔ χ w = true) ∧
    Nonempty (TM2ComputableInPolyTime cod encodeBool χ)

/-- Par `⟨w, c⟩`: bits de `w` duplicados, separador `01`, depois `c`. -/
def par (w c : Palavra) : Palavra := (w.flatMap fun b => [b, b]) ++ [false, true] ++ c

/-- `L ∈ NP`: verificador em P e certificados de tamanho polinomial. -/
def EmNP (L : Linguagem) : Prop :=
  ∃ V : Linguagem, EmP V ∧ ∃ q : Polynomial ℕ,
    ∀ w, w ∈ L ↔ ∃ c : Palavra, c.length ≤ q.eval w.length ∧ par w c ∈ V

/-- A classe P. -/
def classeP : Set Linguagem := {L | EmP L}

/-- A classe NP. -/
def classeNP : Set Linguagem := {L | EmNP L}

/-- **O enunciado fiel**: P ≠ NP. -/
def PneNP : Prop := classeP ≠ classeNP

/-! ### A codificação de pares é injetiva -/

theorem par_injective_aux :
    ∀ (w₁ w₂ c₁ c₂ : Palavra), par w₁ c₁ = par w₂ c₂ → w₁ = w₂ ∧ c₁ = c₂
  | [], [], c₁, c₂, h => by simpa [par] using h
  | [], b :: w₂, c₁, c₂, h => by cases b <;> simp [par] at h
  | b :: w₁, [], c₁, c₂, h => by cases b <;> simp [par] at h
  | a :: w₁, b :: w₂, c₁, c₂, h => by
      simp only [par, List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc,
        List.cons.injEq] at h
      obtain ⟨hab, -, h⟩ := h
      have := par_injective_aux w₁ w₂ c₁ c₂ (by simpa [par] using h)
      exact ⟨by rw [hab, this.1], this.2⟩

/-- `⟨w₁, c₁⟩ = ⟨w₂, c₂⟩ ⇒ w₁ = w₂ ∧ c₁ = c₂`. -/
theorem par_injective {w₁ w₂ c₁ c₂ : Palavra} (h : par w₁ c₁ = par w₂ c₂) :
    w₁ = w₂ ∧ c₁ = c₂ :=
  par_injective_aux w₁ w₂ c₁ c₂ h

/-! ### Uma máquina construída: apaga a entrada e escreve `b` -/

open Turing.TM2.Stmt in
/-- Máquina de uma pilha: desempilha até esvaziar e então escreve `b`. -/
abbrev apagaEscreve (b : Bool) : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m _ := pop () (fun _ o => o.isSome) (branch id (goto fun _ => ()) (push () (fun _ => b) halt))

/-- Configuração com rótulo `l`, estado `s` e pilha `w`. -/
def cfg (b : Bool) (l : Option Unit) (s : Bool) (w : List Bool) : (apagaEscreve b).Cfg :=
  ⟨l, s, fun _ => w⟩

theorem update_unit (S : Unit → List Bool) (v : List Bool) :
    Function.update S () v = fun _ => v := by
  funext k
  cases k
  simp

theorem step_cons (b : Bool) (s a : Bool) (w : List Bool) :
    (apagaEscreve b).step (cfg b (some ()) s (a :: w)) = some (cfg b (some ()) true w) := by
  simp only [FinTM2.step, cfg, apagaEscreve, TM2.step, TM2.stepAux]
  simp only [List.head?_cons, Option.isSome_some, List.tail_cons, id, Bool.cond_true]
  congr 2

theorem step_nil (b : Bool) (s : Bool) :
    (apagaEscreve b).step (cfg b (some ()) s []) = some (cfg b none false [b]) := by
  simp only [FinTM2.step, cfg, apagaEscreve, TM2.step, TM2.stepAux]
  simp only [List.head?_nil, Option.isSome_none, List.tail_nil, id, Bool.cond_false]
  congr 2

theorem iterate_apaga (b : Bool) :
    ∀ (w : List Bool) (s : Bool),
      (flip bind (apagaEscreve b).step)^[w.length + 1] (some (cfg b (some ()) s w)) =
        some (cfg b none false [b])
  | [], s => by
      rw [List.length_nil, zero_add, Function.iterate_one]
      exact step_nil b s
  | a :: w, s => by
      rw [List.length_cons, Function.iterate_succ_apply]
      have h1 : flip bind (apagaEscreve b).step (some (cfg b (some ()) s (a :: w))) =
          some (cfg b (some ()) true w) := step_cons b s a w
      rw [h1]
      exact iterate_apaga b w true

theorem initList_apaga (b : Bool) (w : List Bool) :
    initList (apagaEscreve b) w = cfg b (some ()) false w := by
  simp only [initList, cfg]
  congr

theorem haltList_apaga (b : Bool) :
    haltList (apagaEscreve b) [b] = cfg b none false [b] := by
  simp only [haltList, cfg]
  congr

/-- A função constante `b` é computável em tempo `n + 1`. -/
noncomputable def constComputavel (b : Bool) :
    TM2ComputableInPolyTime cod encodeBool (fun _ : Palavra => b) where
  tm := apagaEscreve b
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun w :=
    { steps := w.length + 1
      evals_in_steps := by
        have hin : List.map (Equiv.refl Bool).invFun (cod w) = w := by
          simp [cod]
        have hout : List.map (Equiv.refl Bool).invFun (encodeBool b) = [b] := by
          simp [encodeBool]
        rw [hin, hout, initList_apaga, Option.map_some, haltList_apaga]
        exact iterate_apaga b w false
      steps_le_m := by simp [cod] }

/-- `∅ ∈ P`. -/
theorem vazio_em_P : (∅ : Linguagem) ∈ classeP :=
  ⟨fun _ => false, fun w => by simp, ⟨constComputavel false⟩⟩

/-- Todas as palavras `∈ P`. -/
theorem univ_em_P : (Set.univ : Linguagem) ∈ classeP :=
  ⟨fun _ => true, fun w => by simp, ⟨constComputavel true⟩⟩

/-- `∅ ∈ NP` (verificador vazio). -/
theorem vazio_em_NP : (∅ : Linguagem) ∈ classeNP :=
  ⟨∅, vazio_em_P, 0, fun w => by simp⟩

/-- Todas as palavras `∈ NP` (verificador que aceita tudo, certificado vazio). -/
theorem univ_em_NP : (Set.univ : Linguagem) ∈ classeNP :=
  ⟨Set.univ, univ_em_P, 0, fun w => by simp⟩

end ClayPvsNPProof.ATK.LigacaoPNP

