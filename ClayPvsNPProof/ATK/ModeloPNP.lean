-- Origem: kernel ATK, espelho público ShantiDraconis/atk-math-core-public @ ffc111a
-- (= ShantiDraconis/M-Core @ 390e378), arquivo imports/M-Core/atk-kernel/ATK/ModeloPNP.lean
-- (sha256 do original: 878719f912962506…).
-- Alterações comuns: namespace `ATK.*` → `ClayPvsNPProof.ATK.*`; linhas `#print axioms` removidas
-- (a auditoria está em `ClayPvsNPProof/Audit.lean`). Alterações específicas: removido o import de `ATK.Termos` e o teorema `fielL2` (dependia de `ATK.Termos`, fora do escopo P vs NP); import de `LigacaoPNP` explícito.
import ClayPvsNPProof.ATK.ComposicaoTM2
import ClayPvsNPProof.ATK.LigacaoPNP

/-!
# ATK — Ligação L2 (parte 2): o modelo genuíno de P e NP

Com a composição de máquinas em tempo polinomial (`ClayPvsNPProof.ATK.ComposicaoTM2.comp`):

* `decTM`: máquina que decodifica o primeiro componente de um par `⟨w, c⟩` (`dec_par`), em tempo
  linear (`decComputavel`);
* `P_sub_NP`: `classeP ⊆ classeNP` sobre `Turing.FinTM2` (o verificador decodifica e roda o
  decisor; o certificado é vazio);
* `Red`: reduções de Karp (função computável em tempo polinomial por `FinTM2`) e
  `P_fechada_red`: P é fechada por elas;
* `SAT`: fórmulas CNF codificadas em binário, satisfatíveis;
* `modeloPNP`: a instância `ComplexityModel` com as classes de `ClayPvsNPProof.ATK.LigacaoPNP`, e
  `fiel`: `PneNP modeloPNP ↔ ClayPvsNPProof.ATK.LigacaoPNP.PneNP` (é o enunciado oficial, por definição).

Nada aqui decide P vs NP. A ponte B4 (Cook–Levin sobre este modelo) e o produtor O4 (SAT ∉ P)
continuam abertos.
-/

open Turing Computability StateTransition Function

namespace ClayPvsNPProof.ATK.ModeloPNP

open ClayPvsNPProof.ATK.LigacaoPNP

/-! ### O decodificador do primeiro componente -/

/-- Lê pares de bits iguais até achar um par diferente (o separador `01`). -/
def dec : List Bool → List Bool
  | a :: b :: r => if a = b then a :: dec r else []
  | _ => []

theorem dec_par (w c : Palavra) : dec (par w c) = w := by
  induction w with
  | nil => simp [par, dec]
  | cons b w ih =>
    simp only [par, List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc] at ih ⊢
    rw [dec]; simp [ih]

theorem dec_length_le : ∀ x : List Bool, (dec x).length ≤ x.length
  | a :: b :: r => by
    simp only [dec]
    split_ifs
    · simp only [List.length_cons]; have := dec_length_le r; omega
    · simp
  | [a] => by simp [dec]
  | [] => by simp [dec]

/-- Pilhas do decodificador: `false` = entrada/saída, `true` = auxiliar. -/
def pil (x A : List Bool) : Bool → List Bool := fun k => if k then A else x

theorem pil_false (x A) : pil x A false = x := rfl
theorem pil_true (x A) : pil x A true = A := rfl

theorem upd_false (x A y) : update (pil x A) false y = pil y A := by
  funext k; cases k <;> simp [pil]

theorem upd_true (x A y) : update (pil x A) true y = pil x y := by
  funext k; cases k <;> simp [pil]

abbrev σD := Option Bool × Option Bool

open Turing.TM2.Stmt

abbrev StD := Turing.TM2.Stmt (fun _ : Bool => Bool) (Fin 3) σD

/-- Rótulo 0: lê um par. -/
def passoPar : StD :=
  pop false (fun s o => (o, s.2))
    (branch (fun s => s.1.isSome)
      (pop false (fun s o => (s.1, o))
        (branch (fun s => s.2.isSome)
          (branch (fun s => decide (s.1 = s.2))
            (push true (fun s => s.1.getD false) (load (fun _ => (none, none)) (goto fun _ => 0)))
            (load (fun _ => (none, none)) (goto fun _ => 1)))
          (load (fun _ => (none, none)) (goto fun _ => 2))))
      (load (fun _ => (none, none)) (goto fun _ => 2)))

/-- Rótulo 1: descarta o resto da entrada. -/
def passoLimpa : StD :=
  pop false (fun _ o => (o, none))
    (branch (fun s => s.1.isSome) (load (fun _ => (none, none)) (goto fun _ => 1)) (goto fun _ => 2))

/-- Rótulo 2: devolve a pilha auxiliar para a saída (restaura a ordem). -/
def passoSaida : StD :=
  pop true (fun _ o => (o, none))
    (branch (fun s => s.1.isSome)
      (push false (fun s => s.1.getD false) (load (fun _ => (none, none)) (goto fun _ => 2)))
      halt)

def progD : Fin 3 → StD
  | 0 => passoPar
  | 1 => passoLimpa
  | 2 => passoSaida

/-- **O decodificador** como `FinTM2`. -/
abbrev decTM : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := false
  Γ _ := Bool
  Λ := Fin 3
  main := 0
  σ := σD
  initialState := (none, none)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := progD

abbrev CfgD := Turing.TM2.Cfg (fun _ : Bool => Bool) (Fin 3) σD

def cfgD (l : Fin 3) (x A : List Bool) : CfgD := ⟨some l, (none, none), pil x A⟩

abbrev stepD := Turing.TM2.step progD

theorem par_igual (a r A) :
    stepD (cfgD 0 (a :: a :: r) A) = some (cfgD 0 r (a :: A)) := by
  simp [cfgD, stepD, progD, passoPar, Turing.TM2.stepAux, pil_false, upd_false, pil_true, upd_true]

theorem par_dif (a b r A) (h : a ≠ b) :
    stepD (cfgD 0 (a :: b :: r) A) = some (cfgD 1 r A) := by
  simp [cfgD, stepD, progD, passoPar, Turing.TM2.stepAux, pil_false, upd_false, h]

theorem par_um (a A) : stepD (cfgD 0 [a] A) = some (cfgD 2 [] A) := by
  simp [cfgD, stepD, progD, passoPar, Turing.TM2.stepAux, pil_false, upd_false]

theorem par_vazio (A) : stepD (cfgD 0 [] A) = some (cfgD 2 [] A) := by
  simp [cfgD, stepD, progD, passoPar, Turing.TM2.stepAux, pil_false, upd_false]

theorem limpa_cons (a r A) : stepD (cfgD 1 (a :: r) A) = some (cfgD 1 r A) := by
  simp [cfgD, stepD, progD, passoLimpa, Turing.TM2.stepAux, pil_false, upd_false]

theorem limpa_vazio (A) : stepD (cfgD 1 [] A) = some (cfgD 2 [] A) := by
  simp [cfgD, stepD, progD, passoLimpa, Turing.TM2.stepAux, pil_false, upd_false]

theorem saida_cons (B a A) : stepD (cfgD 2 B (a :: A)) = some (cfgD 2 (a :: B) A) := by
  simp [cfgD, stepD, progD, passoSaida, Turing.TM2.stepAux, pil_true, upd_true, pil_false, upd_false]

theorem saida_vazio (B) : stepD (cfgD 2 B []) = some ⟨none, (none, none), pil B []⟩ := by
  simp [cfgD, stepD, progD, passoSaida, Turing.TM2.stepAux, pil_true, upd_true]

theorem iter_one_step {c c' : CfgD} (h : stepD c = some c') :
    flip bind stepD (some c) = some c' := h

theorem run_limpa : ∀ (r A : List Bool),
    (flip bind stepD)^[r.length + 1] (some (cfgD 1 r A)) = some (cfgD 2 [] A)
  | [], A => by rw [List.length_nil, zero_add, iterate_one]; exact limpa_vazio A
  | a :: r, A => by
    rw [List.length_cons, iterate_succ_apply, iter_one_step (limpa_cons a r A), run_limpa r A]

theorem run_saida : ∀ (A B : List Bool),
    (flip bind stepD)^[A.length + 1] (some (cfgD 2 B A)) =
      some ⟨none, (none, none), pil (A.reverse ++ B) []⟩
  | [], B => by rw [List.length_nil, zero_add, iterate_one]; exact saida_vazio B
  | a :: A, B => by
    rw [List.length_cons, iterate_succ_apply, iter_one_step (saida_cons B a A), run_saida A (a :: B)]
    simp

/-- Passos da fase de leitura. -/
def kPar : List Bool → ℕ
  | a :: b :: r => if a = b then kPar r + 1 else r.length + 2
  | _ => 1

theorem kPar_le : ∀ x : List Bool, kPar x ≤ x.length + 1
  | a :: b :: r => by
    simp only [kPar, List.length_cons]
    split_ifs
    · have := kPar_le r; omega
    · omega
  | [a] => by simp [kPar]
  | [] => by simp [kPar]

theorem run_par : ∀ (x A : List Bool),
    (flip bind stepD)^[kPar x] (some (cfgD 0 x A)) = some (cfgD 2 [] ((dec x).reverse ++ A))
  | a :: b :: r, A => by
    by_cases h : a = b
    · subst h
      simp only [kPar, ite_true]
      rw [iterate_succ_apply, iter_one_step (par_igual a r A), run_par r (a :: A)]
      simp [dec]
    · simp only [kPar, h, ite_false]
      rw [show r.length + 2 = r.length + 1 + 1 from rfl, iterate_succ_apply,
        iter_one_step (par_dif a b r A h), run_limpa r A]
      simp [dec, h]
  | [a], A => by
    simp only [kPar, iterate_one, dec, List.reverse_nil, List.nil_append]
    exact par_um a A
  | [], A => by
    simp only [kPar, iterate_one, dec, List.reverse_nil, List.nil_append]
    exact par_vazio A

theorem initList_dec (x : List Bool) : initList decTM x = cfgD 0 x [] := by
  simp only [initList, cfgD, decTM]
  congr 1
  funext k
  cases k <;> (simp [pil]; try rfl)

theorem haltList_dec (y : List Bool) :
    haltList decTM y = (⟨none, (none, none), pil y []⟩ : CfgD) := by
  simp only [haltList, decTM]
  congr 1
  funext k
  cases k <;> (simp [pil]; try rfl)

/-- **O decodificador roda em tempo linear**: `dec` é computável em tempo `2|x| + 2`. -/
noncomputable def decComputavel : TM2ComputableInPolyTime cod cod dec where
  tm := decTM
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 2
  outputsFun x := by
    have hrun := run_par x []
    have hk := kPar_le x
    have hsai := run_saida ((dec x).reverse ++ []) []
    simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at hsai
    simp only [List.append_nil] at hrun
    have hin : List.map (Equiv.refl Bool).invFun (cod x) = x := by simp [cod]
    have hout : List.map (Equiv.refl Bool).invFun (cod (dec x)) = dec x := by simp [cod]
    refine ⟨⟨((dec x).length + 1) + kPar x, ?_⟩, ?_⟩
    · rw [hin, hout, initList_dec, Option.map_some, haltList_dec]
      show (flip bind stepD)^[((dec x).length + 1) + kPar x] (some (cfgD 0 x [])) = _
      rw [iterate_add_apply, hrun, hsai]
      rfl
    · have := dec_length_le x
      change (dec x).length + 1 + kPar x ≤ Polynomial.eval x.length (2 * Polynomial.X + 2)
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      omega


/-! ### P ⊆ NP -/

/-- **P ⊆ NP** sobre `Turing.FinTM2`: o verificador decodifica o primeiro componente do par e roda
o decisor de `L`; basta o certificado vazio (`q = 0`). -/
theorem P_sub_NP : classeP ⊆ classeNP := by
  rintro L ⟨χ, hχ, ⟨M⟩⟩
  refine ⟨{x | χ (dec x) = true}, ⟨χ ∘ dec, fun x => Iff.rfl,
    ⟨ClayPvsNPProof.ATK.ComposicaoTM2.comp decComputavel M⟩⟩, 0, fun w => ?_⟩
  simp only [Polynomial.eval_zero, Nat.le_zero, List.length_eq_zero_iff, Set.mem_ofPred_eq]
  constructor
  · intro hw; exact ⟨[], rfl, by rw [dec_par]; exact (hχ w).mp hw⟩
  · rintro ⟨c, rfl, hc⟩; rw [dec_par] at hc; exact (hχ w).mpr hc

/-! ### Reduções de Karp -/

/-- `A` reduz a `B` por uma função computável em tempo polinomial por uma `FinTM2`. -/
def Red (A B : Linguagem) : Prop :=
  ∃ f : Palavra → Palavra, (∀ w, w ∈ A ↔ f w ∈ B) ∧ Nonempty (TM2ComputableInPolyTime cod cod f)

/-- **P é fechada por reduções de Karp.** -/
theorem P_fechada_red {A B : Linguagem} (h : Red A B) (hB : B ∈ classeP) : A ∈ classeP := by
  obtain ⟨f, hf, ⟨Mf⟩⟩ := h
  obtain ⟨χ, hχ, ⟨M⟩⟩ := hB
  exact ⟨χ ∘ f, fun w => (hf w).trans (hχ (f w)), ⟨ClayPvsNPProof.ATK.ComposicaoTM2.comp Mf M⟩⟩

/-- Reduções de Karp são reflexivas (a identidade roda em tempo linear). -/
theorem red_refl (A : Linguagem) : Red A A :=
  ⟨id, fun _ => Iff.rfl, ⟨idComputableInPolyTime cod⟩⟩

/-- E transitivas (composição). -/
theorem red_trans {A B C : Linguagem} (h₁ : Red A B) (h₂ : Red B C) : Red A C := by
  obtain ⟨f, hf, ⟨Mf⟩⟩ := h₁
  obtain ⟨g, hg, ⟨Mg⟩⟩ := h₂
  exact ⟨g ∘ f, fun w => (hf w).trans (hg (f w)), ⟨ClayPvsNPProof.ATK.ComposicaoTM2.comp Mf Mg⟩⟩

/-! ### SAT -/

/-- Literal: índice da variável e polaridade (`true` = positivo). -/
abbrev Literal := ℕ × Bool
/-- Cláusula: disjunção de literais. -/
abbrev Clausula := List Literal
/-- Fórmula em CNF: conjunção de cláusulas. -/
abbrev CNF := List Clausula

/-- Uma valoração satisfaz a fórmula: cada cláusula tem um literal verdadeiro. -/
def Satisfaz (τ : ℕ → Bool) (φ : CNF) : Prop := ∀ C ∈ φ, ∃ ℓ ∈ C, τ ℓ.1 = ℓ.2

/-- A fórmula é satisfatível. -/
def Satisfativel (φ : CNF) : Prop := ∃ τ : ℕ → Bool, Satisfaz τ φ

/-- Codificação binária, com quatro símbolos de dois bits: `0 ↦ 00`, `1 ↦ 01`, fim de literal
`↦ 10`, fim de cláusula `↦ 11`. Um literal é a polaridade seguida dos bits do índice
(`Nat.bits`, menos significativo primeiro) e do fim de literal. -/
def simb (b : Bool) : List Bool := [false, b]
def codLiteral (ℓ : Literal) : List Bool :=
  simb ℓ.2 ++ (ℓ.1.bits.flatMap simb) ++ [true, false]
def codClausula (C : Clausula) : List Bool := C.flatMap codLiteral ++ [true, true]
def codCNF (φ : CNF) : List Bool := φ.flatMap codClausula

/-- **SAT**: as codificações das fórmulas CNF satisfatíveis. -/
def SAT : Linguagem := {x | ∃ φ : CNF, codCNF φ = x ∧ Satisfativel φ}

/-- Sanidade: a fórmula vazia é satisfatível; a cláusula vazia não. -/
theorem sat_vazia : codCNF [] ∈ SAT := ⟨[], rfl, ⟨fun _ => false, by simp [Satisfaz]⟩⟩

theorem clausula_vazia_insat : ¬ Satisfativel [[]] := by
  rintro ⟨τ, h⟩
  obtain ⟨ℓ, hℓ, _⟩ := h [] (by simp)
  simp at hℓ

/-! ### O modelo -/

/-- **O modelo genuíno de P vs NP** (ligação L2): linguagens binárias, P e NP sobre
`Turing.FinTM2` (as de `ClayPvsNPProof.ATK.LigacaoPNP`), reduções de Karp. -/
def modeloPNP : ClayPvsNPProof.ATK.Conditional.PvsNP.ComplexityModel.{0} where
  Lang := Linguagem
  P := classeP
  NP := classeNP
  Red := Red
  P_subset_NP := P_sub_NP
  P_closed_under_red := fun h hB => P_fechada_red h hB

/-- **Fidelidade**: o enunciado paramétrico sobre `modeloPNP` é, por definição, o enunciado
oficial `P ≠ NP` sobre máquinas de Turing (`ClayPvsNPProof.ATK.LigacaoPNP.PneNP`). -/
theorem fiel : ClayPvsNPProof.ATK.Conditional.PvsNP.PneNP modeloPNP ↔ ClayPvsNPProof.ATK.LigacaoPNP.PneNP := Iff.rfl

end ClayPvsNPProof.ATK.ModeloPNP

