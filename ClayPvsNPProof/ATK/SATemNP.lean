-- Origem: kernel ATK, espelho público ShantiDraconis/atk-math-core-public @ ffc111a
-- (= ShantiDraconis/M-Core @ 390e378), arquivo imports/M-Core/atk-kernel/ATK/SATemNP.lean
-- (sha256 do original: ab78922537c886f9…).
-- Alterações comuns: namespace `ATK.*` → `ClayPvsNPProof.ATK.*`; linhas `#print axioms` removidas
-- (a auditoria está em `ClayPvsNPProof/Audit.lean`). Alterações específicas: acrescentados os imports `Mathlib.Tactic.{Linarith,IntervalCases,Tauto}` (antes vinham transitivamente).
import ClayPvsNPProof.ATK.ModeloPNP
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto

/-!
# ATK — Ponte B4, marco M1: SAT ∈ NP no modelo genuíno

Primeira metade de Cook–Levin sobre as classes de `ClayPvsNPProof.ATK.LigacaoPNP` (máquinas `Turing.FinTM2`
da Mathlib, tempo polinomial), para a linguagem `ClayPvsNPProof.ATK.ModeloPNP.SAT` (CNF em binário, índices
de variável em `Nat.bits`, sem zeros à direita):

* **certificado esparso**: lista de entradas `(bits do índice, valor)` codificadas como literais,
  só para as variáveis que ocorrem na fórmula — tamanho `≤ |w|` (um vetor denso de atribuição
  teria tamanho exponencial, porque os índices vêm em binário);
* **busca por filtragem**: para cada bit de índice lido da fórmula, uma passada mantém as entradas
  cujo próximo bit coincide (`ftr`, `filt`); no fim do literal, vale a primeira entrada sem bits
  restantes (`lk`). O valor atribuído a `n` é uma função de `(c, n.bits)` (`val`), logo a
  consistência da atribuição é automática;
* **analisador** (`acc`) com checagem de canonicidade dos índices: aceita só codificações
  `codCNF φ` (`forma`), e sobre elas aceita exatamente quando cada cláusula tem um literal
  satisfeito (`acc_cnf`);
* `sat_iff`: `w ∈ SAT ↔ ∃ c, |c| ≤ |w| ∧ acc c none .p0 w = true`;
* **a máquina** `satTM` (4 pilhas, 18 rótulos) computa `verif` (`verif (par w c) = acc c …`)
  em no máximo `2 (n + 4)²` passos (`runTotal`, `verifComputavel`);
* `sat_em_NP : SAT ∈ classeNP` e `cookLevin_iff`: no modelo genuíno, a ponte B4
  (`CookLevin modeloPNP SAT`) equivale à NP-dificuldade de SAT (marco M2, provado em
  `ClayPvsNPProof.ATK.CookLevinNP.cookLevin`).

Nada aqui decide P vs NP. **CLOSED_MATH continua false.**
-/

namespace ClayPvsNPProof.ATK.SATemNP

def deBits : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (deBits l)

def Canonica (l : List Bool) : Prop := l = [] ∨ l.getLast? = some true

theorem deBits_bits (n : ℕ) : deBits n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [deBits]
  | bit b n h ih => rw [Nat.bits_append_bit n b h, deBits, ih]

theorem canonica_bits (n : ℕ) : Canonica n.bits := by
  induction n using Nat.binaryRec' with
  | zero => left; simp
  | bit b n h ih =>
    right
    rw [Nat.bits_append_bit n b h]
    rcases ih with h0 | h1
    · have hn : n = 0 := by
        by_contra hn
        have := deBits_bits n
        rw [h0] at this
        exact hn (by simpa [deBits] using this.symm)
      rw [h0]; simp [h hn]
    · rcases hb : n.bits with _ | ⟨x, xs⟩
      · rw [hb] at h1; simp at h1
      · rw [hb] at h1
        rw [List.getLast?_cons_cons]; exact h1

theorem deBits_ne_zero {l : List Bool} (hl : l ≠ []) (hc : Canonica l) : deBits l ≠ 0 := by
  induction l with
  | nil => exact absurd rfl hl
  | cons b l ih =>
    rcases hc with h | h
    · exact absurd h (by simp)
    · simp only [deBits]
      rcases l with _ | ⟨c, l⟩
      · simp at h; subst h; simp [Nat.bit]
      · have hc' : Canonica (c :: l) := Or.inr (by rwa [List.getLast?_cons_cons] at h)
        have := ih (by simp) hc'
        cases b <;> (simp [Nat.bit]; try omega)

theorem bits_deBits {l : List Bool} (hc : Canonica l) : (deBits l).bits = l := by
  induction l with
  | nil => simp [deBits]
  | cons b l ih =>
    simp only [deBits]
    rcases l with _ | ⟨c, l⟩
    · rcases hc with h | h
      · exact absurd h (by simp)
      · simp at h; subst h; simp [deBits, Nat.bit]
    · have hc' : Canonica (c :: l) := by
        rcases hc with h | h
        · exact absurd h (by simp)
        · exact Or.inr (by rwa [List.getLast?_cons_cons] at h)
      rw [Nat.bits_append_bit _ b (fun h0 => absurd h0 (deBits_ne_zero (by simp) hc')), ih hc']


open ClayPvsNPProof.ATK.LigacaoPNP ClayPvsNPProof.ATK.ModeloPNP

/-! ## Certificado: lista de entradas `(bits do índice, valor)` -/

abbrev Entrada := List Bool × Bool

def codEntrada (e : Entrada) : List Bool := [false, e.2] ++ e.1.flatMap simb ++ [true, false]

def codEntradas (E : List Entrada) : List Bool := E.flatMap codEntrada

/-- Modos do filtro (espelham os rótulos `E0`, `E1 x`, `Ec`, `Es` da máquina). -/
inductive MF | e0 | e1 (x : Bool) | ec | es

/-- Uma passada do filtro: mantém as entradas cujo próximo bit de índice é `b` (sem esse bit). -/
def ftr (b : Bool) : MF → List Bool → List Bool → List Bool × List Bool
  | .e0, false :: x :: W, T => ftr b (.e1 x) W T
  | .e0, _ :: _ :: W, T => (W, T)
  | .e0, _, T => ([], T)
  | .e1 x, false :: y :: W, T => if y = b then ftr b .ec W (x :: false :: T) else ftr b .es W T
  | .e1 _, true :: false :: W, T => ftr b .e0 W T
  | .e1 _, _ :: _ :: W, T => (W, T)
  | .e1 _, _, T => ([], T)
  | .ec, false :: y :: W, T => ftr b .ec W (y :: false :: T)
  | .ec, true :: false :: W, T => ftr b .e0 W (false :: true :: T)
  | .ec, _ :: _ :: W, T => (W, T)
  | .ec, _, T => ([], T)
  | .es, false :: _ :: W, T => ftr b .es W T
  | .es, true :: false :: W, T => ftr b .e0 W T
  | .es, _ :: _ :: W, T => (W, T)
  | .es, _, T => ([], T)

def filt (b : Bool) (W : List Bool) : List Bool := (ftr b .e0 W []).2.reverse ++ (ftr b .e0 W []).1

def filts (bs W : List Bool) : List Bool := bs.foldl (fun W b => filt b W) W

def filtE (b : Bool) (E : List Entrada) : List Entrada :=
  E.filterMap fun e => match e.1 with
    | c :: r => if c = b then some (r, e.2) else none
    | [] => none

def filtsE (bs : List Bool) (E : List Entrada) : List Entrada := bs.foldl (fun E b => filtE b E) E

theorem ftr_ec (b : Bool) : ∀ (bs W T : List Bool),
    ftr b .ec (bs.flatMap simb ++ [true, false] ++ W) T =
      ftr b .e0 W ((bs.flatMap simb ++ [true, false]).reverse ++ T)
  | [], W, T => by simp [ftr]
  | c :: bs, W, T => by
    have ih := ftr_ec b bs W (c :: false :: T)
    simp only [List.flatMap_cons, simb, List.cons_append, List.nil_append, List.append_assoc] at ih ⊢
    simp only [ftr]
    rw [ih]
    simp

theorem ftr_es (b : Bool) : ∀ (bs W T : List Bool),
    ftr b .es (bs.flatMap simb ++ [true, false] ++ W) T = ftr b .e0 W T
  | [], W, T => by simp [ftr]
  | c :: bs, W, T => by
    have ih := ftr_es b bs W T
    simp only [List.flatMap_cons, simb, List.cons_append, List.nil_append, List.append_assoc] at ih ⊢
    simp only [ftr]
    exact ih

theorem ftr_cod (b : Bool) : ∀ (E : List Entrada) (W T : List Bool),
    ftr b .e0 (codEntradas E ++ W) T = ftr b .e0 W ((codEntradas (filtE b E)).reverse ++ T)
  | [], W, T => by simp [codEntradas, filtE]
  | (bits, v) :: E, W, T => by
    rcases bits with _ | ⟨c, bs⟩
    · have ih := ftr_cod b E W T
      simp only [codEntradas, List.flatMap_cons, codEntrada, List.flatMap_nil, List.nil_append,
        List.cons_append] at ih ⊢
      simp only [ftr]
      rw [ih]
      simp [filtE]
    · simp only [codEntradas, List.flatMap_cons, codEntrada, List.cons_append, List.nil_append,
        List.append_assoc, simb]
      simp only [ftr]
      by_cases hc : c = b
      · simp only [hc, ite_true]
        have h1 := ftr_ec b bs (E.flatMap codEntrada ++ W) (v :: false :: T)
        simp only [List.append_assoc, List.cons_append, List.nil_append] at h1
        rw [h1]
        have h2 := ftr_cod b E W ((bs.flatMap simb ++ [true, false]).reverse ++ v :: false :: T)
        simp only [codEntradas] at h2
        rw [h2]
        subst hc
        simp [filtE, codEntrada]
      · simp only [hc, ite_false]
        have h1 := ftr_es b bs (E.flatMap codEntrada ++ W) T
        simp only [List.append_assoc, List.cons_append, List.nil_append] at h1
        rw [h1]
        have h2 := ftr_cod b E W T
        simp only [codEntradas] at h2
        rw [h2]
        simp [filtE, hc]

theorem filt_cod (b : Bool) (E : List Entrada) : filt b (codEntradas E) = codEntradas (filtE b E) := by
  have h := ftr_cod b E [] []
  simp only [List.append_nil] at h
  simp only [filt, h]
  simp [ftr]

theorem filts_cod : ∀ (bs : List Bool) (E : List Entrada),
    filts bs (codEntradas E) = codEntradas (filtsE bs E)
  | [], E => rfl
  | b :: bs, E => by
    simp only [filts, filtsE, List.foldl_cons] at *
    rw [filt_cod]
    exact filts_cod bs (filtE b E)

theorem mem_filtE (b : Bool) (E : List Entrada) (e : Entrada) :
    e ∈ filtE b E ↔ (b :: e.1, e.2) ∈ E := by
  simp only [filtE, List.mem_filterMap]
  constructor
  · rintro ⟨⟨bits, v⟩, hm, h⟩
    rcases bits with _ | ⟨c, r⟩
    · simp at h
    · simp only at h
      split_ifs at h with hc
      · simp only [Option.some.injEq] at h
        subst h hc
        exact hm
  · intro h
    exact ⟨(b :: e.1, e.2), h, by simp⟩

theorem mem_filtsE : ∀ (bs : List Bool) (E : List Entrada) (e : Entrada),
    e ∈ filtsE bs E ↔ (bs ++ e.1, e.2) ∈ E
  | [], E, e => by simp [filtsE]
  | b :: bs, E, e => by
    have ih := mem_filtsE bs (filtE b E) e
    simp only [filtsE, List.foldl_cons] at ih ⊢
    rw [ih, mem_filtE]
    simp

/-- Modos da busca (rótulos `L0`, `L1 x`, `Ls`). -/
inductive ML | l0 | l1 (x : Bool) | ls

/-- Busca: valor da primeira entrada sem bits de índice restantes. -/
def lk : ML → List Bool → Option Bool × List Bool
  | .l0, false :: x :: W => lk (.l1 x) W
  | .l0, _ :: _ :: W => (none, W)
  | .l0, _ => (none, [])
  | .l1 x, true :: false :: W => (some x, W)
  | .l1 _, false :: _ :: W => lk .ls W
  | .l1 _, _ :: _ :: W => (none, W)
  | .l1 _, _ => (none, [])
  | .ls, false :: _ :: W => lk .ls W
  | .ls, true :: false :: W => lk .l0 W
  | .ls, _ :: _ :: W => (none, W)
  | .ls, _ => (none, [])

def lookupE : List Entrada → Option Bool
  | [] => none
  | e :: E => if e.1 = [] then some e.2 else lookupE E

theorem lk_ls : ∀ (bs W : List Bool), lk .ls (bs.flatMap simb ++ [true, false] ++ W) = lk .l0 W
  | [], W => by simp [lk]
  | c :: bs, W => by
    have ih := lk_ls bs W
    simp only [List.flatMap_cons, simb, List.cons_append, List.nil_append, List.append_assoc] at ih ⊢
    simp only [lk]
    exact ih

theorem lk_cod : ∀ E : List Entrada, (lk .l0 (codEntradas E)).1 = lookupE E
  | [] => by simp [codEntradas, lk, lookupE]
  | (bits, v) :: E => by
    rcases bits with _ | ⟨c, bs⟩
    · simp [codEntradas, codEntrada, lk, lookupE]
    · have ih := lk_cod E
      simp only [codEntradas, List.flatMap_cons, codEntrada, List.cons_append, List.nil_append,
        List.append_assoc, simb] at ih ⊢
      simp only [lk]
      have h1 := lk_ls bs (E.flatMap codEntrada)
      simp only [List.append_assoc, List.cons_append, List.nil_append] at h1
      rw [h1, ih]
      simp [lookupE]

theorem lookupE_eq {v : Bool} : ∀ {E : List Entrada}, (∃ e ∈ E, e.1 = []) →
    (∀ e ∈ E, e.1 = [] → e.2 = v) → lookupE E = some v
  | [], ⟨_, h, _⟩, _ => by simp at h
  | e :: E, ⟨e', he', h'⟩, hv => by
    simp only [lookupE]
    split_ifs with h0
    · rw [hv e (by simp) h0]
    · rcases List.mem_cons.mp he' with h | h
      · subst h; exact absurd h' h0
      · exact lookupE_eq ⟨e', h, h'⟩ (fun e'' he'' => hv e'' (by simp [he'']))

/-- Valor atribuído pelo certificado `S` ao índice de bits `bs`. -/
def val (S bs : List Bool) : Option Bool := (lk .l0 (filts bs S.reverse)).1

/-! ## O verificador (função pura que espelha a máquina) -/

/-- Modo: `p0` = início de literal / fim de cláusula; `p1 v lb W` = lendo bits de índice. -/
inductive Md | p0 | p1 (v : Bool) (lb : Option Bool) (W : List Bool)

def acc (S : List Bool) : Option Bool → Md → List Bool → Bool
  | fl, .p0, false :: v :: G => acc S fl (.p1 v none S.reverse) G
  | fl, .p0, true :: true :: G => decide (fl = some true) && acc S none .p0 G
  | fl, .p0, [] => decide (fl = none)
  | _, .p0, _ => false
  | fl, .p1 v _ W, false :: b :: G => acc S fl (.p1 v (some b) (filt b W)) G
  | fl, .p1 v lb W, true :: false :: G =>
      !decide (lb = some false) &&
        acc S (some (fl.getD false || decide ((lk .l0 W).1 = some v))) .p0 G
  | _, .p1 _ _ _, _ => false

theorem getLast?_cons_or (c : Bool) (bs : List Bool) :
    (c :: bs).getLast? = bs.getLast?.or (some c) := by
  induction bs generalizing c with
  | nil => simp
  | cons d bs ih =>
    rw [List.getLast?_cons_cons, ih d]
    cases bs <;> simp

theorem acc_lit (S : List Bool) (fl : Option Bool) (v : Bool) : ∀ (bs : List Bool) (lb : Option Bool)
    (W G : List Bool),
    acc S fl (.p1 v lb W) (bs.flatMap simb ++ [true, false] ++ G) =
      (!decide (bs.getLast?.or lb = some false) &&
        acc S (some (fl.getD false || decide ((lk .l0 (filts bs W)).1 = some v))) .p0 G)
  | [], lb, W, G => by
    simp only [List.flatMap_nil, List.nil_append, List.cons_append, acc]
    rfl
  | c :: bs, lb, W, G => by
    have ih := acc_lit S fl v bs (some c) (filt c W) G
    simp only [List.flatMap_cons, simb, List.cons_append, List.nil_append, List.append_assoc] at ih ⊢
    simp only [acc]
    rw [ih, getLast?_cons_or]
    have hor : (bs.getLast?.or (some c)).or lb = bs.getLast?.or (some c) := by
      cases bs.getLast? <;> rfl
    rw [hor]
    rfl

/-- Predicado "o literal é satisfeito pelo certificado". -/
def bom (S : List Bool) (ℓ : Literal) : Bool := decide (val S ℓ.1.bits = some ℓ.2)

def passoFl (S : List Bool) (fl : Option Bool) (ℓ : Literal) : Option Bool :=
  some (fl.getD false || bom S ℓ)

theorem lb_canon (n : ℕ) : (n.bits.getLast?.or none) ≠ some false := by
  rcases canonica_bits n with h | h
  · rw [h]; simp
  · rw [h]; simp

theorem acc_cla (S : List Bool) : ∀ (C : Clausula) (fl : Option Bool) (G : List Bool),
    acc S fl .p0 (C.flatMap codLiteral ++ G) = acc S (C.foldl (passoFl S) fl) .p0 G
  | [], fl, G => by simp
  | ℓ :: C, fl, G => by
    simp only [List.flatMap_cons, codLiteral, simb, List.cons_append, List.nil_append,
      List.append_assoc, List.foldl_cons]
    simp only [acc]
    have h := acc_lit S fl ℓ.2 ℓ.1.bits none S.reverse (C.flatMap codLiteral ++ G)
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h
    rw [h]
    have hc : decide (ℓ.1.bits.getLast?.or none = some false) = false := by
      simpa using lb_canon ℓ.1
    rw [hc, Bool.not_false, Bool.true_and, acc_cla S C]
    rfl

theorem foldl_passo (S : List Bool) : ∀ (C : Clausula) (fl : Option Bool),
    C.foldl (passoFl S) fl = if C = [] then fl else some (fl.getD false || C.any (bom S))
  | [], fl => by simp
  | ℓ :: C, fl => by
    rw [List.foldl_cons, foldl_passo S C]
    by_cases hC : C = []
    · subst hC; simp [passoFl]
    · simp [hC, passoFl, Bool.or_assoc]

theorem dec_some (a : Bool) : decide (some a = some true) = a := by cases a <;> rfl

theorem acc_cnf (S : List Bool) : ∀ φ : CNF,
    acc S none .p0 (codCNF φ) = φ.all fun C => C.any (bom S)
  | [] => by simp [codCNF, acc]
  | C :: φ => by
    simp only [codCNF, List.flatMap_cons, codClausula, List.append_assoc]
    rw [acc_cla, foldl_passo]
    have ih := acc_cnf S φ
    simp only [codCNF] at ih
    by_cases hC : C = []
    · subst hC; simp [acc]
    · simp only [hC, ite_false]
      simp only [List.cons_append, List.nil_append]
      simp only [acc]
      rw [ih, Option.getD_none, Bool.false_or, dec_some, List.all_cons]

/-- **Correção do analisador**: o que o verificador aceita é a codificação de uma CNF. -/
theorem forma (S : List Bool) : ∀ (n : ℕ) (G : List Bool), G.length ≤ n →
    (∀ fl, acc S fl .p0 G = true →
      (fl = none → ∃ φ : CNF, codCNF φ = G) ∧
      (fl ≠ none → ∃ (C : Clausula) (φ : CNF), codClausula C ++ codCNF φ = G)) ∧
    (∀ fl v (pre W : List Bool), acc S fl (.p1 v pre.getLast? W) G = true →
      ∃ (bs G' : List Bool), G = bs.flatMap simb ++ [true, false] ++ G' ∧ Canonica (pre ++ bs) ∧
        ∃ fl', fl' ≠ none ∧ acc S fl' .p0 G' = true)
  | 0, G, hG => by
    rw [Nat.le_zero, List.length_eq_zero_iff] at hG
    subst hG
    refine ⟨fun fl h => ⟨fun _ => ⟨[], rfl⟩, fun hfl => ?_⟩, fun fl v pre W h => ?_⟩
    · simp [acc] at h; exact absurd h hfl
    · simp [acc] at h
  | n + 1, G, hG => by
    rcases G with _ | ⟨a, _ | ⟨b, G⟩⟩
    · refine ⟨fun fl h => ⟨fun _ => ⟨[], rfl⟩, fun hfl => ?_⟩, fun fl v pre W h => ?_⟩
      · simp [acc] at h; exact absurd h hfl
      · simp [acc] at h
    · refine ⟨fun fl h => ?_, fun fl v pre W h => ?_⟩
      · cases a <;> simp [acc] at h
      · cases a <;> simp [acc] at h
    · have hG' : G.length ≤ n := by simp at hG; omega
      have ih := forma S n G hG'
      refine ⟨fun fl h => ?_, fun fl v pre W h => ?_⟩
      · cases a
        · -- literal
          simp only [acc] at h
          have h1 := ih.2 fl b [] S.reverse (by simpa using h)
          obtain ⟨bs, G', hGe, hcan, fl', hfl', hacc⟩ := h1
          have hlen : G'.length ≤ n := by
            have := congrArg List.length hGe; simp at this; omega
          obtain ⟨C, φ, hCφ⟩ := ((forma S n G' hlen).1 fl' hacc).2 hfl'
          have hcan' : Canonica bs := by simpa using hcan
          have hlit : codLiteral (deBits bs, b) = [false, b] ++ bs.flatMap simb ++ [true, false] := by
            simp [codLiteral, simb, bits_deBits hcan']
          refine ⟨fun _ => ⟨((deBits bs, b) :: C) :: φ, ?_⟩, fun _ => ⟨(deBits bs, b) :: C, φ, ?_⟩⟩
          · rw [hGe, ← hCφ]
            simp [codCNF, codClausula, hlit]
          · rw [hGe, ← hCφ]
            simp [codClausula, hlit]
        · cases b
          · simp [acc] at h
          · simp only [acc] at h
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨hfl, hacc⟩ := h
            obtain ⟨φ, hφ⟩ := (ih.1 none hacc).1 rfl
            refine ⟨fun h0 => by rw [h0] at hfl; exact absurd hfl (by simp), fun _ => ⟨[], φ, ?_⟩⟩
            rw [← hφ]; simp [codClausula]
      · cases a
        · simp only [acc] at h
          have hl : (some b : Option Bool) = (pre ++ [b]).getLast? := by simp
          rw [hl] at h
          obtain ⟨bs, G', hGe, hcan, rest⟩ := ih.2 fl v (pre ++ [b]) (filt b W) h
          refine ⟨b :: bs, G', ?_, by simpa using hcan, rest⟩
          rw [hGe]; simp [simb]
        · cases b
          · simp only [acc] at h
            simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
            obtain ⟨hlb, hacc⟩ := h
            refine ⟨[], G, by simp, ?_, _, by simp, hacc⟩
            simp only [List.append_nil, Canonica]
            rcases hp : pre.getLast? with _ | ⟨_ | _⟩
            · left; simpa using hp
            · rw [hp] at hlb; exact absurd rfl hlb
            · right; rfl
          · simp [acc] at h

/-! ## Separação do par e o verificador final -/

/-- Segundo componente do par (espelha a máquina de leitura). -/
def resto : List Bool → List Bool
  | a :: b :: r => if a = b then resto r else r
  | _ => []

theorem resto_par (w c : Palavra) : resto (par w c) = c := by
  induction w with
  | nil => simp [par, resto]
  | cons b w ih =>
    simp only [par, List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc] at ih ⊢
    rw [resto]; simp [ih]

theorem resto_length_le : ∀ x : List Bool, (resto x).length ≤ x.length
  | a :: b :: r => by
    simp only [resto, List.length_cons]
    split_ifs
    · have := resto_length_le r; omega
    · omega
  | [_] => by simp [resto]
  | [] => by simp [resto]

/-- **O verificador de SAT**: separa o par `⟨w, c⟩` e roda o analisador com o certificado `c`. -/
def verif (x : List Bool) : Bool := acc (resto x) none .p0 (dec x)

theorem verif_par (w c : Palavra) : verif (par w c) = acc c none .p0 w := by
  simp [verif, dec_par, resto_par]

theorem bits_inj {m n : ℕ} (h : m.bits = n.bits) : m = n := by
  rw [← deBits_bits m, h, deBits_bits]

theorem codEntradas_len (τ : ℕ → Bool) : ∀ C : Clausula,
    (codEntradas (C.map fun ℓ => (ℓ.1.bits, τ ℓ.1))).length = (C.flatMap codLiteral).length
  | [] => by simp [codEntradas]
  | ℓ :: C => by
    have := codEntradas_len τ C
    simp only [codEntradas] at this ⊢
    simp [codEntrada, codLiteral, simb, this]

theorem len_cert (τ : ℕ → Bool) : ∀ φ : CNF,
    (codEntradas (φ.flatMap fun C => C.map fun ℓ => (ℓ.1.bits, τ ℓ.1))).length ≤ (codCNF φ).length
  | [] => by simp [codEntradas, codCNF]
  | C :: φ => by
    have ih := len_cert τ φ
    have hC := codEntradas_len τ C
    simp only [codEntradas, codCNF, List.flatMap_cons, List.flatMap_append, List.length_append,
      codClausula] at ih hC ⊢
    omega

/-- **SAT com certificados**: `w ∈ SAT` ⟺ existe certificado `c` com `|c| ≤ |w|` aceito. -/
theorem sat_iff (w : Palavra) :
    w ∈ SAT ↔ ∃ c : Palavra, c.length ≤ w.length ∧ acc c none .p0 w = true := by
  constructor
  · rintro ⟨φ, rfl, τ, hτ⟩
    let E : List Entrada := φ.flatMap fun C => C.map fun ℓ => (ℓ.1.bits, τ ℓ.1)
    refine ⟨(codEntradas E).reverse, ?_, ?_⟩
    · rw [List.length_reverse]
      exact len_cert τ φ
    · rw [acc_cnf, List.all_eq_true]
      intro C hC
      obtain ⟨ℓ, hℓ, hℓv⟩ := hτ C hC
      rw [List.any_eq_true]
      refine ⟨ℓ, hℓ, ?_⟩
      simp only [bom, decide_eq_true_eq, val, List.reverse_reverse, filts_cod, lk_cod]
      apply lookupE_eq
      · refine ⟨([], τ ℓ.1), ?_, rfl⟩
        rw [mem_filtsE]
        simp only [List.append_nil, E, List.mem_flatMap, List.mem_map]
        exact ⟨C, hC, ℓ, hℓ, rfl⟩
      · intro e he he0
        rw [mem_filtsE, he0, List.append_nil] at he
        simp only [E, List.mem_flatMap, List.mem_map, Prod.mk.injEq] at he
        obtain ⟨C', _, ℓ', _, hb, hv⟩ := he
        rw [← hv, bits_inj hb, hℓv]
  · rintro ⟨c, _, h⟩
    obtain ⟨φ, rfl⟩ := ((forma c w.length w le_rfl).1 none h).1 rfl
    refine ⟨φ, rfl, fun n => decide (val c n.bits = some true), ?_⟩
    rw [acc_cnf, List.all_eq_true] at h
    intro C hC
    obtain ⟨ℓ, hℓ, hb⟩ := List.any_eq_true.mp (h C hC)
    refine ⟨ℓ, hℓ, ?_⟩
    simp only [bom, decide_eq_true_eq] at hb
    show decide (val c ℓ.1.bits = some true) = ℓ.2
    rw [hb, dec_some]


/-! ## A máquina verificadora (`Turing.FinTM2`) -/

open Turing Function

/-- Pilhas: `s` entrada/certificado/saída, `g` fórmula, `w` cópia de trabalho, `t` auxiliar. -/
inductive Pk | s | g | w | t
  deriving DecidableEq

instance : Fintype Pk := ⟨⟨{Pk.s, Pk.g, Pk.w, Pk.t}, by decide⟩, fun k => by cases k <;> decide⟩

/-- Rótulos. -/
inductive Lb
  | U | R | P0 | P1 | C1 | C2 | E0 | E1 (x : Bool) | Ec | Es | F2 | L0 | L1 (x : Bool) | Ls | X
  | Zs | Zg | Zw
  deriving DecidableEq, Fintype

/-- Estado persistente. -/
structure St where
  v : Bool
  b : Bool
  ok : Bool
  fl : Option Bool
  lb : Option Bool
  deriving DecidableEq, Fintype

abbrev Sg := Option Bool × Option Bool × St
abbrev Gm : Pk → Type := fun _ => Bool
abbrev Stm := Turing.TM2.Stmt Gm Lb Sg

def st0 : St := ⟨false, false, false, none, none⟩

open Turing.TM2.Stmt in
def ir (l : Lb) : Stm := load (fun σ => (none, none, σ.2.2)) (goto fun _ => l)

open Turing.TM2.Stmt in
def irS (f : St → St) (l : Lb) : Stm := load (fun σ => (none, none, f σ.2.2)) (goto fun _ => l)

open Turing.TM2.Stmt in
/-- Lê um símbolo de dois bits da pilha `k`. -/
def rd2 (k : Pk) (bit : Bool → Stm) (fim fc mau : Stm) : Stm :=
  pop k (fun σ o => (o, σ.2)) <| pop k (fun σ o => (σ.1, o, σ.2.2)) <|
    branch (fun σ => decide (σ.1 = some false))
      (branch (fun σ => decide (σ.2.1 = some false)) (bit false)
        (branch (fun σ => decide (σ.2.1 = some true)) (bit true) mau))
      (branch (fun σ => decide (σ.1 = some true))
        (branch (fun σ => decide (σ.2.1 = some false)) fim
          (branch (fun σ => decide (σ.2.1 = some true)) fc mau))
        mau)

def falha : Stm := irS (fun st => {st with ok := false}) .Zs

def nf : Stm := irS (fun st => {st with fl := some (st.fl.getD false)}) .X

open Turing.TM2.Stmt in
def prog : Lb → Stm
  | .U => pop .s (fun σ o => (o, σ.2)) <| pop .s (fun σ o => (σ.1, o, σ.2.2)) <|
      branch (fun σ => σ.1.isSome && decide (σ.1 = σ.2.1))
        (push .t (fun σ => σ.1.getD false) (ir .U)) (ir .R)
  | .R => pop .t (fun σ o => (o, σ.2)) <|
      branch (fun σ => σ.1.isSome) (push .g (fun σ => σ.1.getD false) (ir .R)) (ir .P0)
  | .P0 => rd2 .g (fun v => irS (fun st => {st with v := v, lb := none}) .C1) falha
      (branch (fun σ => decide (σ.2.2.fl = some true)) (irS (fun st => {st with fl := none}) .P0)
        falha)
      (branch (fun σ => σ.1.isNone) (irS (fun st => {st with ok := decide (st.fl = none)}) .Zs)
        falha)
  | .C1 => pop .s (fun σ o => (o, σ.2)) <|
      branch (fun σ => σ.1.isSome)
        (push .w (fun σ => σ.1.getD false) (push .t (fun σ => σ.1.getD false) (ir .C1))) (ir .C2)
  | .C2 => pop .t (fun σ o => (o, σ.2)) <|
      branch (fun σ => σ.1.isSome) (push .s (fun σ => σ.1.getD false) (ir .C2)) (ir .P1)
  | .P1 => rd2 .g (fun b => irS (fun st => {st with b := b, lb := some b}) .E0)
      (branch (fun σ => decide (σ.2.2.lb = some false)) falha (ir .L0)) falha falha
  | .E0 => rd2 .w (fun x => ir (.E1 x)) (ir .F2) (ir .F2) (ir .F2)
  | .E1 x => rd2 .w (fun y => branch (fun σ => decide (σ.2.2.b = y))
        (push .t (fun _ => false) (push .t (fun _ => x) (ir .Ec))) (ir .Es))
      (ir .E0) (ir .F2) (ir .F2)
  | .Ec => rd2 .w (fun y => push .t (fun _ => false) (push .t (fun _ => y) (ir .Ec)))
      (push .t (fun _ => true) (push .t (fun _ => false) (ir .E0))) (ir .F2) (ir .F2)
  | .Es => rd2 .w (fun _ => ir .Es) (ir .E0) (ir .F2) (ir .F2)
  | .F2 => pop .t (fun σ o => (o, σ.2)) <|
      branch (fun σ => σ.1.isSome) (push .w (fun σ => σ.1.getD false) (ir .F2)) (ir .P1)
  | .L0 => rd2 .w (fun x => ir (.L1 x)) nf nf nf
  | .L1 x => rd2 .w (fun _ => ir .Ls)
      (irS (fun st => {st with fl := some (st.fl.getD false || decide (x = st.v))}) .X) nf nf
  | .Ls => rd2 .w (fun _ => ir .Ls) (ir .L0) nf nf
  | .X => pop .w (fun σ o => (o, σ.2)) <| branch (fun σ => σ.1.isSome) (ir .X) (ir .P0)
  | .Zs => pop .s (fun σ o => (o, σ.2)) <| branch (fun σ => σ.1.isSome) (ir .Zs) (ir .Zg)
  | .Zg => pop .g (fun σ o => (o, σ.2)) <| branch (fun σ => σ.1.isSome) (ir .Zg) (ir .Zw)
  | .Zw => pop .w (fun σ o => (o, σ.2)) <| branch (fun σ => σ.1.isSome) (ir .Zw)
      (push .s (fun σ => σ.2.2.ok) (load (fun _ => (none, none, st0)) halt))

/-- **A máquina verificadora de SAT**. -/
abbrev satTM : FinTM2 where
  K := Pk
  k₀ := .s
  k₁ := .s
  Γ := Gm
  Λ := Lb
  main := .U
  σ := Sg
  initialState := (none, none, st0)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := prog

def stks (s g w t : List Bool) : Pk → List Bool
  | .s => s
  | .g => g
  | .w => w
  | .t => t

@[simp] theorem stks_s (s g w t) : stks s g w t .s = s := rfl
@[simp] theorem stks_g (s g w t) : stks s g w t .g = g := rfl
@[simp] theorem stks_w (s g w t) : stks s g w t .w = w := rfl
@[simp] theorem stks_t (s g w t) : stks s g w t .t = t := rfl

@[simp] theorem upd_s (s g w t x) : update (stks s g w t) Pk.s x = stks x g w t := by
  funext k; cases k <;> rfl
@[simp] theorem upd_g (s g w t x) : update (stks s g w t) Pk.g x = stks s x w t := by
  funext k; cases k <;> rfl
@[simp] theorem upd_w (s g w t x) : update (stks s g w t) Pk.w x = stks s g x t := by
  funext k; cases k <;> rfl
@[simp] theorem upd_t (s g w t x) : update (stks s g w t) Pk.t x = stks s g w x := by
  funext k; cases k <;> rfl

abbrev Cf := Turing.TM2.Cfg Gm Lb Sg

def cf (l : Lb) (st : St) (s g w t : List Bool) : Cf := ⟨some l, (none, none, st), stks s g w t⟩

abbrev stp := Turing.TM2.step prog

theorem stp_cf (l : Lb) (st : St) (s g w t : List Bool) :
    stp (cf l st s g w t) = some (TM2.stepAux (prog l) (none, none, st) (stks s g w t)) := rfl

/-! ### Leitura de dois bits -/

section rd2
variable {k : Pk} {bit : Bool → Stm} {fim fc mau : Stm} {st : St} {S : Pk → List Bool}

theorem rd2_bit {x : Bool} {W : List Bool} (h : S k = false :: x :: W) :
    TM2.stepAux (rd2 k bit fim fc mau) (none, none, st) S =
      TM2.stepAux (bit x) (some false, some x, st) (update S k W) := by
  cases x <;> simp [rd2, TM2.stepAux, h, update_idem]

theorem rd2_fim {W : List Bool} (h : S k = true :: false :: W) :
    TM2.stepAux (rd2 k bit fim fc mau) (none, none, st) S =
      TM2.stepAux fim (some true, some false, st) (update S k W) := by
  simp [rd2, TM2.stepAux, h, update_idem]

theorem rd2_fc {W : List Bool} (h : S k = true :: true :: W) :
    TM2.stepAux (rd2 k bit fim fc mau) (none, none, st) S =
      TM2.stepAux fc (some true, some true, st) (update S k W) := by
  simp [rd2, TM2.stepAux, h, update_idem]

theorem rd2_nil (h : S k = []) :
    TM2.stepAux (rd2 k bit fim fc mau) (none, none, st) S =
      TM2.stepAux mau (none, none, st) (update S k []) := by
  simp [rd2, TM2.stepAux, h, update_idem]

theorem rd2_one {a : Bool} (h : S k = [a]) :
    TM2.stepAux (rd2 k bit fim fc mau) (none, none, st) S =
      TM2.stepAux mau (some a, none, st) (update S k []) := by
  cases a <;> simp [rd2, TM2.stepAux, h, update_idem]

end rd2

/-! ### Execuções com cota de passos -/

/-- `c` chega a `c'` em no máximo `B` passos. -/
def Run (c c' : Cf) (B : ℕ) : Prop := ∃ n ≤ B, (flip bind stp)^[n] (some c) = some c'

theorem Run.refl (c : Cf) : Run c c 0 := ⟨0, le_rfl, rfl⟩

theorem Run.trans {c₁ c₂ c₃ : Cf} {B₁ B₂ : ℕ} (h₁ : Run c₁ c₂ B₁) (h₂ : Run c₂ c₃ B₂) :
    Run c₁ c₃ (B₁ + B₂) := by
  obtain ⟨n₁, hn₁, e₁⟩ := h₁
  obtain ⟨n₂, hn₂, e₂⟩ := h₂
  exact ⟨n₂ + n₁, by omega, by rw [iterate_add_apply, e₁, e₂]⟩

theorem Run.mono {c c' : Cf} {B B' : ℕ} (h : Run c c' B) (hB : B ≤ B') : Run c c' B' := by
  obtain ⟨n, hn, e⟩ := h
  exact ⟨n, hn.trans hB, e⟩

theorem Run.passo {c c' c'' : Cf} {B : ℕ} (h : stp c = some c') (h' : Run c' c'' B) :
    Run c c'' (B + 1) := by
  obtain ⟨n, hn, e⟩ := h'
  exact ⟨n + 1, by omega, by rw [iterate_succ_apply]; exact (congrArg _ h).trans e⟩

theorem Run.um {c c' : Cf} (h : stp c = some c') : Run c c' 1 := Run.passo h (Run.refl c')


/-! ### Laços simples -/

section lacos
variable (st : St)

theorem runU (G W : List Bool) : ∀ x T : List Bool,
    Run (cf .U st x G W T) (cf .R st (resto x) G W ((dec x).reverse ++ T)) (x.length + 1)
  | a :: b :: r, T => by
    by_cases h : a = b
    · subst h
      have hs : stp (cf .U st (a :: a :: r) G W T) = some (cf .U st r G W (a :: T)) := by
        cases a <;> simp [prog, TM2.stepAux, ir, cf]
      have := Run.passo hs (runU G W r (a :: T))
      simp only [resto, dec, ite_true, List.reverse_cons, List.append_assoc, List.cons_append,
        List.nil_append, List.length_cons] at this ⊢
      exact this.mono (by omega)
    · have hs : stp (cf .U st (a :: b :: r) G W T) = some (cf .R st r G W T) := by
        cases a <;> cases b <;> simp_all [prog, TM2.stepAux, ir, cf]
      have h' : Run (cf .U st (a :: b :: r) G W T) (cf .R st r G W T) ((a :: b :: r).length + 1) :=
        (Run.um hs).mono (by simp)
      simpa [resto, dec, h] using h'
  | [a], T => by
    have hs : stp (cf .U st [a] G W T) = some (cf .R st [] G W T) := by
      cases a <;> simp [prog, TM2.stepAux, ir, cf]
    simpa [resto, dec] using (Run.um hs).mono (by simp)
  | [], T => by
    have hs : stp (cf .U st [] G W T) = some (cf .R st [] G W T) := by
      simp [prog, TM2.stepAux, ir, cf]
    simpa [resto, dec] using (Run.um hs).mono (by simp)

theorem runR (S W : List Bool) : ∀ T G : List Bool,
    Run (cf .R st S G W T) (cf .P0 st S (T.reverse ++ G) W []) (T.length + 1)
  | a :: T, G => by
    have hs : stp (cf .R st S G W (a :: T)) = some (cf .R st S (a :: G) W T) := by
      simp [prog, TM2.stepAux, ir, cf]
    have := Run.passo hs (runR S W T (a :: G))
    simpa using this
  | [], G => by
    have hs : stp (cf .R st S G W []) = some (cf .P0 st S G W []) := by
      simp [prog, TM2.stepAux, ir, cf]
    simpa using Run.um hs

theorem runC1 (G : List Bool) : ∀ S W T : List Bool,
    Run (cf .C1 st S G W T) (cf .C2 st [] G (S.reverse ++ W) (S.reverse ++ T)) (S.length + 1)
  | a :: S, W, T => by
    have hs : stp (cf .C1 st (a :: S) G W T) = some (cf .C1 st S G (a :: W) (a :: T)) := by
      simp [prog, TM2.stepAux, ir, cf]
    have := Run.passo hs (runC1 G S (a :: W) (a :: T))
    simpa using this
  | [], W, T => by
    have hs : stp (cf .C1 st [] G W T) = some (cf .C2 st [] G W T) := by
      simp [prog, TM2.stepAux, ir, cf]
    simpa using Run.um hs

theorem runC2 (G W : List Bool) : ∀ T S : List Bool,
    Run (cf .C2 st S G W T) (cf .P1 st (T.reverse ++ S) G W []) (T.length + 1)
  | a :: T, S => by
    have hs : stp (cf .C2 st S G W (a :: T)) = some (cf .C2 st (a :: S) G W T) := by
      simp [prog, TM2.stepAux, ir, cf]
    have := Run.passo hs (runC2 G W T (a :: S))
    simpa using this
  | [], S => by
    have hs : stp (cf .C2 st S G W []) = some (cf .P1 st S G W []) := by
      simp [prog, TM2.stepAux, ir, cf]
    simpa using Run.um hs

theorem runF2 (S G : List Bool) : ∀ T W : List Bool,
    Run (cf .F2 st S G W T) (cf .P1 st S G (T.reverse ++ W) []) (T.length + 1)
  | a :: T, W => by
    have hs : stp (cf .F2 st S G W (a :: T)) = some (cf .F2 st S G (a :: W) T) := by
      simp [prog, TM2.stepAux, ir, cf]
    have := Run.passo hs (runF2 S G T (a :: W))
    simpa using this
  | [], W => by
    have hs : stp (cf .F2 st S G W []) = some (cf .P1 st S G W []) := by
      simp [prog, TM2.stepAux, ir, cf]
    simpa using Run.um hs

theorem runX (S G T : List Bool) : ∀ W : List Bool,
    Run (cf .X st S G W T) (cf .P0 st S G [] T) (W.length + 1)
  | a :: W => by
    have hs : stp (cf .X st S G (a :: W) T) = some (cf .X st S G W T) := by
      simp [prog, TM2.stepAux, ir, cf]
    simpa using Run.passo hs (runX S G T W)
  | [] => by
    have hs : stp (cf .X st S G [] T) = some (cf .P0 st S G [] T) := by
      simp [prog, TM2.stepAux, ir, cf]
    simpa using Run.um hs

theorem runZs (G W T : List Bool) : ∀ S : List Bool,
    Run (cf .Zs st S G W T) (cf .Zg st [] G W T) (S.length + 1)
  | a :: S => by
    have hs : stp (cf .Zs st (a :: S) G W T) = some (cf .Zs st S G W T) := by
      simp [prog, TM2.stepAux, ir, cf]
    simpa using Run.passo hs (runZs G W T S)
  | [] => by
    have hs : stp (cf .Zs st [] G W T) = some (cf .Zg st [] G W T) := by
      simp [prog, TM2.stepAux, ir, cf]
    simpa using Run.um hs

theorem runZg (S W T : List Bool) : ∀ G : List Bool,
    Run (cf .Zg st S G W T) (cf .Zw st S [] W T) (G.length + 1)
  | a :: G => by
    have hs : stp (cf .Zg st S (a :: G) W T) = some (cf .Zg st S G W T) := by
      simp [prog, TM2.stepAux, ir, cf]
    simpa using Run.passo hs (runZg S W T G)
  | [] => by
    have hs : stp (cf .Zg st S [] W T) = some (cf .Zw st S [] W T) := by
      simp [prog, TM2.stepAux, ir, cf]
    simpa using Run.um hs

/-- Configuração final: só a pilha de saída, com `[ok]`. -/
def cfFim (b : Bool) : Cf := ⟨none, (none, none, st0), stks [b] [] [] []⟩

theorem runZw : ∀ W : List Bool,
    Run (cf .Zw st [] [] W []) (cfFim st.ok) (W.length + 1)
  | a :: W => by
    have hs : stp (cf .Zw st [] [] (a :: W) []) = some (cf .Zw st [] [] W []) := by
      simp [prog, TM2.stepAux, ir, cf]
    simpa using Run.passo hs (runZw W)
  | [] => by
    have hs : stp (cf .Zw st [] [] [] []) = some (cfFim st.ok) := by
      simp [prog, TM2.stepAux, ir, cf, cfFim]
    simpa using Run.um hs

end lacos


/-! ### Filtro e busca -/

def lblF : MF → Lb
  | .e0 => .E0
  | .e1 x => .E1 x
  | .ec => .Ec
  | .es => .Es

section filtro
variable (st : St) (S G : List Bool)

theorem runF : ∀ (m : MF) (W T : List Bool),
    Run (cf (lblF m) st S G W T) (cf .F2 st S G (ftr st.b m W T).1 (ftr st.b m W T).2)
      (W.length + 1)
  | .e0, false :: x :: W, T => by
    have hs : stp (cf .E0 st S G (false :: x :: W) T) = some (cf (.E1 x) st S G W T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_bit (stks_w S G (false :: x :: W) T)]
      simp [ir, TM2.stepAux, cf]
    have := Run.passo hs (runF (.e1 x) W T)
    simp only [ftr]
    exact this.mono (by simp)
  | .e0, true :: y :: W, T => by
    have hs : stp (cf .E0 st S G (true :: y :: W) T) = some (cf .F2 st S G W T) := by
      rw [stp_cf]; simp only [prog]
      cases y
      · rw [rd2_fim (stks_w S G (true :: false :: W) T)]; simp [ir, TM2.stepAux, cf]
      · rw [rd2_fc (stks_w S G (true :: true :: W) T)]; simp [ir, TM2.stepAux, cf]
    simp only [ftr]
    exact (Run.um hs).mono (by simp)
  | .e0, [a], T => by
    have hs : stp (cf .E0 st S G [a] T) = some (cf .F2 st S G [] T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_one (stks_w S G [a] T)]; simp [ir, TM2.stepAux, cf]
    simp only [ftr]
    exact (Run.um hs).mono (by simp)
  | .e0, [], T => by
    have hs : stp (cf .E0 st S G [] T) = some (cf .F2 st S G [] T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_nil (stks_w S G [] T)]; simp [ir, TM2.stepAux, cf]
    simp only [ftr]
    exact (Run.um hs).mono (by simp)
  | .e1 x, false :: y :: W, T => by
    by_cases hy : y = st.b
    · subst hy
      have hs : stp (cf (.E1 x) st S G (false :: st.b :: W) T) =
          some (cf .Ec st S G W (x :: false :: T)) := by
        rw [stp_cf]; simp only [prog]; rw [rd2_bit (stks_w S G (false :: st.b :: W) T)]
        simp [ir, TM2.stepAux, cf]
      have := Run.passo hs (runF .ec W (x :: false :: T))
      simp only [ftr, ite_true]
      exact this.mono (by simp)
    · have hs : stp (cf (.E1 x) st S G (false :: y :: W) T) = some (cf .Es st S G W T) := by
        rw [stp_cf]; simp only [prog]; rw [rd2_bit (stks_w S G (false :: y :: W) T)]
        have hy' : ¬ st.b = y := fun h => hy h.symm
        simp [ir, TM2.stepAux, cf, hy']
      have := Run.passo hs (runF .es W T)
      simp only [ftr, hy, ite_false]
      exact this.mono (by simp)
  | .e1 x, true :: false :: W, T => by
    have hs : stp (cf (.E1 x) st S G (true :: false :: W) T) = some (cf .E0 st S G W T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_fim (stks_w S G (true :: false :: W) T)]
      simp [ir, TM2.stepAux, cf]
    have := Run.passo hs (runF .e0 W T)
    simp only [ftr]
    exact this.mono (by simp)
  | .e1 x, true :: true :: W, T => by
    have hs : stp (cf (.E1 x) st S G (true :: true :: W) T) = some (cf .F2 st S G W T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_fc (stks_w S G (true :: true :: W) T)]
      simp [ir, TM2.stepAux, cf]
    simp only [ftr]
    exact (Run.um hs).mono (by simp)
  | .e1 x, [a], T => by
    have hs : stp (cf (.E1 x) st S G [a] T) = some (cf .F2 st S G [] T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_one (stks_w S G [a] T)]; simp [ir, TM2.stepAux, cf]
    simp only [ftr]
    exact (Run.um hs).mono (by simp)
  | .e1 x, [], T => by
    have hs : stp (cf (.E1 x) st S G [] T) = some (cf .F2 st S G [] T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_nil (stks_w S G [] T)]; simp [ir, TM2.stepAux, cf]
    simp only [ftr]
    exact (Run.um hs).mono (by simp)
  | .ec, false :: y :: W, T => by
    have hs : stp (cf .Ec st S G (false :: y :: W) T) = some (cf .Ec st S G W (y :: false :: T)) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_bit (stks_w S G (false :: y :: W) T)]
      simp [ir, TM2.stepAux, cf]
    have := Run.passo hs (runF .ec W (y :: false :: T))
    simp only [ftr]
    exact this.mono (by simp)
  | .ec, true :: false :: W, T => by
    have hs : stp (cf .Ec st S G (true :: false :: W) T) =
        some (cf .E0 st S G W (false :: true :: T)) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_fim (stks_w S G (true :: false :: W) T)]
      simp [ir, TM2.stepAux, cf]
    have := Run.passo hs (runF .e0 W (false :: true :: T))
    simp only [ftr]
    exact this.mono (by simp)
  | .ec, true :: true :: W, T => by
    have hs : stp (cf .Ec st S G (true :: true :: W) T) = some (cf .F2 st S G W T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_fc (stks_w S G (true :: true :: W) T)]
      simp [ir, TM2.stepAux, cf]
    simp only [ftr]
    exact (Run.um hs).mono (by simp)
  | .ec, [a], T => by
    have hs : stp (cf .Ec st S G [a] T) = some (cf .F2 st S G [] T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_one (stks_w S G [a] T)]; simp [ir, TM2.stepAux, cf]
    simp only [ftr]
    exact (Run.um hs).mono (by simp)
  | .ec, [], T => by
    have hs : stp (cf .Ec st S G [] T) = some (cf .F2 st S G [] T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_nil (stks_w S G [] T)]; simp [ir, TM2.stepAux, cf]
    simp only [ftr]
    exact (Run.um hs).mono (by simp)
  | .es, false :: y :: W, T => by
    have hs : stp (cf .Es st S G (false :: y :: W) T) = some (cf .Es st S G W T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_bit (stks_w S G (false :: y :: W) T)]
      simp [ir, TM2.stepAux, cf]
    have := Run.passo hs (runF .es W T)
    simp only [ftr]
    exact this.mono (by simp)
  | .es, true :: false :: W, T => by
    have hs : stp (cf .Es st S G (true :: false :: W) T) = some (cf .E0 st S G W T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_fim (stks_w S G (true :: false :: W) T)]
      simp [ir, TM2.stepAux, cf]
    have := Run.passo hs (runF .e0 W T)
    simp only [ftr]
    exact this.mono (by simp)
  | .es, true :: true :: W, T => by
    have hs : stp (cf .Es st S G (true :: true :: W) T) = some (cf .F2 st S G W T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_fc (stks_w S G (true :: true :: W) T)]
      simp [ir, TM2.stepAux, cf]
    simp only [ftr]
    exact (Run.um hs).mono (by simp)
  | .es, [a], T => by
    have hs : stp (cf .Es st S G [a] T) = some (cf .F2 st S G [] T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_one (stks_w S G [a] T)]; simp [ir, TM2.stepAux, cf]
    simp only [ftr]
    exact (Run.um hs).mono (by simp)
  | .es, [], T => by
    have hs : stp (cf .Es st S G [] T) = some (cf .F2 st S G [] T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_nil (stks_w S G [] T)]; simp [ir, TM2.stepAux, cf]
    simp only [ftr]
    exact (Run.um hs).mono (by simp)

end filtro


def lblL : ML → Lb
  | .l0 => .L0
  | .l1 x => .L1 x
  | .ls => .Ls

/-- Atualização da bandeira da cláusula pelo resultado da busca. -/
def stL (st : St) (o : Option Bool) : St :=
  {st with fl := some (st.fl.getD false || decide (o = some st.v))}

section busca
variable (st : St) (S G T : List Bool)

theorem nf_eq (w : List Bool) (a b : Option Bool) :
    TM2.stepAux nf (a, b, st) (stks S G w T) = cf .X (stL st none) S G w T := by
  simp [nf, irS, TM2.stepAux, cf, stL]

theorem runL : ∀ (m : ML) (W : List Bool),
    Run (cf (lblL m) st S G W T) (cf .X (stL st (lk m W).1) S G (lk m W).2 T) (W.length + 1)
  | .l0, false :: x :: W => by
    have hs : stp (cf .L0 st S G (false :: x :: W) T) = some (cf (.L1 x) st S G W T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_bit (stks_w S G (false :: x :: W) T)]
      simp [ir, TM2.stepAux, cf]
    have := Run.passo hs (runL (.l1 x) W)
    simp only [lk]
    exact this.mono (by simp)
  | .l0, true :: y :: W => by
    have hs : stp (cf .L0 st S G (true :: y :: W) T) = some (cf .X (stL st none) S G W T) := by
      rw [stp_cf]; simp only [prog]
      cases y
      · rw [rd2_fim (stks_w S G (true :: false :: W) T), upd_w, nf_eq]
      · rw [rd2_fc (stks_w S G (true :: true :: W) T), upd_w, nf_eq]
    simp only [lk]
    exact (Run.um hs).mono (by simp)
  | .l0, [a] => by
    have hs : stp (cf .L0 st S G [a] T) = some (cf .X (stL st none) S G [] T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_one (stks_w S G [a] T), upd_w, nf_eq]
    simp only [lk]
    exact (Run.um hs).mono (by simp)
  | .l0, [] => by
    have hs : stp (cf .L0 st S G [] T) = some (cf .X (stL st none) S G [] T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_nil (stks_w S G [] T), upd_w, nf_eq]
    simp only [lk]
    exact (Run.um hs).mono (by simp)
  | .l1 x, true :: false :: W => by
    have hs : stp (cf (.L1 x) st S G (true :: false :: W) T) =
        some (cf .X (stL st (some x)) S G W T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_fim (stks_w S G (true :: false :: W) T)]
      simp [irS, TM2.stepAux, cf, stL]
    simp only [lk]
    exact (Run.um hs).mono (by simp)
  | .l1 x, false :: y :: W => by
    have hs : stp (cf (.L1 x) st S G (false :: y :: W) T) = some (cf .Ls st S G W T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_bit (stks_w S G (false :: y :: W) T)]
      simp [ir, TM2.stepAux, cf]
    have := Run.passo hs (runL .ls W)
    simp only [lk]
    exact this.mono (by simp)
  | .l1 x, true :: true :: W => by
    have hs : stp (cf (.L1 x) st S G (true :: true :: W) T) = some (cf .X (stL st none) S G W T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_fc (stks_w S G (true :: true :: W) T), upd_w, nf_eq]
    simp only [lk]
    exact (Run.um hs).mono (by simp)
  | .l1 x, [a] => by
    have hs : stp (cf (.L1 x) st S G [a] T) = some (cf .X (stL st none) S G [] T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_one (stks_w S G [a] T), upd_w, nf_eq]
    simp only [lk]
    exact (Run.um hs).mono (by simp)
  | .l1 x, [] => by
    have hs : stp (cf (.L1 x) st S G [] T) = some (cf .X (stL st none) S G [] T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_nil (stks_w S G [] T), upd_w, nf_eq]
    simp only [lk]
    exact (Run.um hs).mono (by simp)
  | .ls, false :: y :: W => by
    have hs : stp (cf .Ls st S G (false :: y :: W) T) = some (cf .Ls st S G W T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_bit (stks_w S G (false :: y :: W) T)]
      simp [ir, TM2.stepAux, cf]
    have := Run.passo hs (runL .ls W)
    simp only [lk]
    exact this.mono (by simp)
  | .ls, true :: false :: W => by
    have hs : stp (cf .Ls st S G (true :: false :: W) T) = some (cf .L0 st S G W T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_fim (stks_w S G (true :: false :: W) T)]
      simp [ir, TM2.stepAux, cf]
    have := Run.passo hs (runL .l0 W)
    simp only [lk]
    exact this.mono (by simp)
  | .ls, true :: true :: W => by
    have hs : stp (cf .Ls st S G (true :: true :: W) T) = some (cf .X (stL st none) S G W T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_fc (stks_w S G (true :: true :: W) T), upd_w, nf_eq]
    simp only [lk]
    exact (Run.um hs).mono (by simp)
  | .ls, [a] => by
    have hs : stp (cf .Ls st S G [a] T) = some (cf .X (stL st none) S G [] T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_one (stks_w S G [a] T), upd_w, nf_eq]
    simp only [lk]
    exact (Run.um hs).mono (by simp)
  | .ls, [] => by
    have hs : stp (cf .Ls st S G [] T) = some (cf .X (stL st none) S G [] T) := by
      rw [stp_cf]; simp only [prog]; rw [rd2_nil (stks_w S G [] T), upd_w, nf_eq]
    simp only [lk]
    exact (Run.um hs).mono (by simp)

end busca


/-! ### Tamanhos -/

theorem ftr_len (b : Bool) (m : MF) (W T : List Bool) :
    (ftr b m W T).1.length + (ftr b m W T).2.length ≤ W.length + T.length := by
  fun_induction ftr b m W T <;> simp_all <;> omega

theorem lk_len (m : ML) (W : List Bool) : (lk m W).2.length ≤ W.length := by
  fun_induction lk m W <;> simp_all <;> omega

theorem filt_len (b : Bool) (W : List Bool) : (filt b W).length ≤ W.length := by
  have := ftr_len b .e0 W []
  simp only [filt, List.length_append, List.length_reverse, List.length_nil] at *
  omega


/-! ### A análise da fórmula -/

theorem falha_eq (st : St) (S G W T : List Bool) (a b : Option Bool) :
    TM2.stepAux falha (a, b, st) (stks S G W T) = cf .Zs {st with ok := false} S G W T := by
  simp [falha, irS, TM2.stepAux, cf]

theorem cota (n M c : ℕ) (hc : c ≤ M) : c + (n + 1) * M ≤ (n + 2 + 1) * M := by
  nlinarith

theorem runP (S : List Bool) : ∀ (n : ℕ) (G : List Bool), G.length ≤ n →
    (∀ st : St, ∃ (st' : St) (G' W' : List Bool),
      Run (cf .P0 st S G [] []) (cf .Zs st' S G' W' []) ((G.length + 1) * (2 * S.length + 3)) ∧
      st'.ok = acc S st.fl .p0 G ∧ W'.length ≤ S.length ∧ G'.length ≤ G.length) ∧
    (∀ (st : St) (W : List Bool), W.length ≤ S.length → ∃ (st' : St) (G' W' : List Bool),
      Run (cf .P1 st S G W []) (cf .Zs st' S G' W' []) ((G.length + 1) * (2 * S.length + 3)) ∧
      st'.ok = acc S st.fl (.p1 st.v st.lb W) G ∧ W'.length ≤ S.length ∧ G'.length ≤ G.length)
  | n, [], _ => by
    refine ⟨fun st => ?_, fun st W hW => ?_⟩
    · have hs : stp (cf .P0 st S [] [] []) =
          some (cf .Zs {st with ok := decide (st.fl = none)} S [] [] []) := by
        rw [stp_cf]; simp only [prog]; rw [rd2_nil (stks_g S [] [] [])]
        simp [irS, TM2.stepAux, cf]
      exact ⟨_, [], [], (Run.um hs).mono (by simp), by simp [acc], by simp, by simp⟩
    · have hs : stp (cf .P1 st S [] W []) = some (cf .Zs {st with ok := false} S [] W []) := by
        rw [stp_cf]; simp only [prog]; rw [rd2_nil (stks_g S [] W []), upd_g, falha_eq]
      exact ⟨_, [], W, (Run.um hs).mono (by simp), by simp [acc], hW, by simp⟩
  | n, [a], _ => by
    refine ⟨fun st => ?_, fun st W hW => ?_⟩
    · have hs : stp (cf .P0 st S [a] [] []) = some (cf .Zs {st with ok := false} S [] [] []) := by
        rw [stp_cf]; simp only [prog]; rw [rd2_one (stks_g S [a] [] [])]
        simp [falha, irS, TM2.stepAux, cf]
      exact ⟨_, [], [], (Run.um hs).mono (by simp; omega), by cases a <;> simp [acc], by simp, by simp⟩
    · have hs : stp (cf .P1 st S [a] W []) = some (cf .Zs {st with ok := false} S [] W []) := by
        rw [stp_cf]; simp only [prog]; rw [rd2_one (stks_g S [a] W []), upd_g, falha_eq]
      exact ⟨_, [], W, (Run.um hs).mono (by simp; omega), by cases a <;> simp [acc], hW, by simp⟩
  | 0, _ :: _ :: _, h => by simp at h
  | n + 1, a :: b :: G, hG => by
    have hn : G.length ≤ n := by simp at hG; omega
    have ih := runP S n G hn
    have hM : ∀ c, c ≤ 2 * S.length + 3 → c + (G.length + 1) * (2 * S.length + 3) ≤
        ((a :: b :: G).length + 1) * (2 * S.length + 3) := fun c hc => by
      simpa using cota G.length (2 * S.length + 3) c hc
    refine ⟨fun st => ?_, fun st W hW => ?_⟩
    · cases a
      · -- literal: copia o certificado
        let st1 : St := {st with v := b, lb := none}
        have hs : stp (cf .P0 st S (false :: b :: G) [] []) = some (cf .C1 st1 S G [] []) := by
          rw [stp_cf]; simp only [prog]; rw [rd2_bit (stks_g S (false :: b :: G) [] [])]
          simp [irS, TM2.stepAux, cf, st1]
        have h1 := runC1 st1 G S [] []
        have h2 := runC2 st1 G (S.reverse ++ []) (S.reverse ++ []) []
        simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h1 h2
        obtain ⟨st', G', W', h3, hok, hW', hG'⟩ := ih.2 st1 S.reverse (by simp)
        refine ⟨st', G', W', ?_, ?_, hW', by simp; omega⟩
        · have := Run.passo hs (h1.trans (h2.trans h3))
          exact this.mono (by have := hM (S.length + 1 + (S.length + 1) + 1) (by omega); omega)
        · rw [hok]; simp [acc, st1]
      · cases b
        · have hs : stp (cf .P0 st S (true :: false :: G) [] []) =
              some (cf .Zs {st with ok := false} S G [] []) := by
            rw [stp_cf]; simp only [prog]; rw [rd2_fim (stks_g S (true :: false :: G) [] []), upd_g,
              falha_eq]
          exact ⟨_, G, [], (Run.um hs).mono (by have := hM 1 (by omega); omega), by simp [acc],
            by simp, by simp; omega⟩
        · by_cases hfl : st.fl = some true
          · have hs : stp (cf .P0 st S (true :: true :: G) [] []) =
                some (cf .P0 {st with fl := none} S G [] []) := by
              rw [stp_cf]; simp only [prog]; rw [rd2_fc (stks_g S (true :: true :: G) [] [])]
              simp [irS, TM2.stepAux, cf, hfl]
            obtain ⟨st', G', W', h3, hok, hW', hG'⟩ := ih.1 {st with fl := none}
            refine ⟨st', G', W', ?_, ?_, hW', by simp; omega⟩
            · exact (Run.passo hs h3).mono (by have := hM 1 (by omega); omega)
            · rw [hok]; simp [acc, hfl]
          · have hs : stp (cf .P0 st S (true :: true :: G) [] []) =
                some (cf .Zs {st with ok := false} S G [] []) := by
              rw [stp_cf]; simp only [prog]; rw [rd2_fc (stks_g S (true :: true :: G) [] [])]
              simp [falha, irS, TM2.stepAux, cf, hfl]
            exact ⟨_, G, [], (Run.um hs).mono (by have := hM 1 (by omega); omega),
              by simp [acc, hfl], by simp, by simp; omega⟩
    · cases a
      · -- bit de índice: filtra
        let st1 : St := {st with b := b, lb := some b}
        have hs : stp (cf .P1 st S (false :: b :: G) W []) = some (cf .E0 st1 S G W []) := by
          rw [stp_cf]; simp only [prog]; rw [rd2_bit (stks_g S (false :: b :: G) W [])]
          simp [irS, TM2.stepAux, cf, st1]
        have h1 := runF st1 S G .e0 W []
        have h2 := runF2 st1 S G (ftr st1.b .e0 W []).2 (ftr st1.b .e0 W []).1
        have hb : st1.b = b := rfl
        rw [hb] at h1 h2
        have hfilt : (ftr b .e0 W []).2.reverse ++ (ftr b .e0 W []).1 = filt b W := rfl
        rw [hfilt] at h2
        have hlen := ftr_len b .e0 W []
        simp only [List.length_nil, add_zero] at hlen
        obtain ⟨st', G', W', h3, hok, hW', hG'⟩ :=
          ih.2 st1 (filt b W) ((filt_len b W).trans hW)
        refine ⟨st', G', W', ?_, ?_, hW', by simp; omega⟩
        · have := Run.passo hs (h1.trans (h2.trans h3))
          exact this.mono (by
            have := hM (W.length + 1 + ((ftr b .e0 W []).2.length + 1) + 1) (by omega); omega)
        · rw [hok]; simp [acc, st1]
      · cases b
        · by_cases hlb : st.lb = some false
          · have hs : stp (cf .P1 st S (true :: false :: G) W []) =
                some (cf .Zs {st with ok := false} S G W []) := by
              rw [stp_cf]; simp only [prog]; rw [rd2_fim (stks_g S (true :: false :: G) W [])]
              simp [falha, irS, TM2.stepAux, cf, hlb]
            exact ⟨_, G, W, (Run.um hs).mono (by have := hM 1 (by omega); omega),
              by simp [acc, hlb], hW, by simp; omega⟩
          · have hs : stp (cf .P1 st S (true :: false :: G) W []) = some (cf .L0 st S G W []) := by
              rw [stp_cf]; simp only [prog]; rw [rd2_fim (stks_g S (true :: false :: G) W [])]
              simp [ir, TM2.stepAux, cf, hlb]
            have h1 := runL st S G [] .l0 W
            have h2 := runX (stL st (lk .l0 W).1) S G [] (lk .l0 W).2
            obtain ⟨st', G', W', h3, hok, hW', hG'⟩ := ih.1 (stL st (lk .l0 W).1)
            refine ⟨st', G', W', ?_, ?_, hW', by simp; omega⟩
            · have := Run.passo hs (h1.trans (h2.trans h3))
              have hl := lk_len .l0 W
              exact this.mono (by
                have := hM (W.length + 1 + ((lk .l0 W).2.length + 1) + 1) (by omega); omega)
            · rw [hok]; simp [acc, hlb, stL]
        · have hs : stp (cf .P1 st S (true :: true :: G) W []) =
              some (cf .Zs {st with ok := false} S G W []) := by
            rw [stp_cf]; simp only [prog]; rw [rd2_fc (stks_g S (true :: true :: G) W []), upd_g,
              falha_eq]
          exact ⟨_, G, W, (Run.um hs).mono (by have := hM 1 (by omega); omega), by simp [acc], hW,
            by simp; omega⟩

/-! ### A execução completa e SAT ∈ NP -/

theorem initList_sat (x : List Bool) : initList satTM x = cf .U st0 x [] [] [] := by
  simp only [initList, cf]
  congr 1
  funext k
  cases k <;> (simp [stks]; try rfl)

theorem haltList_sat (b : Bool) : haltList satTM [b] = cfFim b := by
  simp only [haltList, cfFim]
  congr 1
  funext k
  cases k <;> (simp [stks]; try rfl)

theorem runTotal (x : List Bool) :
    Run (cf .U st0 x [] [] []) (cfFim (verif x)) (2 * (x.length + 4) ^ 2) := by
  have hd := dec_length_le x
  have hr := resto_length_le x
  have h1 := runU st0 [] [] x []
  have h2 := runR st0 (resto x) [] ((dec x).reverse ++ []) []
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h1 h2
  obtain ⟨st', G', W', h3, hok, hW', hG'⟩ := (runP (resto x) (dec x).length (dec x) le_rfl).1 st0
  have h4 := runZs st' G' W' [] (resto x)
  have h5 := runZg st' [] W' [] G'
  have h6 := runZw st' W'
  have hv : st'.ok = verif x := by rw [hok]; rfl
  rw [hv] at h6
  refine (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))).mono ?_
  nlinarith

/-- **O verificador de SAT roda em tempo polinomial** numa `FinTM2`: `2 (n + 4)²` passos. -/
noncomputable def verifComputavel : TM2ComputableInPolyTime cod Computability.encodeBool verif where
  tm := satTM
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * (Polynomial.X + 4) ^ 2
  outputsFun x :=
    have hin : List.map (Equiv.refl Bool).invFun (cod x) = x := by simp [cod]
    have hout : List.map (Equiv.refl Bool).invFun (Computability.encodeBool (verif x)) = [verif x] := by
      simp [Computability.encodeBool]
    have hT : Polynomial.eval (cod x).length (2 * (Polynomial.X + 4) ^ 2) = 2 * (x.length + 4) ^ 2 := by
      simp [cod]
    have hrun := runTotal x
    { steps := Classical.choose hrun
      evals_in_steps := by
        rw [hin, hout, initList_sat, Option.map_some, haltList_sat]
        exact (Classical.choose_spec hrun).2
      steps_le_m := by
        rw [hT]
        exact (Classical.choose_spec hrun).1 }

/-- **SAT ∈ NP** sobre `Turing.FinTM2`: verificador em P (máquina acima) e certificados de
tamanho `≤ |w|` (pares índice/valor só para as variáveis que ocorrem na fórmula). -/
theorem sat_em_NP : SAT ∈ classeNP := by
  show EmNP SAT
  refine ⟨{x | verif x = true}, ⟨verif, fun w => Iff.rfl, ⟨verifComputavel⟩⟩, Polynomial.X,
    fun w => ?_⟩
  rw [sat_iff]
  simp only [Polynomial.eval_X]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, show verif (par w c) = true by rw [verif_par]; exact h⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, by rw [← verif_par]; exact h⟩

/-- **SAT ∈ NP no modelo genuíno** (`modeloPNP.NP = classeNP`). -/
theorem sat_em_NP_modelo : SAT ∈ modeloPNP.NP := sat_em_NP

/-- **B4 reduzida à NP-dificuldade**: com `SAT ∈ NP` provado, a ponte de Cook–Levin no modelo
genuíno é exatamente "toda linguagem de NP reduz (Karp, `FinTM2`, tempo polinomial) a SAT". -/
theorem cookLevin_iff :
    ClayPvsNPProof.ATK.Conditional.PvsNP.CookLevin modeloPNP SAT ↔ ∀ L ∈ classeNP, Red L SAT :=
  ⟨fun h => h.2, fun h => ⟨sat_em_NP, h⟩⟩

/-! ### Testes de sanidade (computados pelo kernel com `decide`) -/

/-- Fórmula satisfatível com o certificado certo: aceita. -/
theorem teste_aceita :
    verif (par (codCNF [[(1, true)], [(0, false), (1, true)]])
      (codEntradas [((1 : ℕ).bits, true)]).reverse) = true := by
  rw [verif_par]
  decide

/-- O mesmo índice com o valor errado no certificado: recusa. -/
theorem teste_certificado_errado :
    verif (par (codCNF [[(1, true)]]) (codEntradas [((1 : ℕ).bits, false)]).reverse) = false := by
  rw [verif_par]
  decide

/-- A cláusula vazia é recusada com qualquer certificado. -/
theorem teste_clausula_vazia (c : Palavra) : verif (par (codCNF [[]]) c) = false := by
  rw [verif_par, acc_cnf]
  rfl

/-- `x₀ ∧ ¬x₀` é recusada com qualquer certificado (a atribuição lida é consistente). -/
theorem teste_contradicao (c : Palavra) :
    verif (par (codCNF [[(0, true)], [(0, false)]]) c) = false := by
  rw [verif_par, acc_cnf]
  simp only [List.all_cons, List.any_cons, List.any_nil, List.all_nil, Bool.or_false,
    Bool.and_true, bom]
  generalize val c (Nat.bits 0) = o
  rcases o with _ | _ | _ <;> rfl

end ClayPvsNPProof.ATK.SATemNP


