-- Origem: kernel ATK, espelho público ShantiDraconis/atk-math-core-public @ ffc111a
-- (= ShantiDraconis/M-Core @ 390e378), arquivo imports/M-Core/atk-kernel/ATK/CookLevinBase.lean
-- (sha256 do original: 8240cd58a4cf9cae…).
-- Alterações comuns: namespace `ATK.*` → `ClayPvsNPProof.ATK.*`; linhas `#print axioms` removidas
-- (a auditoria está em `ClayPvsNPProof/Audit.lean`). Alterações específicas: acrescentado o import `Mathlib.Algebra.Polynomial.Eval.Degree`; binder `{α : Type*}` explícito em `head?_janela`/`tail_janela` (`autoImplicit = false`).
import ClayPvsNPProof.ATK.SATemNP
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# ATK — Ponte B4, marco M2a: fatos gerais sobre um passo de `Turing.TM2`

Base genérica para o tableau de Cook–Levin (qualquer máquina de pilhas da Mathlib):

* `stepAux_moldura` / `stepAux_topo`: um passo só lê o topo de cada pilha. Se `prof q ≤ d`, o
  passo sobre `S` é o passo sobre as janelas `take d`, com `drop d` intacto embaixo. É o que torna
  as cláusulas de transição locais;
* `length_stepAux_le`: uma pilha cresce no máximo `emp q` por passo (altura do tableau);
* `mem_stepAux`, `simbolos_finite`: todo símbolo novo vem de um `push` do programa, e esses
  símbolos formam um conjunto finito. Isso importa porque `Turing.FinTM2` só exige alfabeto finito
  na pilha de entrada;
* `passoA`, `acolchoada_de_evals`: a execução acolchoada (parada fica parada) de `T` passos
  termina na configuração de parada sempre que a máquina para em `n ≤ T` passos;
* `eval_mono`, `cota`: polinômios em `ℕ` são monótonos e cotados por `p(1)·(n+1)^grau`;
* sanidade: o verificador de SAT (`ClayPvsNPProof.ATK.SATemNP.prog`) lê no máximo 2 símbolos e empurra no máximo
  2 por passo, e o lema de moldura vale para ele com janela 2.

Nada aqui decide P vs NP. **CLOSED_MATH continua false.**
-/

namespace ClayPvsNPProof.ATK.CookLevinBase

open Turing Turing.TM2 Function Polynomial Finset

section geral

variable {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}

/-! ### Janela de leitura -/


/-- Profundidade de leitura de um comando (`pop`/`peek` encadeados num ramo). -/
def prof : Stmt Γ Λ σ → ℕ
  | .push _ _ q => prof q
  | .peek _ _ q => prof q + 1
  | .pop _ _ q => prof q + 1
  | .load _ q => prof q
  | .branch _ q₁ q₂ => max (prof q₁) (prof q₂)
  | .goto _ => 0
  | .halt => 0

theorem head?_janela {α : Type*} {A B : List α} (h : 1 ≤ A.length ∨ B = []) : (A ++ B).head? = A.head? := by
  rcases h with h | h
  · rcases A with _ | ⟨a, A⟩
    · simp at h
    · rfl
  · simp [h]

theorem tail_janela {α : Type*} {A B : List α} (h : 1 ≤ A.length ∨ B = []) : (A ++ B).tail = A.tail ++ B := by
  rcases h with h | h
  · rcases A with _ | ⟨a, A⟩
    · simp at h
    · rfl
  · simp [h]

/-- **Lema de moldura**: se a janela `A` de cada pilha é funda o bastante para o comando, o passo
sobre `A ++ B` é o passo sobre `A`, com `B` intacto embaixo. -/
theorem stepAux_moldura : ∀ (q : Stmt Γ Λ σ) (v : σ) (A B : ∀ k, List (Γ k)),
    (∀ k, prof q ≤ (A k).length ∨ B k = []) →
    stepAux q v (fun k => A k ++ B k) =
      ⟨(stepAux q v A).l, (stepAux q v A).var, fun k => (stepAux q v A).stk k ++ B k⟩
  | .push k f q, v, A, B, h => by
    have hu : update (fun j => A j ++ B j) k (f v :: (A k ++ B k)) =
        fun j => update A k (f v :: A k) j ++ B j := by
      funext j
      by_cases hj : j = k
      · subst hj; simp
      · simp [update_of_ne hj]
    simp only [stepAux]
    rw [hu]
    refine stepAux_moldura q v _ B (fun j => ?_)
    rcases h j with h' | h'
    · left
      by_cases hj : j = k
      · subst hj; simp only [prof] at h'; simp; omega
      · simpa [update_of_ne hj, prof] using h'
    · right; exact h'
  | .peek k f q, v, A, B, h => by
    have hk : 1 ≤ (A k).length ∨ B k = [] := by
      rcases h k with h' | h'
      · left; simp only [prof] at h'; omega
      · right; exact h'
    simp only [stepAux]
    rw [head?_janela hk]
    refine stepAux_moldura q _ A B (fun j => ?_)
    rcases h j with h' | h'
    · left; simp only [prof] at h'; omega
    · right; exact h'
  | .pop k f q, v, A, B, h => by
    have hk : 1 ≤ (A k).length ∨ B k = [] := by
      rcases h k with h' | h'
      · left; simp only [prof] at h'; omega
      · right; exact h'
    have hu : update (fun j => A j ++ B j) k (A k ++ B k).tail =
        fun j => update A k (A k).tail j ++ B j := by
      funext j
      by_cases hj : j = k
      · subst hj; simp [tail_janela hk]
      · simp [update_of_ne hj]
    simp only [stepAux]
    rw [head?_janela hk, hu]
    refine stepAux_moldura q _ _ B (fun j => ?_)
    rcases h j with h' | h'
    · left
      by_cases hj : j = k
      · subst hj; simp only [prof] at h'; simp; omega
      · simp only [prof] at h'; simp [update_of_ne hj]; omega
    · right; exact h'
  | .load a q, v, A, B, h => by
    simp only [stepAux]
    exact stepAux_moldura q _ A B (fun j => by simpa [prof] using h j)
  | .branch f q₁ q₂, v, A, B, h => by
    simp only [stepAux]
    cases f v
    · simp only [Bool.cond_false]
      refine stepAux_moldura q₂ v A B (fun j => ?_)
      rcases h j with h' | h'
      · left; simp only [prof] at h'; omega
      · right; exact h'
    · simp only [Bool.cond_true]
      refine stepAux_moldura q₁ v A B (fun j => ?_)
      rcases h j with h' | h'
      · left; simp only [prof] at h'; omega
      · right; exact h'
  | .goto f, v, A, B, _ => by simp
  | .halt, v, A, B, _ => by simp

/-- Forma usada no tableau: a janela é o topo `take d` de cada pilha. -/
theorem stepAux_topo (q : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) {d : ℕ} (hd : prof q ≤ d) :
    stepAux q v S =
      ⟨(stepAux q v (fun k => (S k).take d)).l, (stepAux q v (fun k => (S k).take d)).var,
        fun k => (stepAux q v (fun k => (S k).take d)).stk k ++ (S k).drop d⟩ := by
  have h := stepAux_moldura q v (fun k => (S k).take d) (fun k => (S k).drop d) (fun k => by
    by_cases hk : d ≤ (S k).length
    · left; simp [List.length_take]; omega
    · right; simp; omega)
  simp only [List.take_append_drop] at h
  exact h

/-! ### Crescimento das pilhas e símbolos empurrados -/


/-- Máximo de `push` encadeados num ramo. -/
def emp : Stmt Γ Λ σ → ℕ
  | .push _ _ q => emp q + 1
  | .peek _ _ q => emp q
  | .pop _ _ q => emp q
  | .load _ q => emp q
  | .branch _ q₁ q₂ => max (emp q₁) (emp q₂)
  | .goto _ => 0
  | .halt => 0

/-- Uma pilha cresce no máximo `emp q` num passo. -/
theorem length_stepAux_le : ∀ (q : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K),
    ((stepAux q v S).stk k).length ≤ (S k).length + emp q
  | .push j f q, v, S, k => by
    simp only [stepAux, emp]
    have := length_stepAux_le q v (update S j (f v :: S j)) k
    by_cases hk : k = j
    · subst hk; simp at this; omega
    · simp [update_of_ne hk] at this; omega
  | .peek j f q, v, S, k => by
    simp only [stepAux, emp]; exact length_stepAux_le q _ S k
  | .pop j f q, v, S, k => by
    simp only [stepAux, emp]
    have := length_stepAux_le q (f v (S j).head?) (update S j (S j).tail) k
    by_cases hk : k = j
    · subst hk; simp at this; omega
    · simp [update_of_ne hk] at this; omega
  | .load a q, v, S, k => by simp only [stepAux, emp]; exact length_stepAux_le q _ S k
  | .branch f q₁ q₂, v, S, k => by
    simp only [stepAux, emp]
    cases f v
    · have := length_stepAux_le q₂ v S k; simp only [Bool.cond_false]; omega
    · have := length_stepAux_le q₁ v S k; simp only [Bool.cond_true]; omega
  | .goto f, v, S, k => by simp
  | .halt, v, S, k => by simp

/-- Símbolos que um comando pode empurrar. -/
def simbolos : Stmt Γ Λ σ → Set (Σ k, Γ k)
  | .push k f q => Set.range (fun v => (⟨k, f v⟩ : Σ k, Γ k)) ∪ simbolos q
  | .peek _ _ q => simbolos q
  | .pop _ _ q => simbolos q
  | .load _ q => simbolos q
  | .branch _ q₁ q₂ => simbolos q₁ ∪ simbolos q₂
  | .goto _ => ∅
  | .halt => ∅

omit [DecidableEq K] in
theorem simbolos_finite [Finite σ] : ∀ q : Stmt Γ Λ σ, (simbolos q).Finite
  | .push _ _ q => (Set.finite_range _).union (simbolos_finite q)
  | .peek _ _ q => simbolos_finite q
  | .pop _ _ q => simbolos_finite q
  | .load _ q => simbolos_finite q
  | .branch _ q₁ q₂ => (simbolos_finite q₁).union (simbolos_finite q₂)
  | .goto _ => Set.finite_empty
  | .halt => Set.finite_empty

/-- Todo símbolo depois do passo já estava na pilha ou foi empurrado pelo comando. -/
theorem mem_stepAux : ∀ (q : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) (x : Γ k),
    x ∈ (stepAux q v S).stk k → x ∈ S k ∨ (⟨k, x⟩ : Σ k, Γ k) ∈ simbolos q
  | .push j f q, v, S, k, x, h => by
    simp only [stepAux] at h
    rcases mem_stepAux q v _ k x h with h' | h'
    · by_cases hk : k = j
      · subst hk
        simp only [update_self, List.mem_cons] at h'
        rcases h' with h' | h'
        · right; left; exact ⟨v, by rw [h']⟩
        · left; exact h'
      · left; simpa [update_of_ne hk] using h'
    · right; right; exact h'
  | .peek j f q, v, S, k, x, h => mem_stepAux q _ S k x h
  | .pop j f q, v, S, k, x, h => by
    simp only [stepAux] at h
    rcases mem_stepAux q _ _ k x h with h' | h'
    · left
      by_cases hk : k = j
      · subst hk; simp only [update_self] at h'; exact List.mem_of_mem_tail h'
      · simpa [update_of_ne hk] using h'
    · right; exact h'
  | .load a q, v, S, k, x, h => mem_stepAux q _ S k x h
  | .branch f q₁ q₂, v, S, k, x, h => by
    simp only [stepAux] at h
    cases hf : f v
    · rw [hf, Bool.cond_false] at h
      rcases mem_stepAux q₂ v S k x h with h' | h'
      · left; exact h'
      · right; right; exact h'
    · rw [hf, Bool.cond_true] at h
      rcases mem_stepAux q₁ v S k x h with h' | h'
      · left; exact h'
      · right; left; exact h'
  | .goto f, v, S, k, x, h => Or.inl (by simpa using h)
  | .halt, v, S, k, x, h => Or.inl (by simpa using h)

/-! ### Execução acolchoada -/

variable (M : Λ → TM2.Stmt Γ Λ σ)


/-- Passo acolchoado: uma configuração parada fica parada. -/
def passoA (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ σ := (TM2.step M c).getD c

theorem passoA_parada (c : TM2.Cfg Γ Λ σ) (h : c.l = none) : passoA M c = c := by
  rcases c with ⟨l, v, S⟩
  simp only at h; subst h
  rfl

theorem passoA_iter_parada (c : TM2.Cfg Γ Λ σ) (h : c.l = none) : ∀ n, (passoA M)^[n] c = c
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply, passoA_parada M c h, passoA_iter_parada c h n]

/-- Enquanto a execução parcial (`Option`) não falha, ela coincide com a acolchoada. -/
theorem iter_some (c : TM2.Cfg Γ Λ σ) : ∀ (n : ℕ) (d : TM2.Cfg Γ Λ σ),
    (flip bind (TM2.step M))^[n] (some c) = some d → (passoA M)^[n] c = d
  | 0, d, h => by simpa using h
  | n + 1, d, h => by
    rw [Function.iterate_succ_apply'] at h
    rw [Function.iterate_succ_apply']
    rcases he : (flip bind (TM2.step M))^[n] (some c) with _ | e
    · rw [he] at h; simp [flip] at h
    · rw [he] at h
      rw [iter_some c n e he]
      have h' : TM2.step M e = some d := h
      simp [passoA, h']

/-- **Execução acolchoada**: se a máquina para em `h` em `n ≤ T` passos, a execução acolchoada de
`T` passos termina em `h`. -/
theorem acolchoada_de_evals (c h : TM2.Cfg Γ Λ σ) (hl : h.l = none) (n T : ℕ) (hn : n ≤ T)
    (he : (flip bind (TM2.step M))^[n] (some c) = some h) : (passoA M)^[T] c = h := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm, Function.iterate_add_apply, iter_some M c n h he, passoA_iter_parada M h hl]

end geral

/-! ### Polinômios em `ℕ` -/


/-- `p.eval` é monótona em `ℕ` (coeficientes naturais). -/
theorem eval_mono (p : ℕ[X]) {m n : ℕ} (h : m ≤ n) : p.eval m ≤ p.eval n := by
  rw [eval_eq_sum_range, eval_eq_sum_range]
  exact sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

/-- Todo polinômio em `ℕ` é cotado por `a (n + 1)^k`. -/
theorem cota (p : ℕ[X]) : ∀ n, p.eval n ≤ p.eval 1 * (n + 1) ^ p.natDegree := by
  intro n
  rw [eval_eq_sum_range, eval_eq_sum_range, sum_mul]
  refine sum_le_sum fun i hi => ?_
  rw [one_pow, mul_one]
  refine Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (Nat.le_succ n) i).trans ?_)
  exact Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.lt_succ_iff.mp (mem_range.mp hi))

/-! ### Sanidade: o verificador de SAT -/

theorem teste_prof_sat : ∀ l, prof (ClayPvsNPProof.ATK.SATemNP.prog l) ≤ 2 := by
  intro l; cases l <;> first | decide | (rename_i x; cases x <;> decide)

theorem teste_emp_sat : ∀ l, emp (ClayPvsNPProof.ATK.SATemNP.prog l) ≤ 2 := by
  intro l; cases l <;> first | decide | (rename_i x; cases x <;> decide)

/-- O passo do verificador de SAT só depende dos dois símbolos do topo de cada pilha. -/
theorem teste_topo_sat (l : ClayPvsNPProof.ATK.SATemNP.Lb) (v : ClayPvsNPProof.ATK.SATemNP.Sg)
    (S : ClayPvsNPProof.ATK.SATemNP.Pk → List Bool) :
    stepAux (ClayPvsNPProof.ATK.SATemNP.prog l) v S =
      ⟨(stepAux (ClayPvsNPProof.ATK.SATemNP.prog l) v (fun k => (S k).take 2)).l,
        (stepAux (ClayPvsNPProof.ATK.SATemNP.prog l) v (fun k => (S k).take 2)).var,
        fun k => (stepAux (ClayPvsNPProof.ATK.SATemNP.prog l) v (fun k => (S k).take 2)).stk k ++ (S k).drop 2⟩ :=
  stepAux_topo _ v S (teste_prof_sat l)

end ClayPvsNPProof.ATK.CookLevinBase

