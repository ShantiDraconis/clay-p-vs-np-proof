-- Origem: kernel ATK, espelho público ShantiDraconis/atk-math-core-public @ ffc111a
-- (= ShantiDraconis/M-Core @ 390e378), arquivo imports/M-Core/atk-kernel/ATK/Fragmentos.lean
-- (sha256 do original: a408b89e8737ef09…).
-- Alterações comuns: namespace `ATK.*` → `ClayPvsNPProof.ATK.*`; linhas `#print axioms` removidas
-- (a auditoria está em `ClayPvsNPProof/Audit.lean`). Alterações específicas: nenhuma além das comuns.
import ClayPvsNPProof.ATK.CookLevinBase

/-!
# ATK — Ponte B4, marco M2d (parte 1a): fragmentos de programa para máquinas de pilhas

Montagem composicional de programas `Turing.TM2`:

* `rel` / `stepAux_rel`: trocar os rótulos de destino de um comando comuta com o passo;
* `Frag`: rótulos próprios (finitos), entrada e código cujo `goto none` sai do fragmento;
  `Faz F v S v' S' n` diz que `F` vai de `(v, S)` à saída com `(v', S')` em exatamente `n` passos;
* `embute`: um fragmento embutido numa máquina maior (código reetiquetado) roda igual;
* combinadores com as regras de execução: `seq` (`faz_seq`), `cond` (`faz_cond_true`,
  `faz_cond_false`), `atom` (`faz_atom`), `laco` (`faz_laco`, `laco_cons`, `laco_nil`).

Nada aqui decide P vs NP. **CLOSED_MATH continua false.**
-/

namespace ClayPvsNPProof.ATK.Fragmentos

open Turing Turing.TM2 Function

variable {K : Type} [DecidableEq K] {Γ : K → Type} {σ : Type}

/-! ## Reetiquetar comandos -/

/-- Troca os rótulos de destino de um comando. -/
def rel {Λ Λ' : Type} (f : Λ → Λ') : Stmt Γ Λ σ → Stmt Γ Λ' σ
  | .push k g q => .push k g (rel f q)
  | .peek k g q => .peek k g (rel f q)
  | .pop k g q => .pop k g (rel f q)
  | .load g q => .load g (rel f q)
  | .branch g q₁ q₂ => .branch g (rel f q₁) (rel f q₂)
  | .goto g => .goto (f ∘ g)
  | .halt => .halt

/-- Configuração com rótulo trocado. -/
def cmap {Λ Λ' : Type} (f : Λ → Λ') (c : Cfg Γ Λ σ) : Cfg Γ Λ' σ := ⟨c.l.map f, c.var, c.stk⟩

theorem stepAux_rel {Λ Λ' : Type} (f : Λ → Λ') : ∀ (q : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)),
    stepAux (rel f q) v S = cmap f (stepAux q v S)
  | .push k g q, v, S => by simp only [rel, stepAux]; exact stepAux_rel f q _ _
  | .peek k g q, v, S => by simp only [rel, stepAux]; exact stepAux_rel f q _ _
  | .pop k g q, v, S => by simp only [rel, stepAux]; exact stepAux_rel f q _ _
  | .load g q, v, S => by simp only [rel, stepAux]; exact stepAux_rel f q _ _
  | .branch g q₁ q₂, v, S => by
    simp only [rel, stepAux]
    cases g v
    · simp only [Bool.cond_false]; exact stepAux_rel f q₂ _ _
    · simp only [Bool.cond_true]; exact stepAux_rel f q₁ _ _
  | .goto g, v, S => rfl
  | .halt, v, S => rfl

/-! ## Fragmentos de programa -/

/-- Um fragmento: rótulos próprios, entrada, e código cujos `goto none` saem do fragmento. -/
structure Frag (K : Type) (Γ : K → Type) (σ : Type) where
  Λ : Type
  [fin : Fintype Λ]
  entry : Λ
  code : Λ → Stmt Γ (Option Λ) σ

attribute [instance] Frag.fin

/-- A máquina isolada do fragmento (o rótulo `none` é a saída). -/
def Frag.maq (F : Frag K Γ σ) : Option F.Λ → Stmt Γ (Option F.Λ) σ
  | some l => F.code l
  | none => .halt

/-- `F` vai de `(v, S)` a `(v', S')`, saindo, em `n` passos. -/
def Faz (F : Frag K Γ σ) (v : σ) (S : ∀ k, List (Γ k)) (v' : σ) (S' : ∀ k, List (Γ k)) (n : ℕ) :
    Prop :=
  (flip bind (step F.maq))^[n] (some ⟨some (some F.entry), v, S⟩) = some ⟨some none, v', S'⟩

/-- **Embutir um fragmento**: numa máquina `M'` cujo código nos rótulos `e (some l)` é o código de
`F` reetiquetado por `e`, a execução de `F` vira uma execução de `M'` que termina em `e none`. -/
theorem embute {F : Frag K Γ σ} {Λ' : Type} (M' : Λ' → Stmt Γ Λ' σ) (e : Option F.Λ → Λ')
    (he : ∀ l, M' (e (some l)) = rel e (F.code l)) :
    ∀ (n : ℕ) (l : F.Λ) (v : σ) (S : ∀ k, List (Γ k)) (v' : σ) (S' : ∀ k, List (Γ k)),
      (flip bind (step F.maq))^[n] (some ⟨some (some l), v, S⟩) = some ⟨some none, v', S'⟩ →
      (flip bind (step M'))^[n] (some ⟨some (e (some l)), v, S⟩) = some ⟨some (e none), v', S'⟩
  | 0, l, v, S, v', S', h => by simp at h
  | n + 1, l, v, S, v', S', h => by
    rw [Function.iterate_succ_apply] at h ⊢
    have h1 : flip bind (step F.maq) (some ⟨some (some l), v, S⟩) =
        some (stepAux (F.code l) v S) := rfl
    have h2 : flip bind (step M') (some ⟨some (e (some l)), v, S⟩) =
        some (cmap e (stepAux (F.code l) v S)) := by
      show some (stepAux (M' (e (some l))) v S) = _
      rw [he, stepAux_rel]
    rw [h1] at h
    rw [h2]
    rcases hc : stepAux (F.code l) v S with ⟨o, v₁, S₁⟩
    rw [hc] at h
    rcases o with _ | _ | l₁
    · -- parou dentro do fragmento: impossível (a iteração devolveria `none`)
      rcases n with _ | n
      · simp at h
      · rw [Function.iterate_succ_apply] at h
        have : flip bind (step F.maq) (some (⟨none, v₁, S₁⟩ : Cfg Γ (Option F.Λ) σ)) = none := rfl
        rw [this] at h
        have hn : ∀ m, (flip bind (step F.maq))^[m] (none : Option (Cfg Γ (Option F.Λ) σ)) = none := by
          intro m; induction m with
          | zero => rfl
          | succ m ih => rw [Function.iterate_succ_apply]; exact ih
        rw [hn] at h; simp at h
    · -- saiu: só pode ser com `n = 0`
      rcases n with _ | n
      · simp at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
      · rw [Function.iterate_succ_apply] at h
        have : flip bind (step F.maq) (some (⟨some none, v₁, S₁⟩ : Cfg Γ (Option F.Λ) σ)) =
            some ⟨none, v₁, S₁⟩ := rfl
        rw [this] at h
        rcases n with _ | n
        · simp at h
        · rw [Function.iterate_succ_apply] at h
          have h0 : flip bind (step F.maq) (some (⟨none, v₁, S₁⟩ : Cfg Γ (Option F.Λ) σ)) = none := rfl
          rw [h0] at h
          have hn : ∀ m, (flip bind (step F.maq))^[m] (none : Option (Cfg Γ (Option F.Λ) σ)) = none := by
            intro m; induction m with
            | zero => rfl
            | succ m ih => rw [Function.iterate_succ_apply]; exact ih
          rw [hn] at h; simp at h
    · exact embute M' e he n l₁ v₁ S₁ v' S' h


theorem iter_none {Λ : Type} (M : Λ → Stmt Γ Λ σ) :
    ∀ m, (flip bind (step M))^[m] (none : Option (Cfg Γ Λ σ)) = none
  | 0 => rfl
  | m + 1 => by rw [Function.iterate_succ_apply]; exact iter_none M m

/-! ## Composição sequencial -/

/-- `F` e depois `G`. -/
def seq (F G : Frag K Γ σ) : Frag K Γ σ where
  Λ := F.Λ ⊕ G.Λ
  entry := .inl F.entry
  code
    | .inl l => rel (fun o => some (o.elim (.inr G.entry) .inl)) (F.code l)
    | .inr l => rel (Option.map .inr) (G.code l)

theorem faz_seq {F G : Frag K Γ σ} {v v₁ v₂ : σ} {S S₁ S₂ : ∀ k, List (Γ k)} {n m : ℕ}
    (hF : Faz F v S v₁ S₁ n) (hG : Faz G v₁ S₁ v₂ S₂ m) : Faz (seq F G) v S v₂ S₂ (m + n) := by
  have h1 := embute (seq F G).maq (fun o => some (o.elim (.inr G.entry) .inl)) (fun l => rfl) n
    F.entry v S v₁ S₁ hF
  have h2 := embute (seq F G).maq (Option.map .inr) (fun l => rfl) m G.entry v₁ S₁ v₂ S₂ hG
  unfold Faz
  rw [Function.iterate_add_apply]
  exact (congrArg _ h1).trans h2

/-! ## Desvio condicional pelo estado -/

/-- Se `c v` então `F`, senão `G`. -/
def cond (c : σ → Bool) (F G : Frag K Γ σ) : Frag K Γ σ where
  Λ := Unit ⊕ F.Λ ⊕ G.Λ
  entry := .inl ()
  code
    | .inl () => .branch c (.goto fun _ => some (.inr (.inl F.entry)))
        (.goto fun _ => some (.inr (.inr G.entry)))
    | .inr (.inl l) => rel (Option.map (.inr ∘ .inl)) (F.code l)
    | .inr (.inr l) => rel (Option.map (.inr ∘ .inr)) (G.code l)

theorem faz_cond_true {c : σ → Bool} {F G : Frag K Γ σ} {v v' : σ} {S S' : ∀ k, List (Γ k)} {n : ℕ}
    (hc : c v = true) (hF : Faz F v S v' S' n) : Faz (cond c F G) v S v' S' (n + 1) := by
  have h := embute (cond c F G).maq (Option.map (.inr ∘ .inl)) (fun l => rfl) n F.entry v S v' S' hF
  unfold Faz
  rw [Function.iterate_succ_apply]
  have h0 : flip bind (step (cond c F G).maq) (some ⟨some (some (cond c F G).entry), v, S⟩) =
      some ⟨some (some (.inr (.inl F.entry))), v, S⟩ := by
    show some (stepAux _ v S) = _
    simp [cond, Frag.maq, stepAux, hc]
  rw [h0]
  exact h

theorem faz_cond_false {c : σ → Bool} {F G : Frag K Γ σ} {v v' : σ} {S S' : ∀ k, List (Γ k)} {n : ℕ}
    (hc : c v = false) (hG : Faz G v S v' S' n) : Faz (cond c F G) v S v' S' (n + 1) := by
  have h := embute (cond c F G).maq (Option.map (.inr ∘ .inr)) (fun l => rfl) n G.entry v S v' S' hG
  unfold Faz
  rw [Function.iterate_succ_apply]
  have h0 : flip bind (step (cond c F G).maq) (some ⟨some (some (cond c F G).entry), v, S⟩) =
      some ⟨some (some (.inr (.inr G.entry))), v, S⟩ := by
    show some (stepAux _ v S) = _
    simp [cond, Frag.maq, stepAux, hc]
  rw [h0]
  exact h

/-! ## Um comando atômico -/

/-- Fragmento de um rótulo: roda `q` (que deve terminar em `goto`) e sai. -/
def atom (q : Stmt Γ Unit σ) : Frag K Γ σ where
  Λ := Unit
  entry := ()
  code _ := rel (fun _ => none) q

theorem faz_atom {q : Stmt Γ Unit σ} {v v' : σ} {S S' : ∀ k, List (Γ k)}
    (h : stepAux q v S = ⟨some (), v', S'⟩) : Faz (atom q) v S v' S' 1 := by
  show some (stepAux (rel (fun _ => none) q) v S) = _
  rw [stepAux_rel, h]
  rfl

/-! ## Laço sobre uma pilha -/

/-- Enquanto a pilha `k` não está vazia: tira o topo (guardado no estado por `rd`) e roda o
corpo. -/
def laco (k : K) (rd : σ → Option (Γ k) → σ) (c : σ → Bool) (B : Frag K Γ σ) : Frag K Γ σ where
  Λ := Unit ⊕ B.Λ
  entry := .inl ()
  code
    | .inl () => .pop k rd (.branch c (.goto fun _ => some (.inr B.entry)) (.goto fun _ => none))
    | .inr l => rel (fun o => some (o.elim (.inl ()) .inr)) (B.code l)

theorem faz_laco {k : K} {rd : σ → Option (Γ k) → σ} {c : σ → Bool} {B : Frag K Γ σ}
    (Ss : ℕ → ∀ k, List (Γ k)) (vs : ℕ → σ) (ns : ℕ → ℕ) :
    ∀ (m i : ℕ), (∀ j, i ≤ j → j < i + m → ∃ a r, (Ss j) k = a :: r ∧ c (rd (vs j) (some a)) = true ∧
        Faz B (rd (vs j) (some a)) (update (Ss j) k r) (vs (j + 1)) (Ss (j + 1)) (ns j)) →
      (Ss (i + m)) k = [] → c (rd (vs (i + m)) none) = false →
      Faz (laco k rd c B) (vs i) (Ss i) (rd (vs (i + m)) none) (Ss (i + m))
        ((Finset.range m).sum (fun j => ns (i + j) + 1) + 1)
  | 0, i, _, he, hc => by
    simp only [add_zero] at he hc
    unfold Faz
    simp only [Finset.range_zero, Finset.sum_empty, zero_add, Function.iterate_one, add_zero]
    show some (stepAux _ (vs i) (Ss i)) = _
    have hu : update (Ss i) k [] = Ss i := he ▸ Function.update_eq_self k (Ss i)
    simp [laco, Frag.maq, stepAux, he, hc, hu]
  | m + 1, i, hit, he, hc => by
    obtain ⟨a, r, hS, hca, hB⟩ := hit i le_rfl (by omega)
    have ih := faz_laco Ss vs ns m (i + 1) (fun j h1 h2 => hit j (by omega) (by omega))
      (by rw [show i + 1 + m = i + (m + 1) by omega]; exact he)
      (by rw [show i + 1 + m = i + (m + 1) by omega]; exact hc)
    rw [show i + 1 + m = i + (m + 1) by omega] at ih
    have hBe := embute (laco k rd c B).maq (fun o => some (o.elim (.inl ()) .inr)) (fun l => rfl)
      (ns i) B.entry _ _ _ _ hB
    dsimp only [Option.elim] at hBe
    unfold Faz at ih ⊢
    have hsum : (Finset.range (m + 1)).sum (fun j => ns (i + j) + 1) + 1 =
        ((Finset.range m).sum (fun j => ns (i + 1 + j) + 1) + 1) + ns i + 1 := by
      rw [Finset.sum_range_succ']
      simp only [add_zero]
      rw [show (fun j => ns (i + (j + 1)) + 1) = (fun j => ns (i + 1 + j) + 1) from by
        funext j; congr 2; omega]
      omega
    rw [hsum, Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_one]
    have h0 : flip bind (step (laco k rd c B).maq) (some ⟨some (some (laco k rd c B).entry), vs i, Ss i⟩) =
        some ⟨some (some (.inr B.entry)), rd (vs i) (some a), update (Ss i) k r⟩ := by
      show some (stepAux _ (vs i) (Ss i)) = _
      simp [laco, Frag.maq, stepAux, hS, hca]
    rw [h0, hBe]
    exact ih


/-- Uma volta do laço. -/
theorem laco_cons {k : K} {rd : σ → Option (Γ k) → σ} {c : σ → Bool} {B : Frag K Γ σ}
    {v v₁ v' : σ} {S S₁ S' : ∀ k, List (Γ k)} {a : Γ k} {r : List (Γ k)} {n₁ n₂ : ℕ}
    (hS : S k = a :: r) (hc : c (rd v (some a)) = true)
    (hB : Faz B (rd v (some a)) (update S k r) v₁ S₁ n₁)
    (hL : Faz (laco k rd c B) v₁ S₁ v' S' n₂) : Faz (laco k rd c B) v S v' S' (n₂ + n₁ + 1) := by
  have hBe := embute (laco k rd c B).maq (fun o => some (o.elim (.inl ()) .inr)) (fun l => rfl)
    n₁ B.entry _ _ _ _ hB
  dsimp only [Option.elim] at hBe
  unfold Faz at hL ⊢
  rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_one]
  have h0 : flip bind (step (laco k rd c B).maq) (some ⟨some (some (laco k rd c B).entry), v, S⟩) =
      some ⟨some (some (.inr B.entry)), rd v (some a), update S k r⟩ := by
    show some (stepAux _ v S) = _
    simp [laco, Frag.maq, stepAux, hS, hc]
  rw [h0, hBe]
  exact hL

/-- Saída do laço com a pilha vazia. -/
theorem laco_nil {k : K} {rd : σ → Option (Γ k) → σ} {c : σ → Bool} {B : Frag K Γ σ}
    {v : σ} {S : ∀ k, List (Γ k)} (hS : S k = []) (hc : c (rd v none) = false) :
    Faz (laco k rd c B) v S (rd v none) S 1 := by
  show some (stepAux _ v S) = _
  have hu : update S k [] = S := hS ▸ Function.update_eq_self k S
  simp [laco, Frag.maq, stepAux, hS, hc, hu]

/-! ## Empilhar em várias pilhas -/

section empilha

variable {Λ : Type}

/-- Empilha, em cada pilha `d` da lista, o valor `f d v`; depois vai para `l`. -/
def empilha (l : Λ) : List (Σ' k : K, (σ → Γ k)) → Stmt Γ Λ σ
  | [] => .goto fun _ => l
  | ⟨d, f⟩ :: ds => .push d f (empilha l ds)

end empilha

end ClayPvsNPProof.ATK.Fragmentos

