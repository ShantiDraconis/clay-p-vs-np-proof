-- Origem: kernel ATK, espelho público ShantiDraconis/atk-math-core-public @ ffc111a
-- (= ShantiDraconis/M-Core @ 390e378), arquivo imports/M-Core/atk-kernel/ATK/CookLevinLacos.lean
-- (sha256 do original: 3870f4a92eb0abc8…).
-- Alterações comuns: namespace `ATK.*` → `ClayPvsNPProof.ATK.*`; linhas `#print axioms` removidas
-- (a auditoria está em `ClayPvsNPProof/Audit.lean`). Alterações específicas: nenhuma além das comuns.
import ClayPvsNPProof.ATK.Compilador

/-!
# ATK — Ponte B4, marco M2d (parte 2a): ferramentas da linguagem de laços

Ferramentas genéricas sobre os programas de `ClayPvsNPProof.ATK.Compilador`, usadas pelo gerador da redução de
Cook–Levin:

* `seqC`, `Emite`, `GeraU`: blocos que emitem uma saída fixa e preservam um conjunto de
  registradores; `geraU_forU` (laço contado);
* `powLoop`, `polyZ`: `y += P(x)` para qualquer `P : Polynomial ℕ` por laços aninhados
  (`polyZ_spec`: semântica exata e custo);
* `arit`: a fase aritmética do gerador (`n = |w|`, `Q = q(n)`, `m = 2n+2+Q`, `T = p(m)`, e as
  alturas do tableau), com `arit_spec` (ambiente final exato e custo `custoA`);
* `Poli`: funções cotadas por polinômios, fechadas por soma, produto, potência e composição;
  `poli_custoA`;
* `Emis`, `Cota`, `cota_emis`: programas de pura emissão custam e emitem no máximo
  `10 · tam · (V+1)^(prof+1)` a partir de ambientes limitados por `V`.

Nada aqui decide P vs NP. **CLOSED_MATH continua false.**
-/

namespace ClayPvsNPProof.ATK.CookLevinLacos

open Function ClayPvsNPProof.ATK.Compilador

variable {R : ℕ} (w : List Bool)

/-! ## Sequências de comandos -/

/-- Encadeia uma lista de comandos. -/
def seqC : List (Cmd R) → Cmd R
  | [] => .emit []
  | c :: cs => .seq c (seqC cs)

/-- Comando que não altera o ambiente (a partir de `E`) e emite `o`. -/
def Emite (c : Cmd R) (E : Env R) (o : List Bool) : Prop := sem w c E = (E, o)

theorem emite_seqC_nil (E : Env R) : Emite w (seqC []) E [] := rfl

theorem emite_seqC_cons {c : Cmd R} {cs : List (Cmd R)} {E : Env R} {o os : List Bool}
    (h1 : Emite w c E o) (h2 : Emite w (seqC cs) E os) : Emite w (seqC (c :: cs)) E (o ++ os) := by
  unfold Emite at h1 h2 ⊢
  simp [seqC, sem, h1, h2]

theorem sem_seqC_append : ∀ (cs₁ cs₂ : List (Cmd R)) (E : Env R),
    sem w (seqC (cs₁ ++ cs₂)) E = ((sem w (seqC cs₂) (sem w (seqC cs₁) E).1).1,
      (sem w (seqC cs₁) E).2 ++ (sem w (seqC cs₂) (sem w (seqC cs₁) E).1).2)
  | [], cs₂, E => by simp [seqC, sem]
  | c :: cs, cs₂, E => by
    simp only [List.cons_append, seqC, sem]
    rw [sem_seqC_append cs cs₂]
    simp

theorem emite_seqC_append {cs₁ cs₂ : List (Cmd R)} {E : Env R} {o₁ o₂ : List Bool}
    (h1 : Emite w (seqC cs₁) E o₁) (h2 : Emite w (seqC cs₂) E o₂) :
    Emite w (seqC (cs₁ ++ cs₂)) E (o₁ ++ o₂) := by
  unfold Emite at h1 h2 ⊢
  rw [sem_seqC_append, h1]
  simp [h2]

theorem emite_seqC_map {α : Type*} (f : α → Cmd R) (g : α → List Bool) {E : Env R} :
    ∀ l : List α, (∀ x ∈ l, Emite w (f x) E (g x)) → Emite w (seqC (l.map f)) E (l.flatMap g)
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.map_cons, List.flatMap_cons]
    exact emite_seqC_cons w (h x (by simp)) (emite_seqC_map f g xs (fun y hy => h y (by simp [hy])))

theorem emite_emit (s : List Bool) (E : Env R) : Emite w (.emit s) E s := rfl

/-! ## Blocos que emitem uma saída fixa e preservam registradores -/

/-- `E'` coincide com `E` nos registradores de `S`. -/
def Igual (S : List (Fin R)) (E E' : Env R) : Prop := ∀ r ∈ S, E' r = E r

theorem igual_refl (S : List (Fin R)) (E : Env R) : Igual S E E := fun _ _ => rfl

theorem igual_trans {S : List (Fin R)} {E₁ E₂ E₃ : Env R} (h₁ : Igual S E₁ E₂) (h₂ : Igual S E₂ E₃) :
    Igual S E₁ E₃ := fun r hr => (h₂ r hr).trans (h₁ r hr)

/-- Para todo ambiente que coincide com `E₀` em `S`, o comando emite `o` e preserva `S`. -/
def GeraU (c : Cmd R) (E₀ : Env R) (S : List (Fin R)) (o : List Bool) : Prop :=
  ∀ E, Igual S E₀ E → (sem w c E).2 = o ∧ Igual S E (sem w c E).1

theorem geraU_emite {c : Cmd R} {E₀ : Env R} {S : List (Fin R)} {o : List Bool}
    (h : ∀ E, Igual S E₀ E → Emite w c E o) : GeraU w c E₀ S o := by
  intro E hE
  have := h E hE
  unfold Emite at this
  rw [this]
  exact ⟨rfl, igual_refl S E⟩

theorem geraU_nil (E₀ : Env R) (S : List (Fin R)) : GeraU w (seqC []) E₀ S [] :=
  geraU_emite w (fun E _ => emite_seqC_nil w E)

theorem geraU_cons {c : Cmd R} {cs : List (Cmd R)} {E₀ : Env R} {S : List (Fin R)} {o os : List Bool}
    (h₁ : GeraU w c E₀ S o) (h₂ : GeraU w (seqC cs) E₀ S os) :
    GeraU w (seqC (c :: cs)) E₀ S (o ++ os) := by
  intro E hE
  obtain ⟨o₁, e₁⟩ := h₁ E hE
  obtain ⟨o₂, e₂⟩ := h₂ (sem w c E).1 (igual_trans hE e₁)
  simp only [seqC, sem]
  exact ⟨by rw [o₁, o₂], igual_trans e₁ e₂⟩

theorem geraU_append {cs₁ cs₂ : List (Cmd R)} {E₀ : Env R} {S : List (Fin R)} {o₁ o₂ : List Bool}
    (h₁ : GeraU w (seqC cs₁) E₀ S o₁) (h₂ : GeraU w (seqC cs₂) E₀ S o₂) :
    GeraU w (seqC (cs₁ ++ cs₂)) E₀ S (o₁ ++ o₂) := by
  intro E hE
  obtain ⟨a₁, e₁⟩ := h₁ E hE
  obtain ⟨a₂, e₂⟩ := h₂ (sem w (seqC cs₁) E).1 (igual_trans hE e₁)
  rw [sem_seqC_append]
  exact ⟨by rw [a₁, a₂], igual_trans e₁ e₂⟩

theorem geraU_map {α : Type*} (f : α → Cmd R) (g : α → List Bool) {E₀ : Env R} {S : List (Fin R)} :
    ∀ l : List α, (∀ a ∈ l, GeraU w (f a) E₀ S (g a)) → GeraU w (seqC (l.map f)) E₀ S (l.flatMap g)
  | [], _ => geraU_nil w E₀ S
  | a :: l, h => by
    rw [List.map_cons, List.flatMap_cons]
    exact geraU_cons w (h a (by simp)) (geraU_map f g l (fun b hb => h b (by simp [hb])))

/-- **Laço contado**: se o corpo, com o índice `y = k`, emite `g k` e preserva `y` e `S`, o laço
emite a concatenação sobre `k < E₀ x`. -/
theorem geraU_forU {x y : Fin R} {body : Cmd R} {E₀ : Env R} {S : List (Fin R)}
    (hy : y ∉ S) (hx : x ∈ S) (g : ℕ → List Bool)
    (hb : ∀ k, GeraU w body (update E₀ y k) (y :: S) (g k)) :
    GeraU w (.forU x y body) E₀ S ((List.range (E₀ x)).flatMap g) := by
  have key : ∀ (m k : ℕ) (E : Env R), Igual S E₀ E → E y = k →
      (semFor (sem w body) y m E).2 = (List.range' k m).flatMap g ∧
        Igual S E (semFor (sem w body) y m E).1 := by
    intro m
    induction m with
    | zero => intro k E _ _; exact ⟨by simp [semFor], igual_refl S E⟩
    | succ m ih =>
      intro k E hE hk
      have hE' : Igual (y :: S) (update E₀ y k) E := by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · simp [hk]
        · rw [hE r hr]; simp [show r ≠ y from fun h => hy (h ▸ hr)]
      obtain ⟨o₁, e₁⟩ := hb k E hE'
      set E₁ := (sem w body E).1
      have hE₂ : Igual S E₀ (update E₁ y (E₁ y + 1)) := by
        intro r hr
        have hry : r ≠ y := fun h => hy (h ▸ hr)
        simp only [update_of_ne hry]
        exact (e₁ r (List.mem_cons_of_mem _ hr)).trans (hE r hr)
      have hy₁ : E₁ y = k := (e₁ y (List.mem_cons_self ..)).trans hk
      obtain ⟨o₂, e₂⟩ := ih (k + 1) _ hE₂ (by simp [hy₁])
      simp only [semFor]
      refine ⟨?_, ?_⟩
      · rw [o₂, o₁, List.range'_succ, List.flatMap_cons]
      · intro r hr
        have hry : r ≠ y := fun h => hy (h ▸ hr)
        rw [e₂ r hr]
        simp only [update_of_ne hry]
        exact e₁ r (List.mem_cons_of_mem _ hr)
  intro E hE
  have hxE : E x = E₀ x := hE x hx
  obtain ⟨o, e⟩ := key (E x) 0 (update E y 0) (by
    intro r hr; rw [update_of_ne (fun h : r = y => hy (h ▸ hr))]; exact hE r hr) (by simp)
  simp only [sem]
  refine ⟨by rw [o, List.range'_eq_map_range]; simp [hxE], ?_⟩
  intro r hr
  rw [e r hr]
  simp [update_of_ne (fun h : r = y => hy (h ▸ hr))]

theorem geraU_congr {c : Cmd R} {E₀ : Env R} {S : List (Fin R)} {o o' : List Bool}
    (h : GeraU w c E₀ S o) (e : o = o') : GeraU w c E₀ S o' := e ▸ h

theorem forall₂_map_map {α γ δ : Type*} {Rel : γ → δ → Prop} (f : α → γ) (g : α → δ) :
    ∀ l : List α, (∀ a ∈ l, Rel (f a) (g a)) → List.Forall₂ Rel (l.map f) (l.map g)
  | [], _ => List.Forall₂.nil
  | a :: l, h => List.Forall₂.cons (h a (by simp)) (forall₂_map_map f g l (fun b hb => h b (by simp [hb])))

theorem forall₂_append {γ δ : Type*} {Rel : γ → δ → Prop} {l₁ l₂ : List γ} {m₁ m₂ : List δ}
    (h₁ : List.Forall₂ Rel l₁ m₁) (h₂ : List.Forall₂ Rel l₂ m₂) :
    List.Forall₂ Rel (l₁ ++ l₂) (m₁ ++ m₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | cons h _ ih => exact List.Forall₂.cons h ih

theorem forall₂_flatMap {α γ δ : Type*} {Rel : γ → δ → Prop} (f : α → List γ) (g : α → List δ) :
    ∀ l : List α, (∀ a ∈ l, List.Forall₂ Rel (f a) (g a)) →
      List.Forall₂ Rel (l.flatMap f) (l.flatMap g)
  | [], _ => List.Forall₂.nil
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact forall₂_append (h a (by simp)) (forall₂_flatMap f g l (fun b hb => h b (by simp [hb])))

/-! ## Laços aninhados: `y += x ^ k` -/

/-- `|cs|` laços aninhados sobre `x` (contadores `cs`) com `inc y` no centro. -/
def powLoop (x y : Fin R) : List (Fin R) → Cmd R
  | [] => .inc y
  | c :: cs => .forU x c (powLoop x y cs)

theorem custoFor_le (f : Env R → ℕ) (g : Env R → Env R × List Bool) (y : Fin R) (P : Env R → Prop)
    (B : ℕ) (h : ∀ E, P E → f E ≤ B ∧ P (update (g E).1 y ((g E).1 y + 1))) :
    ∀ m E, P E → custoFor f g y m E ≤ m * (B + 2) + 1
  | 0, E, _ => by simp [custoFor]
  | m + 1, E, hE => by
    obtain ⟨h1, h2⟩ := h E hE
    have := custoFor_le f g y P B h m _ h2
    simp only [custoFor]
    rw [Nat.succ_mul]
    omega

theorem powLoop_spec (x y : Fin R) : ∀ (cs : List (Fin R)), (x :: y :: cs).Nodup →
    ∀ (W : ℕ) (E : Env R), E x ≤ W → (∀ c ∈ cs, E c ≤ W) →
      (sem w (powLoop x y cs) E).2 = [] ∧
      (sem w (powLoop x y cs) E).1 y = E y + E x ^ cs.length ∧
      (∀ z, z ≠ y → z ∉ cs → (sem w (powLoop x y cs) E).1 z = E z) ∧
      (∀ c ∈ cs, (sem w (powLoop x y cs) E).1 c ≤ W) ∧
      custo w (powLoop x y cs) E ≤ (10 * W + 10) ^ (cs.length + 1)
  | [], hnd, W, E, hx, _ => by
    refine ⟨rfl, by simp [powLoop, sem], fun z hz _ => by simp [powLoop, sem, update_of_ne hz], by simp,
      by simp [powLoop, custo]; try omega⟩
  | c :: cs, hnd, W, E, hx, hcs => by
    have hxy : x ≠ y := by intro h; simp [h] at hnd
    have hxc : x ≠ c := by intro h; simp [h] at hnd
    have hyc : y ≠ c := by intro h; simp [h] at hnd
    have hxcs : x ∉ cs := by intro h; simp [h] at hnd
    have hycs : y ∉ cs := by intro h; simp [h] at hnd
    have hccs : c ∉ cs := by simp at hnd; tauto
    have hnd' : (x :: y :: cs).Nodup := by simp at hnd ⊢; tauto
    have ih := powLoop_spec x y cs hnd' W
    set v := E x
    set body := powLoop x y cs
    have inner : ∀ m (E' : Env R), E' x = v → (∀ c' ∈ cs, E' c' ≤ W) →
        (semFor (sem w body) c m E').2 = [] ∧
        (semFor (sem w body) c m E').1 y = E' y + m * v ^ cs.length ∧
        (∀ z, z ≠ y → z ∉ cs → z ≠ c → (semFor (sem w body) c m E').1 z = E' z) ∧
        (semFor (sem w body) c m E').1 c = E' c + m ∧
        (∀ c' ∈ cs, (semFor (sem w body) c m E').1 c' ≤ W) := by
      intro m
      induction m with
      | zero => intro E' _ hE'; exact ⟨rfl, by simp [semFor], fun _ _ _ _ => rfl, rfl, hE'⟩
      | succ m ihm =>
        intro E' hx' hE'
        obtain ⟨o1, y1, z1, c1, -⟩ := ih E' (hx' ▸ hx) hE'
        have hb := ih E' (hx' ▸ hx) hE'
        set E₁ := (sem w body E').1
        have hx₁ : update E₁ c (E₁ c + 1) x = v := by
          rw [update_of_ne hxc, z1 x hxy hxcs, hx']
        have hcs₁ : ∀ c' ∈ cs, update E₁ c (E₁ c + 1) c' ≤ W := by
          intro c' hc'
          rw [update_of_ne (fun h : c' = c => hccs (h ▸ hc'))]
          exact hb.2.2.2.1 c' hc'
        obtain ⟨o2, y2, z2, c2, k2⟩ := ihm _ hx₁ hcs₁
        simp only [semFor]
        refine ⟨by rw [o1, o2]; rfl, ?_, ?_, ?_, k2⟩
        · rw [y2, update_of_ne hyc, y1, hx']
          ring
        · intro z hz hzcs hzc
          rw [z2 z hz hzcs hzc, update_of_ne hzc, z1 z hz hzcs]
        · rw [c2, update_self, z1 c hyc.symm hccs]
          ring
    have hE0x : update E c 0 x = v := by rw [update_of_ne hxc]
    have hE0cs : ∀ c' ∈ cs, update E c 0 c' ≤ W := by
      intro c' hc'
      rw [update_of_ne (fun h : c' = c => hccs (h ▸ hc'))]
      exact hcs c' (List.mem_cons_of_mem _ hc')
    obtain ⟨o, yv, zv, cv, kv⟩ := inner v (update E c 0) hE0x hE0cs
    have hcost := custoFor_le (custo w body) (sem w body) c
      (fun E' => E' x = v ∧ ∀ c' ∈ cs, E' c' ≤ W) ((10 * W + 10) ^ (cs.length + 1))
      (fun E' ⟨hx', hE'⟩ => by
        obtain ⟨-, -, z1, k1, h1⟩ := ih E' (hx' ▸ hx) hE'
        refine ⟨h1, ?_, ?_⟩
        · rw [update_of_ne hxc, z1 x hxy hxcs, hx']
        · intro c' hc'
          rw [update_of_ne (fun h : c' = c => hccs (h ▸ hc'))]
          exact k1 c' hc')
      v (update E c 0) ⟨hE0x, hE0cs⟩
    simp only [powLoop, sem, custo]
    refine ⟨o, ?_, ?_, ?_, ?_⟩
    · rw [yv, update_of_ne hyc, List.length_cons, pow_succ]
      ring
    · intro z hz hzcs
      have hzc : z ≠ c := fun h => hzcs (h ▸ List.mem_cons_self ..)
      rw [zv z hz (fun h => hzcs (List.mem_cons_of_mem _ h)) hzc, update_of_ne hzc]
    · intro c' hc'
      rcases List.mem_cons.mp hc' with rfl | hc'
      · rw [cv, update_self]; simpa using hx
      · exact kv c' hc'
    · have hc : E c ≤ W := hcs c (List.mem_cons_self ..)
      have hv : v ≤ W := hx
      have hX : 1 ≤ (10 * W + 10) ^ (cs.length + 1) := Nat.one_le_pow _ _ (by omega)
      rw [List.length_cons, pow_succ]
      set X := (10 * W + 10) ^ (cs.length + 1)
      have : v * (X + 2) ≤ W * (X + 2) := Nat.mul_le_mul_right _ hv
      nlinarith

/-! ## Sequências: custo -/

theorem one_le_custo_seqC : ∀ (cs : List (Cmd R)) (E : Env R), 1 ≤ custo w (seqC cs) E
  | [], _ => by simp [seqC, custo]
  | c :: cs, E => by
    simp only [seqC, custo]
    have := one_le_custo_seqC cs (sem w c E).1
    omega

theorem custo_seqC_append : ∀ (cs₁ cs₂ : List (Cmd R)) (E : Env R),
    custo w (seqC (cs₁ ++ cs₂)) E = custo w (seqC cs₂) (sem w (seqC cs₁) E).1 + custo w (seqC cs₁) E - 1
  | [], cs₂, E => by simp [seqC, sem, custo]
  | c :: cs, cs₂, E => by
    simp only [List.cons_append, seqC, sem, custo]
    rw [custo_seqC_append cs cs₂]
    have := one_le_custo_seqC w cs (sem w c E).1
    omega

/-- Acumulação: cada comando soma `δ a` a `y`, preserva o invariante e custa no máximo `B`. -/
theorem seqC_acum {α : Type*} (F : α → Cmd R) (δ : α → ℕ) (y : Fin R) (Inv : Env R → Prop) (B : ℕ) :
    ∀ (l : List α), (∀ a ∈ l, ∀ E, Inv E → (sem w (F a) E).2 = [] ∧ (sem w (F a) E).1 y = E y + δ a ∧
      Inv (sem w (F a) E).1 ∧ custo w (F a) E ≤ B) → ∀ (E : Env R), Inv E →
      (sem w (seqC (l.map F)) E).2 = [] ∧ (sem w (seqC (l.map F)) E).1 y = E y + (l.map δ).sum ∧
      Inv (sem w (seqC (l.map F)) E).1 ∧ custo w (seqC (l.map F)) E ≤ l.length * B + 1
  | [], _, E, hE => by simp [seqC, sem, custo, hE]
  | a :: l, hc, E, hE => by
    obtain ⟨o1, y1, i1, k1⟩ := hc a (List.mem_cons_self ..) E hE
    obtain ⟨o2, y2, i2, k2⟩ := seqC_acum F δ y Inv B l (fun b hb => hc b (List.mem_cons_of_mem _ hb)) _ i1
    simp only [List.map_cons, seqC, sem, custo, List.sum_cons, List.length_cons]
    refine ⟨by rw [o1, o2]; rfl, by rw [y2, y1]; ring, i2, ?_⟩
    rw [Nat.succ_mul]
    omega

/-! ## Polinômios -/

/-- A lista de expoentes: `k` repetido `coeff k` vezes. -/
noncomputable def expoentes (P : Polynomial ℕ) : List ℕ :=
  (List.range (P.natDegree + 1)).flatMap fun k => List.replicate (P.coeff k) k

theorem sum_range_list (f : ℕ → ℕ) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, sum_range_list f n,
      Finset.sum_range_succ]; simp

theorem sum_flatMap_sum {α : Type*} (f : α → List ℕ) : ∀ l : List α,
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum
  | [] => by simp
  | a :: l => by rw [List.flatMap_cons, List.sum_append, sum_flatMap_sum f l]; simp

theorem sum_expoentes (P : Polynomial ℕ) (v : ℕ) : ((expoentes P).map fun k => v ^ k).sum = P.eval v := by
  rw [Polynomial.eval_eq_sum_range, ← sum_range_list, expoentes, List.map_flatMap, sum_flatMap_sum]
  congr 1
  refine List.map_congr_left (fun k _ => ?_)
  simp [List.map_replicate, List.sum_replicate]

theorem le_natDegree_of_mem_expoentes {P : Polynomial ℕ} {k : ℕ} (h : k ∈ expoentes P) :
    k ≤ P.natDegree := by
  obtain ⟨j, hj, hk⟩ := List.mem_flatMap.mp h
  rw [List.eq_of_mem_replicate hk]
  exact Nat.lt_succ_iff.mp (List.mem_range.mp hj)

/-- `y += P(x)`, com contadores `cs` (zerados no fim). -/
noncomputable def polyZ (P : Polynomial ℕ) (x y : Fin R) (cs : List (Fin R)) : Cmd R :=
  seqC ((expoentes P).map (fun k => powLoop x y (cs.take k)) ++ cs.map Cmd.zero)

theorem sem_zeros : ∀ (cs : List (Fin R)) (E : Env R),
    (sem w (seqC (cs.map Cmd.zero)) E).2 = [] ∧
    (∀ z, z ∉ cs → (sem w (seqC (cs.map Cmd.zero)) E).1 z = E z) ∧
    (∀ c ∈ cs, (sem w (seqC (cs.map Cmd.zero)) E).1 c = 0) ∧
    custo w (seqC (cs.map Cmd.zero)) E ≤ (cs.map fun c => 2 * E c + 1).sum + 1
  | [], E => by simp [seqC, sem, custo]
  | c :: cs, E => by
    obtain ⟨o, z, k, h⟩ := sem_zeros cs (update E c 0)
    simp only [List.map_cons, seqC, sem, custo, List.sum_cons]
    refine ⟨o, fun y hy => ?_, fun c' hc' => ?_, ?_⟩
    · rw [z y (fun h => hy (List.mem_cons_of_mem _ h)),
        update_of_ne (fun h : y = c => hy (h ▸ List.mem_cons_self ..))]
    · by_cases h' : c' ∈ cs
      · exact k c' h'
      · rcases List.mem_cons.mp hc' with rfl | h''
        · rw [z c' h', update_self]
        · exact absurd h'' h'
    · have : (cs.map fun c' => 2 * update E c 0 c' + 1).sum ≤ (cs.map fun c' => 2 * E c' + 1).sum := by
        apply List.sum_le_sum
        intro c' _
        by_cases h : c' = c
        · subst h; simp
        · simp [update_of_ne h]
      omega

theorem polyZ_spec (P : Polynomial ℕ) (x y : Fin R) (cs : List (Fin R)) (hnd : (x :: y :: cs).Nodup)
    (hdeg : P.natDegree ≤ cs.length) (W : ℕ) (E : Env R) (hx : E x ≤ W) (hcs : ∀ c ∈ cs, E c = 0) :
    sem w (polyZ P x y cs) E = (update E y (E y + P.eval (E x)), []) ∧
    custo w (polyZ P x y cs) E ≤ (expoentes P).length * (10 * W + 10) ^ (cs.length + 1) + 1 +
      (cs.length * (2 * W + 1) + 1) := by
  have hxy : x ≠ y := by intro h; simp [h] at hnd
  have hxcs : x ∉ cs := by intro h; simp [h] at hnd
  have hycs : y ∉ cs := by intro h; simp [h] at hnd
  set Inv : Env R → Prop := fun E' => E' x = E x ∧ (∀ c ∈ cs, E' c ≤ W) ∧
    ∀ z, z ≠ y → z ∉ cs → E' z = E z
  have hacc := seqC_acum w (fun k => powLoop x y (cs.take k)) (fun k => E x ^ k) y Inv
    ((10 * W + 10) ^ (cs.length + 1)) (expoentes P) (fun k hk E' ⟨hx', hc', hz'⟩ => by
      have hk' : k ≤ cs.length := (le_natDegree_of_mem_expoentes hk).trans hdeg
      have hnd' : (x :: y :: cs.take k).Nodup := by
        refine List.Nodup.sublist ?_ hnd
        exact List.Sublist.cons_cons _ (List.Sublist.cons_cons _ (List.take_sublist _ _))
      obtain ⟨o, yy, zz, kk, cc⟩ := powLoop_spec w x y (cs.take k) hnd' W E' (hx' ▸ hx)
        (fun c hc => hc' c (List.mem_of_mem_take hc))
      refine ⟨o, by rw [yy, hx', List.length_take, min_eq_left hk'], ⟨?_, ?_, ?_⟩, ?_⟩
      · rw [zz x hxy (fun h => hxcs (List.mem_of_mem_take h)), hx']
      · intro c hc
        by_cases h : c ∈ cs.take k
        · exact kk c h
        · rw [zz c (fun h' => hycs (h' ▸ hc)) h]; exact hc' c hc
      · intro z hz hzcs
        rw [zz z hz (fun h => hzcs (List.mem_of_mem_take h)), hz' z hz hzcs]
      · refine cc.trans (Nat.pow_le_pow_right (by omega) ?_)
        have := List.length_take_le k cs
        omega)
    E ⟨rfl, fun c hc => by rw [hcs c hc]; exact Nat.zero_le _, fun _ _ _ => rfl⟩
  obtain ⟨o1, y1, ⟨-, c1, z1⟩, k1⟩ := hacc
  set E₁ := (sem w (seqC ((expoentes P).map fun k => powLoop x y (cs.take k))) E).1 with hE₁
  obtain ⟨o2, z2, c2, k2⟩ := sem_zeros w cs E₁
  rw [sum_expoentes] at y1
  unfold polyZ
  rw [sem_seqC_append, custo_seqC_append]
  refine ⟨Prod.ext ?_ (by simp only [o1, List.nil_append]; exact o2), ?_⟩
  · funext r
    by_cases hr : r ∈ cs
    · have hry : r ≠ y := fun h => hycs (h ▸ hr)
      simp only
      rw [c2 r hr, update_of_ne hry, hcs r hr]
    · simp only
      rw [z2 r hr]
      by_cases hry : r = y
      · subst hry; rw [update_self, y1]
      · rw [update_of_ne hry, z1 r hry hr]
  · have hsum : (cs.map fun c => 2 * E₁ c + 1).sum ≤ cs.length * (2 * W + 1) := by
      have := List.sum_le_length_nsmul (cs.map fun c => 2 * E₁ c + 1) (2 * W + 1) (by
        intro a ha
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
        have := c1 c hc
        omega)
      simpa using this
    have hk1 : custo w (seqC ((expoentes P).map fun k => powLoop x y (cs.take k))) E ≤
        (expoentes P).length * (10 * W + 10) ^ (cs.length + 1) + 1 := k1
    rw [← hE₁]
    omega

/-! ## Passos com saída vazia -/

/-- `c` leva `E` a `E'` sem emitir nada, com custo `≤ k`. -/
def Passo (c : Cmd R) (E E' : Env R) (k : ℕ) : Prop := sem w c E = (E', []) ∧ custo w c E ≤ k

theorem passo_nil (E : Env R) : Passo w (seqC []) E E 1 := ⟨rfl, le_rfl⟩

theorem passo_cons {c : Cmd R} {cs : List (Cmd R)} {E E₁ E₂ : Env R} {k₁ k₂ : ℕ}
    (h₁ : Passo w c E E₁ k₁) (h₂ : Passo w (seqC cs) E₁ E₂ k₂) : Passo w (seqC (c :: cs)) E E₂ (k₁ + k₂) := by
  obtain ⟨s₁, c₁⟩ := h₁
  obtain ⟨s₂, c₂⟩ := h₂
  refine ⟨by simp [seqC, sem, s₁, s₂], ?_⟩
  simp only [seqC, custo, s₁]
  omega

theorem passo_mono {c : Cmd R} {E E' : Env R} {k k' : ℕ} (h : Passo w c E E' k) (hk : k ≤ k') :
    Passo w c E E' k' := ⟨h.1, h.2.trans hk⟩

theorem passo_lenIn (x : Fin R) (E : Env R) :
    Passo w (.lenIn x) E (update E x (E x + w.length)) (4 * w.length + 2) :=
  ⟨rfl, by simp [custo]; omega⟩

/-- Bloco linear: `r += Σ ss + k`. -/
def lin (r : Fin R) (ss : List (Fin R)) (k : ℕ) : Cmd R :=
  seqC (ss.map (Cmd.add r) ++ List.replicate k (Cmd.inc r))

theorem passo_incs (r : Fin R) : ∀ (k : ℕ) (E : Env R),
    Passo w (seqC (List.replicate k (Cmd.inc r))) E (update E r (E r + k)) (k + 1)
  | 0, E => by simpa using passo_nil w E
  | k + 1, E => by
    have := passo_cons w (c := .inc r) (k₁ := 1) ⟨rfl, le_rfl⟩ (passo_incs r k (update E r (E r + 1)))
    have e : update (update E r (E r + 1)) r (update E r (E r + 1) r + k) = update E r (E r + (k + 1)) := by
      rw [update_self, update_idem]; congr 1; omega
    rw [e] at this
    rw [List.replicate_succ]
    exact passo_mono w this (by omega)

theorem passo_lin (r : Fin R) : ∀ (ss : List (Fin R)), r ∉ ss → ∀ (k : ℕ) (E : Env R),
    Passo w (lin r ss k) E (update E r (E r + (ss.map E).sum + k))
      ((ss.map fun s => 4 * E s + 2).sum + k + 1)
  | [], _, k, E => by simpa [lin] using passo_incs w r k E
  | s :: ss, hr, k, E => by
    have hrs : r ≠ s := fun h => hr (h ▸ List.mem_cons_self ..)
    have hr' : r ∉ ss := fun h => hr (List.mem_cons_of_mem _ h)
    have h1 : Passo w (.add r s) E (update E r (E r + E s)) (4 * E s + 2) := ⟨rfl, by simp [custo]; omega⟩
    have h2 := passo_lin r ss hr' k (update E r (E r + E s))
    have e : (ss.map (update E r (E r + E s))) = ss.map E := List.map_congr_left (fun x hx => by
      rw [update_of_ne (fun h : x = r => hr' (h ▸ hx))])
    have e' : (ss.map fun x => 4 * update E r (E r + E s) x + 2) = ss.map fun x => 4 * E x + 2 :=
      List.map_congr_left (fun x hx => by rw [update_of_ne (fun h : x = r => hr' (h ▸ hx))])
    rw [e, e', update_self, update_idem] at h2
    have := passo_cons w h1 h2
    unfold lin
    simp only [List.map_cons, List.cons_append, List.sum_cons]
    rw [show E r + (E s + (ss.map E).sum) + k = E r + E s + (ss.map E).sum + k by ring]
    exact passo_mono w this (by omega)

/-! ## Cotas polinomiais -/

/-- `f` é cotada por um polinômio. -/
def Poli (f : ℕ → ℕ) : Prop := ∃ P : Polynomial ℕ, ∀ n, f n ≤ P.eval n

theorem eval_mono (P : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : P.eval a ≤ P.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _))

theorem poli_eval (P : Polynomial ℕ) : Poli fun n => P.eval n := ⟨P, fun _ => le_rfl⟩

theorem poli_const (c : ℕ) : Poli fun _ => c := ⟨Polynomial.C c, fun _ => by simp⟩

theorem poli_id : Poli fun n => n := ⟨Polynomial.X, fun _ => by simp⟩

theorem poli_le {f g : ℕ → ℕ} (h : ∀ n, f n ≤ g n) (hg : Poli g) : Poli f := by
  obtain ⟨P, hP⟩ := hg
  exact ⟨P, fun n => (h n).trans (hP n)⟩

theorem poli_add {f g : ℕ → ℕ} (hf : Poli f) (hg : Poli g) : Poli fun n => f n + g n := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨Q, hQ⟩ := hg
  exact ⟨P + Q, fun n => by simpa using Nat.add_le_add (hP n) (hQ n)⟩

theorem poli_mul {f g : ℕ → ℕ} (hf : Poli f) (hg : Poli g) : Poli fun n => f n * g n := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨Q, hQ⟩ := hg
  exact ⟨P * Q, fun n => by simpa using Nat.mul_le_mul (hP n) (hQ n)⟩

theorem poli_pow {f : ℕ → ℕ} (hf : Poli f) : ∀ k : ℕ, Poli fun n => f n ^ k
  | 0 => by simpa using poli_const 1
  | k + 1 => by simpa [pow_succ] using poli_mul (poli_pow hf k) hf

theorem poli_comp {f g : ℕ → ℕ} (hf : Poli f) (hg : Poli g) : Poli fun n => f (g n) := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨Q, hQ⟩ := hg
  exact ⟨P.comp Q, fun n => by rw [Polynomial.eval_comp]; exact (hP _).trans (eval_mono P (hQ n))⟩

theorem poli_eval_comp (P : Polynomial ℕ) {g : ℕ → ℕ} (hg : Poli g) : Poli fun n => P.eval (g n) :=
  poli_comp (poli_eval P) hg

/-! ## A fase aritmética do gerador -/

section arit

variable (L : ℕ)

/-- Número de registradores: 9 parâmetros e `L + 2` contadores. -/
abbrev RA : ℕ := 9 + (L + 2)

def rn : Fin (RA L) := ⟨0, by unfold RA; omega⟩
def rQ : Fin (RA L) := ⟨1, by unfold RA; omega⟩
def rip : Fin (RA L) := ⟨2, by unfold RA; omega⟩
def rm : Fin (RA L) := ⟨3, by unfold RA; omega⟩
def rT : Fin (RA L) := ⟨4, by unfold RA; omega⟩
def rT1 : Fin (RA L) := ⟨5, by unfold RA; omega⟩
def rHb : Fin (RA L) := ⟨6, by unfold RA; omega⟩
def rRr : Fin (RA L) := ⟨7, by unfold RA; omega⟩
def rH : Fin (RA L) := ⟨8, by unfold RA; omega⟩
def rt : Fin (RA L) := ⟨9, by unfold RA; omega⟩
def ri : Fin (RA L) := ⟨10, by unfold RA; omega⟩

@[simp] theorem rn_val : (rn L).val = 0 := rfl
@[simp] theorem rQ_val : (rQ L).val = 1 := rfl
@[simp] theorem rip_val : (rip L).val = 2 := rfl
@[simp] theorem rm_val : (rm L).val = 3 := rfl
@[simp] theorem rT_val : (rT L).val = 4 := rfl
@[simp] theorem rT1_val : (rT1 L).val = 5 := rfl
@[simp] theorem rHb_val : (rHb L).val = 6 := rfl
@[simp] theorem rRr_val : (rRr L).val = 7 := rfl
@[simp] theorem rH_val : (rH L).val = 8 := rfl
@[simp] theorem rt_val : (rt L).val = 9 := rfl
@[simp] theorem ri_val : (ri L).val = 10 := rfl

/-- Os contadores. -/
def ctrs : List (Fin (RA L)) := (List.finRange (L + 2)).map (Fin.natAdd 9)

theorem ctrs_nodup : (ctrs L).Nodup := (List.nodup_finRange _).map (Fin.natAdd_injective _ _)

theorem length_ctrs : (ctrs L).length = L + 2 := by simp [ctrs]

theorem ge_of_mem_ctrs {c : Fin (RA L)} (h : c ∈ ctrs L) : 9 ≤ c.val := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp h
  simp

theorem nodup_poly {x y : Fin (RA L)} (hx : x.val < 9) (hy : y.val < 9) (hxy : x ≠ y) :
    (x :: y :: ctrs L).Nodup := by
  refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, ctrs_nodup L⟩⟩
  · intro h
    rcases List.mem_cons.mp h with h | h
    · exact hxy h
    · have := ge_of_mem_ctrs L h; omega
  · intro h; have := ge_of_mem_ctrs L h; omega

/-- **A fase aritmética**: `n = |w|`, `Q = q(n)`, `m = 2n+2+Q`, `T = p(m)`, `T+1`,
`Hb = m + D·T + 1`, `Rr = D·T + 1 + d + D`, `H = m + Rr`. -/
noncomputable def arit (q p : Polynomial ℕ) (DD dd : ℕ) : Cmd (RA L) :=
  seqC [.lenIn (rn L), polyZ q (rn L) (rQ L) (ctrs L), lin (rip L) [rn L, rn L] 2,
    lin (rm L) [rip L, rQ L] 0, polyZ p (rm L) (rT L) (ctrs L), lin (rT1 L) [rT L] 1,
    lin (rHb L) (rm L :: List.replicate DD (rT L)) 1,
    lin (rRr L) (List.replicate DD (rT L)) (1 + dd + DD), lin (rH L) [rm L, rRr L] 0]

/-- Custo de `polyZ` com entrada `≤ W`. -/
noncomputable def custoZ (P : Polynomial ℕ) (W : ℕ) : ℕ :=
  (expoentes P).length * (10 * W + 10) ^ (L + 2 + 1) + 1 + ((L + 2) * (2 * W + 1) + 1)

theorem passo_polyZ (P : Polynomial ℕ) {x y : Fin (RA L)} (hx : x.val < 9) (hy : y.val < 9) (hxy : x ≠ y)
    (hdeg : P.natDegree ≤ L + 2) (E : Env (RA L)) (hcs : ∀ c ∈ ctrs L, E c = 0) :
    Passo w (polyZ P x y (ctrs L)) E (update E y (E y + P.eval (E x))) (custoZ L P (E x)) := by
  obtain ⟨h1, h2⟩ := polyZ_spec w P x y (ctrs L) (nodup_poly L hx hy hxy) (by rw [length_ctrs]; exact hdeg)
    (E x) E le_rfl hcs
  exact ⟨h1, by rw [length_ctrs] at h2; exact h2⟩

theorem passo_congr {c : Cmd R} {E E' E'' : Env R} {k k' : ℕ} (h : Passo w c E E' k) (he : E' = E'')
    (hk : k ≤ k') : Passo w c E E'' k' := he ▸ passo_mono w h hk

/-- Custo da fase aritmética. -/
noncomputable def custoA (q p : Polynomial ℕ) (DD dd n : ℕ) : ℕ :=
  (4 * n + 2) + (custoZ L q n + ((8 * n + 7) + ((8 * n + 4 * q.eval n + 13) +
    (custoZ L p (2 * n + 2 + q.eval n) + ((4 * p.eval (2 * n + 2 + q.eval n) + 4) +
    ((4 * (2 * n + 2 + q.eval n) + 2 + DD * (4 * p.eval (2 * n + 2 + q.eval n) + 2) + 2) +
    ((DD * (4 * p.eval (2 * n + 2 + q.eval n) + 2) + (1 + dd + DD) + 1) +
    ((4 * (2 * n + 2 + q.eval n) + 2 + (4 * (DD * p.eval (2 * n + 2 + q.eval n) + (1 + dd + DD)) + 2) + 1) +
    1))))))))

set_option hygiene false in
/-- Avalia os ambientes da fase aritmética. -/
local macro "ev" : tactic => `(tactic| ((try simp only [v9, v8, v7, v6, v5, v4, v3, v2, v1, rn_val, rQ_val, rip_val,
    rm_val, rT_val, rT1_val, rHb_val, rRr_val, rH_val, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.map_replicate, List.sum_replicate, smul_eq_mul]) <;> (try simp) <;> (try omega)))

theorem arit_spec (q p : Polynomial ℕ) (DD dd : ℕ) (hq : q.natDegree ≤ L + 2) (hp : p.natDegree ≤ L + 2) :
    ∃ Ef : Env (RA L), Passo w (arit L q p DD dd) (fun _ => 0) Ef (custoA L q p DD dd w.length) ∧
      Ef (rn L) = w.length ∧ Ef (rQ L) = q.eval w.length ∧ Ef (rip L) = 2 * w.length + 2 ∧
      Ef (rm L) = 2 * w.length + 2 + q.eval w.length ∧
      Ef (rT L) = p.eval (2 * w.length + 2 + q.eval w.length) ∧
      Ef (rT1 L) = p.eval (2 * w.length + 2 + q.eval w.length) + 1 ∧
      Ef (rHb L) = 2 * w.length + 2 + q.eval w.length + DD * p.eval (2 * w.length + 2 + q.eval w.length) + 1 ∧
      Ef (rRr L) = DD * p.eval (2 * w.length + 2 + q.eval w.length) + (1 + dd + DD) ∧
      Ef (rH L) = 2 * w.length + 2 + q.eval w.length +
        (DD * p.eval (2 * w.length + 2 + q.eval w.length) + (1 + dd + DD)) ∧
      (∀ c ∈ ctrs L, Ef c = 0) := by
  have ue : ∀ (E : Env (RA L)) (r c : Fin (RA L)) (v : ℕ),
      update E r v c = if c.val = r.val then v else E c := by
    intro E r c v; simp [update_apply, Fin.ext_iff]
  obtain ⟨n, hn⟩ : ∃ n, w.length = n := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, q.eval n = Q := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, 2 * n + 2 + Q = m := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, p.eval m = T := ⟨_, rfl⟩
  obtain ⟨Rr, hR⟩ : ∃ Rr, DD * T + (1 + dd + DD) = Rr := ⟨_, rfl⟩
  have hc0 : ∀ c ∈ ctrs L, ¬ c.val < 9 := fun c hc => by have := ge_of_mem_ctrs L hc; omega
  obtain ⟨E1, h1⟩ : ∃ E : Env (RA L), E = update (fun _ => 0) (rn L) n := ⟨_, rfl⟩
  obtain ⟨E2, h2⟩ : ∃ E : Env (RA L), E = update E1 (rQ L) Q := ⟨_, rfl⟩
  obtain ⟨E3, h3⟩ : ∃ E : Env (RA L), E = update E2 (rip L) (2 * n + 2) := ⟨_, rfl⟩
  obtain ⟨E4, h4⟩ : ∃ E : Env (RA L), E = update E3 (rm L) m := ⟨_, rfl⟩
  obtain ⟨E5, h5⟩ : ∃ E : Env (RA L), E = update E4 (rT L) T := ⟨_, rfl⟩
  obtain ⟨E6, h6⟩ : ∃ E : Env (RA L), E = update E5 (rT1 L) (T + 1) := ⟨_, rfl⟩
  obtain ⟨E7, h7⟩ : ∃ E : Env (RA L), E = update E6 (rHb L) (m + DD * T + 1) := ⟨_, rfl⟩
  obtain ⟨E8, h8⟩ : ∃ E : Env (RA L), E = update E7 (rRr L) Rr := ⟨_, rfl⟩
  obtain ⟨E9, h9⟩ : ∃ E : Env (RA L), E = update E8 (rH L) (m + Rr) := ⟨_, rfl⟩
  -- valores
  have v1 : ∀ c, E1 c = if c.val = (rn L).val then n else 0 := by intro c; rw [h1, ue]
  have v2 : ∀ c, E2 c = if c.val = (rQ L).val then Q else E1 c := by intro c; rw [h2, ue]
  have v3 : ∀ c, E3 c = if c.val = (rip L).val then 2 * n + 2 else E2 c := by intro c; rw [h3, ue]
  have v4 : ∀ c, E4 c = if c.val = (rm L).val then m else E3 c := by intro c; rw [h4, ue]
  have v5 : ∀ c, E5 c = if c.val = (rT L).val then T else E4 c := by intro c; rw [h5, ue]
  have v6 : ∀ c, E6 c = if c.val = (rT1 L).val then T + 1 else E5 c := by intro c; rw [h6, ue]
  have v7 : ∀ c, E7 c = if c.val = (rHb L).val then m + DD * T + 1 else E6 c := by intro c; rw [h7, ue]
  have v8 : ∀ c, E8 c = if c.val = (rRr L).val then Rr else E7 c := by intro c; rw [h8, ue]
  have v9 : ∀ c, E9 c = if c.val = (rH L).val then m + Rr else E8 c := by intro c; rw [h9, ue]
  have pv : ∀ {E E' : Env (RA L)} {r : Fin (RA L)} {x : ℕ},
      (∀ c, E' c = if c.val = r.val then x else E c) → r.val < 9 → ∀ c : Fin (RA L), ¬ c.val < 9 →
        E' c = E c := by
    intro E E' r x hv hr c hc
    rw [hv c]; exact ite_eq_right (by omega)
  have zc : ∀ (E : Env (RA L)), (∀ c, ¬ c.val < 9 → E c = 0) → ∀ c ∈ ctrs L, E c = 0 :=
    fun E hE c hc => hE c (hc0 c hc)
  have z1 : ∀ c : Fin (RA L), ¬ c.val < 9 → E1 c = 0 := by
    intro c hc; rw [v1]; exact ite_eq_right (by rw [rn_val]; omega)
  have z4 : ∀ c : Fin (RA L), ¬ c.val < 9 → E4 c = 0 := fun c hc =>
    (pv v4 (by simp) c hc).trans ((pv v3 (by simp) c hc).trans ((pv v2 (by simp) c hc).trans (z1 c hc)))
  have z9 : ∀ c : Fin (RA L), ¬ c.val < 9 → E9 c = 0 := fun c hc =>
    (pv v9 (by simp) c hc).trans ((pv v8 (by simp) c hc).trans ((pv v7 (by simp) c hc).trans
      ((pv v6 (by simp) c hc).trans ((pv v5 (by simp) c hc).trans (z4 c hc)))))
  have s1 : Passo w (.lenIn (rn L)) (fun _ => 0) E1 (4 * n + 2) :=
    passo_congr w (passo_lenIn w _ _) (by rw [h1, hn]; simp) (by rw [hn])
  have s2 : Passo w (polyZ q (rn L) (rQ L) (ctrs L)) E1 E2 (custoZ L q n) :=
    passo_congr w (passo_polyZ w L q (x := rn L) (y := rQ L) (by simp) (by simp) (by simp [Fin.ext_iff]) hq E1
      (zc E1 z1)) (by rw [h2]; congr 1; ev) (by ev)
  have s3 : Passo w (lin (rip L) [rn L, rn L] 2) E2 E3 (8 * n + 7) :=
    passo_congr w (passo_lin w (rip L) [rn L, rn L] (by simp [Fin.ext_iff]) 2 E2)
      (by rw [h3]; congr 1; ev) (by ev)
  have s4 : Passo w (lin (rm L) [rip L, rQ L] 0) E3 E4 (8 * n + 4 * Q + 13) :=
    passo_congr w (passo_lin w (rm L) [rip L, rQ L] (by simp [Fin.ext_iff]) 0 E3)
      (by rw [h4]; congr 1; ev) (by ev)
  have s5 : Passo w (polyZ p (rm L) (rT L) (ctrs L)) E4 E5 (custoZ L p m) :=
    passo_congr w (passo_polyZ w L p (x := rm L) (y := rT L) (by simp) (by simp) (by simp [Fin.ext_iff]) hp E4
      (zc E4 z4)) (by rw [h5]; congr 1; ev) (by ev)
  have s6 : Passo w (lin (rT1 L) [rT L] 1) E5 E6 (4 * T + 4) :=
    passo_congr w (passo_lin w (rT1 L) [rT L] (by simp [Fin.ext_iff]) 1 E5)
      (by rw [h6]; congr 1; ev) (by ev)
  have s7 : Passo w (lin (rHb L) (rm L :: List.replicate DD (rT L)) 1) E6 E7
      (4 * m + 2 + DD * (4 * T + 2) + 2) :=
    passo_congr w (passo_lin w (rHb L) (rm L :: List.replicate DD (rT L))
      (by simp [Fin.ext_iff, List.mem_replicate]) 1 E6)
      (by rw [h7]; congr 1; ev)
      (by ev)
  have s8 : Passo w (lin (rRr L) (List.replicate DD (rT L)) (1 + dd + DD)) E7 E8
      (DD * (4 * T + 2) + (1 + dd + DD) + 1) :=
    passo_congr w (passo_lin w (rRr L) (List.replicate DD (rT L))
      (by simp [Fin.ext_iff, List.mem_replicate]) (1 + dd + DD) E7)
      (by rw [h8]; congr 1; ev)
      (by ev)
  have s9 : Passo w (lin (rH L) [rm L, rRr L] 0) E8 E9 (4 * m + 2 + (4 * Rr + 2) + 1) :=
    passo_congr w (passo_lin w (rH L) [rm L, rRr L] (by simp [Fin.ext_iff]) 0 E8)
      (by rw [h9]; congr 1; ev) (by ev)
  have hall := passo_cons w s1 (passo_cons w s2 (passo_cons w s3 (passo_cons w s4 (passo_cons w s5
    (passo_cons w s6 (passo_cons w s7 (passo_cons w s8 (passo_cons w s9 (passo_nil w E9)))))))))
  simp only [hn, hQ, hm, hT, hR]
  refine ⟨E9, passo_mono w hall (le_of_eq ?_), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, zc E9 z9⟩
  · unfold custoA
    rw [hQ, hm, hT, hR]
  all_goals ev

end arit

theorem poli_custoZ (L : ℕ) (P : Polynomial ℕ) {g : ℕ → ℕ} (hg : Poli g) :
    Poli fun n => custoZ L P (g n) := by
  unfold custoZ
  exact poli_add (poli_add (poli_mul (poli_const _) (poli_pow (poli_add (poli_mul (poli_const _) hg)
    (poli_const _)) _)) (poli_const _)) (poli_add (poli_mul (poli_const _) (poli_add (poli_mul (poli_const _) hg)
    (poli_const _))) (poli_const _))

theorem poli_custoA (L : ℕ) (q p : Polynomial ℕ) (DD dd : ℕ) : Poli (custoA L q p DD dd) := by
  have hQ : Poli fun n => q.eval n := poli_eval q
  have hm : Poli fun n => 2 * n + 2 + q.eval n :=
    poli_add (poli_add (poli_mul (poli_const 2) poli_id) (poli_const 2)) hQ
  have hT : Poli fun n => p.eval (2 * n + 2 + q.eval n) := poli_eval_comp p hm
  show Poli fun n => custoA L q p DD dd n
  unfold custoA
  exact poli_add (poli_add (poli_mul (poli_const 4) poli_id) (poli_const 2))
    (poli_add (poli_custoZ L q poli_id)
    (poli_add (poli_add (poli_mul (poli_const 8) poli_id) (poli_const 7))
    (poli_add (poli_add (poli_add (poli_mul (poli_const 8) poli_id) (poli_mul (poli_const 4) hQ)) (poli_const 13))
    (poli_add (poli_custoZ L p hm)
    (poli_add (poli_add (poli_mul (poli_const 4) hT) (poli_const 4))
    (poli_add (poli_add (poli_add (poli_add (poli_mul (poli_const 4) hm) (poli_const 2))
      (poli_mul (poli_const DD) (poli_add (poli_mul (poli_const 4) hT) (poli_const 2)))) (poli_const 2))
    (poli_add (poli_add (poli_add (poli_mul (poli_const DD) (poli_add (poli_mul (poli_const 4) hT)
      (poli_const 2))) (poli_const _)) (poli_const 1))
    (poli_add (poli_add (poli_add (poli_add (poli_mul (poli_const 4) hm) (poli_const 2))
      (poli_add (poli_mul (poli_const 4) (poli_add (poli_mul (poli_const DD) hT) (poli_const _)))
        (poli_const 2))) (poli_const 1)) (poli_const 1)))))))))

/-! ## Cotas uniformes para a fase de emissão -/

/-- O comando escreve no registrador `r`. -/
def escreve : Cmd R → Fin R → Prop
  | .emit _, _ => False
  | .emitU _ _, _ => False
  | .zero x, r => x = r
  | .inc x, r => x = r
  | .add x _, r => x = r
  | .lenIn x, r => x = r
  | .seq c₁ c₂, r => escreve c₁ r ∨ escreve c₂ r
  | .forU _ y b, r => y = r ∨ escreve b r
  | .forBits b₀ b₁, r => escreve b₀ r ∨ escreve b₁ r

/-- Comandos de pura emissão: emissões e laços contados cujo corpo não mexe no contador. -/
def Emis : Cmd R → Prop
  | .emit _ => True
  | .emitU _ _ => True
  | .seq c₁ c₂ => Emis c₁ ∧ Emis c₂
  | .forU x y b => Emis b ∧ ¬ escreve b y ∧ x ≠ y
  | _ => False

/-- Tamanho (com os comprimentos emitidos). -/
def tam : Cmd R → ℕ
  | .emit s => s.length + 1
  | .emitU _ s => s.length + 1
  | .seq c₁ c₂ => tam c₁ + tam c₂
  | .forU _ _ b => tam b + 1
  | _ => 1

/-- Profundidade de laços. -/
def profL : Cmd R → ℕ
  | .seq c₁ c₂ => max (profL c₁) (profL c₂)
  | .forU _ _ b => profL b + 1
  | _ => 0

theorem semFor_nao_escreve (f : Env R → Env R × List Bool) (y r : Fin R) (hry : r ≠ y)
    (hf : ∀ E, (f E).1 r = E r) : ∀ m E, (semFor f y m E).1 r = E r
  | 0, E => rfl
  | m + 1, E => by
    simp only [semFor]
    rw [semFor_nao_escreve f y r hry hf m, update_of_ne hry, hf]

theorem sem_nao_escreve : ∀ (c : Cmd R), Emis c → ∀ r, ¬ escreve c r → ∀ E, (sem w c E).1 r = E r
  | .emit _, _, _, _, _ => rfl
  | .emitU _ _, _, _, _, _ => rfl
  | .seq c₁ c₂, ⟨h₁, h₂⟩, r, hr, E => by
    simp only [escreve, not_or] at hr
    simp only [sem]
    rw [sem_nao_escreve c₂ h₂ r hr.2, sem_nao_escreve c₁ h₁ r hr.1]
  | .forU x y b, ⟨hb, _, _⟩, r, hr, E => by
    simp only [escreve, not_or] at hr
    simp only [sem]
    rw [semFor_nao_escreve _ y r (Ne.symm hr.1) (sem_nao_escreve b hb r hr.2), update_of_ne (Ne.symm hr.1)]
  | .zero _, h, _, _, _ => h.elim
  | .inc _, h, _, _, _ => h.elim
  | .add _ _, h, _, _, _ => h.elim
  | .lenIn _, h, _, _, _ => h.elim
  | .forBits _ _, h, _, _, _ => h.elim

/-- Cota: a partir de ambientes limitados por `V`, custo `≤ b`, saída `≤ o`, ambiente limitado. -/
def Cota (c : Cmd R) (V b o : ℕ) : Prop :=
  ∀ E : Env R, (∀ r, E r ≤ V) → custo w c E ≤ b ∧ (sem w c E).2.length ≤ o ∧ ∀ r, (sem w c E).1 r ≤ V

theorem cota_mono {c : Cmd R} {V b o b' o' : ℕ} (h : Cota w c V b o) (hb : b ≤ b') (ho : o ≤ o') :
    Cota w c V b' o' := fun E hE => by
  obtain ⟨h1, h2, h3⟩ := h E hE
  exact ⟨h1.trans hb, h2.trans ho, h3⟩

theorem cota_seq {c₁ c₂ : Cmd R} {V b₁ o₁ b₂ o₂ : ℕ} (h₁ : Cota w c₁ V b₁ o₁) (h₂ : Cota w c₂ V b₂ o₂) :
    Cota w (.seq c₁ c₂) V (b₁ + b₂) (o₁ + o₂) := fun E hE => by
  obtain ⟨a1, a2, a3⟩ := h₁ E hE
  obtain ⟨d1, d2, d3⟩ := h₂ _ a3
  simp only [custo, sem, List.length_append]
  exact ⟨by omega, by omega, d3⟩

theorem cota_seqC {V : ℕ} : ∀ (cs : List (Cmd R)) (bs os : List ℕ),
    List.Forall₂ (fun c bo => Cota w c V bo.1 bo.2) cs (bs.zip os) → bs.length = os.length →
    Cota w (seqC cs) V (bs.sum + 1) os.sum
  | [], bs, os, h, hl => by
    rcases bs with _ | ⟨b, bs⟩ <;> rcases os with _ | ⟨o, os⟩
    · intro E hE; simp [seqC, custo, sem, hE]
    all_goals simp at hl h
  | c :: cs, b :: bs, o :: os, h, hl => by
    rw [List.zip_cons_cons] at h
    obtain ⟨hc, hcs⟩ := List.forall₂_cons.mp h
    have := cota_seq w hc (cota_seqC cs bs os hcs (by simpa using hl))
    exact cota_mono w this (by simp; omega) (by simp)
  | c :: cs, [], _, h, _ => by simp at h
  | c :: cs, _ :: _, [], h, _ => by simp at h

theorem cota_emis (V : ℕ) : ∀ c : Cmd R, Emis c →
    Cota w c V (10 * tam c * (V + 1) ^ (profL c + 1)) (10 * tam c * (V + 1) ^ (profL c + 1))
  | .emit s, _ => fun E hE => by
    refine ⟨?_, ?_, hE⟩
    · simp only [custo, tam, profL, zero_add, pow_one]; nlinarith
    · simp only [sem, tam, profL, zero_add, pow_one]; nlinarith
  | .emitU x s, _ => fun E hE => by
    have hx := hE x
    refine ⟨?_, ?_, hE⟩
    · simp only [custo, tam, profL, zero_add, pow_one]; nlinarith
    · simp only [sem, tam, profL, zero_add, pow_one, List.length_flatten, List.map_replicate,
        List.sum_replicate, smul_eq_mul]
      nlinarith
  | .seq c₁ c₂, ⟨h₁, h₂⟩ => by
    have a := cota_emis V c₁ h₁
    have b := cota_emis V c₂ h₂
    refine cota_mono w (cota_seq w a b) ?_ ?_ <;>
    · simp only [tam, profL]
      have e1 : (V + 1) ^ (profL c₁ + 1) ≤ (V + 1) ^ (max (profL c₁) (profL c₂) + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have e2 : (V + 1) ^ (profL c₂ + 1) ≤ (V + 1) ^ (max (profL c₁) (profL c₂) + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      nlinarith
  | .forU x y b, ⟨hb, hy, _⟩ => fun E hE => by
    have ih := cota_emis V b hb
    set B := 10 * tam b * (V + 1) ^ (profL b + 1)
    have inner : ∀ k (E' : Env R), (∀ r, E' r ≤ V) → E' y + k ≤ V →
        custoFor (custo w b) (sem w b) y k E' ≤ k * (B + 2) + 1 ∧
        (semFor (sem w b) y k E').2.length ≤ k * B ∧ ∀ r, (semFor (sem w b) y k E').1 r ≤ V := by
      intro k
      induction k with
      | zero => intro E' hE' _; simp [custoFor, semFor, hE']
      | succ k ihk =>
        intro E' hE' hk
        obtain ⟨c1, o1, r1⟩ := ih E' hE'
        have hy1 : (sem w b E').1 y = E' y := sem_nao_escreve w b hb y hy E'
        have hE₂ : ∀ r, update (sem w b E').1 y ((sem w b E').1 y + 1) r ≤ V := by
          intro r
          by_cases hr : r = y
          · subst hr; rw [update_self, hy1]; omega
          · rw [update_of_ne hr]; exact r1 r
        obtain ⟨c2, o2, r2⟩ := ihk _ hE₂ (by rw [update_self, hy1]; omega)
        simp only [custoFor, semFor, List.length_append]
        refine ⟨by rw [Nat.succ_mul]; omega, by rw [Nat.succ_mul]; omega, r2⟩
    have hx := hE x
    have hy0 := hE y
    have hE0 : ∀ r, update E y 0 r ≤ V := by
      intro r; by_cases hr : r = y
      · subst hr; simp
      · rw [update_of_ne hr]; exact hE r
    obtain ⟨c1, o1, r1⟩ := inner (E x) (update E y 0) hE0 (by simp; exact hx)
    have hX : 1 ≤ (V + 1) ^ (profL b + 1) := Nat.one_le_pow _ _ (by omega)
    have hB : (V + 1) ^ (profL b + 1 + 1) = (V + 1) ^ (profL b + 1) * (V + 1) := pow_succ _ _
    set X := (V + 1) ^ (profL b + 1)
    have hXV : V ≤ X * V := Nat.le_mul_of_pos_left V hX
    have eR : 10 * (tam b + 1) * (X * (V + 1)) = V * B + B + 10 * (X * V) + 10 * X := by
      simp only [B]; ring
    have hExB : E x * B ≤ V * B := Nat.mul_le_mul_right _ hx
    refine ⟨?_, ?_, r1⟩
    · simp only [custo, tam, profL]
      rw [hB, eR]
      have : E x * (B + 2) ≤ V * (B + 2) := Nat.mul_le_mul_right _ hx
      have e2 : V * (B + 2) = V * B + 2 * V := by ring
      omega
    · simp only [sem, tam, profL]
      rw [hB, eR]
      omega
  | .zero _, h => h.elim
  | .inc _, h => h.elim
  | .add _ _, h => h.elim
  | .lenIn _, h => h.elim
  | .forBits _ _, h => h.elim

/-- Emissão pura com profundidade `≤ k` que só escreve em registradores de `W`. -/
def EmisW (W : List (Fin R)) (k : ℕ) (c : Cmd R) : Prop :=
  Emis c ∧ profL c ≤ k ∧ ∀ r, escreve c r → r ∈ W

theorem emisW_emit (W : List (Fin R)) (k : ℕ) (s : List Bool) : EmisW W k (.emit s) :=
  ⟨trivial, Nat.zero_le _, fun _ h => h.elim⟩

theorem emisW_emitU (W : List (Fin R)) (k : ℕ) (x : Fin R) (s : List Bool) : EmisW W k (.emitU x s) :=
  ⟨trivial, Nat.zero_le _, fun _ h => h.elim⟩

theorem emisW_seqC {W : List (Fin R)} {k : ℕ} : ∀ cs : List (Cmd R), (∀ c ∈ cs, EmisW W k c) →
    EmisW W k (seqC cs)
  | [], _ => emisW_emit W k []
  | c :: cs, h => by
    obtain ⟨e1, p1, w1⟩ := h c (List.mem_cons_self ..)
    obtain ⟨e2, p2, w2⟩ := emisW_seqC cs (fun d hd => h d (List.mem_cons_of_mem _ hd))
    refine ⟨⟨e1, e2⟩, by simp only [seqC, profL]; omega, fun r hr => ?_⟩
    rcases hr with hr | hr
    · exact w1 r hr
    · exact w2 r hr

theorem emisW_forU {W : List (Fin R)} {k : ℕ} {x y : Fin R} {b : Cmd R} (h : EmisW W k b) (hy : y ∉ W)
    (hxy : x ≠ y) : EmisW (y :: W) (k + 1) (.forU x y b) := by
  obtain ⟨e, p, wr⟩ := h
  refine ⟨⟨e, fun h' => hy (wr y h'), hxy⟩, by simp only [profL]; omega, fun r hr => ?_⟩
  rcases hr with rfl | hr
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (wr r hr)

theorem emisW_mono {W W' : List (Fin R)} {k k' : ℕ} {c : Cmd R} (h : EmisW W k c) (hW : ∀ r ∈ W, r ∈ W')
    (hk : k ≤ k') : EmisW W' k' c :=
  ⟨h.1, h.2.1.trans hk, fun r hr => hW r (h.2.2 r hr)⟩

theorem wf_emis (A : ℕ) (β : Bool) : ∀ (c : Cmd R) (δ : ℕ), Emis c → δ + profL c ≤ A → WF A c δ β
  | .emit _, _, _, _ => trivial
  | .emitU _ _, _, _, _ => trivial
  | .seq c₁ c₂, δ, ⟨h₁, h₂⟩, hp => by
    simp only [profL] at hp
    exact ⟨wf_emis A β c₁ δ h₁ (by omega), wf_emis A β c₂ δ h₂ (by omega)⟩
  | .forU _ _ b, δ, ⟨hb, _, hxy⟩, hp => by
    simp only [profL] at hp
    exact ⟨hxy, by omega, wf_emis A β b (δ + 1) hb (by omega)⟩
  | .zero _, _, h, _ => h.elim
  | .inc _, _, h, _ => h.elim
  | .add _ _, _, h, _ => h.elim
  | .lenIn _, _, h, _ => h.elim
  | .forBits _ _, _, h, _ => h.elim

theorem wf_seqC (A : ℕ) (δ : ℕ) (β : Bool) : ∀ cs : List (Cmd R), (∀ c ∈ cs, WF A c δ β) →
    WF A (seqC cs) δ β
  | [], _ => trivial
  | c :: cs, h => ⟨h c (List.mem_cons_self ..), wf_seqC A δ β cs (fun d hd => h d (List.mem_cons_of_mem _ hd))⟩

theorem wf_powLoop (A : ℕ) (β : Bool) (x y : Fin R) : ∀ (cs : List (Fin R)) (δ : ℕ), x ∉ cs →
    δ + cs.length ≤ A → WF A (powLoop x y cs) δ β
  | [], _, _, _ => trivial
  | c :: cs, δ, hx, hA => by
    simp only [List.length_cons] at hA
    exact ⟨fun h => hx (h ▸ List.mem_cons_self ..), by omega,
      wf_powLoop A β x y cs (δ + 1) (fun h => hx (List.mem_cons_of_mem _ h)) (by omega)⟩

theorem wf_polyZ (A : ℕ) (β : Bool) (P : Polynomial ℕ) (x y : Fin R) (cs : List (Fin R)) (hx : x ∉ cs)
    (hA : cs.length ≤ A) : WF A (polyZ P x y cs) 0 β := by
  unfold polyZ
  refine wf_seqC A 0 β _ (fun c hc => ?_)
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hc
    exact wf_powLoop A β x y _ 0 (fun h => hx (List.mem_of_mem_take h))
      (by have := List.length_take_le' k cs; omega)
  · obtain ⟨c', -, rfl⟩ := List.mem_map.mp hc
    trivial

theorem wf_lin (A : ℕ) (δ : ℕ) (β : Bool) (r : Fin R) (ss : List (Fin R)) (hr : r ∉ ss) (k : ℕ) :
    WF A (lin r ss k) δ β := by
  unfold lin
  refine wf_seqC A δ β _ (fun c hc => ?_)
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
    exact fun h => hr (h ▸ hs)
  · rw [List.eq_of_mem_replicate hc]; trivial

theorem wf_arit (L : ℕ) (q p : Polynomial ℕ) (DD dd : ℕ) : WF (L + 2) (arit L q p DD dd) 0 false := by
  have hc : ∀ {x : Fin (RA L)}, x.val < 9 → x ∉ ctrs L := fun hx h => by
    have := ge_of_mem_ctrs L h; omega
  unfold arit
  refine wf_seqC _ 0 false _ (fun c hc' => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
  rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact wf_polyZ _ _ _ _ _ _ (hc (by simp)) (by rw [length_ctrs])
  · exact wf_lin _ _ _ _ _ (by simp [Fin.ext_iff]) _
  · exact wf_lin _ _ _ _ _ (by simp [Fin.ext_iff]) _
  · exact wf_polyZ _ _ _ _ _ _ (hc (by simp)) (by rw [length_ctrs])
  · exact wf_lin _ _ _ _ _ (by simp [Fin.ext_iff]) _
  · exact wf_lin _ _ _ _ _ (by simp [Fin.ext_iff, List.mem_replicate]) _
  · exact wf_lin _ _ _ _ _ (by simp [Fin.ext_iff, List.mem_replicate]) _
  · exact wf_lin _ _ _ _ _ (by simp [Fin.ext_iff]) _

end ClayPvsNPProof.ATK.CookLevinLacos

