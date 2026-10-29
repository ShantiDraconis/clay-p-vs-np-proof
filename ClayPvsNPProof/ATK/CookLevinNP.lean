-- Origem: kernel ATK, espelho público ShantiDraconis/atk-math-core-public @ ffc111a
-- (= ShantiDraconis/M-Core @ 390e378), arquivo imports/M-Core/atk-kernel/ATK/CookLevinNP.lean
-- (sha256 do original: a26cca2c6d2158b4…).
-- Alterações comuns: namespace `ATK.*` → `ClayPvsNPProof.ATK.*`; linhas `#print axioms` removidas
-- (a auditoria está em `ClayPvsNPProof/Audit.lean`). Alterações específicas: nenhuma além das comuns.
import ClayPvsNPProof.ATK.CookLevinGerador

/-!
# ATK — Ponte B4, marco M2d (parte 2c): Cook–Levin no modelo genuíno

Montagem final da NP-dificuldade de SAT:

* `gerador D`: a fase aritmética (`arit`) seguida da emissão do tableau (`progTab`), um programa
  bem formado da linguagem de laços (`wf_gerador`);
* `saida_gerador`: a saída do programa sobre `w` é exatamente `reducao D Tf Hf w`;
* `custo_gerador`: custo e tamanho da saída cotados por um polinômio em `|w|`
  (cotas uniformes da fase de emissão, `cota_emis`, e do bloco que lê a entrada);
* `red_SAT`: toda `L ∈ classeNP` se reduz a SAT por uma redução de Karp computada por uma
  `FinTM2` em tempo polinomial (o compilador verificado, `computavel`);
* **`cookLevin : CookLevin modeloPNP SAT`**.

Isto fecha a ponte B4 (Cook 1971; Levin 1973) no kernel. **CLOSED_MATH continua false**: P vs NP
continua aberto (a lacuna é `SATNotInP`).
-/

namespace ClayPvsNPProof.ATK.CookLevinNP

open Function Turing ClayPvsNPProof.ATK.Compilador ClayPvsNPProof.ATK.SATemNP ClayPvsNPProof.ATK.ModeloPNP ClayPvsNPProof.ATK.LigacaoPNP ClayPvsNPProof.ATK.CookLevinBase
  ClayPvsNPProof.ATK.CookLevinTableau ClayPvsNPProof.ATK.CookLevinReducao ClayPvsNPProof.ATK.CookLevinLacos ClayPvsNPProof.ATK.CookLevinGerador

variable {R : ℕ}

/-! ## Emissão pura dos impressores -/

section impressores
variable {W : List (Fin R)} {k : ℕ}

theorem emisW_pTermo (τ : Termo R) : EmisW W k (pTermo τ) := by
  unfold pTermo
  refine emisW_seqC _ (fun c hc => ?_)
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨x, -, rfl⟩ := List.mem_map.mp hc; exact emisW_emitU _ _ _ _
  · rw [List.mem_singleton.mp hc]; exact emisW_emit _ _ _

theorem emisW_pLit (b : Bool) (tag : List Bool) (ts : List (Termo R)) : EmisW W k (pLit b tag ts) := by
  unfold pLit
  refine emisW_seqC _ (fun c hc => ?_)
  simp only [List.mem_append, List.mem_singleton, List.mem_map] at hc
  rcases hc with (rfl | ⟨τ, -, rfl⟩) | rfl
  · exact emisW_emit _ _ _
  · exact emisW_pTermo τ
  · exact emisW_emit _ _ _

theorem emisW_lx {K : Type} [Fintype K] (b : Bool) (kk : K) (τt τi τj : Termo R) :
    EmisW W k (lx b kk τt τi τj) := emisW_pLit _ _ _
theorem emisW_ly (b : Bool) (τt τj : Termo R) : EmisW W k (ly b τt τj) := emisW_pLit _ _ _
theorem emisW_lz (b : Bool) (τt τj : Termo R) : EmisW W k (lz b τt τj) := emisW_pLit _ _ _

theorem emisW_pCla {lits : List (Cmd R)} (h : ∀ c ∈ lits, EmisW W k c) : EmisW W k (pCla lits) := by
  unfold pCla
  refine emisW_seqC _ (fun c hc => ?_)
  rcases List.mem_append.mp hc with hc | hc
  · exact h c hc
  · rw [List.mem_singleton.mp hc]; exact emisW_emit _ _ _

theorem emisW_pNoMax (lit : ℕ → Bool → Cmd R) (h : ∀ j b, EmisW W k (lit j b)) :
    ∀ l : List ℕ, ∀ c ∈ pNoMax lit l, EmisW W k c
  | [] => fun c hc => by simp [pNoMax] at hc
  | j :: js => fun c hc => by
    simp only [pNoMax, List.mem_append, List.mem_map] at hc
    rcases hc with ⟨j', -, rfl⟩ | hc
    · exact emisW_pCla (fun d hd => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl <;> exact h _ _)
    · exact emisW_pNoMax lit h js c hc

theorem emisW_pUmSo (N : ℕ) (lit : ℕ → Bool → Cmd R) (h : ∀ j b, EmisW W k (lit j b)) :
    EmisW W k (pUmSo N lit) := by
  unfold pUmSo
  refine emisW_seqC _ (fun c hc => ?_)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact emisW_pCla (fun d hd => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hd; exact h _ _)
  · exact emisW_pNoMax lit h _ c hc

end impressores

/-! ## Emissão pura das famílias -/

section familias
variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} {Λ σ : Type} (A : Tab K Γ Λ σ)

omit [DecidableEq K] in
theorem emisW_progE {rT1 rH t i : Fin R} (h1 : rT1 ≠ t) (h2 : rH ≠ i) (hti : t ≠ i) :
    EmisW [t, i] 2 (progE A rT1 rH t i) := by
  unfold progE
  refine emisW_forU (emisW_seqC _ (fun c hc => ?_)) (by simp [hti]) h1
  rcases List.mem_append.mp hc with hc | hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact emisW_pUmSo _ _ (fun _ _ => emisW_ly _ _ _)
    · exact emisW_pUmSo _ _ (fun _ _ => emisW_lz _ _ _)
  · obtain ⟨kk, -, rfl⟩ := List.mem_map.mp hc
    exact emisW_forU (emisW_pUmSo _ _ (fun _ _ => emisW_lx _ _ _ _ _)) (by simp) h2

omit [DecidableEq K] in
theorem emisW_progP {rT rH t i : Fin R} (h1 : rT ≠ t) (h2 : rH ≠ i) (hti : t ≠ i) :
    EmisW [t, i] 2 (progP A rT rH t i) := by
  unfold progP
  refine emisW_forU (emisW_seqC _ (fun c hc => ?_)) (by simp [hti]) h1
  simp only [List.mem_append, List.mem_singleton, List.mem_map] at hc
  rcases hc with (rfl | ⟨jv, -, rfl⟩) | ⟨kk, -, rfl⟩
  · exact emisW_pCla (fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl <;> exact emisW_ly _ _ _)
  · exact emisW_pCla (fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · exact emisW_ly _ _ _
      · exact emisW_lz _ _ _
      · exact emisW_lz _ _ _)
  · refine emisW_forU (emisW_seqC _ (fun c hc => ?_)) (by simp) h2
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hc
    exact emisW_pCla (fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · exact emisW_ly _ _ _
      · exact emisW_lx _ _ _ _ _
      · exact emisW_lx _ _ _ _ _)

omit [DecidableEq K] in
theorem emisW_progA {W : List (Fin R)} {k : ℕ} (rT : Fin R) (acc : Γ A.k₁) : EmisW W k (progA A rT acc) := by
  unfold progA
  refine emisW_seqC _ (fun c hc => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact emisW_pCla (fun d hd => by rw [List.mem_singleton.mp hd]; exact emisW_ly _ _ _)
  · exact emisW_pCla (fun d hd => by rw [List.mem_singleton.mp hd]; exact emisW_lx _ _ _ _ _)

omit [DecidableEq K] in
theorem emisW_antesC {W : List (Fin R)} {k : ℕ} (t : Fin R) (jl jv : ℕ) (p : A.Pat) :
    ∀ c ∈ antesC A t jl jv p, EmisW W k c := by
  intro c hc
  simp only [antesC, List.mem_cons, List.mem_flatMap, List.mem_map] at hc
  rcases hc with rfl | rfl | ⟨kk, -, ii, -, rfl⟩
  · exact emisW_ly _ _ _
  · exact emisW_lz _ _ _
  · exact emisW_lx _ _ _ _ _

omit [DecidableEq K] in
theorem emisW_progConseq {rHb t i : Fin R} (DD : ℕ) {ant : List (Cmd R)} (r : Turing.TM2.Cfg Γ Λ σ)
    (hant : ∀ c ∈ ant, EmisW [] 0 c) (h2 : rHb ≠ i) :
    EmisW [i] 1 (progConseq A rHb t i DD ant r) := by
  have cla : ∀ {W : List (Fin R)} {k : ℕ} {lits : List (Cmd R)}, (∀ c ∈ lits, EmisW W k c) →
      EmisW W k (pCla (ant ++ lits)) :=
    fun h => emisW_pCla (fun c hc => by
      rcases List.mem_append.mp hc with hc | hc
      · exact emisW_mono (hant c hc) (by simp) (Nat.zero_le _)
      · exact h c hc)
  unfold progConseq
  refine emisW_seqC _ (fun c hc => ?_)
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hc
  rcases hc with (rfl | rfl) | ⟨kk, -, rfl⟩
  · exact cla (fun d hd => by rw [List.mem_singleton.mp hd]; exact emisW_ly _ _ _)
  · exact cla (fun d hd => by rw [List.mem_singleton.mp hd]; exact emisW_lz _ _ _)
  · refine emisW_seqC _ (fun c hc => ?_)
    simp only [List.mem_append, List.mem_singleton, List.mem_map] at hc
    rcases hc with (⟨ii, -, rfl⟩ | rfl) | ⟨e, -, rfl⟩
    · exact cla (fun d hd => by rw [List.mem_singleton.mp hd]; exact emisW_lx _ _ _ _ _)
    · refine emisW_forU (W := []) (k := 0) (emisW_seqC _ (fun c hc => ?_)) (by simp) h2
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hc
      exact cla (fun d hd => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl <;> exact emisW_lx _ _ _ _ _)
    · split
      · exact emisW_seqC _ (fun c hc => by
          obtain ⟨a, -, rfl⟩ := List.mem_map.mp hc
          exact cla (fun d hd => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
            rcases hd with rfl | rfl <;> exact emisW_lx _ _ _ _ _))
      · exact cla (fun d hd => by rw [List.mem_singleton.mp hd]; exact emisW_lx _ _ _ _ _)

theorem emisW_progR {rT rHb t i : Fin R} (DD : ℕ) (h1 : rT ≠ t) (h2 : rHb ≠ i) (hti : t ≠ i) :
    EmisW [t, i] 2 (progR A rT rHb t i DD) := by
  unfold progR
  refine emisW_forU (emisW_seqC _ (fun c hc => ?_)) (by simp [hti]) h1
  obtain ⟨jl, -, rfl⟩ := List.mem_map.mp hc
  refine emisW_seqC _ (fun c hc => ?_)
  obtain ⟨jv, -, rfl⟩ := List.mem_map.mp hc
  refine emisW_seqC _ (fun c hc => ?_)
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hc
  unfold progRp
  split
  · exact emisW_progConseq A DD _ (emisW_antesC A t jl jv p) h2
  · exact emisW_seqC _ (fun c hc => by simp at hc)

/-- A lista de comandos da família (I). -/
noncomputable def listaI (e : Bool → Γ A.k₀) (cands : List (Γ A.k₀)) (rH rn rip rQ rm rRr t : Fin R) :
    List (Cmd R) :=
  [pCla [ly true (tc 0) (tc (ix A.labs (some A.l₀)))],
    pCla [lz true (tc 0) (tc (ix A.sts A.v₀))],
    seqC ((Tab.ks.filter (· ≠ A.k₀)).map fun k =>
      .forU rH t (pCla [lx true k (tc 0) (tr t 0) (tc (ix (A.vals k) none))])),
    progPre A.k₀ t (ix (A.vals A.k₀) (some (e false))) (ix (A.vals A.k₀) (some (e true))),
    pCla [lx true A.k₀ (tc 0) (tr2 rn rn 0) (tc (ix (A.vals A.k₀) (some (e false))))],
    pCla [lx true A.k₀ (tc 0) (tr2 rn rn 1) (tc (ix (A.vals A.k₀) (some (e true))))],
    .forU rQ t (seqC ((livres A cands).map (fun a => pCla [lx false A.k₀ (tc 0) (tr2 rip t 0) (tc a)]) ++
      [pCla [lx false A.k₀ (tc 0) (tr2 rip t 0) (tc (ix (A.vals A.k₀) none)),
        lx true A.k₀ (tc 0) (tr2 rip t 1) (tc (ix (A.vals A.k₀) none))]])),
    .forU rRr t (pCla [lx true A.k₀ (tc 0) (tr2 rm t 0) (tc (ix (A.vals A.k₀) none))])]

theorem progI_eq (e : Bool → Γ A.k₀) (cands : List (Γ A.k₀)) (rH rn rip rQ rm rRr t : Fin R) :
    progI A e cands rH rn rip rQ rm rRr t = seqC (listaI A e cands rH rn rip rQ rm rRr t) := rfl

omit [DecidableEq K] in
theorem nao_emis_progPre (k₀ : K) (rj : Fin R) (j₀ j₁ : ℕ) : ¬ Emis (progPre k₀ rj j₀ j₁) := by
  simp [progPre, Emis]

/-- Cada comando da lista (I), exceto o bloco da entrada, é de pura emissão (profundidade `≤ 1`). -/
theorem emis_listaI (e : Bool → Γ A.k₀) (cands : List (Γ A.k₀)) {rH rn rip rQ rm rRr t : Fin R}
    (hH : rH ≠ t) (hQ : rQ ≠ t) (hR : rRr ≠ t) :
    ∀ c ∈ listaI A e cands rH rn rip rQ rm rRr t,
      c = progPre A.k₀ t (ix (A.vals A.k₀) (some (e false))) (ix (A.vals A.k₀) (some (e true))) ∨
      EmisW [t] 1 c := by
  intro c hc
  simp only [listaI, List.mem_cons, List.not_mem_nil, or_false] at hc
  have lit1 : ∀ {W : List (Fin R)} {k : ℕ} {l : Cmd R}, EmisW W k l → EmisW W k (pCla [l]) :=
    fun h => emisW_pCla (fun d hd => by rw [List.mem_singleton.mp hd]; exact h)
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (lit1 (emisW_ly _ _ _))
  · exact Or.inr (lit1 (emisW_lz _ _ _))
  · refine Or.inr (emisW_seqC _ (fun c hc => ?_))
    obtain ⟨kk, -, rfl⟩ := List.mem_map.mp hc
    exact emisW_forU (W := []) (k := 0) (lit1 (emisW_lx _ _ _ _ _)) (by simp) hH
  · exact Or.inl rfl
  · exact Or.inr (lit1 (emisW_lx _ _ _ _ _))
  · exact Or.inr (lit1 (emisW_lx _ _ _ _ _))
  · refine Or.inr (emisW_forU (W := []) (k := 0) (emisW_seqC _ (fun c hc => ?_)) (by simp) hQ)
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨a, -, rfl⟩ := List.mem_map.mp hc
      exact lit1 (emisW_lx _ _ _ _ _)
    · rw [List.mem_singleton.mp hc]
      exact emisW_pCla (fun d hd => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl <;> exact emisW_lx _ _ _ _ _)
  · exact Or.inr (emisW_forU (W := []) (k := 0) (lit1 (emisW_lx _ _ _ _ _)) (by simp) hR)

end familias

/-! ## Cotas -/

section cotas
variable (w : List Bool)

/-- Cota uniforme de um programa de pura emissão. -/
def Cst (c : Cmd R) (V : ℕ) : ℕ := 10 * tam c * (V + 1) ^ (profL c + 1)

theorem cota_seqC_gen (V : ℕ) (bf of : Cmd R → ℕ) : ∀ cs : List (Cmd R),
    (∀ c ∈ cs, Cota w c V (bf c) (of c)) → Cota w (seqC cs) V ((cs.map bf).sum + 1) (cs.map of).sum
  | [], _ => fun E hE => by simp [seqC, custo, sem, hE]
  | c :: cs, h => by
    have := cota_seq w (h c (List.mem_cons_self ..))
      (cota_seqC_gen V bf of cs (fun d hd => h d (List.mem_cons_of_mem _ hd)))
    exact cota_mono w this (by simp; omega) (by simp)

theorem cota_emisW {W : List (Fin R)} {k : ℕ} {c : Cmd R} (h : EmisW W k c) (V : ℕ) :
    Cota w c V (Cst c V) (Cst c V) := cota_emis w V c h.1

theorem sem_puro {c : Cmd R} (h : EmisW [] 0 c) (E : Env R) : (sem w c E).1 = E :=
  funext fun r => sem_nao_escreve w c h.1 r (fun hr => by simpa using h.2.2 r hr) E

section pre
variable {K : Type} [Fintype K]

/-- As duas cláusulas do corpo do bloco da entrada. -/
noncomputable def clPre (k₀ : K) (rj : Fin R) (j₀ j₁ o : ℕ) (β : Bool) : Cmd R :=
  pCla [lx true k₀ (tc 0) (tr2 rj rj o) (tc (bif β then j₁ else j₀))]

theorem emisW_clPre {W : List (Fin R)} {k : ℕ} (k₀ : K) (rj : Fin R) (j₀ j₁ o : ℕ) (β : Bool) :
    EmisW W k (clPre k₀ rj j₀ j₁ o β) :=
  emisW_pCla (fun d hd => by rw [List.mem_singleton.mp hd]; exact emisW_lx _ _ _ _ _)

/-- Cota de custo e saída de um corpo do bloco da entrada. -/
noncomputable def Bc (k₀ : K) (rj : Fin R) (j₀ j₁ V : ℕ) : ℕ :=
  Cst (clPre k₀ rj j₀ j₁ 0 false) V + Cst (clPre k₀ rj j₀ j₁ 1 false) V +
    (Cst (clPre k₀ rj j₀ j₁ 0 true) V + Cst (clPre k₀ rj j₀ j₁ 1 true) V)

theorem custo_corpoPre (k₀ : K) (rj : Fin R) (j₀ j₁ V : ℕ) (β : Bool) (E : Env R) (hE : ∀ r, E r ≤ V) :
    custo w (corpoPre k₀ rj j₀ j₁ β) E ≤ Bc k₀ rj j₀ j₁ V + 2 ∧
    (sem w (corpoPre k₀ rj j₀ j₁ β) E).2.length ≤ Bc k₀ rj j₀ j₁ V := by
  have e : corpoPre k₀ rj j₀ j₁ β = seqC [clPre k₀ rj j₀ j₁ 0 β, clPre k₀ rj j₀ j₁ 1 β, .inc rj] := rfl
  have p1 := sem_puro w (emisW_clPre (W := []) (k := 0) k₀ rj j₀ j₁ 0 β) E
  have p2 := sem_puro w (emisW_clPre (W := []) (k := 0) k₀ rj j₀ j₁ 1 β) E
  obtain ⟨c1, o1, -⟩ := cota_emisW w (emisW_clPre (W := []) (k := 0) k₀ rj j₀ j₁ 0 β) V E hE
  obtain ⟨c2, o2, -⟩ := cota_emisW w (emisW_clPre (W := []) (k := 0) k₀ rj j₀ j₁ 1 β) V E hE
  rw [e]
  simp only [seqC, custo, sem, p1, p2, List.length_append, List.length_nil]
  cases β <;> simp only [Bc] at * <;> omega

theorem cota_progPre (k₀ : K) (rj : Fin R) (j₀ j₁ V : ℕ) (hw : w.length ≤ V) :
    Cota w (progPre k₀ rj j₀ j₁) V (2 * V + 1 + (2 * V + 1 + (V * (Bc k₀ rj j₀ j₁ V + 5) + 1)))
      (V * Bc k₀ rj j₀ j₁ V) := by
  set B := Bc k₀ rj j₀ j₁ V
  have bits : ∀ (l : List Bool) (E : Env R), (∀ r, E r ≤ V) → E rj + l.length ≤ V →
      custoBits (custo w (corpoPre k₀ rj j₀ j₁ false)) (custo w (corpoPre k₀ rj j₀ j₁ true))
        (sem w (corpoPre k₀ rj j₀ j₁ false)) (sem w (corpoPre k₀ rj j₀ j₁ true)) l E ≤
          l.length * (B + 5) + 1 ∧
      (semBits (sem w (corpoPre k₀ rj j₀ j₁ false)) (sem w (corpoPre k₀ rj j₀ j₁ true)) l E).2.length ≤
        l.length * B := by
    intro l
    induction l with
    | nil => intro E _ _; simp [custoBits, semBits]
    | cons b l ih =>
      intro E hE hl
      have hb : ∀ β : Bool, (if b then sem w (corpoPre k₀ rj j₀ j₁ true) else sem w (corpoPre k₀ rj j₀ j₁ false))
          = sem w (corpoPre k₀ rj j₀ j₁ b) := fun _ => by cases b <;> rfl
      have hc : (if b then custo w (corpoPre k₀ rj j₀ j₁ true) else custo w (corpoPre k₀ rj j₀ j₁ false))
          = custo w (corpoPre k₀ rj j₀ j₁ b) := by cases b <;> rfl
      obtain ⟨c1, o1⟩ := custo_corpoPre w k₀ rj j₀ j₁ V b E hE
      have hE' : ∀ r, update E rj (E rj + 1) r ≤ V := by
        intro r; by_cases hr : r = rj
        · subst hr; simp at hl ⊢; omega
        · rw [update_of_ne hr]; exact hE r
      obtain ⟨c2, o2⟩ := ih _ hE' (by simp at hl ⊢; omega)
      simp only [custoBits, semBits, hb b, hc, sem_corpoPre, List.length_append, List.length_cons]
      rw [sem_corpoPre] at o1
      constructor
      · rw [Nat.succ_mul]; omega
      · rw [Nat.succ_mul]; simp only at o1; omega
  intro E hE
  have hE0 : ∀ r, update E rj 0 r ≤ V := by
    intro r; by_cases hr : r = rj
    · subst hr; simp
    · rw [update_of_ne hr]; exact hE r
  obtain ⟨c1, o1⟩ := bits w (update E rj 0) hE0 (by simpa using hw)
  have hj := hE rj
  refine ⟨?_, ?_, ?_⟩
  · simp only [progPre, custo, sem]
    have : w.length * (B + 5) ≤ V * (B + 5) := Nat.mul_le_mul_right _ hw
    omega
  · simp only [progPre, sem, List.nil_append]
    have : w.length * B ≤ V * B := Nat.mul_le_mul_right _ hw
    omega
  · intro r
    simp only [progPre, sem, semBits_pre]
    by_cases hr : r = rj
    · subst hr; simpa using hw
    · rw [update_of_ne hr, update_of_ne hr]; exact hE r

end pre

theorem emis_seqC_mem : ∀ {cs : List (Cmd R)}, Emis (seqC cs) → ∀ c ∈ cs, Emis c
  | [], _, c, hc => by simp at hc
  | d :: ds, h, c, hc => by
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact emis_seqC_mem h.2 c hc

open Classical in
/-- Cota de um comando: a uniforme se for de pura emissão, senão `pre`. -/
noncomputable def bfE (pre V : ℕ) (c : Cmd R) : ℕ := if Emis c then Cst c V else pre

theorem bfE_emis {pre V : ℕ} {c : Cmd R} (h : Emis c) : bfE pre V c = Cst c V := by
  unfold bfE; exact ite_eq_left h

theorem bfE_nao {pre V : ℕ} {c : Cmd R} (h : ¬ Emis c) : bfE pre V c = pre := by
  unfold bfE; exact ite_eq_right h

end cotas

section cotasFam
variable (w : List Bool) {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} {Λ σ : Type}
  (A : Tab K Γ Λ σ)

/-- Cotas do bloco da entrada. -/
noncomputable def bPre (k₀ : K) (rj : Fin R) (j₀ j₁ V : ℕ) : ℕ :=
  2 * V + 1 + (2 * V + 1 + (V * (Bc k₀ rj j₀ j₁ V + 5) + 1))
noncomputable def oPre (k₀ : K) (rj : Fin R) (j₀ j₁ V : ℕ) : ℕ := V * Bc k₀ rj j₀ j₁ V

/-- Cotas da família (I). -/
noncomputable def bI (e : Bool → Γ A.k₀) (cands : List (Γ A.k₀)) (rH rn rip rQ rm rRr t : Fin R) (V : ℕ) : ℕ :=
  ((listaI A e cands rH rn rip rQ rm rRr t).map (bfE (bPre A.k₀ t (ix (A.vals A.k₀) (some (e false)))
    (ix (A.vals A.k₀) (some (e true))) V) V)).sum + 1
noncomputable def oI (e : Bool → Γ A.k₀) (cands : List (Γ A.k₀)) (rH rn rip rQ rm rRr t : Fin R) (V : ℕ) : ℕ :=
  ((listaI A e cands rH rn rip rQ rm rRr t).map (bfE (oPre A.k₀ t (ix (A.vals A.k₀) (some (e false)))
    (ix (A.vals A.k₀) (some (e true))) V) V)).sum

theorem cota_progI (e : Bool → Γ A.k₀) (cands : List (Γ A.k₀)) {rH rn rip rQ rm rRr t : Fin R}
    (hH : rH ≠ t) (hQ : rQ ≠ t) (hR : rRr ≠ t) (V : ℕ) (hw : w.length ≤ V) :
    Cota w (progI A e cands rH rn rip rQ rm rRr t) V (bI A e cands rH rn rip rQ rm rRr t V)
      (oI A e cands rH rn rip rQ rm rRr t V) := by
  rw [progI_eq]
  refine cota_seqC_gen w V _ _ _ (fun c hc => ?_)
  rcases emis_listaI A e cands hH hQ hR c hc with rfl | h
  · rw [bfE_nao (nao_emis_progPre _ _ _ _), bfE_nao (nao_emis_progPre _ _ _ _)]
    exact cota_progPre w _ _ _ _ V hw
  · rw [bfE_emis h.1, bfE_emis h.1]
    exact cota_emisW w h V

theorem nao_emis_progI (e : Bool → Γ A.k₀) (cands : List (Γ A.k₀)) (rH rn rip rQ rm rRr t : Fin R) :
    ¬ Emis (progI A e cands rH rn rip rQ rm rRr t) := fun h =>
  nao_emis_progPre A.k₀ t (ix (A.vals A.k₀) (some (e false))) (ix (A.vals A.k₀) (some (e true)))
    (emis_seqC_mem (cs := listaI A e cands rH rn rip rQ rm rRr t) (by rw [← progI_eq]; exact h) _
      (by simp only [listaI, List.mem_cons]; tauto))

/-- A lista de comandos da emissão. -/
noncomputable def listaTab (g : Regs R) (e : Bool → Γ A.k₀) (cands : List (Γ A.k₀)) (acc : Γ A.k₁) (DD : ℕ) :
    List (Cmd R) :=
  [progE A g.rT1 g.rH g.t g.i, progI A e cands g.rH g.rn g.rip g.rQ g.rm g.rRr g.t,
    progR A g.rT g.rHb g.t g.i DD, progP A g.rT g.rH g.t g.i, progA A g.rT acc]

/-- Cotas da emissão inteira. -/
noncomputable def bTab (g : Regs R) (e : Bool → Γ A.k₀) (cands : List (Γ A.k₀)) (acc : Γ A.k₁) (DD V : ℕ) : ℕ :=
  ((listaTab A g e cands acc DD).map (bfE (bI A e cands g.rH g.rn g.rip g.rQ g.rm g.rRr g.t V) V)).sum + 1
noncomputable def oTab (g : Regs R) (e : Bool → Γ A.k₀) (cands : List (Γ A.k₀)) (acc : Γ A.k₁) (DD V : ℕ) : ℕ :=
  ((listaTab A g e cands acc DD).map (bfE (oI A e cands g.rH g.rn g.rip g.rQ g.rm g.rRr g.t V) V)).sum

/-- Distinção dos registradores usada nas cotas. -/
structure Distintos (g : Regs R) : Prop where
  t_i : g.t ≠ g.i
  T1_t : g.rT1 ≠ g.t
  T_t : g.rT ≠ g.t
  H_i : g.rH ≠ g.i
  H_t : g.rH ≠ g.t
  Hb_i : g.rHb ≠ g.i
  Q_t : g.rQ ≠ g.t
  R_t : g.rRr ≠ g.t

theorem cota_progTab (g : Regs R) (hg : Distintos g) (e : Bool → Γ A.k₀) (cands : List (Γ A.k₀))
    (acc : Γ A.k₁) (DD V : ℕ) (hw : w.length ≤ V) :
    Cota w (progTab A g e cands acc DD) V (bTab A g e cands acc DD V) (oTab A g e cands acc DD V) := by
  refine cota_seqC_gen w V _ _ _ (fun c hc => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · have h := emisW_progE A hg.T1_t hg.H_i hg.t_i
    rw [bfE_emis h.1, bfE_emis h.1]; exact cota_emisW w h V
  · rw [bfE_nao (nao_emis_progI _ _ _ _ _ _ _ _ _ _), bfE_nao (nao_emis_progI _ _ _ _ _ _ _ _ _ _)]
    exact cota_progI w A e cands hg.H_t hg.Q_t hg.R_t V hw
  · have h := emisW_progR A DD hg.T_t hg.Hb_i hg.t_i
    rw [bfE_emis h.1, bfE_emis h.1]; exact cota_emisW w h V
  · have h := emisW_progP A hg.T_t hg.H_i hg.t_i
    rw [bfE_emis h.1, bfE_emis h.1]; exact cota_emisW w h V
  · have h := emisW_progA A (W := []) (k := 0) g.rT acc
    rw [bfE_emis h.1, bfE_emis h.1]; exact cota_emisW w h V

theorem wf_progTab (g : Regs R) (hg : Distintos g) (e : Bool → Γ A.k₀) (cands : List (Γ A.k₀))
    (acc : Γ A.k₁) (DD Ad : ℕ) (hA : 2 ≤ Ad) : WF Ad (progTab A g e cands acc DD) 0 false := by
  refine wf_seqC _ _ _ _ (fun c hc => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · have h := emisW_progE A hg.T1_t hg.H_i hg.t_i
    exact wf_emis _ _ _ _ h.1 (by have := h.2.1; omega)
  · rw [progI_eq]
    refine wf_seqC _ _ _ _ (fun c hc => ?_)
    rcases emis_listaI A e cands hg.H_t hg.Q_t hg.R_t c hc with rfl | h
    · have wfc : ∀ β, WF Ad (corpoPre (R := R) A.k₀ g.t (ix (A.vals A.k₀) (some (e false)))
          (ix (A.vals A.k₀) (some (e true))) β) 0 true := by
        intro β
        have h0 := emisW_clPre (R := R) (W := []) (k := 0) A.k₀ g.t (ix (A.vals A.k₀) (some (e false)))
          (ix (A.vals A.k₀) (some (e true))) 0 β
        have h1 := emisW_clPre (R := R) (W := []) (k := 0) A.k₀ g.t (ix (A.vals A.k₀) (some (e false)))
          (ix (A.vals A.k₀) (some (e true))) 1 β
        exact ⟨wf_emis Ad true (clPre A.k₀ g.t (ix (A.vals A.k₀) (some (e false)))
            (ix (A.vals A.k₀) (some (e true))) 0 β) 0 h0.1 (by have := h0.2.1; omega),
          wf_emis Ad true (clPre A.k₀ g.t (ix (A.vals A.k₀) (some (e false)))
            (ix (A.vals A.k₀) (some (e true))) 1 β) 0 h1.1 (by have := h1.2.1; omega), trivial, trivial⟩
      exact ⟨trivial, rfl, wfc false, wfc true⟩
    · exact wf_emis _ _ _ _ h.1 (by have := h.2.1; omega)
  · have h := emisW_progR A DD hg.T_t hg.Hb_i hg.t_i
    exact wf_emis _ _ _ _ h.1 (by have := h.2.1; omega)
  · have h := emisW_progP A hg.T_t hg.H_i hg.t_i
    exact wf_emis _ _ _ _ h.1 (by have := h.2.1; omega)
  · have h := emisW_progA A (W := []) (k := 0) g.rT acc
    exact wf_emis _ _ _ _ h.1 (by have := h.2.1; omega)

end cotasFam

/-! ## Cotas polinomiais das cotas -/

section poli

theorem poli_sum_list {α : Type*} (f : α → ℕ → ℕ) : ∀ l : List α, (∀ a ∈ l, Poli (f a)) →
    Poli fun n => (l.map fun a => f a n).sum
  | [], _ => by simpa using poli_const 0
  | a :: l, h => by
    simpa using poli_add (h a (List.mem_cons_self ..)) (poli_sum_list f l (fun b hb => h b (List.mem_cons_of_mem _ hb)))

variable {V : ℕ → ℕ} (hV : Poli V)
include hV

theorem poli_Cst (c : Cmd R) : Poli fun n => Cst c (V n) :=
  poli_mul (poli_const _) (poli_pow (poli_add hV (poli_const 1)) _)

theorem poli_bfE {pre : ℕ → ℕ} (hpre : Poli pre) (c : Cmd R) : Poli fun n => bfE (pre n) (V n) c := by
  by_cases h : Emis c
  · simpa [bfE_emis h] using poli_Cst hV c
  · simpa [bfE_nao h] using hpre

theorem poli_Bc {K : Type} [Fintype K] (k₀ : K) (rj : Fin R) (j₀ j₁ : ℕ) :
    Poli fun n => Bc k₀ rj j₀ j₁ (V n) := by
  unfold Bc
  exact poli_add (poli_add (poli_Cst hV _) (poli_Cst hV _)) (poli_add (poli_Cst hV _) (poli_Cst hV _))

variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} {Λ σ : Type} (A : Tab K Γ Λ σ)

omit [DecidableEq K] in
theorem poli_bPre (k₀ : K) (rj : Fin R) (j₀ j₁ : ℕ) : Poli fun n => bPre k₀ rj j₀ j₁ (V n) := by
  unfold bPre
  exact poli_add (poli_add (poli_mul (poli_const 2) hV) (poli_const 1)) (poli_add (poli_add
    (poli_mul (poli_const 2) hV) (poli_const 1)) (poli_add (poli_mul hV (poli_add (poli_Bc hV _ _ _ _)
    (poli_const 5))) (poli_const 1)))

omit [DecidableEq K] in
theorem poli_oPre (k₀ : K) (rj : Fin R) (j₀ j₁ : ℕ) : Poli fun n => oPre k₀ rj j₀ j₁ (V n) :=
  poli_mul hV (poli_Bc hV _ _ _ _)

theorem poli_bI (e : Bool → Γ A.k₀) (cands : List (Γ A.k₀)) (rH rn rip rQ rm rRr t : Fin R) :
    Poli fun n => bI A e cands rH rn rip rQ rm rRr t (V n) := by
  unfold bI
  exact poli_add (poli_sum_list _ _ (fun c _ => poli_bfE hV (poli_bPre hV _ _ _ _) c)) (poli_const 1)

theorem poli_oI (e : Bool → Γ A.k₀) (cands : List (Γ A.k₀)) (rH rn rip rQ rm rRr t : Fin R) :
    Poli fun n => oI A e cands rH rn rip rQ rm rRr t (V n) := by
  unfold oI
  exact poli_sum_list _ _ (fun c _ => poli_bfE hV (poli_oPre hV _ _ _ _) c)

theorem poli_bTab (g : Regs R) (e : Bool → Γ A.k₀) (cands : List (Γ A.k₀)) (acc : Γ A.k₁) (DD : ℕ) :
    Poli fun n => bTab A g e cands acc DD (V n) := by
  unfold bTab
  exact poli_add (poli_sum_list _ _ (fun c _ => poli_bfE hV (poli_bI hV A _ _ _ _ _ _ _ _ _) c)) (poli_const 1)

theorem poli_oTab (g : Regs R) (e : Bool → Γ A.k₀) (cands : List (Γ A.k₀)) (acc : Γ A.k₁) (DD : ℕ) :
    Poli fun n => oTab A g e cands acc DD (V n) := by
  unfold oTab
  exact poli_sum_list _ _ (fun c _ => poli_bfE hV (poli_oI hV A _ _ _ _ _ _ _ _ _) c)

end poli

/-! ## O gerador da redução -/

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

section gerador

variable {L : Linguagem} (D : DadosNP L)

/-- Número de contadores (menos 2): basta cobrir os graus de `q` e do tempo da máquina. -/
noncomputable def LL : ℕ := max D.q.natDegree D.M.time.natDegree

/-- O tableau da máquina verificadora. -/
noncomputable abbrev tabD := tabTM D.M.tm D.M.inputAlphabet D.M.outputAlphabet

/-- Registradores da fase de emissão. -/
def regs (L : ℕ) : Regs (RA L) := ⟨rT L, rT1 L, rH L, rHb L, rn L, rip L, rQ L, rm L, rRr L, rt L, ri L⟩

/-- **O gerador**: fase aritmética seguida da emissão do tableau. -/
noncomputable def gerador : Cmd (RA (LL D)) :=
  .seq (arit (LL D) D.q D.M.time (empTM D.M.tm) (tabD D).d)
    (progTab (tabD D) (regs (LL D)) D.M.inputAlphabet.invFun (candsD D) (accD D) (empTM D.M.tm))

/-- Tempo do tableau. -/
noncomputable def Tf (n : ℕ) : ℕ := D.M.time.eval (2 * n + 2 + D.q.eval n)

/-- Altura do tableau. -/
noncomputable def Hf (n : ℕ) : ℕ :=
  2 * n + 2 + D.q.eval n + (empTM D.M.tm * Tf D n + (1 + (tabD D).d + empTM D.M.tm))

theorem aritD (w : List Bool) :
    ∃ Ef : Env (RA (LL D)), Passo w (arit (LL D) D.q D.M.time (empTM D.M.tm) (tabD D).d) (fun _ => 0) Ef
        (custoA (LL D) D.q D.M.time (empTM D.M.tm) (tabD D).d w.length) ∧
      Vals (regs (LL D)) Ef w.length (D.q.eval w.length) (Tf D w.length)
        (2 * w.length + 2 + D.q.eval w.length + empTM D.M.tm * Tf D w.length + 1)
        (empTM D.M.tm * Tf D w.length + (1 + (tabD D).d + empTM D.M.tm)) (Hf D w.length) ∧
      (∀ c ∈ ctrs (LL D), Ef c = 0) := by
  obtain ⟨Ef, hP, e1, e2, e3, e4, e5, e6, e7, e8, e9, ec⟩ := arit_spec w (LL D) D.q D.M.time (empTM D.M.tm)
    (tabD D).d (by unfold LL; omega) (by unfold LL; omega)
  exact ⟨Ef, hP, ⟨e5, e6, e9, e7, e1, e3, e2, e4, e8⟩, ec⟩

theorem saida_gerador (w : List Bool) :
    (sem w (gerador D) (fun _ => 0)).2 = reducao D (Tf D) (Hf D) w := by
  obtain ⟨Ef, ⟨hs, -⟩, hv, -⟩ := aritD D w
  have hg := geraU_progTab w (tabD D) (regs (LL D)) D.M.inputAlphabet.invFun (candsD D) (accD D)
    (DD := empTM D.M.tm) hv (by simp [regs, Regs.params, Fin.ext_iff]) (by simp [regs, Regs.params, Fin.ext_iff])
    (by simp [regs, Fin.ext_iff]) (by unfold Hf; omega) (by unfold Hf; omega) (by omega)
    (fun l => Finset.le_sup (f := fun l => emp (D.M.tm.m l)) (Finset.mem_univ l))
  obtain ⟨ho, -⟩ := hg Ef (fun _ _ => rfl)
  simp only [gerador, sem, hs, List.nil_append]
  rw [ho, reducao, codCNF_renomeia_cc, formulaD, preD]

theorem distintos_regs (L : ℕ) : Distintos (regs L) := by
  constructor <;> simp [regs, Fin.ext_iff]

theorem wf_gerador : WF (LL D + 2) (gerador D) 0 false :=
  ⟨wf_arit _ _ _ _ _, wf_progTab _ _ (distintos_regs _) _ _ _ _ _ (by omega)⟩

/-- Cota dos valores dos registradores depois da fase aritmética. -/
noncomputable def Vf (n : ℕ) : ℕ := Hf D n + Tf D n + 1

theorem limitado (w : List Bool) (Ef : Env (RA (LL D)))
    (hv : Vals (regs (LL D)) Ef w.length (D.q.eval w.length) (Tf D w.length)
        (2 * w.length + 2 + D.q.eval w.length + empTM D.M.tm * Tf D w.length + 1)
        (empTM D.M.tm * Tf D w.length + (1 + (tabD D).d + empTM D.M.tm)) (Hf D w.length))
    (hz : ∀ c ∈ ctrs (LL D), Ef c = 0) : ∀ r, Ef r ≤ Vf D w.length := by
  intro r
  obtain ⟨k, hk⟩ := r
  unfold Vf Hf
  by_cases h9 : k < 9
  · interval_cases k
    · change Ef (regs (LL D)).rn ≤ _; rw [hv.en]; try unfold Hf
      omega
    · change Ef (regs (LL D)).rQ ≤ _; rw [hv.eQ]; try unfold Hf
      omega
    · change Ef (regs (LL D)).rip ≤ _; rw [hv.eip]; try unfold Hf
      omega
    · change Ef (regs (LL D)).rm ≤ _; rw [hv.em]; try unfold Hf
      omega
    · change Ef (regs (LL D)).rT ≤ _; rw [hv.eT]; try unfold Hf
      omega
    · change Ef (regs (LL D)).rT1 ≤ _; rw [hv.eT1]; try unfold Hf
      omega
    · change Ef (regs (LL D)).rHb ≤ _; rw [hv.eHb]; try unfold Hf
      omega
    · change Ef (regs (LL D)).rRr ≤ _; rw [hv.eR]; try unfold Hf
      omega
    · change Ef (regs (LL D)).rH ≤ _; rw [hv.eH]; try unfold Hf
      omega
  · have hm : (⟨k, hk⟩ : Fin (RA (LL D))) ∈ ctrs (LL D) :=
      List.mem_map.mpr ⟨⟨k - 9, by unfold RA at hk; omega⟩, List.mem_finRange _, Fin.ext (by simp; omega)⟩
    rw [hz _ hm]; exact Nat.zero_le _

/-- A cota polinomial do custo total da máquina. -/
noncomputable def custoTotal (n : ℕ) : ℕ :=
  (2 * n + 1) + (RA (LL D) * (2 * Vf D n + 1) + 1) +
    (2 * oTab (tabD D) (regs (LL D)) D.M.inputAlphabet.invFun (candsD D) (accD D) (empTM D.M.tm) (Vf D n) + 1) +
    (bTab (tabD D) (regs (LL D)) D.M.inputAlphabet.invFun (candsD D) (accD D) (empTM D.M.tm) (Vf D n) +
      custoA (LL D) D.q D.M.time (empTM D.M.tm) (tabD D).d n) + 1

theorem custo_gerador (w : List Bool) :
    custoLimpa w (sem w (gerador D) (fun _ => 0)).1 (sem w (gerador D) (fun _ => 0)).2 +
      custo w (gerador D) (fun _ => 0) + 1 ≤ custoTotal D w.length := by
  obtain ⟨Ef, ⟨hs, hc⟩, hv, hz⟩ := aritD D w
  have hb := limitado D w Ef hv hz
  have hw : w.length ≤ Vf D w.length := by unfold Vf Hf; omega
  obtain ⟨c1, o1, r1⟩ := cota_progTab w (tabD D) (regs (LL D)) (distintos_regs _) D.M.inputAlphabet.invFun
    (candsD D) (accD D) (empTM D.M.tm) (Vf D w.length) hw Ef hb
  have e1 : (sem w (gerador D) (fun _ => 0)).1 = (sem w (progTab (tabD D) (regs (LL D))
      D.M.inputAlphabet.invFun (candsD D) (accD D) (empTM D.M.tm)) Ef).1 := by
    simp [gerador, sem, hs]
  have e1' : (sem w (gerador D) (fun _ => 0)).2 = (sem w (progTab (tabD D) (regs (LL D))
      D.M.inputAlphabet.invFun (candsD D) (accD D) (empTM D.M.tm)) Ef).2 := by
    simp [gerador, sem, hs]
  have e2 : custo w (gerador D) (fun _ => 0) = custo w (progTab (tabD D) (regs (LL D)) D.M.inputAlphabet.invFun
      (candsD D) (accD D) (empTM D.M.tm)) Ef + custo w (arit (LL D) D.q D.M.time (empTM D.M.tm) (tabD D).d)
        (fun _ => 0) := by
    simp [gerador, custo, hs]
  rw [e1, e1', e2]
  have hsum : ((List.finRange (RA (LL D))).map fun r =>
      2 * (sem w (progTab (tabD D) (regs (LL D)) D.M.inputAlphabet.invFun (candsD D) (accD D)
        (empTM D.M.tm)) Ef).1 r + 1).sum ≤ RA (LL D) * (2 * Vf D w.length + 1) := by
    have := List.sum_le_length_nsmul (((List.finRange (RA (LL D))).map fun r =>
      2 * (sem w (progTab (tabD D) (regs (LL D)) D.M.inputAlphabet.invFun (candsD D) (accD D)
        (empTM D.M.tm)) Ef).1 r + 1)) (2 * Vf D w.length + 1) (by
      intro a ha
      obtain ⟨r, -, rfl⟩ := List.mem_map.mp ha
      have := r1 r
      omega)
    simpa using this
  unfold custoLimpa custoTotal
  omega

theorem poli_Vf : Poli (Vf D) := by
  have hQ : Poli fun n => D.q.eval n := poli_eval _
  have hm : Poli fun n => 2 * n + 2 + D.q.eval n :=
    poli_add (poli_add (poli_mul (poli_const 2) poli_id) (poli_const 2)) hQ
  have hT : Poli (Tf D) := poli_eval_comp _ hm
  have hH : Poli (Hf D) := poli_add hm (poli_add (poli_mul (poli_const _) hT) (poli_const _))
  exact poli_add (poli_add hH hT) (poli_const 1)

theorem poli_custoTotal : Poli (custoTotal D) := by
  have hV := poli_Vf D
  unfold custoTotal
  exact poli_add (poli_add (poli_add (poli_add (poli_add (poli_mul (poli_const 2) poli_id) (poli_const 1))
    (poli_add (poli_mul (poli_const _) (poli_add (poli_mul (poli_const 2) hV) (poli_const 1))) (poli_const 1)))
    (poli_add (poli_mul (poli_const 2) (poli_oTab hV _ _ _ _ _ _)) (poli_const 1)))
    (poli_add (poli_bTab hV _ _ _ _ _ _) (poli_custoA _ _ _ _ _))) (poli_const 1)

/-- **A máquina da redução**: o gerador compilado, em tempo polinomial. -/
noncomputable def maqRed :
    TM2ComputableInPolyTime cod cod (fun w => (sem w (gerador D) (fun _ => 0)).2) :=
  computavel (A := LL D + 2) (gerador D) (wf_gerador D) (Classical.choose (poli_custoTotal D))
    (fun w => (custo_gerador D w).trans (Classical.choose_spec (poli_custoTotal D) w.length))

end gerador

/-! ## Cook–Levin -/

/-- **Toda linguagem de NP se reduz a SAT** (redução de Karp em tempo polinomial). -/
theorem red_SAT {L : Linguagem} (hL : L ∈ classeNP) : Red L SAT := by
  let D := dadosNP hL
  refine ⟨fun w => (sem w (gerador D) (fun _ => 0)).2, fun w => ?_, ⟨maqRed D⟩⟩
  dsimp only
  rw [saida_gerador]
  exact reducao_iff D (Tf D) (Hf D) (fun n => le_rfl) (fun n => by unfold Hf tabD; omega) w

/-- **Teorema de Cook–Levin** no modelo genuíno: SAT ∈ NP e toda L ∈ NP se reduz a SAT. -/
theorem cookLevin : ClayPvsNPProof.ATK.Conditional.PvsNP.CookLevin modeloPNP SAT :=
  cookLevin_iff.mpr fun _ hL => red_SAT hL

end ClayPvsNPProof.ATK.CookLevinNP

