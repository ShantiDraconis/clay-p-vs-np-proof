# P vs NP — prova (Lean 4 / Mathlib)

Depende do enunciado em [`ShantiDraconis/clay-p-vs-np-statement`](https://github.com/ShantiDraconis/clay-p-vs-np-statement),
fixado no commit `6375290`. O alvo é `ClayPvsNP.P_eq_NP`, sem redefinição.

`P_eq_NP` é uma proposição a DECIDIR: a prova é `theorem main : ClayPvsNP.P_eq_NP` ou `theorem main : ¬ ClayPvsNP.P_eq_NP`.

Estado: sem prova. `OPEN_MATH = true`.

Regras: nenhum `sorry`, `axiom`, `native_decide` ou marcador; `#print axioms ClayPvsNPProof.main` fixado
com `#guard_msgs` quando `main` existir.

Prêmio: a formalização é material suplementar. O Clay e a AMS só consideram soluções publicadas
em periódico referado; o Clay espera ainda dois anos e aceitação geral.

## O que está provado (e o que não está)

Nada abaixo prova `P = NP` nem `P ≠ NP`. São teoremas sobre as classes FIXADAS `ClayPvsNP.P`,
`ClayPvsNP.NP` (máquinas `Turing.FinTM2` da Mathlib em tempo polinomial) que reduzem o problema a
uma única lacuna, `Gap : Prop := SAT ∉ ClayPvsNP.P`, e uma equivalência provada `¬ P_eq_NP ↔ Gap`.
`Gap` continua em aberto: é o próprio problema reescrito, não um passo a mais.

Axiomas: todas as declarações novas (902, incluindo as portadas) dependem só de `propext`,
`Classical.choice`, `Quot.sound` (ou de um subconjunto). Cada uma tem um
`#guard_msgs in #print axioms` com a saída real em [`ClayPvsNPProof/Audit.lean`](ClayPvsNPProof/Audit.lean).
`Classical.choice` já aparece no próprio enunciado fixado (`#print axioms ClayPvsNP.P_eq_NP`).

### 1. `P` fixado = `classeP` do ATK — [`ClayPvsNPProof/ClassP.lean`](ClayPvsNPProof/ClassP.lean)

* `P_eq_classeP : ClayPvsNP.P = ATK.LigacaoPNP.classeP`
* `inP_iff_emP (L) : ClayPvsNP.InP L ↔ ATK.LigacaoPNP.EmP L`
* `polyTimeComputable_iff (f) : ClayPvsNP.PolyTimeComputable f ↔ Nonempty (TM2ComputableInPolyTime cod encodeBool f)`

Classificação: teorema (equivalência de definições; as duas são a mesma, com conjunções trocadas).
NÃO é: nenhum resultado sobre P vs NP. Origem: `ATK/LigacaoPNP.lean` (definições `EmP`, `classeP`).
Axiomas: `[propext, Classical.choice, Quot.sound]`.

### 2. Transcodificadores de pares — [`ClayPvsNPProof/Transcoders.lean`](ClayPvsNPProof/Transcoders.lean)

O enunciado fixado codifica `⟨w, c⟩` como `(w.flatMap fun b => [true, b]) ++ false :: c`; o ATK,
como `(w.flatMap fun b => [b, b]) ++ [false, true] ++ c`. Duas máquinas `FinTM2` de duas pilhas,
construídas e verificadas passo a passo, de tempo linear (`2n + 4`):

* `tAComputable : TM2ComputableInPolyTime cod cod tA` com `tA_pair : tA (ClayPvsNP.pair w c) = par w c`
* `tPComputable : TM2ComputableInPolyTime cod cod tP` com `tP_par : tP (par w c) = ClayPvsNP.pair w c`

Classificação: teoremas / construções. NÃO é: nada sobre P vs NP; é engenharia de máquinas.
Origem: código NOVO deste repositório (o kernel ATK não tinha transcodificador para esta
codificação), no estilo de `ATK/ModeloPNP.lean` (`decTM`) e `ATK/TranscodificadoresFC.lean`.
Axiomas: `[propext, Classical.choice, Quot.sound]` ou subconjunto.

### 3. `NP` fixado = `classeNP` do ATK e `P ⊆ NP` — [`ClayPvsNPProof/ClassNP.lean`](ClayPvsNPProof/ClassNP.lean)

* `NP_eq_classeNP : ClayPvsNP.NP = ATK.LigacaoPNP.classeNP`
* `P_subset_NP : ClayPvsNP.P ⊆ ClayPvsNP.NP`
* `P_eq_NP_iff_classes : ClayPvsNP.P_eq_NP ↔ classeP = classeNP`
* `not_P_eq_NP_iff_PneNP : ¬ ClayPvsNP.P_eq_NP ↔ ATK.LigacaoPNP.PneNP`
* `P_eq_NP_iff_NP_subset_P : ClayPvsNP.P_eq_NP ↔ ClayPvsNP.NP ⊆ ClayPvsNP.P`

Prova: os verificadores são compostos com os transcodificadores (composição de máquinas
`ATK.ComposicaoTM2.comp`, P fechada por reduções de Karp `ATK.ModeloPNP.P_fechada_red`);
`P ⊆ NP` é `ATK.ModeloPNP.P_sub_NP` (decodificador `decTM` + decisor, certificado vazio)
transportado pelas duas igualdades. Classificação: teoremas. NÃO é: nenhuma das duas inclusões
difíceis. Origem: `ATK/ModeloPNP.lean`, `ATK/ComposicaoTM2.lean`. Axiomas:
`[propext, Classical.choice, Quot.sound]`.

### 4. SAT, Cook–Levin e a lacuna — [`ClayPvsNPProof/SAT.lean`](ClayPvsNPProof/SAT.lean)

`SAT : ClayPvsNP.Language` = codificações binárias `codCNF φ` das CNF satisfatíveis (codificação do
ATK: `0 ↦ 00`, `1 ↦ 01`, fim de literal `↦ 10`, fim de cláusula `↦ 11`; índices em `Nat.bits`).
Sanidade: `nil_mem_SAT`, `x0_mem_SAT`, `true_true_not_mem_SAT`.

* `SAT_mem_NP : SAT ∈ ClayPvsNP.NP`
* `SAT_NP_hard : ∀ L ∈ ClayPvsNP.NP, KarpRed L SAT` (Cook 1971, Levin 1973)
* `P_closed_KarpRed : KarpRed A B → B ∈ ClayPvsNP.P → A ∈ ClayPvsNP.P`
* `P_eq_NP_iff_SAT_mem_P : ClayPvsNP.P_eq_NP ↔ SAT ∈ ClayPvsNP.P`
* **`def Gap : Prop := SAT ∉ ClayPvsNP.P`** e **`not_P_eq_NP_iff_Gap : ¬ ClayPvsNP.P_eq_NP ↔ Gap`**
* `Target_iff_not_Gap : Target ↔ ¬ Gap`

`KarpRed A B` = existe `f : Word → Word` com `w ∈ A ↔ f w ∈ B` computada por `FinTM2` em tempo
polinomial (`TM2ComputableInPolyTime id id f`).

Classificação: teoremas + equivalência com lacuna nomeada (`Gap`). NÃO é: prova nem refutação de
`Gap`; `Gap` é exatamente P ≠ NP. Origem: `ATK/SATemNP.lean` (`sat_em_NP`),
`ATK/CookLevinNP.lean` (`red_SAT`), `ATK/ZeroClasses/Pontes.lean` (`p_eq_np_iff_sat`, reprovado
aqui sobre as classes fixadas). Axiomas: `[propext, Classical.choice, Quot.sound]`
(`SAT` e os testes de sanidade: `[propext, Quot.sound]`).

### Arquivos portados do kernel ATK — [`ClayPvsNPProof/ATK/`](ClayPvsNPProof/ATK/)

Origem: kernel ATK, espelho público `ShantiDraconis/atk-math-core-public` @ `ffc111a`
(= `ShantiDraconis/M-Core` @ `390e378`), pasta `imports/M-Core/atk-kernel/ATK/`, escrito para
Lean 4.34.1 / Mathlib v4.34.1 e recompilado aqui em Lean 4.36.0-rc2 / Mathlib `8fe7ce4`.
Cada arquivo traz no topo o caminho de origem, o sha256 do original e as alterações.

| arquivo | conteúdo |
|---|---|
| `Conditional/PvsNP` | interface `ComplexityModel` (só para `modeloPNP`) |
| `LigacaoPNP` | `EmP`, `EmNP`, `par`, `classeP`, `classeNP`, `PneNP` |
| `ComposicaoTM2` | composição de `FinTM2` em tempo polinomial (`comp`) |
| `ModeloPNP` | `decTM`, `P_sub_NP`, `Red`, `P_fechada_red`, `SAT`, `codCNF` |
| `SATemNP` | verificador de SAT como `FinTM2` (`sat_em_NP`) |
| `CookLevinBase`, `Fragmentos`, `Compilador` | compilador verificado de laços para `FinTM2` |
| `CookLevinLacos`, `CookLevinTableau`, `CookLevinReducao`, `CookLevinGerador`, `CookLevinNP` | redução de Cook–Levin (`red_SAT`) |

Alterações: namespace `ATK.*` → `ClayPvsNPProof.ATK.*`; linhas `#print axioms` removidas (auditoria
em `Audit.lean`); três imports explícitos de Mathlib (`Mathlib.Tactic.{Linarith,IntervalCases,Tauto}`,
`Mathlib.Algebra.Polynomial.Eval.Degree`) que antes vinham transitivamente; binder `{α : Type*}`
explícito em dois lemas (`autoImplicit = false`); removido `ModeloPNP.fielL2` (dependia de
`ATK.Termos`, fora do escopo). Nenhuma prova foi alterada.

### Não portado

* `ATK/IntegracaoFCPNP.lean`, `ATK/TranscodificadoresFC.lean` (equivalência com o enunciado do
  formal-conjectures): não é necessário para o enunciado fixado.
* O resto de `ATK/ZeroClasses/Pontes.lean` (ordem de anulação, `ZERO_ORDER`): depende de
  `ATK.ZeroClasses.Forcar` e de uma cadeia grande de análise; não acrescenta nada ao alvo.
