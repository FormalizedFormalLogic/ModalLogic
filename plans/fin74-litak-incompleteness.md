# Fin74/Litak: Fine logic の不完全性の形式化プラン（[Lit04] Theorem 2.4 準拠）

作成: 2026-07-21．立案: Fable（メインループ）．

## 背景

- [Fin74] の印刷版の式定義には誤りがあり，Lemma 2 stage (2) は成立しない
  （機械検証済み反例，`Fin74/Lemma2/NotValidatesG.lean`，`plans/fin74-lemma2-not-validates-g.md`）．
- [Lit04]（Litak, "Modal Incompleteness Revisited", Studia Logica 76, 2004）§2 は
  「Fine logic」を**修正された式**で提示する（p.332）．この修正は本プロジェクトが独立に導出した
  修理案と完全に一致する：
  - `γ_{m+2} := ◇γ_{m+1} ⋏ ◇β_m ⋏ ∼◇β_{m+1}`（[Fin74] 印刷版の `∼◇B_{m+2}` を `∼◇β_{m+1}` に．
    これで γ は β の完全な鏡像になる）
  - `α_m := ◇β_{m+1} ⋏ ◇γ_{m+1} ⋏ ∼◇β_{m+2} ⋏ ∼◇γ_{m+2}`（第4連言肢を追加）
  - `ι₁ := □(p₀ → ∼p₁ ⋏ ◇p₁) ⋏ □(p₁ → ∼p₀ ⋏ ◇p₀)`（[Fin74] 印刷版の D に欠けていた
    `p₁ →` 方向を追加）
- [Lit04] Theorem 2.4:「Fine logic は completely incomplete」＝ Σ₁ = S4+γ+χ を妥当化する
  **任意の complete (general) frame** は φ₁ を妥当化するが，φ₁ ∉ L（Fine frame 上の
  **一般フレーム**が Σ₁ と φ₁ を分離する）．Kripke 不完全性はその系（Kripke frame は complete）．
- **[Lit04] の誤植**: p.332 の `φ₁ := ∼(δ ⋏ α₀ ⋏ κ)` は `∼(δ ⋏ ◇α₀ ⋏ κ)` の誤り
  （◇ なしでは δ の強制する d 点で α₀ が成立できず分離が壊れ，Lemma 2.3 のポンピングも
  通らない．[Fin74] の E = D ⋏ ◇A₀ ⋏ K，および Thm 2.4 証明中の
  `E_n := V(∼φ₁ⁿ ⋏ ∼◇α_{n−1})` と整合するのは ◇ あり）．本形式化は ◇ ありを採用する．
- [Lit04] Lemma 2.2（κⁿ → κᵐ の S4 導出可能性，n ≤ m）は Gerson [Ge75a] に帰属．
  Fine の (3) にあった K 添字のギャップを埋める補題．
- [Lit04] は「Σ₁ ⊬ φ₁ の証明（一般フレームが γ を妥当化すること）は Fine の論文にある」と
  述べて委ねるが，Fine のその証明（stage 2）は壊れている．**修正された式＋一般フレームの
  制限付き付値のもとで，この妥当性を初めて厳密に証明することが本形式化の核心**（Phase 2）．

## 記法対応表（[Lit04] ↔ 本形式化 `Fin74.Litak` 名前空間）

| [Lit04] | Lean | 備考 |
|---|---|---|
| β_m, γ_m | `B m`, `C m` | 対称な相互再帰 |
| α_m | `A m` | 4連言肢 |
| ι₁ ⋏ ι₂ と p₀⋎p₁ | `D` | Fine の D の修正版（ι₁ 両方向） |
| κ = ι₃ ⋏ ι₄ | `K` | [Fin74] の K と同一（原子 q₀,q₁,r₀,r₁ のみ使用） |
| ∼φ₁ | `E` = `D ⋏ ◇(A 0) ⋏ K` | ◇ は誤植訂正 |
| ψ | `F` = `◇((p₀⋎p₁) ⋏ ∼◇(A 0) ⋏ ◇(A 1))` | |
| γ | `G` = `E 🡒 F` | |
| χ | = `Fin74.H`（不変） | |
| Σ₁ | `mkLogic {G, H}` | Fine logic L |
| αᵐ（shift代入）| `⟦shift m⟧` | q_i ↦ B (m+i), r_i ↦ C (m+i) |

## 数学的な全体構造（検証済みの証明スケッチ）

### (I) Kripke（および complete general）frame 側: Σ₁ ⊨ ∼E

任意の complete general S4 frame 𝔉 = (W,R,P)（P が任意の族の上限を持つ）で
𝔉 ⊨ G, 𝔉 ⊨ H とし，ある admissible 付値 V と点 x で x ⊩ E とすると矛盾：

1. **κ 単調性**（[Lit04] Lemma 2.2 の意味論版）: 任意の（反射推移）モデルで
   `x ⊩ K⟦shift n⟧ → x ⊩ K⟦shift (n+1)⟧`．各連言肢は K^n の box 事実＋推移性から
   ポイントワイズに出る（β_{m+2} → ◇β_{m+1} ⋏ ∼◇γ_{m+1} は命題論理的に真，
   β_{m+1} ⋏ ◇β_{m+2} は ◇◇γ_m → ◇γ_m 等で矛盾）．S4 導出は不要（意味論で閉じる）．
2. **ポンピング**（[Lit04] Lemma 2.3 精密化）: `E_0 := value(E)`，
   `E_{n+1} := value(E⟦shift (n+1)⟧ ⋏ ∼◇(A n))` とおくと `E_n ⊆ ◇E_{n+1}`．
   証明: x ∈ E_n → G のshift instance（admissible 付値の閉性より 𝔉 ⊨ G から従う）で
   x ⊩ F⟦shift n⟧ → 証人 y ⊩ (p₀⋎p₁) ⋏ ∼◇A_n ⋏ ◇A_{n+1}．y ⊩ E^{n+1}:
   δ = (p₀⋎p₁) ⋏（boxed ι₁,ι₂ は x から遺伝）✓，◇A_{n+1} ✓，K^{n+1} は
   x の K^n が boxed 遺伝＋κ単調性 ✓．
3. **非空・互いに素**: E_0 ∋ x で各 E_n ≠ ∅（2 の反復）．E_n の点は ◇A_k（∀k≥n）を満たす
   （2 の反復と ◇◇=◇）一方 E_m（m>n）の点は ∼◇A_{m−1} を満たし m−1 ≥ n なので互いに素．
4. **上限で3相付値**: B(s) := ⋁_P E_{3n}，B(t) := ⋁_P E_{3n+1}（complete 性で存在，
   admissible）．集合束の補題（[Lit04] Lemma 1.2）:
   - 完備ブール代数の無限分配則（補元で初等的に証明可）から，和が互いに素 → 上限も互いに素．
   - ◇ の単調性から ⋁◇C_n ⊆ ◇⋁C_n．E_k ⊆ ◇E_{k'}（k<k'，◇連鎖）と cofinality により
     `⋁E_{3n+i} ⊆ ◇⋁E_{3n+j}`（任意の i,j ∈ {0,1,2}）．
5. **χ = H の反駁**: x ∈ E_0 ⊆ B(s) で x ⊩ s ⋏ □(s → ◇(∼s⋏t⋏◇((∼s⋏∼t)⋏◇s)))：
   s 点 z ∈ B(s) ⊆ ◇B(t)，その先 y ⊩ ∼s⋏t（上限の互いに素），さらに ⋁E_{3n+2} の点
   v ⊩ ∼s⋏∼t，v ⊩ ◇B(s) = ◇s．よって x ⊮ H で 𝔉 ⊨ H に矛盾．□
   （Kripke frame は P = powerset・⋁ = ⋃ の complete frame なので Kripke 版は特殊化で従う．
   旧 Lemma 1 の鳩の巣論法は不要になる．）

### (II) 一般フレーム側: φ₁ = ∼E ∉ L

Fine frame（`Fin74.Lemma2.Model` の W, R —— 変更なし）上の一般フレーム 𝔉 = (W,R,P)：

- **P の閉形式**: W を3領域 R' := {b,c,a 点}，De := {d 偶数}，Do := {d 奇数} に分割し，
  `X ∈ P :↔ X∩R' が R' 内で有限または補有限 ∧ X∩De が De 内で有限または補有限 ∧
  X∩Do が Do 内で有限または補有限`．
  （[Lit04] p.333「有限集合・補有限集合・d偶数集合・d奇数集合で生成」の生成結果．）
- **閉性**: 補集合 ✓，∩ ✓，◇（前像）: pred(b_k)・pred(c_k) は補有限，pred(a_k)・pred(d_k) は
  有限，X∩(b∪c) が無限なら ◇X 補有限，X∩D が無限なら ◇X ⊇ D，等の場合分けで ◇X ∈ P．
- **一般フレームの論理**: admissible 付値（全原子の値 ∈ P）に対する妥当性 GFValid．
  帰納法で `value_mem : {x | x ⊩ φ} ∈ P`．mkLogic の帰納で
  `mkLogic {G,H} A → GFValid 𝔉 A`（S4公理は反射推移フレームで妥当，MP/Nec 保存，
  **Subst は value_mem による付値の書き換えで保存** —— 一般フレームの要点）．
- **𝔉 ⊨ H**（GF妥当性）: H の反駁は s/t/∼s∼t の3相を無限に繰り返す上昇鎖を生む
  （既存の `StronglyVerifiesH.lean` の `exists_phase_chain`・`ChainConfinement` を再利用）．
  鎖は d 点に閉じ込められ，3相それぞれが D 内で無限に再来する．しかし P の D 上の自由度は
  De/Do の2つのみ：3つの互いに素な集合が各々 D 内で無限 → 各々 De か Do の中で補有限 →
  鳩の巣で2つが同じ De/Do 内で補有限 → 交わり非空で矛盾．
  （旧 mod-2 鳩の巣補題 `exists_same_parity_*` がそのまま使える．）
- **𝔉 ⊨ G**（GF妥当性）: **Phase 2 の核心・最難関**．[Lit04] は Fine の壊れた証明に委ねている
  ため，ここは新規の数学．方針: x ⊩ E → 修正済み ι₁（両方向）から p₀/p₁ 交代の無限上昇鎖 →
  `ChainConfinement` で x = d_m を強制（これは修正により任意付値で成立するようになった）→
  `exists_V_shape`（形式化済み，任意付値対応）で V字 → **admissible 制約（各原子値が領域ごと
  有限/補有限）＋K-block の box 制約で B_i/C_i 値集合の位置を分類** → 修正された式では
  c_{n+3}型・a_n型の模倣点が消えるので [A₀-instance] が錐内で低い a/d 領域に閉じ込められ，
  F の証人 d_{大} が取れる（または当該分岐で E が矛盾）．
  この分類はケースが多いため，Phase 2 で専用の Fable プランニングを行ってから実装する．
- **E の充足**: 標準付値 φ（q_i ↦ {b_i}（有限 ✓），r_i ↦ {c_i} ✓，p₀ ↦ De ✓，p₁ ↦ Do ✓）は
  admissible．d₀ ⊩ E：D の追加方向 □(p₁→∼p₀⋏◇p₀) も d 奇数 → d 偶数の遷移で成立，
  ◇A₀ の証人 a₀（第4連言肢 ∼◇C₂ は cone(a₀) 内に C₂ 点が無いことから），K は既存
  `forces_K0_at_d0` と同形．
- 以上より ∼E ∉ mkLogic {G, H}．

### (III) 結論

`theorem fine_logic_kripke_incomplete`：
`(∀ frame F, F ⊧ G → F ⊧ H → F ⊧ ∼E) ∧ ¬ mkLogic {G, H} (∼E)`．
（complete general frame 版 (I) を形式化すれば completely incomplete も従う．
Kripke 版を最小目標，complete 版を努力目標とする．）

## モジュール構成と実装ステップ

新規ディレクトリ `Fin74/Litak/`，名前空間 `Fin74.Litak`．
既存の `Fin74/Lemma2/Model.lean`（W・R・frame）はそのまま import して使う．

### Phase 1（インフラ，並列実装）

- **Step L1**（worktree `fin74-lt-formula`）: `Fin74/Litak/Formula.lean` —
  `B`/`C`（対称相互再帰）・`A`・`D`・`K1..K4`/`K`・`E`/`F`/`G` の定義＋展開補題（simp/grind），
  `Fin74/Litak/Shift.lean` — shift 代入と `B_subst_shift` 等（既存 `Fin74/Logic/Shift.lean` の写し），
  `E⟦shift m⟧ = D ⋏ ◇A m ⋏ K⟦shift m⟧` 型の補題．χ は `Fin74.H` を再利用．
- **Step L2**（worktree `fin74-lt-kappa`，L1 依存だが statement 先行で並列可）:
  `Fin74/Litak/KappaMono.lean` — `forces_K_shift_succ : x ⊩ K⟦shift n⟧ → x ⊩ K⟦shift (n+1)⟧`
  と `≤` 版．
- **Step L3**（worktree `fin74-lt-gframe`，独立）: `Fin74/Kripke/GeneralFrame.lean` —
  `GeneralFrame`（`Frame` + `P : Set (Set κ)` + 補・∩・◇前像の閉性＋`univ ∈ P`），
  admissible 付値，`value_mem`，`GFValid`，`mkLogic_le_gf`
  （S4公理の反射推移妥当性・MP/Nec/Subst 保存）．`forces_subst`（代入と付値書き換えの対応）は
  既存資産を確認して再利用または新設．
- **Step L4**（worktree `fin74-lt-padm`，L3 依存・statement 先行可）:
  `Fin74/Litak/Admissible.lean` — 3領域分割，P の定義，閉性（◇ 前像計算：
  pred の有限/補有限補題群），`fineGFrame : GeneralFrame W`，標準付値 φ の admissible 性．

### Phase 2（コア，Phase 1 マージ後に専用プランニング）

- **Step L5**: `Fin74/Litak/SatisfiesE.lean` — `d₀ ⊩ E`（既存 SatisfiesE の corrected 版）．
- **Step L6**: `Fin74/Litak/ValidatesH.lean` — 𝔉 ⊨ H（GF版；既存 StronglyVerifiesH の
  機構を移植，鳩の巣は De/Do 版に差し替え）．
- **Step L7**: `Fin74/Litak/ValidatesG.lean` — 𝔉 ⊨ G（GF版；**最難関**．専用 Fable
  プランニング必須）．
- **Step L8**: `Fin74/Litak/Lemma1.lean` — (I) の Kripke 版（できれば complete general frame 版）．
  上限補題（無限分配則）を含む．
- **Step L9**: `Fin74/Litak/Incomplete.lean` — 最終定理の組み立て．

## 追記（2026-07-22）：Gerson [Ger75] の検証により Route A（一般フレーム不要）へ方針転換

ユーザー提供の Gerson [Ger75]（"The Inadequacy of the Neighbourhood Semantics for Modal
Logic", JSL 40(2), 1975）§4 を精読．Fable（`model: fable`）に，一次資料の画像（`.notes/Ger75/`・
`.notes/Lit04/`・`.notes/Fin74/`）と既存 Lean 資産を直接読ませて検証・再プランニングさせた．

### 新発見1：Gerson の式は Litak と部分的に一致する（対称 C のみ，A は3連言のまま）

Gerson §4（p.145）の式定義は，印刷版 [Fin74] とは異なり **`C_{m+2} := ◇C_{m+1} ⋏ ◇B_m ⋏
∼◇B_{m+1}`**（B の完全な鏡像．印刷版の `∼◇B_{m+2}` ではない）を使う．これは [Lit04] の γ の
修正と完全に一致する．ただし Gerson の `A_m` は印刷版と同じ**3連言**（`∼◇B_{m+2}` のみ，
[Lit04] の第4連言 `∼◇C_{m+2}` は無い）．

Gerson の「Claim 2」（`K_m → K_{m+1}` の S4 導出可能性）は [Lit04] Lemma 2.2 の初出であり
（[Lit04] 自身が Gerson に帰属），完全な導出が p.146 に載っている．Fable がこれを検算：
**正しい**．対称化された C により，K1 の鏡像として **K2 も無条件に**（`∼◇(A m)` のような
追加仮定なしに）1段昇格することが確認された．これは
`Fin74/Lemma1/Basic.lean` の既存の `forces_K2_succ_of_not_dia_A`（`∼◇(A m)` を要求する
局所的な回避策）を，対称化された C の下では不要にする．**ユーザーの見立て「Gerson の証明は
あっているのでは」は正しかった**．

### 新発見2：Gerson の修正だけでは stage 2 の反例は消えない．Litak の第4連言が必須

`Fin74/Lemma2/NotValidatesG.lean` で機械検証済みの反例（`c_3 ⊩ A_0`）は，`R(c_3,·)` が
`B_2`（`{b_2}` のみが強制点）を見ないことに由来し，これは **C の対称化と無関係**
（`B_2` の定義は C を参照しない）．Fable が具体的に再計算し確認：対称 C＋3連言 A のままでは
`[A_n] = {a_n, c_{n+3}}`（`c_{n+3}` のリークは残る）．[Lit04] の第4連言 `∼◇C_{n+2}` を追加
すると `c_{n+3}` は `c_{n+2}` を見るためこれで排除され，**`[A_n] = {a_n}` ちょうど**（他の
リークも系統的に確認済み，b/c/a/d の全候補を排除）．したがって **Litak の完全な修正（対称 C
＋4連言 A＋両方向 D）が stage 2 を救うために必要**であり，Gerson の修正はその一部（K2 の
無条件化）のみを提供する．

Gerson 自身の Theorem 2 は，`¬E ∉ L'` の部分を「Fine [1] (Lemma 2) で示されているので
繰り返さない」と明記して**印刷版 Fine の（壊れた）Lemma 2 をそのまま引用**している．
つまり Gerson も stage 2 の反例を独立に検証していない．一方 [Lit04] Theorem 2.4 も
「Σ₁ ⊬ φ₁ は Fine の論文にある」と同様に委ねている．**このプロジェクトが機械検証した
反例は，過去の文献のいずれにも記録されていない新規の発見と判断してよい**．

なお `.notes/Ger75A.pdf`（Gerson の別論文，"An Extension of S4 Complete for the
Neighbourhood Semantics but Incomplete for the Relational Semantics", Studia Logica 34）は
`grep` で確認：Fine の式族への言及なし，無関係な独立構成．本タスクでは使わない．

### 方針転換：Route A（Litak 修正式族＋既存の具体モデル 𝔄 で Kripke 不完全性を直接証明）

Fable が Litak の完全修正式族（対称 C＋4連言 A＋両方向 D）のもとで，**既存の具体モデル
𝔄 = (W,R,φ)（`Fin74/Lemma2/Model.lean`，変更なし）が任意の付値 ψ で frame ⊧ G を満たす**
ことを，V字分類・原子集合の釘付け・導出真理集合の伝播という手計算で完全にスケッチした
（下記 Step 8 参照）．これにより，**上記 (II) 節の一般フレーム／許容代数 P（有限・補有限・
De/Do 分割）は不要**であることが判明した．「Fine logic の不完全性」（ユーザーの依頼）は
Kripke 意味論だけで完結し，[Lit04] Theorem 2.4 の「completely incomplete」（一般フレーム版，
上記 (I)(II) 節）は真に強い結果だが今回のスコープを超える．

**Route A を主目標とし，Step L3（`GeneralFrame.lean`，worktree `fin74-lt-gframe`）・
Step L4（`Admissible.lean`）は凍結（今後のストレッチ課題として保持，`.directions/` に記録）．**
Route A の「任意 ψ での frame ⊧ G」は Route B の Step L7（許容付値のみでの GF妥当性）を
論理的に含意するため，Route A 完成後に Route B へ戻る作業は無駄にならない．

### Route A 実装ステップ（新規，旧 Step L1/L2/L5〜L9 を置き換え）

新規ディレクトリ `Fin74/Litak/`，名前空間 `Fin74.Litak`．`Fin74/Lemma2/Model.lean`
（`W`・`R`・`frame`・`φ`・`R_refl`/`R_trans`/`R_antisymm`）はそのまま import，変更不要．

- **Step 1**（`Fin74/Litak/Formula.lean`，worktree `fin74-lt-formula` で着工済み・要修正）：
  B/C（対称相互再帰）・4連言 A・両方向 D・**添字付き** `K1 m`/`K2 m`/`K3 m`/`K4 m`/`K m`
  （旧プランの固定添字 K1..K4 から変更：`E := D ⋏ ◇(A 0) ⋏ K 0` の形で以降の shift が
  一様に書けるようにする）・E/F/G・`LogicFine`．既存 `Fin74/Logic/Basic.lean` に軽微に類似．
- **Step 2**（`Fin74/Litak/Shift.lean`）：shift 代入と展開補題．`Fin74/Logic/Shift.lean` の
  ほぼ逐語移植．
- **Step 3**（`Fin74/Kripke/Basic.lean` への追加，独立）：意味論的代入補題 `forces_subst`
  （`x ⊩[⟨F,V⟩] A⟦σ⟧ ↔ x ⊩[⟨F,V_σ⟩] A`）と，`Frame.Validates`→`Model.StronglyVerifies` の
  代入閉包の系．
- **Step 4**（`Fin74/Litak/KLemmas.lean`，ユーザー名指しの目標）：Gerson Claim 2 / [Lit04]
  Lemma 2.2 の意味論版．`forces_K1_succ`・**`forces_K2_succ`（無条件，K1 の鏡像）**・
  `forces_K3_succ_of_K1`・`forces_K4_succ_of_K2`・`forces_K_succ`・`forces_K_mono`．
  引用は `- [Ger75, Claim 2]`・`- [Lit04, Lemma 2.2]`．K1/K3/K4 は既存 `Lemma1/Basic.lean`
  の該当補題を式族名だけ替えて移植．K2 は新規だが自明級（K1 の鏡像）．
- **Step 5**（`Fin74/Litak/Lemma1.lean`）：既存 `Lemma1/Basic.lean` の簡略版（K2 昇格に
  `∼◇(A m)` 不要になった分だけ簡潔化）．ψ-モデル部（`psiVal`・`forces_s_iff`・
  `psi_forces_neg_H`）は式族に依存しないため `Fin74` 名前空間から逐語再利用（移動不要）．
- **Step 6**（`Fin74/Litak/SatisfiesE.lean`）：既存 `Lemma2/SatisfiesE.lean` の中規模改変移植．
  `forces_C2_iff`（新規，B2の鏡像）追加，`forces_D_d0`・`forces_A0_a0` に修正式族対応の
  ケースを1つずつ追加．
- **Step 7**（`Fin74/Litak/Swap.lean`，独立）：b↔c 鏡像対称性のインフラ（`swap : W → W`・
  原子交換代入 τ・`(B m)⟦τ⟧ = C m` 等・force の転送補題）．修正された対称式族だからこそ
  E/F/G が τ-不変になり，この節が意味を持つ（印刷版では不成立）．
- **Step 8**（`Fin74/Litak/ValidatesG.lean` 群，最重要かつ最大．8a〜8g は statement 確定後
  ファイルを分けて並列実装推奨）：`frame ⊧ G` の直接証明．
  - 8a `exists_V_shape` の移植（既存 `Lemma2/NotValidatesG.lean` の同名補題，A の展開が
    4連言になる点のみ変更）．
  - 8b 閉じ込め：`w ⊩ D → ∃m, w = W.d m`（両方向 ι₁ から p0/p1 交代の無限鎖，
    `Model.exists_strictChain`＋既存 `ChainConfinement.lean`/`Kripke/Chain.lean` の
    `strict_chain_all_d` を逐語再利用）．
  - 8c V字分類：純組合せ論（R の閉形式＋omega）で，V字の5点が鏡像を除き
    `(b_{n+1},b_n,c_{n+1},c_n)` に一意に押し込まれることを場合分けで確定．
  - 8d 原子集合の釘付け：cone(w) 内で `[B1]={b_{n+1}}`・`[C1]={c_{n+1}}` などが exactly
    成立することを K-block の box 制約から順に消去．
  - 8e 導出真理集合：`[B2]`・`[C2]`・`[B3]`・`[C3]` の exactly 成立を 8d から伝播．
  - 8f A レベル：`[A0]∩cone(w)={a_n}`（**第4連言が c_{n+3} を排除する箇所**）・
    `[A1]∩cone(w)={a_{n+1}}`，および `w ⊩ ◇A0` から `m ≤ n` が従うこと．
  - 8g 組み立て：証人 `y := d_{n+1}` で `w ⊩ F` を締める．鏡像ケースは Step 7 の
    WLOG で正立ケースに帰着．
  詳細な証明スケッチ（各ステップの場合分けの筋道）は Fable のレポート全文を
  `.directions/202607220000_fin74-litak-route-a.md` に転記済み．実装者は着手前に必読．
- **Step 9**（`Fin74/Litak/StronglyVerifiesH.lean`）：既存 `Lemma2/StronglyVerifiesH.lean` の
  機構（`phase`・`exists_phase_chain`・鳩の巣補題）は式族と無関係なので逐語再利用．
  欠けている最終定理 `model.StronglyVerifies H` の組み立てのみ新規．
- **Step 10**（`Fin74/Litak/Incomplete.lean`）：命題公理・S4公理の全モデル妥当性補題，
  `mkLogic {G,H} A → model.StronglyVerifies A`（帰納），
  `¬ mkLogic {G,H} (∼E)`（さもなくば恒等代入で `model ⊧ ∼E` が `d0 ⊩ E` と矛盾），
  主定理 `fine_logic_kripke_incomplete`．
- **Step 11（ストレッチ・任意）**：構文版 Lemma 2.2（`LogicS4` 上の導出可能性），
  Route B 再開（Step L7 は Route A から自動的に従う），回帰テスト
  `(W.c 3) ⊮[model] Litak.A 0`（`NotValidatesG` との対比）．

**再利用サマリ**：逐語再利用 = `Lemma2/Model.lean`・`Lemma2/MemGraph.lean`・
`Lemma2/ChainConfinement.lean`・`Lemma2/StronglyVerifiesH.lean` の機構・`Kripke/Chain.lean`・
`Lemma1/Basic.lean` の ψ-モデル部．軽微リネーム移植 = `Logic/Shift.lean`・`exists_V_shape`・
K1/K3/K4 補題・`SatisfiesE.lean` の大半・`chain_step`/`lemma1`．実質新規 = `forces_subst`・
K2 無条件版・Step 7・Step 8b〜8g（核心）・Step 9 の結論・Step 10．旧 `Fin74`（印刷版）
名前空間と `NotValidatesG.lean` は「印刷版が壊れていることの機械検証」として変更せず保存する．

## 追記履歴

- 2026-07-21: 初版．
- 2026-07-22: Gerson [Ger75] の検証結果を反映．Route A（Litak 修正式族＋既存具体モデルによる
  直接 Kripke 不完全性証明）へ方針転換．Route B（一般フレーム）は凍結・ストレッチ課題化．
