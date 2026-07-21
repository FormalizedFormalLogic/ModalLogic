# Fin74 Lemma 2: 論文の誤りの形式証明プラン（not-validates-G）

作成: 2026-07-21．立案: Fable（メインループ）．

## 背景と決定

[Fin74] Lemma 2 は「モデル 𝔄 = (W, R, φ) は L を強検証しつつ E を満たす」と主張するが，
その証明 stage (2)（(W,R) validates G）は成立しない．本セッションで論文原文
（p.23-28，300dpi スキャン画像）を一切の前提なしに読み直し，以下を再確認した
（過去3回の独立検証と同一の結論，通算4回目）．

- Lean 側の定義（`B`/`C`/`A`/`D`/`E`/`F`/`G`/`H`，`W`/`R`/`φ`）は論文と逐語一致する．
  特に `D` に `□(p1 → …)` の対称節が無いこと，`C_{m+2}` の否定節が `∼◇B_{m+2}`
  （同添字）であることも論文どおり．
- `R` の閉形式は論文 p.25 の集合論的定義（推移閉包 TC）から正しく導出されている．
  `TC({c_m}) = {c_k : k ≤ m} ∪ {b_k : k ≤ m−2}` 等．
- **論文 p.27 の誤り**: 「B₂ (C₂, A₀, B₃, C₃, A₁) は b_{n+2} (c_{n+2}, a_n, b_{n+3},
  c_{n+3}, a_{n+1}) でのみ真」という主張のうち **A₀ の一意性が偽**．論文自身の直前の
  前提（i<2 で B_i/C_i は b_{n+i}/c_{n+i} でのみ真）だけから **c_{n+3} ⊩ A₀** が導ける：
  - c_{n+3} は b_{n+1}（(n+1)+2 ≤ n+3）と c_{n+1} を見るので ◇B₁ ⋏ ◇C₁．
  - c_{n+3} は b_{n+2} を見ない（(n+2)+2 ≤ n+3 は偽）．さらに c_{n+3} の錐
    {b_k : k ≤ n+1} ∪ {c_k : k ≤ n+3} 内に B₂ = ◇B₁ ⋏ ◇C₀ ⋏ ∼◇C₁ を強制する点は無い
    （b_{n+1} を見るのは c_{n+3} 自身と b_{n+1} のみ；c_{n+3} は c_{n+1} を見るので
    ∼◇C₁ に反し，b_{n+1} は c_n を見ないので ◇C₀ に反する）．よって ∼◇B₂．
- その帰結として F の証人が存在しない：φ の下で p₀⋎p₁ を満たす点は d 点のみで，
  すべての d 点は（全 c 点を見るので）c₃ 経由で ◇A₀ を満たし，∼◇A₀ を満たせない．
  よって `(𝔄, d₀) ⊩ E` かつ `(𝔄, d₀) ⊮ F`，すなわち 𝔄 自身の付値で既に G が破れる．

ユーザー指示（2026-07-21）:「元論文の定義をそのまま正確に検討して Lemma 2 が
証明できるか確認せよ．…元論文の定義でうまくいかないのなら，なぜかを説明し，
やはり元論文の定義を可能なら形式化して誤りを形式証明で提出せよ」．
→ 上記のとおり元論文の定義では成立しないため，**誤りの形式証明を提出する**．

## 成果物（2ファイル，独立に並列実装可能）

### Step N — `Fin74/Lemma2/NotValidatesG.lean`（worktree: `fin74-l2-notg`）

`ValidatesG.lean` を置き換える（`exists_V_shape`・構造補題群は真なので新ファイルへ移設し，
偽の目標 `validates_G : frame ⊧ G` の sorry を反証定理群に差し替える）．

statement 一覧（骨組み→中身の順で実装）:

1. `forces_A0_c3 : (W.c 3) ⊩[model] A 0`
   — 証人: c₃ ≺ b₁（1+2≤3）で `forces_B1_iff`，c₃ ≺ c₁ で `forces_C1_iff`；
   ∼◇B₂ は `forces_B2_iff`（既存，SatisfiesE.lean）で任意の B₂ 点は b₂ に等しく，
   c₃ ⊀ b₂（2+2≤3 は偽）で閉じる．
2. `forces_dia_A0_d (k : ℕ) : (W.d k) ⊩[model] ◇(A 0)`
   — d_k ≺ c₃（d は全 c を見る）＋ 1．
3. `not_forces_F_d0 : (W.d 0) ⊮[model] F`
   — F の証人 y は φ の下で p₀⋎p₁ を満たすので `cases y` で y = d_j に限られ，
   y ⊩ ∼◇A₀ が 2 と矛盾．
4. `forces_E_d0 : (W.d 0) ⊩[model] E`
   — `forces_E_iff`（Logic/Shift.lean）＋既存の `forces_D_d0`・`forces_dia_A0_d0`・
   `forces_K0_at_d0`（SatisfiesE.lean）の合成のみ．
5. `not_validates_G_model : ¬ (model ⊧ G)`
   — w = d₀，G = E 🡒 F，3・4 から．
6. `not_validates_G_frame : ¬ (frame ⊧ G)`
   — 付値 φ を代入（`Model.mk frame φ = model` は定義的）．
7. `subst_id`（`Formula/Substitution.lean` に追加）: `A⟦(# ·)⟧ = A`（構造帰納法）．
8. `not_stronglyVerifies_G : ¬ model.StronglyVerifies G`
   — 恒等代入 σ = (# ·) と 5・7 から．
9. `not_stronglyVerifies_LogicFi : ¬ (∀ A ∈ LogicFi, model.StronglyVerifies A)`
   — G ∈ LogicFi（`mkLogic.addAxiom`，G ∈ {G, H}）と 8 から．
   これが [Fin74] Lemma 2 の主張「𝔄 strongly verifies L」の直接の反証．

注意: 旧 `validates_G`（sorry）は削除する．`Fin74.lean` の import
`Fin74.Lemma2.ValidatesG` を `Fin74.Lemma2.NotValidatesG` に張り替える．

### Step M — `Fin74/Lemma2/MemGraph.lean`（worktree: `fin74-l2-memgraph`）

論文 p.25 の集合論的定義を所属グラフとして文字どおり形式化し，閉形式 `R` との
同値を機械証明する（「閉形式への翻訳ミス」の可能性を Lean 内で排除する）．

前提となる読み（module docstring に記載）: b₀ = 0，c₀ = 1 をリテラルな von Neumann
順序数として読むと b₁ = {0} = 1 = c₀ と衝突して構成が潰れるため，b₀・c₀ は相異なる
urelement（要素を持たない相異なる対象）として読む．これが唯一の整合的解釈．
また TC({w}) は {w} ∪ w ∪ ⋃w ∪ … で w 自身を含む（S4 の反射性・論文 p.27 の
使用例と整合する標準的な読み）．

1. `mem : W → W → Prop` — `mem w v` ⟺ v ∈ w（論文の集合等式そのまま）:
   - `mem (.b m) (.b k) ↔ m = k + 1`（b₁ = {b₀}，b_{m+2} ∋ b_{m+1}）
   - `mem (.b m) (.c k) ↔ m = k + 2`（b_{m+2} ∋ c_m）
   - `mem (.c m) (.c k) ↔ m = k + 1`，`mem (.c m) (.b k) ↔ m = k + 2`（対称）
   - `mem (.a m) (.b k) ↔ k = m + 1`，`mem (.a m) (.c k) ↔ k = m + 1`
     （a_m = {b_{m+1}, c_{m+1}}）
   - `mem (.d n) (.a k) ↔ n ≤ k`（d_n = {a_m : m ≥ n}）
   - 他は False（b₀・c₀ は urelement で要素なし；d の要素に b/c/d は無い等）
2. `Rtc (w v : W) : Prop :=`
   `((∀ m, v ≠ .d m) ∧ Relation.ReflTransGen mem w v) ∨`
   `(∃ m, v = .d m ∧ ∀ k, m ≤ k → mem w (.a k))`
   — 論文の `wRv iff (∀m)(v≠d_m) & v ∈ TC({w}) or (∃m)(v=d_m) & w ⊇ v` の直訳．
   `v ∈ TC({w})` ⟺ `ReflTransGen mem w v`（TC({w}) = {w} ∪ 要素の推移的取り尽くし），
   `w ⊇ d_m` ⟺ d_m の全要素 a_k (k ≥ m) が w の要素．
3. `theorem Rtc_iff_R (w v : W) : Rtc w v ↔ R w v`
   - (→) 第1選言肢: `ReflTransGen.head_induction_on` 等で mem ⊆ R（1ステップ検査）と
     `R_refl`・`R_trans` に帰着．第2選言肢: w を cases（b/c/a は a 要素を持たないので
     k = m で矛盾；d n なら n ≤ m が出て `R (.d n) (.d m)`）．
   - (←) 各閉形式ペアに明示的な mem 鎖を構成．補助補題
     `b_descend : k ≤ m → Relation.ReflTransGen mem (.b m) (.b k)`（帰納法），
     `c_descend` 同様．d n R b k は d n → a (max n k) → b (max n k + 1) → … → b k．

## 統合手順

両 worktree 完了後，`fin74-lemma2` に merge → `just mk-all` → `just shake` →
`lake build`（sorry・警告なし確認）→ `grep` でプラン参照コメントの残存確認 → 報告．
`main` へのマージはユーザー承認後．

## 追記履歴

- 2026-07-21: 初版（本ファイル）．
