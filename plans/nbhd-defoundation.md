# ModalNeighborhood の脱 Foundation 化 設計文書

`ModalNeighborhood`（41ファイル・約4200行）を，外部パッケージ `Foundation` への依存から切り離し，
Mathlib のみに依存する自己完結ライブラリにするための設計とステップ分割．

- 対象: `ModalNeighborhood/` 配下のみ．`Fin74` は Foundation（`Foundation.Vorspiel.Set.Basic`）への依存が残るため，`lakefile.toml` の `require Foundation` 自体は当面残す．`ModalNeighborhood` のどのモジュールも `Foundation.*` を import しない状態が完成条件．
- 本文書中の Lean 風の型表記はすべて擬似コードであり，実装時の正確な構文は実装担当が確定する．

---

## 1. 現状分析

### 1.1 依存の層構造

`ModalNeighborhood` が Foundation から借りているものは，実ソースを精査した結果，次の6層に整理できる．

| 層 | Foundation 側モジュール | 内容 | ModalNeighborhood での使われ方 |
|---|---|---|---|
| (A) 記法クラス | `Logic/LogicSymbol`（740行）・`Modal/LogicSymbol`（500行） | `Tilde`/`Arrow`/`Wedge`/`Vee`/`Box`/`Dia`/`LogicalConnective`/`BasicModalLogicalConnective`/`ŁukasiewiczAbbrev`/`DiaByBox` の型クラス群と `□^[n]`・`◇^[n]` | `□`・`◇`・`∼`・`🡒`・`⋏`・`⋎`・`🡘` の記法と，`Box.boxItr` 反復記法．全域で使用 |
| (B) 論理式 | `Modal/Formula/Basic`（709行） | `Formula α`（primitive: `atom`/`falsum`/`imp`/`box`），派生記号は abbrev（`∼φ := φ 🡒 ⊥`，`◇φ := ∼□∼φ`，`⋏`/`⋎` は Łukasiewicz 式），`subformulas`，`subst`，`Encodable`，`Letterless` ほか | `Formula ℕ` のみ使用．`subformulas`/`IsSubformulaClosed` は filtration 系（現在コメントアウト中，別 worktree で開発中）と `EN4.lean` が使用．`Letterless`・`Encodable`・`atoms` は不使用 |
| (C) Entailment 抽象 | `Logic/Entailment`（639行）・`Propositional/Entailment/Minimal/Basic`（1508行）・`Cl/Basic`・`Cl/Łukasiewicz`・`Modal/Entailment/Basic`（885行）・`Modal/Entailment/E` ほか | `Entailment S F`（`Prf : S → F → Type`），`⊢!`（Type）と `⊢`（Prop）の2層，`⪯`/`⪱`/`≊`/`Incomparable`，`Consistent`，`FiniteContext`/`Context`，`Entailment.Cl`（Łukasiewicz公理＋MP＋DNE），`RE`/`RM`，`HasAxiomM/C/N/K/T/B/D/P/Four/Five/Geach` と accessor（`axiomT!` 等），E系のバンドル `Entailment.E`/`EM`/…/`ET5` | `variable {𝓢 : S} [Entailment.E 𝓢]` の形で `Completeness.lean`・`AxiomGeach.lean`・`AxiomN.lean`・各 `Logic/*.lean` の完全性節が使用．`⪯`/`⪱`/`Incomparable` は Logic 比較の全定理で使用 |
| (D) Hilbert 体系と論理 | `Modal/Hilbert/Axiom`（149行）・`Modal/Hilbert/WithRE/Basic`（520行）・`Modal/Logic/Basic`（193行） | `Logic α := Set (Formula α)`（`Entailment (Logic α) (Formula α)` は所属で定義），`Axiom α := Set (Formula α)` と `Axiom.HasM` 等の「公理所持」クラス，`inductive Hilbert.WithRE Ax : Logic α`（axm+subst / mdp / re / implyK / implyS / elimContra），`rec!`，`weakerThan_of_subset_axioms`/`weakerThan_of_provable_axioms`，28論理（`Modal.E` … `Modal.ET5`）の定義とバンドルインスタンス | `Hilbert.lean` の健全性帰納，全 `Logic/*.lean` の論理定義参照・包含関係（`weakerThan_of_subset_axioms` 37回） |
| (E) MCS | `Modal/MaximalConsistentSet`（598行） | 集合の無矛盾性 `T *⊬[𝓢] ⊥`（`Context` 経由），Lindenbaum（Zorn），`MaximalConsistentSet` と所属補題群 | `Completeness.lean` の `proofset`・正準モデル，`AxiomGeach.lean`・`AxiomN.lean`・`ET5.lean` 等が `lindenbaum`・`mem_of_prove`・`mdp_provable`・`iff_mem_neg` を使用 |
| (F) 意味論インタフェース | `Logic/Semantics`（359行） | `Semantics M F` 型クラス，`⊧`/`⊭`/`⊧*`，`Semantics.Top/Bot/Tarski`，`Sound`/`Complete`（`Logic/Entailment` 側），`Sound.not_provable_of_countermodel` | `Basic.lean` が世界・モデル・フレーム・フレームクラスの4つのキャリアに `⊧` を多重定義．`Sound`/`Complete` インスタンスと `not_provable_of_countermodel`（40回）は全 Logic ファイルの主役 |

このほか `Vorspiel` から実際に使っているのは次の3点のみ．

- `Vorspiel/Set/Fin`: `Set.Fin1.all_cases`・`Set.Fin2.all_cases`（有限フレーム反例の羃集合全列挙）と付随 simp 補題．`EM.lean`・`EP.lean`・`ECN.lean`・`ENT4.lean` が使用．
- `Vorspiel/Set/Basic`: `Set.doubleton_subset`，`Set.subset_mem_chain_of_finite`（Lindenbaum の Zorn 部で使用）．
- `Foundation.Meta.ClProver` の `cl_prover` タクティク: `Completeness.lean` の2箇所のみ．

### 1.2 機械生成 API 表面（123宣言）の精査 — 見かけ上の依存

`foundation-api-surface.md` は単純名マッチによる機械生成のため，**同名衝突による偽陽性**をかなり含む．実ソースと突き合わせた結果，以下は実依存ではない．

- `Foundation/Meta/ClProver` の `M`（152回）: `Axioms.M` との単純名衝突．`cl_prover` タクティクの実使用は2箇所のみ．
- `Foundation/Modal/PLoN/*` 全部: `Frame`/`Model`/`FrameClass`/`sound`/`complete` 等はすべて Neighborhood 側の同名宣言との衝突．**実依存は `EN.lean` の import 1行のみで，本文では PLoN を一切使っていない（死んだ import）**．grep で確認済み．
- `Foundation/Modal/Hilbert/Normal/Basic`（`N`・`K`・`weakerThan_of_subset_axioms`）: `Axioms.N`/`Axioms.K`/`Hilbert.WithRE.weakerThan_of_subset_axioms` との衝突．正規様相論理は不使用．
- `Foundation/Modal/Entailment/GL・Grz・KTc・KP` の `axiomT`/`axiomFour`/`axiomD`/`g`: `Entailment/Basic` 側 accessor との衝突．
- `Foundation/Propositional/Formula/Basic`: `Modal.Formula` と同じ単純名 `Formula`/`subformulas`/`subst` の衝突．命題論理の Formula は不使用．
- `Foundation/Vorspiel/List/Basic`（`finite`・`toSet`）・`Vorspiel/AdjunctiveSet`（`Finite`）・`Vorspiel/Rel/*`（`trans`・`IsSerial`）: Mathlib の `Finset.toSet`・`Set.Finite` や Neighborhood 側 `Frame.IsSerial`・`IsTransitive.trans` との衝突．実依存なし．

したがって**真の移植対象は層 (A)〜(F) ＋ `Set.Fin` ヘルパ＋ `cl_prover` の代替**に絞られる．Foundation の推移的閉包 73 モジュール・14,475行のうち，意味のある部分はおよそ 3,500 行相当で，さらに後述の設計単純化（Type レベル証明の廃止・記法クラス塔の廃止）で新規コードは **約 2,000〜2,500 行**に収まる見込み．

### 1.3 隠れた依存（見落としやすいもの）

- **`⊢!`（Type レベル証明項）と `⊢`（Prop）の2層構造**: Foundation は `Prf : S → F → Type` を持ち，各補題が `def foo : 𝓢 ⊢! …` と `lemma foo! : 𝓢 ⊢ …` の2本立て．`ModalNeighborhood` が使うのは **`!` 付き（Prop）側のみ**（grep 確認: `re!`・`rm!`・`axiomT!`・`axiomFour!`・`axiomD!`・`axiomGeach!`・`mem_of_prove`・`mdp_provable` 程度）．
- **`simp`/`grind` が暗黙に使う属性**: 既存 41 ファイルの証明は，`axiomM!` 等に付いた `@[simp]` や `Logic.iff_provable` の `@[grind =]` に強く依存して `simp`/`by simp`/`by grind` で閉じている（例: `Logic/E.lean` の `. simp;` は `Hilbert.WithRE.axm'!`＋`@[simp] axiomM!` で閉じている）．移植時に**属性の付与位置を Foundation と同一に保つ**ことが，既存証明を無傷で通すための実質的な互換性条件になる．
- **`◇` が definitional abbrev であること**: `MaximalConsistentSet` や `Canonicity.iff_dia` の証明は `◇φ = ∼□∼φ` が `rfl` で成り立つことを使っている（`_ ↔ ∼□(∼φ) ∈ Γ.1 := by rfl`）．新 `Formula` でも `◇` を abbrev にしなければならない．
- **`Semantics.set_models_iff`（`⊧*` の展開）**: `Hilbert.lean` の `consistent_of_sound_frameclass` が使用．
- **filtration 系との整合**: `Logic/E4.lean` 等のコメントアウト部と別 worktree（nbhd-filtration）が `φ.subformulas`・`FormulaSet.IsSubformulaClosed`・`Formula.subformulas.subset_of_mem` を Foundation の名前で使っている．新コアでも**同名 API** を提供しておくと，filtration 移植がそのまま載る．

---

## 2. 設計方針と結論

### 2.1 どこまで移植するか / Entailment 抽象の扱い（検討事項1）

**結論: 2パラメータ抽象 `Entailment S F`（`𝓢 : S`）は廃止し，`Logic := Set Formula` に固定した上で，証明可能性の閉包条件を `L : Logic` 上の型クラスとして持つ．**

具体的には次の設計にする．

- `Logic := Set Formula`．`L ⊢ φ` は `φ ∈ L` の記法（`def Logic.Provable (L : Logic) (φ : Formula) : Prop := φ ∈ L`，`infix ⊢`．`⊬` も同様）．Foundation の `theory 𝓢` は `L` 自身に潰れる．
- Type レベルの `Prf`・`⊢!` は作らない．**Prop 一本**．これで Foundation の `def foo / lemma foo!` の2本立てが全廃でき，`Modal/Entailment/Basic`（885行）相当は半分以下になる．補題名は移行コスト最小化のため Foundation の `!` 付き名をそのまま使う（`axiomT!` 等．`!` はもはや区別の意味を持たないが，41ファイルの証明本文を書き換えないことを優先する．統合後の一括リネームは任意の後続タスク）．
- 閉包条件は `L : Logic` 上の型クラス（Prop クラス）で表す．Foundation の階層を E 系に必要な最小限だけ写す:
  - `Logic.ModusPonens L`・`Logic.HasImplyK L`・`Logic.HasImplyS L`・`Logic.HasElimContra L`（この4つで `Logic.Cl L` バンドル）．
  - `Logic.HasRE L`（`L ⊢ φ 🡘 ψ → L ⊢ □φ 🡘 □ψ`）．
  - `Logic.HasAxiomM/C/N/K/T/B/D/P/Four/Five/Geach g`（accessor 補題 `axiomM!` 等を `@[simp]` 付きで同名提供）．
  - バンドル: `Logic.IsE := Cl + HasRE`，以下 `IsEM`・`IsEC`・`IsEN`・`IsEMC`・`IsEMN`・`IsECN`・`IsEMCN`・`IsEK`・`IsET`・`IsEMT`・`IsED`・`IsEB`・`IsE4`・`IsEMC4`・`IsEMT4`・`IsE5`・`IsET5`・`IsETB`・`IsEMK`・`IsEND` と，その間の `instance` 継承（Foundation `Entailment/Basic` の E 系セクション＋ `Entailment/EM.lean` 等の個別ファイル相当．K 系・GL 系・S4 系などの正規論理バンドルは**移植しない**）．
  - `Logic.Substitution L`（代入閉包）と `Logic.Consistent L` も同様にクラス化．
- `⪯`/`⪱`/`≊`/`Incomparable` は `Logic` に特化して定義し直す．provability = membership なので **`L₁ ⪯ L₂ ↔ L₁ ⊆ L₂`** となり，Foundation の `theory` 経由の定義より大幅に単純化する．既存コードが `instance : Modal.E ⪱ Modal.EM := …` とクラスとして使っているので，クラスのまま提供し，`weakerThan_iff`・`not_weakerThan_iff`・`strictlyWeakerThan_iff`・`Incomparable.of_unprovable`・`StrictlyWeakerThan.of_unprovable_provable`・`Equiv.antisymm_iff` 等の使用中補題を同名で用意する．

**採らなかった選択肢とその理由．**

- (i) Foundation の `Entailment S F` をそのまま写す: `Prf` の Type レベル層・`Axiomatized`/`Compact`/`Deduction`/`Pullback` 等，この ライブラリで一切使わない一般性を丸ごと抱え込む．また `S` を抽象化する動機（算術など他の証明体系との共有）はこのリポジトリの方針（プロジェクト独立）と正反対．却下．
- (ii) さらに進めて `Hilbert Ax` に全面特化（型クラスなし，全補題を `Ax : Axiom` パラメータ＋ `[Ax.HasT]` で書く）: コード量は最小になるが，`Completeness.lean` の `Canonicity`・`proofset` 節が現在 `variable {𝓢} [Entailment.E 𝓢]` の形で書かれており，これを `Hilbert Ax` に書き換えると既存証明の変数・インスタンス参照を広範囲に手直しする必要がある．`L : Logic` 上のクラスなら `𝓢` → `L`，`Entailment.E 𝓢` → `L.IsE` の機械置換で済む．また「Hilbert 表示を持たない論理」（例えばフレームクラスの論理 `C.logic` に対して閉包性を語る）にもクラスがそのまま使える．却下（ただし §2.4 の通り，公理クラス `Axiom.HasM` → `(Hilbert Ax).HasAxiomM` の instance 生成は Hilbert 特化で行う）．

なお `Canonicity`・`AxiomGeach.lean` の「任意の `𝓢` に対する一般性」は，この設計では「任意の `L : Logic` with `[L.IsE]`」として**維持される**．失うのは「`Logic` 以外の証明体系 `S`」への一般性だけであり，本ライブラリ内に用例はない．

### 2.2 `Formula` の構成方法（検討事項2）

**結論: Foundation と同じ primitive（`atom`・`falsum`・`imp`・`box`）を維持し，原子命題の型は `ℕ` に固定する．派生記号は `@[match_pattern] abbrev` とし，記法クラス塔（層A）は導入しない．**

- primitive の選択理由:
  - 近傍意味論の中核再帰（`Model.truthset`）と完全性の truth lemma（`Canonicity.truthlemma`）は `atom`/`⊥`/`🡒`/`□` の4ケース帰納であり，現行コードはこの構成に最適化済み．`□` は `𝒩` に直結する意味論の主役なので primitive にすべきで，`◇` は `∼□∼` の abbrev が正しい（`Frame.dia := (box ·ᶜ)ᶜ` と定義的に対応し，`Satisfies.dia_dual` や MCS の `iff_dia` が `rfl` ベースで通る）．
  - Fin74 は逆に `◇` を primitive（`□ := ∼◇∼`）としたが，あれは S4 の `◇` 中心の組合せ論のため．近傍意味論では逆にすべきで，**変更しない＝既存41ファイルの帰納法が一切崩れない**ことが最大の利点．
  - `∼`・`⋏`・`⋎`・`⊤`・`🡘` は Foundation の `ŁukasiewiczAbbrev` と同じ定義（`∼φ := φ 🡒 ⊥`，`φ ⋎ ψ := ∼φ 🡒 ψ`，`φ ⋏ ψ := ∼(φ 🡒 ∼ψ)`，`⊤ := ∼⊥`，`🡘 := (→)⋏(←)`）の abbrev にする．これにより `truthset.eq_and`・`eq_or`・`eq_neg` 等の既存 simp 補題の証明が変更なしで通り，かつ MCS の `∼φ ∈ Γ ↔ φ🡒⊥ ∈ Γ` が定義的になって Foundation の `NegationEquiv` 類が不要になる．
- 原子型を `ℕ` に固定する理由: `ModalNeighborhood` の全使用箇所が `Formula ℕ`．固定すれば `[DecidableEq α]` の伝搬（`subformulas`・MCS 系の仮定）が全て消える．CLAUDE.md の「プロジェクトごとに証明しやすい形で個別に用意する」方針とも一致．汎用化が必要になった時点で generalize すればよい．
- 記法は Fin74 と同様に素の `notation`/`infixr` で直接 `Formula` に付ける．Foundation の `LogicalConnective` 塔（1,240行）はゼロ行になる．`□^[n]`・`◇^[n]` は `Formula.multibox : ℕ → Formula → Formula`・`multidia` を再帰定義し，同じ表層記法 `□^[n]φ`・`◇^[n]φ` を与える（`AxiomGeach.lean`・`Completeness.lean` の `boxItr_proofset` 等が使用）．
- 付随 API: `subst`（`φ⟦s⟧` 記法，`Substitution := ℕ → Formula`，`Substitution.comp`），`subformulas : Formula → Finset Formula`（`subset_of_mem`・`mem_imp`/`mem_box`/`mem_neg`/`mem_and`/`mem_or` の grind 補題），`FormulaSet.IsSubformulaClosed`．**filtration worktree が Foundation 名で参照しているため，これらの名前・シグネチャは Foundation と揃える**．`Encodable`・`Letterless`・`atoms`・`toString`・`cases_neg`/`rec_neg` 系は不使用のため移植しない（必要になったら追加）．
- 既存41ファイルへの影響: primitive と abbrev の定義が Foundation と同一なので，帰納法・simp 集合は原理的に無傷．書き換えは (a) `Formula ℕ` → `Formula`（型引数の削除），(b) `Formula.atom` の綴り（そのまま），(c) `open Formula (atom)` 等の open 行の調整程度で，**機械的置換の範疇**．

### 2.3 極大無矛盾集合と Lindenbaum（検討事項3）

**結論: `Context`/`FiniteContext` 構造体は作らず，「有限部分集合の連言からの含意」を直接の定義とする文脈証明可能性を1本定義し，その上に必要最小限の MCS API を載せる．**

- 定義（擬似コード）:
  - `Finset.conj : Finset Formula → Formula`（`⋀Γ`．リスト経由でも直接 fold でもよいが，`models_finset_conj` 相当の simp 補題を持たせる）
  - `Logic.CProvable (L) (T : Set Formula) (φ) : Prop := ∃ Γ : Finset Formula, ↑Γ ⊆ T ∧ L ⊢ Γ.conj 🡒 φ`（記法 `T *⊢[L] φ`）
  - `FormulaSet.Consistent L T := ¬(T *⊢[L] ⊥)`
- Foundation の `Context.deduct` に相当する演繹定理は，導出に対する帰納を回さず，**Cl の命題論理補題だけで** `insert φ Γ` の連言と `φ 🡒 (Γ.conj 🡒 ψ)` の相互変換として証明できる（Foundation も実質この方式）．RE 規則が文脈で使えない問題はこの定式化では最初から生じない．
- 必要な MCS API（実使用から逆算した最小集合）:
  - `FormulaSet.Consistent` 系: `def_consistent`（有限部分集合特徴付け），`emptyset_consistent`，`either_consistent`，`unprovable_iff_insert_neg_consistent`，`unprovable_iff_singleton_neg_consistent`，`not_mem_falsum_of_consistent`．
  - `lindenbaum`（Zorn: Mathlib `zorn_subset_nonempty`＋鎖の有限部分集合補題）．
  - `MaximalConsistentSet L`（subtype），`membership_iff`（`φ ∈ Ω ↔ Ω.1 *⊢[L] φ`），`either_mem`，`equality_def`/`intro_equality`，`mem_verum`，`not_mem_falsum`，`iff_mem_neg`，`iff_mem_negneg`，`iff_mem_imp`，`iff_mem_and`，`iff_mem_or`，`mdp`，`mem_of_prove`，`mdp_provable`，`iff_forall_mem_provable`，`neg_iff`/`neg_imp`，`iff_congr`．
  - **移植しないもの**: `iff_mem_box`/`iff_mem_boxItr`/`iff_mem_dia`（Foundation では `Entailment.K` 前提の関係意味論用補題．E 系では成り立たず，`ModalNeighborhood` の実使用も無い．API 表面の 1 回ずつのヒットは `Canonicity.iff_box`/`iff_dia`＝Neighborhood 側の同名宣言との衝突），`mem_box_dual`/`mem_dia_dual`（`◇` が abbrev なので不要），`iff_mem_conj`・`intro_union_consistent`・`not_singleton_consistent`（不使用）．
- 支える命題論理補題（§2.1 の `Logic.Cl` 上）: `C_id`（`φ🡒φ`），`imp_trans!`，`verum!`，EFQ（`of_O!`: `⊥🡒φ`．`elimContra` から導出），DNI/DNE，対偶系（`contra!` 等），`K!_intro`/`K!_left`/`K!_right`（`⋏`），`A!_intro_left`/`A!_intro_right`/`of_C!_of_C!_of_A!`（`⋎` の場合分け），`neg_mdp`，`E_intro`/`E_symm`/`E_trans`/`K!_left`・`K!_right` の `🡘` 版，`CN_of_CN_left` 系の必要分，連言の出し入れ（`Finset.conj` と要素の相互導出）．目安 30〜40 補題．`∼φ` が `φ 🡒 ⊥` の abbrev なので Foundation の `N!_iff_CO!` 系（否定↔含意⊥の変換）はすべて `rfl`/不要になる．
- `cl_prover` は移植しない．使用2箇所（`proofset.iff_subset` の両方向）は「`⊢ φ 🡘 ψ` から `⊢ φ 🡒 ψ`」「`⊢ φ🡒ψ` と `⊢ ψ🡒φ` から `⊢ φ 🡘 ψ`」で，それぞれ `K!_left`/`K!_right`・`K!_intro` の1行に置換できる．MCS 内部の `cl_prover` 使用（Foundation 版 `not_singleton_consistent` 等）は当該補題ごと移植対象外．
- **採らなかった選択肢**: (i) `cl_prover` 相当のタクティク自作（決定手続き）— 使用箇所が2箇所では割に合わない．(ii) 命題論理部分の完全性を経由して「トートロジーは可証」を一般定理にする — それ自体が別プロジェクト規模．(iii) Foundation の `Context`/`FiniteContext` 構造体（`Entailment` インスタンス化して MCS 補題を型クラス機構に乗せる方式）の踏襲 — `Logic` 特化では構造体を挟む意味がなく，素の `∃ Γ` 定義の方が `obtain` で直接扱えて証明が短い．

### 2.4 28論理の定義と包含関係（検討事項4）

**結論: `Hilbert.WithRE` を `Hilbert` として実質そのまま移植する．`Axiom.HasX` クラス方式も維持する．**

- `Axiom := Set Formula`．`inductive Hilbert (Ax : Axiom) : Formula → Prop` を Foundation と同じ6構成子（`axm`（代入込み）/`mdp`/`re`/`implyK`/`implyS`/`ec`）で定義し，`Hilbert Ax : Logic` として使う（`Set` は `Formula → Prop` なのでそのまま）．
  - 命題論理基底を Łukasiewicz 3公理＋MP のまま維持する理由: 既存の健全性証明（`Hilbert.lean` の `rec!` 帰納）と各 `Satisfies.implyK/implyS/elimContra` simp 補題がこの3公理向けに書かれており，変更すると意味論側の場合分けも書き直しになる．代替案（EFQ・DNE 等を独立公理に加えて命題論理補題の導出を楽にする）は，導出の手間を減らす一方で soundness の場合数を増やすだけなので採らない．
- インスタンス群: `(Hilbert Ax).Cl`（構成子から即），`(Hilbert Ax).HasRE`，`(Hilbert Ax).Substitution`（導出帰納），`Hilbert.rec!`（可証性への帰納原理），`axm!`/`axm'!`．
- `weakerThan_of_provable_axioms (hs : Hilbert Ax₂ ⊢* Ax₁) : Hilbert Ax₁ ⪯ Hilbert Ax₂` と `weakerThan_of_subset_axioms`．`⊢*`（集合の全要素可証）は `∀ φ ∈ T, L ⊢ φ` の略記として `Logic` 側に定義．
- `Axiom.HasM/HasC/HasN/HasK/HasT/HasD/HasP/HasB/HasFour/HasFive`（＋将来用に `HasGeach g`）: Foundation の定義（証拠原子 `p`・`q` と所属証明を持つクラス）を α=ℕ 特化で移植し，`instHasAxiomM : [Ax.HasM] → (Hilbert Ax).HasAxiomM` 等の代入トリック instance も移植する．この方式は「公理図式の任意インスタンスが `axm`＋代入で得られる」ことの標準的な仕組みで，28論理すべてのバンドルインスタンスがここから出るため，設計変更の利益がない．
- 28論理: `Modal.E := Hilbert ∅`，`Modal.EM`，… `Modal.ET5` まで，`WithRE/Basic.lean` の該当節（196行目以降）をほぼ逐語移植（`Modal.EMK ≊ Modal.EMCK`・`Modal.ETB ≊ Modal.ENTB` の同値証明含む）．名前空間も `LO.Modal` を維持し，`Modal.E` 等の参照名を変えない．
- **採らなかった選択肢**: 28論理を Hilbert 表示でなくフレームクラス側から定義する（`FrameClass.logic`）— 健全性・完全性の主張自体が Hilbert 表示との一致を言う定理なので本末転倒．また各論理を個別の `inductive` にする案は `weakerThan_of_subset_axioms` の一般証明が失われるため却下．

### 2.5 `Sound`・`Complete`・`⊧` の意味論インタフェース（検討事項5）

**結論: `Semantics M F` 型クラス方式は縮小コピーして維持する．`Tarski` 系クラスは `Semantics.Top`/`Bot` のみ残し，他は落とす．**

- `⊧` は現在，世界（`x : M.World`）・モデル・フレーム・フレームクラスの4キャリアで多重定義されており，41ファイル全体がこの記法多重化に依存している．これを個別の `def`＋個別記法に分解すると全ファイルの書き換えが発生するため，型クラス `Semantics M F`（`Models : M → F → Prop`，`⊧`/`⊭`/`⊧*`，`set_models_iff` 相当）を **F = Formula 固定**で1ファイルに縮小移植するのが最小コスト．F も抽象のまま残すか迷うが，`outParam` 周りの挙動を Foundation と揃えるため `class Semantics (M : Type*)` で `Formula` 固定とする（キャリア側だけ多相）．
- `Sound L 𝓜`・`Complete L 𝓜` は `L : Logic` と `𝓜 : M` に対するクラスとして定義（`sound : L ⊢ φ → 𝓜 ⊧ φ` 等）．`Sound.not_provable_of_countermodel`（40回使用）と `Complete.complete` を同名提供．`consistent_of_meaningful` 系は使われていないため，`Hilbert.Neighborhood.consistent_of_sound_frameclass` が必要とする形（`⊥` の反例モデルの存在から `L.Consistent`）を直接証明する補題1本で置き換える．
- `Semantics.Tarski`（Top/Bot/And/Or/Imp/Not の6クラス束）: `Basic.lean` の `Satisfies` が `Semantics.Tarski (M.World)` インスタンスを宣言しているが，このインスタンス経由で使っているのは実質 `models_iff`（`🡘` の展開）と `Top`/`Bot` 程度．移植コストは小さいので **Tarski 束も同名でそのまま縮小移植**し，`Basic.lean` の該当インスタンス宣言を無傷で通す（`models_list_conj` 等のリスト連言補題は不使用なら落とす）．

---

## 3. 移植後のファイル構成案

新設モジュール（すべて Mathlib のみ import; 名前空間は既存コードとの互換のため `LO`／`LO.Modal` を維持）:

```
ModalNeighborhood/
  Vorspiel.lean                 -- Set.Fin1/Fin2.all_cases ほか集合小補題（doubleton_subset,
                                --  subset_mem_chain_of_finite）．Mathlib に既存なら再エクスポートせず削る
  Formula/Basic.lean            -- Formula（atom ℕ / ⊥ / 🡒 / □），派生 abbrev（∼ ⋏ ⋎ ⊤ 🡘 ◇），
                                --  記法，DecidableEq，multibox/multidia（□^[n], ◇^[n]），
                                --  Substitution・subst（φ⟦s⟧）・comp
  Formula/Subformulas.lean      -- subformulas，subset_of_mem，mem_* grind 補題，
                                --  FormulaSet.IsSubformulaClosed（filtration 互換 API）
  Axioms.lean                   -- Axioms.ImplyK/ImplyS/ElimContra，K M C N T B D P Four Five，
                                --  Geach.Taple・Geach
  Logic/Basic.lean              -- Logic := Set Formula，⊢/⊬/⊢*，Logic.Substitution，
                                --  Logic.Consistent，⪯/⪱/≊/Incomparable と基本補題
  Logic/Calculus.lean           -- 閉包クラス: ModusPonens/HasImplyK/HasImplyS/HasElimContra/Cl，
                                --  HasRE，HasAxiomM/C/N/K/T/B/D/P/Four/Five/Geach と accessor
                                --  （axiomM! 等，@[simp]），IsE〜IsET5 バンドルと継承 instance，
                                --  re!/rm!/multire!
  Logic/Cl.lean                 -- 命題論理ツールキット（C_id, imp_trans!, EFQ, DNI/DNE, 対偶,
                                --  K!_*/A!_*/E_* 系，Finset.conj とその補題，30〜40本）
  Logic/Context.lean            -- T *⊢[L] φ（有限連言含意），演繹補題，FormulaSet.Consistent と
                                --  その特徴付け・insert 系補題
  Logic/MaximalConsistentSet.lean -- lindenbaum（Zorn），MaximalConsistentSet と所属補題群
  Hilbert/Basic.lean            -- Axiom := Set Formula，Axiom.Has* クラス，inductive Hilbert，
                                --  rec!/axm!，Cl/HasRE/Substitution instance，instHasAxiom*，
                                --  weakerThan_of_{subset,provable}_axioms
  Hilbert/Logics.lean           -- 28論理の定義（Modal.E … Modal.ET5）とバンドル instance，
                                --  EMK≊EMCK・ETB≊ENTB
  Semantics/Interface.lean      -- Semantics クラス，⊧/⊭/⊧*，Semantics.Top/Bot/…/Tarski，
                                --  Sound/Complete，not_provable_of_countermodel
```

import グラフ（→ は「が import される」向き，下流ほど後段）:

```
Vorspiel ─┬─→ Formula/Basic ─┬─→ Formula/Subformulas
          │                  ├─→ Axioms ─→ Logic/Basic ─→ Logic/Calculus ─→ Logic/Cl
          │                  │                                   │              │
          │                  │                                   │              ↓
          │                  │                                   │        Logic/Context
          │                  │                                   │              ↓
          │                  │                                   │   Logic/MaximalConsistentSet
          │                  │                                   ↓
          │                  │                          Hilbert/Basic ─→ Hilbert/Logics
          │                  └────────→ Semantics/Interface（Logic/Basic にも依存）
```

既存41ファイル側の接続（import の付け替え先）:

- `Semantics/Basic.lean` ← `Logic/Basic`＋`Semantics/Interface`（現在は `Foundation.Modal.Logic.Basic`）
- `Semantics/Hilbert.lean` ← `Hilbert/Basic`＋`Hilbert/Logics`（現在は `Foundation.Modal.Hilbert.WithRE.Basic`）
- `Semantics/Completeness.lean` ← `Logic/MaximalConsistentSet`＋`Logic/Calculus`
- `Semantics/AxiomGeach.lean`・`AxiomN.lean` ← `Logic/Calculus`（Geach/EN 系クラス）
- `Logic/EM.lean`・`EP.lean`・`ECN.lean`・`ENT4.lean` ← `Vorspiel`（`Set.Fin2.all_cases`）
- `Logic/EN.lean` の `Foundation.Modal.PLoN.Logic.N` import は**削除**（死んだ import）

---

## 4. ステップ分割

方針: 「骨組み（statement＋`sorry`）を先に置き，中身を後で埋める」．Phase 1 の各ファイルはまず骨組みステップで全宣言を確定させ（これにより Phase 1 内の並列化と Phase 2 の着手前倒しが可能になる），肉付けステップを並列に走らせる．難易度は ★（機械的）〜★★★（証明の設計が要る）．

### Phase 0: 準備

| # | ステップ | 内容 | 依存 | 難易度 |
|---|---|---|---|---|
| S0 | Vorspiel | `Set.Fin1/Fin2.all_cases`・`eq_powerset`・付随 simp 補題（Foundation `Vorspiel/Set/Fin` 87行の必要部分），`Set.doubleton_subset`，`Set.subset_mem_chain_of_finite`（Mathlib に相当補題があれば移植せず使う）を `ModalNeighborhood/Vorspiel.lean` に | なし | ★ |

### Phase 1: 新コアの構築

| # | ステップ | 内容 | 依存 | 難易度 |
|---|---|---|---|---|
| S1 | Formula 骨組み＋定義 | `Formula`・記法・派生 abbrev・`DecidableEq`・`multibox`/`multidia`＋反復展開 simp 補題・`Substitution`/`subst`/`comp`・`inj_*` 補題．ほぼ定義のみなので骨組みと肉付けを分けない | なし | ★★ |
| S2 | Axioms | 公理図式の abbrev 群（`ImplyK`〜`Geach`）．`Formula` 直上 | S1 | ★ |
| S3 | Subformulas | `subformulas` と grind 補題群，`IsSubformulaClosed`．Foundation 709行中の該当節（約130行）の写経＋`ℕ` 特化 | S1 | ★★ |
| S4 | Logic/Basic | `Logic`・`⊢`・`⊢*`・`Substitution`・`Consistent`・`⪯`/`⪱`/`≊`/`Incomparable` の定義と基本補題（`weakerThan_iff`・`not_weakerThan_iff`・`strictlyWeakerThan_iff`・`Equiv.antisymm_iff`・`Incomparable.of_unprovable`・`StrictlyWeakerThan.of_unprovable_provable`・`Consistent.of_unprovable`・`iff_provable`/`iff_unprovable` grind 補題） | S1, S2 | ★★ |
| S5 | Logic/Calculus 骨組み | 閉包クラス全部と accessor 補題（`axiomM!` 等）・バンドル `IsE`〜`IsET5`・継承 instance・`re!`/`rm!`/`multire!` の **statement**．`rm!` の導出等は `sorry` | S4 | ★ |
| S6 | Cl ツールキット骨組み | `Finset.conj` 定義＋約30〜40本の命題論理補題の statement（`sorry`）．Foundation の該当補題の使用箇所から逆算したリストを固定する | S5 | ★ |
| S7 | Cl ツールキット肉付け(基礎) | `C_id`・`imp_trans!`・`imply_left/right` 系・EFQ・DNI/DNE・対偶（Łukasiewicz 基底からの古典的導出） | S6 | ★★★ |
| S8 | Cl ツールキット肉付け(結合子) | `K!_*`（⋏）・`A!_*`（⋎）・`E_*`（🡘）・`neg_mdp`・`of_C!_of_C!_of_A!`・`Finset.conj` 出し入れ補題 | S7 | ★★ |
| S9 | Context 骨組み | `*⊢[L]`・`FormulaSet.Consistent`・演繹系補題（`def_consistent`・insert 系・`either_consistent` 等）の statement | S6 | ★ |
| S10 | Context 肉付け | S9 の証明（演繹定理相当を Cl 補題で；Foundation `MaximalConsistentSet.lean` 前半の翻訳） | S8, S9 | ★★★ |
| S11 | MCS 骨組み | `lindenbaum`・`MaximalConsistentSet`・所属補題群（§2.3 のリスト）の statement | S9 | ★ |
| S12 | Lindenbaum 肉付け | Zorn（`zorn_subset_nonempty`）＋鎖の有限性補題で `exists_consistent_maximal_of_consistent`→`lindenbaum` | S10, S11, S0 | ★★★ |
| S13 | MCS 所属補題肉付け | `membership_iff`〜`iff_forall_mem_provable`・`mem_of_prove`・`mdp_provable` 等（Foundation 該当節の翻訳） | S10, S11 | ★★ |
| S14 | Calculus 肉付け | S5 の `sorry`（`rm!` の M＋RE からの導出，`multire!` の帰納，Geach instance `HasAxiomT → HasAxiomGeach ⟨0,0,1,0⟩` 等） | S8 | ★★ |
| S15 | Hilbert 骨組み＋定義 | `Axiom`・`Axiom.Has*`・`inductive Hilbert`・`axm!`/`axm'!`・`rec!`・`Cl`/`HasRE`/`Substitution` instance の定義（`rec!`・`Substitution` の帰納証明含む） | S4, S5 | ★★ |
| S16 | Hilbert 公理 instance | `instHasAxiomM` 等の代入トリック instance 群と `weakerThan_of_{subset,provable}_axioms` | S15 | ★★ |
| S17 | Logics（28論理） | `Modal.E`〜`Modal.ET5` の定義・`Has*` instance・バンドル instance・`EMK≊EMCK`/`ETB≊ENTB`（`WithRE/Basic.lean` 196行目以降の逐語移植） | S16 | ★ |
| S18 | Semantics/Interface | `Semantics` クラス・`⊧`/`⊭`/`⊧*`・`Top`/`Bot`/`Tarski`・`Sound`/`Complete`・`not_provable_of_countermodel`・`set_models_iff`・consistent 導出補題 | S4 | ★★ |

S1〜S18 の並列性: S1→{S2,S3} 後，{S4→S5→S6} を通せば {S7 系列}・{S9/S11 骨組み}・{S15〜S17}・{S18} の4系列が並列に走る．骨組みステップ（S5・S6・S9・S11）を先行させることで Phase 2 の機械的移行も早期に着手できる．

### Phase 2: 既存41ファイルの切替（bottom-up・原子的）

切替は import DAG の根から行う．**1つのモジュールが Foundation の `LO.Modal.Formula` と新コアの `LO.Modal.Formula` を同時に見ると名前衝突する**ため，切替済みファイルだけを import する状態を保って1ファイルずつ進める（幸い41ファイルは `Semantics/Basic`・`Hilbert`・`Completeness` を根とする DAG なので，根3ファイルを切り替えれば残りはファイル単位で並列化できる）．

| # | ステップ | 内容 | 依存 | 難易度 |
|---|---|---|---|---|
| S19 | Semantics/Basic 切替 | import 差し替え・`Formula ℕ`→`Formula`・`Logic ℕ`→`Logic`．証明本文はほぼ無傷の想定 | S17, S18 | ★★ |
| S20 | Semantics/Hilbert 切替 | `Hilbert.WithRE`→`Hilbert`，`rec!` 帰納の健全性2本＋`consistent_of_sound_frameclass` | S19 | ★★ |
| S21 | Completeness 切替 | `variable {𝓢 : S} [Entailment.Cl 𝓢]`→`{L : Logic} [L.Cl]` 等の機械置換，`cl_prover` 2箇所を `K!_left`/`K!_intro` に置換，`proofset`/`Canonicity`/`basicCanonicity`/`relativeBasicCanonicity` の本体は温存 | S13, S19 | ★★★ |
| S22 | AxiomGeach 切替 | フレーム条件節（前半）は S19 のみ依存で機械的，Canonicity 節（後半）は S21 依存．`Entailment.HasAxiomGeach g 𝓢`→`L.HasAxiomGeach g` | S21 | ★★ |
| S23 | 小公理ファイル切替 | `AxiomM`/`AxiomC`/`AxiomK`/`AxiomN`/`AxiomP`（各37〜84行）を各1エージェントで並列切替 | S21（AxiomN/C），S19（M/K/P） | ★ |
| S24 | Supplementation・IntersectionClosure 切替 | 2ファイル並列 | S22, S23 | ★ |
| S25a〜g | Logic/*.lean 切替（28ファイル） | ファイル単位で並列．おおよそ (a) `E` (b) `EM`/`EC`/`EN`(PLoN import 削除)/`ECN`/`EMN`/`EMC`/`EMCN` (c) `ET`/`EMT`/`ED`/`EP`/`EB`/`ETB` (d) `E4`/`EN4`/`ET4`/`ENT4`/`END`/`END4` (e) `EMT4`/`EMC4`/`EMCN4`/`EMNT4` (f) `E5`/`ET5`/`EK`/`EMK` (g) `Incomparability/ED_EP` の7グループ・ファイル単位でさらに分割可 | S24（実質は各ファイルの import 先） | ★〜★★ |
| S26 | 総仕上げ | `ModalNeighborhood.lean`（all-import）更新，`grep -rn "Foundation" ModalNeighborhood/` が空であることの確認，`just mk-all`→`just shake`→`lake build`，`Logic/E.lean` の重複 instance（`Modal.E ⪱ Modal.EM`・`⪱ EC`・`⪱ EN` が2回ずつ宣言されている）の整理 | S25 | ★ |

合計 27 ステップ（S25 をファイル単位に割れば 50 超まで細分化可能）．

---

## 5. 既存41ファイルの移行計画

### 5.1 機械的置換で済む部分（全体の約8割）

以下は sed 的置換＋import 差し替えのみ．

- `public import Foundation.…` → 対応する `public import ModalNeighborhood.…`．
- `Formula ℕ` → `Formula`，`Logic ℕ` → `Logic`，`Axiom ℕ` → `Axiom`．
- `variable {S} [Entailment S (Formula ℕ)] {𝓢 : S}` → `variable {L : Logic}`，および `𝓢` → `L`（`Completeness.lean`・`AxiomGeach.lean`・`AxiomN.lean`・`AxiomC.lean`・`ET5.lean`・`ETB.lean` 等の完全性節）．
- クラス名: `Entailment.E 𝓢` → `L.IsE`，`Entailment.EM` → `L.IsEM`，…，`Entailment.HasAxiomT 𝓢` → `L.HasAxiomT`，`Entailment.Cl` → `L.Cl`，`Entailment.Consistent 𝓢` → `L.Consistent`，`Entailment.Incomparable` → `Logic.Incomparable`（または同名を `LO.Entailment` 名前空間ごと維持して置換ゼロにする．実装時にどちらかへ統一）．
- `Hilbert.WithRE` → `Hilbert`（`Hilbert.WithRE.weakerThan_of_subset_axioms` → `Hilbert.weakerThan_of_subset_axioms` 等）．
- `open LO.Entailment LO.Modal.Entailment` 等の open 行の整理．
- 補題名（`axiomT!`・`re!`・`rm!`・`mem_of_prove`・`mdp_provable`・`not_provable_of_countermodel`・`weakerThan_of_subset_axioms`・`lindenbaum`・`iff_mem_neg` …）は新コアで同名提供するため**証明本文は原則無傷**．

### 5.2 証明の手直しが必要な部分

- `Completeness.lean` の `cl_prover` 2箇所（`proofset.iff_subset`）: 明示の `K!_left`/`K!_right`/`K!_intro` に書き換え（各1〜2行）．
- `Completeness.lean` 冒頭の `omit [DecidableEq α] …` 群: α を ℕ に固定するため `DecidableEq` 仮定ごと消滅．`omit` 行を削除して整える．
- `Hilbert.lean` の `soundness` 2本: `rec!` のシグネチャを新 `Hilbert` に合わせる（構成子は同一なので case 名調整程度）．
- `simp`/`grind` で暗黙に閉じている箇所（例: `Logic/*.lean` の `. simp;` が `axiomM!` 等の `@[simp]` に依存）: 属性を Foundation と同配置にすることで原則回避するが，`simp` 集合の微差で数箇所は個別修正が要る想定．切替ステップの担当エージェントが都度対応する．
- `EN.lean`: PLoN import 削除（本文影響なし）．
- `EN4.lean` の `IsSubformulaClosed` instance と，コメントアウトされた filtration 依存節: instance は S3 の API で通す．コメント部は**触らない**（filtration worktree の担当範囲）．

### 5.3 移行時の検証

- 各切替ステップは対象ファイルの `lake build`（モジュール指定）を通してからコミット．
- S26 で `grep -rn "import Foundation" ModalNeighborhood/` が空・全体 `lake build`・`just mk-all`/`just shake` を確認．
- `AxiomGeach.lean` 316行のコメント内 `sorry` は元からのもの（コメントアウトされた `isSymmetric`）であり，本作業では現状維持．

---

## 6. リスクと難所

1. **Łukasiewicz 基底からの命題論理補題導出（S7）**．`elimContra` ベースで EFQ・DNE・選言除去を組み立てる部分は Hilbert 流の古典的パズルで，最も手戻りが出やすい．
   - 代替案: どうしても難航する補題は，演繹定理（S10 の含意版は S7 の一部補題に依存しない形で先に作れる）を先に確立して文脈内推論に落とす．さらに最後の手段として `Hilbert` の命題論理公理を（同値な範囲で）増強する選択肢もあるが，soundness 側の場合分けが増えるため原則封印．
2. **Lindenbaum（S12）**．Zorn の適用と「鎖の合併の有限部分集合はどこかの要素に入る」補題．Mathlib に直接対応物（`Set.subset_mem_chain_of_finite` 相当）が無い場合は Vorspiel から移植（80行程度，自己完結）．リスクは低いが依存確認を最初に行うこと．
3. **属性互換の破れ**．§1.3 の通り，既存証明は Foundation 側の `@[simp]`/`@[grind]` 配置に暗黙依存している．新コアで属性を落とすと Phase 2 で「なぜか simp が閉じない」が多発する．**対策**: S5/S6/S13/S17 の骨組み段階で，Foundation の対応宣言の属性を機械的に転記することを作業指示に明記する．
4. **名前空間の二重化（移行期間中の衝突）**．新コアは `LO.Modal` を再利用するため，Foundation と新コアを同一モジュールから同時 import すると `Formula` 等が曖昧になる．**対策**: Phase 2 を DAG の根から原子的に行い，「切替済みファイルは切替済みファイルのみ import する」を不変条件にする．worktree 並列化する場合も，S19〜S21（根3ファイル）だけは直列またはひとつの worktree で先に済ませる．
5. **`Canonicity` の一般性の検証**．`{𝓢} [Entailment.E 𝓢]` → `{L : Logic} [L.IsE]` の置換は形式上機械的だが，`MaximalConsistentSet 𝓢` の subtype が `L` の `Set` レベル等式（`Modal.E = Hilbert ∅` が abbrev である等）に敏感な可能性がある．Foundation でも `Logic α` に対して同じ構図で動いているため原理的問題はないが，S21 は最初に `basicCanonicity Modal.E` の1インスタンスで通し確認をしてから全体へ進める．
6. **`Formula` の ℕ 固定の副作用**．万一 filtration や将来の拡張で別の原子型（有限原子など）が必要になった場合は generalize が要る．現時点の全コード（filtration の下書き含む）は ℕ のみなので受容する．戻す判断をした場合も `variable {α}` を足すだけで大半の証明は影響を受けない構成（`DecidableEq ℕ` を暗黙に使う箇所を `decide` 依存にしない）を心がける．
7. **filtration worktree との競合**．本作業と nbhd-filtration worktree が `Semantics/Logic/E4.lean` 等の同じファイルに触る可能性がある．**対策**: 新コアの `subformulas`/`IsSubformulaClosed` API 名を Foundation と一致させる（S3）ことで filtration 側の差分を import 行のみに抑え，マージ順序（本作業→filtration の rebase）を統合時に調整する．
8. **28ファイルの切替のばらつき**．`Logic/*.lean` は大半が反例モデルの有限計算（`simp!`・`grind`・`tauto_set`・`Set.Fin2.all_cases`）で，コア API にほぼ触れないため低リスクだが，`ET5`/`ETB`/`END` 等の完全性節（canonicity のカスタム instance）を含むファイルは S21/S22 の出来に依存する．難度に応じてグループ分け（S25 の a〜g）済み．

---

## 7. 規模見積もり

| 部分 | 新規行数（目安） | 対応する Foundation 行数 |
|---|---|---|
| Vorspiel | 100 | 87＋α |
| Formula（Basic＋Subformulas＋Axioms） | 450 | 709＋500＋740＋129 |
| Logic（Basic＋Calculus＋Cl＋Context＋MCS） | 1,100 | 639＋1508＋885＋598＋… |
| Hilbert（Basic＋Logics） | 550 | 149＋520 |
| Semantics/Interface | 150 | 359＋639の一部 |
| 合計 | **約 2,350** | （推移的閉包 14,475） |

既存41ファイル側の差分は import 行と variable 行が中心で，証明本文の実質変更は `cl_prover` 置換ほか十数箇所の見込み．
