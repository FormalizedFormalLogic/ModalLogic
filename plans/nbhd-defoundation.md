# Neighborhood の脱 Foundation 化 設計文書

`Neighborhood`（41ファイル・約4200行）を，外部パッケージ `Foundation` への依存から切り離し，
Mathlib のみに依存する自己完結ライブラリにするための設計とステップ分割．

- 対象: `Neighborhood/` 配下のみ．`Fin74` は Foundation（`Foundation.Vorspiel.Set.Basic`）への依存が残るため，`lakefile.toml` の `require Foundation` 自体は当面残す．`Neighborhood` のどのモジュールも `Foundation.*` を import しない状態が完成条件．
- 本文書中の Lean 風の型表記はすべて擬似コードであり，実装時の正確な構文は実装担当が確定する．

---

## 1. 現状分析

### 1.1 依存の層構造

`Neighborhood` が Foundation から借りているものは，実ソースを精査した結果，次の6層に整理できる．

| 層 | Foundation 側モジュール | 内容 | Neighborhood での使われ方 |
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

- **`⊢!`（Type レベル証明項）と `⊢`（Prop）の2層構造**: Foundation は `Prf : S → F → Type` を持ち，各補題が `def foo : 𝓢 ⊢! …` と `lemma foo! : 𝓢 ⊢ …` の2本立て．`Neighborhood` が使うのは **`!` 付き（Prop）側のみ**（grep 確認: `re!`・`rm!`・`axiomT!`・`axiomFour!`・`axiomD!`・`axiomGeach!`・`mem_of_prove`・`mdp_provable` 程度）．
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
- 原子型を `ℕ` に固定する理由: `Neighborhood` の全使用箇所が `Formula ℕ`．固定すれば `[DecidableEq α]` の伝搬（`subformulas`・MCS 系の仮定）が全て消える．CLAUDE.md の「プロジェクトごとに証明しやすい形で個別に用意する」方針とも一致．汎用化が必要になった時点で generalize すればよい．
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
  - **移植しないもの**: `iff_mem_box`/`iff_mem_boxItr`/`iff_mem_dia`（Foundation では `Entailment.K` 前提の関係意味論用補題．E 系では成り立たず，`Neighborhood` の実使用も無い．API 表面の 1 回ずつのヒットは `Canonicity.iff_box`/`iff_dia`＝Neighborhood 側の同名宣言との衝突），`mem_box_dual`/`mem_dia_dual`（`◇` が abbrev なので不要），`iff_mem_conj`・`intro_union_consistent`・`not_singleton_consistent`（不使用）．
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
Neighborhood/
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
| S0 | Vorspiel | `Set.Fin1/Fin2.all_cases`・`eq_powerset`・付随 simp 補題（Foundation `Vorspiel/Set/Fin` 87行の必要部分），`Set.doubleton_subset`，`Set.subset_mem_chain_of_finite`（Mathlib に相当補題があれば移植せず使う）を `Neighborhood/Vorspiel.lean` に | なし | ★ |

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
| S26 | 総仕上げ | `Neighborhood.lean`（all-import）更新，`grep -rn "Foundation" Neighborhood/` が空であることの確認，`just mk-all`→`just shake`→`lake build`，`Logic/E.lean` の重複 instance（`Modal.E ⪱ Modal.EM`・`⪱ EC`・`⪱ EN` が2回ずつ宣言されている）の整理 | S25 | ★ |

合計 27 ステップ（S25 をファイル単位に割れば 50 超まで細分化可能）．

---

## 5. 既存41ファイルの移行計画

### 5.1 機械的置換で済む部分（全体の約8割）

以下は sed 的置換＋import 差し替えのみ．

- `public import Foundation.…` → 対応する `public import Neighborhood.…`．
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
- S26 で `grep -rn "import Foundation" Neighborhood/` が空・全体 `lake build`・`just mk-all`/`just shake` を確認．
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

---

## 設計改訂1（ユーザー指示による簡素化・FrameClass/Semantics/Sound/Complete 全廃）

2026-07-30 追記．上の §1〜§7 は履歴として残す（**削除・修正しない**）．本節以降が現行の設計であり，
§2.1・§2.5・§4（S4 以降のステップ分割）・§5 を置き換える．§2.2（Formula の構成）・§2.3（MCS の
方式）・§1（現状分析）は引き続き有効（ただし記法・クラス名は本節に従って読み替える）．
あわせて `plans/nbhd-kappa-parameterization.md`（port-modal-neighborhood worktree）の中心的結論
（述語版 `FrameClass`）も破棄され，本節に統合される（同文書の「設計改訂1」節を参照）．

### R1. ユーザー指示（決定事項）

1. **`Logic.Provable`／`Unprovable` を作らない**．可証性は素直に `φ ∈ L` と書く．
   **`WeakerThan` 等の比較クラスも作らず**，集合の包含（`⊆`・`⊂`・`=`）で書く．
   ProvabilityLogic（`../SeqPL`）を参考にする．
2. **`Logic/Calculus.lean` をここまで用意する必要はない**（閉包クラス群の大幅削減）．
3. **`FrameClass` という型・概念，および FrameClass による validity という概念は廃止する**．
   **`Sound`／`Complete` 型クラスも `Semantics` 型クラスも作らない**．健全性・完全性は
   ProvabilityLogic のように素の `theorem` として，フレーム条件の型クラスを instance 引数に
   置いた全称量化（`∀ {κ}, [Nonempty κ] → ∀ F : Frame κ, [F.IsX] → …`）で書く．

これは比較検討の対象ではなく決定である．以下は決定を前提とした具体設計と移行計画．

### R2. 調査結果（実測．本改訂の根拠データ）

ProvabilityLogic（`SeqPL/ProvabilityLogic/Logic/Basic.lean`・`Logic/GL/Basic.lean`・
`Hilbert/GL/Basic.lean`・`Kripke/Basic.lean`），`Fin74/Kripke/Basic.lean`，本リポジトリの
現行41ファイルと新コア（S0〜S6 のコミット済みファイル）を実際に読んで確認した．

- **ProvabilityLogic の実態**: `abbrev Logic (α) := Set (Formula α)` の1行のみ．
  `Provable`・`⊢`・`WeakerThan`・`Consistent`・閉包クラス階層・`Semantics`／`Sound`／`Complete`
  型クラスは一切無い．論理は `abbrev LogicGL : Logic α := { A | ⊢ʰ[GL] A }`，比較は素の `⊆`／`⊂`，
  健全性・完全性は `theorem soundness (h : ⊢ʰ[GL] A) : ∀ {κ}, [Nonempty κ] → ∀ M : Model κ α,
  [M.IsGL] → M ⊧ A` の形の素の定理．`⊧` は `Model.Validate` への素の `infix`，世界レベルは `⊩`．
  Hilbert 体系の命題論理基底は **Łukasiewicz 3公理ではなく
  `implyK`/`implyS`/`dne`/`andElimL`/`andElimR`/`andIntro`/`orIntroL`/`orIntroR`/`orElim` の9公理**で，
  `elimContra` は導出補題（`Hilbert/GL/Basic.lean:224`）．
- **Fin74 の記法**: `Model.Validates`・`Frame.Validates`・`Frame.ValidatesSet` をそれぞれ素の
  `def`＋同一グリフの `infix:50 " ⊧ "` で多重定義しており（`Fin74/Kripke/Basic.lean:107,123,127`），
  型クラス無しの記法多重化が実運用で成立している．世界レベルは `⊩`（`Forces _` と明示版 `⊩[M]`）．
- **既存41ファイルの実測**:
  - `⪱`: instance 宣言 42箇所＋`calc` 内 1箇所＝43．全て
    `instance : Modal.X ⪱ Modal.Y := by constructor; （⊆側は weakerThan_of_subset_axioms，
    ¬⊇側は not_weakerThan_iff.mpr＋反例）` の同型．
  - `⪱`/`≊` を**型クラス解決で暗黙に消費している箇所は正確に1箇所**:
    `Logic/EMK.lean:64–66` の `calc _ ⪱ Modal.EMCK := inferInstance; _ ≊ Modal.EMK := by symm;
    infer_instance`．他に `⪯` の明示使用は 0，`.pbl`／`weakening` の使用も 0．
  - `≊` は上記1箇所のみ．`Incomparable` は `Logic/Incomparability/ED_EP.lean` の1 instance のみ．
  - `Logic/E.lean` に `Modal.E ⪱ Modal.EM`・`⪱ EC`・`⪱ EN` の**重複宣言**（行90/161，119/190，
    146/217）．instance だから通っていたもので，theorem 化で名前衝突するため本改訂で解消必須．
  - `Entailment.Consistent`: instance 宣言28箇所（全 Logic ファイル）＋仮定としての使用が
    `Completeness`/`AxiomGeach`/`AxiomC`/`AxiomN`/`Supplementation`/`ET5` の variable 行．
  - 閉包条件の型クラス仮定: `Entailment.Cl`（Completeness の proofset 節），`Entailment.E`
    （Completeness/AxiomGeach/AxiomC/AxiomN），`Entailment.EM`（Supplementation/Completeness），
    `Entailment.ET5`（ET5.lean）．`HasAxiom{C,N,T,Four,D,Five,B,Geach}` が canonicity instance の
    仮定として多数．**バンドルが仮定として現れるのは E・EM・ET5 の3種だけ**で，他の約20バンドルは
    28論理側に instance を供給するためだけに存在している．
  - `Sound` instance 28・`Complete` instance 28（＋`finite_complete` が E4/ET4/EMCN4 等の数箇所）・
    `Sound.not_provable_of_countermodel` 40回・`FrameClass` 出現270回・`⊧` 出現93回・`⊧*` 4回・
    `simp [Semantics.Models, …]` 型の unfold 34回・`weakerThan_of_subset_axioms` 41回．
  - `Frame.logic`・`FrameClass.logic` は **`Basic.lean` の定義のみで外部使用ゼロ**（grep 確認）．
- **worktree の現状（前提の訂正）**: S0〜S4 に加えて **S5（`Logic/Calculus.lean`，197行）と
  S6（`Logic/Cl.lean`，240行の骨組み）は既にコミット済み**（コミット eff9efe・569ed7d）．
  よって本改訂はこの2ファイルの「作らない」ではなく「削り直し」を含む．
- **近傍意味論の Boolean 性**: `Model.truthset` の `eq_and`/`eq_or`/`eq_neg` は `@[simp, grind =]`
  で整備済み（`Semantics/Basic.lean:83–85`），既存の `Satisfies.implyK`/`implyS`/`elimContra` は
  いずれも `by grind` の1行（同:151–153）．命題論理公理を増やしても健全性の各ケースが1行で
  済むことの直接の証拠．

### R3. `Logic/Basic.lean` の改訂後の姿

**残すもの**（268行 → 40行程度）:

```
abbrev Logic := Set Formula

/-- `⊥` is not a theorem of `L`. -/
class Logic.Consistent (L : Logic) : Prop where
  not_mem_falsum : ⊥ ∉ L
```

- `Consistent` だけはクラスとして残す．理由: 正準モデルの構成が
  `[L.Consistent] → Nonempty (MaximalConsistentSet L)`（Lindenbaum）→ 正準フレームの
  `[Nonempty κ]` という **instance 合成の連鎖**の起点であり，AxiomGeach 等の canonicity instance
  群（`instance [L.HasAxiomT] : (basicCanonicity L).toModel.IsReflexive` の形）が仮定として
  instance-implicit で受ける必要があるため．素の Prop 引数にするとこれら十数個の instance が
  全部 instance でいられなくなる．定義は Foundation の `¬Inconsistent`（∀φ可証の否定）経由を
  やめ，`⊥ ∉ L` の1フィールドに直す（Cl の下で同値；`exists_unprovable` 等が必要なら導出）．
- 28箇所の `instance consistent : Entailment.Consistent Modal.X := …` は
  `instance : Modal.X.Consistent := …` の形をそのまま保てる（中身は R7 の
  `consistent_of_frame` に差し替え）．

**消すもの**（現行 `Logic/Basic.lean` から削除）:

- `Provable`／`Unprovable`／`⊢`／`⊬`（可証性は `φ ∈ L`，非可証性は `φ ∉ L`）．
- `ProvableSet`／`⊢*`（`L ⊢* T` は単に `T ⊆ L`）．
- `Logic.Substitution` クラス（41ファイルに使用ゼロ．Hilbert 論理の代入閉包は
  `Hilbert Ax` 上の素の補題 `Hilbert.subst_mem : φ ∈ Hilbert Ax → φ⟦s⟧ ∈ Hilbert Ax` として
  Hilbert ファイル側に置く）．
- `WeakerThan`／`⪯`・`StrictlyWeakerThan`／`⪱`・`Equiv`／`≊`・`Incomparable` と付随補題約30本
  （`weakerThan_iff`・`not_weakerThan_iff`・`strictlyWeakerThan_iff`・`Equiv.antisymm_iff`・
  `Trans` instance 9個・`∅ ⪯ L`／`L ⪯ univ` instance など全部）．
- `Inconsistent` と consistent/inconsistent の iff 補題群．
- `iff_provable`/`iff_unprovable`/`iff_provableSet`（`Iff.rfl` の grind 橋渡し．`∈` 直書きなら不要）．

### R4. 比較関係の置換（`⪱` 43・`≊` 1・`Incomparable` 3 箇所）

- **`instance : Modal.X ⪱ Modal.Y` → 名前付き `theorem`**．命名は
  `theorem Modal.X_ssubset_Y : Modal.X ⊂ Modal.Y` の形に統一する（42＋1箇所）．
  型クラス解決で暗黙に使われている箇所は R2 の通り **EMK.lean の calc 1箇所だけ**なので，
  instance → theorem 化の影響はそこへの明示適用だけで済む:

  ```
  -- 旧: instance : Modal.EM ⪱ Modal.EMK := calc
  --       _ ⪱ Modal.EMCK := inferInstance
  --       _ ≊ Modal.EMK  := by symm; infer_instance
  theorem Modal.EM_ssubset_EMK : Modal.EM ⊂ Modal.EMK := calc
    Modal.EM ⊂ Modal.EMCK := EM_ssubset_EMCK
    _        = Modal.EMK  := EMCK_eq_EMK    -- ≊ は集合の等式になる（calc は = を native に繋ぐ）
  ```

- **証明パターンの書き換え**．`Set` の `⊂` は `s ⊆ t ∧ ¬t ⊆ s`（`Set.ssubset_def`），
  `¬t ⊆ s ↔ ∃ φ ∈ t, φ ∉ s` は `Set.not_subset`．現行の2バレット構造がそのまま写る:

  ```
  -- 旧                                          -- 新
  instance : Modal.E ⪱ Modal.EM := by            theorem Modal.E_ssubset_EM : Modal.E ⊂ Modal.EM := by
    constructor;                                   constructor;
    . apply … weakerThan_of_subset_axioms; simp;   . apply Hilbert.subset_of_subset_axioms; simp;
    . apply Entailment.not_weakerThan_iff.mpr;     . apply Set.not_subset.mpr;
      use Axioms.M (.atom 0) (.atom 1);              use Axioms.M (.atom 0) (.atom 1);
      constructor;                                   constructor;
      . simp;                                        . simp;
      . apply Sound.not_provable_of_countermodel …;  . apply Modal.E.unprovable_of_countermodel …;（R7）
  ```

  witness の並び（`∃ φ, Y ⊢ φ ∧ X ⊬ φ` ↔ `∃ φ ∈ Y, φ ∉ X`）は一致しており順序調整は不要．
- **`weakerThan_of_subset_axioms`（41回）** は
  `theorem Hilbert.subset_of_subset_axioms (h : Ax₁ ⊆ Ax₂) : Hilbert Ax₁ ⊆ Hilbert Ax₂` に，
  `weakerThan_of_provable_axioms` は `(h : Ax₁ ⊆ Hilbert Ax₂) : Hilbert Ax₁ ⊆ Hilbert Ax₂` に
  改名・改型して同数の機械置換．
- **`≊`** は集合の等式に．`Modal.EMK ≊ Modal.EMCK`（Hilbert/Logics で証明する側）は
  `theorem Modal.EMK_eq_EMCK : Modal.EMK = Modal.EMCK`（`Set.Subset.antisymm` で両向き ⊆）．
- **`Incomparable`（ED_EP.lean の1 instance）** は素の2定理（または連言1本）に:
  `theorem Modal.not_ED_subset_EP : ¬Modal.ED ⊆ Modal.EP` と逆向き．中身は各バレットが
  そのまま `Set.not_subset.mpr` に乗る．
- **E.lean の重複 ⪱ 宣言 3組**は theorem 化で名前衝突するため，このタイミングで各1本に統合する
  （旧 S26 の残務を前倒し）．

### R5. `Logic/Calculus.lean` の削ぎ落とし

**結論: 閉包クラスは「`Cl`（1個のバンドル）＋`HasRE`＋`HasAxiomM/C/N/K/T/B/D/P/Four/Five/Geach`」
だけ残し，`IsE`〜`IsET5` の全バンドル（約20クラス＋継承 instance 約25個）と `HasRM` を廃止する．**

- 根拠（R2 実測）: バンドルが**仮定**として使われるのは `E`・`EM`・`ET5` の3種のみ．
  それも成分に展開すれば `[L.Cl] [L.HasRE]`（旧 E）・`＋[L.HasAxiomM]`（旧 EM）・
  `＋[L.HasAxiomT] [L.HasAxiomFive]`（旧 ET5）と書けるだけの違いで，バンドルの存在意義は
  「28論理側に instance を供給する」ことにあった．新設計ではそれは
  **`Hilbert Ax` 上の generic instance**（`(Hilbert Ax).Cl`・`(Hilbert Ax).HasRE`・
  `[Ax.HasT] → (Hilbert Ax).HasAxiomT` など計12個程度）が担うため，
  28論理×バンドルの instance 網は丸ごと不要になる．
- 残すもの: `HasRE`＋`re!`/`multire!`，`HasAxiom*` 11クラス＋accessor（`axiomT!` 等，
  `@[simp]` 配置は Foundation と同じに保つ），`axiomK'!` 等の適用形，Geach への橋渡し instance
  5個（`[L.HasAxiomT] → L.HasAxiomGeach ⟨0,0,1,0⟩` 等．AxiomGeach.lean の canonicity が消費）．
- 消すもの: `IsE`〜`IsET5` バンドル全部と継承 instance，`HasRM` クラス
  （`rm!` は `lemma rm! [L.Cl] [L.HasRE] [L.HasAxiomM] : (φ 🡒 ψ) ∈ L → (□φ 🡒 □ψ) ∈ L` の
  **導出補題**に格下げ．現行 Calculus.lean 185–191行の instance 対の中身を1本に畳む）．
  Completeness.lean の `box_subset_of_subset`（旧 `[Entailment.EM]`）はこの `rm!` を使う形に．
- 「任意の証明体系への一般性」について: `Canonicity`・`proofset`・AxiomGeach の canonicity 節の
  一般性は「任意の `L : Logic` with `[L.Cl] [L.HasRE]`」として**維持される**（§2.1 の結論と同じ．
  変数書き換えが `𝓢 → L`，`[Entailment.E 𝓢]` → `[L.Cl] [L.HasRE]` になるだけ）．
  ET5.lean の一般節（`variable [Entailment.ET5 𝓢]`）も同様に成分展開で機械置換．
- `Logic/Cl.lean` の `Cl` は，現行の `ModusPonens`/`HasImplyK`/`HasImplyS`/`HasElimContra` の
  4クラス継承をやめ，**1個のクラスに畳む**（フィールドは R6 の公理系に対応）．4クラスを
  個別に仮定する使用箇所は41ファイルに存在しない（`Entailment.Cl` のみ．grep 確認）．

### R6. 命題論理基底を SeqPL 方式（richer base）に切り替える

**結論: 切り替える．** `Hilbert` の命題論理公理を Łukasiewicz 3公理から SeqPL と同じ
`implyK`・`implyS`・`dne`・`andElimL`・`andElimR`・`andIntro`・`orIntroL`・`orIntroR`・`orElim`
の9公理に変更し，`elimContra` は導出補題にする（`ec` 構成子は置かない）．
`Logic.Cl` クラスのフィールドも `mdp`＋この9公理に揃える．

- これは §2.4 の「代替案は soundness の場合数を増やすだけなので採らない」という判断を覆す．
  覆す根拠:
  1. **soundness 側のコストが1行/ケースであることを実測で確認した**（R2 最終項）．
     `⋏`/`⋎`/`∼` は abbrev のまま（§2.2 は不変）なので，追加公理の妥当性は
     `@[simp] lemma Satisfies.dne : x ⊧ Axioms.DNE φ := by grind` の形で既存の
     `eq_and`/`eq_or`/`eq_neg` から閉じる．`ValidOnModel`/`ValidOnFrame` への持ち上げも
     各1行．`rec!` 帰納（Hilbert.lean の健全性2本）は追加6ケースが既存の
     `| implyK | implyS | … => simp` の頭に並ぶだけ．
  2. 一方 §6-1 は Łukasiewicz 基底からの導出（S7）を**本計画最大の難所（★★★）**と明記していた．
     richer base ではツールキットの `and₁!`〜`or₃!`・`dne!` が**クラスフィールドの accessor**に
     なって消滅し，残る導出（`efq!`・`dni!`・`elimContra!`・`lem!`・選言除去の文脈版）は
     SeqPL に完動の参照実装がある（`SeqPL/ProvabilityLogic/Hilbert/GL/Basic.lean` の
     `dni`/`elimContra`/`efq`/`orElim'`/`orCasesImp`．いずれも文脈演繹＋演繹定理経由で短い）．
     S7 は ★★★ → ★★ に下がる．
  3. 演繹定理（§2.3 の `Finset.conj` 版）自体も `andElimL/R`・`andIntro` が primitive になる
     ことで conj の出し入れ補題が直接書け，順序依存（S7→S10）が緩む．
- `Axioms.lean`（S2 完了分）には `DNE`・`AndElim₁`/`AndElim₂`/`AndIntro`・
  `OrIntro₁`/`OrIntro₂`/`OrElim` の abbrev を**追記**する（既存分は無変更．純追加）．
- 既存41ファイル側の影響: `Hilbert.lean` の `rec!` ケース名変更（`ec` 消滅・6ケース追加）と，
  `Semantics/Basic.lean` に持ち上げ simp 補題を足すことのみ．`Satisfies.elimContra` 等の既存
  simp 補題は残してよい（導出補題の妥当性としても正しい）．

### R7. 意味論の再設計（`Semantics`/`Sound`/`Complete`/`FrameClass` 全廃＋κ 統合）

`plans/nbhd-kappa-parameterization.md` の κ パラメータ化はこの再設計に**吸収**する
（同文書 §2.3 の述語版 FrameClass は破棄）．`Semantics/Basic.lean` は次の骨格に一度で書き直す．

```
structure Frame (κ : Type u) where          -- world_nonempty フィールドは持たない（R7-5）
  𝒩 : κ → Set (Set κ)

abbrev Frame.World {_ : Frame κ} : Type u := κ    -- Fin74 と同じ「F を抱える別名」
-- box・dia・mk_ℬ・IsFinite・simple_blackhole は κ 化するだけで実質同文

structure Model (κ : Type u) extends Frame κ where
  Val : ℕ → Set κ

def Model.truthset (M : Model κ) : Formula → Set M.World   -- eq_and 等の simp 群は同文
def Satisfies (M : Model κ) (x : M.World) (φ : Formula) : Prop := x ∈ M φ
infix:50 " ⊧ " => Satisfies _                     -- Fin74 の `Forces _` トリック（世界レベル）
notation:80 x " ⊧[" M "] " φ => Satisfies M x φ   -- 推論が詰まる箇所用の明示版

def Model.Validates (M : Model κ) (φ : Formula) : Prop := ∀ x : M.World, x ⊧ φ
infix:50 " ⊧ " => Model.Validates
def Frame.Validates (F : Frame κ) [Nonempty κ] (φ : Formula) : Prop := ∀ V, (⟨F, V⟩ : Model κ) ⊧ φ
infix:50 " ⊧ " => Frame.Validates
def Frame.ValidatesSet (F : Frame κ) [Nonempty κ] (T : Set Formula) : Prop := ∀ φ ∈ T, F ⊧ φ
infix:50 " ⊧ " => Frame.ValidatesSet              -- 旧 `F ⊧* Ax`／`C ⊧* Ax` の代替
```

1. **`⊧` の与え方**: `Semantics` 型クラスを使わず，Fin74 実証済みの
   「キャリアごとの素の `def`＋同一グリフの `infix` 多重定義」を採る（3キャリア＋公理集合版）．
   既存93箇所の `⊧` はグリフ・位置とも不変で，`simp [Semantics.Models, Satisfies]`（34箇所）が
   `simp [Satisfies]` 等に**短くなる**．`Semantics.Tarski`/`Top`/`Bot` instance は削除し，
   その内容は既に素の補題として存在する `def_top`/`def_bot`/`ValidOnModel` 系に引き継がれて
   いる（実質削除のみ）．旧 `ValidOnModel`/`ValidOnFrame` の名は `Model.Validates`/
   `Frame.Validates` に改名（Fin74 に揃える．既存の `ValidOnFrame.re` 等の補題名は
   `Frame.Validates.re` 等に機械追随）．
2. **`FrameClass` 廃止**: `FrameClass`・`FrameClass.X`（通常＋finite で約56 abbrev）・
   `C ⊧ φ`・`iff_not_validOnFrameClass_exists_frame`／`…_exists_model_world`・
   `Frame.logic`／`FrameClass.logic`（外部使用ゼロ）を全て削除する．
   フレームの「クラス」は既存の条件型クラス **`Frame.IsX`／`Frame.IsFiniteX` だけで表す**
   （これらは現行コードに全て揃っており，そのまま κ 化して使う．`FrameClass.X` は元々
   `{ F | F.IsX }` の薄いラッパだった）．「クラスに属する全フレームで妥当」は
   `∀ {κ : Type}, [Nonempty κ] → ∀ F : Frame κ, [F.IsX] → F ⊧ φ` の全称量化で書く．
3. **28論理の健全性・完全性・無矛盾性の新しい形**（各 Logic ファイル）:

   ```
   -- 旧: instance Neighborhood.sound : Sound Modal.E4 FrameClass.E4 := …
   lemma Modal.E4.validates_axioms [Nonempty κ] {F : Frame κ} [F.IsE4] : F ⊧ E4.axioms
     -- 中身は旧 sound instance の `rintro _ (rfl | rfl) … <;> simp` がそのまま移る
   theorem Modal.E4.soundness [Nonempty κ] {F : Frame κ} [F.IsE4] (h : φ ∈ Modal.E4) : F ⊧ φ :=
     Hilbert.soundness validates_axioms h
   theorem Modal.E4.unprovable_of_countermodel [Nonempty κ] {F : Frame κ} [F.IsE4]
       (h : ¬F ⊧ φ) : φ ∉ Modal.E4          -- soundness の対偶．旧 not_provable_of_countermodel の代替
   -- 旧: instance Neighborhood.complete : Complete Modal.E4 FrameClass.E4 := …
   theorem Modal.E4.completeness
       (h : ∀ {κ : Type}, [Nonempty κ] → ∀ F : Frame κ, [F.IsE4] → F ⊧ φ) : φ ∈ Modal.E4
     -- 中身: by_contra → (basicCanonicity Modal.E4).exists_countermodel → 正準フレームの
     --       IsE4 instance（既存の canonicity instance 群）で h を正準フレームに適用して矛盾
   -- 旧: instance Neighborhood.finite_complete : Complete Modal.E4 FrameClass.finite_E4
   theorem Modal.E4.finite_completeness
       (h : ∀ {κ : Type}, [Nonempty κ] → ∀ F : Frame κ, [F.IsFiniteE4] → F ⊧ φ) : φ ∈ Modal.E4
   -- 旧: instance consistent : Entailment.Consistent Modal.E4 := consistent_of_sound_frameclass …
   instance : Modal.E4.Consistent := Hilbert.consistent_of_frame Frame.simple_blackhole (by …)
   ```

   completeness の全称は，正準フレーム（世界型 `MaximalConsistentSet L : Type 0`）に
   instantiate するため **κ を `Type 0` で量化**する（soundness 側は universe 多相でよい．
   κ 計画 §3 の分析はこの形にそのまま引き継がれる）．
4. **generic 側（`Semantics/Hilbert.lean`・`Completeness.lean`）の新しい形**:

   ```
   theorem Hilbert.soundness [Nonempty κ] {F : Frame κ} (hAx : F ⊧ Ax) (h : φ ∈ Hilbert Ax) : F ⊧ φ
     -- 旧 soundness_of_axioms_validOnFrame と同文（rec! 帰納．R6 でケースが増える）．
     -- 旧 soundness_of_validates_axioms（FrameClass 版）は不要になり削除
   theorem Hilbert.unprovable_of_countermodel [Nonempty κ] {F : Frame κ}
       (hAx : F ⊧ Ax) (h : ¬F ⊧ φ) : φ ∉ Hilbert Ax
   theorem Hilbert.consistent_of_frame [Nonempty κ] (F : Frame κ) (hAx : F ⊧ Ax) :
       (Hilbert Ax).Consistent
     -- 旧 consistent_of_sound_frameclass の代替．C.Nonempty 引数は消滅する:
     -- 旧呼び出しが nonemptiness の証人として渡していた具体フレームを，そのまま第1引数に渡す．
     -- 中身は F ⊭ ⊥（世界の非空性から）＋soundness の対偶で ⊥ ∉ Hilbert Ax
   theorem Canonicity.exists_countermodel [L.Cl] [L.HasRE] [L.Consistent] {𝓒 : Canonicity L}
       (hφ : φ ∉ L) : ∃ Γ : 𝓒.toModel.World, ¬Γ ⊧ φ
     -- 旧 Canonicity.completeness（Complete instance を返す形）の置き換え．
     -- lindenbaum＋truthlemma の中身は同文．各論理の completeness はこれを消費する3行程度の定理
   ```

5. **`Nonempty` の扱い**: `Frame` の `[world_nonempty : Nonempty World]` フィールドは**廃止**し，
   ProvabilityLogic と同じく **`[Nonempty κ]` の instance 引数**にする（κ 計画 §1.2 の
   「フィールドとして残せる」判断を覆す．FrameClass という「フレームの入れ物」が消えた以上，
   非空性を値に同梱する理由が無く，全ての定理は κ がスコープにあるので binder で受けられる）．
   非空性の実消費者は `Frame.Validates`／`Model.nonempty_univ_world`／`consistent_of_frame`／
   filtration の商，および正準モデル（`[L.Consistent] → Nonempty (MaximalConsistentSet L)` の
   instance を新設して合成）で，いずれも `[Nonempty κ]` で賄える．
6. **40箇所の反例パターンの書き換え**（代表例，`Logic/E.lean` の `E ⪱ EM` 相当）:

   ```
   -- 旧                                              -- 新
   apply Sound.not_provable_of_countermodel           apply Modal.E.unprovable_of_countermodel
     (𝓜 := FrameClass.E);                               (F := M.toFrame);   -- [F.IsE] は instance で自動
   apply not_validOnFrameClass_of_exists_model_world;  -- （行ごと消滅）
   let M : Model := { World := Fin 3, 𝒩 := …, Val := … };  let M : Model (Fin 3) := { 𝒩 := …, Val := … };
   use M, 0;                                           apply Model.not_validates_of_world (x := 0)  -- 相当
   constructor;                                        -- membership バレット（`. tauto;`）は
   . tauto;   -- M.toFrame ∈ FrameClass.E              --   instance 解決に置き換わり消滅
   . simp […]; grind;                                  simp […]; grind;   -- 反例計算の本体は無傷
   ```

   フレームクラス membership の証明（`tauto`／`Set.mem_setOf_eq`／`infer_instance`，
   κ 計画実測98箇所）は `[F.IsX]` の instance 解決に吸収されて**大半が行削除**になる．
   `not_validOnFrameClass_of_exists_frame` 経由の箇所（フレームレベル反例）は
   `unprovable_of_countermodel` に `¬F ⊧ φ` を直接渡す形になり，既存の
   `iff_not_exists_valuation_world`（フレームレベル，クラス非依存）はそのまま生き残る．
7. **`Frame.IsFinite`・`IsFiniteX` はそのまま活用できる**（`Finite F.World` は `Finite κ` に
   落ちるだけ）．有限モデル性は上記 `finite_completeness` の形（仮定側の条件クラスを
   `IsFiniteX` にした全称量化）で書く．filtration 復活時の 8論理の `finite_complete` も同形．

### R8. S0〜S6（コミット済み）への遡及影響

| ステップ | ファイル | 影響 |
|---|---|---|
| S0 | `Vorspiel.lean` | **無傷**（集合小補題のみ） |
| S1 | `Formula/Basic.lean` | **無傷**（Logic に依存しない） |
| S2 | `Axioms.lean` | **純追加**（R6 の命題論理スキーム7個を追記） |
| S3 | `Formula/Subformulas.lean` | **無傷** |
| S4 | `Logic/Basic.lean` | **書き直し**（268行 → 約40行，R3） |
| S5 | `Logic/Calculus.lean` | **削り直し**（197行 → 約100行．バンドル約90行と `HasRM` を削除，`rm!` を導出補題化．R5） |
| S6 | `Logic/Cl.lean` | **改訂**（`Cl` を1クラスに畳み，フィールドを9公理に変更．sorry のままの約40 statement のうち `and₁!`〜`or₃!`・`dne!` 等 約10本が accessor になり sorry が消える．残りは SeqPL 参照実装に沿って埋める．R6） |

S1〜S3 が無傷であることは import 構造（`Formula`・`Subformulas`・`Vorspiel` は `Logic` 系を
import しない）で確認済み．

### R9. この再設計で不要になる作業（明示）

- **S18（`Semantics/Interface.lean`）: 丸ごと中止**．`Semantics` クラス・`Tarski` 束・
  `Sound`/`Complete` クラス・`not_provable_of_countermodel`・`set_models_iff`・
  Foundation の `Semantics (Set M)` generic instance の移植は一切行わない．
- **述語版 `FrameClass` の実装（κ 計画 §2.3・§5，K0 スパイクの (a)(c)）: 中止**．
  `Membership (Frame κ) FrameClass` の outParam 検証も不要．K0 のうち世界レベル `x ⊧ φ` の
  記法検証（旧 (b)）だけは意味を持つが，Fin74 の `Forces _` 実装が完動の前例なのでリスクは低い．
- **`FrameClass.X` 約56 abbrev の移植・書き換え: 不要**（定義ごと廃止）．
- **`IsE`〜`IsET5` バンドル約20クラス＋継承 instance: 削除**（S5 の成果物の一部）．
- **`WeakerThan`/`Equiv`/`Incomparable` と補題約30本: 削除**（S4 の成果物の大部分）．
- **`Frame.logic`／`FrameClass.logic`: 移植しない**（外部使用ゼロを確認済み）．
- 変わらないもの: `cl_prover` 2箇所の `K!_left`/`K!_intro` 置換（§2.3）・MCS の方式（§2.3）・
  `Formula` の構成（§2.2）・`Axiom.Has*`＋代入トリック instance（§2.4）は従来計画のまま．

### R10. 統合ステップ分割（改訂版．S5 以降を置き換え，κ 計画 K0〜K9 を吸収）

逐次実行前提（`CLAUDE.local.md` の方針．並列化はしない）．T9 以降は旧 Phase 2＋κ 化＋
意味論再設計を**1パスで**行う．軸を分けて2パスにしない理由: `Sound`/`Complete`/`FrameClass` の
廃止で各ファイルの**ステートメント自体**が変わるため，κ だけ先に通しても同じ行をもう一度
書き直すことになる（κ 計画 §7.2 の「軸は1つずつ」は，ステートメントが不変な前提の議論だった）．
リスクは「最終形を本計画で完全に固定し，T14 でテンプレートファイルを1つ丁寧に作ってから
残りを機械適用する」ことで抑える．

| # | ステップ | 内容 | 依存 | 難易度 |
|---|---|---|---|---|
| T1 | Logic/Basic 改訂 | R3 の形へ書き直し（`Logic`＋`Consistent` のみ） | — | ★ |
| T2 | Axioms 追記 | 命題論理スキーム7個（`DNE`・`AndElim₁₂`・`AndIntro`・`OrIntro₁₂`・`OrElim`）を追加 | — | ★ |
| T3 | Cl 改訂（骨組み） | `Cl` を1クラス9公理＋mdp に畳み，accessor 化で消える statement を整理．`Finset.conj` 節は維持 | T1, T2 | ★ |
| T4 | Calculus 削り | バンドル・`HasRM` 削除，`rm!` 導出補題化（statement のみ，証明は T6 後） | T3 | ★ |
| T5 | Context 骨組み＋肉付け | `T *⊢[L] φ`（`∃ Γ : Finset, ↑Γ ⊆ T ∧ (Γ.conj 🡒 φ) ∈ L`）・演繹定理・`FormulaSet.Consistent`（旧 S9/S10．richer base で演繹定理が先に立つ） | T3 | ★★ |
| T6 | Cl 肉付け | 残りのツールキット（`efq!`・`dni!`・`elimContra!`・`lem!`・選言除去・`E!_*`・conj 出し入れ）．SeqPL の該当証明を参照実装として翻訳 | T5 | ★★ |
| T7 | MCS | `lindenbaum`（Zorn）・`MaximalConsistentSet L`・所属補題群・`[L.Consistent] → Nonempty (MaximalConsistentSet L)` instance（旧 S11〜S13） | T5, T6, S0 | ★★★ |
| T8 | Hilbert | `Axiom`・`Ax.Has*`・`inductive Hilbert`（9公理＋axm/mdp/re）・`rec!`・`subst_mem`・`(Hilbert Ax).Cl`/`HasRE`/`instHasAxiom*`・`subset_of_subset_axioms`／provable 版・28論理定義・`EMK_eq_EMCK`/`ETB_eq_ENTB`（旧 S15〜S17） | T4 | ★★ |
| T9 | Semantics/Basic 全面改稿 | R7 の骨格: `Frame κ`（`[Nonempty κ]` 引数化）・`World` abbrev・`Model κ`・truthset・3キャリア `⊧`＋`ValidatesSet`・R6 の追加 simp 補題・`subst`．FrameClass 系は書かない．世界レベル `⊧` の elaboration をこのステップ冒頭で最小例確認（旧 K0(b)） | T8 | ★★★ |
| T10 | Semantics/Hilbert | `Hilbert.soundness`（単一フレーム）・`unprovable_of_countermodel`・`consistent_of_frame`（R7-4） | T9 | ★★ |
| T11 | Completeness | `proofset`／`Canonicity` を `{L : Logic} [L.Cl] [L.HasRE] [L.Consistent]` に機械置換，`toModel : Model (MaximalConsistentSet L)`，`exists_countermodel`，`cl_prover` 2箇所置換 | T7, T9 | ★★★ |
| T12 | 公理ファイル群 | `AxiomM`/`C`/`K`/`N`/`P`/`Geach`: フレーム条件節の κ 化＋canonicity instance の `[L.HasAxiom*]` 置換 | T11 | ★★ |
| T13 | Supplementation・IntersectionClosure | `Frame κ → Frame κ` 化（`[Entailment.EM]` → `[L.Cl][L.HasRE][L.HasAxiomM]`） | T12 | ★ |
| T14 | Logic/E.lean（テンプレート） | 1ファイルを丁寧に最終形へ: `validates_axioms`・`soundness`・`unprovable_of_countermodel`・`completeness`・`Consistent` instance・`⊂` 定理群（重複3組の統合込み）・反例書き換え（R7-6）．ここで書式を確定 | T13 | ★★★ |
| T15 | 残り Logic 27ファイル | T14 の書式を機械適用（3〜4ファイルずつコミット）．`EN.lean` の PLoN import 削除，`finite_completeness` を持つファイルは R7-7 の形 | T14 | ★〜★★ |
| T16 | ED_EP・総仕上げ | `Incomparable` → 2定理化，`grep -rn "Foundation" Neighborhood/` 空確認，`just mk-all` → `just shake` → `lake build`，プラン番号コメントの除去確認 | T15 | ★ |
| T17 | Filtration の追随 | （nbhd-filtration 統合後）`Filtration`/`FilterEqvQuotient` の κ 化・型合わせ workaround 除去・8論理の `finite_completeness` 復活 | T16＋filtration 統合 | ★★ |

実施順序: **nbhd-filtration のマージを待ってから T9 以降に着手するのが望ましい**が，
T1〜T8（新コア側，既存41ファイルに触れない）は filtration と完全に直交なので先行してよい．
κ 計画 §7 の「filtration → κ → Phase 2」という3段構えは「filtration マージ → T9〜T17 の1パス」に
置き換わる．

### R11. リスク（改訂版）

1. **世界レベル `⊧`（`Satisfies _` の infix）の elaboration**．Fin74 の `⊩` が完動の前例だが，
   グリフを `⊧` にして Model/Frame 版と重ねたときの overload 解決は T9 冒頭で最小例確認する．
   詰まる場合は世界レベルだけ Fin74 と同じ `⊩`（＋`⊩[M]`）に分離する（既存93箇所のうち
   世界レベルの出現の一括置換で済む）．
2. **1パス書き換えの失敗切り分け**．T14 のテンプレート確定前に T15 に入らないこと．
   各ファイルはビルド確認してからコミット．
3. **`[Nonempty κ]` の伝搬漏れ**．`Frame.Validates` を使う全補題に binder が要る．
   コンパイルエラーで機械的に検出されるため実害は小さいが，`instance : Nonempty F.World`
   相当の橋渡しを `World` abbrev 側に置いて回復経路を確保する．
4. **`Modal.X.unprovable_of_countermodel` の instance 引数が反例フレームで解決できること**．
   反例フレームには従来 `constructor;`／`infer_instance` で `IsX` を証明していた．新形では
   その証明を local instance（`haveI`）または補題引数として明示に渡す箇所が出る．T14 で
   書式を固定する．
5. 旧計画 §6 のリスク 2（Lindenbaum）・3（属性互換）・6（ℕ 固定）・7（filtration 競合）は
   引き続き有効．リスク 1（Łukasiewicz 導出）は R6 により大幅に緩和，リスク 4（名前空間二重化）は
   Phase 2 が1パスになったことで「切替済みファイルのみ import する」不変条件を T9〜T16 の
   直列実行で保つ形に単純化される．

### R12. 規模見積もり（改訂版）

| 部分 | 旧見積 | 新見積（目安） | 差の理由 |
|---|---|---|---|
| Logic（Basic＋Calculus＋Cl＋Context＋MCS） | 1,100 | 750 | 比較クラス・バンドル・`Substitution` 廃止，accessor 化 |
| Hilbert（Basic＋Logics） | 550 | 550 | 公理が6個増えるが `ec` 廃止・バンドル instance 消滅で相殺 |
| Semantics/Interface | 150 | **0** | 中止 |
| Semantics/Basic 改稿 | （Phase 2 扱い） | 300 | κ 化＋記法直付け＋追加 simp 補題 |
| 合計（新規） | 約2,350 | **約2,050** | |

既存41ファイル側は，旧計画の「import・variable の機械置換」に加えて
Sound/Complete/⪱/反例パターンのステートメント書き換え（1ファイルあたり数十行規模）が乗るが，
証明の計算本体（有限フレームの `simp`/`grind`/`tauto_set`）は無傷である．
