# `ModalNeighborhood/Semantics/Filtration.lean` 修正計画

対象: `.claude/worktrees/nbhd-filtration/ModalNeighborhood/Semantics/Filtration.lean`（691行，26エラー）．
参照論文: [Kop23]（`.references/Kop23.pdf`，K. Kopnev, "The Finite Model Property of Some Non-normal Modal Logics with the Transitivity Axiom", arXiv:2305.08605）．
エラー一覧: `.claude/directions/pending-modal-neighborhood/filtration-build-errors.txt`（`lake build` 出力からの抜粋．各エラーの後続文脈は12行で切られており，一部のゴールは途中までしか見えない．以下で「（推定）」と付けた記述はこの切り詰めから復元した推測であり，実装時に `lean_goal` で必ず確認すること）．

前提: 移植元（Lean v4.28.0-rc1 / Foundation 4a7dd136）では本ファイルは完全にビルドが通っていた．エラーは全て Lean v4.31.0 / Foundation b62b3bac へのバージョン差に起因し，**数学的な誤りは見つからなかった**（§2 で詳述）．修正は statement を一切変えず，証明・宣言形式のみを直す方針とする（唯一の例外は `instance` → `def` 化で，これは移植コミット 6a8146d が `Hilbert.lean`・`AxiomGeach.lean` で既に採用した手当てと同一）．

---

## 1. 論文 [Kop23] の filtration 構成の数学的整理

論文の目的は，非正規様相論理 E4（= E + 公理 4: □p → □□p），S04（= E4 + T + M），EMC4（= E4 + M + C）の FMP（有限モデル性）を近傍意味論の filtration で示すこと（Theorem 5.19）．□⊤ のような変数なし論理式の追加でも filtration が保たれる（Corollary 5.20）ので，EN4 系にも拡張できる．

近傍フレームは (W, □) で □ : ℘(W) → ℘(W)（Definition 2.1）．フレーム性質は
reflexive: □X ⊆ X（Def 4.1），regular: □X ∩ □Y ⊆ □(X ∩ Y)（Def 4.2，有限個への一般化が Lemma 4.3），monotonic: X ⊆ Y ⇒ □X ⊆ □Y（Def 4.4），transitive: □X ⊆ □□X（Def 4.5）．

filtration（Section 5）の骨格:

1. **同値関係 ∼Σ**（Σ は部分論理式で閉じた集合）: w ∼Σ v ⇔ ∀φ ∈ Σ (w ⊧ φ ⇔ v ⊧ φ)．商 W̃ と，X ⊆ W に対する像 X̃ = {w̃ | w ∈ X} を取る．
2. **filtration の定義**（Definition 5.1）: W̃ 上のモデル Mf であって，(i) 台が W̃，(ii) φ ∈ Σ なら □f |φ|~ = |□φ|~，(iii) Vf(p) = |p|~ を満たすもの．
3. **Filtration Theorem**（Theorem 5.2）: φ ∈ Σ に対し |φ|_{Mf} = |φ|~．系として Lemma 5.3: φ, ψ ∈ Σ について |φ| = |ψ| ⇔ |φ|~ = |ψ|~，および Lemma 5.8: |φ|~ = □f |ψ|~ なら |□φ|~ = |□□ψ|~（正確には |□φ|~ = □f の像の押し出し．技術補題）．
4. **最小 filtration**（Definition 5.4）: □f⁻ X = |□φ|~（X = |φ|~ となる φ ∈ Σ があるとき），それ以外は ∅．well-definedness が Proposition 5.5（|φ|~ = |ψ|~ なら |□φ|~ = |□ψ|~）．
5. **閉包 □̂**（Definition 5.6）: □̂X = X（X = □Y となる Y があるとき），それ以外は ∅．
6. **推移的 filtration**（Definition 5.7）: □fᵀ X = □f⁻ X ∪ □̂f⁻ X．これが filtration であること（Lemma 5.9），推移的モデルに適用すると推移性を保つこと（Lemma 5.10，□f⁻X = ∅ か否かの2ケース），反射的モデルなら反射性を保つこと（Lemma 5.12）．→ **E4 の FMP**．
7. **supplementation**（Definition 4.10）: □# X = ⋃{□Y | Y ⊆ X}．単調（Lemma 4.11），反射性・推移性・正則性を保存（Lemma 4.14）．単調かつ推移的なモデルでは MfT の supplementation MfT# も filtration（Lemma 5.11）．→ **S04 の FMP**．
8. **intersection closure**（Definition 5.13）: □* X = ⋃{□X₁ ∩ … ∩ □Xₙ | X = X₁ ∩ … ∩ Xₙ}．正則性を与える（Theorem 5.14）．supplementation と可換: F*# = F#*（Lemma 5.15）．合成を **rm-closure** □• と呼ぶ（Definition 5.16）．単調・推移的なら □• は推移性を保つ（Lemma 5.17）．単調・推移的・正則なモデルでは MfT• が filtration（Lemma 5.18）．→ **EMC4 の FMP**．

Lemma 5.18 の証明の骨格（本ファイル最難関部の元）: w̃ ∈ □fᵀ* Y，Y = Y₁ ∩ … ∩ Yₙ ⊆ |φ|~，各 i で w̃ ∈ □f⁻ Yᵢ または w̃ ∈ □̂f⁻ Yᵢ．前者の Yᵢ を Vⱼ（Vⱼ = |ψⱼ|~，w̃ ∈ |□ψⱼ|~），後者を Uₖ（Uₖ = |□γₖ|~，w̃ ∈ |□γₖ|~）と分ける．w ⊧ □ψⱼ と，推移性から w ⊧ □□γₖ を得て，正則性（Lemma 4.3 の有限交叉版）で w ∈ □(⋂ⱼ|ψⱼ| ∩ ⋂ₖ|□γₖ|)，単調性で w ∈ □|φ| = |□φ|，すなわち w̃ ∈ |□φ|~．

## 2. 実装と論文の対応表

| 実装（`Filtration.lean` ほか） | 論文 [Kop23] | 一致の確認 |
|---|---|---|
| `filterEquiv` / `FilterEqvSetoid` / `FilterEqvQuotient`（29–41行） | ∼Σ と W̃（§5 冒頭） | 一致 |
| `toFilterEquivSet`＝`【X】`（81行） | X̃ | 一致 |
| `FilterEqvQuotient.finite`（49行） | 「W̃ は有限（Σ 有限のとき）」（暗黙に使用） | 一致（℘Σ への単射） |
| `structure Filtration`：`B_def`・`V_def`（195行） | Definition 5.1 の条件 (ii)(iii)．条件 (i) は台の型が `FilterEqvQuotient` である事実に吸収 | 一致 |
| `Filtration.filtration`（214行） | Theorem 5.2 | 一致 |
| `Filtration.truthlemma`（234行）・`toFilterEquivSet.eq_original_truthset_of_eq`（144行）・`subset_original_truthset_of_subset`（137行） | Lemma 5.3（後2者は ⇐ 方向とその ⊆ 版） | 一致 |
| `Filtration.box_in_out`（243行）・`transitive_lemma`（252行） | Lemma 5.8 とその帰結 | 一致 |
| `minimalFiltration`（261行，`if ∃φ, □φ ∈ T ∧ X = 【M φ】` で分岐） | Definition 5.4，well-definedness の `B_def` 証明が Proposition 5.5 | 一致 |
| `transitiveFiltration` の `if ∃ Y, X = (minimalFiltration M T).B Y then X else ∅`（298行） | Definition 5.6 の閉包 □̂（□ = □f⁻ の場合） | 一致 |
| `transitiveFiltration`（297行，`B X := minimal.B X ∪ (if … then X else ∅)`）と `B_def` | Definition 5.7 と Lemma 5.9 | 一致 |
| `transitiveFiltration.isTransitive`（359行） | Lemma 5.10（□f⁻X = ∅ / ≠ ∅ の2ケース構造まで一致） | 一致 |
| `transitiveFiltration.isReflexive`（397行） | Lemma 5.12（実装は `iff_mem_B` 経由でより簡潔だが主張は同じ） | 一致 |
| `Frame.supplementation`（`Supplementation.lean`） | Definition 4.10・Lemma 4.11・4.14 | 一致 |
| `supplementedTransitiveFiltration`（420行） | Lemma 5.11（S04 用） | 一致 |
| `Frame.intersectionClosure`（`IntersectionClosure.lean`，`Finset` の非空有限族 `Xs` による ⋂） | Definition 5.13（有限交叉を `Finset` で表現） | 一致 |
| `Frame.quasiFiltering := intersectionClosure.supplementation`（同ファイル46行） | Definition 5.16 の rm-closure □•（`symm_box` が Lemma 5.15 に対応） | 一致 |
| `quasiFilteringTransitiveFiltration`（467行）の `B_def` | Lemma 5.18．`Vs`/`Us` の分割＝論文の Vⱼ/Uₖ，`Ψ`/`Ξ`＝{ψⱼ}/{γₖ}，`M.regular_finite_iUnion`（`AxiomC.lean`）＝Lemma 4.3 | 一致（下記補足） |
| `transitiveFiltration.containsUnit`・`supplemented….containsUnit`・`quasiFiltering….containsUnit`（405・456・656行，仮定 `hT : □⊤ ∈ T`） | 論文に直接の対応なし．Corollary 5.20（変数なし公理の追加）の □⊤ 特化に相当する実装独自の拡張（EN4 系の FMP 用） | 数学的に正当（□⊤ ∈ T なら 【M ⊤】 = univ が B の像に入る） |

補足（Lemma 5.18 と実装の差分）: 論文は Vⱼ・Uₖ の少なくとも一方が非空である場合を一様に扱うが，実装は `Nonempty Ψ` × `Nonempty Ξ` の4通りに場合分けし，両方空のケースは `Ys ≠ ∅`（intersection closure の非空性条件 `hYs₁`）との矛盾で潰す（623–632行）．これは論文の証明の忠実な精緻化であり食い違いではない．

**結論: 実装と論文の間に数学的な食い違いは見つからなかった**．ユーザーの「実装自体はあっていたはず」という認識と整合する．全エラーはバージョン差по起因．

## 3. 26 エラーの分類と修正方針

系統の凡例（依頼文の分類に従う）:
- **(1)** instance 宣言の厳格化 → `def` 化
- **(2)** `simp`/`simp_all`/`tauto`/`grind` が definitional な残差を閉じない → `rfl` 追加・明示証明
- **(3)** `instances` 透過度の変化による型不一致 → 型の明示的整列
- **(4)** `Finset` の `∪` メンバーシップの扱い → `Finset.mem_union` 経由に書き換え
- **(5)** `calc` の `Trans` instance 合成失敗

| # | 位置 | 系統 | 数学的内容と修正方針 |
|---|---|---|---|
| E1 | 140:4 | (2) | `subset_original_truthset_of_subset`（Lemma 5.3 の ⊆ 版）内．`simpa … using h` の正規形が変わり，`h` が `∀ a, ∀ x ∈ M φ, ⟦x⟧ = a → ∃ x ∈ M ψ, ⟦x⟧ = a` の形（量化子順序が違う）に化ける．**方針**: `simpa` による一発変換をやめ，目標 `∀ y ∈ M φ, ∃ z ∈ M ψ, filterEquiv M T z y` を直接示す．`y ∈ M φ` を取り，`h` に商 `⟦y⟧` と代表 `y` を渡して `z ∈ M ψ` かつ `⟦z⟧ = ⟦y⟧` を得て，`Quotient.eq`（`FilterEqvSetoid` の定義）で `⟦z⟧ = ⟦y⟧` を `filterEquiv M T z y` に読み替える |
| E2 | 212:49 | (2) | `toModel_def`．残ゴール `{w \| X ∈ {X \| w ∈ Fi.B X}} = Fi.B X` は set-builder のβ簡約で定義的に両辺一致．**方針**: 末尾に `rfl` を足す（`simp` を `simp only` に絞ってもよい） |
| E3 | 217:12 | (2) | `filtration`（Theorem 5.2）の `hfalsum` ケース．残ゴール `∅ = ∅`．**方針**: `rfl` 追加（`toFilterEquivSet.empty` を simp が当てた後の残差） |
| E4 | 218:21 | (2) | 同 `himp` ケース．残ゴール `A = A` の形（両辺完全同形）．**方針**: `simp_all […]` が閉じなくなっただけなので `rfl` で終える形に直す |
| E5 | 235:87 | (2) | `truthlemma`（Lemma 5.3）．`rw` 後の残ゴールが `X = Y ↔ X = Y`．**方針**: `Iff.rfl`（ないし `rfl`）追加 |
| E6 | 239:93 | (2) | `iff_mem_toModel_box_mem_B`．残ゴール `W ∈ {w \| Y ∈ {X \| w ∈ Fi.B X}} ↔ W ∈ Fi.B Y`（β簡約で自明）．**方針**: `Iff.rfl` 追加，または `simp` を外して `rfl` 一発 |
| E7 | 244:39 | (2) | `box_in_out`（Lemma 5.8 相当）の calc 第1ステップ．残ゴール `Fi.B 【M φ】 = {w \| 【M φ】 ∈ {X \| w ∈ Fi.B X}}`（`Frame.mk_ℬ`・`Frame.box` の展開で定義的に等しい）．**方針**: `rfl` 追加 |
| E8 | 363:2 | (2) | `transitiveFiltration.isTransitive`（Lemma 5.10）Case 1（`(minimalFiltration M T).B X = ∅`）．`simp_all` が `if` の場合分けまで自動でやらなくなった（残ゴールは途中で切られており全形は未確認・要 `lean_goal`）．**方針**: 論文 Case 1 の議論を明示化する．`w ∈ (transitiveFiltration M T).toModel.box X` は `h` の下で「`(∃ Y, X = minimal.B Y) ∧ w ∈ X`」に潰れる（左の選言肢は `h` で空）．このとき `transitiveFiltration.B X = X`（if の真分岐）なので，`box^[2] X` の元であることは同じ条件で再び言える．`intro` してから `split_ifs`／`Set.mem_setOf_eq` のβ簡約で選言を露出させ，手で分岐する |
| E9 | 374:6 | (5)+(3) | 同補題 Case 2 の calc 最終ステップ `_ = (transitiveFiltration M T).toModel.box^[2] X`．`Trans Subset Eq` の合成失敗．直前ステップの型が `Set (FilterEqvQuotient M T)` で，`toModel.box^[2]` 側は `Set (transitiveFiltration M T).toModel.World` であり，`instances` 透過度でしか一致しないため `Trans` の型統一に失敗している可能性が高い（要 `lean_goal` 確認）．**方針**: 最終 `=` ステップを `⊆` に変える（`Eq.subset` で埋める），または `show (…: Set (FilterEqvQuotient M T)) = …` の型注釈で両辺の型を明示的に揃えてから `=` のまま通す |
| E10 | 405:0 | (1) | `transitiveFiltration.containsUnit`．explicit 引数 `hT : □⊤ ∈ T` を持つ `instance` が拒否される．**方針**: `protected def` に変更（移植コミットの `Hilbert.lean`/`AxiomGeach.lean` と同じ手当て）．呼び出し側（460行・660行）は既に `transitiveFiltration.containsUnit hT` と明示適用しており変更不要 |
| E11 | 456:0 | (1) | `supplementedTransitiveFiltration.containsUnit` も同様に `protected def` 化 |
| E12 | 456:128 | (2) | 同補題の証明本体．残ゴール `X ∈ (transitiveFiltration M T).toModel.supplementation.box Set.univ`．`simp [supplementedTransitiveFiltration, ….supplementation.contains_unit]` の後者引数が効かなくなった（unused 警告も出ている）．数学的内容: transitiveFiltration が `ContainsUnit`（`this`）なのでその supplementation も unit を含む（Lemma 4.11 系）．**方針**: `this` を `haveI` で instance 登録した上で，`Frame.supplementation.containsUnit` から従う `contains_unit`（`box Set.univ = Set.univ`）を `rw` で明示的に使い，`X ∈ Set.univ` を `trivial` で閉じる．または `Frame.supplementation.mem_box_of_mem_original_box` で transitiveFiltration 側の `contains_unit` に帰着させる |
| E13 | 484:12 | (4) | `quasiFilteringTransitiveFiltration.B_def`（Lemma 5.18）内 `eYVU : Ys = Vs ∪ Us` の mp 分岐．`left` が「target is not an inductive datatype」で失敗．480行の `simp only [Finset.mem_union, …]` で `Finset.mem_union` が unused（警告）になっており，ゴールが `Yi ∈ Vs ∪ Us`（Finset メンバーシップ）のまま `Or` に分解されていない．**方針**: `Finset.mem_union.mpr` + `Or.inl`／`Finset.mem_filter.mpr` を明示的に適用する形へ．CLAUDE.md のテンプレート（`simp only [Finset.mem_union, Finset.mem_filter]; grind`）も試す価値あり |
| E14 | 485:12 | (4) | 同・`right` 失敗．E13 と同じ手当て（`Or.inr`） |
| E15 | 486:10 | (4)+(2) | 同・mpr 分岐の `tauto_set` が閉じない．内容は「`Yi ∈ Vs ∪ Us` なら `Yi ∈ Ys`」（Vs・Us はいずれも Ys の filter なので自明）．**方針**: `Finset.mem_union`・`Finset.mem_filter` で開いてから `grind`／`tauto` |
| E16 | 527:31 | (4) | 同補題内 calc `_ = ⋂ Xi ∈ Ys, Xi` ステップ．`simp only […, eYVU, Finset.mem_union]` 後のゴール形状が変わり，`rintro ⟨hV, hU⟩ i (hi \| hi)` のパターン位置がずれて `(hi \| hi)` が集合そのもの（`World → Prop`）に当たって失敗．**方針**: `rintro` パターンに頼らず `intro` で受けてから `rcases Finset.mem_union.mp hi with hi \| hi` と明示的に分解する（`IntersectionClosure.lean` 29–35行の同型証明が通っている形を踏襲する） |
| E17 | 534:14 | (4) | 同・mpr 側の `left` 失敗（ゴールが `i ∈ Vs ∪ Us` のままで `Or` でない）．**方針**: `apply h` の後 `Finset.mem_union.mpr (Or.inl hi)` 相当に書き換え |
| E18 | 538:14 | (4) | 同・`right` 失敗．E17 と同様（`Or.inr`） |
| E19 | 540:8 | (5)+(3) | 同 calc の `_ = Y := by grind` ステップで `Trans Eq Eq` 合成失敗．`Eq` と `Eq` の Trans は常に存在するので，実態は両ステップの型が `Set (FilterEqvQuotient M T)` と `Set (transitiveFiltration M T).toModel.World` に分かれており reducible 透過度で統一できないこと（`Y` は `quasiFiltering.box` の分解から来るので後者の型を持つ）が原因と推定（要 `lean_goal` 確認）．**方針**: calc 冒頭または当該ステップに `show` / 型注釈を入れて全ステップの型を `Set (FilterEqvQuotient M T)` に揃える |
| E20 | 570:10 | (2) | Lemma 5.18 の Ψ・Ξ とも非空のケース，Ξ 側の `∀ ξ : Ξ, w ∈ M (□^[2]ξ)` を示す `grind only […]` が失敗．数学的内容: `⟨ξ, hξ, ⟨Ui, hUi, rfl⟩, ⟨v, hv₁, hv₂⟩⟩` から `⟦w⟧ ∈ 【M (□ξ)】` が分かるので，`□ξ ∈ T` と `toFilterEquivSet.iff_mem_truthset` で `w ⊧ □ξ`，すなわち `w ∈ M.box (M ξ)` を得て，`M.trans`（推移性）で `w ∈ M.box^[2] (M ξ) = M (□^[2]ξ)`（`Model.truthset.eq_boxItr`）とすればよい．**方針**: `grind only` を捨てて上記2段を明示証明にする（§5 難所1参照）．なお既存の `replace hv₁ := M.trans hv₁`（v 側に推移性を適用する行）は w への転送に □□ξ ∈ T が必要になる筋悪ルートなので，w 側で直接推移性を使う形に組み替える |
| E21 | 619:8 | (2) | Ψ 空・Ξ 非空ケースの同型の `grind only` 失敗．E20 と全く同じ手当て |
| E22 | 625:35 | (4)+(2) | Ψ・Ξ とも空のケース．`suffices (Vs = ∅ ∧ Us = ∅) by simp [eYVU, this.1, this.2]` の `simp` が `Ys = ∅` を閉じない（`eYVU` の書き換えと `∅ ∪ ∅ = ∅` の縮約の噛み合わせが変わった．正確な残差は要 `lean_goal`）．**方針**: `simp` を `rw [eYVU, this.1, this.2]` ＋ `Finset.union_empty`（または `Finset.empty_union`／`simp only`）の明示列に置き換える |
| E23 | 629:67 | (3) | 同ケース内 `apply (show ∀ ψ, □ψ ∈ T → 【M ψ】 ∈ Ys → ⟦w⟧ ∉ 【M (□ψ)】 by simpa [Ψ] using hΨ)`．エラー表示上は binder 名（`x` vs `ψ`）しか違わない型不一致で，表示に出ない部分（`∈`/`∉` の展開形か，`⟦·⟧` の Setoid instance 経路か）が reducible 透過度で一致していないと推定（要 `lean_goal`/`lean_term_goal` での特定）．数学的内容: `¬Nonempty Ψ` から「条件を満たす ψ は存在しない」の全称形への読み替え．**方針**: `simpa … using hΨ` の最終 defeq チェックに依存する形をやめる．`hΨ` を `not_nonempty_iff`→`IsEmpty` 経由で開き，`have h : ∀ ψ, □ψ ∈ T → 【M ψ】 ∈ Ys → ⟦w⟧ ∉ 【M (□ψ)】 := by intro ψ …; exact (hΨ ⟨⟨ψ, …⟩⟩).elim` のように，目標型を先に固定した `have` で明示的に構成してから `apply` する |
| E24 | 632:70 | (3) | Ξ 側の同型エラー．E23 と同じ手当て |
| E25 | 656:0 | (1) | `quasiFilteringTransitiveFiltration.containsUnit` の `instance` → `protected def` 化（E10・E11 と同様） |
| E26 | 656:139 | (2) | 同証明本体．E12 の quasiFiltering 版（661行の `contains_unit` simp 引数が unused）．残ゴールは `X ∈ (transitiveFiltration M T).toModel.quasiFiltering.box Set.univ`（推定，文脈切り詰めのため要確認）．**方針**: E12 と同じく，`this` を instance 登録して `Frame.quasiFiltering.containsUnit`（`IntersectionClosure.lean` 136行）由来の `contains_unit` を明示 `rw`，または `Frame.quasiFiltering.mem_box_of_mem_original_box` で帰着 |

エラーではないが同時に処理すべき警告（コミット前に警告ゼロにするため）:

- W1（153:45）: `simpa` → `simp` に変更（linter 指示どおり）．
- W2（269:6）: `push_neg` の deprecation → `push Not` に変更（`minimalFiltration` の `B_def` 内．291行・321行にも同型の `push_neg` があるが，エラー・警告一覧に出ているのは269行のみ．実装時に同ファイル内の全 `push_neg` を確認して一括で直すのが安全）．
- W3（461:42）・W4（661:44）・W5（480:19）: unused simp args．それぞれ E12・E26・E13–E15 の修正で自然に解消される（残れば削除）．

## 4. ステップ分割

**並列化の判断: 逐次実行を推奨する．** 本タスクは1ファイル（`Filtration.lean`）内の修正であり，特にエラーの半数（E13–E24 の12件）は単一の証明（`quasiFilteringTransitiveFiltration` の `B_def`，466–638行）の内部に集中している．同一証明内のエラーは前段の修正がゴール形状を変えるため原理的に並列化できない．残りも同一ファイルの近接行であり，worktree を分けても merge の手間がリスクに見合わない．よって **この worktree 上で1エージェント（`lean4-proof-writer`）が下記ステップ順に逐次実行し，1ステップごとにビルド確認・コミットする**のが最適．ステップ間の独立性（下表の依存欄）は「失敗時にどこまで切り戻せるか」「途中で別エージェントに交代できるか」の単位として使う．

| Step | 対象（行・宣言） | エラー | 依存 | 難易度 |
|---|---|---|---|---|
| S1 | 212–247行: `toModel_def`・`filtration`・`truthlemma`・`iff_mem_toModel_box_mem_B`・`box_in_out` | E2–E7 | なし | 低（機械的な `rfl`/`Iff.rfl` 追加） |
| S2 | 137–142行: `subset_original_truthset_of_subset` | E1 | なし | 低〜中（`simpa` を明示証明へ） |
| S3 | 153行・269行（＋291・321行の同型箇所）: 警告2件 | W1, W2 | なし | 低 |
| S4 | 359–395行: `transitiveFiltration.isTransitive` | E8, E9 | なし | 中（Case 1 の明示化と calc の型揃え．論文 Lemma 5.10 の Case 1/2 構造を保つ） |
| S5 | 405–414行: `transitiveFiltration.containsUnit` の def 化 | E10 | なし | 低 |
| S6 | 456–461行: `supplementedTransitiveFiltration.containsUnit`（def 化＋証明修正） | E11, E12, W3 | S5（460行で `transitiveFiltration.containsUnit hT` を def として呼ぶ．シグネチャ不変なので実質独立だが，ビルド順として S5 を先に） | 低〜中 |
| S7 | 478–486行: `eYVU`（`Ys = Vs ∪ Us`） | E13–E15, W5 | なし | 中（`Finset.mem_union`/`mem_filter` 明示化） |
| S8 | 496–541行: calc 連鎖 `H`（⋂ の組み替え） | E16–E19 | S7（`eYVU` の証明形を simp で参照しており，同一証明内で直後に続く） | 中〜高（§5 難所2） |
| S9 | 543–574行: Ψ・Ξ 非空ケースの `grind` 置換 | E20 | S8（同一証明内の直後） | 中〜高（§5 難所1） |
| S10 | 597–622行: Ξ のみ非空ケースの `grind` 置換 | E21 | S9（S9 で確立した証明パターンを流用） | 中（S9 のコピー適用） |
| S11 | 623–632行: 両方空ケース | E22–E24, （W5 残余） | S7（`eYVU` を使用），S8–S10 と同一証明内 | 中（§5 難所3） |
| S12 | 656–661行: `quasiFilteringTransitiveFiltration.containsUnit`（def 化＋証明修正） | E25, E26, W4 | S5（実質 S6 と同型．S6 の修正パターンを流用） | 低 |
| S13 | 仕上げ: `lake build` 全体確認 → 警告ゼロ確認 → `ModalNeighborhood.lean` の import（追加済み）でのビルド → `just mk-all`・`just shake`・再ビルド | — | S1–S12 | 低 |

備考:
- S1–S6 は互いに独立（どの順でもよい）．S7–S11 は単一証明内なので必ずこの順で逐次．S12 は S6 完了後ならいつでも可．
- どうしても並列化するなら，境界は「S1–S3（29–294行，`Filtration` 基盤部）」「S4–S5（296–416行，`transitiveFiltration`）」「S6（418–463行，supplementation 版）」「S7–S11（465–638行，quasiFiltering 版）」「S12（640–663行）」の namespace 単位で行範囲が分離できるが，前述のとおり推奨しない．
- 移植コミット 6a8146d のメッセージにある通り，`Logic/E4.lean` 等8ロジックの `finite_complete` instance がコメントアウトされたまま残っている．これらの復活（コメント解除とビルド確認）は本計画の範囲外の後続タスクとして別途扱う（Filtration.lean が green になった後に着手可能になる）．

## 5. 難所の詳細

### 難所1: E20・E21（570・619行）の `grind only` 失敗

**何が起きているか**: ここは論文 Lemma 5.18 の「Uₖ 側（Ξ 側）の各 γₖ について w ∈ □□|γₖ| を示す」箇所．旧 Lean では `grind only [長い補題リスト]` が次の推論連鎖を自動で発見していた:

1. `⟨v, hv₁, hv₂⟩ : ⟦w⟧ ∈ 【M (□ξ)】`，すなわち `v ∈ M (□ξ)` かつ `⟦v⟧ = ⟦w⟧`．
2. `□ξ ∈ T` なので `FilterEqvQuotient.iff_eq`（∼Σ の定義）により satisfaction が転送でき，`w ∈ M (□ξ)`．
3. `M.trans`（フレームの推移性，`□X ⊆ □□X`）により `w ∈ M.box^[2] (M ξ)`．
4. `Model.truthset.eq_boxItr` により `M (□^[2]ξ) = M.box^[2] (M ξ)` なのでゴール一致．

新 Lean の `grind` はこの連鎖（特にステップ2の商をまたぐ転送と，ステップ4の defeq でない書き換えの組み合わせ）を見つけられなくなった．

**注意点**: 直前の行 `replace hv₁ : v ∈ M.box^[2] (M ξ) := M.trans hv₁` は **v 側に**推移性を適用しているが，`v ⊧ □□ξ` を `w` に転送するには `□□ξ ∈ T` が必要で，これは一般に成り立たない（T は □ξ までしか含まない）．旧 grind はおそらくこの `hv₁` を使わず上記ルート（w 側で先に転送してから推移性）で閉じていた．**明示証明に書き直す際は `replace` 行ごと削除し，w 側転送→推移性の順で組む**こと．ステップ2は既存補題 `toFilterEquivSet.iff_mem_truthset`（92行，`□ξ ∈ T` を引数に取る）がそのまま使える．

**代替方針**: もし1点ずつの明示証明が煩雑なら，「`⟦w⟧ ∈ 【M (□ξ)】` かつ `□ξ ∈ T` なら `w ∈ M (□^[2]ξ)`」を section 内 private 補題として1本切り出し，570行・619行（および同型の595行 `grind`——現在は通っているが同じ補題で置き換えれば頑健になる）から呼ぶ形が綺麗．

### 難所2: E16–E19（527–540行付近）の `Finset` union と calc の型不一致

**何が起きているか**: 2つの独立な劣化が同じ calc 連鎖に重なっている．

(a) **Finset union の分解**（E16–E18）: `Vs`・`Us` は `Finset` の filter で，`eYVU : Ys = Vs ∪ Us` は `Finset` の等式．旧 Lean では `simp only […, Finset.mem_union]` 後のゴールに対する `rintro … (hi | hi)` や，`i ∈ Vs ∪ Us` ゴールへの `left`/`right` が（メンバーシップが `Or` に簡約されて）通っていたが，新 Lean では `Finset` の `∈ ∪` が自動で `Or` に落ちず，`left`/`right`/`rcases` が「inductive でない」と拒否する．**方針**: 分解方向は `rcases Finset.mem_union.mp hi with hi | hi`，構成方向は `exact Finset.mem_union.mpr (Or.inl hi)` のように，全て `Finset.mem_union` を明示的に経由する．同リポジトリで既に通っている `IntersectionClosure.lean` の `isRegular` 証明（29–38行）がまさに同じ「⋂ over Finset union」の場合分けを新 Lean で通る形で書いており，最良のテンプレートになる．

(b) **calc の型不一致**（E19，および同根の E9）: `Trans Eq Eq` の合成失敗という一見不可解なエラーは，`Eq` の両辺の型が `Set (FilterEqvQuotient M T)`（`【·】` 側の式）と `Set ((transitiveFiltration M T).toModel.World)`（`quasiFiltering.box` の分解から来る `Y`・`Ys` 側の式）に分裂していることが原因と推定される．`toModel.World` は `Frame.mk_ℬ (FilterEqvQuotient M T) …` の `World` フィールドで，unfold すれば `FilterEqvQuotient M T` そのものだが，新 Lean は `instances` 透過度でこの展開をしなくなった（系統(3)．移植コミットの3点目と同一の現象）．**方針**: calc の対象式に `show`（または開始行に `(… : Set (FilterEqvQuotient M T))` の型注釈）を入れて全ステップを片方の型に固定する．どちらに寄せるかは，使う補題群（`toFilterEquivSet` 系は `FilterEqvQuotient` 側，`hYs₃` 等の分解仮説は `toModel.World` 側）の分布を見て，書き換えが少ない側に寄せる．`lean_goal`/`lean_term_goal` で実際の型表示を確認してから決めること．

### 難所3: E23・E24（629・632行）の「同一に見える」型不一致

**何が起きているか**: `simpa [Ψ] using hΨ` の結果の型とゴール型が，pretty printer 上は binder 名しか違わない（`∀ (x : Formula ℕ), …` vs `∀ (ψ : Formula ℕ), …`）のに mismatch になる．binder 名は defeq に無関係なので，**表示に現れない差**——候補は (i) `【·】`（`toFilterEquivSet`）や `∉` の内部展開形の差，(ii) `⟦·⟧` の `Quotient.mk` が経由する Setoid instance 項の差，(iii) `Ys` のメンバーシップ（`Finset` 直接 vs 強制写像経由）——が reducible 透過度で一致していない．どれが原因かは未確認（エラー文脈が12行で切られているため）．実装時に `lean_term_goal` と `set_option pp.all true` 相当の観察で特定するのが第一歩．

**方針（原因特定に依らず有効な回避策）**: `show … by simpa using hΨ` という「simpa の出力とゴールの defeq 一致」に賭ける書き方を放棄する．`hΨ : ¬Nonempty Ψ`（Ψ は subtype `{ψ // □ψ ∈ T ∧ (∃ Vi ∈ Ys, Vi = 【M ψ】) ∧ W ∈ 【M (□ψ)】}`）から，目標の全称文を `intro` で開いた具体的な反例 `⟨ψ, hψ, ⟨_, hVi, rfl⟩, hw⟩ : Ψ` を組み立てて `hΨ ⟨…⟩` の矛盾で閉じる形に書き直す．こうすれば型合わせは各項の `exact` 時に局所的に起き，透過度問題が表面化しない．E22（625行）の `simp` 失敗も同じ書き直しの中で `rw` ベースにすれば一緒に解消できる．

### 補足の難所: E8（363行）

`simp_all` が閉じていたゴールの全形が確認できていない（文脈切り詰め）．論文 Lemma 5.10 Case 1 の内容（□f⁻X = ∅ のとき □fᵀX は閉包項のみ＝X 自身か ∅，いずれでも □fᵀ□fᵀX に入る）は単純だが，`if` を含む set-builder の中の選言を手で分岐する必要があるため，`split_ifs` の位置と `Set.mem_setOf_eq` のβ簡約タイミングに注意．修正前に必ず `lean_goal` で残ゴールを観察すること．

## 6. 検証手順（各ステップ共通）

1. 修正前に `mcp__lean-lsp__lean_goal` で当該位置の実ゴールを確認する（本計画の「推定」箇所は特に必須）．
2. 修正後は `lean_diagnostic_messages` で当該宣言のエラー・警告が消えたことを確認する．
3. ステップ完了ごとにコミット（メッセージは英語，`Co-Authored-By: Claude <noreply@anthropic.com>` 付き）．本ファイルは `ModalNeighborhood` ライブラリなのでプロジェクト prefix は `ModalNeighborhood:` を用いる（移植コミット 6a8146d に倣う）．
4. S13 で全体 `lake build` → `just mk-all` → `just shake` → 再 `lake build`．

## 7. 確認できなかったこと（正直な限界の明記）

- エラー一覧の文脈が12行で切られているため，E8・E19・E22・E23・E24・E26 の**残ゴールの全形は未確認**．修正方針は前後のコードと移植コミットの前例からの推定であり，実装時に `lean_goal` での確認を必須とする．
- E9・E19 の `Trans` 失敗を型不一致（系統(3)）と断定する直接証拠（エラー中の型表示）はエラー文脈からは得られていない．`Trans Eq Eq` が失敗するのは型の分裂以外に考えにくい，という消去法による推定である．
- 論文との照合は本文（Definition 5.1–5.16，Lemma 5.3–5.18，Theorem 5.19，Corollary 5.20）を `pdftotext` 抽出で通読して行ったが，`containsUnit` 系3宣言は論文に直接対応する補題が存在しない（Corollary 5.20 の精神に沿う実装独自拡張である）ことを明記しておく．
