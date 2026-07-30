# Neighborhood の Frame/Model κ パラメータ化 設計文書

`Neighborhood` の近傍フレーム・モデルを，Fin74 と同様に「世界の型 `κ : Type u` を構造体の
パラメータとして受け取る」形にリファクタリングするための設計とステップ分割．

- 対象: `Neighborhood/Semantics/` 配下（本 worktree の27ファイル＋別 worktree で修正中の
  `Filtration.lean`）．
- 本文書中の Lean 風の型表記はすべて擬似コード（型シグネチャの意図を示すもの）であり，
  正確な構文は実装担当が確定する．
- 調査は次の実物を読んで行った: `Neighborhood/Semantics/Basic.lean`・`Hilbert.lean`・
  `Completeness.lean`・`Supplementation.lean`・`Logic/E4.lean`・`Logic/Incomparability/ED_EP.lean`，
  `Fin74/Kripke/Basic.lean`・`Fin74/Result/Incomplete.lean`，Foundation の
  `Logic/Semantics.lean`・`Logic/Entailment.lean`（`Sound`/`Complete`），nbhd-filtration worktree の
  `Filtration.lean`・`plans/nbhd-filtration-fix.md`，
  `.claude/directions/pending-modal-neighborhood/filtration-build-errors.txt`，
  移植コミット 6a8146d のコミットメッセージ，`plans/nbhd-defoundation.md`．

---

## 1. 現状分析

### 1.1 現在の設計（`Semantics/Basic.lean`）

| 宣言 | 現在の形 | 備考 |
|---|---|---|
| `Frame` | `structure Frame where World : Type; [world_nonempty : Nonempty World]; 𝒩 : World → Set (Set World)` | `World` はフィールド，`Type 0` 固定．`Frame : Type 1` |
| `CoeSort` | `instance : CoeSort Frame Type := ⟨Frame.World⟩` | `F.box : Set F.World → Set F.World` 等が依存 |
| `mk_ℬ` | `def mk_ℬ (World : Type) [Nonempty World] (B : Set World → Set World) : Frame` | box 演算子から 𝒩 を作る．**plain `def`**（reducible でない） |
| `FrameClass` | `abbrev FrameClass := Set Frame` | `Set` の全 API（`∈`・set-builder・`Set.Nonempty`）と Foundation の generic instance `Semantics (Set M) F` にただ乗りしている |
| `Valuation` | `abbrev Valuation (F : Frame) := ℕ → Set F.World` | |
| `Model` | `structure Model extends Frame where Val : Valuation toFrame` ＋ `CoeSort Model Type` | |
| 世界レベル `⊧` | `Satisfies.semantics {M : Model} : Semantics M (Formula ℕ)`（`M` は `CoeSort` で型に強制） | `x ⊧ φ` の instance 解決は「`x` の型 `M.World` から `M` を復元できる」ことに依存 |
| クラスレベル `⊧` | Foundation の `instance [Semantics M F] : Semantics (Set M) F`（`Semantics.lean:231`）経由 | `Semantics.set_models_iff`・`⊧* Ax` もここから |

### 1.2 κ 化で壊れる／変わるものの棚卸し

- **`FrameClass := Set Frame`（使用221箇所）が型として成立しなくなる**．§2 で詳述．
- **フレームクラスの membership 操作**: `Set.mem_setOf_eq` 系の書き換えが `Semantics/` 配下に
  98箇所（grep 実測）．`{ F | F.IsE4 }` の set-builder が28論理×（通常＋finite）で約50定義．
- **構造体リテラル**: `World := Fin 2` のような世界型のフィールド指定が実測15箇所
  （`Logic/E.lean`×5・`EC.lean`×2・`EN.lean`×2・`ECN.lean`・`EM.lean`・`EK.lean`・
  `Supplementation.lean`・`IntersectionClosure.lean`・`Completeness.lean`）．
  κ 化後は `World :=` 行を消して型引数に移すだけの機械的変更．
  無名コンストラクタ `⟨Unit, λ _ => {Set.univ}⟩`（`simple_blackhole` 等）も第一成分を型引数へ．
- **`world_nonempty` フィールド**: パラメータ κ についての証明フィールド
  `[world_nonempty : Nonempty κ]` としてそのまま残せる（フィールドがパラメータに言及するのは
  合法で，defeq 問題も再導入しない）．Fin74 の `Frame` に nonempty 制約は無いが，
  近傍側は `Semantics.Bot Model`（`M ⊭ ⊥`）・`FilterEqvQuotient` の `Nonempty` instance・
  `consistent_of_sound_frameclass` が世界の非空性を実際に使うため維持する．
- **`Frame.World`**: Fin74 と同じく `abbrev Frame.World {_ : Frame κ} := κ` にする．
  ポイントは **frame を「使わない implicit 引数」として抱える**こと．これにより
  (i) `x : M.World` という型注釈の項の中に `M` が構文的に残り，`x ⊧ φ` や `Valuation F` の
  elaboration で `M`/`F` を復元できる（Fin74 の `Rel`/`≺` と同じ仕掛け），
  (ii) reducible 展開一発で `κ` に一致するため型ギャップが生じない，の両立ができる．
- **`Valuation`・`Model`**: `abbrev Valuation (F : Frame κ) := ℕ → Set F.World`，
  `structure Model (κ : Type u) extends Frame κ where Val : ℕ → Set κ`．
  モデルリテラル `⟨F, V⟩` は無傷で通る想定．
- **`mk_ℬ`**: `def Frame.mk_ℬ (κ : Type u) [Nonempty κ] (B : Set κ → Set κ) : Frame κ`．
  呼び出し側（`Filtration.toModel` の `Frame.mk_ℬ (FilterEqvQuotient M T) Fi.B` 等）は
  **テキスト上ほぼ無変更**で，返り値の型に κ が現れるようになる．
- **`Frame.logic`／`FrameClass.logic`**: 前者は `Frame.logic (F : Frame κ) : Logic ℕ` と
  パラメータ化するだけ．後者は FrameClass の設計（§2）に従う．
- **`Semantics` 各 instance**: `Semantics (Frame κ) (Formula ℕ)`・`Semantics (Model κ) …` は
  κ を implicit に持つ universe 多相 instance にするだけで成立する．
  問題は世界レベル（§8 リスク1）とフレームクラスレベル（§2）の2つ．

---

## 2. `FrameClass` 問題の設計判断（本文書の中心）

### 2.1 前提となる観察

- FrameClass に対して実際に使われている操作は grep 実測で次の3種類**のみ**．
  1. membership: `F ∈ C`・`M.toFrame ∈ C`・set-builder `{ F | F.IsX }`・`Set.mem_setOf_eq` 変換．
  2. `C ⊧ φ`（Foundation の `Semantics (Set M)` instance）と `C ⊧* Ax`（`ModelsSet`），
     および `Semantics.set_models_iff`（`Hilbert.lean` の1箇所）．
  3. `C.Nonempty`（`consistent_of_sound_frameclass`，呼び出し29ファイル）．
  `⊆`・`∩`・`∪`・`ᶜ` などの集合演算は**一切使われていない**（grep で確認）．
  つまり「`Set` であること」への依存は見かけほど深くなく，membership・validity・非空性の
  3 API を提供できればどの表現でもよい．
- フレームクラスは本質的に「異なる世界型のフレームを混在させて含む」必要がある．
  同じ `FrameClass.E4` が反例フレーム（`Fin 2`）と正準フレーム（`MaximalConsistentSet 𝓢`）の
  両方を含むことが健全性・完全性の証明の骨格そのものである（`Canonicity.completeness` は
  `𝓒.toModel.toFrame ∈ C` を仮定に取る）．よって `Set (Frame κ)`（κ 固定）は論外で，
  κ をまたぐ量化がどこかに必ず要る．

### 2.2 選択肢の比較

**選択肢1: Σ 型で束ねる** — `FrameClass := Set ((κ : Type) × Frame κ)`．

- 「実質フィールド版に戻るのでは？」への答え: **戻らない**．defeq 問題（§4）は
  「証明の内部で扱うフレーム・モデルの `World` が構造体射影であること」から生じるのであって，
  フレームクラスの束ね方からは生じない．Σ 版でも証明内部の主体は常に `Frame κ`（κ 明示）で
  あり，Σ の対は Sound/Complete の主張の境界にしか現れない．また Σ の第2射影
  `(⟨κ, F⟩ : Σ …).2` は「コンストラクタ直上の射影」なので reducible 透過度で即簡約され，
  `mk_ℬ` のような plain `def` を挟む今回の病理は再現しない．
- 利点: `Set` API と Foundation の `Semantics (Set M)` instance・`set_models_iff` を
  そのまま使える（`Semantics ((κ : Type) × Frame κ)` を1個書けば残りは generic）．
- 欠点: **membership を書く全箇所に `⟨_, F⟩` の包み**が入る．
  `M.toFrame ∈ C` → `⟨_, M.toFrame⟩ ∈ C`，`{ F | F.IsE4 }` → `{ p | p.2.IsE4 }`，
  反例の `use ⟨Fin 2, …⟩` → `use ⟨_, ⟨Fin 2, …⟩⟩`．98箇所の membership 操作と
  約50のクラス定義すべてに視覚ノイズが乗り，dot notation（`p.2.IsE4`）も不格好になる．

**選択肢2: 述語版** — `FrameClass := ∀ ⦃κ : Type⦄, Frame κ → Prop`（`Type 1` に住む）．

- `Set` の API は使えなくなるが，§2.1 の通り必要なのは3 API のみで，すべて自前定義できる．
  - membership: `instance : Membership (Frame κ) FrameClass := ⟨λ C F => C F⟩`．
    以後 `F ∈ C` は今まで通りの表記で書け，`Set.mem_setOf_eq.mp hF` は不要になる
    （`hF : F ∈ C` がそのまま `C F` に defeq）．
  - validity: `instance : Semantics FrameClass (Formula ℕ)` を
    `C ⊧ φ := ∀ ⦃κ⦄ (F : Frame κ), F ∈ C → F ⊧ φ` で直接張る．`Semantics (M : Type*)` は
    universe 多相（Foundation `Semantics.lean:25` で確認）なので `Type 1` の carrier で問題ない．
    `C ⊧* Ax` は `ModelsSet` が任意の `Semantics` carrier に対して定義されるため自動で乗る．
    `Semantics.set_models_iff` の使用1箇所は同内容の自前補題（定義の unfold）に置換．
  - 非空性: `def FrameClass.Nonempty (C : FrameClass) : Prop := ∃ (κ : Type) (F : Frame κ), F ∈ C`．
    `consistent_of_sound_frameclass` の `C_nonempty.choose` の2行を `obtain` に書き直す．
- クラス定義は `protected def FrameClass.E4 : FrameClass := λ F => F.IsE4` の形
  （set-builder は使えないが，むしろ短くなる）．
- Sound/Complete の主張 `Sound Modal.E4 FrameClass.E4` は**一字も変わらない**
  （Foundation の `Sound (𝓢 : S) (𝓜 : M)` は `M : Type*` の任意の carrier を取る）．
- 反例補題は `(¬C ⊧ φ) ↔ (∃ κ (F : Frame κ), F ∈ C ∧ ¬F ⊧ φ)` になり，existential に κ が
  1個増えるが，呼び出し側は `use Fin 2, ⟨…⟩`（あるいは `use _, ⟨…⟩`）と1引数増えるだけ．
- 懸念点: `Membership (α : outParam Type*) (γ : Type*)` の α が outParam であるため，
  `Membership (Frame κ) FrameClass` の instance 解決で κ が γ 側から決まらない．
  discrimination tree 上は `Membership ? FrameClass` にマッチして κ は要素側の unification で
  埋まる見込みだが，**動作は S1 で最初に実証する**（§8 リスク2）．失敗した場合の代替は
  (i) `FrameClass` を述語1本を包む one-field structure にして `CoeFun` を張り membership 記法を
  自前 `infix`（`∈` のまま `Membership` を諦める），または (ii) Σ 版（選択肢1）への切替．

**選択肢3: フレームクラス廃止・全称量化（Fin74 方式）**．

- Fin74 は `theorem fine_logic_kripke_incomplete : (∀ {κ} (F : Frame κ), F ⊧ LogicFi → F ⊧ ∼E) ∧ …`
  （`Result/Incomplete.lean` 実物確認）のように，その場の全称量化で書きフレームクラス型を
  持たない．これは Fin74 が「主定理1本」のプロジェクトだから成り立つ書き方である．
- `Neighborhood` では `Sound L C`・`Complete L C` という**型クラスの第2引数に置く対象**が
  フレームクラスの存在意義であり，28論理×（健全性・完全性・無矛盾性・有限モデル性）＝
  100個超の instance と，それを消費する `Sound.not_provable_of_countermodel (𝓜 := FrameClass.ED)`
  型の呼び出し（40回超）がこの機構に乗っている．廃止すると Sound/Complete の型クラス運用が
  丸ごと崩れ，各論理に bespoke な命題を書き直すことになる．書き換え量は選択肢2の数倍で，
  得るものは型1個の削減のみ．**却下**．

**選択肢4: ハイブリッド**（`Frame κ` ＋ 束ねた `Bundled.Frame` の二本立て）．

- `Bundled.Frame := (κ : Type) × Frame κ`（または World フィールド版の再定義）を別に持ち，
  `FrameClass := Set Bundled.Frame` とする案．選択肢1と実質同型だが，`Bundled.Frame` に
  独自の構造体を使うと `IsE4` 等のフレーム性質クラスを bundled 側にも重複定義するか
  強制写像越しに引き回すかの二択になり，二重定義・相互変換補題のコストが恒常的に残る．
  Σ 型なら重複定義は不要（`p.2.IsE4` と書けばよい）ので，この選択肢は選択肢1に吸収される．
  **独立の選択肢としては却下**．

### 2.3 結論

**選択肢2（述語版）を採用する．** `FrameClass := ∀ ⦃κ : Type⦄, Frame κ → Prop` とし，
membership instance・`Semantics FrameClass` instance・`FrameClass.Nonempty` を自前で用意する．

決め手は次の3点．

1. 使用221箇所の大半（`Sound`/`Complete` の主張・`FrameClass.X` の参照・`C ⊧ φ`）が
   **テキスト無変更**で残り，変更が必要な箇所（membership 操作98箇所）も
   `Set.mem_setOf_eq` 変換の削除という「行が減る」方向の機械的変更になる．
   Σ 版は逆に全 membership 箇所へ包み・射影が増える．
2. `Canonicity.completeness (hC : 𝓒.toModel.toFrame ∈ C)` のように「素のフレームの membership」
   を仮定に取る補題が証明の主動線にあり，述語版はここが最も自然に書ける．
3. 集合演算（⊆・∩）が現状使われていないため，`Set` を捨てるコストが実測ゼロ．
   将来クラス間の包含を語りたくなったら `C₁ ≤ C₂ := ∀ ⦃κ⦄ ⦃F : Frame κ⦄, F ∈ C₁ → F ∈ C₂` を
   足せばよい．

ただし §2.2 の outParam 懸念があるため，**S1 で `Membership`・`Semantics`・`⊧*` の3点が
実際に elaborate することを最初に検証し，失敗時は選択肢1（Σ 版）へ切り替える**．
切替コストは FrameClass 関連の定義ファイル1箇所＋membership 箇所の書き方だけで，
Frame/Model の κ 化本体（S1 の大部分）は両案で共通なので手戻りは限定的である．

---

## 3. universe の扱い

- **`Frame (κ : Type u)`・`Model (κ : Type u)` は universe 多相にする**（Fin74 と同じ）．
  `𝒩 : κ → Set (Set κ)` は `κ : Type u` のとき `Type u` に収まり，`Frame κ : Type u`．
  多相化のコストはゼロで，現状の `Type 0` 固定より一般的になる．
- **`FrameClass` は κ の量化範囲を `Type`（= `Type 0`）に固定する**（`FrameClass : Type 1`）．
  理由: `Complete 𝓢 C` は「正準フレームが `C` の要素であること」を通じて証明される
  （`Canonicity.completeness`）．正準フレームの世界は `MaximalConsistentSet 𝓢 : Type 0`，
  filtration の商 `FilterEqvQuotient M T` も `Type 0`，全ての反例フレーム（`Fin n`・`Unit`）も
  `Type 0` である．FrameClass を `∀ ⦃κ : Type u⦄, …` と多相にすると，`Complete` instance は
  「正準フレームを要素に持てる」`u = 0` でしか成立せず，`u > 0` の主張は別途 `ULift` 移送を
  書かない限り**偽ではないが証明されない**宙ぶらりんの型になる．現状（`World : Type` 固定）と
  同じ表現力を保つには `Type 0` 固定が正しい．なお validity の「全フレーム」への一般化が
  必要になった場合（Fin74 の非完全性定理のような主張）は，FrameClass を経由せず
  `∀ {κ : Type u} (F : Frame κ), …` とその場で量化すればよく，`Frame` 自体が多相なので
  表現力は失われない．
- `FrameClass : Type 1` は現状の `Set Frame : Type 1` と同じ大きさなので，
  `Sound`/`Complete`（`M : Type*` を取る）にも `Logic ℕ` との組合せにも影響しない．
- `Valuation F = ℕ → Set F.World : Type u`・truthset・`Satisfies` も u 多相で素直に通る．
  `Frame.IsFinite`（`Finite F.World`）も `Finite κ` に落ちるだけで問題ない．

---

## 4. defeq 仮説の検証結果

**結論: 仮説は本質的に正しい．ただし効果範囲は「World 起因の型レベルのギャップ」に限られ，
現在の Filtration の26エラーの大半は別系統である．** 根拠は以下の通り．

### 4.1 病理のメカニズム（実物で確認できたこと）

- `Filtration.toModel` は `Frame.mk_ℬ (FilterEqvQuotient M T) Fi.B` を `toFrame` に置く
  （`Filtration.lean:204–206`）．`mk_ℬ` は **reducible でない plain `def`** で，その値が
  構造体リテラルである．したがって `Fi.toModel.World` を `FilterEqvQuotient M T` に簡約するには
  「`toModel` の delta 展開 → `mk_ℬ` の delta 展開 → コンストラクタ上の射影簡約」という
  連鎖が必要で，先頭2段が plain `def` の delta である．`instances` 透過度は
  reducible＋instance のみを unfold するため，この連鎖は新しい Lean の unifier では実行されない．
  これが `Set (FilterEqvQuotient M T)` と `Set ((transitiveFiltration M T).toModel.World)` の
  型分裂の正体である．
- 移植コミット 6a8146d のメッセージが同じ現象を独立に記録している:
  「Definitional unfolding at `instances` transparency no longer bridges `Proofset` and
  `Model.World`」．`Proofset 𝓢 = Set (MaximalConsistentSet 𝓢)` と
  `Set (𝓒.toModel.World)` のギャップは，`Canonicity.toModel` が
  `World := MaximalConsistentSet 𝓢` のリテラル（`Completeness.lean:156–159`）である以上，
  上と同一の構造（plain `def` 越しの射影）である．directions の記録
  （`202607301200_port-modal-neighborhood.md` の「3系統」）とも一致する．
- エラーログ実物との突き合わせ: `filtration-build-errors.txt` の 363行・374行（E8/E9）・
  540行（E19）は文脈中に `X : Set (transitiveFiltration M T).toModel.World` と
  `Set (FilterEqvQuotient M T)` の混在が実際に見え，`Trans` 合成失敗（E9/E19）は
  この型分裂で説明できる（`nbhd-filtration-fix.md` §5 難所2(b) の推定と同じ結論）．

### 4.2 κ 化で消えることの確認

κ 化後は `Filtration.toModel : Model (FilterEqvQuotient M T)` となり，
`Fi.toModel.World` は `@Frame.World (FilterEqvQuotient M T) _` — すなわち
**reducible な `abbrev` の適用**であって構造体射影ではない．reducible 透過度
（`instances` 透過度に含まれる）の1段展開で `FilterEqvQuotient M T` に一致するため，
この種の型分裂は**構成方法（`mk_ℬ` 経由か，リテラルか，多段の `def` 越しか）に依らず**
原理的に発生しなくなる．`Canonicity.toModel : Model (MaximalConsistentSet 𝓢)` と
`Proofset 𝓢` のギャップも同様に消える．`Supplementation`・`IntersectionClosure` の
`Frame → Frame` 変換も `Frame κ → Frame κ`（世界型保存が型で明示）になり，
`supplementedTransitiveFiltration` のような合成でも World の同一性が構文的に保たれる．

### 4.3 効果の限界（正直な限定）

- 26エラーの分類（`nbhd-filtration-fix.md` §3）で系統(3)（透過度起因の型不一致）と
  される・疑われるのは E9・E19・E23・E24 の**4件**（E23/E24 は Setoid instance 経路等の
  別因の可能性が残ると同計画自身が明記している）．残りの系統(1) instance 厳格化・
  系統(2) `rfl` 残差・系統(4) `Finset.mem_union`・系統(5)の一部は **κ 化では消えない**．
  つまり本改修は「Filtration の26エラーの主因の除去」ではなく，
  「型分裂系のエラーを恒久的に絶ち，同種の再発（今後の filtration 合成・正準モデル拡張で
  必ず再燃する）を防ぐ構造的修正」である．
- `𝓒.𝒩` vs `𝓒.toModel.𝒩` のような**項レベル**の射影ギャップ（6a8146d が記録するもう一つの
  現象）は World ではなく `𝒩` フィールドの話なので κ 化では消えない．ただし型が一致していれば
  `simp only [toModel]` 等の局所処置で済み，型不一致による `rw` 失敗・`Trans` 失敗よりはるかに
  軽症である．
- **代替の安価な対処との比較**: `mk_ℬ`・`toModel` 等に `@[reducible]` を付ければ今回の
  型分裂も unifier が越えられるようになる可能性が高い．しかしこれは (i) モデル構成のたびに
  reducibility を人手で管理し続ける対症療法であり，(ii) 大きな定義の無差別 unfold で
  elaboration・`simp`・`grind` の性能と挙動を悪化させ得る．κ パラメータ化は「World の同一性を
  型システムに載せる」根治であり，Fin74 と構成が揃う副次効果もあるため，こちらを採る．

以上より，**この改修はスタイル改善に留まらずバグ修正的な意味を持つ**（仮説は支持される）．
ただし §7 の通り，だからといって Filtration 修正より先に割り込ませる根拠にはならない．

---

## 5. 改修後の定義案（擬似コード）

```
-- Semantics/Basic.lean（改修後の骨格）

structure Frame (κ : Type u) where
  [world_nonempty : Nonempty κ]
  𝒩 : κ → Set (Set κ)

namespace Frame
  variable {F : Frame κ}
  abbrev World {_ : Frame κ} : Type u := κ          -- Fin74 と同じ「F を抱える別名」
  instance : Nonempty F.World := F.world_nonempty
  @[reducible] def box (F : Frame κ) : Set F.World → Set F.World := λ X => { w | X ∈ F.𝒩 w }
  @[reducible] def dia (F : Frame κ) := λ X => (F.box Xᶜ)ᶜ
  def mk_ℬ (κ : Type u) [Nonempty κ] (B : Set κ → Set κ) : Frame κ   -- 𝒩 x := { X | x ∈ B X }
  class IsFinite (F : Frame κ) : Prop where world_finite : Finite κ
  abbrev simple_blackhole : Frame Unit := ⟨λ _ => { Set.univ }⟩
end Frame

abbrev Valuation (F : Frame κ) := ℕ → Set F.World

structure Model (κ : Type u) extends Frame κ where
  Val : ℕ → Set κ
instance : CoeSort (Model κ) (Type u) := ⟨λ M => M.World⟩   -- 要検証（§8 リスク1）

-- フレームクラス（選択肢2）
def FrameClass : Type 1 := ∀ ⦃κ : Type⦄, Frame κ → Prop
instance : Membership (Frame κ) FrameClass := ⟨λ C F => C F⟩          -- 要検証（§8 リスク2）
instance : Semantics FrameClass (Formula ℕ) := ⟨λ C φ => ∀ ⦃κ⦄ (F : Frame κ), F ∈ C → F ⊧ φ⟩
def FrameClass.Nonempty (C : FrameClass) : Prop := ∃ (κ : Type) (F : Frame κ), F ∈ C
abbrev FrameClass.logic (C : FrameClass) : Logic ℕ := { φ | C ⊧ φ }

-- 反例用補題（κ の existential が1個増える）
lemma iff_not_validOnFrameClass_exists_frame :
  (¬C ⊧ φ) ↔ (∃ (κ : Type) (F : Frame κ), F ∈ C ∧ ¬F ⊧ φ)

-- 各論理（Logic/E4.lean など）
protected def FrameClass.E4 : FrameClass := λ F => F.IsE4
protected def FrameClass.finite_E4 : FrameClass := λ F => F.IsFiniteE4
instance Neighborhood.sound : Sound Modal.E4 FrameClass.E4 := …       -- 主張は無変更

-- Completeness.lean / Filtration.lean
def Canonicity.toModel (𝓒 : Canonicity 𝓢) : Model (MaximalConsistentSet 𝓢)
def Filtration.toModel (Fi : Filtration M T) : Model (FilterEqvQuotient M T)
```

注意点:

- `FrameClass.X` は現在 `abbrev`＋set-builder だが，述語版では `Set.mem_setOf_eq` の
  simp 経路が消えるため，`F ∈ FrameClass.E4` が `F.IsE4` へ defeq で潰れる．既存証明の
  `replace hF := Set.mem_setOf_eq.mp hF`／`apply Set.mem_setOf_eq.mpr` 行（98箇所の大半）は
  削除または `show`／`exact` の直書きに置換する．
- `iff_not_validOnFrameClass_exists_model_world` は
  `∃ κ (M : Model κ), ∃ x : M.World, M.toFrame ∈ C ∧ ¬(x ⊧ φ)` になる．
- `consistent_of_sound_frameclass` の `C_nonempty.choose`／`choose_spec` は
  `obtain ⟨κ, F, hF⟩ := C_nonempty` に書き直す（デフォルト引数 `:= by simp` は，
  非空性が `use Unit, Frame.simple_blackhole` で閉じる形の simp 補題を用意するか，
  デフォルト引数を外して29箇所の呼び出しに明示引数を渡すかを実装時に選ぶ．後者が安全）．

---

## 6. ステップ分割（逐次実行前提）

`CLAUDE.local.md` の方針に従い並列化は前提にしない．各ステップは「1エージェント・
1ビルド確認・1コミット（論理単位で複数可）」の粒度．難易度は ★（機械的）〜★★★（設計判断あり）．

| # | ステップ | 内容 | 依存 | 難易度 |
|---|---|---|---|---|
| K0 | 事前スパイク | 使い捨てファイルで (a) `Membership (Frame κ) FrameClass` の outParam 解決，(b) `x ⊧ φ`（`Semantics M`＋`CoeSort`）の instance 解決，(c) `C ⊧* Ax` の3点が新設計で elaborate することを最小例で確認．失敗なら §2.3 のフォールバックを発動して本計画を更新 | なし | ★★ |
| K1 | `Basic.lean` 改修 | `Frame κ`・`World` abbrev・`mk_ℬ`・`Model κ`・`Valuation`・truthset・`Satisfies`/`ValidOnModel`/`ValidOnFrame`・新 `FrameClass`（membership・`Semantics`・`Nonempty`・`logic`・反例2補題）．このファイル単体でビルド | K0 | ★★★ |
| K2 | `Hilbert.lean` | 健全性2本と `consistent_of_sound_frameclass`（`Nonempty` の obtain 化・デフォルト引数の扱い決定） | K1 | ★★ |
| K3 | `Completeness.lean` | `Canonicity.toModel : Model (MaximalConsistentSet 𝓢)`．`Proofset` と `toModel.World` が defeq になるので，移植時に入れた型合わせの回避策（`simp only [toModel]` 等）が不要になった箇所は素直な形に戻す | K1 | ★★ |
| K4 | 公理ファイル群 | `AxiomK`/`AxiomM`/`AxiomC`/`AxiomN`/`AxiomP`/`AxiomGeach`（フレーム性質クラスの `variable {F : Frame κ}` 化．Geach 後半の Canonicity 節は K3 依存） | K3 | ★★ |
| K5 | `Supplementation.lean`・`IntersectionClosure.lean` | `Frame κ → Frame κ` 化（`World := F.World` フィールド行の削除） | K4 | ★ |
| K6 | `Logic/E.lean`・`EM.lean`・`EC.lean`・`EN.lean`・`ECN.lean`・`EK.lean` | 構造体リテラル（`World := Fin n`）を持つファイル群．`FrameClass.X` の述語化・membership simp の除去・反例 `use` の κ 引数追加 | K5 | ★★ |
| K7 | 残りの `Logic/*.lean`（22ファイル）と `Incomparability/ED_EP.lean` | K6 と同じパターンの機械的適用．3〜4ファイルずつコミット | K6 | ★ |
| K8 | 総仕上げ | `lake build` 全体 → 回避策・死んだ `Set.mem_setOf_eq` の残骸 grep → `just mk-all` → `just shake` → 再ビルド | K7 | ★ |
| K9 | `Filtration.lean` の κ 追随 | （nbhd-filtration 統合後に行う場合）`Filtration`/`minimalFiltration`/`transitiveFiltration` 等の型を κ 化に合わせ，型合わせ用に入れた `show`/型注釈の workaround を除去，コメントアウト中の8論理の `finite_complete` を復活してビルド | K8＋filtration 統合 | ★★ |

規模感: 変更対象は27＋1ファイル・約4900行のうち，実質差分は
membership 操作98箇所・リテラル15箇所・FrameClass 定義約50個・反例 `use` 約40箇所＋
`Basic.lean` の書き直し（約300行）で，Fin74 の実物という完動する参照実装があるため
K1 以外は機械的作業が支配的．

---

## 7. 実施順序の推奨

**推奨: 「Filtration 修正（nbhd-filtration の完遂）→ κ 改修 → Foundation 脱却 Phase 2」の順．
Foundation 脱却の Phase 1（新コア構築，nbhd-core の S1〜S18）だけは κ 改修と並行してよい．**

### 7.1 Filtration 修正を先に終わらせる理由

- κ 化で消えるのは残エラーのうち高々4件（E9・E19・E23・E24，§4.3）で，S5 まで完了済みの
  現行修正は6割方進んでいる．残る主戦場（E13〜E22 の `Finset`・`grind`・`rfl` 系）は κ と無関係．
- κ 改修は `Filtration.lean` が依存する `Basic.lean`〜`IntersectionClosure.lean` を全面的に
  書き換える．**ビルドが通っていない691行のファイルを土台ごと動かすのは，エラーの原因の
  切り分けを不可能にする**最悪の組み合わせであり，逆に filtration が green になっていれば
  K9 は「通っているファイルの機械的追随」に落ちる．
- 型分裂系への workaround（`show`・型注釈）は数行の局所処置であり，κ 化後の K9 で除去すれば
  無駄にならない（除去しなくても正しいまま残る）．

### 7.2 κ 改修を Foundation 脱却 Phase 2 より先に行う理由

- 2つの作業の直交性の検証: nbhd-defoundation 計画（`plans/nbhd-defoundation.md`）を精読した
  限り，Phase 1（S1〜S18）は新設ファイル（`Formula`・`Logic`・`Hilbert`・MCS・
  `Semantics/Interface`）のみを作り，`Frame`/`Model` には触れない．**ここまでは完全に直交**で
  並行可能．一方 Phase 2（S19〜S26）は既存41ファイルの import・variable 行を1ファイルずつ
  書き換えるため，κ 改修と**同じファイル・同じ行域**に触る．内容的には直交でも
  テキスト的には衝突するので，同時進行は不可，順序付けが必要．
- κ を先にすべき理由:
  1. κ 改修（差分は上記の通り限定的）の方が Phase 2（41ファイル全とっかえ）より小さく，
     先に確定させれば Phase 2 の各ファイル切替が最終形に一発で着地する．逆順だと
     切替済みファイルへもう一度全量パスをかけることになる．
  2. **設計の連成が1箇所ある**: defoundation §2.5 は Foundation の
     `Semantics (Set M)` generic instance と `set_models_iff` を縮小移植する計画だが，
     述語版 FrameClass の採用でフレームクラスは `Set` でなくなり，generic Set instance の
     主要顧客が消える．κ の設計を先に確定させれば，nbhd-core の S18（Semantics/Interface）は
     Set instance を移植対象から外し FrameClass 用 instance を直接持てる．
     逆順では S18 が旧設計向けに作られ，後で書き直しになる．
  3. κ 改修は Filtration 由来の型分裂の根治なので，早く入れるほど後続作業
     （8論理の `finite_complete` 復活・今後の FMP 拡張）が同じ罠を踏まなくなる．
- 「Phase 2 と同時に行う」案（1ファイル切替のついでに κ 化も済ませる）は，1ファイルあたりの
  差分に2つの独立な失敗要因を混ぜることになり，どちらの変更でビルドが壊れたかの切り分けが
  できなくなるため採らない（defoundation 計画自身が Phase 2 を「原子的に」進める方針であり，
  その原子性を保つ意味でも変更軸は1つずつにする）．

### 7.3 まとめ（時系列）

1. nbhd-filtration: 現行計画（S6〜S13）を完遂し，統合先（port-modal-neighborhood / PR #24）へ
   マージ．
2. κ 改修: 本計画 K0〜K9 を新しい worktree で逐次実行（K9 で filtration も κ 追随＋
   workaround 除去＋8論理の `finite_complete` 復活）．
3. nbhd-core: Phase 1 は 1・2 と並行可．S18 だけは本計画の FrameClass 設計を反映して
   実装する．Phase 2（既存ファイル切替）は κ 改修の統合後に開始する．

---

## 8. リスクと難所

1. **世界レベル `x ⊧ φ` の instance 解決（最重要）**．現在は
   `Satisfies.semantics {M : Model} : Semantics M (Formula ℕ)`（`M` を `CoeSort` で型化）で
   動いており，`x : M.World` の型から `M` を復元できるのは `World` が `M` の射影だからである．
   κ 化後は `World` が「`F` を使わない implicit として抱える abbrev」になるため復元経路が
   変わる．Fin74 は `⊩` 記法＋`Forces _` で同じ問題を解いており（`x : @Frame.World κ M.toFrame`
   という型注釈から `M` が unify される），近傍側の `Semantics`／`CoeSort` 経由でも同じ機構で
   通る見込みだが，**discrimination tree が abbrev を key 化する際に instance が過度に一般化
   される可能性**は否定できない．K0 のスパイクで必ず最初に検証し，駄目なら
   (i) `Semantics` instance の carrier を `M.World`（abbrev 適用形）にする，
   (ii) 世界レベルだけ Fin74 式の明示記法 `x ⊧[M] φ` に切り替える（影響大なので最終手段），
   の順で代替する．
2. **`Membership (Frame κ) FrameClass` の outParam 問題**（§2.2）．K0 で検証．
   フォールバックは §2.3 に記載（one-field structure 化，または Σ 版への切替）．
3. **98箇所の membership simp 修正のばらつき**．大半は行削除だが，`simp` の closing に
   `Set.mem_setOf_eq` が暗黙に効いていた証明が数箇所は壊れる想定．K6/K7 で1ファイルずつ
   ビルドして潰す（一括 sed で済ませない）．
4. **`Nonempty` のデフォルト引数 `(C_nonempty : C.Nonempty := by simp)`**．述語版では
   `simp` が自動で閉じなくなる可能性が高い．29箇所の呼び出しは現状すでに明示引数を
   渡している（`consistent_of_sound_frameclass FrameClass.E4 $ by use …`）ため，
   デフォルト引数を外す方向で整理するのが安全．
5. **`grind`/`simp` 属性の再チューニング**．`Frame.box` 等は `@[reducible]` のまま残すが，
   `World` の意味が変わることで既存の `grind` 証明の探索空間が微妙に変わり得る．
   1ファイルずつのビルドで検知し，壊れた箇所は明示証明に落とす．
6. **Filtration との rebase 衝突**．κ 改修を nbhd-filtration の完了前に始めてしまうと，
   `Basic.lean`〜`IntersectionClosure.lean` の書き換えが filtration 側の前提を壊す．
   §7 の順序を守ることで回避する．
7. **nbhd-core S18 との設計連成**．本計画の FrameClass 設計（述語版）を nbhd-core 側へ
   伝達しないと，`Semantics/Interface` が `Set M` generic instance 前提で作られて手戻りになる．
   本ファイルを統合ブランチにコミットして参照可能にし，nbhd-core の direction ファイルにも
   一言注記するのが望ましい．
8. **K0 の結果次第で本計画の一部（§2.3・§5）が更新される**．スパイクで判明した事実は
   本ファイルに追記し（上書きせず），採用案の変更があれば K1 着手前にユーザーへ報告する．

---

## 設計改訂1（FrameClass 廃止によりこの文書の結論は破棄）

2026-07-30 追記．**本文書の中心的結論（§2.3「選択肢2（述語版 FrameClass）を採用する」）は，
ユーザーの明示的な指示により破棄された．後から読む人は §2・§5 の FrameClass 設計を
実装しないこと．** 既存の記述は履歴として残す（削除・修正しない）．

### 破棄の経緯

ユーザーから次の決定が下された（検討事項ではなく決定事項）．

1. `FrameClass` という型・概念，および FrameClass による validity という概念は廃止する．
   述語版（`∀ ⦃κ⦄, Frame κ → Prop`）も Σ 型版も作らない．
2. `Sound`／`Complete` 型クラスも `Semantics` 型クラスも作らない．健全性・完全性は
   ProvabilityLogic（`../SeqPL`）のように素の `theorem` として，フレーム条件の型クラスを
   instance 引数に置いた全称量化（`∀ {κ}, [Nonempty κ] → ∀ F : Frame κ, [F.IsX] → F ⊧ φ`）で書く．

本文書 §2.2 が選択肢3（フレームクラス廃止・全称量化）を却下した根拠は
「`Sound L C`・`Complete L C` という型クラスの第2引数に置く対象がフレームクラスの存在意義であり，
100個超の instance と40回超の消費がこの機構に乗っている」ことだった．**その `Sound`/`Complete`
型クラス機構そのものを廃止せよというのが今回の決定なので，却下理由は消滅し，選択肢3
（を型クラス条件 `Frame.IsX` で整えた形）が新しい結論になる．**

### 本文書のうち生き残る部分

- **κ パラメータ化そのもの（§1・§3・§4・§5 の Frame/Model/World abbrev/mk_ℬ 部分）は有効**．
  `Frame (κ : Type u)`・`abbrev Frame.World {_ : Frame κ} := κ` の Fin74 方式・defeq 分析（§4）・
  universe の扱い（§3．完全性の仮定側は κ を `Type 0` で量化，健全性側は多相）はそのまま
  新設計に引き継がれる．
- **§1.2 の `world_nonempty` フィールド維持の判断は覆る**: ProvabilityLogic に合わせ
  `[Nonempty κ]` の **instance 引数**にする．フレームを集合に入れる機構（FrameClass）が
  消えた以上，非空性を値に同梱する理由が無く，全定理で κ が binder に立つため．
- **K0 スパイクのうち (a) `Membership (Frame κ) FrameClass` と (c) `C ⊧* Ax` は不要**．
  (b) 世界レベル `x ⊧ φ` の elaboration 確認だけが引き続き意味を持つ．
- **§7 の実施順序（filtration → κ → defoundation Phase 2 の3段構え）は再編**され，
  「filtration マージ → κ 化＋意味論再設計＋Foundation 脱却 Phase 2 を1パスで」になる．
  Sound/Complete/FrameClass の廃止で各ファイルのステートメント自体が変わるため，κ だけ先に
  通しても同じ行を二度書き直すことになる（§7.2 の「変更軸は1つずつ」はステートメント不変が
  前提の議論だった）．

### 新しい設計・統合ステップ

具体設計（3キャリアの `⊧` の素の `infix` 多重定義，28論理の
`soundness`／`unprovable_of_countermodel`／`completeness`／`finite_completeness`／`Consistent` の
新しい形，`consistent_of_frame`，40箇所の反例パターンの書き換え，K0〜K9 を吸収した
統合ステップ T1〜T17）は，**nbhd-core worktree の `plans/nbhd-defoundation.md`
「設計改訂1（ユーザー指示による簡素化・FrameClass/Semantics/Sound/Complete 全廃）」節**に
一本化して記載した．そちらを正とする．
