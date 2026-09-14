# 原稿とLean形式化の対応（第12版・完了）

添付原稿の番号付き数学的結果14件を、付録A.1と二値例の補助主張を含めて形式化しました。有限座標モデルだけでなく、原稿の状態空間・周辺化・Čech微分・原始元最小値・コホモロジー・障害ノルムへの接続も実装済みです。

| 原稿 | 内容 | 主要実装 | 状態 |
|---|---|---|---|
| 2.1 | 全支持複体の非輪状性 | `FullSupportAcyclicity` | 完了 |
| 3.1 | 厳密な逆比例則・ゼロ係数の場合・双対公式 | `LinearProblem` | 完了 |
| 3.2 | 実際の原始元最小値と障害ノルムの極限 | `CechPrimitive`, `CechReciprocal`, `CechObstruction` | 完了 |
| 3.3 | 支持拡大の非拡大性 | `CechSupportNorm` | 完了 |
| 3.4 | 共通消失スケール | `LinearProblem` | 完了 |
| 4.1 | 相対表示・単位球・中心対称な多面体 | `CechObstruction`, `CechPolytope` | 完了 |
| 4.2 | 相対接続の線形等長同型と次数0の追加商 | `CechRelativeIsometry` | 完了 |
| 5.1 | 観測制限・選択ホモトピー・増大次数 | `ObservationRestrictionNorm`, `ObservationHomotopy`, `ObservationAugmentation` | 完了 |
| 5.2 | 生成リストによらない等長同型 | `ObservationListInvariance` | 完了 |
| 5.3 | 有限次元ノルム空間への関手 | `ObservationFunctor` | 完了 |
| 5.4 | 参照法則の比較 | `CechObstruction` | 完了 |
| 6.1 | 対角支持の例：一次元性・接続核・ノルム・最小値 | `DiagonalNorm`, `DiagonalSpanning`, `DiagonalConnecting`, `DiagonalRelativeCoordinates`, `DiagonalCost`, `SmallObservationLists` | 完了 |
| 6.2 | 三角形の例：微分・最小値・非零類・閾値 | `TriangleSetup`, `TriangleCocycle`, `TriangleCost`, `TriangleNorm`, `SmallObservationLists` | 完了 |
| A.1 | 順序複体比較：全次数の非拡大性と低次数の等長同型 | `OrderComplex`, `OrderComparison`, `OrderLowIsometry` | 完了 |

## 確認方法

- `audit/paper_coverage.json` は各結果に対応する完全修飾Lean宣言名を記録します。
- `scripts/verify.py` は全モジュールをビルドし、全640個の定理・補題と、対応表中の追加5定義の公理依存を検査します。
- `sorry`、`admit`、独自の `axiom`、`unsafe`、`native_decide` を実装内で許していません。依存を許可する標準公理は `propext`、`Classical.choice`、`Quot.sound` です。
- 原稿と全実装のSHA-256、Lean/mathlibの固定バージョン、検証コマンドと終了状態を `audit/verification.json` に記録します。
- パッケージ作成時に全実装ファイルの集合とハッシュを再照合し、古い検証結果の使い回しを拒否します。

## 表現上の対応

- `Cochain ... n` の `n` はタプルの長さです。原稿の次数pはn=p+1、増大次数−1はn=0に対応します。
- 二値状態は `Fin 2` で表し、0が−1、1が+1に対応します。三角形の観測順序は原稿どおり(12,23,13)です。
- 付録の順序複体は包含半順序上の鎖そのもので構成し、リスト複体との比較を明示的に証明しています。

## 形式化の対象外

文献紹介、動機、応用の見通し、結論の文章は証明命題にはしていません。複数消失スケールや次数2以上の等長比較など、原稿で未解決の展望として記した事項を、定理に格上げしていません。番号付き結果およびここで扱う付随数学的主張に未証明項目はありません。
