# 第2回の追加成果

Lean 4.19.0 / mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b で、全106件の名前付き theorem/lemma を検証しました。前回79件から27件増えています。この件数は論文の定理数ではなく、補助補題を含むLean宣言の数です。

## 追加した証明

- `LinearProblem.zero_obstruction_limit`：旧座標だけで解ける場合、旧重みが正の極限へ、新重みがゼロへ収束すると、最適値は旧座標の最適値へ収束します。補正線形写像を構成し、最適値の上下から挟んで証明しています。
- `common_scale_zero_limit` と `common_scale_exact_eventual`：原稿の共通スケール命題のゼロ分岐と最終的比例の条件を追加しました。
- `RelativeWindow`：旧コホモロジーをコサイクル／境界の商として構成。相対コサイクル上の接続写像、全射性、商最適化条件との一致、単位球公式、ノルムの公理、接続核、非零類の厳密な逆比例則を証明しました。

## 検証の範囲

`lake build` と全106宣言の `#print axioms` が成功しました。実装に `sorry`、`admit`、独自の `axiom`、`unsafe`、`native_decide` はありません。推移的な公理依存は Lean/mathlib の標準的な `propext`、`Classical.choice`、`Quot.sound` のみです。

`RelativeWindow.full_exact` は全支持での完全性に相当する仮定です。具体的なČech複体でこの仮定を証明したわけではありません。接続写像は相対コサイクルから定義しており、相対境界で割った相対コホモロジーへの降下は残っています。

**原稿全体の形式化は未完了です。** 具体的Čech複体・非輪状性、双対公式、観測変更の写像・ホモトピー・関手性、順序複体比較、および例との同定などは `FORMALIZATION_STATUS.md` に記載しています。
