# 資料案内

論文の概要は [日本語README](../README_ja.md) または
[English README](../README.md) を参照してください。

## 論文と証明コード

| 資料 | 内容 |
| --- | --- |
| [paper/](../paper/) | 日本語・英語の論文PDFとTeXソース |
| [WeightedObstructionNorms/](../WeightedObstructionNorms/) | Leanによる定義と証明 |
| [LEAN.md](LEAN.md) | Lean実装の説明と検証の実行方法 |
| [FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) | 論文の各結果とLeanコードの対応範囲 |

## 検証資料

[audit/](../audit/) に、ビルド結果、公理監査、
検証対象のハッシュ値、実行環境の記録を収録しています。

検証記録が保証する範囲は、各記録に示された対象と実行条件に限られます。
Leanの検証成功と、論文全体との意味上の対応は区別してください。
対応範囲の確認には [FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md)
を参照してください。

## 研究・管理資料

| 資料 | 内容 |
| --- | --- |
| [共同研究ルール](mathematical_collaboration_rules.md) | 研究・原稿編集・検証を進める際の方針 |
| [改訂記録](history/revisions/) | 論文と形式化の検討・修正の経緯 |
| [取り込み記録](history/import/) | 登録した成果物の照合結果と関連資料 |

改訂記録と取り込み記録は、作成時点の経緯を保存する資料です。
論文を読む際や、検証を実行する際の手順書ではありません。

## ファイルの取得

論文PDF・ソース・証明コード・検証資料をまとめて取得するには、
GitHubの「Code → Download ZIP」または `git clone` を使ってください。

## 保管方針

原稿、PDF、証明コード、依存関係の固定情報、検証記録を保管します。
認証情報、秘密鍵、ビルドキャッシュ、TeXの一時生成物は含めません。
