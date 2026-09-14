# 補足資料

論文の要旨と主結果は [リポジトリのREADME](../README.md)、日英の原稿は [paper/](../paper/) にあります。

| 資料 | 内容 |
| --- | --- |
| [LEAN.md](LEAN.md) | Lean実装の詳細と再検証方法 |
| [FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) | 原稿の数学的結果とLean宣言の対応範囲 |
| [共同研究ルール](mathematical_collaboration_rules.md) | このプロジェクトでの研究・検証の進め方 |
| [改訂記録](history/revisions/) | GitHub登録前の第2〜12版の作業記録 |
| [初回取り込み資料](history/import/) | 元ファイルの照合結果・識別情報と当時のアップロード案内 |
| [検証資料](../audit/) | ビルド・公理監査・ハッシュ・実行環境の記録 |

## 履歴の読み方

改訂記録と初回取り込み資料は当時の内容を保持しています。途中版にある「未完了」や、初回案内の「アップロード未実施」は当時の状態です。現在の原稿対応は上記の形式化対応表を参照してください。技術説明・対応表にコード書式で記した `audit/` や `scripts/` などのパスは、リポジトリのルートを基準にしています。

2026-09-14の構成整理で、次の移動を行いました。移動したファイルの内容は変更していません。

| 旧パス | 現在のパス |
| --- | --- |
| `README_ja.md` | `docs/LEAN.md` |
| `FORMALIZATION_STATUS.md` | `docs/FORMALIZATION_STATUS.md` |
| `REVISION_*.md` | `docs/history/revisions/REVISION_*.md` |
| `docs/GITHUB_GUIDE.md` | `docs/history/import/GITHUB_GUIDE.md` |
| `docs/IMPORT_REPORT.md` | `docs/history/import/IMPORT_REPORT.md` |
| `docs/received_files.json` | `docs/history/import/received_files.json` |

`audit/computation-manifest.json` は元の配布物のハッシュ記録です。上表の移動前パスや当時の配布スクリプトのハッシュを含み、現在のリポジトリ全体の一覧ではありません。元の配置とスクリプトは [整理前のコミット](https://github.com/abetaku/weighted-obstruction-norms/tree/22d682e971fb05d5f2921596e0b52ae79df1efd8) から確認できます。原稿・Leanソース・監査ファイルは構成整理で変更しておらず、`audit/verification.json` に記録された検証対象のパスとハッシュは維持しています。今回、Leanの再実行は行っていません。

`scripts/package.py` は移動後のパスに対応していますが、従来どおりLean配布物を作るためのスクリプトです。日英PDFや管理資料を含むリポジトリ全体の取得には、GitHubのソースアーカイブまたはgit cloneを使ってください。配布スクリプトを実行すると `audit/computation-manifest.json` が更新されます。

## 保管対象

原稿、証明コード、依存ライブラリの固定情報と検証の来歴を保持します。`audit/build.log` と `audit/axioms.log` は検証証拠なので、一般的な一時ログと区別して追跡します。`audit/environment.md` の一時実行パスと互換補助コードも、過去の実行条件を説明する資料です。

認証情報、秘密鍵、ローカル設定、ビルドキャッシュ、取得済みの依存ライブラリ、TeXの一時生成物は保管対象にしません。一般的なローカルファイルの除外パターンを `.gitignore` に設定しています。除外設定は既存のGit履歴からファイルを取り除くものではありません。
