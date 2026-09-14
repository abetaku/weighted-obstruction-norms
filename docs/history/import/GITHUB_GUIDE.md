# GitHubでの管理手順

## 方針

一つの研究を一つのリポジトリに置きます。日常はGitHubの同じ場所を見れば最新版が分かるようにします。初回だけ、この整理済みZIPを展開して内容をアップロードします。ZIPファイル自体をコード置き場に置く方法では中身の差分を追いにくくなります。

## 初回：Chromeからアップロードする

1. GitHubにサインインし、右上の「+」から「New repository」を選びます。
2. 名前を `weighted-obstruction-norms` にし、公開範囲はまず **Private** にします。README・gitignore・licenseの自動追加は使わず作成します。必要な案内・除外設定はこの一式に入っています。
3. ダウンロードした準備用ZIPを展開します。中の `weighted-obstruction-norms` フォルダを開きます。外側のフォルダを丸ごと入れて一段余分にしないでください。
4. 空のリポジトリでは「uploading an existing file」、ファイルがある場合は「Add file → Upload files」を開きます。
5. **1回目**：展開フォルダの中の `WeightedObstructionNorms` フォルダだけをドラッグします。75個のLeanファイルです。説明を「Import Lean proof modules」として保存します。
6. **2回目**：再度アップロード画面を開き、同じ階層の残り全て（先ほどの `WeightedObstructionNorms` フォルダを除く）をドラッグします。説明を「Import manuscripts, verification records and project guide」として保存します。
7. トップページにREADMEの案内が表示され、日本語PDF・英語PDFのリンクが開くことを確認します。`paper/`、`audit/`、Leanの設定ファイルも確認します。

GitHubのブラウザアップロードは1回100ファイルまで、1ファイル25 MiBまでです。この一式はサイズ制限以内で、2回に分ければ件数制限も満たします。初期投入の2回が終わるまではリポジトリが一時的に不完全です。

## その後の更新

- ファイル名を固定し、同じパスのファイルを更新します。「最終版2」「(1)」を増やしません。
- 小さな修正でも、保存時に「補題の仮定を明記」「日本語PDFを更新」など変更理由を一行書きます。
- TeXを変えたら対応するPDFの更新要否も確認します。Leanや仮定を変えたら、形式化との対応と検証を確認します。
- 大きな変更は別の作業ブランチとPull Requestで確認してから本流へ取り込みます。これらは「変更案を確認して採用する」仕組みです。
- PDFは今回小さいため通常ファイルとして保持します。完成版はReleasesにも添付できます。旧版をファイル名違いで大量に積まず、履歴とReleasesで参照します。
- ブラウザでフォルダを再アップロードしても、削除・改名の同期まで自動で済むとは考えないでください。変更後に余分な旧ファイルがないか確認します。

## 完成した節目を残す

初回投入後、右側の「Releases」から新しいリリースを作り、例えば `v1.0.0` とします。形式化作業の内部履歴「第12版」と、リポジトリの最初のリリース番号は別物です。説明に対応する原稿と検証状態を書きます。

GitHubが用意するソース一式のダウンロードに加え、日英PDFを添付すれば閲覧しやすくなります。元のLean ZIPを保管したければ、このリリースの添付物に置けます。日常のコード管理は展開したソースで行います。

## AIと継続する場合

次回はリポジトリのURLと、今回直したい内容を伝えます。非公開リポジトリはURLだけではAIが読めないため、利用環境のGitHub接続とアクセス権が必要です。この一式を作った時点では接続・実アップロードは行っていません。

プロジェクト内の `AGENTS.md` と共同研究ルールに、文献確認、随時Lean検証、原稿対応、履歴の残し方を記載しています。対応する環境で読み込んで作業します。

## 参考：GitHub公式手順（2026-09-14確認）

- [リポジトリの作成](https://docs.github.com/en/repositories/creating-and-managing-repositories/creating-a-new-repository)
- [ファイル・フォルダのアップロードと制限](https://docs.github.com/en/repositories/working-with-files/managing-files/adding-a-file-to-a-repository)
- [リリースの管理](https://docs.github.com/en/repositories/releasing-projects-on-github/managing-releases-in-a-repository)
