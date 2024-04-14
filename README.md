# Hello, Type System
Lean 4でプログラミング言語の意味論・型システムに入門するリポジトリです。
## Build
```sh
lake update
lake build

# with docs by doc-gen4
lake build -R -Kenv=dev HelloTypeSystem:docs
```
## References
- 五十嵐淳 著. プログラミング言語の基礎概念, サイエンス社, 2011.7, (ライブラリ情報学コア・テキスト ; 24). 978-4-7819-1285-1. https://ndlsearch.ndl.go.jp/books/R100000002-I000011238587
- 大堀淳 著. プログラミング言語の基礎理論. 新装版, 共立出版, 2019.8. 978-4-320-12450-9. https://ndlsearch.ndl.go.jp/books/R100000002-I029842615
- G.ウィンスケル 著ほか. プログラミング言語の形式的意味論入門, 丸善出版, 2023.1. 978-4-621-30763-2. https://ndlsearch.ndl.go.jp/books/R100000002-I032600297
